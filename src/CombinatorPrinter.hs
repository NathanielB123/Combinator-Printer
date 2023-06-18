{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# LANGUAGE ImpredicativeTypes #-}

-- | Print out combinators!
module CombinatorPrinter
  ( showCombinator
  , printCombinator
  , foo
  , foo'
  , foo''
  , Tree(..)
  , T2T
  , STree
  , CreateSTree(..)
  , FillFun(..)
  , toL
  , Pretty(..)
  , L
  , breduce
  , ereduce
  , showS
  , fresh
  ) where

import Control.Monad.State (MonadState(..), State, evalState)
import Data.Char (chr, ord)
import Data.Coerce (coerce)
import Data.Foldable (Foldable(..))
import Data.List (intercalate)
import Data.Monoid (Endo(..))

-- | Show a combinator
--
-- Specifically, this function allows printing any function with a type
-- containing only `(->)`s and `Tree`s.
--
-- Arbitrary combinators can be transformed into this form be simply 
-- instantiating every type variable with `Tree`
--
-- Possible future improvements for neater printing:
--
-- * Replace unused variables with "@_@" instead of giving them explicit names
--
-- * Introduce some mechanism to keep creating unique valid variable names past 
-- @26/"z"@. For example, appending numbers
--
-- * Offer an alternative show function which takes a dictionary of known
-- combinators  (@Map String L@) and prints the output in terms of them (i.e: by
-- checking sub-trees of the generated `L` for alpha equivalence). This would
-- provide a really nice interface for doing arithmetric on `Church` numerals
showCombinator :: CreateSTree f => f -> String
showCombinator x = pretty . ereduce $ evalState (toL $ stree x) 0

-- | Print a combinator
--
-- This is useful in GHCI as when GHCI prints strings, it includes escape
-- characters (i.e: "\\" becomes "\\\\")
printCombinator :: CreateSTree f => f -> IO ()
printCombinator = putStrLn . showCombinator

-- | Example combinator
foo :: forall p1 p2. (p1 -> p1) -> (p1 -> (p1 -> p1) -> p1) -> p2 -> p1 -> p1
foo = \x y _ z -> y z (\w -> (x (x (y w (\_ -> x w)))))

-- | Like `foo` but with all type variables instantiated to `Tree`
--
-- >>> showCombinator foo'
-- "\\a b c d -> b d (\\e -> a (a (b e (\\f -> a e))))"
foo' ::
     (Tree -> Tree) -> (Tree -> (Tree -> Tree) -> Tree) -> Tree -> Tree -> Tree
foo' = foo

-- | What it says on the tin: a `Tree` to a `Tree`
type T2T = Tree -> Tree

-- | We can instantiate the polymorphic type variables with alternative types
-- containing just `(->)`s and `Tree`s. For example, "@Tree -> Tree@".
--
-- After `ereduce`-ing, we will obtain the same `L` and so will print to the 
-- same combinator
foo'' :: (T2T -> T2T) -> (T2T -> (T2T -> T2T) -> T2T) -> T2T -> T2T -> T2T
foo'' = foo

-- | A rose tree, used to observe the structure of the combinator (each node is
-- an application of a variable to @n@ other expressions), containing a list of 
-- @n@ stateful computations which track which variables have been brought into
-- scope
data Tree =
  Node Int [STree]

-- | A 'Tree' wrapped in State monad
type STree = State Int Tree

-- | Simple lambda calculus AST
data L
  = Lam Int L
  | App L L
  | Var Int
  deriving (Show)

-- | Reduce via eta reduction
ereduce :: L -> L
ereduce = fst . go
  where
    go (Lam i (App l t@(Var i')))
      | i == i' && not (occurIn i l) = (l', True)
      | otherwise = (Lam i (App l' t), b)
      where
        (l', b) = go l
    go (Lam i l) = apWhen b (go . fst) (Lam i l', False)
      where
        (l', b) = go l
    go (App l1 l2) = (App (ereduce l1) l2', b)
      where
        (l2', b) = go l2
    go t@Var {} = (t, False)

-- | Reduce via beta reduction
--
-- Not actually used - beta reduction is perfomed automatically by the
-- combinator getting evaluated 
breduce :: L -> L
breduce t@Var {} = t
breduce (Lam x l) = Lam x (breduce l)
breduce (App (Lam x l) y) = breduce $ replaceIn x y l
breduce (App l1 l2) = App (breduce l1) (breduce l2)

-- | Pretty-printing
class Pretty a where
  pretty :: a -> String

enclose :: String -> String -> String -> String
enclose l r s = mconcat [l, s, r]

parensEnclose :: String -> String
parensEnclose = enclose "(" ")"

data PrettyState
  = WasLam
  | NoParens
  | Parens
  deriving (Eq)

instance Pretty L where
  pretty :: L -> String
  pretty = go NoParens
    where
      addParens ps = apWhen (needParens ps) parensEnclose
      addArrow ps s = mwhen (wasLam ps) "-> " <> s
      needParens = (Parens ==)
      wasLam = (WasLam ==)
      go ps (Lam x l) =
        addParens ps $ munless (wasLam ps) "\\" <> toChr x <> " " <> go WasLam l
      go ps (App l1 l2) =
        addParens ps . addArrow ps $ go NoParens l1 <> " " <> go Parens l2
      go ps (Var x) = addArrow ps $ toChr x

mwhen :: Monoid a => Bool -> a -> a
mwhen True = id
mwhen False = const mempty

munless :: Monoid c => Bool -> c -> c
munless = mwhen . not

apWhen :: forall a. Bool -> (a -> a) -> a -> a
apWhen = coerce $ mwhen @(Endo a)

toChr :: Int -> [Char]
toChr i = [chr $ (i + ord 'a')]

-- | Traverse the built-up tree and convert into the lambda calculus ADT `L`
toL :: STree -> State Int L
toL t = do
  Node i xs `With` r <- withFreshes t
  xs' <- traverse toL xs
  pure $ foldr Lam (foldl' App (Var i) xs') r

replaceIn :: Int -> L -> L -> L
replaceIn x y t@(Var x')
  | x == x' = y
  | otherwise = t
replaceIn x y (Lam i l) = Lam i $ replaceIn x y l
replaceIn x y (App l1 l2) = App (replaceIn x y l1) (replaceIn x y l2)

occurIn :: Int -> L -> Bool
occurIn i (Var i') = i == i'
occurIn i (App l1 l2) = occurIn i l1 || occurIn i l2
-- Technically, we don't need to check the name of the bound variable here
-- for `L`s we create as we guarantee by construction that variables will not
-- be shadowed, but the cost is low
occurIn i (Lam i' l) = i /= i' && occurIn i l

-- | Creates a fresh identifier
--
-- Arguably a more limited `Monad` that full-on `State` would be "cleaner" to
-- use here (would prevent misuse)
fresh :: State Int Int
fresh = do
  x <- get
  put $ succ x
  pure x

data WithFreshes a =
  a `With` [Int]

-- | Runs a stateful computation, and returns a list of all the fresh values
-- that were generated during it (assuming no state-modifying function other
-- than `fresh` was called)
withFreshes :: State Int a -> State Int (WithFreshes a)
withFreshes f = do
  cur <- get
  x <- f
  new <- get
  pure $ x `With` [cur .. new - 1]

-- | Creates a new variable/constructor (given a new unique identifier via 
-- `fresh`)
genNode :: State Int ([STree] -> Tree)
genNode = Node <$> fresh

-- | Everything that can be turned into an `STree`
--
-- Instances should cover every every type constructed with `(->)`s and 
-- `Tree`s
class CreateSTree f where
  stree :: f -> STree
  -- ^ Convert a combinator to a tree

instance CreateSTree Tree where
  stree :: Tree -> STree
  stree = pure

instance (FillFun f, CreateSTree g) => CreateSTree (f -> g) where
  stree :: (f -> g) -> STree
  stree f = genNode >>= stree . f . fill

-- | Class to provide appropriate constructors to pass to the combinator so its
-- structure can be observed
class FillFun f where
  fill :: ([STree] -> Tree) -> f
  -- ^ Create a constructor of the appropriate arity from an "@[STree] -> Tree@"
  -- (which can take any number of `STree`s, but is not curried)
  --
  -- It must take `[STree]`s instead of `Tree`s so we can recurse with `stree`,
  -- allowing us to generate constructors with types like 
  -- "@(STree -> STree) -> STree@"

instance FillFun Tree where
  fill :: ([STree] -> Tree) -> Tree
  fill n = n []

instance (CreateSTree f, FillFun g) => FillFun (f -> g) where
  fill :: ([STree] -> Tree) -> f -> g
  fill n f = fill $ n . (stree f :)

--------------------------------------------------------------------------------
-- Some More Example Combinators: Church Numerals
--------------------------------------------------------------------------------
type Church = forall a. (a -> a) -> a -> a

zero :: Church
zero = \_ x -> x

one :: Church
one = suc zero

two :: Church
two = suc one

suc :: Church -> Church
suc = \n f x -> n f (f x)

add :: Church -> Church -> Church
add = \n m f x -> n f (m f x)

mul :: Church -> Church -> Church
mul = \n m f x -> n (m f) x

pow :: Church -> Church -> Church
pow = \n m -> m n

pre :: Church -> Church
pre = \n f x -> n (\g h -> h (g f)) (\_ -> x) (\u -> u)

sub :: Church -> Church -> Church
sub = \m n -> (n pre) m

ifz :: Church -> Church -> Church -> Church
ifz = \n tr fa -> n (\_ -> tr) fa

-- | We can let GHC to infer type signatures for these combinators, moving the
-- @forall@s to the start...
--
-- ...making them printable!
--
-- >>> showCombinator (sub' @Tree @Tree @Tree @Tree @Tree @Tree @Tree @Tree @Tree)
-- "\\a b -> b (\\c d e -> c (\\f g -> g (f d)) (\\h -> e) (\\i -> i)) a"
--
-- This doesn't work fully in general. Some combinators may actually rely on
-- impredicativity which the `CreateSTree` class cannot handle, but it's still
-- pretty cool IMO.
sub' ::
     forall t1 t2 t3 t4 t5 t6 p1 p2 p3.
     t1
  -> (((((t2 -> t3) -> (t3 -> t4) -> t4) -> (p1 -> p2) -> (p3 -> p3) -> t5) -> t2 -> p2 -> t5) -> t1 -> t6)
  -> t6
sub' = \m n -> (n pre') m

pre' ::
     forall t1 t2 t3 t4 p1 p2 p3.
     (((t1 -> t2) -> (t2 -> t3) -> t3) -> (p1 -> p2) -> (p3 -> p3) -> t4)
  -> t1
  -> p2
  -> t4
pre' = \n f x -> n (\g h -> h (g f)) (\_ -> x) (\u -> u)

ifz' :: forall p1 p2 t1 t2. ((p1 -> p2) -> t1 -> t2) -> p2 -> t1 -> t2
ifz' = \n tr fa -> n (\_ -> tr) fa

mul' :: forall t1 t2 t3 t4. (t1 -> t2 -> t3) -> (t4 -> t1) -> t4 -> t2 -> t3
mul' = \n m f x -> n (m f) x

add' ::
     forall t1 t2 t3 t4. (t1 -> t2 -> t3) -> (t1 -> t4 -> t2) -> t1 -> t4 -> t3
add' = \n m f x -> n f (m f x)

pow' :: forall t1 t2. t1 -> (t1 -> t2) -> t2
pow' = \n m -> m n

suc' :: forall t1 t2 t3. ((t1 -> t2) -> t2 -> t3) -> (t1 -> t2) -> t1 -> t3
suc' = \n f x -> n f (f x)

--------------------------------------------------------------------------------
-- Old:
--------------------------------------------------------------------------------
-- | Traverse the built-up tree and print the lambdas and applications directly
--
-- Lower quality output compared to using `toL` and `pretty` (more parens than
-- necessary). Also no easy way to eta reduce.
showS :: STree -> State Int String
showS t = do
  Node i xs `With` r <- withFreshes t
  xs' <- traverse showS xs
  pure
    $ mconcat
        [ "("
        , munless (null r) ("\\" <> intercalate " " (fmap toChr r) <> " -> ")
        , toChr i
        , munless (null xs') (" " <> intercalate " " xs')
        , ")"
        ]
