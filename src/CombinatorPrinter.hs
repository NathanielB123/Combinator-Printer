-- | Print out combinators!
module CombinatorPrinter
  ( printCombinator
  , showCombinator
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
  ) where

import Control.Monad.State (MonadState(..), State, evalState)
import Data.Char (chr, ord)
import Data.Foldable (Foldable(..))
import Data.List (intercalate)

-- | Print a combinator
--
-- This is useful in GHCI as when GHCI prints strings, it includes escape
-- characters (i.e: "\\" becomes "\\\\")
printCombinator :: CreateSTree f => f -> IO ()
printCombinator = putStrLn . showCombinator

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
showCombinator :: CreateSTree f => f -> String
showCombinator x = pretty . ereduce $ evalState (toL $ stree x) 0

-- | Example combinator
foo :: (p1 -> p1) -> (p1 -> (p1 -> p1) -> p1) -> p2 -> p1 -> p1
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
-- After performing `ereduce`-ing, we will obtain the same `L` and so will
-- print to the same combinator
foo'' :: (T2T -> T2T) -> (T2T -> (T2T -> T2T) -> T2T) -> T2T -> T2T -> T2T
foo'' = foo

-- | `Tree` wrapped in state monad to track the next available ID to use for
-- the next `Node`
type STree = State Int Tree

-- | A simple recursive tree, used to observe the structure of the combinator
data Tree =
  Node Int [STree]

-- | Simple lambda calculus AST
data L
  = Lam Int L
  | App L L
  | Term Int
  deriving (Show)

-- | Pretty-printing
class Pretty a where
  pretty :: a -> String

enclose :: String -> String -> String -> String
enclose l r s = l <> s <> r

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
      addParens Parens = parensEnclose
      addParens _ = id
      wasLam WasLam = True
      wasLam _ = False
      go :: PrettyState -> L -> String
      go ps (Lam x l) =
        addParens ps $ munless (wasLam ps) "\\" <> toChr x <> " " <> go WasLam l
      go ps (App l1 l2) =
        addParens ps $
        mwhen (wasLam ps) "-> " <> go NoParens l1 <> " " <> go Parens l2
      go _ (Term x) = toChr x

mwhen :: Monoid a => Bool -> a -> a
mwhen True = id
mwhen False = const mempty

munless :: Monoid c => Bool -> c -> c
munless = mwhen . not

toChr :: Int -> [Char]
toChr i = [chr $ (i + ord 'a')]

-- | Traverse the built-up tree and convert into the lambda calculus ADT `L`
toL :: STree -> State Int L
toL t = do
  cur <- get
  (Node i xs) <- t
  new <- get
  xs' <- traverse toL xs
  pure $ foldr Lam (foldl' App (Term i) xs') [cur .. new -1]

replaceIn :: Int -> L -> L -> L
replaceIn x y t@(Term x')
  | x == x' = y
  | otherwise = t
replaceIn x y (Lam i l) = Lam i $ replaceIn x y l
replaceIn x y (App l1 l2) = App (replaceIn x y l1) (replaceIn x y l2)

occurIn :: Int -> L -> Bool
occurIn i (Term i') = i == i'
occurIn i (App l1 l2) = occurIn i l1 || occurIn i l2
-- Technically, we don't need to check the name of the bound variable here
-- for `L`s we create as we always guarantee variables will not share names,
-- but the additional code is very small
occurIn i (Lam i' l) = i /= i' && occurIn i l

-- | Reduce via eta reduction
ereduce :: L -> L
ereduce t@(Lam i (App l (Term i')))
  | i == i' && not (occurIn i l) = ereduce l
  | otherwise = t
ereduce (Lam i l) = Lam i $ ereduce l
ereduce (App l1 l2) = App (ereduce l1) (ereduce l2)
ereduce t@Term {} = t

-- | Reduce via beta reduction
--
-- Not actually used
breduce :: L -> L
breduce t@Term {} = t
breduce (Lam x l) = Lam x (breduce l)
breduce (App (Lam x l) y) = breduce $ replaceIn x y l
breduce (App l1 l2) = App (breduce l1) (breduce l2)

-- We need to fold over r, turning the (:)s into Lams
fresh :: State Int Int
fresh = do
  x <- get
  put $ succ x
  pure x

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
  fill n f = fill @g $ \xs -> n (stree f : xs)

--------------------------------------------------------------------------------
-- Old:
--------------------------------------------------------------------------------
-- | Traverse the built-up tree and print the lambdas and applications directly
--
-- Lower quality output compare to using `toL` and `pretty` (more parens than
-- necessary)
showS :: STree -> State Int String
showS t = do
  cur <- get
  (Node i xs) <- t
  new <- get
  xs' <- traverse showS xs
  let r = [cur .. new - 1]
  pure $
    "(" <>
    munless (null r) ("\\" <> intercalate " " (fmap toChr r) <> " -> ") <>
    toChr i <> munless (null xs') (" " <> intercalate " " xs') <> ")"
