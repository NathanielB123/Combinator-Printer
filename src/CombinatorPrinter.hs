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
  , showS
  , CreateSTree(..)
  , FillFun(..)
  ) where

import Control.Monad.State (MonadState(..), State, evalState)
import Data.Char (chr, ord)
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
showCombinator :: CreateSTree f => f -> String
showCombinator x = evalState (showS $ stree x) 0

-- | Example combinator
foo :: (p1 -> p1) -> (p1 -> (p1 -> p1) -> p1) -> p2 -> p1 -> p1
foo = \x y _ z -> y z (\w -> (x (x (y w (\_ -> x w)))))

-- | Version of the combinator with all type variables instantiated with
-- `Tree`
--
-- >>> showCombinator foo'
-- "(\\a b c d -> b (d) (\\e -> a (a (b (e) (\\f -> a (e))))))"
foo' ::
     (Tree -> Tree) -> (Tree -> (Tree -> Tree) -> Tree) -> Tree -> Tree -> Tree
foo' = foo

-- | What it says on the tin: a `Tree` to a `Tree`
type T2T = Tree -> Tree

-- | We can instantiate the polymorphic variables with alternative types
-- containing just `(->)`s and `Tree`s. For example, "@Tree -> Tree@".
--
-- This will print a different (more complicated) combinator but still works
-- (and if we performed beta-reduction, I think it might print the same thing)
foo'' :: (T2T -> T2T) -> (T2T -> (T2T -> T2T) -> T2T) -> T2T -> T2T -> T2T
foo'' = foo

-- | `Tree` wrapped in state monad to track the next available ID to use for
-- the next `Node`
type STree = State Int Tree

-- | A simple recursive tree, used to observe the structure of the combinator
data Tree =
  Node Int [STree]

munless :: Monoid c => Bool -> c -> c
munless True = const mempty
munless False = id

-- | Traverse the built-up tree and print the lambdas and applications
-- Some improvements could be made here for neater printing:
--
-- * Remove unncessary parens
--
-- * Replace unused variables with "@_@" instead of giving them explicit names
--
-- * Perform beta-reduction. i.e: "@\a -> f (a)@" should really just be printed
-- as "@f@"
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
  where
    toChr i = [chr $ (i + ord 'a')]

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
