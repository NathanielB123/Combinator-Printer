{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE UndecidableInstances #-}

module ShowInstance where

import CombinatorPrinter (CreateSTree, showCombinator)

instance (f ~ (a -> a), CreateSTree f) => Show (a -> a) where
  show :: f -> String
  show = showCombinator
