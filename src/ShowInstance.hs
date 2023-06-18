{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Orphan instance of `Show` for functions
-- We could also write one for a newtype-wrapped function, but I very-much doubt
-- there are many instances of `Show` for functions out there that could
-- conflict
module ShowInstance where

import CombinatorPrinter (CreateSTree, showCombinator)

instance (f ~ (a -> a), CreateSTree f) => Show (a -> a) where
  show :: f -> String
  show = showCombinator
