# Combinator-Printer
Print out combinators!

For example, if we have:
```hs
foo :: forall a b. (a -> a) -> (a -> (a -> a) -> a) -> b -> b -> a
foo = \x y _ z -> y z (\w -> (x (x (y w (\_ -> x w)))))
```
We can do:
```
>>> printCombinator (foo @Tree @Tree)
\a b c d -> b d (\e -> a (a (b e (\f -> a e))))
```

See the Haddock documentation (generate with `cabal haddock`) or read the code - it's surprisingly understandable, not a type family in sight!
