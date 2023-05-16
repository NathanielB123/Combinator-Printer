# Combinator-Printer
Print out combinators!

For example, if we have:
```hs
foo :: forall a. (a -> a) -> (a -> (a -> a) -> a) -> ((a -> a) -> a) -> a -> a
foo = \x y _ z -> y z (\w -> (x (x (y w (\_ -> x w)))))
```
We can do:
```
>>> printCombinator (foo @Tree)
\a b c d -> b d (\e -> a (a (b e (\f -> a e))))
```

See Haddock documentation (generate with `cabal haddock`) or read the code - it's surprisingly short!
