# Using Liquid Haskell on the Idris source

Some of the Idris core type checker has been annotated with Liquid Haskell
refinement types. The continuous integration server has been set up to check
these properties, but if you want to check them locally, do the following:

## Installing Liquid Haskell
First, install cvc4 from http://cvc4.cs.nyu.edu/downloads/ .

Next, install Liquid Haskell: `cabal install liquidhaskell`. It requires GHC
7.8.3 or higher.

## Checking the Liquid Haskell invariants

Right now, we only have Liquid Haskell annotations for TT.hs.  Run it with the
appropriate GHC flags:

    liquid -isrc --smtsolver=cvc4 \
           -g -XMultiParamTypeClasses \
           -g -XFlexibleInstances \
           -g -XFlexibleContexts \
           -g -XDeriveFoldable \
           -g -XDeriveTraversable \
           src/Idris/Core/TT.hs

If you are testing changes, consider running it on just the definition DEFN
using `-b DEFN` at the end of the command.

## Errors

The Liquid Haskell error reports can be difficult to read. Luckily, it
generates spiffy colored HTML output with refinement types in tooltips. Consult:

    src/Idris/Core/.liquid/TT.hs.html

## Further reading

Right now, the best place to get started with Liquid Haskell is a series of
[blog posts][lh-blog]. Read them chronologically.

[lh-blog]: http://goto.ucsd.edu/~rjhala/liquid/haskell/blog/blog/archives/
