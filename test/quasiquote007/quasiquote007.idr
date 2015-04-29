module Main

good1 : TypedQuote ((n : Nat) -> n + 1 = S n)
good1 = `(\n => plusCommutative n 1)

good2 : TypedQuote (Nat -> Nat)
good2 = `(id : Nat -> Nat)

good2' : TT
good2' = `(id : Nat -> Nat)

good2ok : untyped good2 = good2'
good2ok = Refl

good3 : TypedQuote Nat -> TypedQuote Nat -> TypedQuote Nat
good3 x y = `(plus ~x ~y)

||| Test that hints in the signature of TypedQuote are used for
||| disambiguation when no explicit goal type is provided in the
||| quasiquotation syntax
good4 : TypedQuote Nat
good4 = `(1 + 1)

good5 : TypedQuote Nat -> TypedQuote Nat
good5 n = `(~n + 1)


bad1 : TypedQuote Nat
bad1 = `("nope!")

bad2 : TypedQuote String -> TypedQuote Nat
bad2 str = `(S ~str)

bad3 : String
bad3 = `("oops")
