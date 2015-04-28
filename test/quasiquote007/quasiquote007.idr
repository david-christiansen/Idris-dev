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

bad1 : TypedQuote Nat
bad1 = `("nope!")

bad2 : TypedQuote String -> TypedQuote Nat
bad2 str = `(S ~str)

