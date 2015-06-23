import NewEden.Natural
import Prelude

-- we can also formally prove things about abstract numbers (even large ones)
-- compare it with the standard Nat in the following:

x : Natural p
x = 1487129834719898712935812394810

x' : Nat
x' = 1487129834719898712935812394810

y : Natural p
y = 1234

y' : Nat
y' = 1234

z : Natural p
z = x * y

z' : Nat
z' = x' * y'

-- now let's prove that z is actually x * y...

prf : NewEden.Natural.(*) x y = z
prf = Refl

-- Aaand uncomment these lines if you want the compiler to explode!
-- It can't prove the following because the hacks to replace Nat
-- with efficient stuff aren't available at compile time.
-- But this is no problem for Natural p, since Natural p expresses
-- numbers in terms of a logarithmic number of axiomatic expessions!

-- prf' : (*) x' y' = z'
-- prf' = Refl

