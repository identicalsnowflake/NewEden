import NewEden.Natural
import NewEden.NaturalTheorems
import NewEden.GMP

import Prelude

-- Just choose an implementation of NaturalProperties (in
-- this case, GMP) and go!

x : Natural GMP
x = 2

y : Natural GMP
y = 102394

z : Natural GMP
z = x * y

main : IO ()
main = putStrLn $ show $ value z

-- Not only can we perform efficient arithmetic with Natural GMP,
-- we can actually reason about it in proofs. See the following example,
-- we have two functions: one which accepts values less than 20, and
-- anther which accepts values less than 10 -- and the latter is able
-- to construct the proof to call the former! Try *that* with regular Integer!

acceptLessThan20 : (x:Natural GMP) -> LessThan x 20 -> ()
acceptLessThan20 x _ = ()

acceptLessThan10 : (x:Natural GMP) -> LessThan x 10 -> ()
acceptLessThan10 x prf =
  acceptLessThan20 x $ lessThanAdditionWeakened prf 10

