import NewEden.Natural
import NewEden.NaturalTheorems
import NewEden.Implementations.GMP

import Prelude

-- some purely abstract numbers

x : Natural p
x = 20129384192384912830491283948120384129348293841923842985102985230948509485923485023948529304859342805298309124982395810293410293

y : Natural p
y = 1023944127934827938571928453485912384029341029348029582039452034951028349023845938451829341829340192384019250192830192580192840

-- we can reason about them, even in their abstract state

z : Natural p
z = x * y

-- and we can use them with respect to some implementation!

render : Natural GMP -> Natural GMP
render n = n + z

main : IO ()
main = do
  putStrLn "Give me a natural number (a big one. come on.)"
  n' <- getLine
  let n = prim__fromStrBigInt n'
  case show n == n' of
    True => do
      putStrLn "Nice! Here's your number n added to our purely abstract (no defined implementation!), internal constants:"
      putStrLn $ show $ value $ render $ fromInteger n
    False => do
      putStrLn "You sure that's a natural number?"
      main

