import NewEden.Natural
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

