import NewEden.Natural
import NewEden.Implementations.Int64

{- Int64
   
   At present, this is pretty much completely worthless, as Idris doesn't have
   unboxed primitives, which means you're not gaining any practically significant
   performance by using this over GMP integers.
   
   But hopefully in the future they'll be available. Along with unboxed arrays.

-}

x : Natural Int64
x = 1024

y : Natural Int64
y = 12345

z : Natural Int64
z = x * y + y * x

