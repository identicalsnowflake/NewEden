module NewEden.NaturalAxioms

import Prelude.Either

import NewEden.Algebra

{- NaturalProperties -
   A full-fledged, non-recursive, axiomatic description of the natural numbers defined in 
   terms of functions on a given type t.
-}

data NaturalProperties : (t:Type) -> Type where
  ProofNaturalProperties :
      (Zero:t)
   -> (One:t)
   -> (lemmaDistinction: (Zero = One -> Void))
   -> (plus: (t -> t -> t))
   -> (lemmaPlusCommut: CommutativeFunction t plus)
   -> (lemmaPlusMonoid: Monoid t plus Zero)
   -> (lemmaPlusNoInverses: StrictMonoid lemmaPlusMonoid)
   -> (lemmaPlusMonomorphic: ((a:t) -> MonomorphicFunction $ plus a))
   -> (multiply: (t -> t -> t))
   -> (lemmaMultCommut: CommutativeFunction t multiply)
   -> (lemmaMultMonoid: Monoid t multiply One)
   -> (lemmaMultNoInverses: StrictMonoid lemmaMultMonoid)
   -> (lemmaMultiplyMonomorphic: ((a:t) -> MonomorphicFunction $ multiply a))
   -> (lemmaMultByZeroIsZero: ((a:t) -> multiply a Zero = Zero))
   -> (lemmaDistributive: ((a:t) -> (b:t) -> (c:t) -> multiply a (plus b c) = plus (multiply a b) (multiply a c)))
   -> (lemmaSequence: ((a:t) -> (b:t) -> (p1: (a = Zero -> Void)) -> (p2: plus a b = One) -> a = One))
   -> (compare:((a:t) -> (b:t) -> Either (a = b) (Either ((c ** ((plus a c = b, (c = Zero -> Void))))) (c ** ((plus b c = a, (c = Zero -> Void)))))))
   -> NaturalProperties t

