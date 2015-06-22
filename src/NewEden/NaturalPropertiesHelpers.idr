module NewEden.NaturalPropertiesHelpers

import Prelude.Either

import NewEden.Algebra
import NewEden.NaturalAxioms

{- Internal -
   This is intended to be a private module which just provides internal
   plumbing used to create the properties of Natural p, but due to issue #144,
   these functions must be public, so for now just use private prefixes.
-}

zero : NaturalProperties t -> t
zero (ProofNaturalProperties Zero _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = Zero

one : NaturalProperties t -> t
one (ProofNaturalProperties _ One _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = One

privateZeroIsNotOne : (p:NaturalProperties t) -> (zero p = one p -> Void)
privateZeroIsNotOne (ProofNaturalProperties _ _ lemmaDistinction _ _ _ _ _ _ _ _ _ _ _ _ _ _) prf = lemmaDistinction prf

privatePlus : NaturalProperties t -> (t -> t -> t)
privatePlus (ProofNaturalProperties _ _ _ plus _ _ _ _ _ _ _ _ _ _ _ _ _) = plus

privatePlusCommutative : (p:NaturalProperties t) -> CommutativeFunction t (privatePlus p)
privatePlusCommutative (ProofNaturalProperties _ _ _ _ lemmaPlusCommut _ _ _ _ _ _ _ _ _ _ _ _) = lemmaPlusCommut

privatePlusMonoid : (p:NaturalProperties t) -> Monoid t (privatePlus p) (zero p)
privatePlusMonoid (ProofNaturalProperties _ _ _ _ _ lemmaPlusMonoid _ _ _ _ _ _ _ _ _ _ _) = lemmaPlusMonoid

privatePlusLacksInverses : (p:NaturalProperties t) -> StrictMonoid $ privatePlusMonoid p
privatePlusLacksInverses (ProofNaturalProperties _ _ _ _ _ _ lemmaPlusNoInverses _ _ _ _ _ _ _ _ _ _) = lemmaPlusNoInverses

privatePlusMonomorphic : (p:NaturalProperties t) -> ((a:t) -> MonomorphicFunction $ privatePlus p a)
privatePlusMonomorphic (ProofNaturalProperties _ _ _ _ _ _ _ lemmaPlusMonomorphic _ _ _ _ _ _ _ _ _) = lemmaPlusMonomorphic

privateMultiply : NaturalProperties t -> (t -> t -> t)
privateMultiply (ProofNaturalProperties _ _ _ _ _ _ _ _ multiply _ _ _ _ _ _ _ _) = multiply

privateMultiplyCommutative : (p:NaturalProperties t) -> CommutativeFunction t (privateMultiply p)
privateMultiplyCommutative (ProofNaturalProperties _ _ _ _ _ _ _ _ _ lemmaMultCommut _ _ _ _ _ _ _) = lemmaMultCommut

privateMultiplyMonoid : (p:NaturalProperties t) -> Monoid t (privateMultiply p) (one p)
privateMultiplyMonoid (ProofNaturalProperties _ _ _ _ _ _ _ _ _ _ lemmaMultMonoid _ _ _ _ _ _) = lemmaMultMonoid

privateMultiplyLacksInverses : (p:NaturalProperties t) -> StrictMonoid $ privateMultiplyMonoid p
privateMultiplyLacksInverses (ProofNaturalProperties _ _ _ _ _ _ _ _ _ _ _ lemmaMultNoInverses _ _ _ _ _) = lemmaMultNoInverses

privateMultiplyMonomorphic : (p:NaturalProperties t) -> ((a:t) -> MonomorphicFunction $ privateMultiply p a)
privateMultiplyMonomorphic (ProofNaturalProperties _ _ _ _ _ _ _ _ _ _ _ _ lemmaMultMonomorphic _ _ _ _) = lemmaMultMonomorphic

privateMultiplyByZero : (p:NaturalProperties t) -> ((a:t) -> (privateMultiply p) a (zero p) = (zero p))
privateMultiplyByZero (ProofNaturalProperties _ _ _ _ _ _ _ _ _ _ _ _ _ lemmaMultByZeroIsZero _ _ _) = lemmaMultByZeroIsZero

privateDistributiveProperty : (p:NaturalProperties t) -> ((a:t) -> (b:t) -> (c:t) -> privateMultiply p a (privatePlus p b c) = privatePlus p (privateMultiply p a b) (privateMultiply p a c))
privateDistributiveProperty (ProofNaturalProperties _ _ _ _ _ _ _ _ _ _ _ _ _ _ lemmaDistributive _ _) = lemmaDistributive

privateSequenceProperty : (p:NaturalProperties t) -> ((a:t) -> (b:t) -> (p1:((a = (zero p) -> Void))) -> (p2: privatePlus p a b = one p) -> a = (one p))
privateSequenceProperty (ProofNaturalProperties _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lemmaSequence _) = lemmaSequence 

privateCompare : (p:NaturalProperties t) -> ((a:t) -> (b:t) -> Either (a = b) (Either (c ** (privatePlus p a c = b, (c = zero p -> Void))) (c ** (privatePlus p b c = a, (c = zero p -> Void)))))
privateCompare (ProofNaturalProperties _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ compare) = compare

