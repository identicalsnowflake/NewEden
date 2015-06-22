module NewEden.GMP

import Prelude

import NewEden.Algebra
import NewEden.NaturalAxioms

{- GMP

   If you assume the GMP implementation is valid, you can use
   Natural GMP by importing this package!

-}

data UInteger : Type where
  MkUInteger : (a : Integer) -> (isNonNegative : a < 0 = False)  -> UInteger

instance Show UInteger where
  show (MkUInteger x _) = show x

GMPplus : UInteger -> UInteger -> UInteger
GMPplus (MkUInteger a _) (MkUInteger b _) = MkUInteger (a + b) (believe_me ())

minus : UInteger -> UInteger -> UInteger
minus (MkUInteger a _) (MkUInteger b _) = MkUInteger (a - b) (believe_me ())

GMPmultiply : UInteger -> UInteger -> UInteger
GMPmultiply (MkUInteger a _) (MkUInteger b _) = MkUInteger (a * b) (believe_me ())

GMPzero : UInteger
GMPzero = MkUInteger 0 Refl

GMPone : UInteger
GMPone = MkUInteger 1 Refl

GMPplusAssociative : AssociativeFunction UInteger GMPplus
GMPplusAssociative = MkAssociativeFunction GMPplus (\_,_,_ => believe_me ())

GMPplusMonoid : Monoid UInteger GMPplus GMPzero
GMPplusMonoid = MkMonoid GMPplusAssociative GMPzero (\_ => believe_me ()) (\_ => believe_me ())

GMPmultiplyAssociative : AssociativeFunction UInteger GMPmultiply
GMPmultiplyAssociative = MkAssociativeFunction GMPmultiply (\_,_,_ => believe_me ())

GMPmultiplyMonoid : Monoid UInteger GMPmultiply GMPone
GMPmultiplyMonoid = MkMonoid GMPmultiplyAssociative GMPone (\_ => believe_me ()) (\_ => believe_me ())

GMPcompare : (a:UInteger) -> (b:UInteger) -> Either (a = b) (Either ((c ** ((GMPplus a c = b, (c = GMPzero -> Void))))) (c ** ((GMPplus b c = a, (c = GMPzero -> Void)))))
GMPcompare (MkUInteger x xp) (MkUInteger y yp) =
  case x == y of
    True => Left (believe_me ())
    _ => case x < y of
           True => Right $ Left ((minus (MkUInteger y yp) (MkUInteger x xp)) ** (believe_me (), believe_me ()))
           False => Right $ Right ((minus (MkUInteger x xp) (MkUInteger y yp)) ** (believe_me (), believe_me ()))


GMP : NaturalProperties UInteger
GMP =
  ProofNaturalProperties
      GMPzero
      GMPone
      (believe_me ())
      GMPplus
      (MkCommutativeFunction GMPplus (believe_me ()))
      GMPplusMonoid
      (MkStrictMonoid GMPplusMonoid (\_,_,_ => believe_me ()))
      (\x => MkMonomorphicFunction (GMPplus x) (\_,_,_ => believe_me ()))
      GMPmultiply
      (MkCommutativeFunction GMPmultiply (believe_me ()))
      GMPmultiplyMonoid
      (MkStrictMonoid GMPmultiplyMonoid (\_,_,_ => believe_me ()))
      (\x => MkMonomorphicFunction (GMPmultiply x) (\_,_,_ => believe_me ()))
      (\_ => believe_me ())
      (\_,_,_ => believe_me ())
      (\_,_,_,_ => believe_me ())
      GMPcompare



