module NewEden.Implementations.Int64

import Prelude

import NewEden.Algebra
import NewEden.NaturalAxioms

{- Int64
   
   Axioms for assuming that your processor's native Int64 instructions 
   behave as natural numbers.
   
   Unlike GMP, this assumption is absolutely false.
   
   Int64 will exhibit unnatural behavior when used on large numbers, so 
   use at your own risk!

-}

data UInt : Type where
  MkUInt : (a : Int) -> (isNonNegative : a < 0 = False)  -> UInt

instance Show UInt where
  show (MkUInt x _) = show x

UIntplus : UInt -> UInt -> UInt
UIntplus (MkUInt a _) (MkUInt b _) = MkUInt (a + b) (believe_me ())

minus : UInt -> UInt -> UInt
minus (MkUInt a _) (MkUInt b _) = MkUInt (a - b) (believe_me ())

UIntmultiply : UInt -> UInt -> UInt
UIntmultiply (MkUInt a _) (MkUInt b _) = MkUInt (a * b) (believe_me ())

UIntzero : UInt
UIntzero = MkUInt 0 Refl

UIntone : UInt
UIntone = MkUInt 1 Refl

UIntplusAssociative : AssociativeFunction UInt UIntplus
UIntplusAssociative = MkAssociativeFunction UIntplus (\_,_,_ => believe_me ())

UIntplusMonoid : Monoid UInt UIntplus UIntzero
UIntplusMonoid = MkMonoid UIntplusAssociative UIntzero (\_ => believe_me ()) (\_ => believe_me ())

UIntmultiplyAssociative : AssociativeFunction UInt UIntmultiply
UIntmultiplyAssociative = MkAssociativeFunction UIntmultiply (\_,_,_ => believe_me ())

UIntmultiplyMonoid : Monoid UInt UIntmultiply UIntone
UIntmultiplyMonoid = MkMonoid UIntmultiplyAssociative UIntone (\_ => believe_me ()) (\_ => believe_me ())

UIntcompare : (a:UInt) -> (b:UInt) -> Either (a = b) (Either ((c ** ((UIntplus a c = b, (c = UIntzero -> Void))))) (c ** ((UIntplus b c = a, (c = UIntzero -> Void)))))
UIntcompare (MkUInt x xp) (MkUInt y yp) =
  case x == y of
    True => Left (believe_me ())
    _ => case x < y of
           True => Right $ Left ((minus (MkUInt y yp) (MkUInt x xp)) ** (believe_me (), believe_me ()))
           False => Right $ Right ((minus (MkUInt x xp) (MkUInt y yp)) ** (believe_me (), believe_me ()))


Int64 : NaturalProperties UInt
Int64 =
  ProofNaturalProperties
      UIntzero
      UIntone
      (believe_me ())
      UIntplus
      (MkCommutativeFunction UIntplus (believe_me ()))
      UIntplusMonoid
      (MkStrictMonoid UIntplusMonoid (\_,_,_ => believe_me ()))
      (\x => MkMonomorphicFunction (UIntplus x) (\_,_,_ => believe_me ()))
      UIntmultiply
      (MkCommutativeFunction UIntmultiply (believe_me ()))
      UIntmultiplyMonoid
      (MkStrictMonoid UIntmultiplyMonoid (\_,_,_ => believe_me ()))
      (\x => MkMonomorphicFunction (UIntmultiply x) (\_,_,_ => believe_me ()))
      (\_ => believe_me ())
      (\_,_,_ => believe_me ())
      (\_,_,_,_ => believe_me ())
      UIntcompare



