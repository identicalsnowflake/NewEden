module NewEden.Natural

import Prelude.Either
import public Prelude.Uninhabited

import public NewEden.Algebra
import public NewEden.NaturalAxioms
import public NewEden.NaturalPropertiesHelpers -- compiler bug #144; can't use private in types

{- Natural
   
   Natural p is a natural number expressed in terms of operations on a given
   set of NaturalProperties p.
   
   Everything else in this module is expressing the axioms given in 
   NaturalProperties in terms of operations on Natural p, so now
   we can use Natural p much the same as we would the 'normal' numeric types.
-}

data Natural : NaturalProperties t -> Type where
  MkNatural : (n:NaturalProperties t) -> (a:t) -> Natural n

value : {p:NaturalProperties t} -> Natural p -> t
value {p} (MkNatural p x) = x

properties : {p:NaturalProperties t} -> Natural p -> NaturalProperties t
properties (MkNatural p _) = p

(+) : {p:NaturalProperties t} -> Natural p -> Natural p -> Natural p
(+) {p} (MkNatural p x) (MkNatural p y) =
  MkNatural p $ privatePlus p x y

(*) : {p:NaturalProperties t} -> Natural p -> Natural p -> Natural p
(*) {p} (MkNatural p x) (MkNatural p y) =
  MkNatural p $ privateMultiply p x y

{- fromInteger
   
   This is the first place we see the real power of an axiomatic implementation.
   Here we are able to construct arbitrary natural numbers and put them in the 
   compiler's head in *logarithmic* space (rather than linear space, like the Peano Nat).
-}

mutual

  -- two functions should not be necessary. serious buggage going on with the compiler here

  fromIntegerHelper : Integer -> Natural p
  fromIntegerHelper x = case x of
    0 => (MkNatural p (one p) + (MkNatural p (one p))) * (assert_total $ fromInteger (prim__sdivBigInt x 2))
    _ => (MkNatural p (one p)) + (assert_total $ fromInteger (prim__subBigInt x 1))
  
  fromInteger : Integer -> Natural p
  fromInteger x =
    case x of
    0 => MkNatural p (zero p)
    1 => MkNatural p (one p)
    m => fromIntegerHelper $ assert_total (prim__sremBigInt m 2)

-- force resolution of 0 to Natural p, since occasionally 0 is
-- ambiguous (e.g., right below in zeroIsNotOne)
Z : (p:NaturalProperties t) -> Natural p
Z p = 0

zeroIsNotOne : (p:NaturalProperties t) -> (Z p = 1 -> Void)
zeroIsNotOne p =
  let prf = NewEden.NaturalPropertiesHelpers.privateZeroIsNotOne p in
  (\given => prf $ equalityMap value given)

plusCommutative : (p:NaturalProperties t) -> CommutativeFunction (Natural p) (+)
plusCommutative p =
  let (MkCommutativeFunction _ prf) = NewEden.NaturalPropertiesHelpers.privatePlusCommutative p in
  MkCommutativeFunction
    (+)
    (\(MkNatural p x),(MkNatural p y) => equalityMap (MkNatural p) $ prf x y)

plusAssociative : (p:NaturalProperties t) -> AssociativeFunction (Natural p) (+)
plusAssociative p =
  let (MkMonoid af _ _ _) = NewEden.NaturalPropertiesHelpers.privatePlusMonoid p in
  let (MkAssociativeFunction _ prf) = af in
  MkAssociativeFunction
    (+)
    (\(MkNatural p x),(MkNatural p y),(MkNatural p z) => equalityMap (MkNatural p) $ prf x y z)

plusMonoid : (p:NaturalProperties t) -> NewEden.Algebra.Monoid (Natural p) (+) 0
plusMonoid P =
  let (MkMonoid _ _ p1 p2) = NewEden.NaturalPropertiesHelpers.privatePlusMonoid P in
  MkMonoid
    (plusAssociative P)
    (Z P)
    (\(MkNatural P x) => equalityMap (MkNatural P) $ p1 x)
    (\(MkNatural P x) => equalityMap (MkNatural P) $ p2 x)

plusLacksInverses : (p:NaturalProperties t) -> StrictMonoid $ NewEden.Natural.plusMonoid p
plusLacksInverses P =
  let (MkStrictMonoid _ prf) = NewEden.NaturalPropertiesHelpers.privatePlusLacksInverses P in
  MkStrictMonoid
    (plusMonoid P)
    (\(MkNatural P x),(MkNatural P y),given =>
      let given' = equalityMap value $ given in
      equalityMap (MkNatural P) $ prf x y given'
    )

plusMonomorphic : (p:NaturalProperties t) -> ((n:Natural p) -> MonomorphicFunction $ (+) n)
plusMonomorphic p =
  let g = NewEden.NaturalPropertiesHelpers.privatePlusMonomorphic p in
  (\(MkNatural p x) =>
    let (MkMonomorphicFunction _ prf) = g x in
    MkMonomorphicFunction
      ((+) (MkNatural p x))
      (\(MkNatural p y),(MkNatural p z),given =>
        equalityMap (MkNatural p) $ prf y z (equalityMap value given)
      )
  )

multiplyCommutative : (p:NaturalProperties t) -> CommutativeFunction (Natural p) (*)
multiplyCommutative p =
  let (MkCommutativeFunction _ prf) = NewEden.NaturalPropertiesHelpers.privateMultiplyCommutative p in
  MkCommutativeFunction
    (*)
    (\(MkNatural p x),(MkNatural p y) => equalityMap (MkNatural p) $ prf x y)

multiplyAssociative : (p:NaturalProperties t) -> AssociativeFunction (Natural p) (*)
multiplyAssociative p =
  let (MkMonoid af _ _ _) = NewEden.NaturalPropertiesHelpers.privateMultiplyMonoid p in
  let (MkAssociativeFunction _ prf) = af in
  MkAssociativeFunction
    (*)
    (\(MkNatural p x),(MkNatural p y),(MkNatural p z) => equalityMap (MkNatural p) $ prf x y z)

multiplyMonoid : (p:NaturalProperties t) -> NewEden.Algebra.Monoid (Natural p) (*) 1
multiplyMonoid P =
  let (MkMonoid _ _ p1 p2) = NewEden.NaturalPropertiesHelpers.privateMultiplyMonoid P in
  MkMonoid
    (multiplyAssociative P)
    1
    (\(MkNatural P x) => equalityMap (MkNatural P) $ p1 x)
    (\(MkNatural P x) => equalityMap (MkNatural P) $ p2 x)

multiplyLacksInverses : (p:NaturalProperties t) -> StrictMonoid $ NewEden.Natural.multiplyMonoid p
multiplyLacksInverses P =
  let (MkStrictMonoid _ prf) = NewEden.NaturalPropertiesHelpers.privateMultiplyLacksInverses P in
  MkStrictMonoid
    (multiplyMonoid P)
    (\(MkNatural P x),(MkNatural P y),given =>
      let given' = equalityMap value $ given in
      equalityMap (MkNatural P) $ prf x y given'
    )

multiplyMonomorphic : (p:NaturalProperties t) -> ((n:Natural p) -> MonomorphicFunction $ (*) n)
multiplyMonomorphic p =
  let g = NewEden.NaturalPropertiesHelpers.privateMultiplyMonomorphic p in
  (\(MkNatural p x) =>
    let (MkMonomorphicFunction _ prf) = g x in
    MkMonomorphicFunction
      ((*) (MkNatural p x))
      (\(MkNatural p y),(MkNatural p z),given =>
        equalityMap (MkNatural p) $ prf y z (equalityMap value given)
      )
  )

multiplyByZeroIsZero : (p:NaturalProperties t) -> ((a:(Natural p)) -> a * 0 = 0)
multiplyByZeroIsZero P =
  let prf = NewEden.NaturalPropertiesHelpers.privateMultiplyByZero P in
  (\(MkNatural P x) => equalityMap (MkNatural P) $ prf x)

multiplyDistributive : (p:NaturalProperties t) -> ((a:Natural p) -> (b:Natural p) -> (c:Natural p) -> a * (b + c) = (a * b) + (a * c))
multiplyDistributive p =
  let prf = NewEden.NaturalPropertiesHelpers.privateDistributiveProperty p in
  (\(MkNatural p x),(MkNatural p y),(MkNatural p z) =>
    equalityMap (MkNatural p) $ prf x y z
  )

naturalNoNumbersBetweenZeroAndOne : (p:NaturalProperties t) -> ((a:Natural p) -> (b:Natural p) -> (p1:(a = 0 -> Void)) -> (p2: a + b = 1) -> a = 1)
naturalNoNumbersBetweenZeroAndOne P =
  let lemmaSequence = NewEden.NaturalPropertiesHelpers.privateSequenceProperty P in
  (\(MkNatural P x),(MkNatural P y),given1,given2 =>
    let given1' = (\lemma => given1 $ equalityMap (MkNatural P) lemma) in
    let given2' = equalityMap value given2 in
    equalityMap (MkNatural P) $ lemmaSequence x y given1' given2'
  )

data LessThan : (a:Natural p) -> (b:Natural p) -> Type where
  MkLessThan : (a:Natural p) -> (b:Natural p) -> (c ** ((a + c = b), (c = 0 -> Void))) -> LessThan a b

data Trichotomy : (a:Type) -> (b:Type) -> (c:Type) -> Type where
  Left : {a:Type} -> {b:Type} -> {c:Type} -> (x:a) -> Trichotomy a b c
  Middle : {a:Type} -> {b:Type} -> {c:Type} -> (x:b) -> Trichotomy a b c
  Right : {a:Type} -> {b:Type} -> {c:Type} -> (x:c) -> Trichotomy a b c

compare : ((a:Natural p) -> (b:Natural p) -> Trichotomy (LessThan a b) (a = b) (LessThan b a))
compare (MkNatural p x) (MkNatural p y) =
  let prf = NewEden.NaturalPropertiesHelpers.privateCompare p in
  case prf x y of
    Left h => Middle $ equalityMap (MkNatural p) h
    Right r => case r of
      Left (c**(h,prf')) =>
        let lt = MkLessThan (MkNatural p x) (MkNatural p y) in
        Left $ lt ((MkNatural p c) ** ((equalityMap (MkNatural p) h),
                  (\prf'' => prf' $ equalityMap value prf'')))
      Right (c**(r,prf')) =>
        let lt = MkLessThan (MkNatural p y) (MkNatural p x) in
        Right $ lt ((MkNatural p c) ** ((equalityMap (MkNatural p) r),(\prf'' => prf' $ equalityMap value prf'')))

(-) : (a:Natural p) -> (b:Natural p) -> {auto prf:((LessThan a b) -> Void)} -> Natural p
(-) {prf} a b = case compare a b of
  Left x => absurd (prf x)
  Middle _ => 0
  Right (MkLessThan _ _ (c ** _)) => c

