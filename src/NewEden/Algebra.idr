module NewEden.Algebra

%default total

data AssociativeFunction : (t:Type) -> (f:(t -> t -> t)) -> Type where
  MkAssociativeFunction :
      (f:(t -> t -> t))
   -> (prf:((a:t) -> (b:t) -> (c:t) -> f a (f b c) = f (f a b) c))
   -> AssociativeFunction t f

data CommutativeFunction : (t:Type) -> (f:(t -> t -> t)) -> Type where
  MkCommutativeFunction :
      (f:(t -> t -> t))
   -> (prf:((a:t) -> (b:t) -> f a b = f b a))
   -> CommutativeFunction t f

data MonomorphicFunction : (t1 -> t2) -> Type where
  MkMonomorphicFunction :
      (f:(t1 -> t2))
   -> ((a:t1) -> (b:t1) -> f a = f b -> a = b)
   -> MonomorphicFunction f

data Monoid : (t:Type) -> (f:(t -> t -> t)) -> (zero:t) -> Type where
  MkMonoid :
      (lemma:AssociativeFunction t f)
   -> (zero:t)
   -> (prf1:((a:t) -> f a zero = a))
   -> (prf2:((a:t) -> f zero a = a))
   -> Monoid t f zero

-- monoid which is strictly not strong enough to be a group (proven lack of inverses)
data StrictMonoid : (m:Monoid t f z) -> Type where
  MkStrictMonoid :
      (m:Monoid t f z)
   -> (prfNoInverses:((a:t) -> (b:t) -> (p:(f a b = z)) -> (a = z)))
   -> StrictMonoid m

data Group : Monoid t f z -> Type where
  MkGroup :
      (m:Monoid t f z)
   -> (prfInverse:((a:t) -> (b : t ** (f a b = z))))
   -> Group m

data Isomorphism : (t:Type) -> (u:Type) -> (f:(t -> u)) -> (g:(u -> t)) -> Type where
  MkIsomorphism : (t:Type) -> (u:Type) -> (f:(t -> u)) -> (g:(u -> t)) -> ((a:t) -> g (f a) = a) -> ((a:u) -> f (g a) = a) -> Isomorphism t u f g

equalityMap : (f:(t -> u)) -> a = b -> f a = f b
equalityMap f Refl = Refl

transitivity : a = b -> b = c -> a = c
transitivity Refl Refl = Refl

symmetric : a = b -> b = a
symmetric Refl = Refl

substitution : {t1:Type} -> {t2:Type} -> {a:t1} -> {b:t1} -> {c:t2} -> (f:t1 -> t2) -> a = b -> f a = c -> f b = c
substitution _ Refl Refl = Refl

