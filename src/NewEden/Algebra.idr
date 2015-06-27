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

data Coproduct : (C : Type) -> Type where
  MkCoproduct :
      {C : Type}
   -> (coproduct : C -> C -> C)
   -> ((x1 : C) -> (x2 : C) ->
        (
           i1 : C -> C **
           (
             i2 : C -> C **
             (
               i1 x1 = coproduct x1 x2
             , i2 x2 = coproduct x1 x2
             , (x : C) ->
               (
                 f1 : C -> C **
                 (
                   f2 : C -> C **
                   (
                     f1 x1 = x
                   , f2 x2 = x
                   , (f : C -> C **
                     (
                       f $ coproduct x1 x2 = x
                     , ((c : C) -> f1 c = f (i1 c))
                     , ((c : C) -> f2 c = f (i2 c))
                     , ((f' : C -> C)
                         -> f' $ coproduct x1 x2 = x
                         -> ((c : C) -> f1 c = f' (i1 c))
                         -> ((c : C) -> f2 c = f' (i2 c))
                         -> ((n : C) -> f' c = f c)
                       )
                     ))
                   )
                 )
               )
             )
           )
        )
      )
   -> Coproduct C

data Product : (C : Type) -> Type where
  MkProduct :
      {C : Type}
   -> (product : C -> C -> C)
   -> ((x1 : C) -> (x2 : C) ->
       (
         p1 : C -> C **
         (
           p2 : C -> C **
           ((y : C) ->
            (f1 : C -> C) ->
            f1 y = x1 ->
            (f2 : C -> C) ->
            f2 y = x2 ->
            (
              f : C -> C **
              (
                f y = product x1 x2
              , ((c : C) -> p1 (f c) = f1 c)
              , ((c : C) -> p2 (f c) = f2 c)
              , ((f' : C -> C) ->
                 f' y = product x1 x2 ->
                 ((c : C) -> p1 (f' c) = f1 c) ->
                 ((c : C) -> p2 (f' c) = f2 c) ->
                 ((c : C) -> f' c = f c)
                )
              )
            )
           )
         )
       )
      )
   -> Product C

data InitialObject : (C : Type) -> Type where
  MkInitialObject :
      {C : Type}
   -> (initialObject : C)
   -> ((x : C) ->
       (f : C -> C **
        ( (f initialObject = x)
        , ((f' : C -> C) ->
           f' initialObject = x ->
           ((c : C) -> f' c = f c)
          )
        )
       )
      )
   -> InitialObject C

data TerminalObject : (C : Type) -> Type where
  MkTerminalObject :
      {C : Type}
   -> (terminalObject : C)
   -> ((x : C) ->
       (f : C -> C **
        ((f x = terminalObject)
        , ((f' : C -> C) ->
           f' x = terminalObject ->
           ((c : C) -> f' c = f c)
          )
        )
       )
      )
   -> TerminalObject C

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

