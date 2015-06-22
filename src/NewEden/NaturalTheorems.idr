import NewEden.Natural

{- Natural Theorems
   
   Basic theorems about the natural numbers expressed in
   terms of operations on Natural p.
   
-}

addToBothSides : (n : Natural p) -> a = b -> a + n = b + n
addToBothSides _ Refl = Refl

addRemoveBothSides : (n : Natural p) -> n + a = n + b -> a = b
addRemoveBothSides {a} {b} n prf =
  let (MkMonomorphicFunction _ mono) = plusMonomorphic p n in
  mono a b prf

multiplyBothSidesBy : (n : Natural p) -> a = b -> a * n = b * n
multiplyBothSidesBy _ Refl = Refl

multiplyRemoveBothSides : (n : Natural p) -> n * a = n * b -> a = b
multiplyRemoveBothSides {a} {b} n prf =
  let (MkMonomorphicFunction _ mono) = multiplyMonomorphic p n in
  mono a b prf

pluscom : {a:Natural p}
        -> a + b = c -> b + a = c
pluscom {p} {a} {b} given =
  let (MkCommutativeFunction _ prf) = plusCommutative p in
  let apply = prf b a in
  transitivity apply given

plusass : {a:Natural p}
        -> a + (b + c) = d -> a + b + c = d
plusass {p} {a} {b} {c} given =
  let (MkAssociativeFunction _ prf) = plusAssociative p in
  let apply = prf a b c in
  transitivity (symmetric apply) given

plusass' : {a:Natural p}
         -> a + b + c = d -> a + (b + c) = d
plusass' {p} {a} {b} {c} given =
  let (MkAssociativeFunction _ prf) = plusAssociative p in
  let apply = prf a b c in
  transitivity apply given

multcom : {a : Natural p}
        -> a * b = c -> b * a = c
multcom {p} {a} {b} given =
  let (MkCommutativeFunction _ prf) = multiplyCommutative p in
  let apply = prf b a in
  transitivity apply given

multass : {a : Natural p}
        -> a * (b * c) = d -> a * b * c = d
multass {p} {a} {b} {c} given =
  let (MkAssociativeFunction _ prf) = multiplyAssociative p in
  let apply = prf a b c in
  transitivity (symmetric apply) given
  
multass' : {a : Natural p}
        -> a * b * c = d -> a * (b * c) = d
multass' {p} {a} {b} {c} given =
  let (MkAssociativeFunction _ prf) = multiplyAssociative p in
  let apply = prf a b c in
  transitivity apply given

nothingIsLessThanZero : (a:Natural p) -> LessThan a 0 -> Void
nothingIsLessThanZero {p} a (MkLessThan a (Z p) (c ** (prf,cNonZero))) =
  let (MkCommutativeFunction _ comm) = NewEden.Natural.plusCommutative p in
  let equation = symmetric $ comm a c in
  let cPlusAIsZero = transitivity equation prf in
  let (MkStrictMonoid _ noInverses) = NewEden.Natural.plusLacksInverses p in 
  let cIsZero = noInverses c a cPlusAIsZero in
  cNonZero cIsZero

lessThanImpliesNotEqual : (a:Natural p) -> (b:Natural p) -> LessThan a b -> a = b -> Void
lessThanImpliesNotEqual a b (MkLessThan a b (c ** (aPlusCIsB,cNonZero))) aEqualsb =
  let step = symmetric aPlusCIsB in
  let step2 = transitivity aEqualsb step in
  let (MkMonoid _ _ mn _) = plusMonoid p in
  let step3 = mn a in
  let step4 = transitivity step3 step2 in
  let mono = plusMonomorphic p in
  let (MkMonomorphicFunction ((+) a) monoprf) = mono a in
  let fin = monoprf 0 c in
  let cIsZero = fin step4 in
  cNonZero $ symmetric cIsZero

lessThanNotSymmetric : {a:Natural p} -> {b:Natural p} -> LessThan a b -> LessThan b a -> Void
lessThanNotSymmetric {p} (MkLessThan a b (c1 ** (prf1,c1NonZero))) (MkLessThan b a (c2 ** (prf2,c2NonZero))) =
  let (MkCommutativeFunction _ comm) = plusCommutative p in
  let (MkMonoid _ _ mon _) = plusMonoid p in
  let (MkMonomorphicFunction _ mono) = plusMonomorphic p $ b in
  let (MkAssociativeFunction _ ass) = plusAssociative p in
  let comm' = symmetric $ comm a c1 in
  let s1 = substitution ((+) c1) (symmetric prf2) (transitivity comm' prf1) in
  let s2 = symmetric $ comm c1 (b + c2) in
  let s3 = transitivity s2 s1 in
  let but4 = mon b in
  let so5 = transitivity but4 $ symmetric s3 in
  let byMono = mono 0 (c2 + c1) in
  let ass' = ass b c2 c1 in
  let prepare = transitivity so5 (symmetric ass') in
  let therefore = byMono prepare in
  let but6 = mon c2 in
  let (MkMonomorphicFunction _ monoc2) = plusMonomorphic p $ c2 in
  let monoapp = monoc2 0 c1 in
  let (MkStrictMonoid _ noInverses) = plusLacksInverses p in
  let so6 = noInverses c2 c1 in
  let c2IsZero = so6 (symmetric therefore) in
  c2NonZero c2IsZero

lessThanIsTransitive : {x:Natural p} -> {y:Natural p} -> {z:Natural p} ->
                       LessThan x y -> LessThan y z -> LessThan x z
lessThanIsTransitive {p} (MkLessThan x y (c1 ** (eq1,c1NonZero))) (MkLessThan y z (c2 ** (eq2,c2NonZero)))=
  case compare x z of
    Left prf => prf
    Middle xIsZ =>
      let sub = pluscom $ substitution ((+) c1) xIsZ (pluscom eq1) in
      let zLessThany = MkLessThan z y (c1 ** (sub,c1NonZero)) in
      let yLessThanz = MkLessThan y z (c2 ** (eq2,c2NonZero)) in
      absurd $ lessThanNotSymmetric yLessThanz zLessThany
    Right (MkLessThan z x (c3 ** (eq3,c3NonZero))) =>
      let sub = substitution ((+) c1) (symmetric eq3) (pluscom eq1) in
      let s0 = pluscom sub in
      let c4 = c3 + c1 in
      let c4e:(c4 = c3 + c1) = Refl in
      let (MkStrictMonoid _ noInverses) = plusLacksInverses p in
      let c4nz = (\c4z => c3NonZero $ noInverses c3 c1 c4z) in
      let s1 = plusass' s0 in
      let zlty = MkLessThan z y ((c3+c1) ** (s1,c4nz)) in
      let yltz = MkLessThan y z (c2 ** (eq2,c2NonZero)) in
      absurd $ lessThanNotSymmetric zlty yltz

lessThanAdditionWeakened : LessThan x y -> (z : Natural p) -> LessThan x (y + z)
lessThanAdditionWeakened {p} {x} {y} (MkLessThan x y (c ** (xpyic,cNotZero))) z =
  let (MkStrictMonoid _ noinv) = plusLacksInverses p in
  let cPlusZIsZeroImpliesCIsZero = noinv c z in
  let cPlusZNotZero = (\sumZero => cNotZero $ cPlusZIsZeroImpliesCIsZero sumZero) in
  let target = addToBothSides z xpyic in
  let target' = plusass' target in
  MkLessThan x (y + z) ((c + z) ** (target',cPlusZNotZero))

