import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter12.Section02Adjunction

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter12

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter11

universe u v

/-! ### 12.3 Arithmetic genus and blowup -/

def chapter12BinomialTwo (m : ℕ) : ℕ :=
  m * (m - 1) / 2

theorem chapter12_two_mul_binomialTwo (m : ℕ) :
    2 * chapter12BinomialTwo m = m * (m - 1) := by
  sorry

structure Chapter12StrictTransformCurveData
    {X Y : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter11PicardTheory Y.carrier]
    [Chapter12IntersectionTheory X] [Chapter12IntersectionTheory Y]
    {s : Chapter12ClosedPoint X}
    (B : Chapter12PointBlowup X Y s)
    (D : Chapter12Curve X) (m : ℕ) where
  curve : Chapter12Curve Y
  divisor_formula : chapter12DivisorLinearEquiv curve.divisor
    (chapter12StrictTransformDivisor B D.divisor m)
  multiplicity_at_center : ℕ
  multiplicity_at_center_eq_parameter : multiplicity_at_center = m
  multiplicity_at_center_is_order_of_vanishing : Prop
  smoothBranchAtCenter : Prop
  smooth_branch_multiplicity : smoothBranchAtCenter → m = 1
  proper_strict_transform : Prop

def chapter12CurveAdjunctionIdentity
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    [Chapter12IntersectionTheory X]
    (P : Chapter12RelativeLCIPresentation X)
    (K : Chapter12RelativeCanonicalDivisor P)
    (D : Chapter12Curve X)
    [Chapter12CurveEulerCharacteristicTheory D] : Prop :=
  2 * chapter12ArithmeticGenus D - 2 =
    chapter12Intersection K.divisor D + chapter12SelfIntersection D

theorem chapter12_arithmetic_genus_strict_transform
    {X Y : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter11PicardTheory Y.carrier]
    [Chapter12IntersectionTheory X] [Chapter12IntersectionTheory Y]
    {s : Chapter12ClosedPoint X}
    (B : Chapter12PointBlowup X Y s)
    (D : Chapter12Curve X) (m : ℕ)
    [Chapter12CurveEulerCharacteristicTheory D]
    (T : Chapter12StrictTransformCurveData B D m)
    [Chapter12CurveEulerCharacteristicTheory T.curve]
    (P : Chapter12RelativeLCIPresentation X)
    (Q : Chapter12RelativeLCIPresentation Y)
    (K : Chapter12RelativeCanonicalDivisor P)
    (L : Chapter12RelativeCanonicalDivisor Q)
    (hD : chapter12CurveAdjunctionIdentity P K D)
    (hT : chapter12CurveAdjunctionIdentity Q L T.curve)
    (hK : chapter12CanonicalBlowupFormula B K L) :
    chapter12ArithmeticGenus T.curve =
      chapter12ArithmeticGenus D -
        (chapter12BinomialTwo m : ℤ) * (B.residueDegree : ℤ) := by
  sorry

theorem chapter12_arithmetic_genus_strict_transform_expanded
    {X Y : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter11PicardTheory Y.carrier]
    [Chapter12IntersectionTheory X] [Chapter12IntersectionTheory Y]
    {s : Chapter12ClosedPoint X}
    (B : Chapter12PointBlowup X Y s)
    (D : Chapter12Curve X) (m : ℕ)
    [Chapter12CurveEulerCharacteristicTheory D]
    (T : Chapter12StrictTransformCurveData B D m)
    [Chapter12CurveEulerCharacteristicTheory T.curve]
    (P : Chapter12RelativeLCIPresentation X)
    (Q : Chapter12RelativeLCIPresentation Y)
    (K : Chapter12RelativeCanonicalDivisor P)
    (L : Chapter12RelativeCanonicalDivisor Q)
    (hD : chapter12CurveAdjunctionIdentity P K D)
    (hT : chapter12CurveAdjunctionIdentity Q L T.curve)
    (hK : chapter12CanonicalBlowupFormula B K L) :
    2 * chapter12ArithmeticGenus T.curve - 2 =
      2 * chapter12ArithmeticGenus D - 2 -
        (m : ℤ) * ((m : ℤ) - 1) * (B.residueDegree : ℤ) := by
  sorry

theorem chapter12_smooth_branch_genus_unchanged
    {X Y : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter11PicardTheory Y.carrier]
    [Chapter12IntersectionTheory X] [Chapter12IntersectionTheory Y]
    {s : Chapter12ClosedPoint X}
    (B : Chapter12PointBlowup X Y s)
    (D : Chapter12Curve X) (m : ℕ)
    [Chapter12CurveEulerCharacteristicTheory D]
    (T : Chapter12StrictTransformCurveData B D m)
    [Chapter12CurveEulerCharacteristicTheory T.curve]
    (hsmooth : T.smoothBranchAtCenter)
    (P : Chapter12RelativeLCIPresentation X)
    (Q : Chapter12RelativeLCIPresentation Y)
    (K : Chapter12RelativeCanonicalDivisor P)
    (L : Chapter12RelativeCanonicalDivisor Q)
    (hD : chapter12CurveAdjunctionIdentity P K D)
    (hT : chapter12CurveAdjunctionIdentity Q L T.curve)
    (hK : chapter12CanonicalBlowupFormula B K L) :
    chapter12ArithmeticGenus T.curve = chapter12ArithmeticGenus D := by
  sorry

theorem chapter12_rational_double_point_genus_drop
    {X Y : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter11PicardTheory Y.carrier]
    [Chapter12IntersectionTheory X] [Chapter12IntersectionTheory Y]
    {s : Chapter12ClosedPoint X}
    (B : Chapter12PointBlowup X Y s)
    (D : Chapter12Curve X) (m : ℕ)
    [Chapter12CurveEulerCharacteristicTheory D]
    (T : Chapter12StrictTransformCurveData B D m)
    [Chapter12CurveEulerCharacteristicTheory T.curve]
    (hm : m = 2) (hd : B.residueDegree = 1)
    (P : Chapter12RelativeLCIPresentation X)
    (Q : Chapter12RelativeLCIPresentation Y)
    (K : Chapter12RelativeCanonicalDivisor P)
    (L : Chapter12RelativeCanonicalDivisor Q)
    (hD : chapter12CurveAdjunctionIdentity P K D)
    (hT : chapter12CurveAdjunctionIdentity Q L T.curve)
    (hK : chapter12CanonicalBlowupFormula B K L) :
    chapter12ArithmeticGenus T.curve = chapter12ArithmeticGenus D - 1 := by
  sorry

/-! The incidence with the exceptional curve is retained as separate data;
it affects the transformed configuration even when the genus formula above
has already fixed the arithmetic-genus drop. -/

structure Chapter12StrictTransformExceptionalIncidence
    {X Y : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter11PicardTheory Y.carrier]
    [Chapter12IntersectionTheory X] [Chapter12IntersectionTheory Y]
    {s : Chapter12ClosedPoint X}
    (B : Chapter12PointBlowup X Y s)
    (T : Chapter12Curve Y) where
  meetsExceptional : Prop
  localIntersectionWithExceptional : ℕ
  incidenceDescription : Prop

/-! ### Structure sheaves and the arithmetic genus of the whole fiber -/

def chapter12StructureSheaf (X : Chapter12ArithmeticSurface) : X.carrier.Modules :=
  SheafOfModules.unit X.carrier.ringCatSheaf

/- LOCAL_DEPENDENCY_GUESS: the pinned derived-pushforward API does not expose
the degree-one direct image and the infinitesimal-neighborhood filtration in a
form reusable by this chapter. -/
structure Chapter12ExceptionalNeighborhoodFiltrationData
    {X Y : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter11PicardTheory Y.carrier]
    [Chapter12IntersectionTheory X] [Chapter12IntersectionTheory Y]
    {s : Chapter12ClosedPoint X}
    (B : Chapter12PointBlowup X Y s)
    [Chapter11PicardTheory B.exceptional.carrier] where
  quotientLineBundle : ℕ → Chapter11LineBundle B.exceptional.carrier
  quotient_is_projectiveLine_twist : ∀ _n : ℕ, Prop
  twistDegree : ℕ → ℤ
  twistDegree_eq_nat : ∀ n, twistDegree n = n
  firstCohomologyDimension : ℕ → ℕ
  firstCohomologyDimension_eq_zero : ∀ n, firstCohomologyDimension n = 0

structure Chapter12BlowupStructureSheafData
    {X Y : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter11PicardTheory Y.carrier]
    [Chapter12IntersectionTheory X] [Chapter12IntersectionTheory Y]
    {s : Chapter12ClosedPoint X}
    (B : Chapter12PointBlowup X Y s)
    [Chapter11PicardTheory B.exceptional.carrier] where
  pushforwardStructureSheafIso :
    (Scheme.Modules.pushforward B.map).obj (chapter12StructureSheaf Y) ≅
      chapter12StructureSheaf X
  higherDirectImageR1_vanishes : Prop
  exceptionalNeighborhoodFiltration :
    Chapter12ExceptionalNeighborhoodFiltrationData B

theorem chapter12_exceptional_neighborhood_first_cohomology_vanishes
    {X Y : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter11PicardTheory Y.carrier]
    [Chapter12IntersectionTheory X] [Chapter12IntersectionTheory Y]
    {s : Chapter12ClosedPoint X}
    (B : Chapter12PointBlowup X Y s)
    [Chapter11PicardTheory B.exceptional.carrier]
    (R : Chapter12BlowupStructureSheafData B) (n : ℕ) :
    R.exceptionalNeighborhoodFiltration.firstCohomologyDimension n = 0 :=
  R.exceptionalNeighborhoodFiltration.firstCohomologyDimension_eq_zero n

def chapter12_point_blowup_pushes_forward_structure_sheaf
    {X Y : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter11PicardTheory Y.carrier]
    [Chapter12IntersectionTheory X] [Chapter12IntersectionTheory Y]
    {s : Chapter12ClosedPoint X}
    (B : Chapter12PointBlowup X Y s)
    [Chapter11PicardTheory B.exceptional.carrier]
    (R : Chapter12BlowupStructureSheafData B) :
    (Scheme.Modules.pushforward B.map).obj (chapter12StructureSheaf Y) ≅
      chapter12StructureSheaf X :=
  R.pushforwardStructureSheafIso

theorem chapter12_point_blowup_R1_structure_sheaf_vanishes
    {X Y : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter11PicardTheory Y.carrier]
    [Chapter12IntersectionTheory X] [Chapter12IntersectionTheory Y]
    {s : Chapter12ClosedPoint X}
    (B : Chapter12PointBlowup X Y s)
    [Chapter11PicardTheory B.exceptional.carrier]
    (R : Chapter12BlowupStructureSheafData B) :
    R.higherDirectImageR1_vanishes :=
  by sorry

structure Chapter12FiberGenusPreservationData
    {X Y : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter11PicardTheory Y.carrier]
    [Chapter12IntersectionTheory X] [Chapter12IntersectionTheory Y]
    {s : Chapter12ClosedPoint X}
    (B : Chapter12PointBlowup X Y s) where
  fiber : Chapter12CartierDivisor X
  fiber_is_scheme_theoretic : Prop
  totalTransform : Chapter12CartierDivisor Y
  totalTransform_is_pullback :
    chapter12DivisorLinearEquiv totalTransform
      (chapter12PullbackDivisor B.map fiber)
  transformedFiber : Chapter12CartierDivisor Y
  transformedFiber_is_scheme_theoretic_fiber : Prop
  transformedFiber_is_totalTransform :
    chapter12DivisorLinearEquiv transformedFiber totalTransform
  fiberEulerCharacteristic : ℤ
  transformedFiberEulerCharacteristic : ℤ
  totalTransformEulerCharacteristic : ℤ
  fiberEulerCharacteristic_is_structure_sheaf : Prop
  transformedFiberEulerCharacteristic_is_structure_sheaf : Prop
  totalTransformEulerCharacteristic_is_structure_sheaf : Prop
  totalTransform_same_EulerCharacteristic :
    totalTransformEulerCharacteristic = fiberEulerCharacteristic
  transformedFiber_same_EulerCharacteristic :
    transformedFiberEulerCharacteristic = totalTransformEulerCharacteristic
  tensorByInverseFiber : X.carrier.Modules
  tensorByInverseFiber_identification : Prop
  fiberQuotient : X.carrier.Modules
  fiberQuotient_identification : Prop
  tensorInclusion : tensorByInverseFiber ⟶ chapter12StructureSheaf X
  tensorQuotientMap : chapter12StructureSheaf X ⟶ fiberQuotient
  tensorCompZero : tensorInclusion ≫ tensorQuotientMap = 0
  tensorExact :
    (ShortComplex.mk tensorInclusion tensorQuotientMap tensorCompZero).Exact
  tensorByInverseFiberEulerCharacteristic : ℤ
  tensorByInverseFiberEulerCharacteristic_is_zero :
    tensorByInverseFiberEulerCharacteristic = 0
  strictTransform_component_genus_change : Prop
  exceptional_incidence_restores_fiber_genus : Prop

def chapter12ArithmeticGenusFromEulerCharacteristic (χ : ℤ) : ℤ :=
  1 - χ

theorem chapter12_point_blowup_preserves_fiber_arithmetic_genus
    {X Y : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter11PicardTheory Y.carrier]
    [Chapter12IntersectionTheory X] [Chapter12IntersectionTheory Y]
    {s : Chapter12ClosedPoint X}
    (B : Chapter12PointBlowup X Y s)
    (F : Chapter12FiberGenusPreservationData B) :
    chapter12ArithmeticGenusFromEulerCharacteristic
        F.transformedFiberEulerCharacteristic =
      chapter12ArithmeticGenusFromEulerCharacteristic F.fiberEulerCharacteristic := by
  rw [F.transformedFiber_same_EulerCharacteristic,
    F.totalTransform_same_EulerCharacteristic]

theorem chapter12_point_blowup_preserves_fiber_euler_characteristic
    {X Y : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter11PicardTheory Y.carrier]
    [Chapter12IntersectionTheory X] [Chapter12IntersectionTheory Y]
    {s : Chapter12ClosedPoint X}
    (B : Chapter12PointBlowup X Y s)
    (F : Chapter12FiberGenusPreservationData B) :
    F.transformedFiberEulerCharacteristic = F.fiberEulerCharacteristic := by
  exact F.transformedFiber_same_EulerCharacteristic.trans
    F.totalTransform_same_EulerCharacteristic

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter12
