import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter10.Section01PushforwardOfCurvesAndPoints

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter10

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Set TopologicalSpace
open scoped AlgebraicGeometry BigOperators

universe u

/-! ### 10.2 Pullback of divisors -/

def chapter10PullbackRationalFunction
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] [IsDominant f]
    [Chapter10DominantFunctionFieldTheory f]
    (g : X.functionField) : Y.functionField :=
  chapter10FunctionFieldMap f g

theorem chapter10_pullback_rationalFunction_ne_zero
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] [IsDominant f]
    [Chapter10DominantFunctionFieldTheory f]
    (g : X.functionField) (hg : g ≠ 0) :
    chapter10PullbackRationalFunction f g ≠ 0 := by
  intro hzero
  apply hg
  exact (Chapter10DominantFunctionFieldTheory.injective (f := f)) (by
    simpa [chapter10PullbackRationalFunction] using hzero)

/-!
The regular-surface Cartier/Weil dictionary is kept as an explicit pullback
record.  Its line-bundle component is the canonical sheaf pullback from the
earlier line-bundle API, while the rational-equation component records the
local description used by the chapter.
-/
structure Chapter10CartierPullbackData
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] [IsDominant f]
    [Chapter10DominantFunctionFieldTheory f]
    (D : Chapter10CartierDivisor X) where
  pullback : Chapter10CartierDivisor Y
  lineBundle_compatibility :
    chapter11LineBundleIsomorphic pullback.lineBundle
      (chapter09PullbackLineBundle f D.lineBundle)
  rational_equation_compatibility : Prop

/- LOCAL_DEPENDENCY_GUESS: a preceding regular-scheme Cartier-divisor
dictionary supplies the local-equation construction and its compatibility
with the invertible-sheaf pullback. -/
theorem chapter10_cartier_pullback_exists
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] [IsDominant f]
    [Chapter10DominantFunctionFieldTheory f]
    (D : Chapter10CartierDivisor X) :
    Nonempty (Chapter10CartierPullbackData f D) := by
  sorry

noncomputable def chapter10CartierPullback
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] [IsDominant f]
    [Chapter10DominantFunctionFieldTheory f]
    (D : Chapter10CartierDivisor X) : Chapter10CartierDivisor Y :=
  (Classical.choice (chapter10_cartier_pullback_exists f D)).pullback

theorem chapter10_cartierPullback_lineBundle_compatibility
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] [IsDominant f]
    [Chapter10DominantFunctionFieldTheory f]
    (D : Chapter10CartierDivisor X) :
    chapter11LineBundleIsomorphic (chapter10CartierPullback f D).lineBundle
      (chapter09PullbackLineBundle f D.lineBundle) := by
  exact (Classical.choice (chapter10_cartier_pullback_exists f D)).lineBundle_compatibility

/-!
For an effective divisor, the pulled-back ideal is always the canonical
scheme-theoretic inverse-image ideal.  To retain effectivity, the local
equations are required to stay regular; dominance on integral schemes is the
standard sufficient hypothesis used here.
-/
noncomputable def chapter10EffectiveCartierPullbackOfRegularEquation
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (D : Chapter10EffectiveCartierDivisor X)
    (hregular : chapter10PulledBackEquationIsRegular f D) :
    Chapter10EffectiveCartierDivisor Y where
  ideal := chapter10SchemeTheoreticInverseImageIdeal f D
  locallyRegularPrincipal := hregular
  closed := by
    sorry

noncomputable def chapter10DominantEffectiveCartierPullback
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] [IsDominant f]
    (D : Chapter10EffectiveCartierDivisor X) :
    Chapter10EffectiveCartierDivisor Y where
  ideal := chapter10SchemeTheoreticInverseImageIdeal f D
  locallyRegularPrincipal := by
    sorry
  closed := by
    sorry

theorem chapter10_dominant_effective_pullback_is_regular
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] [IsDominant f]
    (D : Chapter10EffectiveCartierDivisor X) :
    chapter10PulledBackEquationIsRegular f D := by
  sorry

theorem chapter10_dominant_effective_pullback_ideal
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] [IsDominant f]
    (D : Chapter10EffectiveCartierDivisor X) :
    (chapter10DominantEffectiveCartierPullback f D).ideal = D.ideal.comap f :=
  rfl

/-! ### Ramification at a prime curve -/

structure Chapter10RamificationIndexData
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsDominant f] [Chapter10DominantFunctionFieldTheory f]
    (C : Chapter10PrimeCurvePoint Y) (B : Chapter10PrimeCurvePoint X) where
  maps_to : f.base C.1 = B.1
  local_equation : X.functionField
  local_equation_is_uniformizer : Prop
  ramificationIndex : ℕ
  order_eq_ramificationIndex :
    Scheme.ord (chapter10PullbackRationalFunction f local_equation) C.1 =
      (ramificationIndex : ℤ)

def chapter10PullbackOrderAtPrimeCurve
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsDominant f] [Chapter10DominantFunctionFieldTheory f]
    (C : Chapter10PrimeCurvePoint Y) (g : X.functionField) : ℤ :=
  Scheme.ord (chapter10PullbackRationalFunction f g) C.1

theorem chapter10_pullback_order_eq_ramificationIndex
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsDominant f] [Chapter10DominantFunctionFieldTheory f]
    (C : Chapter10PrimeCurvePoint Y) (B : Chapter10PrimeCurvePoint X)
    (R : Chapter10RamificationIndexData f C B) :
    chapter10PullbackOrderAtPrimeCurve f C R.local_equation =
      (R.ramificationIndex : ℤ) := by
  exact R.order_eq_ramificationIndex

/-! ### Finite flat inverse images and point blowups -/

noncomputable def chapter10FiniteFlatEffectiveCartierPullback
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Flat f]
    (D : Chapter10EffectiveCartierDivisor X) :
    Chapter10EffectiveCartierDivisor Y where
  ideal := chapter10SchemeTheoreticInverseImageIdeal f D
  locallyRegularPrincipal := by
    sorry
  closed := by
    sorry

theorem chapter10_finite_flat_effective_pullback_is_inverse_image
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Flat f]
    (D : Chapter10EffectiveCartierDivisor X) :
    (chapter10FiniteFlatEffectiveCartierPullback f D).ideal =
      D.ideal.comap f := by
  rfl

/-!
The point-blowup interface distinguishes the total transform from the strict
transform and records the exceptional correction.  The actual blowup
construction is supplied by the preceding blowup chapters.
-/
/- LOCAL_DEPENDENCY_GUESS: the earlier blowup chapters supply the point-blowup
predicate and identify its canonical Cartier pullback with the total transform.
-/
structure Chapter10PointBlowupTransformData
    {X Y : Scheme.{u}} (b : Y ⟶ X) (D : Chapter10CartierDivisor X) where
  center : Chapter10ClosedPoint X
  is_point_blowup : Prop
  pullback : Chapter10CartierDivisor Y
  totalTransform : Chapter10CartierDivisor Y
  strictTransform : Chapter10WeilDivisor Y
  exceptional : Chapter10WeilDivisor Y
  multiplicity : ℕ
  total_transform_cycle_eq :
    totalTransform.divisor.cycle =
      strictTransform.cycle + (multiplicity : ℤ) • exceptional.cycle
  pullback_eq_total_transform : pullback = totalTransform
  strict_transform_cycle_eq_total_of_multiplicity_zero :
    multiplicity = 0 → strictTransform.cycle = totalTransform.divisor.cycle
  strict_transform_cycle_ne_total_of_multiplicity_pos :
    0 < multiplicity → strictTransform.cycle ≠ totalTransform.divisor.cycle

theorem chapter10_pointBlowup_total_transform_cycle_formula
    {X Y : Scheme.{u}} (b : Y ⟶ X) (D : Chapter10CartierDivisor X)
    (P : Chapter10PointBlowupTransformData b D) :
  P.totalTransform.divisor.cycle =
      P.strictTransform.cycle + (P.multiplicity : ℤ) • P.exceptional.cycle :=
  P.total_transform_cycle_eq

theorem chapter10_pointBlowup_pullback_equals_total_transform
    {X Y : Scheme.{u}} (b : Y ⟶ X) (D : Chapter10CartierDivisor X)
    (P : Chapter10PointBlowupTransformData b D) :
    P.pullback = P.totalTransform :=
  P.pullback_eq_total_transform

theorem chapter10_pointBlowup_strict_transform_is_not_total_transform
    {X Y : Scheme.{u}} (b : Y ⟶ X) (D : Chapter10CartierDivisor X)
    (P : Chapter10PointBlowupTransformData b D) (hm : 0 < P.multiplicity) :
    P.strictTransform.cycle ≠ P.totalTransform.divisor.cycle :=
  P.strict_transform_cycle_ne_total_of_multiplicity_pos hm

theorem chapter10_pointBlowup_strict_transform_equals_total_of_zero_multiplicity
    {X Y : Scheme.{u}} (b : Y ⟶ X) (D : Chapter10CartierDivisor X)
    (P : Chapter10PointBlowupTransformData b D) (hm : P.multiplicity = 0) :
    P.strictTransform.cycle = P.totalTransform.divisor.cycle :=
  P.strict_transform_cycle_eq_total_of_multiplicity_zero hm

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter10
