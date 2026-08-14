import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter10.Dependencies

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter10

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Set TopologicalSpace
open scoped AlgebraicGeometry BigOperators

universe u

/-! ### 10.1 Pushforward of curves and points -/

/-!
The image of a proper integral curve is either one-dimensional or a closed
point.  These two records keep the geometric factorization and the relevant
coefficient available to the formula, while `chapter10PushforwardPrimeCurve`
below makes the case split in the definition explicit.
-/
structure Chapter10NoncontractedCurvePushforwardData
    {X Y : Scheme.{u}} (f : Y ⟶ X) (C : Chapter10IntegralCurveOn Y) where
  image : Chapter10CurveImageData f C
  coefficient : ℕ
  coefficient_eq_image_degree : coefficient = chapter10CurveImageDegree image

structure Chapter10ContractedCurvePushforwardData
    {X Y : Scheme.{u}} (f : Y ⟶ X) (C : Chapter10IntegralCurveOn Y) where
  image : Chapter10ClosedPoint X
  contracted : ∀ y : C.carrier, (C.inclusion ≫ f).base y = image.1

abbrev Chapter10CurvePushforwardCase
    {X Y : Scheme.{u}} (f : Y ⟶ X) (C : Chapter10IntegralCurveOn Y) :=
  Sum (Chapter10NoncontractedCurvePushforwardData f C)
    (Chapter10ContractedCurvePushforwardData f C)

/-- The divisor-valued pushforward of a prime curve, with the two cases of
(10.1) visible in its input. -/
noncomputable def chapter10PushforwardPrimeCurve
    {X Y : Scheme.{u}} (f : Y ⟶ X) (C : Chapter10IntegralCurveOn Y)
    (h : Chapter10CurvePushforwardCase f C) : Chapter10WeilDivisor X :=
  match h with
  | Sum.inl h =>
      chapter10WeilDivisorZsmul (h.coefficient : ℤ)
        (chapter10PrimeCurveDivisor h.image.image.primePoint)
  | Sum.inr _ => chapter10WeilDivisorZero

theorem chapter10_pushforward_primeCurve_noncontracted
    {X Y : Scheme.{u}} (f : Y ⟶ X) (C : Chapter10IntegralCurveOn Y)
    (h : Chapter10NoncontractedCurvePushforwardData f C) :
    chapter10PushforwardPrimeCurve f C (Sum.inl h) =
      chapter10WeilDivisorZsmul (h.coefficient : ℤ)
        (chapter10PrimeCurveDivisor h.image.image.primePoint) := by
  rfl

theorem chapter10_pushforward_primeCurve_noncontracted_coefficient
    {X Y : Scheme.{u}} (f : Y ⟶ X) (C : Chapter10IntegralCurveOn Y)
    (h : Chapter10NoncontractedCurvePushforwardData f C) :
    h.coefficient = chapter10CurveImageDegree h.image :=
  h.coefficient_eq_image_degree

theorem chapter10_curve_image_field_degree
    {X Y : Scheme.{u}} (f : Y ⟶ X) (C : Chapter10IntegralCurveOn Y)
    (M : Chapter10CurveImageData f C) :
    chapter10CurveImageDegree M = M.map.residueDegree C.genericPoint := by
  exact M.fieldDegree_eq_residueDegree

theorem chapter10_pushforward_primeCurve_contracted
    {X Y : Scheme.{u}} (f : Y ⟶ X) (C : Chapter10IntegralCurveOn Y)
    (h : Chapter10ContractedCurvePushforwardData f C) :
    chapter10PushforwardPrimeCurve f C (Sum.inr h) =
      chapter10WeilDivisorZero := by
  rfl

/-!
The point formula uses the canonical residue-degree operation on a scheme
morphism.  Properness supplies the closedness of the image point; the record
stores that geometric conclusion without replacing the canonical point map.
-/
structure Chapter10PointPushforwardData
    {X Y : Scheme.{u}} (f : Y ⟶ X) (y : Y) where
  image : Chapter10ClosedPoint X
  image_eq : image.1 = f.base y
  coefficient : ℕ
  coefficient_eq_residue_degree : coefficient = chapter10PointFieldDegree f y

noncomputable def chapter10PushforwardPoint
    {X Y : Scheme.{u}} (f : Y ⟶ X) (y : Y)
    (h : Chapter10PointPushforwardData f y) : Chapter10ZeroCycle X :=
  chapter10ZeroCycleZsmul (h.coefficient : ℤ) (chapter10PointZeroCycle h.image)

theorem chapter10_pushforward_point_formula
    {X Y : Scheme.{u}} (f : Y ⟶ X) (y : Y)
    (h : Chapter10PointPushforwardData f y) :
    chapter10PushforwardPoint f y h =
      chapter10ZeroCycleZsmul (h.coefficient : ℤ) (chapter10PointZeroCycle h.image) :=
  rfl

theorem chapter10_pushforward_point_coefficient
    {X Y : Scheme.{u}} (f : Y ⟶ X) (y : Y)
    (h : Chapter10PointPushforwardData f y) :
    h.coefficient = chapter10PointFieldDegree f y :=
  h.coefficient_eq_residue_degree

/- LOCAL_DEPENDENCY_GUESS: the proper-image theorem for closed points should be
connected to the canonical `IsProper` universally-closed API. -/
theorem chapter10_proper_closed_point_has_pushforward_data
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsProper f]
    (y : Y) (hy : IsClosed ({y} : Set Y)) :
    Nonempty (Chapter10PointPushforwardData f y) := by
  sorry

/-!
Mathlib's `AlgebraicCycle.map` is the linear extension of the pointwise
residue-degree rule.  The codimension weight is `Order.coheight`, which is the
weight used by the divisor cycle API and makes contracted curves disappear.
-/
noncomputable def chapter10AlgebraicCyclePushforward
    {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f]
    (z : Chapter10AlgebraicCycle Y) : Chapter10AlgebraicCycle X := by
  classical
  exact AlgebraicCycle.map f Order.coheight Order.coheight z

noncomputable def chapter10WeilDivisorPushforward
    {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f]
    (D : Chapter10WeilDivisor Y) : Chapter10WeilDivisor X where
  cycle := chapter10AlgebraicCyclePushforward f D.cycle
  support_is_curve := by
    sorry
  finite_support := by
    sorry

noncomputable def chapter10ZeroCyclePushforward
    {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f]
    (z : Chapter10ZeroCycle Y) : Chapter10ZeroCycle X where
  cycle := by
    classical
    exact AlgebraicCycle.map f Order.height Order.height z.cycle
  support_is_closed := by
    sorry
  finite_support := by
    sorry

theorem chapter10_pushforward_weilDivisor_is_linear
    {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f]
    (D E : Chapter10WeilDivisor Y) :
    (chapter10WeilDivisorPushforward f (chapter10WeilDivisorAdd D E)).cycle =
      (chapter10WeilDivisorPushforward f D).cycle +
        (chapter10WeilDivisorPushforward f E).cycle := by
  sorry

theorem chapter10_pushforward_zeroCycle_is_linear
    {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f]
    (z w : Chapter10ZeroCycle Y) :
    (chapter10ZeroCyclePushforward f (chapter10ZeroCycleAdd z w)).cycle =
      (chapter10ZeroCyclePushforward f z).cycle +
        (chapter10ZeroCyclePushforward f w).cycle := by
  sorry

/-! ### Birational and finite-map special cases -/

structure Chapter10BirationalNoncontractedCurveData
    {X Y : Scheme.{u}} (f : Y ⟶ X) (C : Chapter10IntegralCurveOn Y) where
  image : Chapter10CurveImageData f C
  birational_on_curve : chapter10CurveImageDegree image = 1

theorem chapter10_birational_noncontracted_curve_pushforward
    {X Y : Scheme.{u}} (f : Y ⟶ X) (C : Chapter10IntegralCurveOn Y)
    (h : Chapter10BirationalNoncontractedCurveData f C)
    (P : Chapter10NoncontractedCurvePushforwardData f C)
    (himage : P.image = h.image) :
    (chapter10PushforwardPrimeCurve f C (Sum.inl P)).cycle =
      (chapter10PrimeCurveDivisor h.image.image.primePoint).cycle := by
  sorry

structure Chapter10ExceptionalCurveData
    {X Y : Scheme.{u}} (f : Y ⟶ X) where
  curve : Chapter10IntegralCurveOn Y
  image : Chapter10ClosedPoint X
  contracted : ∀ y : curve.carrier, (curve.inclusion ≫ f).base y = image.1
  pushforward_case : Chapter10ContractedCurvePushforwardData f curve

theorem chapter10_exceptional_curve_pushforward_zero
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (E : Chapter10ExceptionalCurveData f) :
    chapter10PushforwardPrimeCurve f E.curve (Sum.inr E.pushforward_case) =
      chapter10WeilDivisorZero := by
  rfl

/-!
Finite morphisms have zero-dimensional fibers.  The proposition below is the
book-facing no-contraction interface used by the finite-map section; its
proof is the standard dimension-of-fibers argument.
-/
def Chapter10NoContractedCurves {X Y : Scheme.{u}} (f : Y ⟶ X) : Prop :=
  ∀ C : Chapter10IntegralCurveOn Y,
    Nonempty (Chapter10NoncontractedCurvePushforwardData f C)

theorem chapter10_finite_map_has_no_contracted_curves
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] :
    Chapter10NoContractedCurves f := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the preceding scheme-theoretic curve package should
identify the generically-finite image condition with finiteness of the induced
function-field extension. -/
theorem chapter10_proper_curve_image_is_genericallyFinite
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsProper f]
    (C : Chapter10IntegralCurveOn Y)
    (M : Chapter10CurveImageData f C) :
    M.genericallyFinite := by
  sorry

theorem chapter10_proper_curve_image_field_degree_is_finite
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsProper f]
    (C : Chapter10IntegralCurveOn Y)
    (M : Chapter10CurveImageData f C) :
    M.fieldDegree_is_finite_extension := by
  sorry

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter10
