import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter10.Section02PullbackOfDivisors

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter10

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Set TopologicalSpace
open scoped AlgebraicGeometry BigOperators

universe u

/-! ### 10.3 The projection formula -/

/-!
The common-base condition in the statement is kept explicit.  The two
constructors are the source alternatives: proper curves over one field, or a
fiber over one closed point of a common Dedekind base.
-/
inductive Chapter10CommonProperCurveCondition
    {X Y : Scheme.{u}} (f : Y ⟶ X) (C : Chapter10IntegralCurveOn Y)
    (M : Chapter10CurveImageData f C) : Prop
  | overField (k : Type u) [Field k]
      (curveMap : C.carrier ⟶ Spec (.of k))
      (imageMap : M.image.carrier ⟶ Spec (.of k))
      (curveProper : IsProper curveMap)
      (imageProper : IsProper imageMap)
      (mapOver : M.map ≫ imageMap = curveMap)
  | overClosedDedekindFiber (base : Chapter10DedekindBase)
      (s : base.carrier)
      (sClosed : IsClosed ({s} : Set base.carrier))
      (curveMap : C.carrier ⟶ base.carrier)
      (imageMap : M.image.carrier ⟶ base.carrier)
      (curveProper : IsProper curveMap)
      (imageProper : IsProper imageMap)
      (mapOver : M.map ≫ imageMap = curveMap)
      (curveInFiber : ∀ z : C.carrier, curveMap.base z = s)
      (imageInFiber : ∀ z : M.image.carrier, imageMap.base z = s)

structure Chapter10ProjectionFormulaInput
    {X Y : Scheme.{u}} (f : Y ⟶ X) (D : Chapter10CartierDivisor X)
    (C : Chapter10IntegralCurveOn Y) where
  surfaceMorphism : Chapter10ProperSurfaceMorphismData f
  image : Chapter10CurveImageData f C
  pullback : Chapter10CartierDivisor Y
  pullback_is_cartier_pullback : Prop
  pushforward : Chapter10WeilDivisor X
  pushforward_is_curve_pushforward : Prop
  base_condition : Chapter10CommonProperCurveCondition f C image

def chapter10ProjectionFormulaStatement
    {X Y : Scheme.{u}} (f : Y ⟶ X) (D : Chapter10CartierDivisor X)
    (C : Chapter10IntegralCurveOn Y) [Chapter10IntersectionTheory X]
    [Chapter10IntersectionTheory Y]
    (P : Chapter10ProjectionFormulaInput f D C) : Prop :=
  chapter10IntersectionNumber P.pullback C =
    chapter10IntersectionNumberWithWeilDivisor D P.pushforward

/-!
The degree comparison is the proof-ready numerical interface for the
generically finite branch.  `constant_field_degree_compatibility` records the
constant-field factors which must not be silently dropped.
-/
structure Chapter10ProjectionFormulaDegreeComparison
    {X Y : Scheme.{u}} (f : Y ⟶ X) (D : Chapter10CartierDivisor X)
    (C : Chapter10IntegralCurveOn Y)
    [Chapter10IntersectionTheory X] [Chapter10IntersectionTheory Y]
    [Chapter10CurveDegreeTheory X] [Chapter10CurveDegreeTheory Y] where
  image : Chapter10CurveImageData f C
  degree : ℕ
  degree_eq_image_degree : degree = chapter10CurveImageDegree image
  targetLineBundle : Chapter10LineBundle X
  targetLineBundle_is_D : targetLineBundle = D.lineBundle
  pullback_degree :
    chapter10CurveDegree C
        (chapter09PullbackLineBundle image.map targetLineBundle) =
      (degree : ℤ) * chapter10CurveDegree image.image targetLineBundle
  constant_field_degree_compatibility : Prop

theorem chapter10_projection_formula
    {X Y : Scheme.{u}} (f : Y ⟶ X) (D : Chapter10CartierDivisor X)
    (C : Chapter10IntegralCurveOn Y)
    [Chapter10IntersectionTheory X] [Chapter10IntersectionTheory Y]
    (P : Chapter10ProjectionFormulaInput f D C) :
    chapter10ProjectionFormulaStatement f D C P := by
  sorry

theorem chapter10_theorem_10_1_projection_formula
    {X Y : Scheme.{u}} (f : Y ⟶ X) (D : Chapter10CartierDivisor X)
    (C : Chapter10IntegralCurveOn Y)
    [Chapter10IntersectionTheory X] [Chapter10IntersectionTheory Y]
    (P : Chapter10ProjectionFormulaInput f D C) :
    chapter10IntersectionNumber P.pullback C =
      chapter10IntersectionNumberWithWeilDivisor D P.pushforward := by
  exact chapter10_projection_formula f D C P

/-! ### Contracted and generically finite branches -/

structure Chapter10ContractedProjectionData
    {X Y : Scheme.{u}} (f : Y ⟶ X) (D : Chapter10CartierDivisor X)
    (C : Chapter10IntegralCurveOn Y)
    [Chapter10IntersectionTheory X] [Chapter10IntersectionTheory Y]
    extends Chapter10ProjectionFormulaInput f D C where
  contracted : ∃ x : Chapter10ClosedPoint X,
    ∀ y : C.carrier, (C.inclusion ≫ f).base y = x.1
  pushforward_zero : pushforward = chapter10WeilDivisorZero
  pullback_restriction_zero : chapter10IntersectionNumber pullback C = 0
  target_intersection_zero :
    chapter10IntersectionNumberWithWeilDivisor D pushforward = 0

theorem chapter10_projection_formula_contracted
    {X Y : Scheme.{u}} (f : Y ⟶ X) (D : Chapter10CartierDivisor X)
    (C : Chapter10IntegralCurveOn Y)
    [Chapter10IntersectionTheory X] [Chapter10IntersectionTheory Y]
    (P : Chapter10ContractedProjectionData f D C) :
    chapter10IntersectionNumber P.pullback C =
      chapter10IntersectionNumberWithWeilDivisor D P.pushforward := by
  rw [P.pullback_restriction_zero, P.target_intersection_zero]

structure Chapter10GenericallyFiniteProjectionData
    {X Y : Scheme.{u}} (f : Y ⟶ X) (D : Chapter10CartierDivisor X)
    (C : Chapter10IntegralCurveOn Y)
    [Chapter10IntersectionTheory X] [Chapter10IntersectionTheory Y]
    extends Chapter10ProjectionFormulaInput f D C where
  genericallyFinite : image.genericallyFinite
  degree : ℕ
  degree_eq_image_degree : degree = chapter10CurveImageDegree image

theorem chapter10_projection_formula_generically_finite
    {X Y : Scheme.{u}} (f : Y ⟶ X) (D : Chapter10CartierDivisor X)
    (C : Chapter10IntegralCurveOn Y)
    [Chapter10IntersectionTheory X] [Chapter10IntersectionTheory Y]
    (P : Chapter10GenericallyFiniteProjectionData f D C) :
    chapter10IntersectionNumber P.pullback C =
      chapter10IntersectionNumberWithWeilDivisor D P.pushforward := by
  sorry

/-! ### The divisor/zero-cycle form -/

def chapter10CartierCartierIntersectionZeroCycle
    {X : Scheme.{u}} [Chapter10IntersectionTheory X]
    (D G : Chapter10CartierDivisor X)
    (h : chapter10ProperIntersection D G) : Chapter10ZeroCycle X :=
  Chapter10IntersectionTheory.withCartierDivisors D G h

def chapter10CartierWeilIntersectionZeroCycle
    {X : Scheme.{u}} [Chapter10IntersectionTheory X]
    (D : Chapter10CartierDivisor X) (G : Chapter10WeilDivisor X)
    (h : Disjoint D.divisor.cycle.support G.cycle.support) : Chapter10ZeroCycle X :=
  Chapter10IntersectionTheory.withCartierWeilDivisors D G h

structure Chapter10DivisorProjectionFormulaData
    {X Y : Scheme.{u}} (f : Y ⟶ X) (D : Chapter10CartierDivisor X)
    (G : Chapter10CartierDivisor Y)
    [QuasiCompact f]
    [Chapter10IntersectionTheory X] [Chapter10IntersectionTheory Y] where
  proper : IsProper f
  pullback : Chapter10CartierDivisor Y
  pullback_is_cartier_pullback : Prop
  left_proper_intersection : chapter10ProperIntersection pullback G
  right_proper_intersection :
    Disjoint D.divisor.cycle.support
      (chapter10WeilDivisorPushforward f G.divisor).cycle.support

theorem chapter10_projection_formula_for_divisors
    {X Y : Scheme.{u}} (f : Y ⟶ X) (D : Chapter10CartierDivisor X)
    (G : Chapter10CartierDivisor Y)
    [Chapter10IntersectionTheory X] [Chapter10IntersectionTheory Y]
    [QuasiCompact f]
    (P : Chapter10DivisorProjectionFormulaData f D G) :
    chapter10ZeroCyclePushforward f
        (chapter10CartierCartierIntersectionZeroCycle P.pullback G
          P.left_proper_intersection) =
      chapter10CartierWeilIntersectionZeroCycle D
        (chapter10WeilDivisorPushforward f G.divisor)
        P.right_proper_intersection := by
  sorry

/-! ### Exceptional-curve orthogonality -/

structure Chapter10ExceptionalProjectionData
    {X Y : Scheme.{u}} (f : Y ⟶ X) (D : Chapter10CartierDivisor X)
    [Chapter10IntersectionTheory Y] where
  curve : Chapter10IntegralCurveOn Y
  pullback : Chapter10CartierDivisor Y
  pullback_is_cartier_pullback : Prop
  contracted : ∃ x : Chapter10ClosedPoint X,
    ∀ y : curve.carrier, (curve.inclusion ≫ f).base y = x.1
  restriction_is_trivial : chapter10IntersectionNumber pullback curve = 0

theorem chapter10_exceptional_curve_is_orthogonal_to_pullback
    {X Y : Scheme.{u}} (f : Y ⟶ X) (D : Chapter10CartierDivisor X)
    [Chapter10IntersectionTheory Y]
    (E : Chapter10ExceptionalProjectionData f D) :
    chapter10IntersectionNumber E.pullback E.curve = 0 :=
  E.restriction_is_trivial

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter10
