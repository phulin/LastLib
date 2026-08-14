import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter08.Dependencies

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter08

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped BigOperators

/-! ## 8.2 Intersecting a divisor with a vertical curve -/

def chapter08DivisorLineBundleRestriction
    {X : Chapter08ArithmeticSurface}
    (D : Chapter08CartierDivisor X) (C : Chapter08VerticalCurve X) :
    Chapter08LineBundle C.prime.carrier :=
  chapter08PullbackLineBundle C.prime.inclusion D.lineBundle

theorem chapter08_divisorCurveIntersection_eq_degree_of_restriction
    {X : Chapter08ArithmeticSurface}
    (D : Chapter08CartierDivisor X) (C : Chapter08VerticalCurve X)
    [Chapter08CurveDegreeTheory C] :
    chapter08DivisorCurveIntersection D C =
      chapter08Degree C (chapter08DivisorLineBundleRestriction D C) := by
  rfl

structure Chapter08ProperDivisorCurveIntersectionWitness
    {X : Chapter08ArithmeticSurface}
    (D : Chapter08CartierDivisor X) (C : Chapter08VerticalCurve X)
    [Chapter08LocalIntersectionTheory X] where
  support : Finset (Chapter08ClosedPoint X)
  support_contains_nonzero :
    ∀ x, chapter08LocalIntersectionLength D C x ≠ 0 → x ∈ support
  meetsProperly : chapter08DivisorMeetsCurveProperly D C

def chapter08DivisorCurveLocalLengthSum
    {X : Chapter08ArithmeticSurface}
    [Chapter08LocalIntersectionTheory X]
    {D : Chapter08CartierDivisor X} {C : Chapter08VerticalCurve X}
    (I : Chapter08ProperDivisorCurveIntersectionWitness D C) : ℤ := by
  classical
  exact ∑ x in I.support.filter C.pointOnCurve,
    (chapter08LocalIntersectionLength D C x : ℤ) * (x.residueDegree : ℤ)

theorem chapter08_restricted_intersection_length_eq_local_multiplicity
    {X : Chapter08ArithmeticSurface}
    [Chapter08LocalIntersectionTheory X]
    (D : Chapter08CartierDivisor X) (C : Chapter08VerticalCurve X)
    (hproper : chapter08DivisorMeetsCurveProperly D C)
    (x : Chapter08ClosedPoint X) :
    chapter08LocalIntersectionLength D C x =
      chapter08LocalIntersectionMultiplicity D C.asCartierDivisor x := by
  exact Chapter08LocalIntersectionTheory.localLength_eq_multiplicity D C x hproper

theorem chapter08_divisorCurveIntersection_eq_local_length_sum
    {X : Chapter08ArithmeticSurface}
    [Chapter08LocalIntersectionTheory X]
    {D : Chapter08CartierDivisor X} {C : Chapter08VerticalCurve X}
    [Chapter08CurveDegreeTheory C]
    (I : Chapter08ProperDivisorCurveIntersectionWitness D C) :
    chapter08DivisorCurveIntersection D C =
      chapter08DivisorCurveLocalLengthSum I := by
  sorry

/- The displayed definition also applies when `D` contains `C`; properness is
only needed for the local-length comparison theorem above. -/
theorem chapter08_divisorCurveIntersection_is_defined_for_common_component
    {X : Chapter08ArithmeticSurface}
    (D : Chapter08CartierDivisor X) (C : Chapter08VerticalCurve X)
    [Chapter08CurveDegreeTheory C] :
    ∃ n : ℤ, chapter08DivisorCurveIntersection D C = n := by
  exact ⟨chapter08DivisorCurveIntersection D C, rfl⟩

theorem chapter08_divisorCurveIntersection_additive_in_divisor
    {X : Chapter08ArithmeticSurface}
    [LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Chapter09LineBundleTensorTheory X.carrier]
    (D G : Chapter08CartierDivisor X) (C : Chapter08VerticalCurve X)
    [Chapter08CurveDegreeTheory C]
    [LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Chapter09LineBundleTensorTheory C.prime.carrier]
    [Chapter08CurveDegreeTensorTheory C] :
    chapter08DivisorCurveIntersection
        (chapter08CartierDivisorAdd D G) C =
      chapter08DivisorCurveIntersection D C +
        chapter08DivisorCurveIntersection G C := by
  sorry

theorem chapter08_divisor_oneCycleIntersection_additive_in_cycle
    {X : Chapter08ArithmeticSurface}
    (D : Chapter08CartierDivisor X)
    (V W : Chapter08VerticalOneCycle X)
    [∀ C : Chapter08VerticalCurve X, Chapter08CurveDegreeTheory C] :
    chapter08DivisorOneCycleIntersection D (V + W) =
      chapter08DivisorOneCycleIntersection D V +
        chapter08DivisorOneCycleIntersection D W := by
  sorry

structure Chapter08CurveNeighborhood
    {X : Chapter08ArithmeticSurface} (C : Chapter08VerticalCurve X) where
  carrier : Scheme.{u}
  inclusion : carrier ⟶ X.carrier
  isOpen : IsOpenImmersion inclusion
  curveFactor : C.prime.carrier ⟶ carrier
  curveFactorization : curveFactor ≫ inclusion = C.prime.inclusion

def chapter08LineBundleAgreementNearCurve
    {X : Chapter08ArithmeticSurface}
    (D G : Chapter08CartierDivisor X) (C : Chapter08VerticalCurve X) : Prop :=
  ∃ U : Chapter08CurveNeighborhood C,
    chapter08LineBundleIsomorphic
      (chapter08PullbackLineBundle U.inclusion D.lineBundle)
      (chapter08PullbackLineBundle U.inclusion G.lineBundle)

theorem chapter08_divisorCurveIntersection_depends_only_on_lineBundle_near_curve
    {X : Chapter08ArithmeticSurface}
    (D G : Chapter08CartierDivisor X) (C : Chapter08VerticalCurve X)
    [Chapter08CurveDegreeTheory C]
    (h : chapter08LineBundleAgreementNearCurve D G C) :
    chapter08DivisorCurveIntersection D C =
      chapter08DivisorCurveIntersection G C := by
  sorry

def chapter08NormalBundle
    {X : Chapter08ArithmeticSurface} (C : Chapter08VerticalCurve X) :
    Chapter08LineBundle C.prime.carrier :=
  chapter08DivisorLineBundleRestriction C.asCartierDivisor C

def chapter08CurveSelfIntersection
    {X : Chapter08ArithmeticSurface} (C : Chapter08VerticalCurve X)
    [Chapter08CurveDegreeTheory C] : ℤ :=
  chapter08DivisorCurveIntersection C.asCartierDivisor C

theorem chapter08_curve_selfIntersection_eq_degree_normalBundle
    {X : Chapter08ArithmeticSurface} (C : Chapter08VerticalCurve X)
    [Chapter08CurveDegreeTheory C] :
    chapter08CurveSelfIntersection C = chapter08Degree C (chapter08NormalBundle C) := by
  rfl

end
end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter08
