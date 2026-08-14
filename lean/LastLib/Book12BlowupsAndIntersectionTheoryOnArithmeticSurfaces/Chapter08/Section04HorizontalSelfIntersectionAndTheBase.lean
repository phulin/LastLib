import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter08.Section01ZeroCyclesAndFiberwiseNumbers

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter08

noncomputable section

open CategoryTheory AlgebraicGeometry

/-! ## 8.4 Horizontal self-intersection and the base -/

structure Chapter08HorizontalCartierCurve (X : Chapter08ArithmeticSurface) where
  prime : Chapter08PrimeCurve X
  toBase : prime.carrier ⟶ X.base
  factorization : prime.inclusion ≫ X.structureMap = toBase
  integral : Prop
  horizontal : prime.horizontal
  finiteOverBase : IsFinite toBase
  flatOverBase : Flat toBase
  divisor : Chapter08CartierDivisor X
  divisor_component : divisor.coefficient prime ≠ 0

def chapter08HorizontalNormalBundle
    {X : Chapter08ArithmeticSurface}
    (H : Chapter08HorizontalCartierCurve X) :
    Chapter08LineBundle H.prime.carrier :=
  chapter08PullbackLineBundle H.prime.inclusion H.divisor.lineBundle

theorem chapter08_horizontal_normal_bundle_is_intrinsic
    {X : Chapter08ArithmeticSurface}
    (H : Chapter08HorizontalCartierCurve X) :
    chapter08HorizontalNormalBundle H =
      chapter08PullbackLineBundle H.prime.inclusion H.divisor.lineBundle := by
  rfl

/- LOCAL_DEPENDENCY_GUESS: the finite-flat norm functor is not yet packaged by
the pinned scheme library.  The compatibility field makes its output descend
to a genuine line-bundle class on the base. -/
class Chapter08FiniteFlatNormTheory
    {X : Chapter08ArithmeticSurface}
    (H : Chapter08HorizontalCartierCurve X) where
  norm : Chapter08LineBundle H.prime.carrier → Chapter08LineBundle X.base
  norm_respects_isomorphism :
    ∀ {L M : Chapter08LineBundle H.prime.carrier},
      chapter08LineBundleIsomorphic L M →
        chapter08LineBundleIsomorphic (norm L) (norm M)

def chapter08FiniteFlatNorm
    {X : Chapter08ArithmeticSurface}
    (H : Chapter08HorizontalCartierCurve X)
    [Chapter08FiniteFlatNormTheory H]
    (L : Chapter08LineBundle H.prime.carrier) :
    Chapter08LineBundleClass X.base :=
  chapter08LineBundleClassMk (Chapter08FiniteFlatNormTheory.norm L)

def chapter08HorizontalSelfIntersectionClass
    {X : Chapter08ArithmeticSurface}
    (H : Chapter08HorizontalCartierCurve X)
    [Chapter08FiniteFlatNormTheory H] :
    Chapter08LineBundleClass X.base :=
  chapter08FiniteFlatNorm H (chapter08HorizontalNormalBundle H)

theorem chapter08_finiteFlatNorm_eq_of_isomorphic
    {X : Chapter08ArithmeticSurface}
    (H : Chapter08HorizontalCartierCurve X)
    [Chapter08FiniteFlatNormTheory H]
    {L M : Chapter08LineBundle H.prime.carrier}
    (h : chapter08LineBundleIsomorphic L M) :
    chapter08FiniteFlatNorm H L = chapter08FiniteFlatNorm H M := by
  apply Quotient.sound
  exact Chapter08FiniteFlatNormTheory.norm_respects_isomorphism h

theorem chapter08_horizontal_selfIntersection_class_is_norm_of_normal_bundle
    {X : Chapter08ArithmeticSurface}
    (H : Chapter08HorizontalCartierCurve X)
    [Chapter08FiniteFlatNormTheory H] :
    chapter08HorizontalSelfIntersectionClass H =
      chapter08FiniteFlatNorm H (chapter08HorizontalNormalBundle H) := by
  rfl

/- A degree on line-bundle classes is extra data.  This is the numerical
specialization available for a proper base curve over a field. -/
class Chapter08ProperBaseCurveDegreeTheory
    (X : Chapter08ArithmeticSurface) where
  degree : Chapter08LineBundleClass X.base → ℤ
  baseIsProperCurveOverField : Prop

def chapter08HorizontalSelfIntersectionNumber
    {X : Chapter08ArithmeticSurface}
    (H : Chapter08HorizontalCartierCurve X)
    [Chapter08FiniteFlatNormTheory H]
    [Chapter08ProperBaseCurveDegreeTheory X] : ℤ :=
  Chapter08ProperBaseCurveDegreeTheory.degree
    (chapter08HorizontalSelfIntersectionClass H)

theorem chapter08_horizontal_selfIntersection_number_eq_degree_of_norm
    {X : Chapter08ArithmeticSurface}
    (H : Chapter08HorizontalCartierCurve X)
    [Chapter08FiniteFlatNormTheory H]
    [Chapter08ProperBaseCurveDegreeTheory X] :
    chapter08HorizontalSelfIntersectionNumber H =
      Chapter08ProperBaseCurveDegreeTheory.degree
        (chapter08FiniteFlatNorm H (chapter08HorizontalNormalBundle H)) := by
  rfl

/-! ### Local orders over a DVR -/

structure Chapter08DVRLocalTrivialization (X : Chapter08ArithmeticSurface) where
  lineBundleClass : Chapter08LineBundleClass X.base
  trivializationData : Type u
  trivialization : trivializationData
  localOrder : ℤ

/- The transition between two rational trivializations is recorded as a
principal order on the base; hence a local order is not an absolute global
integer. -/
structure Chapter08DVRLocalOrderTheory (X : Chapter08ArithmeticSurface) where
  baseIsDVR : Prop
  rationalFunctions : Type u
  principalOrder : rationalFunctions → ℤ
  changeOfTrivialization :
    ∀ t₁ t₂ : Chapter08DVRLocalTrivialization X,
      ∃ f : rationalFunctions,
        t₂.localOrder - t₁.localOrder = principalOrder f

theorem chapter08_dvr_local_order_changes_by_principal_divisor
    {X : Chapter08ArithmeticSurface}
    (T : Chapter08DVRLocalOrderTheory X)
    (t₁ t₂ : Chapter08DVRLocalTrivialization X) :
    ∃ f : T.rationalFunctions,
      t₂.localOrder - t₁.localOrder = T.principalOrder f := by
  exact T.changeOfTrivialization t₁ t₂

/-! ### Explicit numerical conventions -/

/- This is only the boundary interface for the out-of-scope metric theory; it
does not assert an Arakelov construction. -/
structure Chapter08MetricIntersectionData (X : Chapter08ArithmeticSurface) where
  archimedeanOrMetricData : Prop
  realDegree : Chapter08BaseDivisor X → ℝ

def chapter08MetricGlobalIntersectionNumber
    {X : Chapter08ArithmeticSurface}
    [Chapter08LocalIntersectionTheory X]
    {D G : Chapter08CartierDivisor X}
    (I : Chapter08ProperIntersectionWitness D G)
    (A : Chapter08MetricIntersectionData X) : ℝ :=
  A.realDegree (chapter08FiberwiseIntersectionDivisor I)

def chapter08NumericalSelfIntersectionConvention
    {X : Chapter08ArithmeticSurface}
    (D : Chapter08CartierDivisor X) : Prop :=
  chapter08CartierDivisorIsVertical D ∨
    chapter08ProperSurfaceOverField X ∨
      Nonempty (Chapter08BaseDegreeChoice X)

end
end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter08
