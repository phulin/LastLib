import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter11.Dependencies

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter11

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07
open scoped AlgebraicGeometry

universe u v

/-! ### 11.1 Exceptional curves and contraction -/

theorem chapter11_blowup_closed_point_preserves_regularity
    {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    {C : Chapter11SmoothProjectiveCurve K}
    (M : Chapter11RegularProperModel R K C)
    (x : M.carrier) (hx : IsClosed ({x} : Set M.carrier)) :
    Nonempty (Chapter11PointBlowupRegularModel M x hx) := by
  sorry

def chapter11ProjectiveLineH1Vanishing
    {k : Type u} [Field k] (n : ℤ)
    (D : LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01.Chapter01CohomologyDimensions
      k (chapter04ProjectiveLine k))
    (T : Chapter11ProjectiveLineTwistData k n) : Prop :=
  T.is_twist_of_structure_sheaf ∧ chapter01h1 D T.module T.coherent = 0

theorem chapter11_exceptional_curve_first_kind_iff_algebraically_closed_signature
    {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    {C : Chapter11SmoothProjectiveCurve K}
    (M : Chapter11RegularProperModel R K C)
    (E : Chapter11VerticalIntegralCurve M)
    [IsAlgClosed ((chapter11BaseScheme R).residueField E.basePoint)] :
    chapter11FirstKindCurveCondition E ↔
      chapter11AlgebraicallyClosedExceptionalSignature E := by
  sorry

theorem chapter11_exceptional_infinitesimal_neighborhood_exact_sequence
    {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    {C : Chapter11SmoothProjectiveCurve K}
    (M : Chapter11RegularProperModel R K C)
    (E : Chapter11ExceptionalCurveOfFirstKind M)
    (n : ℤ) (hn : -1 ≤ n) :
    Nonempty (Chapter11InfinitesimalNeighborhoodExactSequence E.curve n) := by
  sorry

theorem chapter11_projective_line_h1_vanishes
    {k : Type u} [Field k] (n : ℤ)
    (D : LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01.Chapter01CohomologyDimensions
      k (chapter04ProjectiveLine k))
    (T : Chapter11ProjectiveLineTwistData k n)
    (hn : -1 ≤ n) (hT : T.is_twist_of_structure_sheaf) :
    chapter11ProjectiveLineH1Vanishing n D T := by
  sorry

theorem chapter11_relative_contraction
    {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    {C : Chapter11SmoothProjectiveCurve K}
    (M : Chapter11RegularProperModel R K C)
    (hM : Chapter11ContractionCapability M)
    (E : Chapter11ExceptionalCurveOfFirstKind M) :
    Nonempty (Chapter11ExceptionalContraction M E) := by
  sorry

theorem chapter11_contraction_decreases_affected_fiber_components
    {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    {C : Chapter11SmoothProjectiveCurve K}
    {M : Chapter11RegularProperModel R K C}
    (hM : Chapter11ContractionCapability M)
    (E : Chapter11ExceptionalCurveOfFirstKind M)
    (H : Chapter11ExceptionalContraction M E) :
    chapter11ContractionDecreasesFiberComponents E H := by
  sorry

structure Chapter11RelativeMinimalEndpoint
    {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    {C : Chapter11SmoothProjectiveCurve K}
    (M : Chapter11RegularProperModel R K C) where
  endpoint : Chapter11RegularProperModel R K C
  contraction : M.carrier ⟶ endpoint.carrier
  proper : IsProper contraction
  birational : Chapter07Birational contraction
  over_base : contraction ≫ endpoint.structureMap = M.structureMap
  relatively_minimal : chapter11RelativelyMinimal endpoint

theorem chapter11_repeated_contractions_terminate
    {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    {C : Chapter11SmoothProjectiveCurve K}
    (M : Chapter11RegularProperModel R K C)
    (hM : Chapter11ContractionCapability M) :
    Nonempty (Chapter11RelativeMinimalEndpoint M) := by
  sorry

theorem chapter11_relative_minimality_is_the_no_exceptional_curve_condition
    {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    {C : Chapter11SmoothProjectiveCurve K}
    (M : Chapter11RegularProperModel R K C) :
    chapter11RelativelyMinimal M ↔
      ¬ Nonempty (Chapter11ExceptionalCurveOfFirstKind M) :=
  Iff.rfl

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter11
