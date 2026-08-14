import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter11.Section03UniquenessAndLimits

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter11

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01
open scoped AlgebraicGeometry

universe u v

/-! ### 11.4 Marked and semistable variants -/

def chapter11MarkedInvariant
    (D : Chapter11MarkedModel P M) : Chapter11MarkedResolutionInvariant :=
  { surface := D.surfaceInvariant
    boundaryTangencies := D.boundaryTangencies }

def chapter11MarkedResolutionStep
    (D E : Chapter11MarkedModel P M) : Prop :=
  chapter11MarkedComplexityLt
    (chapter11MarkedComplexity (chapter11MarkedInvariant E))
    (chapter11MarkedComplexity (chapter11MarkedInvariant D))

theorem chapter11_marked_resolution_complexity_is_well_founded :
    WellFounded chapter11MarkedComplexityLt := by
  sorry

theorem chapter11_marked_resolution_step_decreases_complexity
    (D E : Chapter11MarkedModel P M)
    (h : chapter11MarkedResolutionStep D E) :
    chapter11MarkedComplexityLt
      (chapter11MarkedComplexity (chapter11MarkedInvariant E))
      (chapter11MarkedComplexity (chapter11MarkedInvariant D)) := by
  sorry

theorem chapter11_marked_resolution_terminates
    {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    {C : Chapter11SmoothProjectiveCurve K} {n : ℕ}
    (P : Chapter11MarkedCurve C n)
    (M : Chapter11RegularProperModel R K C)
    (D : Chapter11MarkedModel P M) :
    ∃ (M' : Chapter11RegularProperModel R K C)
      (D' : Chapter11MarkedModel P M'),
      chapter11MarkedBoundaryResolved D' ∧
        chapter11MarkedModelGenericCompatibility D' ∧
        Nonempty (Chapter11MarkedResolutionFrom D D') := by
  sorry

theorem chapter11_marked_resolution_preserves_the_generic_marked_curve
    {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    {C : Chapter11SmoothProjectiveCurve K} {n : ℕ}
    (P : Chapter11MarkedCurve C n)
    (M : Chapter11RegularProperModel R K C)
    (D : Chapter11MarkedModel P M) :
    ∃ (M' : Chapter11RegularProperModel R K C)
      (D' : Chapter11MarkedModel P M'),
      chapter11MarkedModelGenericCompatibility D' ∧
        Nonempty (Chapter11MarkedResolutionFrom D D') := by
  sorry

/-! A regular semistable model keeps the nodal open visible in every field. -/

theorem chapter11_regular_semistable_model_has_reduced_special_fibers
    {R K : Type u} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
    {C : Chapter11SmoothProjectiveCurve K}
    {M : Chapter11RegularProperModel R K C} {π : R}
    (H : Chapter11RegularSemistableModel M π) :
    chapter11ReducedSpecialFibers M :=
  H.reducedSpecialFibers

theorem chapter11_regular_semistable_model_has_transverse_components
    {R K : Type u} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
    {C : Chapter11SmoothProjectiveCurve K}
    {M : Chapter11RegularProperModel R K C} {π : R}
    (H : Chapter11RegularSemistableModel M π) :
    chapter11ComponentsMeetTransversely M :=
  H.transverseComponents

theorem chapter11_regular_semistable_model_has_xy_equals_pi_node_charts
    {R K : Type u} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
    {C : Chapter11SmoothProjectiveCurve K}
    {M : Chapter11RegularProperModel R K C} {π : R}
    (H : Chapter11RegularSemistableModel M π) :
    chapter11NodeLocalEquation M π :=
  H.nodeLocalEquation

theorem chapter11_resolution_alone_does_not_guarantee_semistability :
    ¬ (∀ {R K : Type u} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
        {C : Chapter11SmoothProjectiveCurve K}
        (M : Chapter11RegularProperModel R K C) (π : R),
        chapter11Uniformizer R π →
          Nonempty (Chapter11RegularSemistableModel M π)) := by
  sorry

theorem chapter11_semistable_reduction_after_finite_separable_extension
    {R : Type u} [CommRing R] [IsDomain R]
    (hR : Chapter11ExcellentDiscreteValuationRing R)
    (C : Chapter11SmoothProjectiveCurve (FractionRing R)) :
    Nonempty (Chapter11SemistableReductionOutput R (FractionRing R) C) := by
  sorry

theorem chapter11_normalize_resolve_and_remove_exceptional_components_preserving_nodal_open
    {S : Scheme.{u}}
    (I : Chapter11SemistableRepairInput S) :
    Nonempty (Chapter11SemistableRepairOutput I) := by
  sorry

theorem chapter11_stable_model_contracts_unstable_rational_components
    {S : Scheme.{u}} (M : Chapter11StableModel S) :
    M.contractsUnstableRationalComponents :=
  M.contractsUnstableRationalComponents

def chapter11_stable_model_can_have_nonregular_total_space_after_ramified_base_change
    {S : Scheme.{u}} : Prop :=
  ∃ M : Chapter11StableModel S,
    chapter11StableModelMayHaveNonregularTotalSpace M

def chapter11_stable_and_minimal_regular_models_are_distinct_interfaces
    {S : Scheme.{u}} : Prop :=
  ∃ M : Chapter11StableModel S,
    M.nodalSpecialFibers ∧ M.contractsUnstableRationalComponents ∧
      chapter11StableModelMayHaveNonregularTotalSpace M

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter11
