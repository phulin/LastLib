import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter13.Section01HypothesisLedger

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter13

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry nonZeroDivisors

universe u v

/-!
## 13.2 The construction pipeline

The records in `Dependencies` carry the geometric stages.  This section adds
the source-order arrows, the diagnostic table, and the comparison statements
needed to use those stages as an API.
-/

/-! ### Projective closure, normalization, and regularization -/

structure Chapter13ConstructionPipelineArrows
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (P : Chapter13ConstructionPipeline C S η) where
  generic_inclusion : C.carrier ⟶ P.embedding.ambient
  projective_closure : P.closure.closure ⟶ S.carrier
  normalization : P.normalization.normalized ⟶ P.closure.closure
  regularization : P.regular_model.regularized ⟶ P.normalization.normalized

def chapter13ConstructionPipelineArrows
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (P : Chapter13ConstructionPipeline C S η) :
    Chapter13ConstructionPipelineArrows P :=
  { generic_inclusion := P.embedding.inclusion
    projective_closure := P.closure.closure_map
    normalization := P.normalization.normalization_map
    regularization := P.regular_model.resolution_map }

theorem chapter13_pipeline_normalization_is_finite
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (P : Chapter13ConstructionPipeline C S η) :
    IsFinite P.normalization.normalization_map :=
  P.normalization.finite

theorem chapter13_pipeline_normalized_stage_is_normal
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (P : Chapter13ConstructionPipeline C S η) :
    Chapter13NormalScheme P.normalization.normalized :=
  P.normalization.normal

theorem chapter13_pipeline_regular_stage_is_regular
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (P : Chapter13ConstructionPipeline C S η) :
    Chapter13RegularScheme P.regular_model.regularized :=
  P.regular_model.regular

theorem chapter13_pipeline_regularization_map_is_proper
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (P : Chapter13ConstructionPipeline C S η) :
    IsProper P.regular_model.resolution_map :=
  P.regular_model.proper

theorem chapter13_pipeline_regular_stage_is_projective_over_the_base
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (P : Chapter13ConstructionPipeline C S η) :
    chapter13ProjectiveMorphism
      (P.regular_model.resolution_map ≫ P.closure.closure_map) :=
  P.regular_model.projective

/-! ### Diagnostics and their prescribed repairs -/

inductive Chapter13PipelineDefect
  | unwantedVerticalComponents
  | missingIntegralFunctionsOrBranches
  | singularClosedSurfacePoints
  | spoiledAfterRamifiedBaseChange
  | superfluousExceptionalCurves
  deriving DecidableEq

inductive Chapter13PipelineRepair
  | takeSchematicClosure
  | removeBaseTorsion
  | normalize
  | resolveNormalizedBlowups
  | contractExceptionalCurves
  deriving DecidableEq

def chapter13RepairsFor : Chapter13PipelineDefect → List Chapter13PipelineRepair
  | .unwantedVerticalComponents =>
      [.takeSchematicClosure, .removeBaseTorsion]
  | .missingIntegralFunctionsOrBranches => [.normalize]
  | .singularClosedSurfacePoints => [.resolveNormalizedBlowups]
  | .spoiledAfterRamifiedBaseChange => [.normalize, .resolveNormalizedBlowups]
  | .superfluousExceptionalCurves => [.contractExceptionalCurves]

theorem chapter13_unwanted_vertical_components_have_the_recorded_repairs :
    chapter13RepairsFor .unwantedVerticalComponents =
      [.takeSchematicClosure, .removeBaseTorsion] :=
  rfl

theorem chapter13_missing_integral_functions_call_for_normalization :
    chapter13RepairsFor .missingIntegralFunctionsOrBranches = [.normalize] :=
  rfl

theorem chapter13_singular_closed_points_call_for_resolution :
    chapter13RepairsFor .singularClosedSurfacePoints =
      [.resolveNormalizedBlowups] :=
  rfl

/-! ### Common dominations and finite extensions -/

theorem chapter13_two_regular_proper_models_have_a_common_regular_domination
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier)
    (M₁ M₂ : Chapter13RegularProperModel C S η) :
    Nonempty (Chapter13CommonRegularDomination
      M₁.carrier M₂.carrier M₁.structureMap M₂.structureMap) := by
  sorry

theorem chapter13_base_change_repair_has_finite_normalization
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    {M : Chapter13RegularProperModel C S η}
    {E : Chapter13FiniteSeparableExtension K}
    (R : Chapter13BaseChangeRepair C S η M E) :
    IsFinite R.normalization_map :=
  R.normalization_finite

theorem chapter13_base_change_repair_restores_normality_and_regularity
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    {M : Chapter13RegularProperModel C S η}
    {E : Chapter13FiniteSeparableExtension K}
    (R : Chapter13BaseChangeRepair C S η M E) :
    Chapter13NormalScheme R.normalized ∧
      Chapter13RegularScheme R.resolved :=
  ⟨R.normalized_normal, R.resolved_regular⟩

theorem chapter13_finite_separable_extension_is_the_base_change_input
    {K : Type u} [Field K]
    (E : Chapter13FiniteSeparableExtension K) :
    FiniteDimensional K E.extension ∧
      Algebra.IsSeparable K E.extension :=
  ⟨inferInstance, inferInstance⟩

/-! ### Minimal and semistable endpoints -/

theorem chapter13_positive_genus_model_has_a_minimal_endpoint
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (hgenus : 0 < C.genus)
    (S : Chapter13ExcellentDedekindScheme)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier) :
    Nonempty (Chapter13MinimalRegularModel C S η) :=
  chapter13_minimal_regular_model_exists C hgenus S η

theorem chapter13_minimal_endpoint_has_no_vertical_exceptional_curve
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (M : Chapter13MinimalRegularModel C S η) :
    chapter13RelativelyMinimal M.model :=
  M.relatively_minimal

theorem chapter13_positive_genus_contracts_to_a_minimal_endpoint
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (M : Chapter13RegularProperModel C S η)
    (hgenus : 0 < C.genus) :
    Nonempty (Chapter13ContractionToMinimal M) := by
  sorry

theorem chapter13_semistable_input_is_followed_by_regularization
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier)
    (H : Chapter13SemistableReductionInput C S η) :
    Nonempty (Chapter13SemistableRegularIncarnation H) :=
  chapter13_semistable_input_gives_regular_incarnation C S η H

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter13
