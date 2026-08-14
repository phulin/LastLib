import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter13.Section02ConstructionPipeline

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter13

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry nonZeroDivisors

universe u

/-!
## 13.3 Conclusion

This leaf records the final synthesis interfaces and the distinctions that
the chapter insists on keeping visible: generic dimension one versus total
dimension two, regularity of the total space versus smoothness of a morphism,
and semistability as an additional fiber condition.
-/

/-! ### The two lives of an arithmetic curve -/

theorem chapter13_generic_life_is_smooth_projective_dimension_one
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (L : Chapter13ArithmeticCurveTwoLives C S η) :
    Chapter13PureDimensionOne L.generic_life.carrier := by
  sorry

theorem chapter13_integral_life_is_regular_dimension_two
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (L : Chapter13ArithmeticCurveTwoLives C S η) :
    Chapter13RegularScheme L.integral_life.carrier ∧
      Chapter13AbsoluteDimensionTwo L.integral_life.carrier :=
  ⟨L.integral_life.regular, L.integral_dimension_two⟩

theorem chapter13_integral_life_is_proper_and_projective
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (L : Chapter13ArithmeticCurveTwoLives C S η) :
    IsProper L.integral_life.structureMap ∧
      chapter13ProjectiveMorphism L.integral_life.structureMap :=
  ⟨L.integral_life.proper, L.integral_life.projective⟩

theorem chapter13_synthesis_conclusion_has_two_lives
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier) :
    Nonempty (Chapter13ArithmeticCurveTwoLives C S η) := by
  sorry

/-! ### Resolution, termination, and comparison -/

theorem chapter13_excellent_surface_resolution_exists
    {X : Scheme.{u}} (hX : Chapter13ExcellentScheme X) :
    Nonempty (Chapter13SurfaceResolutionResult X) := by
  sorry

theorem chapter13_surface_resolution_result_is_regular_and_proper
    {X : Scheme.{u}}
    (R : Chapter13SurfaceResolutionResult X) :
    Chapter13RegularScheme R.resolved ∧ IsProper R.map :=
  ⟨R.regular, R.proper⟩

theorem chapter13_surface_resolution_has_controlled_exceptional_locus
    {X : Scheme.{u}}
    (R : Chapter13SurfaceResolutionResult X) :
    Chapter13ControlledVerticalExceptionalLocus R.map ∧
      Chapter13IsomorphismOffSingularLocus R.map :=
  ⟨R.controlled_vertical_exceptional_curves, R.isomorphism_off_singular_locus⟩

theorem chapter13_surface_resolution_termination_is_well_founded :
    WellFounded chapter13ComplexityLt :=
  chapter13_resolution_complexity_well_founded

theorem chapter13_common_dominations_are_regular :
    ∀ {S X Y : Scheme.{u}} (fX : X ⟶ S) (fY : Y ⟶ S),
      ∀ D : Chapter13CommonRegularDomination X Y fX fY,
        Chapter13RegularScheme D.carrier := by
  intro S X Y fX fY D
  exact D.regular

/-! ### Distinct strength of the adjectives -/

theorem chapter13_regular_total_space_does_not_entail_smoothness :
    ¬ (∀ {X S : Scheme.{u}} (f : X ⟶ S),
      Chapter13RegularScheme X → Smooth f) := by
  sorry

theorem chapter13_semistability_records_stronger_fiber_conditions
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (M : Chapter13SemistableModel C S η) :
    Chapter13ReducedSpecialFibers M.model ∧
      Chapter13OrdinaryDoublePoints M.model ∧
      Chapter13TransverseComponents M.model ∧
      Chapter13NodeLocalEquation M.model :=
  ⟨M.reduced_special_fibers, M.ordinary_double_points,
    M.transverse_components, M.node_local_equation⟩

theorem chapter13_smoothness_has_the_recorded_fiber_consequences
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] :
    Flat f ∧ Nonempty (Chapter13GeometricallyRegularFibers f) :=
  chapter13_smooth_supplies_flat_and_geometrically_regular_fibers f

/-! ### The final output package -/

theorem chapter13_regular_proper_models_are_available
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier) :
    Nonempty (Chapter13RegularProperModel C S η) :=
  chapter13_regular_proper_model_exists C S η

theorem chapter13_finite_extension_repair_is_available
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier)
    (M : Chapter13RegularProperModel C S η)
    (E : Chapter13FiniteSeparableExtension K) :
    Nonempty (Chapter13BaseChangeRepair C S η M E) :=
  chapter13_normalize_and_resolve_after_finite_base_change C S η M E

theorem chapter13_positive_genus_has_a_minimal_regular_model
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (hgenus : 0 < C.genus)
    (S : Chapter13ExcellentDedekindScheme)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier) :
    Nonempty (Chapter13MinimalRegularModel C S η) :=
  chapter13_minimal_regular_model_exists C hgenus S η

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter13
