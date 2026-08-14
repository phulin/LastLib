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
    {S : Chapter13ExcellentDedekindScheme K}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (L : Chapter13ArithmeticCurveTwoLives C S η) :
    Chapter13PureDimensionOne L.generic_life.carrier := by
  sorry

theorem chapter13_integral_life_is_regular_dimension_two
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme K}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (L : Chapter13ArithmeticCurveTwoLives C S η) :
    Chapter13RegularScheme L.integral_life.carrier ∧
      Chapter13AbsoluteDimensionTwo L.integral_life.carrier :=
  ⟨L.integral_life.regular, L.integral_dimension_two⟩

theorem chapter13_integral_life_is_proper_and_projective
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme K}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (L : Chapter13ArithmeticCurveTwoLives C S η) :
    IsProper L.integral_life.structureMap ∧
      chapter13ProjectiveMorphism L.integral_life.structureMap :=
  ⟨L.integral_life.proper, L.integral_life.projective⟩

theorem chapter13_synthesis_conclusion_has_two_lives
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme K)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier)
    (hη : η = chapter13GenericPointMap S) :
    Nonempty (Chapter13ArithmeticCurveTwoLives C S η) := by
  sorry

/-! ### Resolution, termination, and comparison -/

theorem chapter13_excellent_surface_resolution_exists
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hX : Chapter13ExcellentScheme X)
    (hReduced : Chapter13ReducedScheme X)
    (hDim : Chapter13SurfaceDimensionBound X)
    (hProj : chapter13ProjectiveMorphism f) :
    Nonempty (Chapter13SurfaceResolutionResult f) := by
  sorry

theorem chapter13_surface_resolution_result_is_regular_and_proper
    {X S : Scheme.{u}} {f : X ⟶ S}
    (R : Chapter13SurfaceResolutionResult f) :
    Chapter13RegularScheme R.resolved ∧ IsProper R.map ∧
      chapter13ProjectiveMorphism (R.map ≫ f) :=
  ⟨R.regular, R.proper, R.projective⟩

theorem chapter13_surface_resolution_has_controlled_exceptional_locus
    {X S : Scheme.{u}} {f : X ⟶ S}
    (R : Chapter13SurfaceResolutionResult f) :
    Chapter13ControlledExceptionalLocus R.map ∧
      Chapter13IsomorphismOffSingularLocus R.map :=
  ⟨R.controlled_exceptional_locus, R.isomorphism_off_singular_locus⟩

theorem chapter13_surface_resolution_termination_is_well_founded :
    WellFounded chapter13ComplexityLt :=
  chapter13_resolution_complexity_well_founded

theorem chapter13_common_dominations_are_regular :
    ∀ {K : Type u} [Field K]
      (C : Chapter13SmoothProjectiveCurve K)
      (S : Chapter13ExcellentDedekindScheme K)
      (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier)
      (X Y : Scheme.{u}) (fX : X ⟶ S.carrier) (fY : Y ⟶ S.carrier),
      ∀ D : Chapter13CommonRegularDomination C S η X Y fX fY,
        Chapter13RegularScheme D.carrier := by
  intro K _ C S η X Y fX fY D
  exact D.regular

/-! ### Distinct strength of the adjectives -/

theorem chapter13_regular_total_space_does_not_entail_smoothness :
    ¬ (∀ {X S : Scheme.{u}} (f : X ⟶ S),
      Chapter13RegularScheme X → Smooth f) := by
  sorry

theorem chapter13_semistability_records_stronger_fiber_conditions
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme K}
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
    Flat f ∧ Chapter13GeometricallyRegularFibers f :=
  chapter13_smooth_supplies_flat_and_geometrically_regular_fibers f

/-! ### The final output package -/

theorem chapter13_regular_proper_models_are_available
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme K)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier)
    (hη : η = chapter13GenericPointMap S) :
    Nonempty (Chapter13RegularProperModel C S η) :=
  chapter13_regular_proper_model_exists C S η hη

theorem chapter13_finite_extension_repair_is_available
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme K)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier)
    (hη : η = chapter13GenericPointMap S)
    (M : Chapter13RegularProperModel C S η)
    (E : Chapter13FiniteExtension K) :
    Nonempty (Chapter13BaseChangeRepair C S η M E) :=
  chapter13_normalize_and_resolve_after_finite_base_change C S η hη M E

theorem chapter13_positive_genus_has_a_minimal_regular_model
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (hgenus : 0 < C.genus)
    (S : Chapter13ExcellentDedekindScheme K)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier)
    (hη : η = chapter13GenericPointMap S) :
    Nonempty (Chapter13MinimalRegularModel C S η) :=
  chapter13_minimal_regular_model_exists C hgenus S η hη

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter13
