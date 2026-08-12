import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter14.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter14

noncomputable section

/-! ## 14.2. Bounded step degree is not bounded total degree -/

def chapter14RelativeDegreeBound
    (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L] [FiniteDimensional F L] (C : ℕ) : Prop :=
  Module.finrank F L ≤ C

theorem chapter14_number_field_tower_degree_formula
    (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L] [Algebra ℚ F] [Algebra ℚ L]
    [IsScalarTower ℚ F L] [FiniteDimensional F L] :
    chapter14Degree L = chapter14Degree F * Module.finrank F L := by
  sorry

theorem chapter14_exponential_profile_total_degree
    (C m : ℕ) :
    (chapter14ExponentialTowerDegreeProfile C).totalDegree m = C ^ m := by
  rfl

theorem chapter14_bounded_step_degree_allows_exponential_total_degree
    {C : ℕ} (hC : 1 < C) :
    chapter14UnboundedDegreeProfile
      (chapter14ExponentialTowerDegreeProfile C) := by
  sorry

def chapter14FixedStepRamificationScenario (C : ℕ) : Prop :=
  ∃ P : Chapter14LocalTowerRamificationProfile C,
    chapter14UnboundedRamificationDepth P

theorem chapter14_bounded_step_degree_does_not_bound_tower_ramification_depth
    (C : ℕ) : chapter14FixedStepRamificationScenario C := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter14
