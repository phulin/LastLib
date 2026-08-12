import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter15.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter15

noncomputable section

open NumberField

/-! ## 15.2. Certified cutoff theorem -/

def chapter15ThreeSqrtThreeCeiling : ℝ :=
  Real.rpow 3 (3 / 2 : ℝ)

def chapter15FiveFourthCeiling : ℝ :=
  Real.rpow 5 (5 / 4 : ℝ)

def chapter15TwoPrimeCeiling : ℝ :=
  Real.rpow 3 (3 / 2 : ℝ) * Real.rpow 2 (2 / 3 : ℝ)

theorem chapter15_three_sqrt_three_ceiling_eq_source :
    chapter15ThreeSqrtThreeCeiling = Real.rpow 3 (3 / 2 : ℝ) :=
  rfl

theorem chapter15_five_fourth_ceiling_eq_source :
    chapter15FiveFourthCeiling = Real.rpow 5 (5 / 4 : ℝ) :=
  rfl

theorem chapter15_two_prime_ceiling_eq_source :
    chapter15TwoPrimeCeiling =
      Real.rpow 3 (3 / 2 : ℝ) * Real.rpow 2 (2 / 3 : ℝ) :=
  rfl

theorem chapter15_degree_cap_below_four
    (K : Type*) [Field K] [NumberField K]
    (hceiling : chapter15RootDiscriminant K < 4) :
    chapter15Degree K ≤ 11 := by
  sorry

theorem chapter15_degree_cap_below_three_sqrt_three
    (K : Type*) [Field K] [NumberField K]
    (hceiling : chapter15RootDiscriminant K < chapter15ThreeSqrtThreeCeiling) :
    chapter15Degree K ≤ 20 := by
  sorry

theorem chapter15_degree_cap_below_five_fourth
    (K : Type*) [Field K] [NumberField K]
    (hceiling : chapter15RootDiscriminant K < chapter15FiveFourthCeiling) :
    chapter15Degree K ≤ 16 := by
  sorry

theorem chapter15_degree_cap_below_two_prime_ceiling
    (K : Type*) [Field K] [NumberField K]
    (hceiling : chapter15RootDiscriminant K < chapter15TwoPrimeCeiling) :
    chapter15Degree K ≤ 20 := by
  sorry

theorem chapter15_certified_cutoff_table
    (K : Type*) [Field K] [NumberField K] :
    (chapter15RootDiscriminant K < 4 → chapter15Degree K ≤ 11) ∧
      (chapter15RootDiscriminant K < chapter15ThreeSqrtThreeCeiling →
        chapter15Degree K ≤ 20) ∧
      (chapter15RootDiscriminant K < chapter15FiveFourthCeiling →
        chapter15Degree K ≤ 16) ∧
      (chapter15RootDiscriminant K < chapter15TwoPrimeCeiling →
        chapter15Degree K ≤ 20) := by
  exact ⟨chapter15_degree_cap_below_four K,
    chapter15_degree_cap_below_three_sqrt_three K,
    chapter15_degree_cap_below_five_fourth K,
    chapter15_degree_cap_below_two_prime_ceiling K⟩

theorem chapter15_totally_real_degree_cap_below_four
    (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]
    (hceiling : chapter15RootDiscriminant K < 4) :
    chapter15Degree K ≤ 5 := by
  sorry

theorem chapter15_totally_real_degree_cap_below_three_sqrt_three
    (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]
    (hceiling : chapter15RootDiscriminant K < chapter15ThreeSqrtThreeCeiling) :
    chapter15Degree K ≤ 12 := by
  sorry

theorem chapter15_totally_real_degree_cap_below_five_fourth
    (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]
    (hceiling : chapter15RootDiscriminant K < chapter15FiveFourthCeiling) :
    chapter15Degree K ≤ 6 := by
  sorry

theorem chapter15_totally_real_certified_cutoff_table
    (K : Type*) [Field K] [NumberField K] [IsTotallyReal K] :
    (chapter15RootDiscriminant K < 4 → chapter15Degree K ≤ 5) ∧
      (chapter15RootDiscriminant K < chapter15ThreeSqrtThreeCeiling →
        chapter15Degree K ≤ 12) ∧
      (chapter15RootDiscriminant K < chapter15FiveFourthCeiling →
        chapter15Degree K ≤ 6) := by
  exact ⟨chapter15_totally_real_degree_cap_below_four K,
    chapter15_totally_real_degree_cap_below_three_sqrt_three K,
    chapter15_totally_real_degree_cap_below_five_fourth K⟩

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter15
