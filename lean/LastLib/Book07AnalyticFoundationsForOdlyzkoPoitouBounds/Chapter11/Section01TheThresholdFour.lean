import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11

noncomputable section

open NumberField

/-! ## 11.1. The threshold 4 -/

theorem chapter11_minkowski_factor_twelve_formula :
    chapter11MinkowskiFactor 12 =
      Real.rpow ((12 : ℝ) ^ 12 / (Nat.factorial 12 : ℝ)) (1 / 6 : ℝ) := by
  sorry

theorem chapter11_minkowski_factor_twelve_crosses_four :
    (4 : ℝ) < 4.0432402329 ∧
      4.0432402329 < (Real.pi / 4) * chapter11MinkowskiFactor 12 := by
  sorry

theorem chapter11_minkowski_factor_twelve_crosses_four_lower_endpoint :
    (4 : ℝ) < (Real.pi / 4) * chapter11MinkowskiFactor 12 := by
  sorry

theorem chapter11_minkowski_factor_six_formula :
    chapter11MinkowskiFactor 6 =
      Real.rpow ((6 : ℝ) ^ 6 / (Nat.factorial 6 : ℝ)) (1 / 3 : ℝ) := by
  sorry

theorem chapter11_minkowski_factor_six_crosses_four :
    (4 : ℝ) < 4.0165977004 ∧
      4.0165977004 < chapter11MinkowskiFactor 6 := by
  sorry

theorem chapter11_minkowski_degree_twelve_cutoff
    (K : Type*) [Field K] [NumberField K]
    (hceiling : chapter11RootDiscriminant K < 4) :
    chapter11Degree K ≤ 11 := by
  sorry

theorem chapter11_minkowski_degree_six_totally_real_cutoff
    (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]
    (hceiling : chapter11RootDiscriminant K < 4) :
    chapter11Degree K ≤ 5 := by
  sorry

/- The two displayed ledger rows are also exposed as one reusable pair. -/
theorem chapter11_threshold_four_degree_caps
    (K : Type*) [Field K] [NumberField K]
    (hceiling : chapter11RootDiscriminant K < 4) :
    chapter11Degree K ≤ 11 := by
  exact chapter11_minkowski_degree_twelve_cutoff K hceiling

theorem chapter11_threshold_four_totally_real_degree_cap
    (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]
    (hceiling : chapter11RootDiscriminant K < 4) :
    chapter11Degree K ≤ 5 := by
  exact chapter11_minkowski_degree_six_totally_real_cutoff K hceiling

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11
