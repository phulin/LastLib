import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11

noncomputable section

open NumberField

/-! ## 11.2. The threshold `3^(3/2)` -/

def chapter11ThreeSqrtThreeCeiling : ℝ :=
  Real.rpow 3 (3 / 2 : ℝ)

theorem chapter11_three_sqrt_three_ceiling_enclosure :
    (5.1961524227 : ℝ) < chapter11ThreeSqrtThreeCeiling ∧
      chapter11ThreeSqrtThreeCeiling < 5.1961524228 := by
  sorry

theorem chapter11_minkowski_factor_fifty_three_formula :
    chapter11MinkowskiFactor 53 =
      Real.rpow ((53 : ℝ) ^ 53 / (Nat.factorial 53 : ℝ)) (2 / 53 : ℝ) := by
  sorry

theorem chapter11_minkowski_factor_fifty_three_crossing :
    (5.2006733020 : ℝ) <
      (Real.pi / 4) * chapter11MinkowskiFactor 53 := by
  sorry

theorem chapter11_three_sqrt_three_minkowski_crossing :
    chapter11ThreeSqrtThreeCeiling <
      (Real.pi / 4) * chapter11MinkowskiFactor 53 := by
  sorry

/- The first excluded degree is 53; no asymptotic limit is used in this row. -/
theorem chapter11_minkowski_degree_fifty_three_cutoff
    (K : Type*) [Field K] [NumberField K]
    (hceiling : chapter11RootDiscriminant K < chapter11ThreeSqrtThreeCeiling) :
    chapter11Degree K ≤ 52 := by
  sorry

theorem chapter11_minkowski_factor_thirteen_formula :
    chapter11MinkowskiFactor 13 =
      Real.rpow ((13 : ℝ) ^ 13 / (Nat.factorial 13 : ℝ)) (2 / 13 : ℝ) := by
  sorry

theorem chapter11_minkowski_factor_thirteen_crossing :
    (5.2610732465 : ℝ) < chapter11MinkowskiFactor 13 := by
  sorry

theorem chapter11_totally_real_three_sqrt_three_crossing :
    chapter11ThreeSqrtThreeCeiling < chapter11MinkowskiFactor 13 := by
  sorry

theorem chapter11_minkowski_degree_thirteen_totally_real_cutoff
    (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]
    (hceiling : chapter11RootDiscriminant K < chapter11ThreeSqrtThreeCeiling) :
    chapter11Degree K ≤ 12 := by
  sorry

theorem chapter11_threshold_three_sqrt_three_degree_cap
    (K : Type*) [Field K] [NumberField K]
    (hceiling : chapter11RootDiscriminant K < chapter11ThreeSqrtThreeCeiling) :
    chapter11Degree K ≤ 52 := by
  exact chapter11_minkowski_degree_fifty_three_cutoff K hceiling

theorem chapter11_threshold_three_sqrt_three_totally_real_degree_cap
    (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]
    (hceiling : chapter11RootDiscriminant K < chapter11ThreeSqrtThreeCeiling) :
    chapter11Degree K ≤ 12 := by
  exact chapter11_minkowski_degree_thirteen_totally_real_cutoff K hceiling

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11
