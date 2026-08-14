import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11

noncomputable section

open NumberField

/-! ## 11.1. The threshold 4 -/

theorem chapter11_minkowski_factor_twelve_formula :
    chapter11MinkowskiFactor 12 =
      Real.rpow ((12 : ℝ) ^ 12 / (Nat.factorial 12 : ℝ)) (1 / 6 : ℝ) := by
  rw [chapter11_minkowski_factor_of_pos 12 (by norm_num)]
  norm_num

theorem chapter11_minkowski_factor_twelve_crosses_four :
    (4 : ℝ) < 4.0432402329 ∧
      4.0432402329 < (Real.pi / 4) * chapter11MinkowskiFactor 12 := by
  constructor
  · norm_num
  · have hpi : (Chapter10.chapter10PiLower : ℝ) < Real.pi :=
      Chapter10.chapter10_pi_directed_bounds.1
    have hfactor : (5.1480133534 : ℝ) < chapter11MinkowskiFactor 12 := by
      rw [chapter11_minkowski_factor_twelve_formula]
      have hpow : (5.1480133534 : ℝ) <
          ((12 : ℝ) ^ 12 / (Nat.factorial 12 : ℝ)) ^ (6 : ℝ)⁻¹ := by
        apply (Real.lt_rpow_inv_iff_of_pos (x := (5.1480133534 : ℝ))
          (y := ((12 : ℝ) ^ 12 / (Nat.factorial 12 : ℝ)))
          (z := (6 : ℝ)) (by norm_num) (by norm_num)
          (by norm_num : (0 : ℝ) < 6)).2
        norm_num [Real.rpow_natCast]
      simpa [one_div] using hpow
    calc
      (4.0432402329 : ℝ) <
          (Chapter10.chapter10PiLower / 4 : ℝ) * 5.1480133534 := by
            norm_num [Chapter10.chapter10PiLower]
      _ < (Real.pi / 4) * 5.1480133534 := by
        exact mul_lt_mul_of_pos_right (div_lt_div_of_pos_right hpi (by norm_num))
          (by norm_num)
      _ < (Real.pi / 4) * chapter11MinkowskiFactor 12 := by
        exact mul_lt_mul_of_pos_left hfactor (by positivity)

theorem chapter11_minkowski_factor_twelve_crosses_four_lower_endpoint :
    (4 : ℝ) < (Real.pi / 4) * chapter11MinkowskiFactor 12 := by
  exact lt_trans (chapter11_minkowski_factor_twelve_crosses_four).1
    (chapter11_minkowski_factor_twelve_crosses_four).2

theorem chapter11_minkowski_factor_six_formula :
    chapter11MinkowskiFactor 6 =
      Real.rpow ((6 : ℝ) ^ 6 / (Nat.factorial 6 : ℝ)) (1 / 3 : ℝ) := by
  rw [chapter11_minkowski_factor_of_pos 6 (by norm_num)]
  norm_num

theorem chapter11_minkowski_factor_six_crosses_four :
    (4 : ℝ) < 4.0165977004 ∧
      4.0165977004 < chapter11MinkowskiFactor 6 := by
  constructor
  · norm_num
  · rw [chapter11_minkowski_factor_six_formula]
    have hpow : (4.0165977004 : ℝ) <
        ((6 : ℝ) ^ 6 / (Nat.factorial 6 : ℝ)) ^ (3 : ℝ)⁻¹ := by
      apply (Real.lt_rpow_inv_iff_of_pos (x := (4.0165977004 : ℝ))
        (y := ((6 : ℝ) ^ 6 / (Nat.factorial 6 : ℝ)))
        (z := (3 : ℝ)) (by norm_num) (by norm_num)
        (by norm_num : (0 : ℝ) < 3)).2
      norm_num [Real.rpow_natCast]
    simpa [one_div] using hpow

theorem chapter11_minkowski_degree_twelve_cutoff
    (K : Type*) [Field K] [NumberField K]
    (hceiling : chapter11RootDiscriminant K < 4) :
    chapter11Degree K ≤ 11 := by
  have h := chapter11_degree_lt_of_worst_signature_crossing K 4 12
    (by norm_num) hceiling
    (chapter11_minkowski_factor_twelve_crosses_four_lower_endpoint)
  omega

theorem chapter11_minkowski_degree_six_totally_real_cutoff
    (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]
    (hceiling : chapter11RootDiscriminant K < 4) :
    chapter11Degree K ≤ 5 := by
  have h := chapter11_degree_lt_of_totally_real_crossing K 4 6
    (by norm_num) hceiling
    (lt_trans (by norm_num : (4 : ℝ) < 4.0165977004)
      (chapter11_minkowski_factor_six_crosses_four).2)
  omega

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
