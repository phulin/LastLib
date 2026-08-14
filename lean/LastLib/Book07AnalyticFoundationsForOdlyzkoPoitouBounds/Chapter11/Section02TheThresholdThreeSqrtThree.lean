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
  have hsq : chapter11ThreeSqrtThreeCeiling ^ (2 : ℕ) = (27 : ℝ) := by
    unfold chapter11ThreeSqrtThreeCeiling
    calc
      (Real.rpow (3 : ℝ) (3 / 2 : ℝ)) ^ (2 : ℕ) =
          Real.rpow (Real.rpow (3 : ℝ) (3 / 2 : ℝ)) (2 : ℝ) := by
            exact (Real.rpow_natCast
              (Real.rpow (3 : ℝ) (3 / 2 : ℝ)) 2).symm
      _ = Real.rpow (3 : ℝ) ((3 / 2 : ℝ) * (2 : ℝ)) :=
        (Real.rpow_mul (by norm_num) (3 / 2 : ℝ) (2 : ℝ)).symm
      _ = (27 : ℝ) := by norm_num [Real.rpow_natCast]
  have hnonneg : 0 ≤ chapter11ThreeSqrtThreeCeiling := by
    unfold chapter11ThreeSqrtThreeCeiling
    exact (Real.rpow_pos_of_pos (by norm_num) _).le
  constructor
  · apply (sq_lt_sq₀ (by norm_num) hnonneg).mp
    rw [hsq]
    norm_num
  · apply (sq_lt_sq₀ hnonneg (by norm_num)).mp
    rw [hsq]
    norm_num

theorem chapter11_minkowski_factor_fifty_three_formula :
    chapter11MinkowskiFactor 53 =
      Real.rpow ((53 : ℝ) ^ 53 / (Nat.factorial 53 : ℝ)) (2 / 53 : ℝ) := by
  rw [chapter11_minkowski_factor_of_pos 53 (by norm_num)]
  norm_num

theorem chapter11_minkowski_factor_fifty_three_crossing :
    (5.2006733020 : ℝ) <
      (Real.pi / 4) * chapter11MinkowskiFactor 53 := by
  have hpi : (Chapter10.chapter10PiLower : ℝ) < Real.pi :=
    Chapter10.chapter10_pi_directed_bounds.1
  have hfactor : (6.6217029074 : ℝ) < chapter11MinkowskiFactor 53 := by
    rw [chapter11_minkowski_factor_fifty_three_formula]
    have hbase : 0 ≤ ((53 : ℝ) ^ 53 / (Nat.factorial 53 : ℝ)) := by
      positivity
    have hbase_pos : 0 < ((53 : ℝ) ^ 53 / (Nat.factorial 53 : ℝ)) := by
      positivity
    have hMpow :
        Real.rpow (Real.rpow ((53 : ℝ) ^ 53 / (Nat.factorial 53 : ℝ))
          (2 / 53 : ℝ)) (53 : ℝ) =
          Real.rpow ((53 : ℝ) ^ 53 / (Nat.factorial 53 : ℝ)) (2 : ℝ) := by
      calc
        Real.rpow (Real.rpow ((53 : ℝ) ^ 53 / (Nat.factorial 53 : ℝ))
            (2 / 53 : ℝ)) (53 : ℝ) =
            Real.rpow ((53 : ℝ) ^ 53 / (Nat.factorial 53 : ℝ))
              ((2 / 53 : ℝ) * (53 : ℝ)) :=
          (Real.rpow_mul hbase (2 / 53 : ℝ) (53 : ℝ)).symm
        _ = Real.rpow ((53 : ℝ) ^ 53 / (Nat.factorial 53 : ℝ)) (2 : ℝ) := by
          congr 1
          norm_num
    apply (Real.rpow_lt_rpow_iff (by norm_num) (le_of_lt (Real.rpow_pos_of_pos hbase_pos _))
      (by norm_num : (0 : ℝ) < 53)).mp
    change Real.rpow (6.6217029074 : ℝ) (53 : ℝ) <
      Real.rpow (Real.rpow ((53 : ℝ) ^ 53 / (Nat.factorial 53 : ℝ))
        (2 / 53 : ℝ)) (53 : ℝ)
    rw [hMpow]
    norm_num [Real.rpow_natCast]
  calc
    (5.2006733020 : ℝ) <
        (Chapter10.chapter10PiLower / 4 : ℝ) * 6.6217029074 := by
          norm_num [Chapter10.chapter10PiLower]
    _ < (Real.pi / 4) * 6.6217029074 := by
      exact mul_lt_mul_of_pos_right
        (div_lt_div_of_pos_right hpi (by norm_num)) (by norm_num)
    _ < (Real.pi / 4) * chapter11MinkowskiFactor 53 := by
      exact mul_lt_mul_of_pos_left hfactor (by positivity)

theorem chapter11_three_sqrt_three_minkowski_crossing :
    chapter11ThreeSqrtThreeCeiling <
      (Real.pi / 4) * chapter11MinkowskiFactor 53 := by
  exact lt_trans (chapter11_three_sqrt_three_ceiling_enclosure).2
    (lt_trans (by norm_num : (5.1961524228 : ℝ) < 5.2006733020)
      chapter11_minkowski_factor_fifty_three_crossing)

/- The first excluded degree is 53; no asymptotic limit is used in this row. -/
theorem chapter11_minkowski_degree_fifty_three_cutoff
    (K : Type*) [Field K] [NumberField K]
    (hceiling : chapter11RootDiscriminant K < chapter11ThreeSqrtThreeCeiling) :
    chapter11Degree K ≤ 52 := by
  have h := chapter11_degree_lt_of_worst_signature_crossing K
    chapter11ThreeSqrtThreeCeiling 53 (by norm_num) hceiling
    chapter11_three_sqrt_three_minkowski_crossing
  omega

theorem chapter11_minkowski_factor_thirteen_formula :
    chapter11MinkowskiFactor 13 =
      Real.rpow ((13 : ℝ) ^ 13 / (Nat.factorial 13 : ℝ)) (2 / 13 : ℝ) := by
  rw [chapter11_minkowski_factor_of_pos 13 (by norm_num)]
  norm_num

theorem chapter11_minkowski_factor_thirteen_crossing :
    (5.2610732465 : ℝ) < chapter11MinkowskiFactor 13 := by
  rw [chapter11_minkowski_factor_thirteen_formula]
  have hbase : 0 ≤ ((13 : ℝ) ^ 13 / (Nat.factorial 13 : ℝ)) := by
    positivity
  have hbase_pos : 0 < ((13 : ℝ) ^ 13 / (Nat.factorial 13 : ℝ)) := by
    positivity
  have hMpow :
      Real.rpow (Real.rpow ((13 : ℝ) ^ 13 / (Nat.factorial 13 : ℝ))
        (2 / 13 : ℝ)) (13 : ℝ) =
        Real.rpow ((13 : ℝ) ^ 13 / (Nat.factorial 13 : ℝ)) (2 : ℝ) := by
    calc
      Real.rpow (Real.rpow ((13 : ℝ) ^ 13 / (Nat.factorial 13 : ℝ))
          (2 / 13 : ℝ)) (13 : ℝ) =
          Real.rpow ((13 : ℝ) ^ 13 / (Nat.factorial 13 : ℝ))
            ((2 / 13 : ℝ) * (13 : ℝ)) :=
        (Real.rpow_mul hbase (2 / 13 : ℝ) (13 : ℝ)).symm
      _ = Real.rpow ((13 : ℝ) ^ 13 / (Nat.factorial 13 : ℝ)) (2 : ℝ) := by
        congr 1
        norm_num
  apply (Real.rpow_lt_rpow_iff (by norm_num) (le_of_lt (Real.rpow_pos_of_pos hbase_pos _))
    (by norm_num : (0 : ℝ) < 13)).mp
  change Real.rpow (5.2610732465 : ℝ) (13 : ℝ) <
    Real.rpow (Real.rpow ((13 : ℝ) ^ 13 / (Nat.factorial 13 : ℝ))
      (2 / 13 : ℝ)) (13 : ℝ)
  rw [hMpow]
  norm_num [Real.rpow_natCast]

theorem chapter11_totally_real_three_sqrt_three_crossing :
    chapter11ThreeSqrtThreeCeiling < chapter11MinkowskiFactor 13 := by
  exact lt_trans (chapter11_three_sqrt_three_ceiling_enclosure).2
    (lt_trans (by norm_num : (5.1961524228 : ℝ) < 5.2610732465)
      chapter11_minkowski_factor_thirteen_crossing)

theorem chapter11_minkowski_degree_thirteen_totally_real_cutoff
    (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]
    (hceiling : chapter11RootDiscriminant K < chapter11ThreeSqrtThreeCeiling) :
    chapter11Degree K ≤ 12 := by
  have h := chapter11_degree_lt_of_totally_real_crossing K
    chapter11ThreeSqrtThreeCeiling 13 (by norm_num) hceiling
    chapter11_totally_real_three_sqrt_three_crossing
  omega

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
