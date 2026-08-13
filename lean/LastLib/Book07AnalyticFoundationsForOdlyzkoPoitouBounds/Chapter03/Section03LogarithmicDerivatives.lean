import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03.Dependencies
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03.Section02EulerProducts
import Mathlib.Analysis.Normed.Module.Connected

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03

noncomputable section

open NumberField IsDedekindDomain
open scoped BigOperators nonZeroDivisors

/-! ### 3.3 Logarithmic derivatives -/

theorem chapter03_log_growth_bound
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ q : ℝ, 1 ≤ q →
      Real.log q ≤ C * Real.rpow q (ε / 2) := by
  refine ⟨2 / ε, fun q hq => ?_⟩
  calc
    Real.log q ≤ Real.rpow q (ε / 2) / (ε / 2) :=
      Real.log_le_rpow_div (le_trans zero_le_one hq) (half_pos hε)
    _ = (2 / ε) * Real.rpow q (ε / 2) := by
      field_simp [ne_of_gt hε]

theorem chapter03_log_derivative_term_hasDerivAt
    (K : Type*) [Field K] [NumberField K]
    (P : Chapter03PrimeIdeal K) (m : ℕ) {s : ℂ} :
    HasDerivAt (fun z : ℂ => chapter03EulerLogTerm P m z)
      (-(Real.log (chapter03PrimeIdealNorm P : ℝ) : ℂ) *
        (chapter03PrimeIdealNorm P : ℂ) ^ (-((m + 1 : ℕ) : ℂ) * s)) s := by
  have hbase : (chapter03PrimeIdealNorm P : ℂ) ≠ 0 := by
    exact_mod_cast (NumberField.HeightOneSpectrum.absNorm_ne_zero P)
  have hn : (m + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero m
  change HasDerivAt (fun z : ℂ =>
      (chapter03PrimeIdealNorm P : ℂ) ^ (-((m + 1 : ℕ) : ℂ) * z) /
        ((m + 1 : ℕ) : ℂ))
    (-(Real.log (chapter03PrimeIdealNorm P : ℝ) : ℂ) *
      (chapter03PrimeIdealNorm P : ℂ) ^ (-((m + 1 : ℕ) : ℂ) * s)) s
  have h :=
    ((hasDerivAt_id' s).const_mul (-((m + 1 : ℕ) : ℂ))).const_cpow
      (c := (chapter03PrimeIdealNorm P : ℂ)) (Or.inl hbase)
  apply (h.div_const ((m + 1 : ℕ) : ℂ)).congr_deriv
  rw [Complex.natCast_log]
  apply (div_eq_iff (by exact_mod_cast hn)).2
  ring

private theorem chapter03_log_derivative_prime_base_norm_summable
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    Summable (fun P : Chapter03PrimeIdeal K =>
      ‖(chapter03PrimeIdealNorm P : ℂ) ^ (-s)‖) := by
  classical
  let e : Chapter03PrimeIdeal K ≃
      {I : Chapter03IntegralIdeal K // (I : Ideal (𝓞 K)).IsPrime} :=
    { toFun := fun P =>
          ⟨⟨P.asIdeal, mem_nonZeroDivisors_of_ne_zero P.ne_bot⟩, P.isPrime⟩
      invFun := fun I =>
          ⟨I.1.1, I.2, mem_nonZeroDivisors_iff_ne_zero.mp I.1.2⟩
      left_inv := by intro P; rfl
      right_inv := by intro I; cases I; rfl }
  have hsub : Summable (fun I :
      {I : Chapter03IntegralIdeal K // (I : Ideal (𝓞 K)).IsPrime} =>
      ‖chapter03IdealTerm s I.1‖) :=
    (chapter03_ideal_series_absolutely_summable K hs).subtype _
  have he : Summable (fun P : Chapter03PrimeIdeal K =>
      ‖chapter03IdealTerm s (e P).1‖) := by
    exact e.summable_iff.mpr hsub
  simpa [e, chapter03IdealTerm, chapter03IdealNorm,
    chapter03AbsoluteIdealNorm, chapter03PrimeIdealNorm] using he

theorem chapter03_log_derivative_series_absolutely_summable
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    Summable (fun q : Chapter03PrimePower K =>
      ‖chapter03LogDerivativeTerm q s‖) := by
  classical
  have hsre : (1 : ℝ) < s.re := hs
  let δ : ℝ := (s.re - 1) / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  let s₀ : ℂ := ((1 + s.re) / 2 : ℝ)
  have hs₀ : s₀ ∈ chapter03EulerHalfPlane := by
    change (1 : ℝ) < (1 + s.re) / 2
    linarith
  have hs₀le : s₀.re ≤ s.re := by
    dsimp [s₀]
    linarith
  obtain ⟨C, hC⟩ := chapter03_log_growth_bound (ε := 2 * δ) (by linarith)
  have hCnonneg : 0 ≤ C := by
    have h := hC 1 (le_rfl)
    simpa using h
  let a : Chapter03PrimeIdeal K → ℝ := fun P =>
    ‖(chapter03PrimeIdealNorm P : ℂ) ^ (-s₀)‖
  have ha : Summable a := by
    simpa [a] using (chapter03_log_derivative_prime_base_norm_summable K hs₀)
  let r : ℝ := Real.rpow 2 (-s₀.re)
  have hr : 0 ≤ r := by
    dsimp [r]
    positivity
  have hrlt : r < 1 := by
    dsimp [r]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    exact neg_lt_zero.mpr (by change 0 < (1 + s.re) / 2; linarith)
  have hgeom : Summable (fun m : ℕ => r ^ m) :=
    summable_geometric_of_lt_one hr hrlt
  have ha_le (P : Chapter03PrimeIdeal K) : a P ≤ r := by
    have hP : 0 < chapter03PrimeIdealNorm P :=
      Nat.zero_lt_of_lt (chapter03_prime_ideal_norm_gt_one P)
    have hP' : (2 : ℝ) ≤ chapter03PrimeIdealNorm P := by
      exact_mod_cast
        ((Nat.succ_le_iff).2 (chapter03_prime_ideal_norm_gt_one P))
    dsimp [a, r]
    rw [Complex.norm_natCast_cpow_of_pos hP]
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) hP'
      (by change -((1 + s.re) / 2) ≤ 0; linarith)
  have hmajor : Summable (fun q : Chapter03PrimePower K =>
      C * a q.1 * r ^ q.2) := by
    exact (ha.mul_left C).mul_of_nonneg hgeom
      (fun P => mul_nonneg hCnonneg (norm_nonneg _)) (fun _ => by positivity)
  apply hmajor.of_nonneg_of_le (fun q => norm_nonneg _)
  intro q
  have hP : 0 < chapter03PrimeIdealNorm q.1 :=
    Nat.zero_lt_of_lt (chapter03_prime_ideal_norm_gt_one q.1)
  have hlog :
      ‖(Real.log (chapter03PrimeIdealNorm q.1 : ℝ) : ℂ)‖ ≤
        C * (chapter03PrimeIdealNorm q.1 : ℝ) ^ δ := by
    have h := hC (chapter03PrimeIdealNorm q.1 : ℝ) (by
      exact_mod_cast (show 1 ≤ chapter03PrimeIdealNorm q.1 by
        exact (Nat.succ_le_iff.mp hP)))
    simpa only [Complex.norm_real,
      Real.norm_of_nonneg (Real.log_natCast_nonneg _)] using
      h.trans_eq (by
        congr 2
        ring)
  have hpow :
      (chapter03PrimeIdealNorm q.1 : ℝ) ^ δ *
          ‖(chapter03PrimeIdealNorm q.1 : ℂ) ^
            (-((q.2 + 1 : ℕ) : ℂ) * s)‖ ≤
        a q.1 * r ^ q.2 := by
    have hpow₀ :
        (chapter03PrimeIdealNorm q.1 : ℝ) ^ δ *
            ‖(chapter03PrimeIdealNorm q.1 : ℂ) ^
              (-((q.2 + 1 : ℕ) : ℂ) * s)‖ ≤
          ‖(chapter03PrimeIdealNorm q.1 : ℂ) ^
            (-((q.2 + 1 : ℕ) : ℂ) * s₀)‖ := by
      rw [Complex.norm_natCast_cpow_of_pos hP,
        Complex.norm_natCast_cpow_of_pos hP]
      rw [← Real.rpow_add (by positivity)]
      apply Real.rpow_le_rpow_of_exponent_le
      · exact_mod_cast (show 1 ≤ chapter03PrimeIdealNorm q.1 from
          Nat.succ_le_iff.mp hP)
      · norm_num [Complex.mul_re]
        have hn : (1 : ℝ) ≤ (q.2 + 1 : ℕ) := by
          exact_mod_cast (Nat.succ_le_succ (Nat.zero_le q.2))
        have hδ' : δ ≤ ((q.2 + 1 : ℕ) : ℝ) * δ :=
          by simpa only [one_mul] using mul_le_mul_of_nonneg_right hn hδ.le
        dsimp [δ, s₀] at hδ' ⊢
        ring_nf at hδ' ⊢
        nlinarith [hδ']
    have hpow₁ :
        ‖(chapter03PrimeIdealNorm q.1 : ℂ) ^
            (-((q.2 + 1 : ℕ) : ℂ) * s₀)‖ = a q.1 ^ (q.2 + 1) := by
      rw [Complex.norm_natCast_cpow_of_pos hP]
      dsimp [a]
      rw [Complex.norm_natCast_cpow_of_pos hP]
      norm_num [Complex.mul_re]
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (by positivity)]
      congr 1
      norm_num [Nat.cast_add, Nat.cast_one]
      ring_nf
    calc
      (chapter03PrimeIdealNorm q.1 : ℝ) ^ δ *
          ‖(chapter03PrimeIdealNorm q.1 : ℂ) ^
            (-((q.2 + 1 : ℕ) : ℂ) * s)‖ ≤
          ‖(chapter03PrimeIdealNorm q.1 : ℂ) ^
            (-((q.2 + 1 : ℕ) : ℂ) * s₀)‖ := hpow₀
      _ = a q.1 ^ (q.2 + 1) := by rw [hpow₁]
      _ ≤ a q.1 * r ^ q.2 := by
        rw [pow_succ, mul_comm]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (ha_le q.1) _)
          (norm_nonneg _)
  change ‖(Real.log (chapter03PrimeIdealNorm q.1 : ℝ) : ℂ) *
      (chapter03PrimeIdealNorm q.1 : ℂ) ^
        (-((q.2 + 1 : ℕ) : ℂ) * s)‖ ≤ C * a q.1 * r ^ q.2
  rw [norm_mul]
  calc
    ‖(Real.log (chapter03PrimeIdealNorm q.1 : ℝ) : ℂ)‖ *
        ‖(chapter03PrimeIdealNorm q.1 : ℂ) ^
          (-((q.2 + 1 : ℕ) : ℂ) * s)‖ ≤
      (C * (chapter03PrimeIdealNorm q.1 : ℝ) ^ δ) *
        ‖(chapter03PrimeIdealNorm q.1 : ℂ) ^
          (-((q.2 + 1 : ℕ) : ℂ) * s)‖ :=
      mul_le_mul_of_nonneg_right hlog (norm_nonneg _)
    _ = C * ((chapter03PrimeIdealNorm q.1 : ℝ) ^ δ *
        ‖(chapter03PrimeIdealNorm q.1 : ℂ) ^
          (-((q.2 + 1 : ℕ) : ℂ) * s)‖) := by ring
    _ ≤ C * (a q.1 * r ^ q.2) := by
      exact mul_le_mul_of_nonneg_left hpow hCnonneg
    _ = C * a q.1 * r ^ q.2 := by ring

theorem chapter03_log_derivative_series_summable
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    Summable (fun q : Chapter03PrimePower K => chapter03LogDerivativeTerm q s) := by
  exact (chapter03_log_derivative_series_absolutely_summable K hs).of_norm

private theorem chapter03_log_derivative_uniform_majorant
    (K : Type*) [Field K] [NumberField K] (ε : ℝ) (hε : 0 < ε) :
    ∃ g : Chapter03PrimePower K → ℝ,
      Summable g ∧
        ∀ q : Chapter03PrimePower K, ∀ s : ℂ,
          s ∈ chapter03EulerHalfPlaneClosed ε →
            ‖chapter03LogDerivativeTerm q s‖ ≤ g q := by
  classical
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  let s₀ : ℂ := (1 + ε / 2 : ℝ)
  have hs₀ : s₀ ∈ chapter03EulerHalfPlane := by
    change (1 : ℝ) < 1 + ε / 2
    linarith
  let a : Chapter03PrimeIdeal K → ℝ := fun P =>
    ‖(chapter03PrimeIdealNorm P : ℂ) ^ (-s₀)‖
  have ha : Summable a := by
    simpa [a] using (chapter03_log_derivative_prime_base_norm_summable K hs₀)
  let r : ℝ := Real.rpow 2 (-s₀.re)
  have hr : 0 ≤ r := by
    dsimp [r]
    positivity
  have hrlt : r < 1 := by
    dsimp [r]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    exact neg_lt_zero.mpr (by change 0 < 1 + ε / 2; linarith)
  have hgeom : Summable (fun m : ℕ => r ^ m) :=
    summable_geometric_of_lt_one hr hrlt
  have ha_le (P : Chapter03PrimeIdeal K) : a P ≤ r := by
    have hP : 0 < chapter03PrimeIdealNorm P :=
      Nat.zero_lt_of_lt (chapter03_prime_ideal_norm_gt_one P)
    have hP' : (2 : ℝ) ≤ chapter03PrimeIdealNorm P := by
      exact_mod_cast
        ((Nat.succ_le_iff).2 (chapter03_prime_ideal_norm_gt_one P))
    dsimp [a, r]
    rw [Complex.norm_natCast_cpow_of_pos hP]
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) hP'
      (by change -(1 + ε / 2) ≤ 0; linarith)
  let g : Chapter03PrimePower K → ℝ := fun q =>
    δ⁻¹ * a q.1 * r ^ q.2
  have hg : Summable g := by
    dsimp [g]
    exact (ha.mul_left δ⁻¹).mul_of_nonneg hgeom
      (fun P => mul_nonneg (inv_nonneg.mpr hδ.le) (norm_nonneg _))
      (fun _ => by positivity)
  refine ⟨g, hg, ?_⟩
  intro q s hs
  have hs' : (1 : ℝ) + ε ≤ s.re := hs
  have hP : 0 < chapter03PrimeIdealNorm q.1 :=
    Nat.zero_lt_of_lt (chapter03_prime_ideal_norm_gt_one q.1)
  have hlog :
      ‖(Real.log (chapter03PrimeIdealNorm q.1 : ℝ) : ℂ)‖ ≤
        (chapter03PrimeIdealNorm q.1 : ℝ) ^ δ / δ := by
    simpa only [Complex.norm_real,
      Real.norm_of_nonneg (Real.log_natCast_nonneg _)] using
      (Real.log_natCast_le_rpow_div (chapter03PrimeIdealNorm q.1) hδ)
  have hpow :
      (chapter03PrimeIdealNorm q.1 : ℝ) ^ δ *
          ‖(chapter03PrimeIdealNorm q.1 : ℂ) ^
            (-((q.2 + 1 : ℕ) : ℂ) * s)‖ ≤
        a q.1 * r ^ q.2 := by
    have hpow₀ :
        (chapter03PrimeIdealNorm q.1 : ℝ) ^ δ *
            ‖(chapter03PrimeIdealNorm q.1 : ℂ) ^
              (-((q.2 + 1 : ℕ) : ℂ) * s)‖ ≤
          ‖(chapter03PrimeIdealNorm q.1 : ℂ) ^
            (-((q.2 + 1 : ℕ) : ℂ) * s₀)‖ := by
      rw [Complex.norm_natCast_cpow_of_pos hP,
        Complex.norm_natCast_cpow_of_pos hP]
      rw [← Real.rpow_add (by positivity)]
      apply Real.rpow_le_rpow_of_exponent_le
      · exact_mod_cast (show 1 ≤ chapter03PrimeIdealNorm q.1 from
          Nat.succ_le_iff.mp hP)
      · norm_num [Complex.mul_re]
        have hn : (1 : ℝ) ≤ (q.2 + 1 : ℕ) := by
          exact_mod_cast (Nat.succ_le_succ (Nat.zero_le q.2))
        have hgap : δ ≤ s.re - s₀.re := by
          dsimp [δ, s₀]
          linarith
        have hngap : δ ≤ ((q.2 + 1 : ℕ) : ℝ) * (s.re - s₀.re) := by
          calc
            δ ≤ s.re - s₀.re := hgap
            _ ≤ ((q.2 + 1 : ℕ) : ℝ) * (s.re - s₀.re) := by
              exact le_mul_of_one_le_left
                ((le_of_lt hδ).trans hgap) hn
        dsimp [s₀] at hngap ⊢
        norm_num [Nat.cast_add, Nat.cast_one] at hngap ⊢
        ring_nf at hngap ⊢
        nlinarith [hngap]
    have hpow₁ :
        ‖(chapter03PrimeIdealNorm q.1 : ℂ) ^
            (-((q.2 + 1 : ℕ) : ℂ) * s₀)‖ = a q.1 ^ (q.2 + 1) := by
      rw [Complex.norm_natCast_cpow_of_pos hP]
      dsimp [a]
      rw [Complex.norm_natCast_cpow_of_pos hP]
      norm_num [Complex.mul_re]
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (by positivity)]
      congr 1
      norm_num [Nat.cast_add, Nat.cast_one]
      ring_nf
    calc
      (chapter03PrimeIdealNorm q.1 : ℝ) ^ δ *
          ‖(chapter03PrimeIdealNorm q.1 : ℂ) ^
            (-((q.2 + 1 : ℕ) : ℂ) * s)‖ ≤
          ‖(chapter03PrimeIdealNorm q.1 : ℂ) ^
            (-((q.2 + 1 : ℕ) : ℂ) * s₀)‖ := hpow₀
      _ = a q.1 ^ (q.2 + 1) := hpow₁
      _ ≤ a q.1 * r ^ q.2 := by
        rw [pow_succ, mul_comm]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (ha_le q.1) _)
          (norm_nonneg _)
  change ‖(Real.log (chapter03PrimeIdealNorm q.1 : ℝ) : ℂ) *
      (chapter03PrimeIdealNorm q.1 : ℂ) ^
        (-((q.2 + 1 : ℕ) : ℂ) * s)‖ ≤ g q
  rw [norm_mul]
  calc
    ‖(Real.log (chapter03PrimeIdealNorm q.1 : ℝ) : ℂ)‖ *
        ‖(chapter03PrimeIdealNorm q.1 : ℂ) ^
          (-((q.2 + 1 : ℕ) : ℂ) * s)‖ ≤
      ((chapter03PrimeIdealNorm q.1 : ℝ) ^ δ / δ) *
        ‖(chapter03PrimeIdealNorm q.1 : ℂ) ^
          (-((q.2 + 1 : ℕ) : ℂ) * s)‖ :=
      mul_le_mul_of_nonneg_right hlog (norm_nonneg _)
    _ = δ⁻¹ * ((chapter03PrimeIdealNorm q.1 : ℝ) ^ δ *
        ‖(chapter03PrimeIdealNorm q.1 : ℂ) ^
          (-((q.2 + 1 : ℕ) : ℂ) * s)‖) := by
      field_simp
    _ ≤ δ⁻¹ * (a q.1 * r ^ q.2) := by
      exact mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr hδ.le)
    _ = g q := by simp [g]; ring

theorem chapter03_log_derivative_series_summable_uniformly_on
    (K : Type*) [Field K] [NumberField K] (ε : ℝ) (hε : 0 < ε) :
    SummableUniformlyOn
      (fun q : Chapter03PrimePower K =>
        fun s : ℂ => chapter03LogDerivativeTerm q s)
      (chapter03EulerHalfPlaneClosed ε) := by
  obtain ⟨g, hg, hbound⟩ :=
    chapter03_log_derivative_uniform_majorant K ε hε
  apply HasSumUniformlyOn.summableUniformlyOn
  rw [hasSumUniformlyOn_iff_tendstoUniformlyOn]
  apply tendstoUniformlyOn_tsum hg
  intro q s hs
  exact hbound q s hs

theorem chapter03_log_derivative_series_norm_summable_uniformly_on
    (K : Type*) [Field K] [NumberField K] (ε : ℝ) (hε : 0 < ε) :
    SummableUniformlyOn
      (fun q : Chapter03PrimePower K =>
        fun s : ℂ => ‖chapter03LogDerivativeTerm q s‖)
      (chapter03EulerHalfPlaneClosed ε) := by
  obtain ⟨g, hg, hbound⟩ :=
    chapter03_log_derivative_uniform_majorant K ε hε
  apply HasSumUniformlyOn.summableUniformlyOn
  rw [hasSumUniformlyOn_iff_tendstoUniformlyOn]
  apply tendstoUniformlyOn_tsum hg
  intro q s hs
  have h := hbound q s hs
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using h

theorem chapter03_log_derivative_nested_series_summable_uniformly_on
    (K : Type*) [Field K] [NumberField K] (ε : ℝ) (hε : 0 < ε) :
    SummableUniformlyOn
      (fun P : Chapter03PrimeIdeal K =>
        fun s : ℂ => ∑' m : ℕ, chapter03LogDerivativeTerm (P, m) s)
      (chapter03EulerHalfPlaneClosed ε) := by
  obtain ⟨g, hg, hbound⟩ :=
    chapter03_log_derivative_uniform_majorant K ε hε
  have hG : Summable (fun P : Chapter03PrimeIdeal K =>
      ∑' m : ℕ, g (P, m)) := by
    refine ⟨∑' q : Chapter03PrimePower K, g q, ?_⟩
    exact hg.hasSum.prod_fiberwise (fun P =>
      (hg.prod_factor P).hasSum)
  apply HasSumUniformlyOn.summableUniformlyOn
  rw [hasSumUniformlyOn_iff_tendstoUniformlyOn]
  apply tendstoUniformlyOn_tsum hG
  intro P s hs
  have hterm : Summable (fun m : ℕ =>
      chapter03LogDerivativeTerm (P, m) s) := by
    apply (hg.prod_factor P).of_norm_bounded
    intro m
    exact hbound (P, m) s hs
  have hnorm := hterm.hasSum.norm_le_of_bounded
    (hg.prod_factor P).hasSum (fun m => hbound (P, m) s hs)
  simpa only [Function.comp_apply] using hnorm

private theorem chapter03_euler_log_series_hasDerivAt
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    HasDerivAt (chapter03EulerLogSeries K)
      (-chapter03LogDerivativeSeries K s) s := by
  classical
  let η : ℝ := (s.re - 1) / 2
  have hsre : (1 : ℝ) < s.re := hs
  have hη : 0 < η := by
    dsimp [η]
    linarith
  have hball_re (y : ℂ) (hy : y ∈ Metric.ball s (η / 2)) :
      y ∈ chapter03EulerHalfPlaneClosed η := by
    have hdist : ‖y - s‖ < η / 2 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hy
    have hrel : -(η / 2) < (y - s).re := by
      exact lt_of_lt_of_le (neg_lt_neg hdist)
        (neg_le_of_abs_le (Complex.abs_re_le_norm _))
    change (1 : ℝ) + η ≤ y.re
    rw [Complex.sub_re] at hrel
    dsimp [η] at hrel ⊢
    linarith
  have hderivProd :
      HasDerivAt
        (fun y : ℂ => ∑' q : Chapter03PrimePower K,
          chapter03EulerLogTerm q.1 q.2 y)
        (∑' q : Chapter03PrimePower K,
          -chapter03LogDerivativeTerm q s) s := by
    obtain ⟨g, hg, hbound⟩ :=
      chapter03_log_derivative_uniform_majorant K η hη
    refine hasDerivAt_tsum_of_isPreconnected
      (u := g) (t := Metric.ball s (η / 2))
      (g := fun q y => chapter03EulerLogTerm q.1 q.2 y)
      (g' := fun q y => -chapter03LogDerivativeTerm q y)
      (y₀ := s) (y := s) hg Metric.isOpen_ball Metric.isPreconnected_ball ?_ ?_ ?_ ?_ ?_
    · intro q y hy
      simpa [chapter03LogDerivativeTerm] using
        (chapter03_log_derivative_term_hasDerivAt K q.1 q.2 (s := y))
    · intro q y hy
      simpa only [norm_neg] using hbound q y (hball_re y hy)
    · exact Metric.mem_ball_self (by positivity)
    · exact chapter03_euler_log_series_summable K hs
    · exact Metric.mem_ball_self (by positivity)
  have hfun : chapter03EulerLogSeries K =ᶠ[nhds s]
      (fun y : ℂ => ∑' q : Chapter03PrimePower K,
        chapter03EulerLogTerm q.1 q.2 y) := by
    filter_upwards [Metric.ball_mem_nhds s (ε := η / 2) (by positivity)] with y hy
    have hy' := hball_re y hy
    have hy'' : y ∈ chapter03EulerHalfPlane := by
      change (1 : ℝ) < y.re
      change (1 : ℝ) + η ≤ y.re at hy'
      linarith
    change (∑' P : Chapter03PrimeIdeal K, ∑' m : ℕ,
      chapter03EulerLogTerm P m y) =
      ∑' q : Chapter03PrimePower K, chapter03EulerLogTerm q.1 q.2 y
    exact (chapter03_euler_log_series_summable K hy'').tsum_prod.symm
  have hderiv := hderivProd.congr_of_eventuallyEq hfun
  have hseries :
      (∑' q : Chapter03PrimePower K, chapter03LogDerivativeTerm q s) =
        chapter03LogDerivativeSeries K s := by
    change ∑' q : Chapter03PrimePower K, chapter03LogDerivativeTerm q s =
      ∑' P : Chapter03PrimeIdeal K, ∑' m : ℕ,
        chapter03LogDerivativeTerm (P, m) s
    exact (chapter03_log_derivative_series_summable K hs).tsum_prod
  apply hderiv.congr_deriv
  rw [tsum_neg, hseries]

theorem chapter03_log_derivative_formula
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    -(deriv (chapter03DedekindZeta K) s) / chapter03DedekindZeta K s =
      chapter03LogDerivativeSeries K s := by
  have hlog := chapter03_euler_log_series_hasDerivAt K hs
  have hzeta_exp :
      HasDerivAt (chapter03DedekindZeta K)
        (Complex.exp (chapter03EulerLogSeries K s) *
          (-chapter03LogDerivativeSeries K s)) s := by
    have hnear :
        chapter03DedekindZeta K =ᶠ[nhds s]
          (fun z : ℂ => Complex.exp (chapter03EulerLogSeries K z)) := by
      filter_upwards [chapter03_euler_half_plane_isOpen.mem_nhds hs] with z hz
      calc
        chapter03DedekindZeta K z = chapter03EulerProduct K z :=
          chapter03_euler_product_eq_dedekind_zeta K hz
        _ = Complex.exp (chapter03EulerLogSeries K z) :=
          chapter03_euler_product_eq_exp_euler_log_series K hz
    exact hlog.cexp.congr_of_eventuallyEq hnear
  have hderiv :
      deriv (chapter03DedekindZeta K) s =
        Complex.exp (chapter03EulerLogSeries K s) *
          (-chapter03LogDerivativeSeries K s) := hzeta_exp.deriv
  have hzeta_value : chapter03DedekindZeta K s =
      Complex.exp (chapter03EulerLogSeries K s) :=
    (chapter03_euler_log_series_exponentiates_to_zeta K hs).symm
  rw [hderiv, hzeta_value]
  field_simp [Complex.exp_ne_zero]

theorem chapter03_log_derivative_formula_explicit
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    -(deriv (chapter03DedekindZeta K) s) / chapter03DedekindZeta K s =
    ∑' P : Chapter03PrimeIdeal K, ∑' m : ℕ,
        (Real.log (chapter03PrimeIdealNorm P : ℝ) : ℂ) *
          (chapter03PrimeIdealNorm P : ℂ) ^
            (-((m + 1 : ℕ) : ℂ) * s) := by
  simpa [chapter03LogDerivativeSeries, chapter03LogDerivativeTerm] using
    (chapter03_log_derivative_formula K hs)

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03
