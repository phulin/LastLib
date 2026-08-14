import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.Dependencies
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.MeanValue

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05

/-! ### 6.5. Removing the truncations -/

theorem chapter06_basic_zero_summand_summable
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) {F : ℝ → ℝ}
    (hF : Chapter06BasicallyAdmissible F) :
    Summable (fun ρ : ℂ => chapter06ZeroSummand Z F ρ) := by
  classical
  let S : ℕ → Set ℂ := fun n => {ρ | (ρ ∉ Z.support ∧ n = 0) ∨
    (ρ ∈ Z.support ∧ Nat.ceil |ρ.im| = n)}
  have hpartition : ∀ ρ : ℂ, ∃! n : ℕ, ρ ∈ S n := by
    intro ρ
    by_cases hρ : ρ ∈ Z.support
    · refine ⟨Nat.ceil |ρ.im|, ?_, ?_⟩
      · exact Or.inr ⟨hρ, rfl⟩
      · intro n hn
        change (ρ ∉ Z.support ∧ n = 0) ∨
          (ρ ∈ Z.support ∧ Nat.ceil |ρ.im| = n) at hn
        rcases hn with ⟨hnρ, hn0⟩ | hn
        · exact False.elim (hnρ hρ)
        · exact hn.2.symm
    · refine ⟨0, ?_, ?_⟩
      · exact Or.inl ⟨hρ, rfl⟩
      · intro n hn
        change (ρ ∉ Z.support ∧ n = 0) ∨
          (ρ ∈ Z.support ∧ Nat.ceil |ρ.im| = n) at hn
        rcases hn with ⟨_, hn0⟩ | hn
        · exact hn0
        · exact False.elim (hρ hn.1)
  let f : ℂ → ℂ := fun ρ => chapter06ZeroSummand Z F ρ
  let b : ℂ → ℝ := fun ρ => ‖f ρ‖
  have hfiniteS : ∀ n : ℕ, 0 < n → (S n).Finite := by
    intro n hn
    apply (Z.locally_finite ((n : ℝ) + 1)).subset
    intro ρ hρ
    change (ρ ∉ Z.support ∧ n = 0) ∨
      (ρ ∈ Z.support ∧ Nat.ceil |ρ.im| = n) at hρ
    rcases hρ with ⟨_, hn0⟩ | hρ
    · omega
    · refine ⟨hρ.1, ?_⟩
      have hupper : |ρ.im| ≤ (n : ℝ) := (Nat.ceil_le).mp hρ.2.le
      linarith
  have hfinite_component : ∀ n : ℕ, Summable (fun ρ : S n => b ρ) := by
    intro n
    by_cases hn : n = 0
    · subst n
      let P : Set (S 0) :=
        Subtype.val ⁻¹' {ρ : ℂ | ρ ∈ Z.support ∧ |ρ.im| < 1}
      have hP : P.Finite := by
        have hP' : Set.Finite
            ((Subtype.val : S 0 → ℂ) ⁻¹'
              {ρ : ℂ | ρ ∈ Z.support ∧ |ρ.im| < 1}) :=
          (Z.locally_finite (1 : ℝ)).preimage
            (fun x _ y _ hxy => Subtype.ext hxy)
        simpa [P] using hP'
      exact summable_of_ne_finset_zero (s := hP.toFinset) (by
        intro ρ hρ
        have hmzero : Z.multiplicity (ρ : ℂ) = 0 := by
          apply Nat.eq_zero_of_not_pos
          intro hmpos
          have hsupport : (ρ : ℂ) ∈ Z.support :=
            (Z.support_iff_multiplicity_ne_zero (ρ : ℂ)).mpr
              (Nat.ne_of_gt hmpos)
          have hS := ρ.property
          change ((ρ : ℂ) ∉ Z.support ∧ 0 = 0) ∨
            ((ρ : ℂ) ∈ Z.support ∧ Nat.ceil |(ρ : ℂ).im| = 0) at hS
          rcases hS with ⟨hnot, _⟩ | hS
          · exact hnot hsupport
          · have hheight : |(ρ : ℂ).im| ≤ (0 : ℝ) := by
              simpa using (Nat.ceil_le).mp hS.2.le
            apply hρ
            exact hP.mem_toFinset.mpr ⟨hsupport, by linarith⟩
        simp [b, f, chapter06ZeroSummand, hmzero])
    · let hFintype : Fintype (S n) :=
        (hfiniteS n (Nat.pos_of_ne_zero hn)).fintype
      exact summable_of_ne_finset_zero (s := @Finset.univ (S n) hFintype)
        (fun ρ hρ => False.elim (hρ (by simp)))
  have htsum_finite : ∀ (T : Set ℂ) (hT : T.Finite),
      (∑' ρ : T, b ρ) = hT.toFinset.sum b := by
    intro T hT
    rw [tsum_subtype]
    have hsum : hT.toFinset.sum (T.indicator b) = hT.toFinset.sum b := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      rw [Set.indicator_of_mem]
      exact hT.mem_toFinset.mp hρ
    rw [← hsum]
    exact (hasSum_sum_of_ne_finset_zero (f := T.indicator b)
      (s := hT.toFinset) (by
        intro ρ hρ
        have hmem : ρ ∉ T := by
          intro hmem
          exact hρ (hT.mem_toFinset.mpr hmem)
        simp [Set.indicator, hmem])).tsum_eq
  obtain ⟨Cdec, hCdec, hdecay⟩ :=
    chapter05_basically_admissible_vertical_decay hF 1 (by norm_num)
  have hrepr : ∀ ρ : ℂ, ρ = (ρ.re : ℂ) + (ρ.im : ℂ) * Complex.I := by
    intro ρ
    apply Complex.ext <;> simp
  have hnorm : ∀ ρ : ℂ, b ρ =
      (Z.multiplicity ρ : ℝ) * ‖chapter06Phi F ρ‖ := by
    intro ρ
    simp [b, f, chapter06ZeroSummand]
  have hterm : ∀ (n : ℕ), 0 < n → ∀ ρ : ℂ,
      ρ ∈ Z.support → (n : ℝ) - 1 < |ρ.im| → |ρ.im| ≤ (n : ℝ) →
      b ρ ≤ (Z.multiplicity ρ : ℝ) * (Cdec / (n : ℝ) ^ 2) := by
    intro n hn ρ hρsupport hlow hupper
    have hstrip := Z.critical_strip hρsupport
    have hre : |ρ.re| ≤ (1 : ℝ) := by
      rw [abs_of_nonneg hstrip.1]
      exact hstrip.2
    have htrans := hdecay ρ.re ρ.im hre
    have htrans' : ‖chapter06Phi F ρ‖ ≤
        Cdec / (1 + |ρ.im|) ^ 2 := by
      calc
        ‖chapter06Phi F ρ‖ =
            ‖chapter06Phi F ((ρ.re : ℂ) + (ρ.im : ℂ) * Complex.I)‖ := by
          exact congrArg norm
            (congrArg (chapter06Phi F) (hrepr ρ))
        _ ≤ Cdec / (1 + |ρ.im|) ^ 2 := htrans
    have hden : (n : ℝ) ^ 2 ≤ (1 + |ρ.im|) ^ 2 := by
      nlinarith [abs_nonneg ρ.im, hlow]
    have hdiv : Cdec / (1 + |ρ.im|) ^ 2 ≤ Cdec / (n : ℝ) ^ 2 := by
      by_cases hCdecpos : 0 < Cdec
      · apply (div_le_div_iff_of_pos_left hCdecpos (by positivity) (by positivity)).2
        exact hden
      · have hCdec0 : Cdec = 0 :=
          le_antisymm (le_of_not_gt hCdecpos) hCdec
        simp [hCdec0]
    rw [hnorm]
    have hfinal : ‖chapter06Phi F ρ‖ ≤ Cdec / (n : ℝ) ^ 2 :=
      htrans'.trans hdiv
    exact mul_le_mul_of_nonneg_left hfinal (by positivity)
  obtain ⟨Ccount, hCcount, hcount⟩ := Z.unit_band_bound
  have hcountdiff : ∀ n : ℕ, 0 < n →
      (chapter06ZeroBandCount Z ((n : ℝ) - 1) : ℝ) ≤
        Ccount * (Real.log (chapter06AbsoluteDiscriminant K) +
          (chapter06Degree K : ℝ) * Real.log ((n : ℝ) + 2)) := by
    intro n hn
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hraw := hcount ((n : ℝ) - 1) (by linarith)
    simpa only [chapter06ZeroBandCount,
      show (n : ℝ) - 1 + 3 = (n : ℝ) + 2 by ring] using hraw
  have hshell_le : ∀ n : ℕ, 0 < n →
      (∑' ρ : S n, b ρ) ≤
        (Cdec / (n : ℝ) ^ 2) * (chapter06ZeroBandCount Z ((n : ℝ) - 1) : ℝ) := by
    intro n hn
    let D : Set ℂ := {ρ | ρ ∈ Z.support ∧
      (n : ℝ) - 1 < |ρ.im| ∧ |ρ.im| ≤ (n : ℝ) - 1 + 1}
    have hD : D.Finite := by
      apply (Z.locally_finite ((n : ℝ) + 1)).subset
      intro ρ hρ
      change ρ ∈ Z.support ∧ |ρ.im| < (n : ℝ) + 1
      exact ⟨hρ.1, by linarith [hρ.2.2]⟩
    have hsub : S n ⊆ D := by
      intro ρ hρ
      change (ρ ∉ Z.support ∧ n = 0) ∨
        (ρ ∈ Z.support ∧ Nat.ceil |ρ.im| = n) at hρ
      rcases hρ with ⟨_, hn0⟩ | hρ
      · omega
      · have hupper : |ρ.im| ≤ (n : ℝ) := (Nat.ceil_le).mp hρ.2.le
        have hceil_lower : n - 1 < Nat.ceil |ρ.im| := by
          rw [hρ.2]
          omega
        have hlow0 : ((n - 1 : ℕ) : ℝ) < |ρ.im| :=
          (Nat.lt_ceil).mp hceil_lower
        have hn1 : 1 ≤ n := hn
        have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
          rw [Nat.cast_sub hn1]
          norm_num
        exact ⟨hρ.1, by simpa [hcast] using hlow0, by linarith [hupper]⟩
    have hsubfin : (hfiniteS n hn).toFinset ⊆ hD.toFinset :=
      (Set.Finite.toFinset_subset_toFinset).2 hsub
    have hsubsum : (hfiniteS n hn).toFinset.sum b ≤ hD.toFinset.sum b :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubfin
        (fun _ _ _ => norm_nonneg _)
    have hDcount :
        (chapter06ZeroBandCount Z ((n : ℝ) - 1) : ℝ) =
          (hD.toFinset.sum (fun ρ => Z.multiplicity ρ) : ℝ) := by
      unfold chapter06ZeroBandCount
      change ((chapter06FiniteMultiplicitySum Z.multiplicity D _ : ℕ) : ℝ) = _
      norm_cast
    rw [htsum_finite (S n) (hfiniteS n hn)]
    calc
      (hfiniteS n hn).toFinset.sum b ≤ hD.toFinset.sum b := hsubsum
      _ ≤ hD.toFinset.sum (fun ρ =>
          (Z.multiplicity ρ : ℝ) * (Cdec / (n : ℝ) ^ 2)) := by
        apply Finset.sum_le_sum
        intro ρ hρ
        have hρD := hD.mem_toFinset.mp hρ
        exact hterm n hn ρ hρD.1 hρD.2.1 (by linarith [hρD.2.2])
      _ = (Cdec / (n : ℝ) ^ 2) *
          hD.toFinset.sum (fun ρ => (Z.multiplicity ρ : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ρ hρ
        ring
      _ = (Cdec / (n : ℝ) ^ 2) *
          (chapter06ZeroBandCount Z ((n : ℝ) - 1) : ℝ) := by
        rw [hDcount]
  have hconst : ∀ n : ℕ, 0 < n →
      1 / (n : ℝ) ^ 2 ≤ 4 / ((n : ℝ) + 1) ^ 2 := by
    intro n hn
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast hn]
  have hsqrt : ∀ n : ℕ, 0 < n →
      ((n : ℝ) + 2) ^ (1 / 2 : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
    intro n hn
    have hbase : (n : ℝ) + 2 ≤ 4 * (n : ℝ) := by
      have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    calc
      ((n : ℝ) + 2) ^ (1 / 2 : ℝ) ≤ (4 * (n : ℝ)) ^ (1 / 2 : ℝ) := by
        apply Real.rpow_le_rpow (by positivity) hbase
        norm_num
      _ = 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) (by positivity)]
        norm_num
  have hsqrt2 : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
    rw [← Real.sqrt_eq_rpow]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hp2 : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 4 := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num)]
    norm_num
    nlinarith [hsqrt2]
  have hratio : ∀ n : ℕ, 0 < n →
      (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2 ≤
        4 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ) := by
    intro n hn
    have hnreal : (0 : ℝ) < n := by positivity
    have hbase : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by
      have hnone : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hz : ((n : ℝ) + 1) ^ (3 / 2 : ℝ) ≤
        4 * (n : ℝ) ^ (3 / 2 : ℝ) := by
      calc
        ((n : ℝ) + 1) ^ (3 / 2 : ℝ) ≤
            (2 * (n : ℝ)) ^ (3 / 2 : ℝ) := by
          apply Real.rpow_le_rpow (by positivity) hbase
          norm_num
        _ = (2 : ℝ) ^ (3 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) := by
          rw [Real.mul_rpow (by norm_num) (by positivity)]
        _ ≤ 4 * (n : ℝ) ^ (3 / 2 : ℝ) := by
          gcongr
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hprod : (n : ℝ) ^ (1 / 2 : ℝ) *
          ((n : ℝ) + 1) ^ (3 / 2 : ℝ) ≤ 4 * (n : ℝ) ^ 2 := by
      calc
        _ ≤ (n : ℝ) ^ (1 / 2 : ℝ) *
            (4 * (n : ℝ) ^ (3 / 2 : ℝ)) := by
          gcongr
        _ = 4 * ((n : ℝ) ^ (1 / 2 : ℝ) *
            (n : ℝ) ^ (3 / 2 : ℝ)) := by ring
        _ = 4 * (n : ℝ) ^ 2 := by
          rw [← Real.rpow_add hnreal]
          norm_num
    exact hprod
  have hlog : ∀ n : ℕ,
      Real.log ((n : ℝ) + 2) ≤ 2 * ((n : ℝ) + 2) ^ (1 / 2 : ℝ) := by
    intro n
    have h := Real.log_le_rpow_div (show 0 ≤ (n : ℝ) + 2 by positivity)
      (show (0 : ℝ) < 1 / 2 by norm_num)
    convert h using 1
    norm_num
    ring
  let v : ℕ → ℝ := fun n => ∑' ρ : S n, b ρ
  have hA0 : 0 ≤ v 0 := by
    dsimp [v]
    exact tsum_nonneg (fun ρ => norm_nonneg (f (ρ : ℂ)))
  let A : ℝ := v 0 + 4 * Cdec * Ccount *
    |Real.log (chapter06AbsoluteDiscriminant K)|
  let B : ℝ := 16 * Cdec * Ccount * (chapter06Degree K : ℝ)
  let q : ℕ → ℝ := fun n =>
    A / ((n : ℝ) + 1) ^ 2 + B / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hq1 : Summable (fun n : ℕ =>
      (1 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
    have h := (Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num)
    convert h using 1
    funext n
    have hn : 0 ≤ (n : ℝ) + 1 := by positivity
    rw [abs_of_nonneg hn]
    norm_num [Real.rpow_natCast]
  have hq2 : Summable (fun n : ℕ =>
      (1 : ℝ) / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)) := by
    have h := (Real.summable_one_div_nat_add_rpow 1 (3 / 2)).2 (by norm_num)
    convert h using 1
    funext n
    rw [abs_of_nonneg (by positivity)]
  have hq : Summable q := by
    dsimp [q]
    simpa [div_eq_mul_inv] using (hq1.mul_left A).add (hq2.mul_left B)
  have hvq : ∀ n : ℕ, v n ≤ q n := by
    intro n
    by_cases hn : n = 0
    · subst n
      dsimp [q, A]
      norm_num
      have htermA : 0 ≤ 4 * Cdec * Ccount *
          |Real.log (chapter06AbsoluteDiscriminant K)| := by positivity
      have htermB : 0 ≤ 16 * Cdec * Ccount *
          (chapter06Degree K : ℝ) := by positivity
      linarith
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hinner :
          Real.log (chapter06AbsoluteDiscriminant K) +
            (chapter06Degree K : ℝ) * Real.log ((n : ℝ) + 2) ≤
          |Real.log (chapter06AbsoluteDiscriminant K)| +
            (chapter06Degree K : ℝ) *
              (2 * ((n : ℝ) + 2) ^ (1 / 2 : ℝ)) := by
        gcongr
        · exact le_abs_self _
        · exact hlog n
      have hbase : v n ≤
          (Cdec / (n : ℝ) ^ 2) *
            (Ccount * (Real.log (chapter06AbsoluteDiscriminant K) +
              (chapter06Degree K : ℝ) * Real.log ((n : ℝ) + 2))) := by
        exact (hshell_le n hnpos).trans
          (mul_le_mul_of_nonneg_left (hcountdiff n hnpos) (by positivity))
      have harith :
          (Cdec / (n : ℝ) ^ 2) *
              (Ccount * (Real.log (chapter06AbsoluteDiscriminant K) +
                (chapter06Degree K : ℝ) * Real.log ((n : ℝ) + 2))) ≤
            (v 0 + 4 * Cdec * Ccount *
                |Real.log (chapter06AbsoluteDiscriminant K)|) /
                ((n : ℝ) + 1) ^ 2 +
              (16 * Cdec * Ccount * (chapter06Degree K : ℝ)) /
                ((n : ℝ) + 1) ^ (3 / 2 : ℝ) := by
        have hleft :
            (Cdec / (n : ℝ) ^ 2) *
                (Ccount * (Real.log (chapter06AbsoluteDiscriminant K) +
                  (chapter06Degree K : ℝ) * Real.log ((n : ℝ) + 2))) ≤
              (Cdec / (n : ℝ) ^ 2) *
                (Ccount * (|Real.log (chapter06AbsoluteDiscriminant K)| +
                  (chapter06Degree K : ℝ) *
                    (2 * ((n : ℝ) + 2) ^ (1 / 2 : ℝ)))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hinner hCcount) (by positivity)
        calc
          _ ≤ (Cdec / (n : ℝ) ^ 2) *
              (Ccount * (|Real.log (chapter06AbsoluteDiscriminant K)| +
                (chapter06Degree K : ℝ) *
                  (2 * ((n : ℝ) + 2) ^ (1 / 2 : ℝ)))) := hleft
          _ = (Cdec * Ccount *
                |Real.log (chapter06AbsoluteDiscriminant K)|) /
                (n : ℝ) ^ 2 +
              (2 * Cdec * Ccount * (chapter06Degree K : ℝ)) *
                (((n : ℝ) + 2) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2) := by ring
          _ ≤ (4 * Cdec * Ccount *
                |Real.log (chapter06AbsoluteDiscriminant K)|) /
                ((n : ℝ) + 1) ^ 2 +
              (2 * Cdec * Ccount * (chapter06Degree K : ℝ)) *
                (8 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)) := by
            have hfirst :
                (Cdec * Ccount *
                  |Real.log (chapter06AbsoluteDiscriminant K)|) /
                    (n : ℝ) ^ 2 ≤
                  (4 * Cdec * Ccount *
                    |Real.log (chapter06AbsoluteDiscriminant K)|) /
                    ((n : ℝ) + 1) ^ 2 := by
              have hcoef : 0 ≤ Cdec * Ccount *
                  |Real.log (chapter06AbsoluteDiscriminant K)| := by positivity
              calc
                _ = (Cdec * Ccount *
                    |Real.log (chapter06AbsoluteDiscriminant K)|) *
                      (1 / (n : ℝ) ^ 2) := by ring
                _ ≤ (Cdec * Ccount *
                    |Real.log (chapter06AbsoluteDiscriminant K)|) *
                      (4 / ((n : ℝ) + 1) ^ 2) := by
                  exact mul_le_mul_of_nonneg_left (hconst n hnpos) hcoef
                _ = _ := by ring
            have hsqrtbound :
                ((n : ℝ) + 2) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2 ≤
                  8 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ) := by
              calc
                _ ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2 :=
                  div_le_div_of_nonneg_right (hsqrt n hnpos) (by positivity)
                _ = 2 * ((n : ℝ) ^ (1 / 2 : ℝ) /
                    (n : ℝ) ^ 2) := by ring
                _ ≤ 2 * (4 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)) := by
                  exact mul_le_mul_of_nonneg_left (hratio n hnpos) (by norm_num)
                _ = 8 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ) := by ring
            have hcoef2 : 0 ≤ 2 * Cdec * Ccount *
                (chapter06Degree K : ℝ) := by positivity
            exact add_le_add hfirst
              (mul_le_mul_of_nonneg_left hsqrtbound hcoef2)
          _ ≤ (v 0 + 4 * Cdec * Ccount *
                |Real.log (chapter06AbsoluteDiscriminant K)|) /
                ((n : ℝ) + 1) ^ 2 +
              (16 * Cdec * Ccount * (chapter06Degree K : ℝ)) /
                ((n : ℝ) + 1) ^ (3 / 2 : ℝ) := by
            have hfirst :
                (4 * Cdec * Ccount *
                  |Real.log (chapter06AbsoluteDiscriminant K)|) /
                    ((n : ℝ) + 1) ^ 2 ≤
                  (v 0 + 4 * Cdec * Ccount *
                    |Real.log (chapter06AbsoluteDiscriminant K)|) /
                    ((n : ℝ) + 1) ^ 2 := by
              exact (div_le_div_of_nonneg_right
                (le_add_of_nonneg_left hA0) (by positivity))
            have hsecond :
                (2 * Cdec * Ccount * (chapter06Degree K : ℝ)) *
                    (8 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)) =
                  (16 * Cdec * Ccount * (chapter06Degree K : ℝ)) /
                    ((n : ℝ) + 1) ^ (3 / 2 : ℝ) := by ring
            exact add_le_add hfirst (le_of_eq hsecond)
      exact hbase.trans harith
  have hv : Summable v := by
    apply Summable.of_norm_bounded hq
    intro n
    have hv_nonneg : 0 ≤ v n := by
      dsimp [v]
      exact tsum_nonneg (fun ρ => norm_nonneg (f (ρ : ℂ)))
    rw [Real.norm_eq_abs, abs_of_nonneg hv_nonneg]
    exact hvq n
  have hpart := summable_partition (f := b)
    (fun ρ => norm_nonneg (f ρ)) hpartition
  have hb : Summable b := by
    apply hpart.mpr
    refine ⟨hfinite_component, ?_⟩
    simpa [v] using hv
  have hnormsum : Summable (fun ρ : ℂ => ‖f ρ‖) := by
    simpa [b] using hb
  have hf : Summable f := hnormsum.of_norm
  simpa [f] using hf

theorem chapter06_canonical_zero_summand_summable
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : Chapter06BasicallyAdmissible F) :
    Summable (fun ρ : ℂ =>
      chapter06ZeroSummand
        (chapter06CanonicalZetaAnalyticPackage K).zeros F ρ) := by
  exact chapter05_symmetric_zero_sum_summable K hF

theorem chapter06_canonical_unconditional_zero_summand_summable
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : Chapter06UnconditionallyAdmissible F) :
    Summable (fun ρ : ℂ =>
      chapter06ZeroSummand
        (chapter06CanonicalZetaAnalyticPackage K).zeros F ρ) := by
  exact chapter06_canonical_zero_summand_summable K hF.1

theorem chapter06_canonical_grh_zero_summand_summable
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : Chapter06GRHAdmissible F) :
    Summable (fun ρ : ℂ =>
      chapter06ZeroSummand
        (chapter06CanonicalZetaAnalyticPackage K).zeros F ρ) := by
  exact chapter06_canonical_zero_summand_summable K hF.basic

theorem chapter06_zero_count_unit_band
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
      ((chapter06ZeroBandCount Z T : ℕ) : ℝ) ≤
        C * (Real.log (chapter06AbsoluteDiscriminant K) +
          (chapter06Degree K : ℝ) * Real.log (T + 3)) := by
  exact Z.unit_band_bound

theorem chapter06_zero_count_increment_bound
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
      (chapter06ZeroBandCount Z T : ℝ) ≤
        C * (Real.log (chapter06AbsoluteDiscriminant K) +
          (chapter06Degree K : ℝ) * Real.log (T + 3)) := by
  exact chapter06_zero_count_unit_band K Z

private theorem chapter06_smooth_compact_basic_of_value_at_zero_early
    {G : ℝ → ℝ} (hG : Chapter06SmoothCompactSupport G) (hG0 : G 0 = 1) :
    Chapter06BasicallyAdmissible G := by
  rcases hG with ⟨hGeven, hGdiff, hGcompact⟩
  have hGderivDiff : Differentiable ℝ (deriv G) := by
    exact (contDiff_infty_iff_deriv.mp hGdiff).2.differentiable (by simp)
  have hGderivDerivCont : Continuous (deriv (deriv G)) := by
    have hGderivDeriv : ContDiff ℝ ∞ (deriv (deriv G)) := by
      exact (contDiff_infty_iff_deriv.mp
        (contDiff_infty_iff_deriv.mp hGdiff).2).2
    exact hGderivDeriv.continuous
  have hGderivDerivCompact : HasCompactSupport (deriv (deriv G)) :=
    hGcompact.deriv.deriv
  obtain ⟨C, hC⟩ := hGderivDerivCompact.exists_bound_of_continuous
    hGderivDerivCont
  let C' : NNReal := ⟨max C (0 : ℝ), le_max_right _ _⟩
  have hC' : ∀ x : ℝ, ‖deriv (deriv G) x‖₊ ≤ C' := by
    intro x
    change ‖deriv (deriv G) x‖ ≤ max C (0 : ℝ)
    exact (hC x).trans (le_max_left _ _)
  have hGderivLipschitz : LipschitzWith C' (deriv G) :=
    lipschitzWith_of_nnnorm_deriv_le hGderivDiff hC'
  have hGderivCompact : HasCompactSupport (deriv G) := hGcompact.deriv
  obtain ⟨R₀, hR₀pos, hR₀⟩ :=
    hGderivCompact.isBounded.subset_closedBall_lt (0 : ℝ) (0 : ℝ)
  let R : ℝ := R₀ + 1
  have hRpos : 0 < R := by
    dsimp [R]
    linarith
  have hGderiv_zero_left : ∀ x : ℝ, x ∈ Iic (-R) → deriv G x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hxt
    have hxball := hR₀ hxt
    have hxabs : |x| ≤ R₀ := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hxball
    have hxabs' : R ≤ |x| := by
      change x ≤ -R at hx
      rw [abs_of_nonpos (by linarith)]
      linarith
    linarith [hR₀pos]
  have hGderiv_zero_right : ∀ x : ℝ, x ∈ Ici R → deriv G x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hxt
    have hxball := hR₀ hxt
    have hxabs : |x| ≤ R₀ := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hxball
    have hxabs' : R ≤ |x| := by
      change R ≤ x at hx
      rw [abs_of_nonneg (by linarith)]
      exact hx
    linarith [hR₀pos]
  have hleft : eVariationOn (deriv G) (Iic (-R)) = 0 := by
    apply eVariationOn.constant_on
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hGderiv_zero_left x hx, hGderiv_zero_left y hy]
  have hright : eVariationOn (deriv G) (Ici R) = 0 := by
    apply eVariationOn.constant_on
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hGderiv_zero_right x hx, hGderiv_zero_right y hy]
  have hmid : BoundedVariationOn (deriv G) (Icc (-R) R) := by
    have hle : eVariationOn (deriv G) (Icc (-R) R) ≤
        C' * eVariationOn id (Icc (-R) R) := by
      exact hGderivLipschitz.lipschitzOnWith.comp_eVariationOn_le
        (mapsTo_id _)
    have hlt : eVariationOn (deriv G) (Icc (-R) R) < (⊤ : ENNReal) := by
      apply lt_of_le_of_lt hle
      rw [eVariationOn_id_Icc]
      exact ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top
    exact hlt.ne
  have hleft_mid_set : Iic (-R) ∪ Icc (-R) R = Iic R := by
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · change x ≤ -R at hx
        exact le_trans hx (by linarith [hRpos.le])
      · exact hx.2
    · intro hx
      by_cases h : x ≤ -R
      · exact Or.inl h
      · exact Or.inr ⟨le_of_not_ge h, hx⟩
  have hmid_right_set : Iic R ∪ Ici R = (Set.univ : Set ℝ) := by
    ext x
    simp only [mem_union, mem_Iic, mem_Ici, mem_univ]
    constructor
    · intro _
      trivial
    · intro _
      exact le_total x R
  have hleft_mid : eVariationOn (deriv G) (Iic R) =
      eVariationOn (deriv G) (Icc (-R) R) := by
    calc
      eVariationOn (deriv G) (Iic R) =
          eVariationOn (deriv G) (Iic (-R) ∪ Icc (-R) R) := by
            rw [hleft_mid_set]
      _ = eVariationOn (deriv G) (Iic (-R)) +
            edist (deriv G (-R)) (deriv G (-R)) +
              eVariationOn (deriv G) (Icc (-R) R) :=
        eVariationOn.union' (deriv G) (s := Iic (-R))
          (t := Icc (-R) R) (x := -R) (y := -R)
          ⟨by simp, fun x hx => hx⟩
          ⟨⟨by rfl, by linarith [hRpos.le]⟩, fun x hx => hx.1⟩ le_rfl
      _ = eVariationOn (deriv G) (Icc (-R) R) := by simp [hleft]
  have htotal : BoundedVariationOn (deriv G) (Set.univ : Set ℝ) := by
    change eVariationOn (deriv G) (Set.univ : Set ℝ) ≠ (⊤ : ENNReal)
    calc
      eVariationOn (deriv G) (Set.univ : Set ℝ) =
          eVariationOn (deriv G) (Iic R ∪ Ici R) := by
            rw [hmid_right_set]
      _ = eVariationOn (deriv G) (Iic R) +
            edist (deriv G R) (deriv G R) +
              eVariationOn (deriv G) (Ici R) :=
        eVariationOn.union' (deriv G) (s := Iic R) (t := Ici R)
          (x := R) (y := R)
          ⟨by simp, fun x hx => hx⟩
          ⟨by simp, fun x hx => hx⟩ le_rfl
      _ = eVariationOn (deriv G) (Icc (-R) R) := by
        simp [hright, hleft_mid]
      _ ≠ (⊤ : ENNReal) := hmid
  refine
    { even := hGeven
      continuous := hGdiff.continuous
      compactSupport := hGcompact
      piecewiseC2 := ?_
      valueAtZero := hG0
      oneSidedDerivativeBV := ?_
      originCondition := ?_ }
  · refine ⟨∅, Set.finite_empty, ?_⟩
    intro x hx
    exact hGdiff.contDiffAt.of_le
      (show (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by
        apply WithTop.coe_le_coe.mpr
        exact le_top)
  · refine ⟨deriv G, deriv G, ?_, ?_, htotal, htotal⟩
    · intro x
      exact ((hGdiff.differentiable (by simp) x).hasDerivAt).hasDerivWithinAt
    · intro x
      exact ((hGdiff.differentiable (by simp) x).hasDerivAt).hasDerivWithinAt
  · exact chapter05_right_corner_origin_condition hG0 hGdiff.continuous
      ((hGdiff.differentiable (by simp) 0).hasDerivAt).hasDerivWithinAt

theorem chapter06_smooth_zero_summand_summable
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) {F : ℝ → ℝ}
    (hF : Chapter06SmoothCompactSupport F) :
    Summable (fun ρ : ℂ => chapter06ZeroSummand Z F ρ) := by
  classical
  rcases hF with ⟨hFeven, hFdiff, hFcompact⟩
  let b : ContDiffBump (0 : ℝ) :=
    { rIn := 1
      rOut := 2
      rIn_pos := by norm_num
      rIn_lt_rOut := by norm_num }
  let B : ℝ → ℝ := b
  have hBdiff : ContDiff ℝ ∞ B := by
    simpa [B] using b.contDiff
  have hBcompact : HasCompactSupport B := by
    simpa [B] using b.hasCompactSupport
  have hBeven : Function.Even B := by
    intro x
    simpa [B] using b.neg x
  have hB0 : B 0 = 1 := by
    have hzero : (0 : ℝ) ∈ Metric.closedBall (0 : ℝ) b.rIn := by
      simp [Metric.mem_closedBall, b]
    simpa [B] using b.one_of_mem_closedBall hzero
  have hB : Chapter06SmoothCompactSupport B := ⟨hBeven, hBdiff, hBcompact⟩
  have hBbasic : Chapter06BasicallyAdmissible B :=
    chapter06_smooth_compact_basic_of_value_at_zero_early hB hB0
  have htransform_integrable :
      ∀ {G : ℝ → ℝ}, Continuous G → HasCompactSupport G → ∀ s : ℂ,
        Integrable
          (fun x : ℝ => (G x : ℂ) * chapter05LaplaceKernel s x) := by
    intro G hGc hGcompact s
    apply Continuous.integrable_of_hasCompactSupport
    · exact (Complex.continuous_ofReal.comp hGc).mul
        (Complex.continuous_exp.comp
          ((continuous_const.sub continuous_const).mul
            (Complex.continuous_ofReal.comp continuous_id)))
    · exact (hGcompact.comp_left (g := fun y : ℝ => (y : ℂ)) (by simp)).mul_right
  have hphi_smul :
      ∀ (a : ℝ) (G : ℝ → ℝ) (s : ℂ),
        chapter06Phi (fun x : ℝ => a * G x) s =
          (a : ℂ) * chapter06Phi G s := by
    intro a G s
    unfold chapter06Phi chapter05BilateralLaplaceTransform
    simpa only [Complex.ofReal_mul, mul_assoc] using
      (MeasureTheory.integral_const_mul (μ := (volume : Measure ℝ))
        (a : ℂ)
        (fun x : ℝ => (G x : ℂ) * chapter05LaplaceKernel s x))
  have hphi_add :
      ∀ (G H : ℝ → ℝ), Continuous G → HasCompactSupport G →
        Continuous H → HasCompactSupport H → ∀ s : ℂ,
          chapter06Phi (fun x : ℝ => G x + H x) s =
            chapter06Phi G s + chapter06Phi H s := by
    intro G H hGc hGcompact hHc hHcompact s
    unfold chapter06Phi chapter05BilateralLaplaceTransform
    simpa only [Complex.ofReal_add, add_mul] using
      (MeasureTheory.integral_add
        (htransform_integrable hGc hGcompact s)
        (htransform_integrable hHc hHcompact s))
  by_cases hF0 : F 0 ≠ 0
  · let G : ℝ → ℝ := fun x => F x / F 0
    have hGeven : Function.Even G := by
      intro x
      dsimp [G]
      rw [hFeven x]
    have hGdiff : ContDiff ℝ ∞ G := by
      simpa [G] using hFdiff.div_const (F 0)
    have hGcompact : HasCompactSupport G := by
      have hEq : G = F * (fun _ : ℝ => (F 0)⁻¹) := by
        funext x
        simp [G, div_eq_mul_inv]
      rw [hEq]
      exact hFcompact.mul_right (f' := fun _ : ℝ => (F 0)⁻¹)
    have hG : Chapter06SmoothCompactSupport G := ⟨hGeven, hGdiff, hGcompact⟩
    have hG0 : G 0 = 1 := by
      simp [G, hF0]
    have hGbasic : Chapter06BasicallyAdmissible G :=
      chapter06_smooth_compact_basic_of_value_at_zero_early hG hG0
    have hFG : F = fun x : ℝ => F 0 * G x := by
      funext x
      dsimp [G]
      field_simp [hF0]
    refine (chapter06_basic_zero_summand_summable K Z hGbasic).mul_left
      (F 0 : ℂ) |>.congr ?_
    intro ρ
    rw [hFG]
    simp only [chapter06ZeroSummand]
    rw [hphi_smul]
    simp [hG0]
    ring
  · let G : ℝ → ℝ := fun x => F x + B x
    have hF0' : F 0 = 0 := by
      exact not_ne_iff.mp hF0
    have hGeven : Function.Even G := by
      intro x
      dsimp [G]
      rw [hFeven x, hBeven x]
    have hGdiff : ContDiff ℝ ∞ G := by
      simpa [G] using hFdiff.add hBdiff
    have hGcompact : HasCompactSupport G := by
      have hEq : G = F + B := by
        funext x
        rfl
      rw [hEq]
      exact hFcompact.add hBcompact
    have hG : Chapter06SmoothCompactSupport G := ⟨hGeven, hGdiff, hGcompact⟩
    have hG0 : G 0 = 1 := by
      simp [G, hF0', hB0]
    have hGbasic : Chapter06BasicallyAdmissible G :=
      chapter06_smooth_compact_basic_of_value_at_zero_early hG hG0
    refine (chapter06_basic_zero_summand_summable K Z hGbasic).sub
        (chapter06_basic_zero_summand_summable K Z hBbasic) |>.congr ?_
    intro ρ
    dsimp [G]
    simp only [chapter06ZeroSummand]
    rw [hphi_add F B hFdiff.continuous hFcompact hBdiff.continuous hBcompact ρ]
    ring

theorem chapter06_zero_partial_sum_tendsto
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) {F : ℝ → ℝ}
    (hF : Chapter06BasicallyAdmissible F)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    Tendsto (fun n => chapter06ZeroPartialSum Z F (T n)) atTop
      (𝓝 (chapter06SymmetricZeroSum Z F)) := by
  classical
  let f : ℂ → ℂ := fun ρ => chapter06ZeroSummand Z F ρ
  have hf : Summable f := by
    simpa only [f] using chapter06_basic_zero_summand_summable K Z hF
  have hsum : HasSum f (∑' ρ : ℂ, f ρ) := hf.hasSum
  have hlim : Tendsto
      (fun T : ℝ => (chapter06ZeroWindowFinset Z T).sum f) atTop
      (𝓝 (∑' ρ : ℂ, f ρ)) := by
    intro U hU
    change ∀ᶠ T : ℝ in atTop,
      (chapter06ZeroWindowFinset Z T).sum f ∈ U
    have hU' : {s : Finset ℂ | s.sum f ∈ U} ∈
        (atTop : Filter (Finset ℂ)) := hsum hU
    rcases mem_atTop_sets.mp hU' with ⟨s, hs⟩
    have hband : ∀ᶠ T : ℝ in atTop,
        0 ≤ T ∧ ∀ ρ ∈ s, |ρ.im| + 1 ≤ T := by
      refine (eventually_ge_atTop (0 : ℝ)).and ?_
      rw [eventually_all_finset]
      intro ρ hρ
      exact eventually_ge_atTop _
    filter_upwards [hband] with T hT'
    have hsum_eq :
        ((chapter06ZeroWindowFinset Z T) ∪ s).sum f =
          (chapter06ZeroWindowFinset Z T).sum f := by
      symm
      apply Finset.sum_subset Finset.subset_union_left
      intro ρ hρ hρnot
      have hρs : ρ ∈ s := by
        rcases Finset.mem_union.mp hρ with hρwindow | hρs
        · exact False.elim (hρnot hρwindow)
        · exact hρs
      have hρzero : Z.multiplicity ρ = 0 := by
        apply Nat.eq_zero_of_not_pos
        intro hmpos
        have hρsupport : ρ ∈ Z.support :=
          (Z.support_iff_multiplicity_ne_zero ρ).mpr (Nat.ne_of_gt hmpos)
        apply hρnot
        apply (Z.locally_finite T).mem_toFinset.mpr
        exact ⟨hρsupport, by linarith [hT'.2 ρ hρs]⟩
      simp [chapter06ZeroSummand, hρzero]
    have hmem : (chapter06ZeroWindowFinset Z T) ∪ s ∈
        {u : Finset ℂ | u.sum f ∈ U} := by
      apply hs
      exact Finset.subset_union_right
    simpa [hsum_eq] using hmem
  change Tendsto
      (fun n => (chapter06ZeroWindowFinset Z (T n)).sum f) atTop
      (𝓝 (∑' ρ : ℂ, f ρ))
  exact hlim.comp hT

theorem chapter06_basic_zero_sum_is_symmetric_limit
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) {F : ℝ → ℝ}
    (hF : Chapter06BasicallyAdmissible F)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    Tendsto (fun n => chapter06ZeroPartialSum Z F (T n)) atTop
      (𝓝 (chapter06SymmetricZeroSum Z F)) := by
  exact chapter06_zero_partial_sum_tendsto K Z hF hT

theorem chapter06_symmetric_zero_value_independent_of_heights
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) {F : ℝ → ℝ}
    (hF : Chapter06BasicallyAdmissible F)
    {T U : ℕ → ℝ} (hT : Tendsto T atTop atTop)
    (hU : Tendsto U atTop atTop) :
    Tendsto (fun n => chapter06ZeroPartialSum Z F (T n) -
      chapter06ZeroPartialSum Z F (U n)) atTop (𝓝 0) := by
  have hT' := chapter06_zero_partial_sum_tendsto K Z hF hT
  have hU' := chapter06_zero_partial_sum_tendsto K Z hF hU
  have hsub := hT'.sub hU'
  simpa using hsub

/-
SOURCE_NOTE (books/007-analytic-foundations-for-odlyzko-poitou-bounds.md:§6.5):
the source gives the standard convolution-and-normalization construction
informally.  The minimal usable interface is
`chapter06ApproximateIdentity` together with the explicit smoothed functions
and origin-correction factor below.
-/
theorem chapter06_approximate_identity_exists :
    ∃ η : ℕ → ℝ → ℝ, chapter06ApproximateIdentity η := by
  let c : ℕ → ContDiffBump (0 : ℝ) := fun n =>
    { rIn := 1 / ((n + 1 : ℕ) : ℝ)
      rOut := 2 / ((n + 1 : ℕ) : ℝ)
      rIn_pos := by positivity
      rIn_lt_rOut := by
        have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
        field_simp
        norm_num }
  let η : ℕ → ℝ → ℝ := fun n => (c n).normed volume
  have hc_out : ∀ n, (c n).rOut ≤ 2 := by
    intro n
    dsimp [c]
    have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
    apply (div_le_iff₀ (by positivity : 0 < ((n + 1 : ℕ) : ℝ))).2
    nlinarith
  have hc_out_tendsto : Tendsto (fun n => (c n).rOut) atTop (𝓝 0) := by
    have hdiv : Tendsto (fun n : ℕ => (2 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      Filter.Tendsto.const_div_atTop tendsto_natCast_atTop_atTop 2
    have hshift := hdiv.comp (tendsto_add_atTop_nat 1)
    simpa [c, Function.comp_def, Nat.cast_add, Nat.cast_one] using hshift
  have hη_integrable : ∀ n, Integrable (η n) := by
    intro n
    simpa [η] using (c n).integrable_normed
  have hη_compact : ∀ n, HasCompactSupport (η n) := by
    intro n
    simpa [η] using (c n).hasCompactSupport_normed
  have hη_support : ∃ R : ℝ, 0 ≤ R ∧ ∀ n,
      Function.support (η n) ⊆ Icc (-R) R := by
    refine ⟨2, by norm_num, ?_⟩
    intro n
    rw [(c n).support_normed_eq]
    intro x hx
    have hxabs : |x| < (c n).rOut := by
      simpa [Metric.mem_ball, Real.dist_eq] using hx
    have hxabs' : -(c n).rOut < x ∧ x < (c n).rOut := abs_lt.mp hxabs
    have hxlt : x < 2 := lt_of_lt_of_le hxabs'.2 (hc_out n)
    have hxgt : -2 < x := (neg_le_neg (hc_out n)).trans_lt hxabs'.1
    exact ⟨hxgt.le, hxlt.le⟩
  have hη_contdiff : ∀ n, ContDiff ℝ ∞ (η n) := by
    intro n
    simpa [η] using (c n).contDiff_normed
  have hη_nonneg : ∀ n x, 0 ≤ η n x := by
    intro n x
    simpa [η] using (c n).nonneg_normed x
  have hη_even : ∀ n x, η n (-x) = η n x := by
    intro n x
    simpa [η] using (c n).normed_neg x
  have hη_integral : ∀ n, ∫ x : ℝ, η n x = 1 := by
    intro n
    simpa [η] using (c n).integral_normed
  have hη_converges : ∀ φ : ℝ → ℝ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun n => ∫ x : ℝ, η n x * φ x) atTop (𝓝 (φ 0)) := by
    intro φ hφ hφcompact
    have hconv := ContDiffBump.convolution_tendsto_right_of_continuous
      (φ := c) (g := φ) (μ := (volume : Measure ℝ)) (l := atTop)
        hc_out_tendsto hφ 0
    apply hconv.congr'
    filter_upwards [] with n
    simp [MeasureTheory.convolution_eq_swap, η]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [(c n).normed_neg x]
  exact ⟨η, ⟨hη_integrable, hη_compact, hη_support, hη_contdiff,
    hη_nonneg, hη_even, hη_integral, hη_converges⟩⟩

theorem chapter06_origin_correction_factor_apply_zero
    (η : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (n : ℕ)
    (h : chapter06SmoothedConvolution η F n 0 ≠ 0) :
    chapter06SmoothedTestFunction η F n 0 = 1 := by
  simp [chapter06SmoothedTestFunction, chapter06OriginCorrectionFactor, h]

theorem chapter06_smoothed_origin_eventually_nonzero
    {η : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hη : chapter06ApproximateIdentity η)
    (hF : Chapter06BasicallyAdmissible F) :
    ∀ᶠ n : ℕ in atTop,
      chapter06SmoothedConvolution η F n 0 ≠ 0 := by
  rcases hη with ⟨hηint, hηcompact, hηsupport, hηdiff, hηnonneg,
    hηeven, hηnorm, hηconv⟩
  have hconv : Tendsto (fun n => ∫ x : ℝ, η n x * F x) atTop (𝓝 (F 0)) :=
    hηconv F hF.continuous hF.compactSupport
  have hconv' : Tendsto (fun n => ∫ x : ℝ, η n x * F x) atTop (𝓝 1) := by
    simpa [hF.valueAtZero] using hconv
  have heq : ∀ n, chapter06SmoothedConvolution η F n 0 =
      ∫ x : ℝ, η n x * F x := by
    intro n
    simp [chapter06SmoothedConvolution, chapter05Convolution,
      MeasureTheory.convolution_def]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [hF.even x]
  have hsmoothed : Tendsto
      (fun n => chapter06SmoothedConvolution η F n 0) atTop (𝓝 1) := by
    simpa only [heq] using hconv'
  filter_upwards [hsmoothed.eventually
      (Ioi_mem_nhds (show (1 : ℝ) ∈ Ioi (0 : ℝ) by norm_num))] with n hn
  exact ne_of_gt hn

theorem chapter06_origin_correction_factor_tendsto_one
    {η : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hη : chapter06ApproximateIdentity η)
    (hF : Chapter06BasicallyAdmissible F) :
    Tendsto (fun n => chapter06OriginCorrectionFactor η F n) atTop (𝓝 1) := by
  have hne := chapter06_smoothed_origin_eventually_nonzero hη hF
  have hconv : Tendsto
      (fun n => chapter06SmoothedConvolution η F n 0) atTop (𝓝 1) := by
    rcases hη with ⟨_, _, _, _, _, _, _, hηconv⟩
    have hconv' := hηconv F hF.continuous hF.compactSupport
    have hconv'' : Tendsto (fun n => ∫ x : ℝ, η n x * F x) atTop (𝓝 1) := by
      simpa [hF.valueAtZero] using hconv'
    have heq : ∀ n, chapter06SmoothedConvolution η F n 0 =
        ∫ x : ℝ, η n x * F x := by
      intro n
      simp [chapter06SmoothedConvolution, chapter05Convolution,
        MeasureTheory.convolution_def]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hF.even x]
    simpa only [heq] using hconv''
  have hinv : Tendsto
      (fun n => (chapter06SmoothedConvolution η F n 0)⁻¹) atTop (𝓝 1) := by
    simpa using hconv.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  apply hinv.congr'
  filter_upwards [hne] with n hn
  simp [chapter06OriginCorrectionFactor, hn]

private theorem chapter06_smooth_compact_basic_of_value_at_zero
    {G : ℝ → ℝ} (hG : Chapter06SmoothCompactSupport G) (hG0 : G 0 = 1) :
    Chapter06BasicallyAdmissible G := by
  rcases hG with ⟨hGeven, hGdiff, hGcompact⟩
  have hGderivDiff : Differentiable ℝ (deriv G) := by
    exact (contDiff_infty_iff_deriv.mp hGdiff).2.differentiable (by simp)
  have hGderivDerivCont : Continuous (deriv (deriv G)) := by
    have hGderivDeriv : ContDiff ℝ ∞ (deriv (deriv G)) := by
      exact (contDiff_infty_iff_deriv.mp
        (contDiff_infty_iff_deriv.mp hGdiff).2).2
    exact hGderivDeriv.continuous
  have hGderivDerivCompact : HasCompactSupport (deriv (deriv G)) :=
    hGcompact.deriv.deriv
  obtain ⟨C, hC⟩ := hGderivDerivCompact.exists_bound_of_continuous
    hGderivDerivCont
  let C' : NNReal := ⟨max C (0 : ℝ), le_max_right _ _⟩
  have hC' : ∀ x : ℝ, ‖deriv (deriv G) x‖₊ ≤ C' := by
    intro x
    change ‖deriv (deriv G) x‖ ≤ max C (0 : ℝ)
    exact (hC x).trans (le_max_left _ _)
  have hGderivLipschitz : LipschitzWith C' (deriv G) :=
    lipschitzWith_of_nnnorm_deriv_le hGderivDiff hC'
  have hGderivCompact : HasCompactSupport (deriv G) := hGcompact.deriv
  obtain ⟨R₀, hR₀pos, hR₀⟩ :=
    hGderivCompact.isBounded.subset_closedBall_lt (0 : ℝ) (0 : ℝ)
  let R : ℝ := R₀ + 1
  have hRpos : 0 < R := by
    dsimp [R]
    linarith
  have hGderiv_zero_left : ∀ x : ℝ, x ∈ Iic (-R) → deriv G x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hxt
    have hxball := hR₀ hxt
    have hxabs : |x| ≤ R₀ := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hxball
    have hxabs' : R ≤ |x| := by
      change x ≤ -R at hx
      rw [abs_of_nonpos (by linarith)]
      linarith
    linarith [hR₀pos]
  have hGderiv_zero_right : ∀ x : ℝ, x ∈ Ici R → deriv G x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hxt
    have hxball := hR₀ hxt
    have hxabs : |x| ≤ R₀ := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hxball
    have hxabs' : R ≤ |x| := by
      change R ≤ x at hx
      rw [abs_of_nonneg (by linarith)]
      exact hx
    linarith [hR₀pos]
  have hleft : eVariationOn (deriv G) (Iic (-R)) = 0 := by
    apply eVariationOn.constant_on
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hGderiv_zero_left x hx, hGderiv_zero_left y hy]
  have hright : eVariationOn (deriv G) (Ici R) = 0 := by
    apply eVariationOn.constant_on
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hGderiv_zero_right x hx, hGderiv_zero_right y hy]
  have hmid : BoundedVariationOn (deriv G) (Icc (-R) R) := by
    have hle : eVariationOn (deriv G) (Icc (-R) R) ≤
        C' * eVariationOn id (Icc (-R) R) := by
      exact hGderivLipschitz.lipschitzOnWith.comp_eVariationOn_le
        (mapsTo_id _) 
    have hlt : eVariationOn (deriv G) (Icc (-R) R) < (⊤ : ENNReal) := by
      apply lt_of_le_of_lt hle
      rw [eVariationOn_id_Icc]
      exact ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top
    exact hlt.ne
  have hleft_mid_set : Iic (-R) ∪ Icc (-R) R = Iic R := by
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · change x ≤ -R at hx
        exact le_trans hx (by linarith [hRpos.le])
      · exact hx.2
    · intro hx
      by_cases h : x ≤ -R
      · exact Or.inl h
      · exact Or.inr ⟨le_of_not_ge h, hx⟩
  have hmid_right_set : Iic R ∪ Ici R = (Set.univ : Set ℝ) := by
    ext x
    simp only [mem_union, mem_Iic, mem_Ici, mem_univ]
    constructor
    · intro _
      trivial
    · intro _
      exact le_total x R
  have hleft_mid : eVariationOn (deriv G) (Iic R) =
      eVariationOn (deriv G) (Icc (-R) R) := by
    calc
      eVariationOn (deriv G) (Iic R) =
          eVariationOn (deriv G) (Iic (-R) ∪ Icc (-R) R) := by
            rw [hleft_mid_set]
      _ =
          eVariationOn (deriv G) (Iic (-R)) +
            edist (deriv G (-R)) (deriv G (-R)) +
              eVariationOn (deriv G) (Icc (-R) R) :=
        eVariationOn.union' (deriv G) (s := Iic (-R))
          (t := Icc (-R) R) (x := -R) (y := -R)
          ⟨by simp, fun x hx => hx⟩
          ⟨⟨by rfl, by linarith [hRpos.le]⟩, fun x hx => hx.1⟩ le_rfl
      _ = eVariationOn (deriv G) (Icc (-R) R) := by simp [hleft]
  have htotal : BoundedVariationOn (deriv G) (Set.univ : Set ℝ) := by
    change eVariationOn (deriv G) (Set.univ : Set ℝ) ≠ (⊤ : ENNReal)
    calc
      eVariationOn (deriv G) (Set.univ : Set ℝ) =
          eVariationOn (deriv G) (Iic R ∪ Ici R) := by
            rw [hmid_right_set]
      _ =
          eVariationOn (deriv G) (Iic R) +
            edist (deriv G R) (deriv G R) +
              eVariationOn (deriv G) (Ici R) :=
        eVariationOn.union' (deriv G) (s := Iic R) (t := Ici R)
          (x := R) (y := R)
          ⟨by simp, fun x hx => hx⟩
          ⟨by simp, fun x hx => hx⟩ le_rfl
      _ = eVariationOn (deriv G) (Icc (-R) R) := by
        simp [hright, hleft_mid]
      _ ≠ (⊤ : ENNReal) := hmid
  refine
    { even := hGeven
      continuous := hGdiff.continuous
      compactSupport := hGcompact
      piecewiseC2 := ?_
      valueAtZero := hG0
      oneSidedDerivativeBV := ?_
      originCondition := ?_ }
  · refine ⟨∅, Set.finite_empty, ?_⟩
    intro x hx
    exact hGdiff.contDiffAt.of_le
      (show (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by
        apply WithTop.coe_le_coe.mpr
        exact le_top)
  · refine ⟨deriv G, deriv G, ?_, ?_, htotal, htotal⟩
    · intro x
      exact ((hGdiff.differentiable (by simp) x).hasDerivAt).hasDerivWithinAt
    · intro x
      exact ((hGdiff.differentiable (by simp) x).hasDerivAt).hasDerivWithinAt
  · exact chapter05_right_corner_origin_condition hG0 hGdiff.continuous
      ((hGdiff.differentiable (by simp) 0).hasDerivAt).hasDerivWithinAt

private theorem chapter06_smoothed_test_function_smooth_compact
    {η : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hη : chapter06ApproximateIdentity η)
    (hF : Chapter06BasicallyAdmissible F) (n : ℕ) :
    Chapter06SmoothCompactSupport
      (chapter06SmoothedTestFunction η F n) := by
  rcases hη with ⟨hηint, hηcompact, hηsupport, hηdiff, hηnonneg,
    hηeven, hηnorm, hηconv⟩
  have hconv_smooth : ContDiff ℝ ∞
      (chapter06SmoothedConvolution η F n) := by
    unfold chapter06SmoothedConvolution chapter05Convolution
    have hflip :
        MeasureTheory.convolution (η n) F
            (ContinuousLinearMap.lsmul ℝ ℝ) volume =
          MeasureTheory.convolution F (η n)
            (ContinuousLinearMap.lsmul ℝ ℝ).flip volume := by
      simpa only [ContinuousLinearMap.flip_flip] using
        (MeasureTheory.convolution_flip
          (L := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
          (f := F) (g := η n) (μ := (volume : Measure ℝ)))
    rw [hflip]
    exact (hηcompact n).contDiff_convolution_right
      ((ContinuousLinearMap.lsmul ℝ ℝ).flip)
      hF.continuous.locallyIntegrable (hηdiff n)
  have hconv_compact : HasCompactSupport
      (chapter06SmoothedConvolution η F n) := by
    unfold chapter06SmoothedConvolution chapter05Convolution
    exact (hηcompact n).convolution
      (ContinuousLinearMap.lsmul ℝ ℝ) hF.compactSupport
  have hconv_even : Function.Even
      (chapter06SmoothedConvolution η F n) := by
    intro x
    unfold chapter06SmoothedConvolution chapter05Convolution
    exact MeasureTheory.convolution_neg_of_neg_eq
      (ContinuousLinearMap.lsmul ℝ ℝ)
      (Eventually.of_forall (hηeven n))
      (Eventually.of_forall hF.even)
  have htest_diff : ContDiff ℝ ∞
      (chapter06SmoothedTestFunction η F n) := by
    have hscalar : ContDiff ℝ ∞ (fun _ : ℝ =>
        chapter06OriginCorrectionFactor η F n) := contDiff_const
    change ContDiff ℝ ∞ (fun x : ℝ =>
      chapter06OriginCorrectionFactor η F n *
        chapter06SmoothedConvolution η F n x)
    exact hscalar.mul hconv_smooth
  have htest_compact : HasCompactSupport
      (chapter06SmoothedTestFunction η F n) := by
    change HasCompactSupport
      ((fun _ : ℝ => chapter06OriginCorrectionFactor η F n) *
        chapter06SmoothedConvolution η F n)
    exact hconv_compact.mul_left
  have htest_even : Function.Even
      (chapter06SmoothedTestFunction η F n) := by
    intro x
    simp [chapter06SmoothedTestFunction, hconv_even x]
  exact ⟨htest_even, htest_diff, htest_compact⟩

theorem chapter06_smoothed_test_functions_basic_admissible
    {η : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hη : chapter06ApproximateIdentity η)
    (hF : Chapter06BasicallyAdmissible F) :
    ∀ᶠ n : ℕ in atTop, Chapter06BasicallyAdmissible
      (chapter06SmoothedTestFunction η F n) := by
  filter_upwards [chapter06_smoothed_origin_eventually_nonzero hη hF] with n hn
  apply chapter06_smooth_compact_basic_of_value_at_zero
  · exact chapter06_smoothed_test_function_smooth_compact hη hF n
  · exact chapter06_origin_correction_factor_apply_zero η F n hn

theorem chapter06_smoothed_test_functions_smooth_compact
    {η : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hη : chapter06ApproximateIdentity η)
    (hF : Chapter06BasicallyAdmissible F) :
    ∀ n, Chapter06SmoothCompactSupport
      (chapter06SmoothedTestFunction η F n) := by
  intro n
  exact chapter06_smoothed_test_function_smooth_compact hη hF n

theorem chapter06_smoothed_test_functions_decay_uniformly
    {η : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hη : chapter06ApproximateIdentity η)
    (hF : Chapter06BasicallyAdmissible F) :
    ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ σ t : ℝ,
      |σ| ≤ R →
        ‖chapter06Phi (chapter06SmoothedTestFunction η F n)
            ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C / (1 + |t|) ^ 2 := by
  sorry

theorem chapter06_smoothed_zero_sum_dominated_convergence
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) {η : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hη : chapter06ApproximateIdentity η)
    (hF : Chapter06BasicallyAdmissible F) :
    Tendsto (fun n => chapter06SymmetricZeroSum Z
      (chapter06SmoothedTestFunction η F n)) atTop
      (𝓝 (chapter06SymmetricZeroSum Z F)) := by
  sorry

theorem chapter06_smoothed_prime_sum_dominated_convergence
    (K : Type*) [Field K] [NumberField K]
    {η : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hη : chapter06ApproximateIdentity η)
    (hF : Chapter06BasicallyAdmissible F) :
    Tendsto (fun n => chapter06PrimeContribution K
      (chapter06SmoothedTestFunction η F n)) atTop
      (𝓝 (chapter06PrimeContribution K F)) := by
  sorry

theorem chapter06_smoothed_archimedean_terms_converge
    {η : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hη : chapter06ApproximateIdentity η)
    (hF : Chapter06BasicallyAdmissible F) :
    Tendsto (fun n => chapter06A (chapter06SmoothedTestFunction η F n)) atTop
        (𝓝 (chapter06A F)) ∧
      Tendsto (fun n => chapter06B (chapter06SmoothedTestFunction η F n)) atTop
        (𝓝 (chapter06B F)) ∧
      Tendsto (fun n => chapter06C (chapter06SmoothedTestFunction η F n)) atTop
        (𝓝 (chapter06C F)) := by
  sorry

theorem chapter06_universal_expression_eq_formula_without_sums
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) (F : ℝ → ℝ) :
    chapter06ExplicitFormulaRightHandSide K Z F -
        chapter06ZeroContribution Z F - chapter06PrimeContribution K F =
      chapter06UniversalLowerBoundExpression K F := by
  simp [chapter06ExplicitFormulaRightHandSide,
    chapter06UniversalLowerBoundExpression]; ring

theorem chapter06_universal_expression_congr_of_ae
    (K : Type*) [Field K] [NumberField K] {F G : ℝ → ℝ}
    (hF : Chapter06BasicallyAdmissible F)
    (hG : Chapter06BasicallyAdmissible G)
    (hFG : F =ᵐ[volume] G) :
    chapter06UniversalLowerBoundExpression K F =
      chapter06UniversalLowerBoundExpression K G := by
  let _ := hF
  let _ := hG
  have hA : chapter06A F = chapter06A G := by
    unfold chapter06A
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hFG] with x hx
    rw [hx]
  have hB : chapter06B F = chapter06B G := by
    unfold chapter06B
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hFG] with x hx
    rw [hx]
  have hC : chapter06C F = chapter06C G := by
    unfold chapter06C
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hFG] with x hx
    rw [hx]
  unfold chapter06UniversalLowerBoundExpression
  rw [hA, hB, hC]

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06
