import LastLib.Book03RamificationTheory.Chapter09.Section04ATowerCheck

namespace LastLib.Book03RamificationTheory.Chapter09

noncomputable section

open LastLib.Book03RamificationTheory.Chapter05
open MeasureTheory
open scoped BigOperators

/-! ## 9.5. Upper-numbered form and a discriminant bound -/

def chapter09UpperDifferentIntegrand
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) : ℝ → ℝ :=
  fun v => (Nat.card (chapter09UpperGroup D v) : ℝ) - 1

def chapter09UpperDifferentIntegral
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) : ℝ :=
  ∫ v in Set.Ici (0 : ℝ), chapter09UpperDifferentIntegrand D v

def chapter09UpperReciprocalIntegrand
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) : ℝ → ℝ :=
  fun v => 1 - (Nat.card (chapter09UpperGroup D v) : ℝ)⁻¹

def chapter09UpperReciprocalIntegral
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) : ℝ :=
  ∫ v in Set.Ici (0 : ℝ), chapter09UpperReciprocalIntegrand D v

theorem chapter09_different_eq_tame_plus_upper_integral
    {G : Type*} [Group G] [Finite G] [Fintype G]
    (D : Chapter05RamificationFiltration G) (d : ℕ)
    (hformula : d = chapter09GroupCountSum D)
    (hbij : Function.Bijective (chapter05HerbrandFunction D)) :
    (d : ℝ) = (chapter09TameBaseline D : ℝ) +
      chapter09UpperDifferentIntegral D := by
  sorry

theorem chapter09_different_eq_upper_reciprocal_integral
    {G : Type*} [Group G] [Finite G] [Fintype G]
    (D : Chapter05RamificationFiltration G) (d : ℕ)
    (hformula : d = chapter09GroupCountSum D)
    (hbij : Function.Bijective (chapter05HerbrandFunction D)) :
    (d : ℝ) = (chapter09TameBaseline D : ℝ) +
      (chapter09RamificationIndex D : ℝ) *
        chapter09UpperReciprocalIntegral D := by
  sorry

theorem chapter09_upper_integral_change_of_variables
    {G : Type*} [Group G] [Finite G] [Fintype G]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D)) :
    chapter09UpperDifferentIntegral D =
      (chapter09RamificationIndex D : ℝ) *
        chapter09UpperReciprocalIntegral D := by
  linarith [chapter09_different_eq_tame_plus_upper_integral D
      (chapter09GroupCountSum D) rfl hbij,
    chapter09_different_eq_upper_reciprocal_integral D
      (chapter09GroupCountSum D) rfl hbij]

def chapter09UpperGroupTrivialAfter
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (R : ℝ) : Prop :=
  ∀ v : ℝ, R < v → chapter09UpperGroup D v = ⊥

theorem chapter09_upper_reciprocal_integrand_eq_zero_after_last_break
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (R : ℝ)
    (hR : chapter09UpperGroupTrivialAfter D R) {v : ℝ} (hv : R < v) :
    chapter09UpperReciprocalIntegrand D v = 0 := by
  rw [chapter09UpperReciprocalIntegrand, hR v hv]
  simp

theorem chapter09_different_upper_bound_from_last_break
    {G : Type*} [Group G] [Finite G] [Fintype G]
    (D : Chapter05RamificationFiltration G) (d e : ℕ) (R : ℝ)
    (he : e = chapter09RamificationIndex D)
    (hformula : d = chapter09GroupCountSum D)
    (hbij : Function.Bijective (chapter05HerbrandFunction D))
    (hR_nonneg : 0 ≤ R)
    (hR : chapter09UpperGroupTrivialAfter D R) :
    (d : ℝ) ≤ (e - 1 : ℕ) + (e : ℝ) * R := by
  let f : ℝ → ℝ := chapter09UpperReciprocalIntegrand D
  have hle_one (v : ℝ) : f v ≤ 1 := by
    have hcard_pos : 0 < (Nat.card (chapter09UpperGroup D v) : ℝ) := by
      exact_mod_cast Nat.card_pos
    have hinv_nonneg :
        0 ≤ (Nat.card (chapter09UpperGroup D v) : ℝ)⁻¹ :=
      inv_nonneg.mpr hcard_pos.le
    change 1 - (Nat.card (chapter09UpperGroup D v) : ℝ)⁻¹ ≤ 1
    exact sub_le_self 1 hinv_nonneg
  have hintegral :
      chapter09UpperReciprocalIntegral D ≤ R := by
    by_cases hI : Integrable f (volume.restrict (Set.Ici (0 : ℝ)))
    · have htail :
          (∫ v in Set.Ici R, f v) = 0 := by
        rw [integral_Ici_eq_integral_Ioi]
        apply integral_eq_zero_of_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
        rw [show f v = 0 by
          dsimp [f]
          exact chapter09_upper_reciprocal_integrand_eq_zero_after_last_break
            D R hR hv]
        simp
      have hsplit := intervalIntegral.integral_Ici_sub_Ici
        (f := f) hI hR_nonneg
      have hmain :
          (∫ v in Set.Ici (0 : ℝ), f v) = ∫ v in Set.Ico 0 R, f v := by
        linarith [hsplit, htail]
      have hmono :
          (∫ v in Set.Ico 0 R, f v) ≤
            ∫ v in Set.Ico 0 R, (1 : ℝ) := by
        apply setIntegral_mono_on
          (IntegrableOn.mono hI Set.Ico_subset_Ici_self le_rfl)
          (integrableOn_const measure_Ico_lt_top.ne)
          measurableSet_Ico
        intro v hv
        exact hle_one v
      change (∫ v in Set.Ici (0 : ℝ), f v) ≤ R
      calc
        (∫ v in Set.Ici (0 : ℝ), f v) = ∫ v in Set.Ico 0 R, f v := hmain
        (∫ v in Set.Ico 0 R, f v) ≤ ∫ v in Set.Ico 0 R, (1 : ℝ) := hmono
        (∫ v in Set.Ico 0 R, (1 : ℝ)) = R := by
          rw [setIntegral_const, smul_eq_mul,
            Real.volume_real_Ico_of_le hR_nonneg]
          simp
    · rw [chapter09UpperReciprocalIntegral]
      change (∫ v in Set.Ici (0 : ℝ), f v) ≤ R
      rw [integral_undef hI]
      exact hR_nonneg
  have he_pos : 0 < e := by
    rw [he]
    exact Nat.card_pos
  have he_one' : 1 ≤ e := Nat.succ_le_iff.mpr he_pos
  have he_one : 1 ≤ chapter09RamificationIndex D :=
    Nat.succ_le_iff.mpr Nat.card_pos
  have htame :
      (chapter09TameBaseline D : ℝ) = (e : ℝ) - 1 := by
    rw [chapter09TameBaseline, Nat.cast_sub he_one]
    norm_num
    rw [← he]
  have hmain := chapter09_different_eq_upper_reciprocal_integral
    D d hformula hbij
  rw [htame, ← he] at hmain
  have hscaled := mul_le_mul_of_nonneg_left hintegral
    (Nat.cast_nonneg e)
  calc
    (d : ℝ) = (e : ℝ) - 1 + (e : ℝ) *
        chapter09UpperReciprocalIntegral D := hmain
    (e : ℝ) - 1 + (e : ℝ) * chapter09UpperReciprocalIntegral D ≤
        (e : ℝ) - 1 + (e : ℝ) * R := by
      have h' := add_le_add_left hscaled ((e : ℝ) - 1)
      simpa [add_comm] using h'
    (e : ℝ) - 1 + (e : ℝ) * R = (e - 1 : ℕ) + (e : ℝ) * R := by
      rw [Nat.cast_sub he_one']
      norm_num

def chapter09DiscriminantExponent (f d : ℕ) : ℕ :=
  f * d

@[simp] theorem chapter09_discriminant_exponent_def (f d : ℕ) :
    chapter09DiscriminantExponent f d = f * d :=
  rfl

theorem chapter09_discriminant_exponent_bound_from_last_break
    {G : Type*} [Group G] [Finite G] [Fintype G]
    (D : Chapter05RamificationFiltration G)
    (d e f : ℕ) (R : ℝ)
    (he : e = chapter09RamificationIndex D)
    (hformula : d = chapter09GroupCountSum D)
    (hbij : Function.Bijective (chapter05HerbrandFunction D))
    (hR_nonneg : 0 ≤ R)
    (hR : chapter09UpperGroupTrivialAfter D R) :
    (chapter09DiscriminantExponent f d : ℝ) ≤
      (f : ℝ) * ((e - 1 : ℕ) + (e : ℝ) * R) := by
  have hbound : (d : ℝ) ≤ (e - 1 : ℕ) + (e : ℝ) * R :=
    chapter09_different_upper_bound_from_last_break D d e R he hformula hbij
      hR_nonneg hR
  have hf_nonneg : (0 : ℝ) ≤ (f : ℝ) := Nat.cast_nonneg f
  have hscaled := mul_le_mul_of_nonneg_left hbound hf_nonneg
  simpa [chapter09DiscriminantExponent, Nat.cast_mul] using hscaled

theorem chapter09_normalized_discriminant_ratio
    (e f d : ℕ) (he : 0 < e) (hf : 0 < f) :
    (chapter09DiscriminantExponent f d : ℚ) /
        ((e * f : ℕ) : ℚ) =
      (d : ℚ) / (e : ℚ) := by
  norm_num [chapter09DiscriminantExponent]; field_simp

theorem chapter09_normalized_upper_integral_identity
    {G : Type*} [Group G] [Finite G] [Fintype G]
    (D : Chapter05RamificationFiltration G) (d e : ℕ)
    (he : e = chapter09RamificationIndex D)
    (hformula : d = chapter09GroupCountSum D)
    (hbij : Function.Bijective (chapter05HerbrandFunction D)) :
    (d : ℝ) / (e : ℝ) =
      1 - (e : ℝ)⁻¹ + chapter09UpperReciprocalIntegral D := by
  have he_pos : 0 < e := by
    rw [he]
    exact Nat.card_pos
  have he_one : 1 ≤ chapter09RamificationIndex D :=
    Nat.succ_le_iff.mpr Nat.card_pos
  have htame :
      (chapter09TameBaseline D : ℝ) = (e : ℝ) - 1 := by
    rw [chapter09TameBaseline, Nat.cast_sub he_one]
    norm_num
    rw [← he]
  have hmain := chapter09_different_eq_upper_reciprocal_integral
    D d hformula hbij
  rw [htame, ← he] at hmain
  field_simp [ne_of_gt he_pos]
  nlinarith [hmain]

theorem chapter09_normalized_different_bound_from_last_break
    {G : Type*} [Group G] [Finite G] [Fintype G]
    (D : Chapter05RamificationFiltration G) (d e : ℕ) (R : ℝ)
    (he : e = chapter09RamificationIndex D)
    (hformula : d = chapter09GroupCountSum D)
    (hbij : Function.Bijective (chapter05HerbrandFunction D))
    (hR_nonneg : 0 ≤ R)
    (hR : chapter09UpperGroupTrivialAfter D R) :
    (d : ℝ) / (e : ℝ) ≤ 1 - (e : ℝ)⁻¹ + R ∧
      (d : ℝ) / (e : ℝ) < 1 + R := by
  sorry

structure Chapter09GlobalDiscriminantLedger where
  relativeDegree : ℕ
  discriminantExponent : ℕ
  branches : ℕ
  e : ℕ
  f : ℕ
  d : ℕ
  branches_pos : 0 < branches
  e_pos : 0 < e
  f_pos : 0 < f
  degree_eq : relativeDegree = branches * e * f
  discriminant_eq : discriminantExponent = branches * f * d

theorem chapter09_global_discriminant_ratio_is_local_ratio
    (C : Chapter09GlobalDiscriminantLedger) :
    (C.discriminantExponent : ℚ) / (C.relativeDegree : ℚ) =
      (C.d : ℚ) / (C.e : ℚ) := by
  sorry

end

end LastLib.Book03RamificationTheory.Chapter09
