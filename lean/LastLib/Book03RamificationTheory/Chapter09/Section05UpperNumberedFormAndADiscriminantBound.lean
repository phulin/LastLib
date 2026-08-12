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
  sorry

def chapter09UpperGroupTrivialAfter
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (R : ℝ) : Prop :=
  ∀ v : ℝ, R < v → chapter09UpperGroup D v = ⊥

theorem chapter09_upper_reciprocal_integrand_eq_zero_after_last_break
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (R : ℝ)
    (hR : chapter09UpperGroupTrivialAfter D R) {v : ℝ} (hv : R < v) :
    chapter09UpperReciprocalIntegrand D v = 0 := by
  sorry

theorem chapter09_different_upper_bound_from_last_break
    {G : Type*} [Group G] [Finite G] [Fintype G]
    (D : Chapter05RamificationFiltration G) (d e : ℕ) (R : ℝ)
    (he : e = chapter09RamificationIndex D)
    (hformula : d = chapter09GroupCountSum D)
    (hbij : Function.Bijective (chapter05HerbrandFunction D))
    (hR_nonneg : 0 ≤ R)
    (hR : chapter09UpperGroupTrivialAfter D R) :
    (d : ℝ) ≤ (e - 1 : ℕ) + (e : ℝ) * R := by
  sorry

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
  sorry

theorem chapter09_normalized_discriminant_ratio
    (e f d : ℕ) (he : 0 < e) (hf : 0 < f) :
    (chapter09DiscriminantExponent f d : ℚ) /
        ((e * f : ℕ) : ℚ) =
      (d : ℚ) / (e : ℚ) := by
  sorry

theorem chapter09_normalized_upper_integral_identity
    {G : Type*} [Group G] [Finite G] [Fintype G]
    (D : Chapter05RamificationFiltration G) (d e : ℕ)
    (he : e = chapter09RamificationIndex D)
    (hformula : d = chapter09GroupCountSum D)
    (hbij : Function.Bijective (chapter05HerbrandFunction D)) :
    (d : ℝ) / (e : ℝ) =
      1 - (e : ℝ)⁻¹ + chapter09UpperReciprocalIntegral D := by
  sorry

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
