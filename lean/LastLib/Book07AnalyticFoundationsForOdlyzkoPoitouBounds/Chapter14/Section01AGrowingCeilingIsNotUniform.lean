import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter14.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter14

noncomputable section

/-! ## 14.1. A growing ceiling is not uniform -/

theorem chapter14_growing_ceiling_does_not_imply_uniform_ceiling
    {c ell : ℝ} (hc : 0 < c) (hell : 1 < ell) :
    ∃ a : ℕ → ℝ,
      (∀ m : ℕ, a m < c * ell ^ m) ∧
        ¬ ∃ U : ℝ, ∀ m : ℕ, a m ≤ U := by
  sorry

abbrev chapter14CyclotomicField (ell m : ℕ) : Type :=
  CyclotomicField (ell ^ m) ℚ

def chapter14CyclotomicDegree (ell m : ℕ) : ℕ :=
  Module.finrank ℚ (chapter14CyclotomicField ell m)

noncomputable def chapter14CyclotomicRootDiscriminant
    (ell m : ℕ) : ℝ :=
  NumberField.rootDiscr (chapter14CyclotomicField ell m)

theorem chapter14_cyclotomic_degree_formula
    {ell m : ℕ} (hell : Nat.Prime ell) (hm : 0 < m) :
    chapter14CyclotomicDegree ell m = ell ^ (m - 1) * (ell - 1) := by
  sorry

theorem chapter14_cyclotomic_rootDiscriminant_formula
    {ell m : ℕ} (hell : Nat.Prime ell) (hm : 0 < m) (hodd : 2 < ell) :
    chapter14CyclotomicRootDiscriminant ell m =
      Real.rpow (ell : ℝ)
        ((m : ℝ) - 1 / ((ell - 1 : ℕ) : ℝ)) := by
  sorry

theorem chapter14_cyclotomic_degree_strictMonoOn
    {ell : ℕ} (hell : Nat.Prime ell) :
    StrictMonoOn (fun m : ℕ => chapter14CyclotomicDegree ell m)
      (Set.Ioi (0 : ℕ)) := by
  sorry

theorem chapter14_cyclotomic_rootDiscriminant_strictMonoOn
    {ell : ℕ} (hell : Nat.Prime ell) (hodd : 2 < ell) :
    StrictMonoOn (fun m : ℕ => chapter14CyclotomicRootDiscriminant ell m)
      (Set.Ioi (0 : ℕ)) := by
  sorry

theorem chapter14_cyclotomic_rootDiscriminant_lt_power
    {ell m : ℕ} (hell : Nat.Prime ell) (hm : 0 < m) (hodd : 2 < ell) :
    chapter14CyclotomicRootDiscriminant ell m < (ell : ℝ) ^ m := by
  sorry

theorem chapter14_cyclotomic_rootDiscriminant_has_no_uniform_ceiling
    {ell : ℕ} (hell : Nat.Prime ell) (hodd : 2 < ell) :
    ¬ ∃ U : ℝ, ∀ m : ℕ, 0 < m →
      chapter14CyclotomicRootDiscriminant ell m ≤ U := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter14
