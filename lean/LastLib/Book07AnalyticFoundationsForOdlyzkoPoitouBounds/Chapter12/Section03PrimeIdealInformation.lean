import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter12.Section01IntermediateSignatures

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter12

open Set
open scoped BigOperators

noncomputable section

/-! ## 12.3. Prime-ideal information -/

/- LOCAL_DEPENDENCY_GUESS: the preceding number-field chapters will provide
the canonical finite set of prime ideals above q and identify its residue
degrees.  The present profile is the weakest interface needed by (12.2).

This is the book-facing finite profile of the primes above a rational prime.
The canonical prime-ideal enumeration and residue-degree theorem belong to
the preceding number-field development; the retained contribution below
needs only the resulting finite list of residue degrees.
-/
structure Chapter12PrimeIdealProfile where
  q : ℕ
  q_prime : Nat.Prime q
  g : ℕ
  g_pos : 0 < g
  residueDegrees : Fin g → ℕ
  residueDegrees_pos : ∀ j, 0 < residueDegrees j

def chapter12PrimeIdealTerm
    (q f m : ℕ) (F : ℝ → ℝ) : ℝ :=
  let m₁ := m + 1
  ((f : ℝ) * Real.log (q : ℝ)) /
      Real.rpow (q : ℝ) (((m₁ * f : ℕ) : ℝ) / 2) *
    F (((m₁ * f : ℕ) : ℝ) * Real.log (q : ℝ))

def chapter12SupportedTestFunction
    (support : Set ℝ) (F : ℝ → ℝ) : ℝ → ℝ :=
  Set.indicator support F

def chapter12PrimeIdealTermOnSupport
    (q f m : ℕ) (support : Set ℝ) (F : ℝ → ℝ) : ℝ :=
  chapter12PrimeIdealTerm q f m
    (chapter12SupportedTestFunction support F)

def chapter12PrimeIdealContribution
    (n : ℕ) (P : Chapter12PrimeIdealProfile) (F : ℝ → ℝ) : ℝ :=
  (2 / (n : ℝ)) *
    ∑ j : Fin P.g, ∑' m : ℕ,
      chapter12PrimeIdealTerm P.q (P.residueDegrees j) m F

def chapter12PrimeIdealContributionOnSupport
    (n : ℕ) (P : Chapter12PrimeIdealProfile)
    (support : Set ℝ) (F : ℝ → ℝ) : ℝ :=
  (2 / (n : ℝ)) *
    ∑ j : Fin P.g, ∑' m : ℕ,
      chapter12PrimeIdealTermOnSupport P.q (P.residueDegrees j) m support F

theorem chapter12_prime_ideal_contribution_formula
    (n : ℕ) (P : Chapter12PrimeIdealProfile) (F : ℝ → ℝ) :
    chapter12PrimeIdealContribution n P F =
      (2 / (n : ℝ)) *
        ∑ j : Fin P.g, ∑' m : ℕ,
          (((P.residueDegrees j : ℝ) * Real.log (P.q : ℝ)) /
              Real.rpow (P.q : ℝ)
                ((((m + 1) * P.residueDegrees j : ℕ) : ℝ) / 2)) *
            F ((((m + 1) * P.residueDegrees j : ℕ) : ℝ) *
              Real.log (P.q : ℝ)) := by
  rfl

theorem chapter12_prime_ideal_term_on_support_vanishes_outside
    {q f m : ℕ} {support : Set ℝ} {F : ℝ → ℝ}
    (h : (((m + 1) * f : ℕ) : ℝ) * Real.log (q : ℝ) ∉ support) :
    chapter12PrimeIdealTermOnSupport q f m support F = 0 := by
  simp only [chapter12PrimeIdealTermOnSupport, chapter12PrimeIdealTerm,
    chapter12SupportedTestFunction]
  rw [Set.indicator_of_notMem h]
  simp

theorem chapter12_supported_contribution_eq_unrestricted
    (n : ℕ) (P : Chapter12PrimeIdealProfile)
    (support : Set ℝ) (F : ℝ → ℝ)
    (hF : ∀ x ∉ support, F x = 0) :
    chapter12PrimeIdealContributionOnSupport n P support F =
      chapter12PrimeIdealContribution n P F := by
  sorry

theorem chapter12_prime_ideal_contribution_nonneg
    {n : ℕ} (hn : 0 < n) (P : Chapter12PrimeIdealProfile)
    {F : ℝ → ℝ} (hF : ∀ x, 0 ≤ F x) :
    0 ≤ chapter12PrimeIdealContribution n P F := by
  sorry

theorem chapter12_supported_prime_ideal_contribution_nonneg
    {n : ℕ} (hn : 0 < n) (P : Chapter12PrimeIdealProfile)
    {support : Set ℝ} {F : ℝ → ℝ} (hF : ∀ x, 0 ≤ F x) :
    0 ≤ chapter12PrimeIdealContributionOnSupport n P support F := by
  sorry

def chapter12PrimeRefinedLogExpression
    (n : ℕ) (T α : ℝ) (P : Chapter12PrimeIdealProfile)
    (support : Set ℝ) (F : ℝ → ℝ) : ℝ :=
  chapter12AffineLogExpression n T α +
    chapter12PrimeIdealContributionOnSupport n P support F

theorem chapter12_prime_information_improves_log_bound
    {n : ℕ} (hn : 0 < n) {T α : ℝ} (P : Chapter12PrimeIdealProfile)
    {support : Set ℝ} {F : ℝ → ℝ} (hF : ∀ x, 0 ≤ F x) :
    chapter12AffineLogExpression n T α ≤
      chapter12PrimeRefinedLogExpression n T α P support F := by
  exact le_add_of_nonneg_right
    (chapter12_supported_prime_ideal_contribution_nonneg (n := n) hn P hF)

def chapter12PrimeIdealContributionWithRamification
    (n : ℕ) (P : Chapter12PrimeIdealProfile)
    (_ramificationIndices : Fin P.g → ℕ)
    (support : Set ℝ) (F : ℝ → ℝ) : ℝ :=
  chapter12PrimeIdealContributionOnSupport n P support F

theorem chapter12_ramification_indices_do_not_multiply_prime_count
    (n : ℕ) (P : Chapter12PrimeIdealProfile)
    (e₁ e₂ : Fin P.g → ℕ) (support : Set ℝ) (F : ℝ → ℝ) :
    chapter12PrimeIdealContributionWithRamification n P e₁ support F =
      chapter12PrimeIdealContributionWithRamification n P e₂ support F := by
  rfl

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter12
