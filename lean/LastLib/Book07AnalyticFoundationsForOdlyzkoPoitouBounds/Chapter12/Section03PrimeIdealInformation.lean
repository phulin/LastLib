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

theorem chapter12_prime_ideal_term_on_support_eventually_zero
    {q f : ℕ} (hq : 1 < q) (hf : 0 < f)
    {T : ℝ} (hT : 0 ≤ T) {support : Set ℝ} {F : ℝ → ℝ}
    (hsupport : support ⊆ Set.Icc (-T) T) :
    ∃ M : ℕ, ∀ m ≥ M,
      chapter12PrimeIdealTermOnSupport q f m support F = 0 := by
  have hqreal : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos hqreal
  have hcoef : 0 < (f : ℝ) * Real.log (q : ℝ) :=
    mul_pos (by positivity) hlog
  obtain ⟨M, hM⟩ := exists_nat_gt
    (max T 0 / ((f : ℝ) * Real.log (q : ℝ)))
  refine ⟨M, ?_⟩
  intro m hm
  have hMreal : (T / ((f : ℝ) * Real.log (q : ℝ))) < (M : ℝ) := by
    simpa [max_eq_left hT] using hM
  have hTprod : T < (M : ℝ) * ((f : ℝ) * Real.log (q : ℝ)) := by
    exact (div_lt_iff₀ hcoef).mp hMreal
  have hMm : (M : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.le_succ_of_le hm)
  have hmono : (M : ℝ) * ((f : ℝ) * Real.log (q : ℝ)) ≤
      ((m + 1 : ℕ) : ℝ) * ((f : ℝ) * Real.log (q : ℝ)) :=
    mul_le_mul_of_nonneg_right hMm hcoef.le
  have harg : T < (((m + 1) * f : ℕ) : ℝ) * Real.log (q : ℝ) := by
    have harg' : T < ((m + 1 : ℕ) : ℝ) *
        ((f : ℝ) * Real.log (q : ℝ)) := hTprod.trans_le hmono
    simpa [Nat.cast_add, Nat.cast_mul, mul_assoc] using harg'
  have hnot : (((m + 1) * f : ℕ) : ℝ) * Real.log (q : ℝ) ∉ support := by
    intro hx
    exact (not_lt_of_ge (hsupport hx).2) harg
  exact chapter12_prime_ideal_term_on_support_vanishes_outside hnot

theorem chapter12_supported_contribution_eq_unrestricted
    (n : ℕ) (P : Chapter12PrimeIdealProfile)
    (support : Set ℝ) (F : ℝ → ℝ)
    (hF : ∀ x ∉ support, F x = 0) :
    chapter12PrimeIdealContributionOnSupport n P support F =
      chapter12PrimeIdealContribution n P F := by
  have hfun : chapter12SupportedTestFunction support F = F := by
    funext x
    by_cases hx : x ∈ support
    · simp [chapter12SupportedTestFunction, hx]
    · simp [chapter12SupportedTestFunction, hx, hF x hx]
  simp [chapter12PrimeIdealContributionOnSupport, chapter12PrimeIdealContribution,
    chapter12PrimeIdealTermOnSupport, hfun]

theorem chapter12_prime_ideal_contribution_nonneg
    {n : ℕ} (hn : 0 < n) (P : Chapter12PrimeIdealProfile)
    {F : ℝ → ℝ} (hF : ∀ x, 0 ≤ F x) :
    0 ≤ chapter12PrimeIdealContribution n P F := by
  unfold chapter12PrimeIdealContribution
  have hscale : 0 ≤ (2 : ℝ) / (n : ℝ) := by positivity
  apply mul_nonneg hscale
  refine Finset.sum_nonneg fun j _ => ?_
  refine tsum_nonneg fun m => ?_
  dsimp [chapter12PrimeIdealTerm]
  have hqone : (1 : ℝ) ≤ (P.q : ℝ) := by
    exact_mod_cast P.q_prime.one_le
  have hlog : 0 ≤ Real.log (P.q : ℝ) := Real.log_nonneg hqone
  have hf : 0 ≤ (P.residueDegrees j : ℝ) := by
    exact_mod_cast (P.residueDegrees_pos j).le
  have hnum : 0 ≤ (P.residueDegrees j : ℝ) * Real.log (P.q : ℝ) :=
    mul_nonneg hf hlog
  have hden : 0 ≤ Real.rpow (P.q : ℝ)
      ((((m + 1) * P.residueDegrees j : ℕ) : ℝ) / 2) := by
    exact Real.rpow_nonneg (by
      exact_mod_cast P.q_prime.pos.le) _
  exact mul_nonneg (div_nonneg hnum hden) (hF _)

theorem chapter12_supported_prime_ideal_contribution_nonneg
    {n : ℕ} (hn : 0 < n) (P : Chapter12PrimeIdealProfile)
    {support : Set ℝ} {F : ℝ → ℝ} (hF : ∀ x, 0 ≤ F x) :
    0 ≤ chapter12PrimeIdealContributionOnSupport n P support F := by
  have hF' : ∀ x, 0 ≤ chapter12SupportedTestFunction support F x := by
    intro x
    by_cases hx : x ∈ support
    · simpa [chapter12SupportedTestFunction, hx] using hF x
    · simp [chapter12SupportedTestFunction, hx]
  change 0 ≤ chapter12PrimeIdealContribution n P
    (chapter12SupportedTestFunction support F)
  exact chapter12_prime_ideal_contribution_nonneg hn P hF'

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
