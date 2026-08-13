import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter13.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter13

noncomputable section

universe u

/-!
## 13.1 The abstract comparison theorem

The positive integer hypothesis on `N` is retained here.  It is needed for
the term `4 A(F) / N` and the degree-threshold comparison.
-/

/- The source explicitly takes `N` to be positive; that hypothesis is retained
here because it is needed for the degree-threshold comparison. -/

theorem chapter13_abstract_comparison_theorem
    (U α₀ : ℝ) (N : ℕ)
    (hU : 0 < U) (hα₀ : 0 ≤ α₀) (hα₀' : α₀ ≤ 1) (hN : 0 < N)
    (F : ℝ → ℝ)
    (hC : chapter13C F ≤ Real.pi / 2)
    (hmargin :
      Real.eulerMascheroniConstant + Real.log (8 * Real.pi) + α₀ * (Real.pi / 2) -
          4 * chapter13A F / (N : ℝ) - chapter13B F - α₀ * chapter13C F > Real.log U)
    (hanalytic : ∀ (K : Type u) [Field K] [NumberField K],
      chapter13FieldwiseAnalyticBound F K) :
    ∀ (K : Type u) [Field K] [NumberField K],
      chapter13RootDiscriminant K ≤ U →
      α₀ ≤ chapter13RealProportion K →
      chapter13Degree K < N := by
  sorry

/-- A named form of the source's Theorem 13.1 conclusion for one field. -/
theorem chapter13_degree_lt_of_discriminant_ceiling
    (U α₀ : ℝ) (N : ℕ)
    (hU : 0 < U) (hα₀ : 0 ≤ α₀) (hα₀' : α₀ ≤ 1) (hN : 0 < N)
    (F : ℝ → ℝ)
    (hC : chapter13C F ≤ Real.pi / 2)
    (hmargin : chapter13LogLowerBound F N α₀ > Real.log U)
    {K : Type u} [Field K] [NumberField K]
    (hanalytic : chapter13FieldwiseAnalyticBound F K)
    (hceil : chapter13RootDiscriminant K ≤ U)
    (hα : α₀ ≤ chapter13RealProportion K) :
    chapter13Degree K < N := by
  sorry

/-! A strict arithmetic ceiling permits equality in the analytic lower bound. -/
theorem chapter13_strict_ceiling_accepts_equal_log_bound
    (K : Type*) [Field K] [NumberField K] {U : ℝ}
    (hU : 0 < U) (hceil : chapter13RootDiscriminant K < U)
    (hlower : Real.log U ≤ Real.log (chapter13RootDiscriminant K)) : False := by
  sorry

/-! The weak-ceiling version must retain a strict logarithmic margin. -/
theorem chapter13_weak_ceiling_contradiction
    (K : Type*) [Field K] [NumberField K] {U L : ℝ}
    (hU : 0 < U) (hceil : chapter13RootDiscriminant K ≤ U)
    (hlower : L ≤ Real.log (chapter13RootDiscriminant K))
    (hmargin : Real.log U < L) : False := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter13
