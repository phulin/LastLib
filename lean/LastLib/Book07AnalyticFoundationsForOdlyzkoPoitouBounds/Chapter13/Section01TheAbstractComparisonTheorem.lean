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
    (hanalytic : chapter13GlobalAnalyticBound.{u} F) :
    ∀ (K : Type u) [Field K] [NumberField K],
      chapter13RootDiscriminant K ≤ U →
      α₀ ≤ chapter13RealProportion K →
      chapter13Degree K < N := by
  by_cases hαneg : α₀ < 0
  · exact False.elim ((not_lt_of_ge hα₀) hαneg)
  by_cases hαgt : 1 < α₀
  · exact False.elim ((not_lt_of_ge hα₀') hαgt)
  have hA : 0 < chapter13A F := by
    have hAdmissible :
        chapter13UnconditionallyAdmissible F ∨ chapter13GRHAdmissible F := by
      rcases hanalytic with hF | ⟨hF, hGRH⟩
      · exact Or.inl hF.admissible
      · exact Or.inr hF.admissible
    exact chapter13A_pos_of_admissible F hAdmissible
  intro K _ _ hceil hα
  by_contra hnot
  have hNle : N ≤ chapter13Degree K := Nat.le_of_not_gt hnot
  have hmono := chapter13_logLowerBound_mono F hA hN hNle hC hα
  have hlogceil := chapter13_log_rootDiscriminant_le_of_ceiling K hU hceil
  have hloglower := chapter13_global_log_rootDiscriminant_lower_bound F hanalytic K
  have hmargin' : chapter13LogLowerBound F N α₀ > Real.log U := by
    simpa [chapter13LogLowerBound] using hmargin
  linarith [hmargin', hmono, hloglower, hlogceil]

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
  by_cases hαneg : α₀ < 0
  · exact False.elim ((not_lt_of_ge hα₀) hαneg)
  by_cases hαgt : 1 < α₀
  · exact False.elim ((not_lt_of_ge hα₀') hαgt)
  have hA : 0 < chapter13A F := by
    have hAdmissible :
        chapter13UnconditionallyAdmissible F ∨ chapter13GRHAdmissible F := by
      rcases hanalytic with hF | ⟨hF, hGRH⟩
      · exact Or.inl hF.admissible
      · exact Or.inr hF.admissible
    exact chapter13A_pos_of_admissible F hAdmissible
  by_contra hnot
  have hNle : N ≤ chapter13Degree K := Nat.le_of_not_gt hnot
  have hmono := chapter13_logLowerBound_mono F hA hN hNle hC hα
  have hlogceil := chapter13_log_rootDiscriminant_le_of_ceiling K hU hceil
  have hloglower := chapter13_log_rootDiscriminant_lower_bound F K hanalytic
  linarith [hmargin, hmono, hloglower, hlogceil]

/-! A strict arithmetic ceiling permits equality in the analytic lower bound. -/
theorem chapter13_strict_ceiling_accepts_equal_log_bound
    (K : Type*) [Field K] [NumberField K] {U : ℝ}
    (hU : 0 < U) (hceil : chapter13RootDiscriminant K < U)
    (hlower : Real.log U ≤ Real.log (chapter13RootDiscriminant K)) : False := by
  have hlog : Real.log (chapter13RootDiscriminant K) < Real.log U := by
    exact Real.strictMonoOn_log
      (show chapter13RootDiscriminant K ∈ Set.Ioi 0 from chapter13_rootDiscriminant_pos K)
      (show U ∈ Set.Ioi 0 from hU) hceil
  linarith

/-! The weak-ceiling version must retain a strict logarithmic margin. -/
theorem chapter13_weak_ceiling_contradiction
    (K : Type*) [Field K] [NumberField K] {U L : ℝ}
    (hU : 0 < U) (hceil : chapter13RootDiscriminant K ≤ U)
    (hlower : L ≤ Real.log (chapter13RootDiscriminant K))
    (hmargin : Real.log U < L) : False := by
  have hlogceil := chapter13_log_rootDiscriminant_le_of_ceiling K hU hceil
  linarith

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter13
