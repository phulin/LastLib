import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08.Section02TheTriangularAutocorrelation

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08

open MeasureTheory Set
open scoped BigOperators

noncomputable section

/-! ## 8.3 Exact evaluation of the archimedean terms -/

def chapter08BT (T : ℝ) : ℝ :=
  chapter08B (chapter08FUnconditionalTriangle T)

def chapter08CT (T : ℝ) : ℝ :=
  chapter08C (chapter08FUnconditionalTriangle T)

def chapter08Coth (x : ℝ) : ℝ :=
  Real.cosh x / Real.sinh x

def chapter08Odd (k : ℕ) : ℝ :=
  ((2 * k + 1 : ℕ) : ℝ)

def chapter08BSeriesTerm (T : ℝ) (k : ℕ) : ℝ :=
  ((1 + chapter08Odd k * T) * Real.exp (-chapter08Odd k * T)) /
    (chapter08Odd k) ^ 2

def chapter08BSeriesTail (T : ℝ) (m : ℕ) : ℝ :=
  ∑' k : ℕ, chapter08BSeriesTerm T (m + 1 + k)

theorem chapter08_B_series_coefficient_bound
    {T : ℝ} (hT : 0 ≤ T) (k : ℕ) :
    (1 + chapter08Odd k * T) / (chapter08Odd k) ^ 2 ≤ 1 + T := by
  sorry

theorem chapter08_B_series_summable {T : ℝ} (hT : 0 < T) :
    Summable (chapter08BSeriesTerm T) := by
  sorry

theorem chapter08_B_exact_formula {T : ℝ} (hT : 0 < T) :
    chapter08BT T =
      Real.log 2 + Real.pi ^ 2 / (4 * T) +
        Real.log (chapter08Coth (T / 2)) -
        (2 / T) * (∑' k : ℕ, chapter08BSeriesTerm T k) := by
  sorry

theorem chapter08_C_exact_formula {T : ℝ} (hT : 0 < T) :
    chapter08CT T = Real.pi / 2 - (2 / T) * Real.log (Real.cosh (T / 2)) := by
  sorry

theorem chapter08_B_series_tail_nonnegative
    {T : ℝ} (hT : 0 < T) (m : ℕ) :
    0 ≤ chapter08BSeriesTail T m := by
  sorry

theorem chapter08_B_series_tail_bound
    {T : ℝ} (hT : 0 < T) (m : ℕ) :
    chapter08BSeriesTail T m ≤
      (1 + T) * Real.exp (-((2 * m + 3 : ℕ) : ℝ) * T) /
        (1 - Real.exp (-2 * T)) := by
  sorry

theorem chapter08_limiting_archimedean_integrals :
    (∫ x : ℝ in Ioi 0,
        (1 - 1 / Real.cosh (x / 2)) / (2 * Real.sinh (x / 2))) =
        Real.log 2 ∧
      (∫ x : ℝ in Ioi 0,
        (1 - 1 / Real.cosh (x / 2)) / (2 * Real.cosh (x / 2))) =
        Real.pi / 2 - 1 := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08
