import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter15.Dependencies
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08.Section01TheThreeGoverningIntegrals

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter15

noncomputable section

open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08
open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter09

open MeasureTheory
open scoped BigOperators

/-! ## 15.1. Explicit lower-bound theorem -/

def chapter15UnconditionalLogExpression
    (n : ℕ) (T α : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (8 * Real.pi) + α * (Real.pi / 2) -
    2 * T / (n : ℝ) - chapter15BT T - α * chapter15CT T

def chapter15GRHLogExpression
    (F : Chapter15TestFunction) (n : ℕ) (α : ℝ) : ℝ :=
  chapter15LogLowerBound F n α

def chapter15UnconditionalPoleCost (n : ℕ) (T : ℝ) : ℝ :=
  4 * chapter15A (chapter15FT T) / (n : ℝ)

theorem chapter15_unconditional_log_expression_eq_chapter09_exponent
    (K : Type*) [Field K] [NumberField K] (T : ℝ) :
    chapter15UnconditionalLogExpression
        (chapter15Degree K) T (chapter15RealProportion K) =
      chapter09UnconditionalExponent K T := by
  sorry

theorem chapter15_unconditional_explicit_lower_bound
    (K : Type*) [Field K] [NumberField K]
    {T : ℝ} (hT : 0 < T) :
    Real.exp
        (chapter15UnconditionalLogExpression
          (chapter15Degree K) T (chapter15RealProportion K)) ≤
      chapter15RootDiscriminant K := by
  sorry

theorem chapter15_unconditional_explicit_log_lower_bound
    (K : Type*) [Field K] [NumberField K]
    {T : ℝ} (hT : 0 < T) :
    chapter15UnconditionalLogExpression
        (chapter15Degree K) T (chapter15RealProportion K) ≤
      Real.log (chapter15RootDiscriminant K) := by
  sorry

theorem chapter15_FT_unconditionally_admissible
    {T : ℝ} (hT : 0 < T) :
    Chapter08UnconditionallyAdmissible (chapter15FT T) := by
  sorry

theorem chapter15_GT_grh_admissible
    {T : ℝ} (hT : 0 < T) :
    Chapter08GRHAdmissible (chapter15GT T) := by
  sorry

theorem chapter15_grh_admissible_iff_source_conditions
    (F : Chapter15TestFunction) :
    Chapter08GRHAdmissible F ↔
      Chapter08BasicallyAdmissible F ∧
        (∀ x : ℝ, 0 ≤ F x) ∧
          Continuous F ∧ Integrable F ∧
            ∀ t : ℝ, 0 ≤ chapter08CosineTransform F t := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: Chapters 6--8 should supply the explicit-formula
identity and the zero/prime positivity fields below from the canonical
completed Dedekind-zeta interface.  The certificate keeps those outputs
separate, so it does not assume the lower-bound conclusion itself.
-/
/-
The certificate contains only the preceding explicit-formula data and the
two independent positivity outputs.  It is the local dependency seam for the
source's assertion that GRH-admissible functions give (8.2); it does not put
the desired discriminant inequality into a field.
-/
structure Chapter15GRHExplicitFormulaCertificate
    (F : Chapter15TestFunction)
    (K : Type*) [Field K] [NumberField K]
    [Chapter09ZetaZeroInterface K] where
  admissible : Chapter08GRHAdmissible F
  grh : chapter15GRHFor K
  formula : Chapter08ExplicitFormulaData K F
  zero_nonnegative : 0 ≤ formula.zeroContribution
  prime_nonnegative : 0 ≤ formula.primeContribution

theorem chapter15_grh_explicit_formula_lower_bound
    {F : Chapter15TestFunction}
    {K : Type*} [Field K] [NumberField K]
    [Chapter09ZetaZeroInterface K]
    (C : Chapter15GRHExplicitFormulaCertificate F K) :
    Real.log (chapter15RootDiscriminant K) ≥
      chapter15GRHLogExpression F (chapter15Degree K)
        (chapter15RealProportion K) := by
  simpa [chapter15GRHLogExpression, chapter15LogLowerBound,
    chapter15A, chapter15B, chapter15C, chapter15RealProportion] using
    (chapter08_root_discriminant_lower_bound
      (K := K) (hK := chapter15_degree_pos K) C.formula
      C.zero_nonnegative C.prime_nonnegative)

theorem chapter15_unconditional_pole_integral
    {T : ℝ} (hT : 0 < T) :
    chapter15A (chapter15FT T) = T / 2 := by
  sorry

theorem chapter15_unconditional_pole_cost_eq
    {n : ℕ} {T : ℝ} (hT : 0 < T) (hn : 0 < n) :
    chapter15UnconditionalPoleCost n T = 2 * T / (n : ℝ) := by
  sorry

theorem chapter15_grh_pole_integral
    {T : ℝ} (hT : 0 < T) :
    chapter15A (chapter15GT T) =
      4 / T * (Real.cosh (T / 2) - 1) := by
  sorry

theorem chapter15_grh_pole_cost_eq
    {n : ℕ} {T : ℝ} (hT : 0 < T) (hn : 0 < n) :
    chapter15GRHPoleCost n T =
      16 * (Real.cosh (T / 2) - 1) / ((n : ℝ) * T) := by
  sorry

/-! The exact finite formulas and the geometric tail from (8.5)--(8.6). -/

def chapter15Coth (x : ℝ) : ℝ :=
  Real.cosh x / Real.sinh x

def chapter15Odd (k : ℕ) : ℝ :=
  ((2 * k + 1 : ℕ) : ℝ)

def chapter15BSeriesTerm (T : ℝ) (k : ℕ) : ℝ :=
  ((1 + chapter15Odd k * T) * Real.exp (-chapter15Odd k * T)) /
    (chapter15Odd k) ^ 2

def chapter15BSeriesTail (T : ℝ) (m : ℕ) : ℝ :=
  ∑' k : ℕ, chapter15BSeriesTerm T (m + 1 + k)

theorem chapter15_B_series_coefficient_bound
    {T : ℝ} (hT : 0 ≤ T) (k : ℕ) :
    (1 + chapter15Odd k * T) / (chapter15Odd k) ^ 2 ≤ 1 + T := by
  sorry

theorem chapter15_B_series_summable
    {T : ℝ} (hT : 0 < T) :
    Summable (chapter15BSeriesTerm T) := by
  sorry

theorem chapter15_B_exact_formula
    {T : ℝ} (hT : 0 < T) :
    chapter15BT T =
      Real.log 2 + Real.pi ^ 2 / (4 * T) +
        Real.log (chapter15Coth (T / 2)) -
        (2 / T) * (∑' k : ℕ, chapter15BSeriesTerm T k) := by
  sorry

theorem chapter15_C_exact_formula
    {T : ℝ} (hT : 0 < T) :
    chapter15CT T =
      Real.pi / 2 - (2 / T) * Real.log (Real.cosh (T / 2)) := by
  sorry

theorem chapter15_B_series_tail_nonnegative
    {T : ℝ} (hT : 0 < T) (m : ℕ) :
    0 ≤ chapter15BSeriesTail T m := by
  sorry

theorem chapter15_B_series_tail_bound
    {T : ℝ} (hT : 0 < T) (m : ℕ) :
    chapter15BSeriesTail T m ≤
      (1 + T) * Real.exp (-((2 * m + 3 : ℕ) : ℝ) * T) /
        (1 - Real.exp (-2 * T)) := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter15
