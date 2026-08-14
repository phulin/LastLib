import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter02.Core
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter10.Section02FiniteFormulasForBTAndCT
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter09.Section01UniversalOdlyzkoPoitouInequalities

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11

noncomputable section

open MeasureTheory
open Module NumberField NumberField.InfinitePlace
open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter02
open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter10
open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter09
open scoped BigOperators

/-!
Shared interfaces for the finite-degree ledger.

The degree, signature, discriminant, and root-discriminant definitions below
are thin book-facing wrappers around the pinned Mathlib number-field API.  The
triangular test function is defined here because all three numerical rows in
Chapter 11 use the same unconditional test function.
-/

abbrev chapter11Degree (K : Type*) [Field K] [NumberField K] : ℕ :=
  Module.finrank ℚ K

def chapter11RootDiscriminant (K : Type*) [Field K] [NumberField K] : ℝ :=
  NumberField.rootDiscr K

@[simp] theorem chapter11_root_discriminant_eq_canonical
    (K : Type*) [Field K] [NumberField K] :
    chapter11RootDiscriminant K = NumberField.rootDiscr K :=
  rfl

theorem chapter11_root_discriminant_pos
    (K : Type*) [Field K] [NumberField K] :
    0 < chapter11RootDiscriminant K := by
  rw [chapter11RootDiscriminant, ← chapter09_root_discriminant_eq_canonical K]
  exact chapter09_root_discriminant_pos K

def chapter11RealProportion (K : Type*) [Field K] [NumberField K] : ℝ :=
  (NumberField.InfinitePlace.nrRealPlaces K : ℝ) /
    (Module.finrank ℚ K : ℝ)

theorem chapter11_real_proportion_nonneg
    (K : Type*) [Field K] [NumberField K] :
    0 ≤ chapter11RealProportion K := by
  simpa [chapter11RealProportion, chapter02RealProportion] using
    (chapter02_real_proportion_bounds K).1

theorem chapter11_real_proportion_le_one
    (K : Type*) [Field K] [NumberField K] :
    chapter11RealProportion K ≤ 1 := by
  simpa [chapter11RealProportion, chapter02RealProportion] using
    (chapter02_real_proportion_bounds K).2

theorem chapter11_degree_pos
    (K : Type*) [Field K] [NumberField K] :
    0 < chapter11Degree K := by
  exact Module.finrank_pos

/-! The factorial factor `Mₙ = (nⁿ/n!)^(2/n)` from the geometric bound. -/

noncomputable def chapter11MinkowskiFactor (n : ℕ) : ℝ :=
  if n = 0 then 1 else
    Real.rpow (((n : ℝ) ^ n) / (Nat.factorial n : ℝ)) (2 / (n : ℝ))

theorem chapter11_minkowski_factor_of_pos (n : ℕ) (hn : 0 < n) :
    chapter11MinkowskiFactor n =
      Real.rpow (((n : ℝ) ^ n) / (Nat.factorial n : ℝ)) (2 / (n : ℝ)) := by
  simp [chapter11MinkowskiFactor, Nat.ne_of_gt hn]

theorem chapter11_minkowski_factor_succ_le (n : ℕ) (hn : 0 < n) :
    chapter11MinkowskiFactor n ≤ chapter11MinkowskiFactor (n + 1) := by
  simpa [chapter11MinkowskiFactor, chapter02FactorialFactor,
    Nat.ne_of_gt hn, Nat.ne_of_gt (by omega : 0 < n + 1)] using
    (chapter02_factorial_factor_succ_le (n := n) hn)

theorem chapter11_minkowski_factor_le_of_le
    {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    chapter11MinkowskiFactor m ≤ chapter11MinkowskiFactor n := by
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  have hmono := chapter02_factorial_factor_monotone
    (a := m) (b := n) (by simpa using hm) (by simpa using hn) hmn
  simpa [chapter11MinkowskiFactor, chapter02FactorialFactor,
    Nat.ne_of_gt hm, Nat.ne_of_gt hn] using hmono

def chapter11GeometricRootDiscriminantBound
    (K : Type*) [Field K] [NumberField K] : ℝ :=
  Real.rpow (Real.pi / 4) (1 - chapter11RealProportion K) *
    chapter11MinkowskiFactor (chapter11Degree K)

theorem chapter11_geometric_root_discriminant_bound
    (K : Type*) [Field K] [NumberField K] :
    chapter11GeometricRootDiscriminantBound K ≤
      chapter11RootDiscriminant K := by
  have hdeg : 0 < chapter11Degree K := chapter11_degree_pos K
  simpa [chapter11GeometricRootDiscriminantBound, chapter11RootDiscriminant,
    chapter11RealProportion, chapter11MinkowskiFactor,
    chapter02GeometricLowerBound, chapter02RootDiscriminant,
    chapter02RealProportion, chapter02FactorialFactor,
    Nat.ne_of_gt hdeg] using
    (chapter02_root_discriminant_lower_bound K)

theorem chapter11_worst_signature_root_discriminant_bound
    (K : Type*) [Field K] [NumberField K] :
    (Real.pi / 4) * chapter11MinkowskiFactor (chapter11Degree K) ≤
      chapter11RootDiscriminant K := by
  have hdeg : 0 < chapter11Degree K := chapter11_degree_pos K
  have h := (chapter02_geometric_lower_bound_ge_worst_signature K).trans
    (chapter02_root_discriminant_lower_bound K)
  simpa [chapter11RootDiscriminant, chapter11MinkowskiFactor,
    chapter02RootDiscriminant, chapter02FactorialFactor,
    Nat.ne_of_gt hdeg] using h

theorem chapter11_totally_real_root_discriminant_bound
    (K : Type*) [Field K] [NumberField K] [IsTotallyReal K] :
    chapter11MinkowskiFactor (chapter11Degree K) ≤
      chapter11RootDiscriminant K := by
  have hdeg : 0 < chapter11Degree K := chapter11_degree_pos K
  have h := chapter02_totally_real_geometric_lower_bound K
  simpa [chapter11RootDiscriminant, chapter11MinkowskiFactor,
    chapter02RootDiscriminant, chapter02FactorialFactor,
    Nat.ne_of_gt hdeg] using h

theorem chapter11_degree_lt_of_worst_signature_crossing
    (K : Type*) [Field K] [NumberField K]
    (U : ℝ) (N : ℕ) (hN : 0 < N)
    (hceiling : chapter11RootDiscriminant K < U)
    (hcross : U < (Real.pi / 4) * chapter11MinkowskiFactor N) :
    chapter11Degree K < N := by
  have hcross' : U < (Real.pi / 4) * chapter02FactorialFactor N := by
    simpa [chapter11MinkowskiFactor, chapter02FactorialFactor,
      Nat.ne_of_gt hN] using hcross
  simpa [chapter11RootDiscriminant, chapter11MinkowskiFactor,
    chapter02RootDiscriminant, chapter02FactorialFactor,
    Nat.ne_of_gt hN] using
    (chapter02_geometric_degree_exclusion K hN hcross' hceiling)

theorem chapter11_degree_lt_of_totally_real_crossing
    (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]
    (U : ℝ) (N : ℕ) (hN : 0 < N)
    (hceiling : chapter11RootDiscriminant K < U)
    (hcross : U < chapter11MinkowskiFactor N) :
    chapter11Degree K < N := by
  have hcross' : U < chapter02FactorialFactor N := by
    simpa [chapter11MinkowskiFactor, chapter02FactorialFactor,
      Nat.ne_of_gt hN] using hcross
  simpa [chapter11RootDiscriminant, chapter11MinkowskiFactor,
    chapter02RootDiscriminant, chapter02FactorialFactor,
    Nat.ne_of_gt hN] using
    (chapter02_totally_real_degree_exclusion K hN hcross' hceiling)

/-! The triangular unconditional test function and its two losses. -/

def chapter11TriangularAutocorrelation (T x : ℝ) : ℝ :=
  max (1 - |x| / T) 0

def chapter11UnconditionalTestFunction (T x : ℝ) : ℝ :=
  chapter11TriangularAutocorrelation T x / Real.cosh (x / 2)

noncomputable def chapter11B (T : ℝ) : ℝ :=
  ∫ x in Set.Ici (0 : ℝ),
    (1 - chapter11UnconditionalTestFunction T x) / (2 * Real.sinh (x / 2))

noncomputable def chapter11C (T : ℝ) : ℝ :=
  ∫ x in Set.Ici (0 : ℝ),
    (1 - chapter11UnconditionalTestFunction T x) / (2 * Real.cosh (x / 2))

def chapter11ExplicitFormulaLogExpression
    (n : ℕ) (T : ℝ) (α : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (8 * Real.pi) + α * (Real.pi / 2) -
    2 * T / (n : ℝ) - chapter11B T - α * chapter11C T

def chapter11ExplicitFormulaLogBound
    (K : Type*) [Field K] [NumberField K] (T : ℝ) : ℝ :=
  chapter11ExplicitFormulaLogExpression (chapter11Degree K) T
    (chapter11RealProportion K)

noncomputable def chapter11ExplicitFormulaRootBound
    (K : Type*) [Field K] [NumberField K] (T : ℝ) : ℝ :=
  Real.exp (chapter11ExplicitFormulaLogBound K T)

theorem chapter11_explicit_formula_log_bound_eq_expression
    (K : Type*) [Field K] [NumberField K] (T : ℝ) :
    chapter11ExplicitFormulaLogBound K T =
      chapter11ExplicitFormulaLogExpression (chapter11Degree K) T
        (chapter11RealProportion K) :=
  rfl

/- The `Ici` integrals used in this chapter and the `Ioi` integrals used by
   Chapter 9 differ only at the null endpoint.  These two wrapper bridges
   keep the canonical Chapter 9 universal inequality usable here. -/
theorem chapter11_root_discriminant_eq_chapter09
    (K : Type*) [Field K] [NumberField K] :
    chapter11RootDiscriminant K = chapter09RootDiscriminant K := by
  rw [chapter09_root_discriminant_eq_canonical K]
  rfl

theorem chapter11_explicit_formula_log_bound_eq_chapter09
    (K : Type*) [Field K] [NumberField K] (T : ℝ) :
    chapter11ExplicitFormulaLogBound K T = chapter09UnconditionalExponent K T := by
  have hB : chapter11B T = chapter09BT T := by
    unfold chapter11B chapter09BT chapter09B
    rw [integral_Ici_eq_integral_Ioi]
    rfl
  have hC : chapter11C T = chapter09CT T := by
    unfold chapter11C chapter09CT chapter09C
    rw [integral_Ici_eq_integral_Ioi]
    rfl
  unfold chapter11ExplicitFormulaLogBound chapter11ExplicitFormulaLogExpression
  rw [hB, hC]
  rfl

theorem chapter11_B_eq_chapter10_BT (T : ℝ) :
    chapter11B T = chapter10BT T := by
  unfold chapter11B chapter10BT
  rw [integral_Ici_eq_integral_Ioi]
  rfl

theorem chapter11_C_eq_chapter10_CT (T : ℝ) :
    chapter11C T = chapter10CT T := by
  unfold chapter11C chapter10CT
  rw [integral_Ici_eq_integral_Ioi]
  rfl

theorem chapter11_explicit_formula_log_root_discriminant_bound
    (K : Type*) [Field K] [NumberField K] (T : ℝ) (hT : 0 < T) :
    chapter11ExplicitFormulaLogBound K T ≤
      Real.log (chapter11RootDiscriminant K) := by
  calc
    chapter11ExplicitFormulaLogBound K T = chapter09UnconditionalExponent K T :=
      chapter11_explicit_formula_log_bound_eq_chapter09 K T
    _ ≤ Real.log (chapter09RootDiscriminant K) :=
      chapter09_universal_odlyzko_poitou_log_bound K hT
    _ = Real.log (chapter11RootDiscriminant K) := by
      rw [← chapter11_root_discriminant_eq_chapter09 K]

theorem chapter11_explicit_formula_root_discriminant_bound
    (K : Type*) [Field K] [NumberField K] (T : ℝ) (hT : 0 < T) :
    chapter11ExplicitFormulaRootBound K T ≤
      chapter11RootDiscriminant K := by
  calc
    chapter11ExplicitFormulaRootBound K T =
        Real.exp (chapter11ExplicitFormulaLogBound K T) := rfl
    _ ≤ Real.exp (Real.log (chapter11RootDiscriminant K)) :=
      Real.exp_le_exp.mpr (chapter11_explicit_formula_log_root_discriminant_bound K T hT)
    _ = chapter11RootDiscriminant K :=
      Real.exp_log (chapter11_root_discriminant_pos K)

theorem chapter11_explicit_formula_log_expression_mono_degree
    {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) (T : ℝ) (hT : 0 < T) (α : ℝ) :
    chapter11ExplicitFormulaLogExpression m T α ≤
      chapter11ExplicitFormulaLogExpression n T α := by
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hdiv : 2 * T / (n : ℝ) ≤ 2 * T / (m : ℝ) := by
    apply (div_le_div_iff₀ hnR hmR).2
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hmn) (by positivity)
  unfold chapter11ExplicitFormulaLogExpression
  linarith

theorem chapter11_explicit_formula_log_expression_mono_signature
    (n : ℕ) (T α β : ℝ) (hαβ : α ≤ β) (hC : chapter11C T ≤ Real.pi / 2) :
    chapter11ExplicitFormulaLogExpression n T α ≤
      chapter11ExplicitFormulaLogExpression n T β := by
  have hαβ' : 0 ≤ β - α := sub_nonneg.mpr hαβ
  have hcoef : 0 ≤ Real.pi / 2 - chapter11C T := sub_nonneg.mpr hC
  have hprod : 0 ≤ (β - α) * (Real.pi / 2 - chapter11C T) :=
    mul_nonneg hαβ' hcoef
  unfold chapter11ExplicitFormulaLogExpression
  nlinarith

theorem chapter11_explicit_formula_log_expression_ge_of_B_upper
    (n : ℕ) (T α B₀ : ℝ) (hB : chapter11B T ≤ B₀) :
    Real.eulerMascheroniConstant + Real.log (8 * Real.pi) + α * (Real.pi / 2) -
        2 * T / (n : ℝ) - B₀ - α * chapter11C T ≤
      chapter11ExplicitFormulaLogExpression n T α := by
  unfold chapter11ExplicitFormulaLogExpression
  linarith

theorem chapter11_degree_lt_of_explicit_formula_crossing
    (K : Type*) [Field K] [NumberField K]
    (U T : ℝ) (N : ℕ) (hN : 0 < N) (hT : 0 < T)
    (hU : 0 < U) (hceiling : chapter11RootDiscriminant K < U)
    (hC : chapter11C T ≤ Real.pi / 2)
    (hcross : Real.log U <
      chapter11ExplicitFormulaLogExpression N T 0) :
    chapter11Degree K < N := by
  by_contra hnot
  have hNle : N ≤ chapter11Degree K := Nat.le_of_not_gt hnot
  have hdeg := chapter11_degree_pos K
  have hα := chapter11_real_proportion_nonneg K
  have hmono_degree := chapter11_explicit_formula_log_expression_mono_degree
    hN hNle T hT 0
  have hmono_signature := chapter11_explicit_formula_log_expression_mono_signature
    (chapter11Degree K) T 0 (chapter11RealProportion K) hα hC
  have hcross' : Real.log U <
      chapter11ExplicitFormulaLogExpression (chapter11Degree K) T
        (chapter11RealProportion K) :=
    hcross.trans_le (hmono_degree.trans hmono_signature)
  have hUexp : U < Real.exp
      (chapter11ExplicitFormulaLogExpression N T 0) := by
    calc
      U = Real.exp (Real.log U) := (Real.exp_log hU).symm
      _ < Real.exp (chapter11ExplicitFormulaLogExpression N T 0) :=
        Real.exp_lt_exp.mpr hcross
  have hExpMono : Real.exp
      (chapter11ExplicitFormulaLogExpression N T 0) ≤
      Real.exp (chapter11ExplicitFormulaLogExpression (chapter11Degree K) T
        (chapter11RealProportion K)) := by
    exact Real.exp_le_exp.mpr (hmono_degree.trans hmono_signature)
  have hbound := chapter11_explicit_formula_root_discriminant_bound K T hT
  have hbound' : Real.exp
      (chapter11ExplicitFormulaLogExpression (chapter11Degree K) T
        (chapter11RealProportion K)) ≤ chapter11RootDiscriminant K := by
    simpa [chapter11ExplicitFormulaRootBound,
      chapter11ExplicitFormulaLogBound] using hbound
  have hlt : U < chapter11RootDiscriminant K :=
    hUexp.trans_le (hExpMono.trans hbound')
  exact (lt_irrefl U) (hlt.trans hceiling)

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11
