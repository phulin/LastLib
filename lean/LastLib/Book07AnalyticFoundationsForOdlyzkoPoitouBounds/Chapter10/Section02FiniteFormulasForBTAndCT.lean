import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter10.Section01RationalEnclosuresForElementaryConstants

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter10

open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08
open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter09
open MeasureTheory Set
open scoped BigOperators

noncomputable section

/-! ## 10.2. Finite formulas for `B_T` and `C_T` -/

def chapter10AT (T : ℝ) : ℝ :=
  T / 2

def chapter10BT (T : ℝ) : ℝ :=
  chapter08BT T

def chapter10CT (T : ℝ) : ℝ :=
  chapter08CT T

def chapter10Coth (x : ℝ) : ℝ :=
  Real.cosh x / Real.sinh x

def chapter10BSeriesTerm (T : ℝ) (k : ℕ) : ℝ :=
  chapter08BSeriesTerm T k

def chapter10BSeriesTail (T : ℝ) (m : ℕ) : ℝ :=
  chapter08BSeriesTail T m

theorem chapter10_AT_eq_half (T : ℝ) : chapter10AT T = T / 2 :=
  rfl

theorem chapter10_AT_eq_chapter09_unconditional_pole_integral
    {T : ℝ} (hT : 0 < T) :
    chapter10AT T = chapter09UnconditionalPoleIntegral T := by
  sorry

theorem chapter10_coth_eq_chapter08_coth (x : ℝ) :
    chapter10Coth x = chapter08Coth x :=
  rfl

theorem chapter10_BT_eq_chapter09_BT (T : ℝ) :
    chapter10BT T = chapter09BT T := by
  sorry

theorem chapter10_CT_eq_chapter09_CT (T : ℝ) :
    chapter10CT T = chapter09CT T := by
  sorry

theorem chapter10_log_coth_rewrite
    {T : ℝ} (hT : 0 < T) :
    Real.log (chapter10Coth (T / 2)) =
      Real.log (1 + Real.exp (-T)) - Real.log (1 - Real.exp (-T)) := by
  sorry

theorem chapter10_log_cosh_half_rewrite
    {T : ℝ} (hT : 0 < T) :
    Real.log (Real.cosh (T / 2)) =
      T / 2 - Real.log 2 + Real.log (1 + Real.exp (-T)) := by
  sorry

theorem chapter10_B_finite_formula
    {T : ℝ} (hT : 0 < T) :
    chapter10BT T =
      Real.log 2 + Real.pi ^ 2 / (4 * T) +
        Real.log (chapter10Coth (T / 2)) -
        (2 / T) * (∑' k : ℕ, chapter10BSeriesTerm T k) := by
  sorry

theorem chapter10_C_finite_formula
    {T : ℝ} (hT : 0 < T) :
    chapter10CT T =
      Real.pi / 2 - (2 / T) * Real.log (Real.cosh (T / 2)) := by
  sorry

theorem chapter10_B_series_tail_bound
    {T : ℝ} (hT : 0 < T) (m : ℕ) :
    0 ≤ chapter10BSeriesTail T m ∧
      chapter10BSeriesTail T m ≤
        (1 + T) * Real.exp (-((2 * m + 3 : ℕ) : ℝ) * T) /
          (1 - Real.exp (-2 * T)) := by
  sorry

def chapter10AlternatingExpPartialSum (r : ℝ) (M : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (M + 1), (-r) ^ j / (Nat.factorial j : ℝ)

def chapter10AlternatingExpRemainder (r : ℝ) (M : ℕ) : ℝ :=
  Real.exp (-r) - chapter10AlternatingExpPartialSum r M

theorem chapter10_alternating_exp_series_identity (r : ℝ) (M : ℕ) :
    Real.exp (-r) =
      chapter10AlternatingExpPartialSum r M +
        chapter10AlternatingExpRemainder r M := by
  sorry

theorem chapter10_alternating_exp_remainder_bound
    {r : ℝ} (hr : 0 ≤ r) {M : ℕ} (hM : r < (M + 2 : ℕ)) :
    0 ≤ (-1 : ℝ) ^ (M + 1) * chapter10AlternatingExpRemainder r M ∧
      (-1 : ℝ) ^ (M + 1) * chapter10AlternatingExpRemainder r M ≤
        r ^ (M + 1) / (Nat.factorial (M + 1) : ℝ) := by
  sorry

structure Chapter10RationalInterval where
  lower : ℚ
  upper : ℚ

def Chapter10RationalInterval.Valid (I : Chapter10RationalInterval) : Prop :=
  I.lower ≤ I.upper

def Chapter10RationalInterval.Contains
    (I : Chapter10RationalInterval) (x : ℝ) : Prop :=
  (I.lower : ℝ) ≤ x ∧ x ≤ (I.upper : ℝ)

theorem chapter10_rational_interval_contains_iff
    (I : Chapter10RationalInterval) (x : ℝ) :
    I.Contains x ↔ x ∈ Set.Icc (I.lower : ℝ) (I.upper : ℝ) := by
  rfl

def chapter10GammaInterval : Chapter10RationalInterval :=
  { lower := chapter10GammaLower
    upper := chapter10GammaUpper }

def chapter10PiInterval : Chapter10RationalInterval :=
  { lower := chapter10PiLower
    upper := chapter10PiUpper }

theorem chapter10_gamma_interval_contains :
    chapter10GammaInterval.Contains Real.eulerMascheroniConstant := by
  sorry

theorem chapter10_gamma_interval_valid : chapter10GammaInterval.Valid := by
  sorry

theorem chapter10_pi_interval_contains :
    chapter10PiInterval.Contains Real.pi := by
  sorry

theorem chapter10_pi_interval_valid : chapter10PiInterval.Valid := by
  sorry

def chapter10SquareInterval (I : Chapter10RationalInterval) :
    Chapter10RationalInterval :=
  { lower := I.lower ^ 2
    upper := I.upper ^ 2 }

theorem chapter10_square_interval_contains
    {I : Chapter10RationalInterval} (hvalid : I.Valid)
    (hlower : 0 ≤ I.lower) {x : ℝ} (hx : I.Contains x) :
    (chapter10SquareInterval I).Contains (x ^ 2) := by
  sorry

theorem chapter10_exp_negative_is_square_of_half (T : ℝ) :
    Real.exp (-T) = (Real.exp (-(T / 2))) ^ 2 := by
  sorry

theorem chapter10_exp_negative_square_interval
    {T a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hlo : a ≤ Real.exp (-(T / 2)))
    (hhi : Real.exp (-(T / 2)) ≤ b) :
    a ^ 2 ≤ Real.exp (-T) ∧ Real.exp (-T) ≤ b ^ 2 := by
  sorry

structure Chapter10ArchimedeanLedgerRow where
  T : ℚ
  A : ℚ
  B_lower : ℚ
  B_upper : ℚ
  C_lower : ℚ
  C_upper : ℚ

def chapter10RowSeventeenOverFive : Chapter10ArchimedeanLedgerRow :=
  { T := 17 / 5
    A := 17 / 10
    B_lower := 139921 / 100000
    B_upper := 139923 / 100000
    C_lower := 95921 / 100000
    C_upper := 95923 / 100000 }

def chapter10RowNineHalves : Chapter10ArchimedeanLedgerRow :=
  { T := 9 / 2
    A := 9 / 4
    B_lower := 123652 / 100000
    B_upper := 123653 / 100000
    C_lower := 87395 / 100000
    C_upper := 87396 / 100000 }

def chapter10RowSix : Chapter10ArchimedeanLedgerRow :=
  { T := 6
    A := 3
    B_lower := 110355 / 100000
    B_upper := 110356 / 100000
    C_lower := 80102 / 100000
    C_upper := 80103 / 100000 }

theorem chapter10_archimedean_ledger_row_seventeen_over_five :
    chapter10AT (17 / 5 : ℝ) = 17 / 10 ∧
      (chapter10RowSeventeenOverFive.B_lower : ℝ) < chapter10BT (17 / 5 : ℝ) ∧
      chapter10BT (17 / 5 : ℝ) < (chapter10RowSeventeenOverFive.B_upper : ℝ) ∧
      (chapter10RowSeventeenOverFive.C_lower : ℝ) < chapter10CT (17 / 5 : ℝ) ∧
      chapter10CT (17 / 5 : ℝ) < (chapter10RowSeventeenOverFive.C_upper : ℝ) := by
  sorry

theorem chapter10_archimedean_ledger_row_nine_halves :
    chapter10AT (9 / 2 : ℝ) = 9 / 4 ∧
      (chapter10RowNineHalves.B_lower : ℝ) < chapter10BT (9 / 2 : ℝ) ∧
      chapter10BT (9 / 2 : ℝ) < (chapter10RowNineHalves.B_upper : ℝ) ∧
      (chapter10RowNineHalves.C_lower : ℝ) < chapter10CT (9 / 2 : ℝ) ∧
      chapter10CT (9 / 2 : ℝ) < (chapter10RowNineHalves.C_upper : ℝ) := by
  sorry

theorem chapter10_archimedean_ledger_row_six :
    chapter10AT 6 = 3 ∧
      (chapter10RowSix.B_lower : ℝ) < chapter10BT 6 ∧
      chapter10BT 6 < (chapter10RowSix.B_upper : ℝ) ∧
      (chapter10RowSix.C_lower : ℝ) < chapter10CT 6 ∧
      chapter10CT 6 < (chapter10RowSix.C_upper : ℝ) := by
  sorry

theorem chapter10_omitted_B_series_contribution_bound
    {T : ℝ} (hT : 0 < T) (m : ℕ) :
    0 ≤ (2 / T) * chapter10BSeriesTail T m ∧
      (2 / T) * chapter10BSeriesTail T m ≤
        (2 / T) * (1 + T) * Real.exp (-((2 * m + 3 : ℕ) : ℝ) * T) /
          (1 - Real.exp (-2 * T)) := by
  sorry

theorem chapter10_omitted_B_series_first_row_lt :
    (2 / (17 / 5 : ℝ)) * chapter10BSeriesTail (17 / 5 : ℝ) 1 <
      (1.072709 : ℝ) * 10 ^ (-7 : ℤ) := by
  sorry

theorem chapter10_omitted_B_series_rows_lt :
    ((2 / (9 / 2 : ℝ)) * chapter10BSeriesTail (9 / 2 : ℝ) 1 <
        (4.136261 : ℝ) * 10 ^ (-10 : ℤ)) ∧
      ((2 / (6 : ℝ)) * chapter10BSeriesTail 6 1 <
        (2.183459 : ℝ) * 10 ^ (-13 : ℤ)) := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter10
