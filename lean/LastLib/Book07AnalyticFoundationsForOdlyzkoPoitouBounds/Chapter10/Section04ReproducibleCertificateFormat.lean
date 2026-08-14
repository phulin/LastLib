import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter10.Section03TailBoundsAndIntervalPropagation

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter10

open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter09
open MeasureTheory Set
open scoped BigOperators

noncomputable section

/-! ## 10.4. A reproducible certificate format -/

def chapter10FixedLogBound (T : ℝ) (n : ℕ) (α : ℝ) : ℝ :=
  chapter09FixedTestFunctionLogBound
    (chapter09UnconditionalTestFunction T) n α

theorem chapter10_fixed_log_bound_eq_chapter09_bound
    (T α : ℝ) (n : ℕ) :
    chapter10FixedLogBound T n α =
      chapter09FixedTestFunctionLogBound
        (chapter09UnconditionalTestFunction T) n α := by
  rfl

theorem chapter10_fixed_log_bound_expanded
    (T α : ℝ) (n : ℕ) :
    chapter10FixedLogBound T n α =
      Real.eulerMascheroniConstant + Real.log (8 * Real.pi) +
        α * (Real.pi / 2) -
        4 * chapter09A (chapter09UnconditionalTestFunction T) / (n : ℝ) -
        chapter09B (chapter09UnconditionalTestFunction T) -
        α * chapter09C (chapter09UnconditionalTestFunction T) := by
  sorry

def Chapter10MonotonicityExtension (T : ℝ) : Prop :=
  ∀ {N n : ℕ} {α₀ α : ℝ},
    0 < N → N ≤ n → α₀ ≤ α →
      chapter10FixedLogBound T N α₀ ≤ chapter10FixedLogBound T n α

theorem chapter10_fixed_test_function_monotonicity_extension
    (F : Chapter09TestFunction)
    (hA : 0 ≤ chapter09A F)
    (hC : chapter09C F < Real.pi / 2) :
    ∀ {N n : ℕ} {α₀ α : ℝ},
      0 < N → N ≤ n → α₀ ≤ α →
        chapter09FixedTestFunctionLogBound F N α₀ ≤
          chapter09FixedTestFunctionLogBound F n α := by
  sorry

theorem chapter10_unconditional_monotonicity_extension
    {T : ℝ} (hT : 0 < T) : Chapter10MonotonicityExtension T := by
  sorry

structure Chapter10DirectedEnclosure (x : ℝ) where
  interval : Chapter10RationalInterval
  valid : interval.Valid
  contains : interval.Contains x

theorem chapter10_directed_enclosure_mem
    {x : ℝ} (E : Chapter10DirectedEnclosure x) :
    (E.interval.lower : ℝ) ≤ x ∧ x ≤ (E.interval.upper : ℝ) := by
  exact E.contains

structure Chapter10ConstantLedger (T : ℝ) where
  gamma : Chapter10DirectedEnclosure Real.eulerMascheroniConstant
  pi : Chapter10DirectedEnclosure Real.pi
  logTwo : Chapter10DirectedEnclosure (Real.log 2)
  expNegativeHalf : Chapter10DirectedEnclosure (Real.exp (-(T / 2)))
  expNegative : Chapter10DirectedEnclosure (Real.exp (-T))
  logOnePlusExpNegative :
    Chapter10DirectedEnclosure (Real.log (1 + Real.exp (-T)))
  logOneMinusExpNegative :
    Chapter10DirectedEnclosure (Real.log (1 - Real.exp (-T)))
  logCoth : Chapter10DirectedEnclosure (Real.log (chapter10Coth (T / 2)))
  logCosh : Chapter10DirectedEnclosure (Real.log (Real.cosh (T / 2)))
  B : Chapter10DirectedEnclosure (chapter10BT T)
  C : Chapter10DirectedEnclosure (chapter10CT T)
  tail : Chapter10DirectedEnclosure (chapter10BSeriesTail T 1)

theorem chapter10_constant_ledger_contains_B_and_C
    {T : ℝ} (L : Chapter10ConstantLedger T) :
    L.B.interval.Contains (chapter10BT T) ∧
      L.C.interval.Contains (chapter10CT T) := by
  exact ⟨L.B.contains, L.C.contains⟩

structure Chapter10Certificate where
  T : ℚ
  T_pos : 0 < (T : ℝ)
  n : ℕ
  n_pos : 0 < n
  alpha : ℚ
  alpha_nonnegative : 0 ≤ (alpha : ℝ)
  alpha_le_one : (alpha : ℝ) ≤ 1
  constants : Chapter10ConstantLedger (T : ℝ)
  logarithmicLowerEndpoint : ℚ
  logarithmicLowerEndpoint_le_bound :
    (logarithmicLowerEndpoint : ℝ) ≤
      chapter10FixedLogBound (T : ℝ) n (alpha : ℝ)
  ceiling : ℚ
  ceiling_pos : 0 < (ceiling : ℝ)
  ceilingLogUpperEndpoint : ℚ
  ceiling_log_le_upper_endpoint :
    Real.log (ceiling : ℝ) ≤ (ceilingLogUpperEndpoint : ℝ)
  positiveDifference : ℚ
  positiveDifference_eq :
    positiveDifference = logarithmicLowerEndpoint - ceilingLogUpperEndpoint
  positiveDifference_pos : 0 < positiveDifference
  monotonicity_extension : Chapter10MonotonicityExtension (T : ℝ)

theorem chapter10_certificate_has_positive_margin
    (C : Chapter10Certificate) :
    0 < C.positiveDifference := by
  exact C.positiveDifference_pos

theorem chapter10_certificate_ceiling_log_upper_endpoint_lt_lower_endpoint
    (C : Chapter10Certificate) :
    (C.ceilingLogUpperEndpoint : ℝ) < (C.logarithmicLowerEndpoint : ℝ) := by
  sorry

theorem chapter10_certificate_extends_logarithmic_lower_endpoint
    (C : Chapter10Certificate) {m : ℕ} {β : ℝ}
    (hm : C.n ≤ m) (hβ : (C.alpha : ℝ) ≤ β) :
    (C.logarithmicLowerEndpoint : ℝ) ≤ chapter10FixedLogBound (C.T : ℝ) m β := by
  exact le_trans C.logarithmicLowerEndpoint_le_bound
    (C.monotonicity_extension C.n_pos hm hβ)

theorem chapter10_certificate_records_key_rounding_inputs
    (C : Chapter10Certificate) :
    0 < (C.T : ℝ) ∧ 0 < C.n ∧ 0 ≤ (C.alpha : ℝ) ∧
      (C.alpha : ℝ) ≤ 1 ∧
      C.constants.B.interval.Contains (chapter10BT (C.T : ℝ)) ∧
      C.constants.C.interval.Contains (chapter10CT (C.T : ℝ)) ∧
      0 < C.positiveDifference := by
  exact ⟨C.T_pos, C.n_pos, C.alpha_nonnegative, C.alpha_le_one,
    C.constants.B.contains, C.constants.C.contains, C.positiveDifference_pos⟩

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter10
