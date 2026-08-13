import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter09.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter09

open Filter
open scoped Topology

noncomputable section

/-! ## 9. Universal Odlyzko--Poitou inequalities -/

/-! ### 9.1 One test function, one rigorous bound -/

theorem chapter09_universal_odlyzko_poitou_bound
    (K : Type*) [Field K] [NumberField K]
    {T : ℝ} (hT : 0 < T) :
    Real.exp (chapter09UnconditionalExponent K T) ≤
      chapter09RootDiscriminant K := by
  sorry

theorem chapter09_universal_odlyzko_poitou_log_bound
    (K : Type*) [Field K] [NumberField K]
    {T : ℝ} (hT : 0 < T) :
    chapter09UnconditionalExponent K T ≤
      Real.log (chapter09RootDiscriminant K) := by
  sorry

/-! ### 9.2 Unconditional asymptotic constants -/

theorem chapter09_unconditional_archimedean_B_tendsto :
    Tendsto chapter09BT atTop (𝓝 (Real.log 2)) := by
  sorry

theorem chapter09_unconditional_archimedean_C_tendsto :
    Tendsto chapter09CT atTop (𝓝 (Real.pi / 2 - 1)) := by
  sorry

def chapter09UnconditionalAsymptoticConstant (α₀ : ℝ) : ℝ :=
  4 * Real.pi * Real.exp (chapter09EulerMascheroni + α₀)

theorem chapter09_unconditional_asymptotic_lower_bound
    (S : Chapter09NumberFieldSequence) (α₀ : ℝ) (T : ℕ → ℝ)
    (hTpos : ∀ j, 0 < T j)
    (hT : Tendsto T atTop atTop)
    (hdegree : Tendsto (fun j => (chapter09SequenceDegree S j : ℝ)) atTop atTop)
    (halpha : α₀ ≤ Filter.liminf (chapter09SequenceRealProportion S) atTop)
    (hTdegree :
      Tendsto
        (fun j => T j / (chapter09SequenceDegree S j : ℝ))
        atTop (𝓝 0)) :
    Filter.liminf (chapter09SequenceRootDiscriminant S) atTop ≥
      chapter09UnconditionalAsymptoticConstant α₀ := by
  sorry

theorem chapter09_unconditional_endpoint_constants :
    chapter09UnconditionalAsymptoticConstant 0 =
        4 * Real.pi * Real.exp chapter09EulerMascheroni ∧
      chapter09UnconditionalAsymptoticConstant 1 =
        4 * Real.pi * Real.exp (1 + chapter09EulerMascheroni) := by
  sorry

/- The source prints decimal approximations with an ellipsis.  These rational
enclosures record the mathematical content without treating a decimal with
ellipsis as an equality. -/
theorem chapter09_unconditional_endpoint_zero_decimal_bounds :
    (223816160954 : ℝ) / (10 : ℝ) ^ 10 <
        chapter09UnconditionalAsymptoticConstant 0 ∧
      chapter09UnconditionalAsymptoticConstant 0 <
        (223816160955 : ℝ) / (10 : ℝ) ^ 10 := by
  sorry

theorem chapter09_unconditional_endpoint_one_decimal_bounds :
    (608395403238 : ℝ) / (10 : ℝ) ^ 10 <
        chapter09UnconditionalAsymptoticConstant 1 ∧
      chapter09UnconditionalAsymptoticConstant 1 <
        (608395403239 : ℝ) / (10 : ℝ) ^ 10 := by
  sorry

/-! ### 9.3 Bounds under the generalized Riemann hypothesis -/

theorem chapter09_grh_archimedean_B_tendsto :
    Tendsto chapter09GRHBT atTop (𝓝 0) := by
  sorry

theorem chapter09_grh_archimedean_C_tendsto :
    Tendsto chapter09GRHCT atTop (𝓝 0) := by
  sorry

/- The signature coefficient used by the threshold comparison is
   nonnegative for the two triangular test functions. -/
theorem chapter09_unconditional_archimedean_C_lt_pi_div_two
    {T : ℝ} (hT : 0 < T) :
    chapter09CT T < Real.pi / 2 := by
  sorry

theorem chapter09_grh_archimedean_C_lt_pi_div_two
    {T : ℝ} (hT : 0 < T) :
    chapter09GRHCT T < Real.pi / 2 := by
  sorry

theorem chapter09_grh_universal_odlyzko_poitou_bound
    (K : Type*) [Field K] [NumberField K]
    [Chapter09ZetaZeroInterface K]
    {T : ℝ} (hT : 0 < T) (hGRH : chapter09GRH K) :
    Real.exp (chapter09GRHExponent K T) ≤
      chapter09RootDiscriminant K := by
  sorry

def chapter09GRHAsymptoticConstant (α₀ : ℝ) : ℝ :=
  8 * Real.pi * Real.exp
    (chapter09EulerMascheroni + α₀ * (Real.pi / 2))

theorem chapter09_grh_asymptotic_lower_bound
    (S : Chapter09NumberFieldSequence) (α₀ : ℝ) (T : ℕ → ℝ)
    (hGRH : ∀ j, chapter09SequenceGRH S j)
    (hTpos : ∀ j, 0 < T j)
    (hT : Tendsto T atTop atTop)
    (hdegree : Tendsto (fun j => (chapter09SequenceDegree S j : ℝ)) atTop atTop)
    (halpha : α₀ ≤ Filter.liminf (chapter09SequenceRealProportion S) atTop)
    (hpole :
      Tendsto
        (fun j =>
          Real.exp (T j / 2) /
            ((chapter09SequenceDegree S j : ℝ) * T j))
        atTop (𝓝 0)) :
    Filter.liminf (chapter09SequenceRootDiscriminant S) atTop ≥
      chapter09GRHAsymptoticConstant α₀ := by
  sorry

theorem chapter09_grh_endpoint_constants :
    chapter09GRHAsymptoticConstant 0 =
        8 * Real.pi * Real.exp chapter09EulerMascheroni ∧
      chapter09GRHAsymptoticConstant 1 =
        8 * Real.pi * Real.exp
          (chapter09EulerMascheroni + Real.pi / 2) := by
  sorry

theorem chapter09_grh_endpoint_zero_decimal_bounds :
    (447632321909 : ℝ) / (10 : ℝ) ^ 10 <
        chapter09GRHAsymptoticConstant 0 ∧
      chapter09GRHAsymptoticConstant 0 <
        (447632321910 : ℝ) / (10 : ℝ) ^ 10 := by
  sorry

theorem chapter09_grh_endpoint_one_decimal_bounds :
    (2153325159534 : ℝ) / (10 : ℝ) ^ 10 <
        chapter09GRHAsymptoticConstant 1 ∧
      chapter09GRHAsymptoticConstant 1 <
        (2153325159535 : ℝ) / (10 : ℝ) ^ 10 := by
  sorry

/- A finite GRH certificate must retain a positive finite support parameter. -/
structure Chapter09FiniteGRHCertificate
    (K : Type*) [Field K] [NumberField K]
    [Chapter09ZetaZeroInterface K] where
  T : ℝ
  T_pos : 0 < T
  grh : chapter09GRH K
  poleIntegral : ℝ
  B : ℝ
  C : ℝ
  poleIntegral_eq : poleIntegral = chapter09GRHPoleIntegral T
  B_eq : B = chapter09GRHBT T
  C_eq : C = chapter09GRHCT T

theorem chapter09_finite_grh_certificate_has_evaluated_test_function
    (K : Type*) [Field K] [NumberField K]
    [Chapter09ZetaZeroInterface K]
    (C : Chapter09FiniteGRHCertificate K) :
    0 < C.T ∧
      C.poleIntegral = chapter09GRHPoleIntegral C.T ∧
      C.B = chapter09GRHBT C.T ∧
      C.C = chapter09GRHCT C.T := by
  exact ⟨C.T_pos, C.poleIntegral_eq, C.B_eq, C.C_eq⟩

theorem chapter09_finite_grh_certificate_gives_bound
    (K : Type*) [Field K] [NumberField K]
    [Chapter09ZetaZeroInterface K]
    (C : Chapter09FiniteGRHCertificate K) :
    Real.exp
        (chapter09EulerMascheroni + Real.log (8 * Real.pi) +
          chapter09RealProportion K * (Real.pi / 2) -
          4 * C.poleIntegral / (chapter09Degree K : ℝ) - C.B -
          chapter09RealProportion K * C.C) ≤
      chapter09RootDiscriminant K := by
  sorry

/-! ### 9.4 Degree and signature monotonicity -/

def chapter09FixedTestFunctionConstant (F : Chapter09TestFunction) : ℝ :=
  chapter09EulerMascheroni + Real.log (8 * Real.pi) - chapter09B F

def chapter09FixedTestFunctionLogBound
    (F : Chapter09TestFunction) (n : ℕ) (α : ℝ) : ℝ :=
  chapter09FixedTestFunctionConstant F +
      α * (Real.pi / 2 - chapter09C F) -
    4 * chapter09A F / (n : ℝ)

def chapter09FixedLogCertificate
    (F : Chapter09TestFunction) (N : ℕ) (α₀ L : ℝ) : Prop :=
  L ≤ chapter09FixedTestFunctionLogBound F N α₀

theorem chapter09_unconditional_exponent_eq_fixed_test_function_log_bound
    (K : Type*) [Field K] [NumberField K]
    {T : ℝ} (hT : 0 < T) :
    chapter09UnconditionalExponent K T =
      chapter09FixedTestFunctionLogBound
        (chapter09UnconditionalTestFunction T)
        (chapter09Degree K) (chapter09RealProportion K) := by
  sorry

theorem chapter09_fixed_log_bound_increases_with_degree
    (F : Chapter09TestFunction) {n m : ℕ} {α : ℝ}
    (hA : 0 ≤ chapter09A F) (hn : 0 < n) (hnm : n ≤ m) :
    chapter09FixedTestFunctionLogBound F n α ≤
      chapter09FixedTestFunctionLogBound F m α := by
  sorry

theorem chapter09_fixed_log_bound_increases_with_signature
    (F : Chapter09TestFunction) {n : ℕ} {α β : ℝ}
    (hαβ : α ≤ β) (hC : chapter09C F < Real.pi / 2) :
    chapter09FixedTestFunctionLogBound F n α ≤
      chapter09FixedTestFunctionLogBound F n β := by
  sorry

theorem chapter09_fixed_certificate_covers_larger_degree_and_signature
    (F : Chapter09TestFunction) {N n : ℕ} {α₀ α : ℝ}
    (hA : 0 ≤ chapter09A F) (hC : chapter09C F < Real.pi / 2)
    (hN : 0 < N) (hNn : N ≤ n) (hα : α₀ ≤ α) :
    chapter09FixedTestFunctionLogBound F N α₀ ≤
      chapter09FixedTestFunctionLogBound F n α := by
  sorry

theorem chapter09_fixed_log_certificate_covers_larger_degree_and_signature
    (F : Chapter09TestFunction) {N n : ℕ} {α₀ α L : ℝ}
    (hcert : chapter09FixedLogCertificate F N α₀ L)
    (hA : 0 ≤ chapter09A F) (hC : chapter09C F < Real.pi / 2)
    (hN : 0 < N) (hNn : N ≤ n) (hα : α₀ ≤ α) :
    chapter09FixedLogCertificate F n α L := by
  sorry

/-! ### 9.5 Threshold and stabilization principles -/

def chapter09UnconditionalInfiniteDegreeExponent
    (T α₀ : ℝ) : ℝ :=
  chapter09EulerMascheroni + Real.log (8 * Real.pi) +
      α₀ * (Real.pi / 2) - chapter09BT T - α₀ * chapter09CT T

def chapter09GRHInfiniteDegreeExponent
    (T α₀ : ℝ) : ℝ :=
  chapter09EulerMascheroni + Real.log (8 * Real.pi) +
      α₀ * (Real.pi / 2) - chapter09GRHBT T - α₀ * chapter09GRHCT T

structure chapter09ThresholdCertificate (U α₀ : ℝ) where
  T : ℚ
  T_pos : 0 < (T : ℝ)
  infinite_degree_gap :
    Real.log U < chapter09UnconditionalInfiniteDegreeExponent (T : ℝ) α₀
  N : ℕ
  N_pos : 0 < N
  pole_gap :
    2 * (T : ℝ) / (N : ℝ) <
      chapter09UnconditionalInfiniteDegreeExponent (T : ℝ) α₀ - Real.log U

theorem chapter09_threshold_certificate_exists
    {U α₀ : ℝ} (hUpos : 0 < U)
    (hU : U < chapter09UnconditionalAsymptoticConstant α₀) :
    Nonempty (chapter09ThresholdCertificate U α₀) := by
  sorry

noncomputable def chapter09Threshold (U α₀ : ℝ) : ℕ :=
  if hUpos : 0 < U then
    if hU : U < chapter09UnconditionalAsymptoticConstant α₀ then
      (Classical.choice
        (chapter09_threshold_certificate_exists hUpos hU)).N
    else 0
  else 0

theorem chapter09_threshold_principle
    {U α₀ : ℝ}
    (hUpos : 0 < U)
    (hU : U < chapter09UnconditionalAsymptoticConstant α₀) :
    ∀ (K : Type*) [Field K] [NumberField K],
      chapter09RootDiscriminant K ≤ U →
      α₀ ≤ chapter09RealProportion K →
      chapter09Degree K < chapter09Threshold U α₀ := by
  sorry

structure chapter09GRHThresholdCertificate (U α₀ : ℝ) where
  T : ℚ
  T_pos : 0 < (T : ℝ)
  infinite_degree_gap :
    Real.log U < chapter09GRHInfiniteDegreeExponent (T : ℝ) α₀
  N : ℕ
  N_pos : 0 < N
  pole_gap :
    4 * chapter09GRHPoleIntegral (T : ℝ) / (N : ℝ) <
      chapter09GRHInfiniteDegreeExponent (T : ℝ) α₀ - Real.log U

theorem chapter09_grh_threshold_certificate_exists
    {U α₀ : ℝ} (hUpos : 0 < U)
    (hU : U < chapter09GRHAsymptoticConstant α₀) :
    Nonempty (chapter09GRHThresholdCertificate U α₀) := by
  sorry

noncomputable def chapter09GRHThreshold (U α₀ : ℝ) : ℕ :=
  if hUpos : 0 < U then
    if hU : U < chapter09GRHAsymptoticConstant α₀ then
      (Classical.choice
        (chapter09_grh_threshold_certificate_exists hUpos hU)).N
    else 0
  else 0

theorem chapter09_grh_threshold_principle
    {U α₀ : ℝ}
    (hUpos : 0 < U)
    (hU : U < chapter09GRHAsymptoticConstant α₀) :
    ∀ (K : Type*) [Field K] [NumberField K]
      [Chapter09ZetaZeroInterface K],
      chapter09GRH K →
      chapter09RootDiscriminant K ≤ U →
      α₀ ≤ chapter09RealProportion K →
      chapter09Degree K < chapter09GRHThreshold U α₀ := by
  sorry

def chapter09StrictUnconditionalThresholdCondition
    (U α₀ : ℝ) : Prop :=
  0 < U ∧ U < chapter09UnconditionalAsymptoticConstant α₀

def chapter09StrictGRHThresholdCondition (U α₀ : ℝ) : Prop :=
  0 < U ∧ U < chapter09GRHAsymptoticConstant α₀

theorem chapter09_unconditional_equality_is_not_strict_threshold
    (α₀ : ℝ) :
    ¬ chapter09StrictUnconditionalThresholdCondition
      (chapter09UnconditionalAsymptoticConstant α₀) α₀ := by
  intro h
  exact (lt_irrefl _ h.2)

theorem chapter09_grh_equality_is_not_strict_threshold
    (α₀ : ℝ) :
    ¬ chapter09StrictGRHThresholdCondition
      (chapter09GRHAsymptoticConstant α₀) α₀ := by
  intro h
  exact (lt_irrefl _ h.2)

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter09
