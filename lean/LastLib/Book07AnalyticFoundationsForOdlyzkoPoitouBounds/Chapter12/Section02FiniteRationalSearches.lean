import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter12.Section01IntermediateSignatures

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter12

open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08
open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11
open Set
open scoped BigOperators

noncomputable section

/-! ## 12.2. Finite rational searches -/

/- Chapter 10 supplies directed rational enclosures for the two archimedean
   losses at each rational support.  This structure records the corresponding
   inequalities; the numerical construction remains in Chapter 10. -/
structure Chapter12ArchimedeanEnclosure (T : ℚ) where
  B_lower : ℚ
  B_upper : ℚ
  C_lower : ℚ
  C_upper : ℚ
  B_lower_le : (B_lower : ℝ) ≤ chapter11B (T : ℝ)
  B_le_upper : chapter11B (T : ℝ) ≤ (B_upper : ℝ)
  C_lower_le : (C_lower : ℝ) ≤ chapter11C (T : ℝ)
  C_le_upper : chapter11C (T : ℝ) ≤ (C_upper : ℝ)

def chapter12DirectedLowerEndpoint
    (n : ℕ) (T α B_upper C_upper : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (8 * Real.pi) -
    2 * T / (n : ℝ) - B_upper +
      α * (Real.pi / 2 - C_upper)

def chapter12CertifiedLowerEndpoint
    (n : ℕ) (α : ℝ) {T : ℚ}
    (E : Chapter12ArchimedeanEnclosure T) : ℝ :=
  chapter12DirectedLowerEndpoint n (T : ℝ) α
    (E.B_upper : ℝ) (E.C_upper : ℝ)

theorem chapter12_directed_lower_endpoint_le_affine
    {n : ℕ} {T : ℚ} {α : ℝ}
    (hα : 0 ≤ α) (E : Chapter12ArchimedeanEnclosure T) :
    chapter12CertifiedLowerEndpoint n α E ≤
      chapter12AffineLogExpression n (T : ℝ) α := by
  dsimp [chapter12CertifiedLowerEndpoint, chapter12DirectedLowerEndpoint,
    chapter12AffineLogExpression, chapter12AffineLogBase, chapter12AffineLogSlope]
  have hB : 0 ≤ (E.B_upper : ℝ) - chapter11B (T : ℝ) :=
    sub_nonneg.mpr E.B_le_upper
  have hC : 0 ≤ (E.C_upper : ℝ) - chapter11C (T : ℝ) :=
    sub_nonneg.mpr E.C_le_upper
  have hαC : 0 ≤ α * ((E.C_upper : ℝ) - chapter11C (T : ℝ)) :=
    mul_nonneg hα hC
  linarith

def chapter12ExactUnconditionalB (T : ℝ) : ℝ :=
  chapter08BT T

def chapter12ExactUnconditionalC (T : ℝ) : ℝ :=
  chapter08CT T

/- The exact Chapter 8 losses and the Chapter 11 wrappers denote the same
   functions.  These bridges let the finite-formula and affine-search APIs
   be used interchangeably. -/
theorem chapter12_exact_unconditional_B_eq_chapter11 (T : ℝ) :
    chapter12ExactUnconditionalB T = chapter11B T := by
  rw [chapter11_B_eq_chapter10_BT]
  rfl

theorem chapter12_exact_unconditional_C_eq_chapter11 (T : ℝ) :
    chapter12ExactUnconditionalC T = chapter11C T := by
  rw [chapter11_C_eq_chapter10_CT]
  rfl

def chapter12ExactSupportObjective (n : ℕ) (α T : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (8 * Real.pi) -
    2 * T / (n : ℝ) - chapter12ExactUnconditionalB T +
      α * (Real.pi / 2 - chapter12ExactUnconditionalC T)

def chapter12ExactSupportDerivative (n : ℕ) (α T : ℝ) : ℝ :=
  deriv (chapter12ExactSupportObjective n α) T

theorem chapter12_exact_unconditional_B_formula
    {T : ℝ} (hT : 0 < T) :
    chapter12ExactUnconditionalB T =
      Real.log 2 + Real.pi ^ 2 / (4 * T) +
        Real.log (chapter08Coth (T / 2)) -
        (2 / T) * (∑' k : ℕ, chapter08BSeriesTerm T k) := by
  exact chapter08_B_exact_formula hT

theorem chapter12_exact_unconditional_C_formula
    {T : ℝ} (hT : 0 < T) :
    chapter12ExactUnconditionalC T =
      Real.pi / 2 - (2 / T) * Real.log (Real.cosh (T / 2)) := by
  exact chapter08_C_exact_formula hT

def chapter12RationalSupportGrid (a h : ℚ) (M : ℕ) : Finset ℚ :=
  (Finset.range (M + 1)).image (fun j : ℕ => a + (j : ℚ) * h)

/- The search structure records positivity for every grid support, so downstream
   test-function applications receive their required positive-support hypotheses. -/

theorem chapter12_rational_support_grid_nonempty
    (a h : ℚ) (M : ℕ) :
    (chapter12RationalSupportGrid a h M).Nonempty := by
  classical
  refine ⟨a, ?_⟩
  unfold chapter12RationalSupportGrid
  exact Finset.mem_image.mpr ⟨0, by simp, by simp⟩

theorem chapter12_mem_rational_support_grid_iff
    {a h T : ℚ} {M : ℕ} :
    T ∈ chapter12RationalSupportGrid a h M ↔
      ∃ j ∈ Finset.range (M + 1), T = a + (j : ℚ) * h := by
  classical
  simp [chapter12RationalSupportGrid, eq_comm]

theorem chapter12_rational_support_grid_positive
    {a h T : ℚ} {M : ℕ} (ha : 0 < a) (hh : 0 ≤ h)
    (hT : T ∈ chapter12RationalSupportGrid a h M) :
    0 < (T : ℝ) := by
  rcases (chapter12_mem_rational_support_grid_iff.mp hT) with ⟨j, hj, rfl⟩
  have ha' : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hh' : (0 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hj' : (0 : ℝ) ≤ (j : ℝ) := by positivity
  norm_num
  exact add_pos_of_pos_of_nonneg ha' (mul_nonneg hj' hh')

structure Chapter12RationalSupportSearch
    (n : ℕ) (a h : ℚ) (M : ℕ) (α : ℝ) where
  degree_pos : 0 < n
  enclosure : ∀ T : ℚ,
    T ∈ chapter12RationalSupportGrid a h M → Chapter12ArchimedeanEnclosure T
  positive_support : ∀ T : ℚ,
    T ∈ chapter12RationalSupportGrid a h M → 0 < (T : ℝ)
  nonnegative_signature : 0 ≤ α

noncomputable def chapter12SearchEndpoint
    {n : ℕ} {a h : ℚ} {M : ℕ} {α : ℝ}
    (S : Chapter12RationalSupportSearch n a h M α) (T : ℚ) : ℝ :=
  if hT : T ∈ chapter12RationalSupportGrid a h M then
    chapter12CertifiedLowerEndpoint n α (S.enclosure T hT)
  else 0

noncomputable def chapter12SearchMaximum
    {n : ℕ} {a h : ℚ} {M : ℕ} {α : ℝ}
    (S : Chapter12RationalSupportSearch n a h M α) : ℝ :=
  (chapter12RationalSupportGrid a h M).sup'
    (chapter12_rational_support_grid_nonempty a h M)
    (chapter12SearchEndpoint S)

theorem chapter12_search_endpoint_eq_certified
    {n : ℕ} {a h : ℚ} {M : ℕ} {α : ℝ}
    (S : Chapter12RationalSupportSearch n a h M α)
    {T : ℚ} (hT : T ∈ chapter12RationalSupportGrid a h M) :
    chapter12SearchEndpoint S T =
      chapter12CertifiedLowerEndpoint n α (S.enclosure T hT) := by
  simp [chapter12SearchEndpoint, hT]

theorem chapter12_search_endpoint_certified
    {n : ℕ} {a h : ℚ} {M : ℕ} {α : ℝ}
    (S : Chapter12RationalSupportSearch n a h M α)
    {T : ℚ} (hT : T ∈ chapter12RationalSupportGrid a h M) :
    chapter12SearchEndpoint S T ≤
      chapter12AffineLogExpression n (T : ℝ) α := by
  rw [chapter12_search_endpoint_eq_certified S hT]
  exact chapter12_directed_lower_endpoint_le_affine
    S.nonnegative_signature (S.enclosure T hT)

theorem chapter12_search_maximum_attained
    {n : ℕ} {a h : ℚ} {M : ℕ} {α : ℝ}
    (S : Chapter12RationalSupportSearch n a h M α) :
    ∃ T : ℚ, T ∈ chapter12RationalSupportGrid a h M ∧
      chapter12SearchMaximum S = chapter12SearchEndpoint S T := by
  rcases Finset.exists_mem_eq_sup'
      (chapter12SearchEndpoint S)
      (s := chapter12RationalSupportGrid a h M)
      (H := chapter12_rational_support_grid_nonempty a h M) with ⟨T, hT, hmax⟩
  refine ⟨T, hT, ?_⟩
  simpa [chapter12SearchMaximum] using hmax

theorem chapter12_search_maximum_certified
    {n : ℕ} {a h : ℚ} {M : ℕ} {α : ℝ}
    (S : Chapter12RationalSupportSearch n a h M α) :
    ∃ T : ℚ, T ∈ chapter12RationalSupportGrid a h M ∧
      chapter12SearchMaximum S = chapter12SearchEndpoint S T ∧
      chapter12SearchMaximum S ≤
        chapter12AffineLogExpression n (T : ℝ) α := by
  rcases chapter12_search_maximum_attained S with ⟨T, hT, hmax⟩
  refine ⟨T, hT, hmax, ?_⟩
  rw [hmax]
  exact chapter12_search_endpoint_certified S hT

def chapter12SuccessfulRationalSupport
    {n : ℕ} {a h : ℚ} {M : ℕ} {α U : ℝ}
    (S : Chapter12RationalSupportSearch n a h M α) : Prop :=
  ∃ T : ℚ, T ∈ chapter12RationalSupportGrid a h M ∧
    Real.log U < chapter12SearchEndpoint S T

theorem chapter12_successful_support_iff_maximum_success
    {n : ℕ} {a h : ℚ} {M : ℕ} {α U : ℝ}
    (S : Chapter12RationalSupportSearch n a h M α) :
    chapter12SuccessfulRationalSupport (U := U) S ↔
      Real.log U < chapter12SearchMaximum S := by
  constructor
  · rintro ⟨T, hT, hsuccess⟩
    have hle := Finset.le_sup'
      (s := chapter12RationalSupportGrid a h M)
      (f := chapter12SearchEndpoint S) hT
    change chapter12SearchEndpoint S T ≤ chapter12SearchMaximum S at hle
    exact lt_of_lt_of_le hsuccess hle
  · intro hsuccess
    rcases chapter12_search_maximum_attained S with ⟨T, hT, hmax⟩
    refine ⟨T, hT, ?_⟩
    rwa [← hmax]

theorem chapter12_one_successful_support_is_enough
    {n : ℕ} {a h : ℚ} {M : ℕ} {α U : ℝ}
    (S : Chapter12RationalSupportSearch n a h M α)
    {T : ℚ} (hT : T ∈ chapter12RationalSupportGrid a h M)
    (hsuccess : Real.log U < chapter12SearchEndpoint S T) :
    Real.log U < chapter12AffineLogExpression n (T : ℝ) α := by
  exact hsuccess.trans_le (chapter12_search_endpoint_certified S hT)

structure Chapter12RationalInterval where
  lower : ℚ
  upper : ℚ
  lower_le_upper : lower ≤ upper
  deriving DecidableEq

def chapter12RealInterval (I : Chapter12RationalInterval) : Set ℝ :=
  Set.Icc (I.lower : ℝ) (I.upper : ℝ)

structure Chapter12DerivativeEnclosure
    (f f' : ℝ → ℝ) (I : Chapter12RationalInterval) where
  lower : ℚ
  upper : ℚ
  lower_le_upper : lower ≤ upper
  lower_bound : ∀ x ∈ chapter12RealInterval I, (lower : ℝ) ≤ f' x
  upper_bound : ∀ x ∈ chapter12RealInterval I, f' x ≤ (upper : ℝ)

def chapter12DerivativePositiveOnInterval
    {f f' : ℝ → ℝ} {I : Chapter12RationalInterval}
    (E : Chapter12DerivativeEnclosure f f' I) : Prop :=
  0 < (E.lower : ℝ)

def chapter12DerivativeNegativeOnInterval
    {f f' : ℝ → ℝ} {I : Chapter12RationalInterval}
    (E : Chapter12DerivativeEnclosure f f' I) : Prop :=
  (E.upper : ℝ) < 0

structure Chapter12FiniteDerivativeAudit
    (f f' : ℝ → ℝ) (I : Chapter12RationalInterval) where
  intervals : Finset Chapter12RationalInterval
  subinterval : ∀ J ∈ intervals,
    chapter12RealInterval J ⊆ chapter12RealInterval I
  cover : ∀ x ∈ chapter12RealInterval I,
    ∃ J ∈ intervals, x ∈ chapter12RealInterval J
  enclosure : ∀ J ∈ intervals,
    Chapter12DerivativeEnclosure f f' J
  derivative : ∀ (J : Chapter12RationalInterval) (_hJ : J ∈ intervals)
      (x : ℝ), x ∈ chapter12RealInterval J → HasDerivAt f (f' x) x
  sign_partition : ∀ (J : Chapter12RationalInterval) (hJ : J ∈ intervals),
    0 < ((enclosure J hJ).lower : ℝ) ∨
      ((enclosure J hJ).upper : ℝ) < 0 ∨
      (((enclosure J hJ).lower : ℝ) ≤ 0 ∧
        0 ≤ ((enclosure J hJ).upper : ℝ) ∧
        ∃ x ∈ chapter12RealInterval J, f' x = 0)

theorem chapter12_derivative_audit_positive_derivative
    {f f' : ℝ → ℝ} {I : Chapter12RationalInterval}
    (A : Chapter12FiniteDerivativeAudit f f' I)
    {J : Chapter12RationalInterval} (hJ : J ∈ A.intervals)
    (hpositive : chapter12DerivativePositiveOnInterval (A.enclosure J hJ)) :
    ∀ x ∈ chapter12RealInterval J, 0 < f' x := by
  intro x hx
  exact lt_of_lt_of_le hpositive ((A.enclosure J hJ).lower_bound x hx)

theorem chapter12_derivative_audit_negative_derivative
    {f f' : ℝ → ℝ} {I : Chapter12RationalInterval}
    (A : Chapter12FiniteDerivativeAudit f f' I)
    {J : Chapter12RationalInterval} (hJ : J ∈ A.intervals)
    (hnegative : chapter12DerivativeNegativeOnInterval (A.enclosure J hJ)) :
    ∀ x ∈ chapter12RealInterval J, f' x < 0 := by
  intro x hx
  exact lt_of_le_of_lt ((A.enclosure J hJ).upper_bound x hx) hnegative

def chapter12SupportObjective (n : ℕ) (α T : ℝ) : ℝ :=
  chapter12AffineLogExpression n T α

theorem chapter12_support_objective_eq_exact_support_objective
    (n : ℕ) (α T : ℝ) :
    chapter12SupportObjective n α T = chapter12ExactSupportObjective n α T := by
  rw [chapter12ExactSupportObjective, chapter12SupportObjective]
  rw [chapter12_affine_log_expression_formula]
  rw [chapter12_exact_unconditional_B_eq_chapter11,
    chapter12_exact_unconditional_C_eq_chapter11]

def chapter12SupportDerivative (n : ℕ) (α T : ℝ) : ℝ :=
  deriv (chapter12SupportObjective n α) T

theorem chapter12_support_derivative_eq_exact_support_derivative
    (n : ℕ) (α T : ℝ) :
    chapter12SupportDerivative n α T = chapter12ExactSupportDerivative n α T := by
  unfold chapter12SupportDerivative chapter12ExactSupportDerivative
  rw [show chapter12SupportObjective n α = chapter12ExactSupportObjective n α by
    funext x
    exact chapter12_support_objective_eq_exact_support_objective n α x]

theorem chapter12_derivative_audit_certifies_sign_partition
    {f f' : ℝ → ℝ} {I : Chapter12RationalInterval}
    (A : Chapter12FiniteDerivativeAudit f f' I)
    {J : Chapter12RationalInterval} (hJ : J ∈ A.intervals) :
    0 < ((A.enclosure J hJ).lower : ℝ) ∨
      ((A.enclosure J hJ).upper : ℝ) < 0 ∨
      (((A.enclosure J hJ).lower : ℝ) ≤ 0 ∧
        0 ≤ ((A.enclosure J hJ).upper : ℝ) ∧
        ∃ x ∈ chapter12RealInterval J, f' x = 0) := by
  exact A.sign_partition J hJ

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter12
