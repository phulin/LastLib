import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter12.Section01IntermediateSignatures

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter12

open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08
open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11
open Set
open scoped BigOperators

noncomputable section

/-! ## 12.2. Finite rational searches -/

/- LOCAL_DEPENDENCY_GUESS: Chapter 10 supplies directed rational enclosures
   for the two archimedean losses at each rational support.  This structure
   records only those inequalities and leaves the numerical construction to
   the Chapter 10 draft. -/
structure Chapter12ArchimedeanEnclosure (T : ℚ) where
  B_lower : ℝ
  B_upper : ℝ
  C_lower : ℝ
  C_upper : ℝ
  B_lower_le : B_lower ≤ chapter11B (T : ℝ)
  B_le_upper : chapter11B (T : ℝ) ≤ B_upper
  C_lower_le : C_lower ≤ chapter11C (T : ℝ)
  C_le_upper : chapter11C (T : ℝ) ≤ C_upper

def chapter12DirectedLowerEndpoint
    (n : ℕ) (T α B_upper C_upper : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (8 * Real.pi) -
    2 * T / (n : ℝ) - B_upper +
      α * (Real.pi / 2 - C_upper)

def chapter12CertifiedLowerEndpoint
    (n : ℕ) (α : ℝ) {T : ℚ}
    (E : Chapter12ArchimedeanEnclosure T) : ℝ :=
  chapter12DirectedLowerEndpoint n (T : ℝ) α E.B_upper E.C_upper

theorem chapter12_directed_lower_endpoint_le_affine
    {n : ℕ} {T : ℚ} {α : ℝ}
    (hα : 0 ≤ α) (E : Chapter12ArchimedeanEnclosure T) :
    chapter12CertifiedLowerEndpoint n α E ≤
      chapter12AffineLogExpression n (T : ℝ) α := by
  sorry

def chapter12ExactUnconditionalB (T : ℝ) : ℝ :=
  chapter08BT T

def chapter12ExactUnconditionalC (T : ℝ) : ℝ :=
  chapter08CT T

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

/- SOURCE_ISSUE (books/007-analytic-foundations-for-odlyzko-poitou-bounds.md:§12.2):
   “Choose a rational grid of supports” omits the positivity needed for the
   support parameter in the test-function and explicit-formula statements.
   `Chapter12RationalSupportSearch.positive_support` supplies the minimal
   direct correction for the finite grid. -/

theorem chapter12_rational_support_grid_nonempty
    (a h : ℚ) (M : ℕ) :
    (chapter12RationalSupportGrid a h M).Nonempty := by
  sorry

theorem chapter12_mem_rational_support_grid_iff
    {a h T : ℚ} {M : ℕ} :
    T ∈ chapter12RationalSupportGrid a h M ↔
      ∃ j ∈ Finset.range (M + 1), T = a + (j : ℚ) * h := by
  sorry

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
  sorry

theorem chapter12_search_maximum_certified
    {n : ℕ} {a h : ℚ} {M : ℕ} {α : ℝ}
    (S : Chapter12RationalSupportSearch n a h M α) :
    ∃ T : ℚ, T ∈ chapter12RationalSupportGrid a h M ∧
      chapter12SearchMaximum S = chapter12SearchEndpoint S T ∧
      chapter12SearchMaximum S ≤
        chapter12AffineLogExpression n (T : ℝ) α := by
  sorry

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
  sorry

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
        0 ≤ ((enclosure J hJ).upper : ℝ))

def chapter12SupportObjective (n : ℕ) (α T : ℝ) : ℝ :=
  chapter12AffineLogExpression n T α

def chapter12SupportDerivative (n : ℕ) (α T : ℝ) : ℝ :=
  deriv (chapter12SupportObjective n α) T

theorem chapter12_derivative_audit_certifies_sign_partition
    {f f' : ℝ → ℝ} {I : Chapter12RationalInterval}
    (A : Chapter12FiniteDerivativeAudit f f' I)
    {J : Chapter12RationalInterval} (hJ : J ∈ A.intervals) :
    0 < ((A.enclosure J hJ).lower : ℝ) ∨
      ((A.enclosure J hJ).upper : ℝ) < 0 ∨
      (((A.enclosure J hJ).lower : ℝ) ≤ 0 ∧
        0 ≤ ((A.enclosure J hJ).upper : ℝ)) := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter12
