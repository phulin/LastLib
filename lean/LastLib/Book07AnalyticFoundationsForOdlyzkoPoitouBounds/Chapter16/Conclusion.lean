import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter16.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter16

noncomputable section

open MeasureTheory
open NumberField
open scoped BigOperators NumberField Classical
open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter01
open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter02
open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03
open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05
open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter07
open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08
open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter09
open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11
open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter13

/-! ## 16. Conclusion -/

/-!
### The discriminant scale and the earlier analytic interfaces

The conclusion is a synthesis rather than a second proof of the preceding
chapters.  These book-facing names keep the canonical degree, signature,
root-discriminant, lattice, and tower interfaces available at the point where
the source summarizes them.
-/

abbrev chapter16Degree (K : Type*) [Field K] [NumberField K] : ℕ :=
  Module.finrank ℚ K

abbrev chapter16RealPlaceCount (K : Type*) [Field K] [NumberField K] : ℕ :=
  NumberField.InfinitePlace.nrRealPlaces K

abbrev chapter16ComplexPlaceCount (K : Type*) [Field K] [NumberField K] : ℕ :=
  NumberField.InfinitePlace.nrComplexPlaces K

abbrev chapter16AbsoluteDiscriminant (K : Type*) [Field K] [NumberField K] : ℝ :=
  chapter02AbsoluteDiscriminant K

abbrev chapter16RootDiscriminant (K : Type*) [Field K] [NumberField K] : ℝ :=
  NumberField.rootDiscr K

def chapter16RealProportion
    (K : Type*) [Field K] [NumberField K] : ℝ :=
  (chapter16RealPlaceCount K : ℝ) / (chapter16Degree K : ℝ)

theorem chapter16_degree_signature_identity
    (K : Type*) [Field K] [NumberField K] :
    chapter16Degree K =
      chapter16RealPlaceCount K + 2 * chapter16ComplexPlaceCount K := by
  sorry

theorem chapter16_real_proportion_mem_Icc
    (K : Type*) [Field K] [NumberField K] :
    chapter16RealProportion K ∈ Set.Icc (0 : ℝ) 1 := by
  sorry

theorem chapter16_degree_eq_chapter09
    (K : Type*) [Field K] [NumberField K] :
    chapter16Degree K = chapter09Degree K :=
  rfl

theorem chapter16_real_proportion_eq_chapter09
    (K : Type*) [Field K] [NumberField K] :
    chapter16RealProportion K = chapter09RealProportion K := by
  rfl

/- LOCAL_DEPENDENCY_GUESS: the Chapter 9 real-power presentation of the
root discriminant must be identified with Mathlib's canonical
`NumberField.rootDiscr` presentation during reconciliation. -/
theorem chapter16_root_discriminant_eq_chapter09
    (K : Type*) [Field K] [NumberField K] :
    chapter16RootDiscriminant K = chapter09RootDiscriminant K := by
  sorry

abbrev chapter16MinkowskiSpace (K : Type*) [Field K] [NumberField K] :=
  chapter02MinkowskiSpace K

abbrev chapter16IntegerLattice (K : Type*) [Field K] [NumberField K] :=
  chapter02IntegerLattice K

theorem chapter16_integer_lattice_covolume
    (K : Type*) [Field K] [NumberField K] :
    ZLattice.covolume (E := chapter16MinkowskiSpace K)
        (chapter16IntegerLattice K) =
      (2 : ℝ)⁻¹ ^ chapter16ComplexPlaceCount K *
        Real.sqrt (chapter16AbsoluteDiscriminant K) := by
  exact chapter02_integer_lattice_covolume K

/- LOCAL_DEPENDENCY_GUESS: this conclusion reuses the Chapter 13 relative
different normalization until the earlier tower API is reconciled with the
canonical Mathlib discriminant identity. -/
/- The finite ramification contribution is the relative different factor in
the canonical tower identity. -/
theorem chapter16_root_discriminant_tower_formula
    (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L] [Module.Finite (𝓞 F) (𝓞 L)] :
    chapter16RootDiscriminant L =
      chapter16RootDiscriminant F *
        chapter13RelativeDifferentContribution F L := by
  sorry

/- The Euler product/logarithmic derivative exposes nonnegative prime-power
weights once the test function is pointwise nonnegative. -/
theorem chapter16_euler_prime_power_term_nonnegative
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : ∀ x, 0 ≤ F x) (q : Chapter03PrimePower K) :
    0 ≤ chapter03WeightedPrimePowerTerm F q := by
  exact chapter03_weighted_prime_power_term_nonneg K hF q

theorem chapter16_euler_prime_power_sum_nonnegative
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : ∀ x, 0 ≤ F x) (S : Finset (Chapter03PrimePower K)) :
    0 ≤ ∑ q ∈ S, chapter03WeightedPrimePowerTerm F q := by
  exact chapter03_weighted_prime_power_sum_nonneg K hF S

/- The gamma contribution is recorded by the real-place proportion, while the
pole contribution is the finite-degree deficit in the explicit formula. -/
def chapter16GammaSignatureTerm
    (K : Type*) [Field K] [NumberField K] : ℝ :=
  chapter16RealProportion K * (Real.pi / 2)

def chapter16PoleDegreeCost (A : ℝ) (n : ℕ) : ℝ :=
  4 * A / (n : ℝ)

theorem chapter16_gamma_signature_term_eq
    (K : Type*) [Field K] [NumberField K] :
    chapter16GammaSignatureTerm K =
      chapter16RealProportion K * (Real.pi / 2) :=
  rfl

theorem chapter16_pole_degree_cost_eq (A : ℝ) (n : ℕ) :
    chapter16PoleDegreeCost A n = 4 * A / (n : ℝ) :=
  rfl

/- The functional-equation involution is the zero reflection used by the
unconditional symmetric-pair argument. -/
theorem chapter16_zero_functional_equation_partner
    (Z : Chapter07ZeroSpectrum) (ρ : ℂ) :
    ρ ∈ Z.support ↔ chapter07ZeroPartner ρ ∈ Z.support := by
  exact Z.functional_equation_partner

/- The central-line Fourier statement is kept in the earlier admissibility
interface, with the hypotheses needed to make its order assertion meaningful. -/
theorem chapter16_grh_central_line_fourier_nonnegative
    {F : ℝ → ℝ} (hF : Chapter05GRHAdmissible F) (t : ℝ) :
    (chapter05BilateralLaplaceTransform F
        ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).im = 0 ∧
      0 ≤ (chapter05BilateralLaplaceTransform F
        ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re := by
  exact chapter05_grh_admissible_central_line_nonnegative hF t

theorem chapter16_grh_fourier_positivity_controls_zero_summand
    (Z : Chapter07ZeroSpectrum) (f : Chapter07TestFunction)
    (hgrh : chapter07GRH Z) (hf : chapter07GRHAdmissible f)
    {ρ : ℂ} (hρ : ρ ∈ Z.support) :
    0 ≤ (chapter07ZeroTermSummand Z f ρ).re := by
  exact chapter07_grh_zero_summand_nonnegative Z f hgrh hf hρ

theorem chapter16_grh_fourier_positivity_controls_zero_term
    (Z : Chapter07ZeroSpectrum) (f : Chapter07TestFunction)
    (hgrh : chapter07GRH Z) (hf : chapter07GRHAdmissible f)
    (hsum : chapter07ZeroTermConvergent Z f) :
    0 ≤ chapter07ZeroTerm Z f := by
  exact chapter07_grh_zero_term_nonnegative Z f hgrh hf hsum

abbrev chapter16StripPositiveKernel := chapter07StripKernel
abbrev chapter16PairedZeroContribution := chapter07PairedZeroContribution

theorem chapter16_strip_positive_kernel_formula (a x : ℝ) :
    chapter16StripPositiveKernel a x = Real.cosh (a * x) / Real.cosh (x / 2) :=
  rfl

theorem chapter16_unconditional_strip_kernel_positive_type
    (G : Chapter07TestFunction) (a : ℝ)
    (hG : chapter07PositiveType G) (ha : |a| < 1 / 2) :
    chapter07PositiveType (fun x => G x * chapter16StripPositiveKernel a x) := by
  exact chapter07_pair_kernel_positiveType_strict G a hG ha

theorem chapter16_unconditional_symmetric_zero_pair_nonnegative
    (G : Chapter07TestFunction) (β γ : ℝ)
    (hG_integrable : Integrable G) (hG_even : chapter07Even G)
    (hG_positive : chapter07PositiveType G)
    (hβ : |β - 1 / 2| ≤ 1 / 2) :
    0 ≤ chapter16PairedZeroContribution G β γ := by
  exact chapter07_paired_zero_contribution_nonnegative
    G β γ hG_integrable hG_even hG_positive hβ

theorem chapter16_unconditional_fourier_positivity_controls_zero_term
    (Z : Chapter07ZeroSpectrum) (G : Chapter07TestFunction)
    (hG_integrable : Integrable G) (hG_even : chapter07Even G)
    (hG_positive : chapter07PositiveType G)
    (hsum : chapter07ZeroTermConvergent Z (chapter07FOfG G)) :
    0 ≤ chapter07ZeroTerm Z (chapter07FOfG G) := by
  exact chapter07_unconditional_zero_term_nonnegative
    Z G hG_integrable hG_even hG_positive hsum

abbrev Chapter16ExplicitFormulaData
    (K : Type*) [Field K] [NumberField K] (F : ℝ → ℝ) :=
  Chapter08ExplicitFormulaData K F

theorem chapter16_explicit_formula_balance_is_exact
    (K : Type*) [Field K] [NumberField K] (F : ℝ → ℝ)
    (D : Chapter16ExplicitFormulaData K F) :
    Real.log (Chapter08AbsoluteDiscriminant K) =
      (Chapter08Degree K : ℝ) *
          (Real.eulerMascheroniConstant + Real.log (8 * Real.pi)) +
        (Chapter08RealPlaceCount K : ℝ) * (Real.pi / 2) -
        4 * chapter08A F -
        (Chapter08Degree K : ℝ) * chapter08B F -
        (Chapter08RealPlaceCount K : ℝ) * chapter08C F +
        D.zeroContribution + D.primeContribution := by
  exact D.identity

/-!
### Asymptotic constants and finite-support certificates

The two constants are defined directly in the conclusion's normalization.
The endpoint and threshold theorems below bridge to the earlier universal
inequality and finite-ledger declarations.
-/

def chapter16UnconditionalAsymptoticConstant (α₀ : ℝ) : ℝ :=
  4 * Real.pi * Real.exp (Real.eulerMascheroniConstant + α₀)

def chapter16GRHAsymptoticConstant (α₀ : ℝ) : ℝ :=
  8 * Real.pi * Real.exp
    (Real.eulerMascheroniConstant + α₀ * (Real.pi / 2))

theorem chapter16_unconditional_asymptotic_constant_eq_chapter09
    (α₀ : ℝ) :
    chapter16UnconditionalAsymptoticConstant α₀ =
      chapter09UnconditionalAsymptoticConstant α₀ := by
  rfl

theorem chapter16_grh_asymptotic_constant_eq_chapter09
    (α₀ : ℝ) :
    chapter16GRHAsymptoticConstant α₀ =
      chapter09GRHAsymptoticConstant α₀ := by
  rfl

theorem chapter16_unconditional_endpoint_ledger :
    chapter16UnconditionalAsymptoticConstant 0 =
        4 * Real.pi * Real.exp Real.eulerMascheroniConstant ∧
      chapter16UnconditionalAsymptoticConstant 1 =
        4 * Real.pi * Real.exp (1 + Real.eulerMascheroniConstant) := by
  sorry

theorem chapter16_grh_endpoint_ledger :
    chapter16GRHAsymptoticConstant 0 =
        8 * Real.pi * Real.exp Real.eulerMascheroniConstant ∧
      chapter16GRHAsymptoticConstant 1 =
        8 * Real.pi * Real.exp
          (Real.eulerMascheroniConstant + Real.pi / 2) := by
  sorry

theorem chapter16_unconditional_asymptotic_threshold_principle
    {U α₀ : ℝ}
    (hU : U < chapter16UnconditionalAsymptoticConstant α₀) :
    ∀ (K : Type*) [Field K] [NumberField K],
      chapter09RootDiscriminant K ≤ U →
      α₀ ≤ chapter09RealProportion K →
      chapter09Degree K < chapter09Threshold U α₀ := by
  simpa [chapter16UnconditionalAsymptoticConstant,
    chapter09UnconditionalAsymptoticConstant] using
    (chapter09_threshold_principle (U := U) (α₀ := α₀) (by
      simpa [chapter16UnconditionalAsymptoticConstant,
        chapter09UnconditionalAsymptoticConstant] using hU))

theorem chapter16_unconditional_asymptotic_threshold_principle_canonical
    {U α₀ : ℝ}
    (hU : U < chapter16UnconditionalAsymptoticConstant α₀) :
    ∀ (K : Type*) [Field K] [NumberField K],
      chapter16RootDiscriminant K ≤ U →
      α₀ ≤ chapter16RealProportion K →
      chapter16Degree K < chapter09Threshold U α₀ := by
  sorry

theorem chapter16_grh_asymptotic_threshold_principle
    {U α₀ : ℝ}
    (hU : U < chapter16GRHAsymptoticConstant α₀) :
    ∀ (K : Type*) [Field K] [NumberField K]
      [Chapter09ZetaZeroInterface K],
      chapter09GRH K →
      chapter09RootDiscriminant K ≤ U →
      α₀ ≤ chapter09RealProportion K →
      chapter09Degree K < chapter09GRHThreshold U α₀ := by
  simpa [chapter16GRHAsymptoticConstant, chapter09GRHAsymptoticConstant] using
    (chapter09_grh_threshold_principle (U := U) (α₀ := α₀) (by
      simpa [chapter16GRHAsymptoticConstant, chapter09GRHAsymptoticConstant] using hU))

theorem chapter16_grh_asymptotic_threshold_principle_canonical
    {U α₀ : ℝ}
    (hU : U < chapter16GRHAsymptoticConstant α₀) :
    ∀ (K : Type*) [Field K] [NumberField K]
      [Chapter09ZetaZeroInterface K],
      chapter09GRH K →
      chapter16RootDiscriminant K ≤ U →
      α₀ ≤ chapter16RealProportion K →
      chapter16Degree K < chapter09GRHThreshold U α₀ := by
  sorry

noncomputable def chapter16PrimePowerLedger
    (K : Type*) [Field K] [NumberField K] (F : ℝ → ℝ) (T : ℝ)
    (hT : 0 ≤ T) (hF : chapter03SupportWithin F T) :
    Finset (Chapter03PrimePower K) :=
  chapter03PrimePowerLedger K F T hT hF

theorem chapter16_prime_power_ledger_mem_iff
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hF : chapter03SupportWithin F T)
    (q : Chapter03PrimePower K) :
    q ∈ chapter16PrimePowerLedger K F T hT hF ↔
      chapter03WeightedPrimePowerTerm F q ≠ 0 := by
  simpa [chapter16PrimePowerLedger] using
    (chapter03_mem_prime_power_ledger_iff K hT hF q)

theorem chapter16_prime_power_ledger_sum_eq_tsum
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hF : chapter03SupportWithin F T) :
    (∑' q : Chapter03PrimePower K,
        chapter03WeightedPrimePowerTerm F q) =
      ∑ q ∈ chapter16PrimePowerLedger K F T hT hF,
        chapter03WeightedPrimePowerTerm F q := by
  simpa [chapter16PrimePowerLedger] using
    (chapter03_weighted_prime_power_tsum_eq_ledger_sum K hT hF)

abbrev chapter16BT := chapter08BT
abbrev chapter16CT := chapter08CT

theorem chapter16_exact_archimedean_formulas
    {T : ℝ} (hT : 0 < T) :
    chapter08BT T =
        Real.log 2 + Real.pi ^ 2 / (4 * T) +
          Real.log (chapter08Coth (T / 2)) -
          (2 / T) * (∑' k : ℕ, chapter08BSeriesTerm T k) ∧
      chapter08CT T = Real.pi / 2 -
        (2 / T) * Real.log (Real.cosh (T / 2)) := by
  exact ⟨chapter08_B_exact_formula hT, chapter08_C_exact_formula hT⟩

theorem chapter16_archimedean_tail_certificate
    {T : ℝ} (hT : 0 < T) (m : ℕ) :
    0 ≤ chapter08BSeriesTail T m ∧
      chapter08BSeriesTail T m ≤
        (1 + T) * Real.exp (-((2 * m + 3 : ℕ) : ℝ) * T) /
          (1 - Real.exp (-2 * T)) := by
  exact ⟨chapter08_B_series_tail_nonnegative hT m,
    chapter08_B_series_tail_bound hT m⟩

/- Decimal literals in the earlier ledger are exact rational real numbers;
this structure records the intended enclosure interface explicitly. -/
structure Chapter16RationalEnclosure (x : ℝ) where
  lower : ℚ
  upper : ℚ
  lower_lt : (lower : ℝ) < x
  upper_gt : x < (upper : ℝ)

abbrev chapter16ThreeSqrtThreeCeiling : ℝ :=
  chapter11ThreeSqrtThreeCeiling

abbrev chapter16FiveFourthCeiling : ℝ :=
  chapter11FiveFourthCeiling

abbrev chapter16TwoPrimeCeiling : ℝ :=
  chapter11TwoPrimeCeiling

def chapter16_three_sqrt_three_rational_enclosure :
    Chapter16RationalEnclosure chapter16ThreeSqrtThreeCeiling := by
  exact
    { lower := 51961524227 / 10 ^ 10
      upper := 51961524228 / 10 ^ 10
      lower_lt := by sorry
      upper_gt := by sorry }

def chapter16_five_fourth_rational_enclosure :
    Chapter16RationalEnclosure chapter16FiveFourthCeiling := by
  exact
    { lower := 74767439061 / 10 ^ 10
      upper := 74767439062 / 10 ^ 10
      lower_lt := by sorry
      upper_gt := by sorry }

def chapter16_two_prime_rational_enclosure :
    Chapter16RationalEnclosure chapter16TwoPrimeCeiling := by
  exact
    { lower := 8248377821991616 / 10 ^ 15
      upper := 8248377821991617 / 10 ^ 15
      lower_lt := by sorry
      upper_gt := by sorry }

theorem chapter16_archimedean_ledger_certificates :
    (chapter11UnconditionalPoleCost (17 / 5 : ℝ) = 17 / 10 ∧
      1.39921 < chapter11B (17 / 5 : ℝ) ∧
      chapter11B (17 / 5 : ℝ) < 1.39923 ∧
      0.95921 < chapter11C (17 / 5 : ℝ) ∧
      chapter11C (17 / 5 : ℝ) < 0.95923) ∧
    (chapter11UnconditionalPoleCost (9 / 2 : ℝ) = 9 / 4 ∧
      1.23652 < chapter11B (9 / 2 : ℝ) ∧
      chapter11B (9 / 2 : ℝ) < 1.23653 ∧
      0.87395 < chapter11C (9 / 2 : ℝ) ∧
      chapter11C (9 / 2 : ℝ) < 0.87396) ∧
    (chapter11UnconditionalPoleCost 6 = 3 ∧
      1.10355 < chapter11B 6 ∧ chapter11B 6 < 1.10356 ∧
      0.80102 < chapter11C 6 ∧ chapter11C 6 < 0.80103) := by
  exact ⟨chapter11_archimedean_ledger_row_seventeen_over_five,
    chapter11_archimedean_ledger_row_nine_halves,
    chapter11_archimedean_ledger_row_six⟩

/-!
### Certified finite-degree cutoffs

The next declarations preserve both the independent geometric crossing and
the stronger explicit-formula crossing at the two-prime ceiling.  In
particular, the smaller `3^(3/2)` row is not silently identified with the
independent Minkowski cap.
-/

theorem chapter16_threshold_four_degree_cap
    (K : Type*) [Field K] [NumberField K]
    (hceiling : chapter16RootDiscriminant K < 4) :
    chapter16Degree K ≤ 11 := by
  exact chapter11_minkowski_degree_twelve_cutoff K hceiling

theorem chapter16_threshold_four_totally_real_degree_cap
    (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]
    (hceiling : chapter16RootDiscriminant K < 4) :
    chapter16Degree K ≤ 5 := by
  exact chapter11_minkowski_degree_six_totally_real_cutoff K hceiling

theorem chapter16_three_sqrt_three_minkowski_degree_cap
    (K : Type*) [Field K] [NumberField K]
    (hceiling : chapter16RootDiscriminant K < chapter16ThreeSqrtThreeCeiling) :
    chapter16Degree K ≤ 52 := by
  exact chapter11_minkowski_degree_fifty_three_cutoff K hceiling

theorem chapter16_three_sqrt_three_explicit_formula_degree_cap
    (K : Type*) [Field K] [NumberField K]
    (hceiling : chapter16RootDiscriminant K < chapter16ThreeSqrtThreeCeiling) :
    chapter16Degree K ≤ 20 := by
  exact chapter11_three_sqrt_three_explicit_formula_degree_cutoff K hceiling

theorem chapter16_five_fourth_degree_cap
    (K : Type*) [Field K] [NumberField K]
    (hceiling : chapter16RootDiscriminant K < chapter16FiveFourthCeiling) :
    chapter16Degree K ≤ 16 := by
  exact chapter11_five_fourth_degree_cutoff K hceiling

theorem chapter16_two_prime_degree_cap
    (K : Type*) [Field K] [NumberField K]
    (hceiling : chapter16RootDiscriminant K < chapter16TwoPrimeCeiling) :
    chapter16Degree K ≤ 20 := by
  exact chapter11_two_prime_degree_cutoff K hceiling

theorem chapter16_three_sqrt_three_explicit_cap_improves_minkowski_row
    (K : Type*) [Field K] [NumberField K]
    (hceiling : chapter16RootDiscriminant K < chapter16ThreeSqrtThreeCeiling) :
    chapter16Degree K ≤ 20 := by
  exact chapter16_three_sqrt_three_explicit_formula_degree_cap K hceiling

theorem chapter16_three_sqrt_three_totally_real_degree_cap
    (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]
    (hceiling : chapter16RootDiscriminant K < chapter16ThreeSqrtThreeCeiling) :
    chapter16Degree K ≤ 12 := by
  exact chapter11_minkowski_degree_thirteen_totally_real_cutoff K hceiling

theorem chapter16_five_fourth_totally_real_degree_cap
    (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]
    (hceiling : chapter16RootDiscriminant K < chapter16FiveFourthCeiling) :
    chapter16Degree K ≤ 6 := by
  exact chapter11_totally_real_five_fourth_degree_cutoff K hceiling

theorem chapter16_minkowski_never_reaches_five_fourth
    {n : ℕ} (hn : 0 < n) :
    chapter11MinkowskiFactor n < chapter16FiveFourthCeiling := by
  exact chapter11_minkowski_never_crosses_five_fourth hn

/-!
### Uniformity, stabilization, and failure diagnostics

The logical dependency on a uniform strict ceiling and on a certified
signature lower bound is exposed as a small generic bridge.  The finite
compositum interface records the additional arithmetic closure needed for a
directed compositum argument.
-/

def chapter16UniformWeakCeiling
    {ι : Type*} (rootDiscriminant : ι → ℝ) (U : ℝ) : Prop :=
  ∀ i, rootDiscriminant i ≤ U

def chapter16UniformDegreeCap
    {ι : Type*} (degree : ι → ℕ) (N : ℕ) : Prop :=
  ∀ i, degree i < N

def chapter16SignatureLowerBound (α₀ α : ℝ) : Prop :=
  α₀ ≤ α

theorem chapter16_uniform_ceiling_below_threshold_bounds_degree
    {ι : Type*} (rootDiscriminant : ι → ℝ) (degree : ι → ℕ)
    (U V : ℝ) (N : ℕ)
    (hbelow : U < V)
    (hthreshold : ∀ i, rootDiscriminant i < V → degree i < N)
    (hceiling : chapter16UniformWeakCeiling rootDiscriminant U) :
    chapter16UniformDegreeCap degree N := by
  intro i
  exact hthreshold i (lt_of_le_of_lt (hceiling i) hbelow)

theorem chapter16_uniform_ceiling_degree_cap_with_signature
    {ι : Type*} (rootDiscriminant : ι → ℝ) (degree : ι → ℕ)
    (signature : ι → ℝ) (U V α₀ : ℝ) (N : ℕ)
    (hbelow : U < V)
    (hthreshold : ∀ i, rootDiscriminant i < V →
      chapter16SignatureLowerBound α₀ (signature i) → degree i < N)
    (hceiling : chapter16UniformWeakCeiling rootDiscriminant U)
    (hsignature : ∀ i, chapter16SignatureLowerBound α₀ (signature i)) :
    chapter16UniformDegreeCap degree N := by
  intro i
  exact hthreshold i (lt_of_le_of_lt (hceiling i) hbelow) (hsignature i)

theorem chapter16_nested_chain_stabilizes_of_uniform_degree_cap
    (Ω : Type*) [Field Ω] [NumberField Ω]
    (C : Chapter01NestedFieldChain Ω) (N : ℕ)
    (hcap : ∀ i, chapter01NestedFieldChainDegree Ω C i ≤ N) :
    ∃ i₀ : ℕ, ∀ j : ℕ, i₀ ≤ j → C.field j = C.field i₀ := by
  exact chapter01_nested_field_chain_stabilizes Ω C ⟨N, hcap⟩

def chapter16CompositumClosed
    {Ω : Type*} [Field Ω] [NumberField Ω]
    (𝓕 : Set (IntermediateField ℚ Ω)) : Prop :=
  ∀ ⦃E F : IntermediateField ℚ Ω⦄,
    E ∈ 𝓕 → F ∈ 𝓕 → E ⊔ F ∈ 𝓕

def chapter16UniformIntermediateDegreeBound
    {Ω : Type*} [Field Ω] [NumberField Ω]
    (𝓕 : Set (IntermediateField ℚ Ω)) (N : ℕ) : Prop :=
  ∀ E : IntermediateField ℚ Ω, E ∈ 𝓕 → Module.finrank ℚ E ≤ N

/- LOCAL_DEPENDENCY_GUESS: a finite number-field ambient extension has only
finitely many intermediate fields; with closure under `⊔`, the bounded-degree
family therefore has a maximal finite compositum.  This is the exact
field-theoretic seam needed by the source's uniform-compositum warning. -/
theorem chapter16_compositum_closure_stabilizes
    {Ω : Type*} [Field Ω] [NumberField Ω]
    (𝓕 : Set (IntermediateField ℚ Ω))
    (hne : 𝓕.Nonempty)
    (hclosed : chapter16CompositumClosed 𝓕)
    (N : ℕ)
    (hbound : chapter16UniformIntermediateDegreeBound 𝓕 N) :
    ∃ M : IntermediateField ℚ Ω, M ∈ 𝓕 ∧
      ∀ E : IntermediateField ℚ Ω, E ∈ 𝓕 → E ≤ M := by
  sorry

def chapter16GrowingCeiling (c lambda : ℝ) : ℕ → ℝ :=
  fun m => c * lambda ^ m

theorem chapter16_growing_ceiling_is_not_uniform
    {c lambda : ℝ} (hc : 0 < c) (hlambda : 1 < lambda) :
    ¬ ∃ U : ℝ, ∀ m : ℕ, chapter16GrowingCeiling c lambda m ≤ U := by
  sorry

def chapter16CumulativeStepDegree (stepDegree : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range n, stepDegree i

def chapter16ConstantStepDegree (_ : ℕ) : ℕ :=
  2

theorem chapter16_bounded_step_degrees_do_not_bound_total_degree :
    (∀ i : ℕ, 0 < chapter16ConstantStepDegree i ∧
      chapter16ConstantStepDegree i ≤ 2) ∧
    (∀ n : ℕ,
      chapter16CumulativeStepDegree chapter16ConstantStepDegree n = 2 ^ n) ∧
    ¬ ∃ N : ℕ, ∀ n : ℕ,
      chapter16CumulativeStepDegree chapter16ConstantStepDegree n ≤ N := by
  sorry

abbrev chapter16LocalDifferentCostProfile
    (F : Type*) [Field F] [NumberField F] :=
  Chapter13LocalDifferentCostProfile F

noncomputable def chapter16AbsoluteCeilingFromLocalCosts
    (F : Type*) [Field F] [NumberField F]
    (P : chapter16LocalDifferentCostProfile F) : ℝ :=
  chapter13AbsoluteCeilingFromLocalCosts F P

noncomputable def chapter16LocalCostProduct
    (F : Type*) [Field F] [NumberField F]
    (P : chapter16LocalDifferentCostProfile F) : ℝ := by
  letI := P.fintype
  exact
    ∏ i : P.index,
      Real.rpow (chapter13FinitePlaceNorm (P.place i))
        (P.cost i / (chapter16Degree F : ℝ))

theorem chapter16_absolute_ceiling_from_local_costs_includes_base_factor
    (F : Type*) [Field F] [NumberField F]
    (P : chapter16LocalDifferentCostProfile F) :
    chapter16AbsoluteCeilingFromLocalCosts F P =
      chapter16RootDiscriminant F * chapter16LocalCostProduct F P := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter16
