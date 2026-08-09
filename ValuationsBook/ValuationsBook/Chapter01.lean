import Mathlib

namespace ValuationsBook.Chapter01

open scoped Polynomial RatFunc nonZeroDivisors
open Set Function Ideal
open scoped BigOperators

noncomputable section

/-! # Chapter 1: Measuring vanishing

This file is a statement-generation pass for Chapter 1 of *Valuations, DVRs, and
Completions*.  The declarations below follow Sections 1.1--1.5 in order. -/

/-! ## 1.1 A local question -/

section LocalQuestion

variable {k : Type*} [Field k]

/-- The multiplicity of the coordinate `t` in a polynomial.  This is used only
for nonzero polynomials, where Mathlib's `multiplicity` is the largest exponent
of `X` dividing the polynomial. -/
def ordZeroPolynomial (f : k[X]) : ℕ :=
  multiplicity (Polynomial.X : k[X]) f

/-- A polynomial factorization at the origin, with its regular factor recorded. -/
structure ZeroOrderFactorization (f : k[X]) where
  exponent : ℕ
  unit : k[X]
  equation : f = (Polynomial.X : k[X]) ^ exponent * unit
  unit_value_ne_zero : Polynomial.eval 0 unit ≠ 0

/-- A nonzero polynomial has a power of `t` times a factor nonzero at `0`. -/
theorem exists_zeroOrderFactorization {f : k[X]} (hf : f ≠ 0) :
    Nonempty (ZeroOrderFactorization f) := by sorry

/-- The chosen factorization used when a concrete factor is needed. -/
noncomputable def zeroOrderFactorization {f : k[X]} (hf : f ≠ 0) :
    ZeroOrderFactorization f :=
  Classical.choice (exists_zeroOrderFactorization hf)

/-- The exponent in the factorization is the order of vanishing. -/
theorem zeroOrderFactorization_exponent_eq_ord {f : k[X]} (hf : f ≠ 0) :
    (zeroOrderFactorization hf).exponent = ordZeroPolynomial f := by sorry

/-- The polynomial version of `f = t^n u(t)` with `u(0) ≠ 0`. -/
theorem exists_polynomial_zero_order_factorization {f : k[X]} (hf : f ≠ 0) :
    ∃ n : ℕ, ∃ u : k[X],
      f = (Polynomial.X : k[X]) ^ n * u ∧ Polynomial.eval 0 u ≠ 0 := by sorry

/-- The largest-power characterization of the order at the origin. -/
theorem ordZeroPolynomial_characterization {f : k[X]} (hf : f ≠ 0) (n : ℕ) :
    ordZeroPolynomial f = n ↔
      (Polynomial.X : k[X]) ^ n ∣ f ∧
        ¬(Polynomial.X : k[X]) ^ (n + 1) ∣ f := by sorry

/-- A nonzero polynomial has positive order exactly when it vanishes at the origin. -/
theorem ordZeroPolynomial_pos_iff_eval_zero {f : k[X]} (hf : f ≠ 0) :
    0 < ordZeroPolynomial f ↔ Polynomial.eval 0 f = 0 := by sorry

/-- The order of a nonvanishing polynomial at the origin is zero. -/
theorem ordZeroPolynomial_eq_zero_iff_eval_ne_zero {f : k[X]} (hf : f ≠ 0) :
    ordZeroPolynomial f = 0 ↔ Polynomial.eval 0 f ≠ 0 := by sorry

/-- The regular factors at the origin, i.e. the candidates for local units. -/
def IsRegularAtZero (u : k[X]) : Prop :=
  Polynomial.eval 0 u ≠ 0

/-- A rational function is regular and nonzero at `0` when both normalized
numerator and denominator are nonzero there. -/
def IsRegularAtZeroRatFunc (u : RatFunc k) : Prop :=
  Polynomial.eval 0 u.num ≠ 0 ∧ Polynomial.eval 0 u.denom ≠ 0

/-- The rational-function coordinate corresponding to the polynomial `X`. -/
def ratFuncCoordinate : RatFunc k :=
  algebraMap k[X] (RatFunc k) Polynomial.X

/-- A rational-function factorization by an integral power of the local
coordinate, with a factor that is a local unit at the origin. -/
structure RatFuncZeroOrderFactorization (x : RatFunc k) where
  exponent : ℤ
  unit : RatFunc k
  equation : x = ratFuncCoordinate ^ exponent * unit
  unit_regular_at_zero : IsRegularAtZeroRatFunc unit

/-- Every nonzero rational function admits a zero/pole factorization. -/
theorem exists_ratFuncZeroOrderFactorization {x : RatFunc k} (hx : x ≠ 0) :
    Nonempty (RatFuncZeroOrderFactorization x) := by sorry

/-- A chosen zero/pole factorization of a nonzero rational function. -/
noncomputable def ratFuncZeroOrderFactorization {x : RatFunc k} (hx : x ≠ 0) :
    RatFuncZeroOrderFactorization x :=
  Classical.choice (exists_ratFuncZeroOrderFactorization hx)

/-- The order of a rational function, extended by zero at the zero function for
convenience when a total function is desired. -/
def ordZeroRatFunc (x : RatFunc k) : ℤ :=
  by
    classical
    exact if x = 0 then 0 else
    (multiplicity (Polynomial.X : k[X]) x.num : ℤ) -
      (multiplicity (Polynomial.X : k[X]) x.denom : ℤ)

/-- The total additive order at the origin, with the zero function assigned
infinite order. -/
def ordZeroRatFuncWithTop (x : RatFunc k) : WithTop ℤ :=
  by
    classical
    exact if x = 0 then ⊤ else (ordZeroRatFunc x : WithTop ℤ)

/-- The order of a polynomial fraction before passing to the fraction field. -/
def ordZeroFraction (f g : k[X]) : ℤ :=
  (multiplicity (Polynomial.X : k[X]) f : ℤ) -
    (multiplicity (Polynomial.X : k[X]) g : ℤ)

/-- Multiplying numerator and denominator by a common nonzero factor does not
change the order of a fraction. -/
theorem ordZeroFraction_cancel_common_factor {f g h : k[X]}
    (hf : f ≠ 0) (hg : g ≠ 0) (hh : h ≠ 0) :
    ordZeroFraction (f * h) (g * h) = ordZeroFraction f g := by sorry

/-- The normalized numerator/denominator definition agrees with the fraction
definition whenever the displayed fraction represents `x`. -/
theorem ordZeroRatFunc_eq_ordZeroFraction {x : RatFunc k} {f g : k[X]}
    (hg : g ≠ 0) (hx : x = algebraMap k[X] (RatFunc k) f /
      algebraMap k[X] (RatFunc k) g) :
    ordZeroRatFunc x = ordZeroFraction f g := by sorry

/-- The order of a product is the sum of the orders. -/
theorem ordZeroRatFunc_mul {x y : RatFunc k} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordZeroRatFunc (x * y) = ordZeroRatFunc x + ordZeroRatFunc y := by sorry

/-- The order of a reciprocal is the negative of the order. -/
theorem ordZeroRatFunc_inv {x : RatFunc k} (hx : x ≠ 0) :
    ordZeroRatFunc x⁻¹ = -ordZeroRatFunc x := by sorry

/-- The order of a quotient is the difference of the orders. -/
theorem ordZeroRatFunc_div {x y : RatFunc k} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordZeroRatFunc (x / y) = ordZeroRatFunc x - ordZeroRatFunc y := by sorry

/-- The total order satisfies the additive valuation inequality. -/
theorem ordZeroRatFuncWithTop_add {x y : RatFunc k} :
    min (ordZeroRatFuncWithTop x) (ordZeroRatFuncWithTop y) ≤
      ordZeroRatFuncWithTop (x + y) := by sorry

/-- If two nonzero rational functions have different orders, their sum has the
smaller order; unequal orders cannot cancel. -/
theorem ordZeroRatFunc_add_of_ne {x y : RatFunc k} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x + y ≠ 0) (hne : ordZeroRatFunc x ≠ ordZeroRatFunc y) :
    ordZeroRatFunc (x + y) = min (ordZeroRatFunc x) (ordZeroRatFunc y) := by sorry

/-- A regular local unit contributes order zero. -/
theorem ordZeroRatFunc_of_regular_unit {u : RatFunc k}
    (hu : IsRegularAtZeroRatFunc u) :
    ordZeroRatFunc u = 0 := by sorry

/-- The unit part of a nonzero rational function is locally invertible and has
order zero. -/
theorem ordZeroRatFunc_factorization_unit_part {x : RatFunc k} (hx : x ≠ 0) :
    ∃ n : ℤ, ∃ u : RatFunc k,
      x = ratFuncCoordinate ^ n * u ∧
        IsRegularAtZeroRatFunc u ∧ ordZeroRatFunc u = 0 := by sorry

/-- Positive, negative, and zero order mean zero, pole, and nonvanishing regular
behavior, respectively. -/
theorem ordZeroRatFunc_sign_classification {x : RatFunc k} (hx : x ≠ 0) :
    (0 < ordZeroRatFunc x ↔ Polynomial.eval 0 x.num = 0) ∧
    (ordZeroRatFunc x < 0 ↔ Polynomial.eval 0 x.denom = 0) ∧
    (ordZeroRatFunc x = 0 ↔
      Polynomial.eval 0 x.num ≠ 0 ∧ Polynomial.eval 0 x.denom ≠ 0) := by sorry

/-- Order at an arbitrary point of the affine line, defined by the factor
`X - a`. -/
def ordAtPolynomial (a : k) (f : k[X]) : ℕ :=
  multiplicity (Polynomial.X - Polynomial.C a : k[X]) f

/-- The rational-function order at `a`, using numerator and denominator. -/
def ordAtRatFunc (a : k) (x : RatFunc k) : ℤ :=
  by
    classical
    exact if x = 0 then 0 else
    (multiplicity (Polynomial.X - Polynomial.C a : k[X]) x.num : ℤ) -
      (multiplicity (Polynomial.X - Polynomial.C a : k[X]) x.denom : ℤ)

/-- Translating the coordinate identifies order at `a` with order at the origin. -/
theorem ordAtPolynomial_eq_ordZero_after_translation (a : k) (f : k[X]) :
    ordAtPolynomial a f =
      ordZeroPolynomial (f.comp (Polynomial.X + Polynomial.C a)) := by sorry

/-- A local parameter is a generator of the maximal ideal of a one-dimensional
regular local ring. -/
def IsLocalParameter {R : Type*} [CommRing R] (𝔪 : Ideal R) (t : R) : Prop :=
  Ideal.span ({t} : Set R) = 𝔪

/-- Two local parameters differ by a local unit. -/
theorem local_parameters_differ_by_unit {R : Type*} [CommRing R] [IsDomain R]
    [IsLocalRing R] {𝔪 : Ideal R} {s t : R}
    (hs : IsLocalParameter 𝔪 s) (ht : IsLocalParameter 𝔪 t) :
    ∃ u : Rˣ, s = (u : R) * t := by sorry

/-- Multiplication by a local unit does not change an additive order. -/
theorem additive_order_invariant_under_local_unit {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (u : Kˣ) (x : K)
    (hu : v (u : K) = 0) :
    v ((u : K) * x) = v x := by sorry

end LocalQuestion

/-! ## 1.2 The prime-adic model and order on a line -/

section PrimeAdicModel

/-- A `p`-free presentation of a rational number, retaining the exponent and
the unit fraction.  The exponent is the canonical part of the presentation;
`a` and `b` themselves are only determined up to a common `p`-free factor. -/
structure PrimeAdicDecomposition (p : ℕ) (x : ℚ) where
  exponent : ℤ
  numerator : ℤ
  denominator : ℤ
  numerator_ne_zero : numerator ≠ 0
  denominator_ne_zero : denominator ≠ 0
  numerator_p_free : ¬(p : ℤ) ∣ numerator
  denominator_p_free : ¬(p : ℤ) ∣ denominator
  equation : x = (p : ℚ) ^ exponent * (numerator : ℚ) / (denominator : ℚ)

/-- The usual integer-valued `p`-adic order on rationals. -/
def pAdicOrder (p : ℕ) (x : ℚ) : ℤ :=
  padicValRat p x

/-- The total additive version, assigning infinite order to zero. -/
def pAdicOrderWithTop (p : ℕ) (x : ℚ) : WithTop ℤ :=
  if x = 0 then ⊤ else (pAdicOrder p x : WithTop ℤ)

/-- Mathlib's multiplicative `p`-adic valuation, included as the valuation-law
realization of `pAdicOrder`. -/
def pAdicMultiplicativeValuation (p : ℕ) [Fact p.Prime] :
    Valuation ℚ (WithZero (Multiplicative ℤ)) :=
  Rat.padicValuation p

/-- Existence of the reduced `p`-power times `p`-free fraction presentation. -/
theorem exists_primeAdicDecomposition {p : ℕ} (hp : p.Prime) {x : ℚ}
    (hx : x ≠ 0) : Nonempty (PrimeAdicDecomposition p x) := by sorry

/-- The exponent in every `p`-free presentation is the `p`-adic order. -/
theorem primeAdicDecomposition_exponent_eq_pAdicOrder {p : ℕ} (hp : p.Prime)
    {x : ℚ} (hx : x ≠ 0) (d : PrimeAdicDecomposition p x) :
    d.exponent = pAdicOrder p x := by sorry

/-- The exponent and the `p`-free rational unit are unique. -/
theorem primeAdicDecomposition_unique_exponent_and_unit {p : ℕ} (hp : p.Prime)
    {x : ℚ} (hx : x ≠ 0) {d e : PrimeAdicDecomposition p x} :
    d.exponent = e.exponent ∧
      (d.numerator : ℚ) / d.denominator =
        (e.numerator : ℚ) / e.denominator := by sorry

/-- Multiplication adds `p`-adic orders. -/
theorem pAdicOrder_mul {p : ℕ} (hp : p.Prime) {x y : ℚ}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    pAdicOrder p (x * y) = pAdicOrder p x + pAdicOrder p y := by sorry

/-- Inversion negates `p`-adic order. -/
theorem pAdicOrder_inv {p : ℕ} (hp : p.Prime) {x : ℚ} (hx : x ≠ 0) :
    pAdicOrder p x⁻¹ = -pAdicOrder p x := by sorry

/-- The additive valuation inequality for `p`-adic order. -/
theorem pAdicOrderWithTop_add (p : ℕ) (x y : ℚ) :
    min (pAdicOrderWithTop p x) (pAdicOrderWithTop p y) ≤
      pAdicOrderWithTop p (x + y) := by sorry

/-- The ordinary integer form of the triangle inequality when the sum is
nonzero. -/
theorem pAdicOrder_add {p : ℕ} (hp : p.Prime) {x y : ℚ}
    (hxy : x + y ≠ 0) :
    min (pAdicOrder p x) (pAdicOrder p y) ≤ pAdicOrder p (x + y) := by sorry

/-- Unequal `p`-adic orders force equality with the lower order. -/
theorem pAdicOrder_add_of_ne {p : ℕ} (hp : p.Prime) {x y : ℚ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0)
    (hne : pAdicOrder p x ≠ pAdicOrder p y) :
    pAdicOrder p (x + y) = min (pAdicOrder p x) (pAdicOrder p y) := by sorry

/-- The `p`-adic order of `p` itself is one. -/
theorem pAdicOrder_self {p : ℕ} (hp : p.Prime) :
    pAdicOrder p (p : ℚ) = 1 := by sorry

/-- The strict inequality in `v₃(1+2)` records cancellation modulo `3`. -/
theorem pAdic_cancellation_at_three :
    pAdicOrder 3 (1 + 2 : ℚ) >
      min (pAdicOrder 3 (1 : ℚ)) (pAdicOrder 3 (2 : ℚ)) := by sorry

/-- The standard numerical example `v₃(45/14) = 2`. -/
example : pAdicOrder 3 (45 / 14 : ℚ) = 2 := by sorry

/-- The standard cancellation example `v₃(1+2) = 1`. -/
example : pAdicOrder 3 (1 + 2 : ℚ) = 1 := by sorry

/-- The `p`-adic unit part of a nonzero rational number. -/
def pAdicUnitPart (p : ℕ) (x : ℚ) : ℚ :=
  x / (p : ℚ) ^ pAdicOrder p x

/-- A rational number is its `p`-power magnitude times its unit part. -/
theorem pAdic_magnitude_unit_decomposition {p : ℕ} (hp : p.Prime)
    {x : ℚ} (hx : x ≠ 0) :
    x = (p : ℚ) ^ pAdicOrder p x * pAdicUnitPart p x := by sorry

/-- The unit part has zero `p`-adic order. -/
theorem pAdicUnitPart_order_zero {p : ℕ} (hp : p.Prime)
    {x : ℚ} (hx : x ≠ 0) :
    pAdicOrder p (pAdicUnitPart p x) = 0 := by sorry

end PrimeAdicModel

/-! ## 1.3 What should count as integral? -/

section IntegralObjects

variable {k : Type*} [Field k]

/-- The set of rational functions with denominator nonzero at the origin,
the displayed model for `k[t]_(t)`. -/
def polynomialLocalElementsAtZero : Set (RatFunc k) :=
  {x | ∃ f g : k[X], Polynomial.eval 0 g ≠ 0 ∧
    x = algebraMap k[X] (RatFunc k) f / algebraMap k[X] (RatFunc k) g}

/-- The set-theoretic model for `ℤ_(p)`. -/
def integerLocalElementsAtPrime (p : ℕ) : Set ℚ :=
  {x | ∃ a b : ℤ, b ≠ 0 ∧ ¬(p : ℤ) ∣ b ∧
    x = (a : ℚ) / (b : ℚ)}

/-- The polynomial prime ideal `(t)` at the origin. -/
def originPrimeIdeal : Ideal k[X] :=
  Ideal.span ({Polynomial.X} : Set k[X])
instance originPrimeIdeal_isPrime_inst :
    (originPrimeIdeal (k := k)).IsPrime := by
  sorry

/-- The prime ideal `(p)` in the integers. -/
def integerPrimeIdeal (p : ℕ) : Ideal ℤ :=
  Ideal.span ({(p : ℤ)} : Set ℤ)
instance integerPrimeIdeal_isPrime_inst (p : ℕ) [Fact p.Prime] :
    (integerPrimeIdeal p).IsPrime := by
  sorry

/-- Localization at the complement of a prime ideal, kept as a type so that
the same declaration can be used for polynomial and arithmetic examples. -/
abbrev chapterLocalizationAtPrime (A : Type*) [CommSemiring A] (P : Ideal A)
    [P.IsPrime] : Type _ :=
  Localization P.primeCompl

/-- The local ring `k[t]_(t)` as a Mathlib localization. -/
abbrev polynomialLocalRingAtZero : Type _ :=
  chapterLocalizationAtPrime k[X] (originPrimeIdeal (k := k))

/-- The local ring `ℤ_(p)` as a Mathlib localization. -/
abbrev integerLocalRingAtPrime (p : ℕ) [Fact p.Prime] : Type _ :=
  chapterLocalizationAtPrime ℤ (integerPrimeIdeal p)

/-- The polynomial origin ideal is prime. -/
theorem originPrimeIdeal_isPrime : (originPrimeIdeal (k := k)).IsPrime := by sorry

/-- The integer ideal `(p)` is prime for a prime `p`. -/
theorem integerPrimeIdeal_isPrime {p : ℕ} (hp : p.Prime) :
    (integerPrimeIdeal p).IsPrime := by sorry

/-- Localization at a prime is local. -/
theorem chapterLocalizationAtPrime_isLocalRing {A : Type*} [CommRing A]
    (P : Ideal A) [P.IsPrime] :
    IsLocalRing (chapterLocalizationAtPrime A P) := by sorry

/-- The polynomial localization `k[t]_(t)` is a local ring. -/
theorem polynomialLocalRingAtZero_isLocalRing :
    IsLocalRing (polynomialLocalRingAtZero (k := k)) := by sorry

/-- The arithmetic localization `ℤ_(p)` is a local ring for prime `p`. -/
theorem integerLocalRingAtPrime_isLocalRing {p : ℕ} [Fact p.Prime] (hp : p.Prime) :
    IsLocalRing (integerLocalRingAtPrime p) := by sorry

/-- In a Dedekind domain, localization at a nonzero prime is a DVR. -/
theorem chapterLocalizationAtPrime_isDiscreteValuationRing {A : Type*} [CommRing A]
    [IsDedekindDomain A] (P : Ideal A) [P.IsPrime] (hP : P ≠ ⊥) :
    IsDiscreteValuationRing (chapterLocalizationAtPrime A P) := by sorry

/-- An affine-line denominator is a local unit precisely when it does not vanish
at the chosen point. -/
theorem polynomial_local_elements_are_fractions_with_unit_denominator (x : RatFunc k) :
    x ∈ polynomialLocalElementsAtZero (k := k) ↔
      ∃ f g : k[X], IsRegularAtZero g ∧
        x = algebraMap k[X] (RatFunc k) f / algebraMap k[X] (RatFunc k) g := by sorry

/-- The `p`-adic integral set is the set of rationals whose denominator is
prime to `p`. -/
theorem integer_local_elements_iff_nonnegative_pAdicOrder {p : ℕ}
    (hp : p.Prime) {x : ℚ} :
    x ∈ integerLocalElementsAtPrime p ↔ 0 ≤ pAdicOrder p x := by sorry

/-- The no-pole part of the rational-function field is the nonnegative-order
part of the order at the origin. -/
noncomputable def rationalFunctionValuationRingAtZero : Subring (RatFunc k) :=
  { carrier := {x | x = 0 ∨ 0 ≤ ordZeroRatFunc x}
    zero_mem' := by simp
    one_mem' := by sorry
    add_mem' := by sorry
    mul_mem' := by sorry
    neg_mem' := by sorry }

/-- The local units at the origin are the nonzero functions of order zero. -/
def rationalFunctionUnitsAtZero : Set (RatFunc k) :=
  {x | x ≠ 0 ∧ ordZeroRatFunc x = 0}

/-- The affine-line local set is exactly the set of rational functions without a
pole at the origin. -/
theorem polynomial_local_elements_iff_no_pole (x : RatFunc k) :
    x ∈ polynomialLocalElementsAtZero (k := k) ↔
      x ∈ rationalFunctionValuationRingAtZero (k := k) := by sorry

/-- In additive notation, the maximal ideal of a valuation subring consists of
the positive-valued elements. -/
theorem additive_valuation_subring_maximalIdeal_iff_positive
    {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ))
    (x : v.toValuation.valuationSubring) :
    x ∈ IsLocalRing.maximalIdeal v.toValuation.valuationSubring ↔
      (0 : WithTop ℤ) < v (x : K) := by sorry

/-- The nonzero elements of a discrete additive valuation ring are powers of a
uniformizer times units. -/
theorem discrete_additive_valuation_factorization {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (π : K) (hπ : v π = 1)
    (x : v.toValuation.valuationSubring) (hx : x ≠ 0) :
    ∃ n : ℕ, ∃ u : v.toValuation.valuationSubringˣ,
      (x : K) = π ^ n * (u : K) := by sorry

/-- The corresponding factorization for a nonzero `p`-adic integral rational. -/
theorem pAdic_integral_factorization {p : ℕ} (hp : p.Prime) {x : ℚ}
    (hx : x ≠ 0) (hIntegral : 0 ≤ pAdicOrder p x) :
    ∃ n : ℕ, ∃ u : ℚ,
      pAdicOrder p u = 0 ∧ x = (p : ℚ) ^ n * u := by sorry

/-- The corresponding factorization for a rational function without a pole at
the origin. -/
theorem zero_order_integral_factorization {x : RatFunc k}
    (hx : x ≠ 0) (hIntegral : 0 ≤ ordZeroRatFunc x) :
    ∃ n : ℕ, ∃ u : RatFunc k,
      ordZeroRatFunc u = 0 ∧ x = ratFuncCoordinate ^ n * u := by sorry

/-- The comparison condition for a subring of a field to be a valuation ring. -/
def HasChapterValuationRingComparison {K : Type*} [Field K] (V : Subring K) : Prop :=
  ∀ x : K, x ∈ V ∨ x⁻¹ ∈ V

/-- A subring satisfying the comparison condition is a valuation subring. -/
def chapterValuationSubring {K : Type*} [Field K] (V : Subring K)
    (hV : HasChapterValuationRingComparison V) : ValuationSubring K :=
  ValuationSubring.ofSubring V hV

/-- The comparison condition yields Mathlib's valuation-ring class. -/
theorem chapterValuationSubring_isValuationRing {K : Type*} [Field K]
    (V : Subring K) (hV : HasChapterValuationRingComparison V) :
    ValuationRing (chapterValuationSubring V hV) := by sorry

/-- The order on a valuation subring is recovered from divisibility by principal
fractional ideals. -/
def ChapterPrincipalIdealDivides {K : Type*} [Field K]
    (V : ValuationSubring K) (x y : K) : Prop :=
  ∃ a : V, (a : K) * y = x

/-- Principal-ideal divisibility and the valuation order agree. -/
theorem chapterPrincipalIdealDivides_iff_valuation_le {K : Type*} [Field K]
    (V : ValuationSubring K) (x y : K) :
    ChapterPrincipalIdealDivides V x y ↔ V.valuation x ≤ V.valuation y := by sorry

/-- Principal fractional ideals are totally ordered in a valuation ring. -/
theorem chapterPrincipalIdealDivides_total {K : Type*} [Field K]
    (V : ValuationSubring K) (x y : K) :
    ChapterPrincipalIdealDivides V x y ∨ ChapterPrincipalIdealDivides V y x := by sorry

end IntegralObjects

/-! ## 1.4 Localizations of Dedekind domains -/

section DedekindLocalizations

open scoped nonZeroDivisors

variable {A K : Type*} [CommRing A] [Field K] [Algebra A K]
  [IsFractionRing A K] [IsDedekindDomain A]

/-- The nonzero prime corresponding to a height-one point of a Dedekind domain. -/
def chapterPrimeOfHeightOne (P : IsDedekindDomain.HeightOneSpectrum A) : Ideal A :=
  P.asIdeal

/-- The exponent of a height-one prime in the principal fractional ideal `(x)`. -/
def dedekindExponent (P : IsDedekindDomain.HeightOneSpectrum A) (x : K) : ℤ :=
  FractionalIdeal.count K P (FractionalIdeal.spanSingleton A⁰ x)

/-- The principal fractional ideal used in the factorization statements. -/
def chapterPrincipalFractionalIdeal (x : K) : FractionalIdeal A⁰ K :=
  FractionalIdeal.spanSingleton A⁰ x

/-- A nonzero principal fractional ideal factors over the height-one primes. -/
theorem dedekind_principal_fractional_ideal_factorization {x : K} (hx : x ≠ 0) :
    ∏ᶠ P : IsDedekindDomain.HeightOneSpectrum A,
      (P.asIdeal : FractionalIdeal A⁰ K) ^ dedekindExponent P x =
        chapterPrincipalFractionalIdeal x := by sorry

/-- Only finitely many height-one exponents of a nonzero principal fractional
ideal are nonzero. -/
theorem dedekindExponent_finite_support {x : K} (hx : x ≠ 0) :
    {P : IsDedekindDomain.HeightOneSpectrum A | dedekindExponent P x ≠ 0}.Finite := by sorry

/-- The exponent is additive under multiplication of nonzero elements. -/
theorem dedekindExponent_mul (P : IsDedekindDomain.HeightOneSpectrum A)
    {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    dedekindExponent P (x * y) = dedekindExponent P x + dedekindExponent P y := by sorry

/-- The Dedekind exponent satisfies the valuation inequality under addition. -/
theorem dedekindExponent_add (P : IsDedekindDomain.HeightOneSpectrum A)
    {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (dedekindExponent P x) (dedekindExponent P y) ≤
      dedekindExponent P (x + y) := by sorry

/-- Unequal Dedekind exponents cannot cancel in a sum. -/
theorem dedekindExponent_add_of_ne (P : IsDedekindDomain.HeightOneSpectrum A)
    {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0)
    (hne : dedekindExponent P x ≠ dedekindExponent P y) :
    dedekindExponent P (x + y) = min (dedekindExponent P x) (dedekindExponent P y) := by sorry

/-- The exponent of a unit is zero. -/
theorem dedekindExponent_one (P : IsDedekindDomain.HeightOneSpectrum A) :
    dedekindExponent P (1 : K) = 0 := by sorry

/-- The exponent of an inverse is the negative exponent. -/
theorem dedekindExponent_inv (P : IsDedekindDomain.HeightOneSpectrum A)
    {x : K} (hx : x ≠ 0) :
    dedekindExponent P x⁻¹ = -dedekindExponent P x := by sorry

/-- Every element of the fraction field can be tested in a localization at a
prime using a denominator outside that prime. -/
def IsInChapterLocalizationAtPrime (P : Ideal A) [P.IsPrime] (x : K) : Prop :=
  ∃ a : A, ∃ s : P.primeCompl,
    x * algebraMap A K (s : A) = algebraMap A K a

/-- A denominator outside `P` contributes no `P`-factor. -/
theorem dedekindExponent_primeCompl_eq_zero
    (P : IsDedekindDomain.HeightOneSpectrum A) (s : P.asIdeal.primeCompl) :
    dedekindExponent P (algebraMap A K (s : A)) = 0 := by sorry

/-- Membership in the localization at `P` is exactly nonnegative `P`-adic
exponent. -/
theorem localization_membership_iff_dedekindExponent_nonnegative
    (P : IsDedekindDomain.HeightOneSpectrum A) (x : K) :
    IsInChapterLocalizationAtPrime P.asIdeal x ↔ 0 ≤ dedekindExponent P x := by sorry

/-- A general nonzero prime of a Dedekind domain gives a height-one spectrum
point. -/
def chapterHeightOneSpectrumOfPrime (P : Ideal A) [P.IsPrime] (hP : P ≠ ⊥) :
    IsDedekindDomain.HeightOneSpectrum A :=
  ⟨P, inferInstance, hP⟩

/-- The localization at a nonzero prime is a discrete valuation ring. -/
theorem dedekind_localization_at_nonzero_prime_isDVR (P : Ideal A) [P.IsPrime]
    (hP : P ≠ ⊥) :
    IsDiscreteValuationRing (chapterLocalizationAtPrime A P) := by sorry

/-- Localizing at one prime makes all other prime factors units, leaving one
integer-valued exponent to govern the local ideal theory. -/
theorem localization_keeps_only_one_dedekind_exponent
    (P : IsDedekindDomain.HeightOneSpectrum A) (x : K) :
    IsInChapterLocalizationAtPrime P.asIdeal x ↔ 0 ≤ dedekindExponent P x := by sorry

end DedekindLocalizations

/-! ## 1.5 Measurements that are not discrete -/

section PuiseuxValuation

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- A stage of the Puiseux tower is modeled by a Laurent series in the variable
`t^(1/n)`.  The fields and transition maps are packaged as an interface since
Mathlib does not select one concrete construction of the full Puiseux union. -/
structure PuiseuxValuationModel where
  stage : ∀ n : ℕ, 0 < n → LaurentSeries k →+* K
  stage_injective : ∀ (n : ℕ) (hn : 0 < n), Function.Injective (stage n hn)
  union : ∀ x : K, ∃ n : ℕ, ∃ hn : 0 < n, ∃ f : LaurentSeries k,
    stage n hn f = x
  valuation : AddValuation K (WithTop ℚ)
  stage_valuation : ∀ (n : ℕ) (hn : 0 < n) (f : LaurentSeries k), f ≠ 0 →
    valuation (stage n hn f) =
      (((f.order : ℚ) / (n : ℚ)) : WithTop ℚ)
  overlap_order : ∀ (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (f g : LaurentSeries k), f ≠ 0 → g ≠ 0 →
    stage m hm f = stage n hn g →
      (f.order : ℚ) / (m : ℚ) = (g.order : ℚ) / (n : ℚ)
  value_surjective : ∀ q : ℚ, ∃ n : ℕ, ∃ hn : 0 < n,
    ∃ f : LaurentSeries k, f ≠ 0 ∧
      ((f.order : ℚ) / (n : ℚ)) = q

/-- The lowest exponent in the `n`th stage lies in `(1/n)ℤ`. -/
def puiseuxStageExponent (n : ℕ) (hn : 0 < n) (f : LaurentSeries k) : ℚ :=
  (f.order : ℚ) / (n : ℚ)

/-- The `n`th Laurent-series stage has exponents in `1/n · ℤ`. -/
theorem puiseuxStageExponent_mem_one_div_n_z {n : ℕ} (hn : 0 < n)
    (f : LaurentSeries k) :
    puiseuxStageExponent n hn f ∈ Set.range (fun z : ℤ => (z : ℚ) / (n : ℚ)) := by sorry

/-- The valuation is well-defined on overlaps of the stages. -/
theorem puiseux_overlap_valuation_well_defined (M : PuiseuxValuationModel (k := k) (K := K))
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {f g : LaurentSeries k}
    (hf : f ≠ 0) (hg : g ≠ 0) (hfg : M.stage m hm f = M.stage n hn g) :
    puiseuxStageExponent m hm f = puiseuxStageExponent n hn g := by sorry

/-- The value group of the Puiseux valuation is represented by the rationals. -/
def puiseuxValueSet (M : PuiseuxValuationModel (k := k) (K := K)) : Set ℚ :=
  {q | ∃ x : K, x ≠ 0 ∧ M.valuation x = (q : WithTop ℚ)}

/-- Every rational value occurs in the Puiseux tower. -/
theorem puiseuxValueSet_eq_univ (M : PuiseuxValuationModel (k := k) (K := K)) :
    puiseuxValueSet M = Set.univ := by sorry

/-- Rank one is expressed here by the Archimedean ordering property. -/
def IsChapterRankOneOrderedGroup (Γ : Type*) [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] : Prop :=
  ∀ a b : Γ, 0 < a → 0 < b → ∃ n : ℕ, a ≤ n • b

/-- Discreteness means that the positive cone has a least element. -/
def IsChapterDiscreteOrderedGroup (Γ : Type*) [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] : Prop :=
  ∃ γ : Γ, 0 < γ ∧ ∀ δ : Γ, 0 < δ → γ ≤ δ

/-- The ordered group of rational values has rank one. -/
theorem rational_value_group_is_rank_one :
    IsChapterRankOneOrderedGroup ℚ := by sorry

/-- The rational value group has no least positive element. -/
theorem rational_value_group_has_no_least_positive :
    ¬IsChapterDiscreteOrderedGroup ℚ := by sorry

/-- Explicitly, every positive rational has a smaller positive rational. -/
theorem exists_smaller_positive_rational {q : ℚ} (hq : 0 < q) :
    ∃ r : ℚ, 0 < r ∧ r < q := by sorry

/-- The Puiseux valuation ring is the ring of nonnegative-valued elements. -/
def puiseuxValuationRing (M : PuiseuxValuationModel (k := k) (K := K)) :
    ValuationSubring K :=
  M.valuation.toValuation.valuationSubring

/-- The maximal ideal of the Puiseux valuation ring. -/
def puiseuxMaximalIdeal (M : PuiseuxValuationModel (k := k) (K := K)) :
    Ideal (puiseuxValuationRing M) :=
  IsLocalRing.maximalIdeal (puiseuxValuationRing M)

/-- Nonnegative additive valuation is equivalent to membership in the valuation
subring. -/
theorem puiseux_mem_valuationRing_iff {M : PuiseuxValuationModel (k := k) (K := K)}
    (x : K) :
    x ∈ puiseuxValuationRing M ↔ (0 : WithTop ℚ) ≤ M.valuation x := by sorry

/-- Positive-valued elements are exactly the maximal ideal of the Puiseux ring. -/
theorem puiseux_mem_maximalIdeal_iff_positive
    (M : PuiseuxValuationModel (k := k) (K := K))
    (x : puiseuxValuationRing M) :
    x ∈ puiseuxMaximalIdeal M ↔
      (0 : WithTop ℚ) < M.valuation (x : K) := by sorry

/-- Given a positive value, a smaller positive rational value is realized by an
element of the tower. -/
theorem puiseux_exists_strictly_smaller_positive_element
    (M : PuiseuxValuationModel (k := k) (K := K))
    {a : puiseuxValuationRing M}
    (ha : (0 : WithTop ℚ) < M.valuation (a : K)) :
    ∃ b : puiseuxValuationRing M,
      (0 : WithTop ℚ) < M.valuation (b : K) ∧
        M.valuation (b : K) < M.valuation (a : K) := by sorry

/-- The strict-divisibility phenomenon behind the nonprincipal maximal ideal:
for a positive-valued `a`, a smaller positive-valued `b` satisfies
`a ∈ (b)` but `b ∉ (a)`. -/
theorem puiseux_strict_divisibility_in_maximalIdeal
    (M : PuiseuxValuationModel (k := k) (K := K))
    {a : puiseuxValuationRing M}
    (ha : (0 : WithTop ℚ) < M.valuation (a : K)) :
    ∃ b : puiseuxValuationRing M,
      (0 : WithTop ℚ) < M.valuation (b : K) ∧
        M.valuation (b : K) < M.valuation (a : K) ∧
        a ∈ Ideal.span ({b} : Set (puiseuxValuationRing M)) ∧
        b ∉ Ideal.span ({a} : Set (puiseuxValuationRing M)) := by sorry

/-- The positive maximal ideal is not generated by one element. -/
theorem puiseux_maximalIdeal_not_principal
    (M : PuiseuxValuationModel (k := k) (K := K)) :
    ¬∃ π : puiseuxValuationRing M,
      puiseuxMaximalIdeal M = Ideal.span ({π} : Set (puiseuxValuationRing M)) := by sorry

/-- The Puiseux valuation ring is nevertheless a valuation ring. -/
theorem puiseux_valuationRing_is_valuationRing
    (M : PuiseuxValuationModel (k := k) (K := K)) :
    ValuationRing (puiseuxValuationRing M) := by sorry

/-- The Puiseux valuation ring is not a discrete valuation ring. -/
theorem puiseux_valuationRing_not_discrete_valuation_ring
    (M : PuiseuxValuationModel (k := k) (K := K)) :
    ¬IsDiscreteValuationRing (puiseuxValuationRing M) := by sorry

/-- The same strict chain prevents the Puiseux valuation ring from being
Noetherian. -/
theorem puiseux_valuationRing_not_noetherian
    (M : PuiseuxValuationModel (k := k) (K := K)) :
    ¬IsNoetherianRing (puiseuxValuationRing M) := by sorry

/-- Rank one and discreteness are different properties: the Puiseux value group
is Archimedean but has no least positive value. -/
theorem puiseux_rank_one_but_not_discrete :
    IsChapterRankOneOrderedGroup ℚ ∧
      ¬IsChapterDiscreteOrderedGroup ℚ := by sorry

end PuiseuxValuation

end

end ValuationsBook.Chapter01
