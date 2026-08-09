import Mathlib

namespace ValuationsBook
namespace Chapter09

universe uK uL uΓ

open scoped BigOperators Polynomial
open Ideal IsLocalRing Polynomial

noncomputable section

local instance chapter09FactPrime7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
local instance chapter09FactPrime2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩

/-! # Chapter 9: Hensel lifting

This file is a statement-generation pass for Chapter 9 of Book 1.  The
declarations deliberately keep the hypotheses visible: in particular, a
complete DVR means adic completeness, while the valuation form is stated for
an arbitrary additive valuation.
-/

/-! ## Common residue-ring and valuation interfaces -/

/-- The residue ring of a local ring, written as a quotient by its maximal ideal. -/
abbrev ResidueRing (A : Type*) [CommRing A] [IsLocalRing A] :=
  A ⧸ IsLocalRing.maximalIdeal A

/-- The canonical map from a local ring to its residue ring. -/
def residueMap (A : Type*) [CommRing A] [IsLocalRing A] : A →+* ResidueRing A :=
  Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)

/-- The residue class of an element of a local ring. -/
def residueClass {A : Type*} [CommRing A] [IsLocalRing A] (a : A) : ResidueRing A :=
  residueMap A a

/-- Reduction of a polynomial to the residue ring. -/
def residuePolynomial {A : Type*} [CommRing A] [IsLocalRing A] (f : A[X]) :
    Polynomial (ResidueRing A) :=
  f.map (residueMap A)

/-- Congruence modulo an ideal, in a form convenient for chapter statements. -/
def CongruentModIdeal {A : Type*} [Ring A] (I : Ideal A) (a b : A) : Prop :=
  a - b ∈ I

/-- Every coefficient of a polynomial belongs to a specified ideal. -/
def PolynomialCoefficientsInIdeal {A : Type*} [Semiring A] (I : Ideal A) (f : A[X]) : Prop :=
  ∀ n : ℕ, f.coeff n ∈ I

/-- Every coefficient of a polynomial over a field lies in a chosen subring. -/
def PolynomialCoefficientsInSubring {K : Type*} [Field K] (A : Subring K) (f : K[X]) : Prop :=
  ∀ n : ℕ, f.coeff n ∈ A

/-- A subring described as the nonnegative part of an additive valuation. -/
def IsValuationSubring {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (A : Subring K)
    (v : AddValuation K Γ) : Prop :=
  ∀ x : K, x ∈ A ↔ v x ≥ 0

/-- A complete DVR for this chapter: a DVR complete and separated in the maximal-ideal topology. -/
class CompleteDVR (A : Type*) [CommRing A] [IsDomain A] : Prop
    extends IsDiscreteValuationRing A where
  isAdicComplete' : IsAdicComplete (IsLocalRing.maximalIdeal A) A

/-- The adic-completeness field of `CompleteDVR` is available as an instance. -/
instance CompleteDVR.isAdicComplete (A : Type*) [CommRing A] [IsDomain A]
    [hA : CompleteDVR A] : IsAdicComplete (IsLocalRing.maximalIdeal A) A :=
  hA.isAdicComplete'

/-- A residue root together with the nonvanishing derivative condition. -/
def IsSimpleResidueRoot {A : Type*} [CommRing A] [IsLocalRing A]
    (f : A[X]) (a : ResidueRing A) : Prop :=
  (residuePolynomial f).eval a = 0 ∧
    IsUnit ((residuePolynomial f).derivative.eval a)

/-- In a DVR, an irreducible element is the Mathlib notion of a uniformizer. -/
def IsUniformizer {A : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (π : A) : Prop :=
  Irreducible π

/-- The additive valuation supplied by Mathlib for a DVR. -/
noncomputable def chapterDvrValuation (A : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] : AddValuation A ℕ∞ :=
  IsDiscreteValuationRing.addVal A

/-- In a DVR, uniformizers are precisely generators of the maximal ideal. -/
theorem isUniformizer_iff_maximalIdeal_span {A : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (π : A) :
    IsUniformizer π ↔ IsLocalRing.maximalIdeal A = Ideal.span ({π} : Set A) := by
  sorry

/-! ## 9.1 Correcting an approximate root -/

/-- The quadratic example `X² - c` used throughout the chapter. -/
def quadraticPolynomial {R : Type*} [CommRing R] (c : R) : R[X] :=
  X ^ 2 - C c

/-- The second-order Taylor identity `f(a+h)=f(a)+h f'(a)+h² g`. -/
theorem taylor_second_order {A : Type*} [CommRing A] (f : A[X]) (a h : A) :
    ∃ g : A,
      f.eval (a + h) = f.eval a + h * f.derivative.eval a + h ^ 2 * g := by
  sorry

/-- Newton's correction, using Mathlib's globally defined ring inverse. -/
noncomputable def newtonCorrection {R : Type*} [CommRing R] (f : R[X]) (a : R) : R :=
  a - f.eval a * Ring.inverse (f.derivative.eval a)

/-- The sequence of Newton iterates. -/
noncomputable def newtonIterate {R : Type*} [CommRing R] (f : R[X]) (a₀ : R) : ℕ → R
  | 0 => a₀
  | n + 1 => newtonCorrection f (newtonIterate f a₀ n)

/-- Over a field, the ring-inverse definition is the usual Newton quotient. -/
theorem newtonCorrection_as_division {K : Type*} [Field K] (f : K[X]) (a : K)
    (h : f.derivative.eval a ≠ 0) :
    newtonCorrection f a = a - f.eval a / f.derivative.eval a := by
  sorry

/-- Polynomial evaluation preserves congruence modulo an ideal. -/
theorem polynomial_eval_congruent_mod_ideal {A : Type*} [CommRing A]
    (I : Ideal A) (f : A[X]) {a b : A} (hab : CongruentModIdeal I a b) :
    CongruentModIdeal I (f.eval a) (f.eval b) := by
  sorry

/-- Newton corrections remain in the maximal ideal when the current error does. -/
theorem newton_correction_congruent {A : Type*} [CommRing A] [IsLocalRing A]
    (f : A[X]) (a : A) (hfa : f.eval a ∈ IsLocalRing.maximalIdeal A) :
    CongruentModIdeal (IsLocalRing.maximalIdeal A) (newtonCorrection f a) a := by
  sorry

/-- The derivative has the same residue at congruent points. -/
theorem derivative_evaluation_congruent {A : Type*} [CommRing A] [IsLocalRing A]
    (f : A[X]) {a b : A}
    (hab : CongruentModIdeal (IsLocalRing.maximalIdeal A) a b) :
    CongruentModIdeal (IsLocalRing.maximalIdeal A)
      (f.derivative.eval a) (f.derivative.eval b) := by
  sorry

/-- A unit derivative stays a unit throughout the Newton residue class. -/
theorem derivative_unit_on_residue_class {A : Type*} [CommRing A] [IsLocalRing A]
    (f : A[X]) {a a₀ : A}
    (ha : CongruentModIdeal (IsLocalRing.maximalIdeal A) a a₀)
    (ha₀ : IsUnit (f.derivative.eval a₀)) :
    IsUnit (f.derivative.eval a) := by
  sorry

/-- In a complete DVR, the valuation of a Newton error at least doubles. -/
theorem newton_error_valuation_doubles {A : Type*} [CommRing A] [IsDomain A]
    [CompleteDVR A] (f : A[X]) (a : A)
    (hfa : f.eval a ∈ IsLocalRing.maximalIdeal A)
    (hunit : IsUnit (f.derivative.eval a)) :
    chapterDvrValuation A (f.eval (newtonCorrection f a)) ≥
      chapterDvrValuation A (f.eval a) + chapterDvrValuation A (f.eval a) := by
  sorry

/-- The correction has the same DVR valuation as the current error when the derivative is a unit. -/
theorem newton_correction_valuation {A : Type*} [CommRing A] [IsDomain A]
    [CompleteDVR A] (f : A[X]) (a : A)
    (hunit : IsUnit (f.derivative.eval a)) :
    chapterDvrValuation A (newtonCorrection f a - a) =
      chapterDvrValuation A (f.eval a) := by
  sorry

/-- An adic Cauchy sequence, stated without choosing a separate topology. -/
def AdicCauchySeq {A : Type*} [CommRing A] [IsLocalRing A] (s : ℕ → A) : Prop :=
  ∀ n : ℕ, ∃ N : ℕ, ∀ m k : ℕ, N ≤ m → N ≤ k →
    s m - s k ∈ (IsLocalRing.maximalIdeal A) ^ n

/-- An adic limit of a sequence. -/
def IsAdicLimit {A : Type*} [CommRing A] [IsLocalRing A] (s : ℕ → A) (a : A) : Prop :=
  ∀ n : ℕ, s n - a ∈ (IsLocalRing.maximalIdeal A) ^ n

/-- Newton iterates form an adic Cauchy sequence under the simple-root hypotheses. -/
theorem newton_iterates_adic_cauchy {A : Type*} [CommRing A] [IsDomain A]
    [CompleteDVR A] (f : A[X]) (a₀ : A)
    (hfa : f.eval a₀ ∈ IsLocalRing.maximalIdeal A)
    (hunit : IsUnit (f.derivative.eval a₀)) :
    AdicCauchySeq (newtonIterate f a₀) := by
  sorry

/-- Completeness supplies an adic limit for the Newton iterates. -/
theorem newton_iterates_have_limit {A : Type*} [CommRing A] [IsDomain A]
    [CompleteDVR A] (f : A[X]) (a₀ : A)
    (hfa : f.eval a₀ ∈ IsLocalRing.maximalIdeal A)
    (hunit : IsUnit (f.derivative.eval a₀)) :
    ∃ a : A, IsAdicLimit (newtonIterate f a₀) a := by
  sorry

/-- Simple-root Hensel lifting: the exact assertion of Theorem 9.1. -/
theorem hensel_simple_root {A : Type*} [CommRing A] [IsDomain A]
    [CompleteDVR A] (f : A[X]) (a₀ : A)
    (hfa : f.eval a₀ ∈ IsLocalRing.maximalIdeal A)
    (hunit : IsUnit (f.derivative.eval a₀)) :
    ∃! a : A,
      f.eval a = 0 ∧
        CongruentModIdeal (IsLocalRing.maximalIdeal A) a a₀ := by
  sorry

/-- Polynomial division in two variables, packaged as a divided-difference statement. -/
def IsDividedDifference {A : Type*} [CommRing A] (f : A[X]) (a b q : A) : Prop :=
  f.eval a - f.eval b = (a - b) * q

/-- Every polynomial admits a divided difference at two points. -/
theorem exists_divided_difference {A : Type*} [CommRing A] (f : A[X]) (a b : A) :
    ∃ q : A, IsDividedDifference f a b q := by
  sorry

/-- The divided difference is congruent to the derivative in the common residue class. -/
theorem divided_difference_congruent_derivative {A : Type*} [CommRing A] [IsLocalRing A]
    (f : A[X]) {a b a₀ : A}
    (ha : CongruentModIdeal (IsLocalRing.maximalIdeal A) a a₀)
    (hb : CongruentModIdeal (IsLocalRing.maximalIdeal A) b a₀) :
    ∃ q : A,
      IsDividedDifference f a b q ∧
        CongruentModIdeal (IsLocalRing.maximalIdeal A) q (f.derivative.eval a₀) := by
  sorry

/-- Two roots in the simple-root residue class coincide by the divided-difference argument. -/
theorem simple_root_residue_class_unique {A : Type*} [CommRing A] [IsDomain A]
    [CompleteDVR A] (f : A[X]) (a₀ a b : A)
    (ha : f.eval a = 0)
    (hb : f.eval b = 0)
    (ha₀ : IsUnit (f.derivative.eval a₀))
    (hca : CongruentModIdeal (IsLocalRing.maximalIdeal A) a a₀)
    (hcb : CongruentModIdeal (IsLocalRing.maximalIdeal A) b a₀) :
    a = b := by
  sorry

/-- Once the error has valuation at least `r`, the next Newton error has valuation at least `2r`. -/
theorem newton_precision_doubles {A : Type*} [CommRing A] [IsDomain A]
    [CompleteDVR A] (f : A[X]) (a : A) (r : ℕ)
    (hunit : IsUnit (f.derivative.eval a))
    (hprecision : f.eval a ∈ (IsLocalRing.maximalIdeal A) ^ r) :
    f.eval (newtonCorrection f a) ∈ (IsLocalRing.maximalIdeal A) ^ (2 * r) := by
  sorry

/-- The example `X²-p` has a root at zero modulo `p`. -/
theorem padic_x_sq_sub_p_has_mod_p_root_zero (p : ℕ) [Fact p.Prime] :
    (quadraticPolynomial (p : ZMod p)).eval 0 = 0 := by
  sorry

/-- The same polynomial has no root in `ℚ_[p]`, because square valuations are even. -/
theorem padic_x_sq_sub_p_has_no_root (p : ℕ) [Fact p.Prime] :
    ¬ ∃ x : ℚ_[p], x ^ 2 = (p : ℚ_[p]) := by
  sorry

/-- The additive p-adic valuation of a square is twice the valuation of its base. -/
theorem padic_square_valuation_is_even (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) :
    Padic.addValuation (p := p) (x ^ 2) =
      Padic.addValuation (p := p) x + Padic.addValuation (p := p) x := by
  sorry

/-! ## 9.2 The valuation form -/

/-- The excess of a valuation error beyond twice a fixed derivative value. -/
def valuationExcess {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ)
    (f : K[X]) (s : Γ) (a : K) : Γ :=
  v (f.eval a) - (s + s)

/- The uniformity canonically induced by an additive valuation. -/
noncomputable def Chapter09ValuationUniformSpace
    {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ) : UniformSpace K :=
  (Valued.mk' v.toValuation).toUniformSpace

/- Completeness for the nonarchimedean uniformity attached to `v`. -/
def Chapter09NonarchimedeanComplete
    {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ) : Prop :=
  @CompleteSpace K (Chapter09ValuationUniformSpace v)

/-- A sequence of values tends to infinity in the ordered-value sense. -/
def TendsToTop {Γ : Type*} [Preorder Γ] (s : ℕ → Γ) : Prop :=
  ∀ γ : Γ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → γ ≤ s n

/- Cofinality needed to turn valuation doubling into convergence to the top. -/
def Chapter09DoublingCofinal {Γ : Type*}
    [LinearOrderedAddCommGroupWithTop Γ] (q : Γ) : Prop :=
  ∀ γ : Γ, ∃ n : ℕ, γ ≤ (2 ^ n) • q

/-- The strong triangle inequality for an additive valuation. -/
theorem valuation_strong_triangle {K Γ : Type*} [Ring K]
    [LinearOrderedAddCommMonoidWithTop Γ] (v : AddValuation K Γ) (x y : K) :
    min (v x) (v y) ≤ v (x + y) := by
  sorry

/-- Unequal valuation terms cannot cancel. -/
theorem valuation_unequal_value_rigidity {K Γ : Type*} [Ring K]
    [LinearOrderedAddCommMonoidWithTop Γ] (v : AddValuation K Γ) {x y : K}
    (hxy : v x ≠ v y) :
    v (x + y) = min (v x) (v y) := by
  sorry

/-- The Newton correction and derivative invariants in the proof of Theorem 9.2. -/
theorem valuation_newton_induction {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ)
    (A : Subring K) (hA : IsValuationSubring A v) (f : K[X])
    (hf : PolynomialCoefficientsInSubring A f) (a₀ : K) (ha₀ : a₀ ∈ A)
    (hineq : v (f.eval a₀) > v (f.derivative.eval a₀) + v (f.derivative.eval a₀))
    (hderiv : v (f.derivative.eval a₀) ≠ ⊤) :
    let s := v (f.derivative.eval a₀)
    let q₀ := v (f.eval a₀) - (s + s)
    ∀ n : ℕ,
      v (f.derivative.eval (newtonIterate f a₀ n)) = s ∧
        valuationExcess v f s (newtonIterate f a₀ n) ≥ (2 ^ n) • q₀ ∧
        v (newtonIterate f a₀ (n + 1) - newtonIterate f a₀ n) =
          s + valuationExcess v f s (newtonIterate f a₀ n) := by
  sorry

/-- The valuation Newton form of Hensel's lemma, including the integral root condition. -/
theorem hensel_newton_form {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ)
    (A : Subring K) (hA : IsValuationSubring A v) (f : K[X])
    (hf : PolynomialCoefficientsInSubring A f) (a₀ : K) (ha₀ : a₀ ∈ A)
    (hineq : v (f.eval a₀) > v (f.derivative.eval a₀) + v (f.derivative.eval a₀))
    (hderiv : v (f.derivative.eval a₀) ≠ ⊤)
    (hcomplete : Chapter09NonarchimedeanComplete v)
    (hcofinal : Chapter09DoublingCofinal
      (valuationExcess v f (v (f.derivative.eval a₀)) a₀)) :
    ∃! a : K,
      a ∈ A ∧ f.eval a = 0 ∧
        v (a - a₀) > v (f.derivative.eval a₀) ∧
          v (a - a₀) = v (f.eval a₀) - v (f.derivative.eval a₀) := by
  sorry

/-- The exact displacement in the valuation Newton form of Hensel's lemma. -/
theorem hensel_newton_exact_displacement {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ)
    (A : Subring K) (hA : IsValuationSubring A v) (f : K[X])
    (hf : PolynomialCoefficientsInSubring A f) (a₀ : K) (ha₀ : a₀ ∈ A)
    (hineq : v (f.eval a₀) > v (f.derivative.eval a₀) + v (f.derivative.eval a₀))
    (hderiv : v (f.derivative.eval a₀) ≠ ⊤)
    (hcomplete : Chapter09NonarchimedeanComplete v)
    (hcofinal : Chapter09DoublingCofinal
      (valuationExcess v f (v (f.derivative.eval a₀)) a₀)) :
    ∃ a : K,
      a ∈ A ∧ f.eval a = 0 ∧
        v (a - a₀) = v (f.eval a₀) - v (f.derivative.eval a₀) := by
  sorry

/-- The Newton corrections tend to the top of the value group. -/
theorem valuation_newton_corrections_tend_to_top {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ)
    (A : Subring K) (hA : IsValuationSubring A v) (f : K[X])
    (hf : PolynomialCoefficientsInSubring A f) (a₀ : K) (ha₀ : a₀ ∈ A)
    (hineq : v (f.eval a₀) > v (f.derivative.eval a₀) + v (f.derivative.eval a₀))
    (hderiv : v (f.derivative.eval a₀) ≠ ⊤)
    (hcomplete : Chapter09NonarchimedeanComplete v)
    (hcofinal : Chapter09DoublingCofinal
      (valuationExcess v f (v (f.derivative.eval a₀)) a₀)) :
    TendsToTop (fun n => v (newtonIterate f a₀ (n + 1) - newtonIterate f a₀ n)) := by
  sorry

/-- The strict Newton inequality is the error being smaller than the square of the derivative. -/
def StrictNewtonCondition {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ)
    (f : K[X]) (a₀ : K) : Prop :=
  v (f.eval a₀) > v (f.derivative.eval a₀) + v (f.derivative.eval a₀)

/-- A residue approximation at which both the polynomial and derivative vanish. -/
def IsMultipleResidueApproximation {A : Type*} [CommRing A] [IsLocalRing A]
    (f : A[X]) (a₀ : A) : Prop :=
  f.eval a₀ ∈ IsLocalRing.maximalIdeal A ∧
    f.derivative.eval a₀ ∈ IsLocalRing.maximalIdeal A

/-- A multiple approximation can split into two distinct exact roots. -/
theorem quadratic_multiple_approximation_can_split {K : Type*} [Field K]
    (c : K) (hc : c ≠ 0) (hcneg : c ≠ -c) :
    quadraticPolynomial (c ^ 2) = (X - C c) * (X + C c) ∧
      (quadraticPolynomial (c ^ 2)).eval c = 0 ∧
      (quadraticPolynomial (c ^ 2)).eval (-c) = 0 ∧ c ≠ -c := by
  sorry

/-- The strict inequality in Theorem 9.2 cannot be dropped in general. -/
theorem strict_newton_condition_is_essential :
    ¬ StrictNewtonCondition (Padic.addValuation (p := 2))
        (quadraticPolynomial (2 : ℚ_[2])) 0 ∧
      ¬ ∃ x : ℚ_[2], x ^ 2 = (2 : ℚ_[2]) := by
  sorry

/-! ## 9.3 Lifting factorizations -/

/-- Approximate factorization modulo a power of the maximal ideal. -/
def ApproximateFactorization {A : Type*} [CommRing A] [IsLocalRing A]
    (f g h : A[X]) (n : ℕ) : Prop :=
  PolynomialCoefficientsInIdeal ((IsLocalRing.maximalIdeal A) ^ n) (f - g * h)

/-- The linear correction map `(r,s) ↦ r h + s g`. -/
def factorizationCorrectionMap {R : Type*} [CommRing R]
    (g h : R[X]) (rs : R[X] × R[X]) : R[X] :=
  rs.1 * h + rs.2 * g

/-- The bounded-degree coprime correction property used in Hensel factor lifting. -/
def CoprimeCorrectionProperty {R : Type*} [CommRing R]
    (g h : R[X]) : Prop :=
  ∀ t : R[X], t.degree < (g * h).degree →
    ∃! rs : R[X] × R[X],
      rs.1.degree < g.degree ∧ rs.2.degree < h.degree ∧
        factorizationCorrectionMap g h rs = t

/-- Coprimality gives the unique bounded-degree solution to the linear correction equation. -/
theorem coprime_correction_property {k : Type*} [Field k]
    {g h : k[X]} (hg : g.Monic) (hh : h.Monic) (hcop : IsCoprime g h) :
    CoprimeCorrectionProperty g h := by
  sorry

/-- One coefficientwise Hensel correction step, modulo `π^(n+1)`. -/
theorem hensel_factorization_step {A : Type*} [CommRing A] [IsDomain A]
    [CompleteDVR A] (f g h : A[X]) (g₀ h₀ : Polynomial (ResidueRing A))
    (π : A) (hπ : IsUniformizer π) (n : ℕ)
    (hf : f.Monic) (hg : g.Monic) (hh : h.Monic)
    (happrox : ApproximateFactorization f g h n)
    (hredg : residuePolynomial g = g₀) (hredh : residuePolynomial h = h₀)
    (hcop : IsCoprime g₀ h₀)
    (hred : residuePolynomial f = g₀ * h₀)
    (hn : 1 ≤ n) :
    ∃ r s : A[X],
      r.natDegree < g.natDegree ∧ s.natDegree < h.natDegree ∧
        ApproximateFactorization f
          (g + C (π ^ n) * r) (h + C (π ^ n) * s) (n + 1) := by
  sorry

/-- A pair of lifted factors with the prescribed reductions and degrees. -/
def IsFactorizationLift {A : Type*} [CommRing A] [IsLocalRing A]
    (f : A[X]) (g₀ h₀ : Polynomial (ResidueRing A)) (g h : A[X]) : Prop :=
  g.Monic ∧ h.Monic ∧
    g.natDegree = g₀.natDegree ∧ h.natDegree = h₀.natDegree ∧
    residuePolynomial g = g₀ ∧ residuePolynomial h = h₀ ∧ f = g * h

/-- Factorization-form Hensel lifting: the exact assertion of Theorem 9.3. -/
theorem hensel_factorization {A : Type*} [CommRing A] [IsDomain A]
    [CompleteDVR A] (f : A[X]) (g₀ h₀ : Polynomial (ResidueRing A))
    (hf : f.Monic) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcop : IsCoprime g₀ h₀)
    (hred : residuePolynomial f = g₀ * h₀) :
    ∃! gh : A[X] × A[X], IsFactorizationLift f g₀ h₀ gh.1 gh.2 := by
  sorry

/- Coefficientwise adic Cauchy condition for a sequence of polynomial factors. -/
def PolynomialAdicCauchy {A : Type*} [CommRing A] [IsLocalRing A]
    (s : ℕ → A[X]) : Prop :=
  ∀ d r : ℕ, ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
    (s m).coeff d - (s n).coeff d ∈
      (IsLocalRing.maximalIdeal A) ^ r

/-- Compatible coefficient corrections form Cauchy sequences in the DVR. -/
theorem hensel_factorization_coefficients_are_adic_cauchy
    {A : Type*} [CommRing A] [IsDomain A] [CompleteDVR A]
    {f : A[X]} {g₀ h₀ : Polynomial (ResidueRing A)}
    (hf : f.Monic) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcop : IsCoprime g₀ h₀) (hred : residuePolynomial f = g₀ * h₀) :
    ∃ g h : ℕ → A[X],
      (∀ n : ℕ,
        (g n).Monic ∧ (h n).Monic ∧
          (g n).natDegree = g₀.natDegree ∧
          (h n).natDegree = h₀.natDegree ∧
          residuePolynomial (g n) = g₀ ∧ residuePolynomial (h n) = h₀ ∧
          ApproximateFactorization f (g n) (h n) (n + 1)) ∧
      PolynomialAdicCauchy g ∧ PolynomialAdicCauchy h := by
  sorry

/-- The homogeneous first-precision correction equation proves uniqueness of factor lifts. -/
theorem hensel_factorization_unique_at_first_nonzero_precision
    {A : Type*} [CommRing A] [IsDomain A] [CompleteDVR A]
    {f : A[X]} {g₀ h₀ : Polynomial (ResidueRing A)}
    (hf : f.Monic) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcop : IsCoprime g₀ h₀) :
    ∀ gh₁ gh₂ : A[X] × A[X],
      IsFactorizationLift f g₀ h₀ gh₁.1 gh₁.2 →
      IsFactorizationLift f g₀ h₀ gh₂.1 gh₂.2 → gh₁ = gh₂ := by
  sorry

/-- A simple residue root is a linear factor and therefore lifts uniquely. -/
theorem monic_simple_residue_root_lifts {A : Type*} [CommRing A] [IsDomain A]
    [CompleteDVR A] (f : A[X]) (a₀ : ResidueRing A)
    (hf : f.Monic)
    (hroot : (residuePolynomial f).eval a₀ = 0)
    (hsimple : IsUnit ((residuePolynomial f).derivative.eval a₀)) :
    ∃! a : A, f.eval a = 0 ∧ residueClass a = a₀ := by
  sorry

/-- Pairwise coprime residue factors lift simultaneously. -/
def PairwiseCoprimeFamily {ι R : Type*} [CommRing R]
    (f : ι → R[X]) : Prop :=
  ∀ ⦃i j : ι⦄, i ≠ j → IsCoprime (f i) (f j)

/-- The simultaneous pairwise-coprime factor lifting consequence. -/
theorem hensel_lift_pairwise_coprime_factors {A ι : Type*} [CommRing A] [IsDomain A]
    [CompleteDVR A] [Fintype ι] (f : A[X]) (f₀ : ι → Polynomial (ResidueRing A))
    (hf : f.Monic) (hmonic : ∀ i, (f₀ i).Monic)
    (hpair : PairwiseCoprimeFamily f₀)
    (hred : residuePolynomial f = ∏ i, f₀ i) :
    ∃ lifts : ι → A[X],
      (∀ i, (lifts i).Monic ∧ (lifts i).natDegree = (f₀ i).natDegree ∧
        residuePolynomial (lifts i) = f₀ i) ∧
      f = ∏ i, lifts i := by
  sorry

/-- Residue-field factorization predicts a corresponding factorization upstairs. -/
theorem residue_factorization_predicts_complete_factorization
    {A : Type*} [CommRing A] [IsDomain A] [CompleteDVR A]
    (f : A[X]) (g₀ h₀ : Polynomial (ResidueRing A))
    (hf : f.Monic) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcop : IsCoprime g₀ h₀) (hred : residuePolynomial f = g₀ * h₀) :
    ∃ g h : A[X], IsFactorizationLift f g₀ h₀ g h := by
  sorry

/-! ## 9.4 Henselian local rings -/

/-- Chapter-specific name for Mathlib's henselian local-ring class. -/
def IsHenselianLocalRingChapter09 (A : Type*) [CommRing A] : Prop :=
  HenselianLocalRing A

/-- The simple-residue-root lifting property. -/
def SimpleResidueRootLiftingProperty (A : Type*) [CommRing A] [IsLocalRing A] : Prop :=
  ∀ (f : A[X]) (a₀ : ResidueRing A), f.Monic →
    (residuePolynomial f).eval a₀ = 0 →
    IsUnit ((residuePolynomial f).derivative.eval a₀) →
    ∃! a : A, f.eval a = 0 ∧ residueClass a = a₀

/-- The coprime-factorization lifting property. -/
def HenselianFactorizationProperty (A : Type*) [CommRing A] [IsLocalRing A] : Prop :=
  ∀ (f : A[X]) (g₀ h₀ : Polynomial (ResidueRing A)), f.Monic →
    g₀.Monic → h₀.Monic → IsCoprime g₀ h₀ → residuePolynomial f = g₀ * h₀ →
    ∃! gh : A[X] × A[X], IsFactorizationLift f g₀ h₀ gh.1 gh.2

/-- A simple root is the linear factor `X-ā`. -/
theorem simple_residue_root_iff_linear_factor {A : Type*} [CommRing A] [IsLocalRing A]
    (f : A[X]) (a₀ : ResidueRing A) :
    (residuePolynomial f).eval a₀ = 0 ↔
      ∃ q : Polynomial (ResidueRing A),
        residuePolynomial f = (X - C a₀) * q := by
  sorry

/-- Lifting factors one at a time reduces the factorization property to simple roots. -/
theorem henselian_factorization_by_successive_linear_lifts
    {A : Type*} [CommRing A] [IsLocalRing A]
    (hroot : SimpleResidueRootLiftingProperty A) :
    HenselianFactorizationProperty A := by
  sorry

/-- Conversely, a factorization lift applied to `X-ā` gives simple-root lifting. -/
theorem simple_root_lifting_by_linear_factorization
    {A : Type*} [CommRing A] [IsLocalRing A]
    (hfactor : HenselianFactorizationProperty A) :
    SimpleResidueRootLiftingProperty A := by
  sorry

/-- Factorization and simple-root definitions of henselianity are equivalent. -/
theorem henselian_iff_simple_residue_root_lifting {A : Type*} [CommRing A]
    [IsLocalRing A] :
    IsHenselianLocalRingChapter09 A ↔ SimpleResidueRootLiftingProperty A := by
  sorry

/-- Complete and separated maximal-ideal-adic local rings. -/
def IsMaximalIdealAdicallyCompleteSeparated (A : Type*) [CommRing A] [IsLocalRing A] : Prop :=
  IsAdicComplete (IsLocalRing.maximalIdeal A) A

/-- Completeness and separatedness imply henselianity. -/
theorem complete_separated_local_ring_is_henselian {A : Type*} [CommRing A]
    [IsLocalRing A] (hA : IsMaximalIdealAdicallyCompleteSeparated A) :
    IsHenselianLocalRingChapter09 A := by
  sorry

/-- Complete DVRs are henselian. -/
theorem complete_DVR_is_henselian {A : Type*} [CommRing A] [IsDomain A]
    [CompleteDVR A] : IsHenselianLocalRingChapter09 A := by
  sorry

/-- The algebraic property of being henselian without the topological completeness property. -/
def IsHenselianButNotComplete (A : Type*) [CommRing A] [IsLocalRing A] : Prop :=
  HenselianLocalRing A ∧ ¬ IsMaximalIdealAdicallyCompleteSeparated A

/-- A henselian DVR need not be complete; this records an actual example interface. -/
structure Chapter09HenselianNoncompleteDVRExample where
  A : Type*
  [commRing : CommRing A]
  [domain : IsDomain A]
  [dvr : IsDiscreteValuationRing A]
  henselian : IsHenselianLocalRingChapter09 A
  not_adically_complete : ¬ IsMaximalIdealAdicallyCompleteSeparated A

theorem henselian_DVR_need_not_be_complete :
    Nonempty Chapter09HenselianNoncompleteDVRExample := by
  sorry
/-- A minimal local interface for the henselization of a local ring. -/
def IsHenselizationOf {A H : Type*} [CommRing A] [IsLocalRing A]
    [CommRing H] [IsLocalRing H] [Algebra A H] : Prop :=
  HenselianLocalRing H ∧ IsLocalHom (algebraMap A H) ∧
    Function.Injective (algebraMap A H) ∧
    (∀ x : H, IsIntegral A x) ∧
    ∀ (B : Type*) [CommRing B] [IsLocalRing B] [Algebra A B]
      [HenselianLocalRing B],
      ∃! φ : H →+* B, IsLocalHom φ ∧ φ.comp (algebraMap A H) = algebraMap A B
/-- The universal-property part of henselization: maps to henselian local rings are unique. -/
def HasHenselizationUniversalProperty {A H : Type*} [CommRing A] [IsLocalRing A]
    [CommRing H] [IsLocalRing H] [Algebra A H] : Prop :=
  ∀ (B : Type*) [CommRing B] [IsLocalRing B] [Algebra A B]
    [HenselianLocalRing B],
    ∃! φ : H →+* B, IsLocalHom φ ∧ φ.comp (algebraMap A H) = algebraMap A B

/-- An adic completion interface, kept abstract so the chapter remains self-contained. -/
def IsAdicCompletionOf {A C : Type*} [CommRing A] [IsLocalRing A]
    [CommRing C] [Algebra A C] : Prop :=
  IsAdicComplete (IsLocalRing.maximalIdeal A) C ∧
    Function.Injective (algebraMap A C)
    ∧ ∀ (B : Type*) [CommRing B] [IsLocalRing B] [Algebra A B]
      [IsAdicComplete
        ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) B],
      ∃! φ : C →+* B, IsLocalHom φ ∧ φ.comp (algebraMap A C) = algebraMap A B

/-- A strict embedding records that an algebraic henselization can be smaller than its completion. -/
def IsStrictRingEmbedding {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    (φ : R →+* S) : Prop :=
  Function.Injective φ ∧ ¬ Function.Surjective φ

/-- Henselization elements are algebraic over the original local ring. -/
theorem henselization_adds_algebraic_solutions {A H : Type*} [CommRing A] [IsLocalRing A]
    [CommRing H] [IsLocalRing H] [Algebra A H]
    (hH : IsHenselizationOf (A := A) (H := H)) :
    HenselianLocalRing H ∧ ∀ x : H, IsIntegral A x := by
  sorry

/-- The henselization/completion comparison can be strict, expressing algebraic versus topological size. -/
theorem henselization_can_be_strictly_smaller_than_completion
    {A H C : Type*} [CommRing A] [IsLocalRing A]
    [CommRing H] [IsLocalRing H] [Algebra A H]
    [CommRing C] [Algebra A C]
    (hH : IsHenselizationOf (A := A) (H := H))
    (hC : IsAdicCompletionOf (A := A) (C := C))
    (hnotH : ¬ IsMaximalIdealAdicallyCompleteSeparated H) :
    ∃ φ : H →+* C, IsStrictRingEmbedding φ := by
  sorry

/-! ## 9.5 Worked lifts -/

/-- A unit has a square residue in `𝔽_p` when its residue is a square. -/
def PadicUnitResidueSquare (p : ℕ) [Fact p.Prime] (u : ℤ_[p]) : Prop :=
  IsUnit u ∧ ∃ z : ZMod p, z ^ 2 = PadicInt.toZMod u

/-- For odd `p`, a p-adic unit is a square exactly when its residue is a square. -/
theorem odd_padic_unit_square_iff_residue_square (p : ℕ) [Fact p.Prime]
    (hpodd : p ≠ 2) (u : ℤ_[p]) (hu : IsUnit u) :
    (∃ a : ℤ_[p], a ^ 2 = u) ↔
      ∃ z : ZMod p, z ^ 2 = PadicInt.toZMod u := by
  sorry

/-- At odd residue characteristic, the derivative `2a₀` is a unit at a unit point. -/
theorem odd_padic_square_derivative_is_unit (p : ℕ) [Fact p.Prime]
    (hpodd : p ≠ 2) (a₀ : ℤ_[p]) (ha₀ : IsUnit a₀) :
    IsUnit ((2 : ℤ_[p]) * a₀) := by
  sorry

/-- A chosen square residue root has a unique p-adic square-root lift. -/
theorem odd_padic_square_simple_lift (p : ℕ) [Fact p.Prime]
    (hpodd : p ≠ 2) (u a₀ : ℤ_[p]) (hu : IsUnit u)
    (hroot : (PadicInt.toZMod a₀) ^ 2 = PadicInt.toZMod u) :
    ∃! a : ℤ_[p], a ^ 2 = u ∧ PadicInt.toZMod a = PadicInt.toZMod a₀ := by
  sorry

/-- For odd `p`, the two residue roots give the two square roots overall. -/
theorem odd_padic_square_has_two_roots (p : ℕ) [Fact p.Prime]
    (hpodd : p ≠ 2) (u : ℤ_[p]) (hu : IsUnit u)
    (hres : ∃ z : ZMod p, z ^ 2 = PadicInt.toZMod u) :
    ∃ aPlus aMinus : ℤ_[p],
      aPlus ^ 2 = u ∧ aMinus ^ 2 = u ∧ aPlus ≠ aMinus ∧
        ∀ a : ℤ_[p], a ^ 2 = u → a = aPlus ∨ a = aMinus := by
  sorry

/-- The polynomial and first approximation in the numerical `u=2` example over `ℤ₇`. -/
def padicSevenPolynomial : (ℤ_[7])[X] :=
  quadraticPolynomial (2 : ℤ_[7])

def padicSevenInitialApproximation : ℤ_[7] :=
  3

def padicSevenFirstNewtonApproximation : ℤ_[7] :=
  3 - (7 : ℤ_[7]) * Ring.inverse (6 : ℤ_[7])

/-- The first Newton approximation agrees with `3-7/6`. -/
theorem padicSeven_first_newton_formula :
    padicSevenFirstNewtonApproximation =
      newtonCorrection padicSevenPolynomial padicSevenInitialApproximation := by
  sorry

/-- The inverse of six modulo forty-nine is forty-one. -/
theorem inverse_six_mod_49 : (6 : ZMod 49) * 41 = 1 := by
  sorry

/-- The first approximation is `10` modulo `49`. -/
theorem padicSeven_first_approximation_mod_49 :
    PadicInt.toZModPow 2 padicSevenFirstNewtonApproximation = (10 : ZMod (7 ^ 2)) := by
  sorry

/-- Indeed `10²=2` modulo `49`. -/
theorem padicSeven_square_mod_49 :
    (10 : ZMod 49) ^ 2 = 2 := by
  sorry

/-- The next Newton step has fourth-power precision, reflecting valuation doubling. -/
def padicSevenSecondNewtonApproximation : ℤ_[7] :=
  newtonCorrection padicSevenPolynomial padicSevenFirstNewtonApproximation

def IsRootModuloPower {A : Type*} [CommRing A] (π : A) (f : A[X]) (a : A) (n : ℕ) : Prop :=
  f.eval a ∈ Ideal.span ({π ^ n} : Set A)

/-- The second numerical correction determines the root modulo `7⁴`, not only `7³`. -/
theorem padicSeven_second_newton_precision :
    IsRootModuloPower (7 : ℤ_[7]) padicSevenPolynomial
      padicSevenSecondNewtonApproximation 4 := by
  sorry

/-- At `p=2`, the derivative of `X²-u` is never a unit at a unit. -/
theorem two_adic_square_derivative_never_unit (a : ℤ_[2]) (ha : IsUnit a) :
    ¬ IsUnit ((2 : ℤ_[2]) * a) := by
  sorry

/-- Being congruent to one modulo eight is the strengthened two-adic Newton condition. -/
theorem two_adic_one_mod_eight_gives_newton_condition (u : ℤ_[2])
    (hu : PadicInt.toZModPow 3 u = 1) :
    Padic.addValuation (p := 2) (1 - (u : ℚ_[2])) ≥ (3 : WithTop ℤ) ∧
      Padic.addValuation (p := 2) (2 : ℚ_[2]) = (1 : WithTop ℤ) ∧
      Padic.addValuation (p := 2) (1 - (u : ℚ_[2])) >
        Padic.addValuation (p := 2) (2 : ℚ_[2]) +
          Padic.addValuation (p := 2) (2 : ℚ_[2]) := by
  sorry

/-- Every `2`-adic unit congruent to one modulo eight is a square. -/
theorem two_adic_unit_square_of_one_mod_eight (u : ℤ_[2])
    (hu : PadicInt.toZModPow 3 u = 1) :
    ∃ a : ℤ_[2], a ^ 2 = u := by
  sorry

/-- The polynomial and first Newton iterate in the `u=17` two-adic example. -/
def padicTwoSeventeenPolynomial : (ℚ_[2])[X] :=
  quadraticPolynomial (17 : ℚ_[2])

def padicTwoSeventeenFirstNewtonApproximation : ℚ_[2] :=
  1 - ((-16 : ℚ_[2]) / (2 : ℚ_[2]))

/-- For `f=X²-17`, the initial error and derivative have values four and one. -/
theorem padicTwoSeventeen_initial_values :
    Padic.addValuation (p := 2) (padicTwoSeventeenPolynomial.eval 1) = (4 : WithTop ℤ) ∧
      Padic.addValuation (p := 2)
          (padicTwoSeventeenPolynomial.derivative.eval 1) = (1 : WithTop ℤ) := by
  sorry

/-- The first Newton iterate is nine, and its new error is sixty-four of value six. -/
theorem padicTwoSeventeen_first_iterate_and_error :
    padicTwoSeventeenFirstNewtonApproximation = 9 ∧
      padicTwoSeventeenPolynomial.eval padicTwoSeventeenFirstNewtonApproximation = 64 ∧
      Padic.addValuation (p := 2)
          (padicTwoSeventeenPolynomial.eval padicTwoSeventeenFirstNewtonApproximation) =
        (6 : WithTop ℤ) := by
  sorry

/-- The lifted root has displacement of value three from one, matching the first correction. -/
theorem padicTwoSeventeen_lifted_root_displacement :
    ∃ a : ℚ_[2], padicTwoSeventeenPolynomial.eval a = 0 ∧
      Padic.addValuation (p := 2) (a - 1) = (3 : WithTop ℤ) := by
  sorry

/-- The Artin--Schreier polynomial `X^p-X-a`. -/
def artinSchreierPolynomial {A : Type*} [CommRing A] (p : ℕ) (a : A) : A[X] :=
  X ^ p - X - C a

/-- The Artin--Schreier polynomial is monic for positive residue characteristic. -/
theorem artinSchreierPolynomial_monic {A : Type*} [CommRing A]
    (p : ℕ) (hp : p ≠ 0) (a : A) :
    (artinSchreierPolynomial p a).Monic := by
  sorry

/-- In residue characteristic `p`, the derivative of `X^p-X-a` is a unit. -/
theorem artinSchreier_derivative_is_unit {A : Type*} [CommRing A] [IsLocalRing A]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueRing A) p] (a x : A) :
    IsUnit ((artinSchreierPolynomial p a).derivative.eval x) := by
  sorry

/-- Every residue root of `X^p-X-a` lifts uniquely over a complete DVR. -/
theorem artinSchreier_every_residue_root_lifts {A : Type*} [CommRing A] [IsDomain A]
    [CompleteDVR A] (p : ℕ) [Fact p.Prime] [CharP (ResidueRing A) p]
    (a : A) (x₀ : ResidueRing A)
    (hroot : (residuePolynomial (artinSchreierPolynomial p a)).eval x₀ = 0) :
    ∃! x : A,
      (artinSchreierPolynomial p a).eval x = 0 ∧ residueClass x = x₀ := by
  sorry

/-- The Artin--Schreier calculation is the simple-root, unramified-style lifting test. -/
theorem artinSchreier_simple_root_separates_unramified_behavior {A : Type*}
    [CommRing A] [IsLocalRing A] (p : ℕ) [Fact p.Prime]
    [CharP (ResidueRing A) p] (a x : A) :
    IsUnit ((artinSchreierPolynomial p a).derivative.eval x) := by
  sorry

/-! ## 9.6 Algebraic consequences -/

/-- A polynomial has a repeated residue root when it and its derivative vanish there. -/
def HasRepeatedResidueRoot {R : Type*} [CommRing R] (f : R[X]) : Prop :=
  ∃ a : R, f.eval a = 0 ∧ f.derivative.eval a = 0

/-- Coefficients of a polynomial are integral over a base ring. -/
def PolynomialCoefficientsIntegralOver {A K : Type*} [CommRing A] [CommRing K]
    [Algebra A K] (f : K[X]) : Prop :=
  ∀ n : ℕ, IsIntegral A (f.coeff n)

/-- A monic factor of a monic polynomial over a fraction field has integral coefficients. -/
theorem monic_factor_coefficients_are_integral {A K : Type*} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K]
    (f : A[X]) (g h : K[X]) (hf : f.Monic) (hg : g.Monic) (hh : h.Monic)
    (hfac : Polynomial.map (algebraMap A K) f = g * h) :
    PolynomialCoefficientsIntegralOver (A := A) (K := K) g ∧ PolynomialCoefficientsIntegralOver (A := A) (K := K) h := by
  sorry

/-- Integral closedness descends a monic factorization from the fraction field to the DVR. -/
theorem monic_factorization_descends_to_integrally_closed_domain
    {A K : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (f : A[X]) (g h : K[X]) (hf : f.Monic) (hg : g.Monic) (hh : h.Monic)
    (hfac : Polynomial.map (algebraMap A K) f = g * h) :
    ∃ gA hA : A[X],
      gA.Monic ∧ hA.Monic ∧
        Polynomial.map (algebraMap A K) gA = g ∧
        Polynomial.map (algebraMap A K) hA = h ∧ f = gA * hA := by
  sorry

/-- A monic polynomial with irreducible reduction is irreducible over the fraction field. -/
theorem irreducible_of_irreducible_residue_reduction
    {A K : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K]
    (f : A[X]) (hf : f.Monic)
    (hred : Irreducible (residuePolynomial f)) :
    Irreducible (Polynomial.map (algebraMap A K) f) := by
  sorry

/-- The irreducibility argument works for any integrally closed local domain, not only a DVR. -/
theorem irreducible_reduction_argument_for_integrally_closed_local_domain
    {A K : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K]
    (f : A[X]) (hf : f.Monic)
    (hred : Irreducible (residuePolynomial f)) :
    Irreducible (Polynomial.map (algebraMap A K) f) := by
  sorry

/-- The converse fails: an irreducible polynomial can acquire a repeated reduction. -/
theorem padic_x_sq_sub_p_irreducible_but_reduction_repeated (p : ℕ) [Fact p.Prime] :
    Irreducible
        (Polynomial.map (algebraMap (ℤ_[p]) (ℚ_[p]))
          (quadraticPolynomial (p : ℤ_[p]))) ∧
      HasRepeatedResidueRoot (quadraticPolynomial (p : ZMod p)) := by
  sorry

/-- Henselianity is the hypothesis needed to lift a coprime residue factorization. -/
theorem henselianity_lifts_coprime_residue_factorization
    {A : Type*} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    (f : A[X]) (g₀ h₀ : Polynomial (ResidueRing A))
    (hf : f.Monic) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcop : IsCoprime g₀ h₀) (hred : residuePolynomial f = g₀ * h₀) :
    ∃! gh : A[X] × A[X], IsFactorizationLift f g₀ h₀ gh.1 gh.2 := by
  sorry

/-- A prime of an extension ring lying above the maximal ideal. -/
def PrimeAboveMaximal {A B : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B] (P : Ideal B) : Prop :=
  P.IsPrime ∧ P.comap (algebraMap A B) = IsLocalRing.maximalIdeal A

/-- A valuation on `L` extends the valuation on `K` up to Mathlib's equivalence relation. -/
def IsValuationExtension {K L ΓK ΓL : Type*} [Field K] [Field L]
    [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL]
    [Algebra K L]
    (vK : Valuation K ΓK) (vL : Valuation L ΓL) : Prop :=
  vK.IsEquiv (vL.comap (algebraMap K L))

/- A valuation extension may require a genuinely larger ordered value group. -/
structure Chapter09ValuationExtension
    {K : Type uK} {L : Type uL} {ΓK : Type uΓ} [Field K] [Field L]
    [LinearOrderedCommGroupWithZero ΓK] [Algebra K L]
    (vK : Valuation K ΓK) where
  ΓL : Type (max (max uK uL) uΓ)
  [valueGroup : LinearOrderedCommGroupWithZero ΓL]
  valuation : Valuation L ΓL
  isExtension : IsValuationExtension vK valuation

def Chapter09ValuationExtensionEquivalent
    {K L ΓK : Type*} [Field K] [Field L]
    [LinearOrderedCommGroupWithZero ΓK] [Algebra K L]
    (vK : Valuation K ΓK)
    (w₁ w₂ : Chapter09ValuationExtension (L := L) vK) : Prop := by
  letI := w₁.valueGroup
  letI := w₂.valueGroup
  exact w₁.valuation.IsEquiv w₂.valuation

def Chapter09ValuationExtensionSetoid
    {K L ΓK : Type*} [Field K] [Field L]
    [LinearOrderedCommGroupWithZero ΓK] [Algebra K L]
    (vK : Valuation K ΓK) : Setoid (Chapter09ValuationExtension (L := L) vK) where
  r := Chapter09ValuationExtensionEquivalent (L := L) vK
  iseqv := by sorry

abbrev Chapter09ValuationExtensionClass
    {K L ΓK : Type*} [Field K] [Field L]
    [LinearOrderedCommGroupWithZero ΓK] [Algebra K L]
    (vK : Valuation K ΓK) : Type _ :=
  Quotient (Chapter09ValuationExtensionSetoid (L := L) vK)
/-- The prime/valuation correspondence, expressed as an equivalence of the two parameter spaces. -/
def ExtensionPrimeCorrespondence {A B K L ΓK : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B] [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK] (vK : Valuation K ΓK) : Prop :=
  Nonempty
    ((Chapter09ValuationExtensionClass (L := L) vK ≃
        {P : Ideal B // PrimeAboveMaximal (A := A) (B := B) P}))

/-- There is exactly one extension valuation in the chosen value group. -/
def HasUniqueValuationExtension {K L ΓK : Type*} [Field K] [Field L]
    [LinearOrderedCommGroupWithZero ΓK] [Algebra K L]
    (vK : Valuation K ΓK) : Prop :=
  ∃ w : Chapter09ValuationExtension (L := L) vK,
    ∀ w' : Chapter09ValuationExtension (L := L) vK,
      Chapter09ValuationExtensionEquivalent (L := L) vK w w'

/-- There is exactly one prime of the extension ring above the maximal ideal. -/
def HasUniquePrimeAbove {A B : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B] : Prop :=
  ∃! P : Ideal B, PrimeAboveMaximal (A := A) (B := B) P

/-- A valued field is henselian when its valuation ring is a henselian local ring. -/
def IsHenselianValuedField {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (vK : Valuation K Γ) : Prop :=
  HenselianLocalRing vK.valuationSubring

/-- For a finite extension, primes above the maximal ideal correspond to valuation extensions. -/
theorem finite_extension_prime_valuation_correspondence
    {A B K L Γ : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    [ValuationRing A] [IsIntegrallyClosed A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra A L] [IsScalarTower A K L]
    [CommRing B] [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    [LinearOrderedCommGroupWithZero Γ] (vK : Valuation K Γ) :
    ExtensionPrimeCorrespondence (A := A) (B := B) (L := L) vK := by
  sorry

/-- The correspondence transfers uniqueness of a prime to uniqueness of the extension valuation. -/
theorem unique_prime_iff_unique_valuation_extension
    {A B K L Γ : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B] [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ] (vK : Valuation K Γ)
    (hcor : ExtensionPrimeCorrespondence (A := A) (B := B) (L := L) vK) :
    HasUniquePrimeAbove (A := A) (B := B) ↔
      HasUniqueValuationExtension (L := L) vK := by
  sorry

/-- A henselian valued field has one prime above the maximal ideal in every finite extension. -/
theorem henselian_valued_field_has_unique_prime_and_extension
    {A B K L Γ : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    [ValuationRing A] [IsIntegrallyClosed A]
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra A K] [IsFractionRing A K]
    [CommRing B] [Algebra A B] [Algebra B L]
    [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    [LinearOrderedCommGroupWithZero Γ] (vK : Valuation K Γ)
    (hH : IsHenselianValuedField vK)
    (hcor : ExtensionPrimeCorrespondence (A := A) (B := B) (L := L) vK) :
    HasUniquePrimeAbove (A := A) (B := B) ∧ HasUniqueValuationExtension (L := L) vK := by
  sorry

/-- The finite integral extension has a finite nonempty set of primes above the maximal ideal. -/
theorem finite_extension_primes_above_are_finite
    {A B : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]
    [IsIntegralClosure B A B] :
    Set.Finite {P : Ideal B | PrimeAboveMaximal (A := A) (B := B) P} ∧
      Nonempty {P : Ideal B // PrimeAboveMaximal (A := A) (B := B) P} := by
  sorry

/-- Adic completeness of the valuation ring implies henselianity of the valued field. -/
theorem complete_valued_field_is_henselian
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ)
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal vK.valuationSubring)
      vK.valuationSubring) :
    IsHenselianValuedField vK := by
  sorry

end
end Chapter09
end ValuationsBook
