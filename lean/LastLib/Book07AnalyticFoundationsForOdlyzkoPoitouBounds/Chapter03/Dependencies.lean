import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03

noncomputable section

open NumberField IsDedekindDomain
open scoped BigOperators nonZeroDivisors

/-!
Shared interfaces for Chapter 3.  The analytic functions below are thin
book-facing wrappers around Mathlib's `NumberField.dedekindZeta` and the
canonical ideal and height-one-spectrum constructions.
-/

/-- The degree of a number field over `ℚ`. -/
abbrev chapter03Degree (K : Type*) [Field K] [NumberField K] : ℕ :=
  Module.finrank ℚ K

/-- The type of nonzero integral ideals of a number field. -/
abbrev Chapter03IntegralIdeal (K : Type*) [Field K] [NumberField K] : Type _ :=
  (Ideal (𝓞 K))⁰

/-- The type of nonzero prime ideals of the ring of integers. -/
abbrev Chapter03PrimeIdeal (K : Type*) [Field K] [NumberField K] : Type _ :=
  IsDedekindDomain.HeightOneSpectrum (𝓞 K)

/-- A prime-power index consists of a prime ideal and a positive exponent. -/
abbrev Chapter03PrimePower (K : Type*) [Field K] [NumberField K] : Type _ :=
  Chapter03PrimeIdeal K × ℕ

/-- The absolute norm of an integral ideal, in the canonical `ℕ` normalization. -/
def chapter03AbsoluteIdealNorm {K : Type*} [Field K] [NumberField K]
    (I : Ideal (𝓞 K)) : ℕ :=
  Ideal.absNorm I

/-- The norm of a nonzero integral ideal. -/
def chapter03IdealNorm {K : Type*} [Field K] [NumberField K]
    (I : Chapter03IntegralIdeal K) : ℕ :=
  chapter03AbsoluteIdealNorm (I : Ideal (𝓞 K))

theorem chapter03_ideal_norm_coe {K : Type*} [Field K] [NumberField K]
    (I : Chapter03IntegralIdeal K) :
    chapter03IdealNorm I = Ideal.absNorm (I : Ideal (𝓞 K)) :=
  rfl

/-- The Euler half-plane `Re(s) > 1`. -/
def chapter03EulerHalfPlane : Set ℂ :=
  {s | (1 : ℝ) < s.re}

/-- The closed half-plane used for a fixed positive convergence margin. -/
def chapter03EulerHalfPlaneClosed (ε : ℝ) : Set ℂ :=
  {s | (1 : ℝ) + ε ≤ s.re}

theorem chapter03_mem_euler_half_plane_iff {s : ℂ} :
    s ∈ chapter03EulerHalfPlane ↔ (1 : ℝ) < s.re :=
  Iff.rfl

theorem chapter03_mem_euler_half_plane_closed_iff {ε : ℝ} {s : ℂ} :
    s ∈ chapter03EulerHalfPlaneClosed ε ↔ (1 : ℝ) + ε ≤ s.re :=
  Iff.rfl

/-- The Dedekind zeta function, using Mathlib's coefficient-series construction. -/
def chapter03DedekindZeta (K : Type*) [Field K] [NumberField K] : ℂ → ℂ :=
  NumberField.dedekindZeta K

/-- The ideal-series summand `(N I)^(-s)`. -/
def chapter03IdealTerm {K : Type*} [Field K] [NumberField K]
    (s : ℂ) (I : Chapter03IntegralIdeal K) : ℂ :=
  (chapter03IdealNorm I : ℂ) ^ (-s)

/-- The ideal Dirichlet series for the Dedekind zeta function. -/
def chapter03IdealSeries (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  ∑' I : Chapter03IntegralIdeal K, chapter03IdealTerm s I

/-- The derivative summand for the ideal series. -/
def chapter03IdealTermDerivative {K : Type*} [Field K] [NumberField K]
    (s : ℂ) (I : Chapter03IntegralIdeal K) : ℂ :=
  -(Real.log (chapter03IdealNorm I : ℝ) : ℂ) * chapter03IdealTerm s I

/-- The norm of a height-one prime ideal. -/
def chapter03PrimeIdealNorm {K : Type*} [Field K] [NumberField K]
    (P : Chapter03PrimeIdeal K) : ℕ :=
  chapter03AbsoluteIdealNorm P.asIdeal

theorem chapter03_prime_ideal_norm_asIdeal {K : Type*} [Field K] [NumberField K]
    (P : Chapter03PrimeIdeal K) :
    chapter03PrimeIdealNorm P = Ideal.absNorm P.asIdeal :=
  rfl

theorem chapter03_prime_ideal_isPrime {K : Type*} [Field K] [NumberField K]
    (P : Chapter03PrimeIdeal K) : P.asIdeal.IsPrime :=
  P.isPrime

theorem chapter03_prime_ideal_ne_bot {K : Type*} [Field K] [NumberField K]
    (P : Chapter03PrimeIdeal K) : P.asIdeal ≠ ⊥ :=
  P.ne_bot

/-- The Euler factor attached to a height-one prime. -/
def chapter03EulerFactor {K : Type*} [Field K] [NumberField K]
    (P : Chapter03PrimeIdeal K) (s : ℂ) : ℂ :=
  (1 - (chapter03PrimeIdealNorm P : ℂ) ^ (-s))⁻¹

/-- The Euler product indexed by the nonzero prime ideals. -/
def chapter03EulerProduct (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  ∏' P : Chapter03PrimeIdeal K, chapter03EulerFactor P s

/-- The real Euler factor used in the comparison with the rational zeta function. -/
def chapter03RealEulerFactor {K : Type*} [Field K] [NumberField K]
    (P : Chapter03PrimeIdeal K) (σ : ℝ) : ℝ :=
  (1 - Real.rpow (chapter03PrimeIdealNorm P : ℝ) (-σ))⁻¹

/-- The real-valued Euler product over prime ideals. -/
def chapter03RealEulerProduct (K : Type*) [Field K] [NumberField K] (σ : ℝ) : ℝ :=
  ∏' P : Chapter03PrimeIdeal K, chapter03RealEulerFactor P σ

/-- The rational Euler product, indexed by the canonical type of natural primes. -/
def chapter03RationalPrimeEulerProduct (σ : ℝ) : ℝ :=
  ∏' p : Nat.Primes, (1 - Real.rpow (p : ℝ) (-σ))⁻¹

/-- The real value of Mathlib's Riemann zeta function. -/
def chapter03RiemannZetaOnReal (σ : ℝ) : ℝ :=
  (riemannZeta (σ : ℂ)).re

/-- The `m`th (`m + 1` in zero-based Lean indexing) logarithmic Euler term. -/
def chapter03EulerLogTerm {K : Type*} [Field K] [NumberField K]
    (P : Chapter03PrimeIdeal K) (m : ℕ) (s : ℂ) : ℂ :=
  (chapter03PrimeIdealNorm P : ℂ) ^ (-((m + 1 : ℕ) : ℂ) * s) /
    ((m + 1 : ℕ) : ℂ)

/-- The absolutely convergent Euler logarithm, without choosing a branch of `log`. -/
def chapter03EulerLogSeries (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  ∑' P : Chapter03PrimeIdeal K, ∑' m : ℕ, chapter03EulerLogTerm P m s

/-- The logarithmic-derivative summand at a prime power. -/
def chapter03LogDerivativeTerm {K : Type*} [Field K] [NumberField K]
    (q : Chapter03PrimePower K) (s : ℂ) : ℂ :=
  (Real.log (chapter03PrimeIdealNorm q.1 : ℝ) : ℂ) *
    (chapter03PrimeIdealNorm q.1 : ℂ) ^ (-((q.2 + 1 : ℕ) : ℂ) * s)

/-- The prime-power series used for the logarithmic derivative. -/
def chapter03LogDerivativeSeries (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  ∑' P : Chapter03PrimeIdeal K, ∑' m : ℕ, chapter03LogDerivativeTerm (P, m) s

/-- The real weight attached to a prime power and a test function. -/
def chapter03WeightedPrimePowerTerm {K : Type*} [Field K] [NumberField K]
    (F : ℝ → ℝ) (q : Chapter03PrimePower K) : ℝ :=
  Real.log (chapter03PrimeIdealNorm q.1 : ℝ) *
    F (((q.2 + 1 : ℕ) : ℝ) * Real.log (chapter03PrimeIdealNorm q.1 : ℝ))

/-- Support containment in the interval `[-T,T]`. -/
def chapter03SupportWithin (F : ℝ → ℝ) (T : ℝ) : Prop :=
  Function.support F ⊆ Set.Icc (-T) T

/-- The rational prime ideal below a prime of `K`, expressed as a prime-over set. -/
def chapter03PrimeIdealsOverNatPrime {K : Type*} [Field K] [NumberField K]
    (p : ℕ) : Set (Ideal (𝓞 K)) :=
  Ideal.primesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 K)

theorem chapter03_mem_prime_ideals_over_nat_prime_iff
    {K : Type*} [Field K] [NumberField K] {p : ℕ}
    (P : Ideal (𝓞 K)) :
    P ∈ chapter03PrimeIdealsOverNatPrime (K := K) p ↔
      P.IsPrime ∧ P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) :=
  Iff.rfl

def chapter03PrimeIdealOfPrime
    {K : Type*} [Field K] [NumberField K]
    (P : Ideal (𝓞 K)) (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    Chapter03PrimeIdeal K :=
  ⟨P, hP, hP0⟩

theorem chapter03PrimeIdealOfPrime_asIdeal
    {K : Type*} [Field K] [NumberField K]
    (P : Ideal (𝓞 K)) (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    (chapter03PrimeIdealOfPrime P hP hP0).asIdeal = P :=
  rfl

theorem chapter03_prime_ideal_ext
    {K : Type*} [Field K] [NumberField K]
    (P Q : Chapter03PrimeIdeal K) (hPQ : P.asIdeal = Q.asIdeal) : P = Q :=
  IsDedekindDomain.HeightOneSpectrum.ext hPQ

/-- The Gaussian-field predicate used for the explicit `ℚ(i)` example. -/
def chapter03IsGaussianField (K : Type*) [Field K] [NumberField K] : Prop :=
  ∃ ι : K, ι ^ 2 = -1 ∧ Algebra.adjoin ℚ ({ι} : Set K) = ⊤

/-- The first-power contribution of a prime ideal to a logarithmic derivative. -/
def chapter03FirstPowerPrimeIdealTerm {K : Type*} [Field K] [NumberField K]
    (P : Ideal (𝓞 K)) (s : ℂ) : ℂ :=
  (Real.log (Ideal.absNorm P : ℝ) : ℂ) *
    (Ideal.absNorm P : ℂ) ^ (-s)

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03
