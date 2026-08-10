import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.FractionalIdeal.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.HahnSeries.Basic
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter01

open scoped Polynomial RatFunc nonZeroDivisors
open Set Function Ideal
open scoped BigOperators

noncomputable section

/-! # Chapter 1: Measuring vanishing

This file is a statement-generation pass for Chapter 1 of *Valuations, DVRs, and
Completions*.  The declarations below follow Sections 1.1--1.5 in order. -/

/-! # Book 1, Chapter 1, Section 1.1: A Local Question
-/

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
    Nonempty (ZeroOrderFactorization f) := by
  classical
  rcases WfDvdMonoid.max_power_factor hf (Polynomial.prime_X.irreducible : Irreducible (Polynomial.X : k[X])) with
    ⟨n, u, hu, hfu⟩
  refine ⟨⟨n, u, hfu, ?_⟩⟩
  intro hu0
  apply hu
  rw [Polynomial.X_dvd_iff]
  simpa [Polynomial.coeff_zero_eq_eval_zero] using hu0

/-- The chosen factorization used when a concrete factor is needed. -/
noncomputable def zeroOrderFactorization {f : k[X]} (hf : f ≠ 0) :
    ZeroOrderFactorization f :=
  Classical.choice (exists_zeroOrderFactorization hf)

/-- The exponent in the factorization is the order of vanishing. -/
theorem zeroOrderFactorization_exponent_eq_ord {f : k[X]} (hf : f ≠ 0) :
    (zeroOrderFactorization hf).exponent = ordZeroPolynomial f := by
  classical
  let d := zeroOrderFactorization hf
  have hfin : FiniteMultiplicity (Polynomial.X : k[X]) f :=
    by simpa using (Polynomial.finiteMultiplicity_X_sub_C (p := f) 0 hf)
  have hpow : (Polynomial.X : k[X]) ^ d.exponent ∣ f := by
    exact ⟨d.unit, d.equation⟩
  have hnot : ¬(Polynomial.X : k[X]) ^ (d.exponent + 1) ∣ f := by
    rintro ⟨w, hw⟩
    have hunit : d.unit = (Polynomial.X : k[X]) * w := by
      apply mul_left_cancel₀ (pow_ne_zero d.exponent (Polynomial.X_ne_zero : (Polynomial.X : k[X]) ≠ 0))
      calc
        (Polynomial.X : k[X]) ^ d.exponent * d.unit = f := d.equation.symm
        _ = (Polynomial.X : k[X]) ^ (d.exponent + 1) * w := hw
        _ = (Polynomial.X : k[X]) ^ d.exponent * ((Polynomial.X : k[X]) * w) := by
          rw [pow_succ]
          ring
    have hdiv : (Polynomial.X : k[X]) ∣ d.unit := ⟨w, hunit⟩
    exact d.unit_value_ne_zero (by
      have hc : d.unit.coeff 0 = 0 := (Polynomial.X_dvd_iff).1 hdiv
      simpa [Polynomial.coeff_zero_eq_eval_zero] using hc)
  have heq : multiplicity (Polynomial.X : k[X]) f = d.exponent :=
    hfin.multiplicity_eq_iff.2 ⟨hpow, hnot⟩
  simpa [d, ordZeroPolynomial] using heq.symm

/-- The polynomial version of `f = t^n u(t)` with `u(0) ≠ 0`. -/
theorem exists_polynomial_zero_order_factorization {f : k[X]} (hf : f ≠ 0) :
    ∃ n : ℕ, ∃ u : k[X],
      f = (Polynomial.X : k[X]) ^ n * u ∧ Polynomial.eval 0 u ≠ 0 := by
  let d := zeroOrderFactorization hf
  exact ⟨d.exponent, d.unit, d.equation, d.unit_value_ne_zero⟩

/-- The largest-power characterization of the order at the origin. -/
theorem ordZeroPolynomial_characterization {f : k[X]} (hf : f ≠ 0) (n : ℕ) :
    ordZeroPolynomial f = n ↔
      (Polynomial.X : k[X]) ^ n ∣ f ∧
        ¬(Polynomial.X : k[X]) ^ (n + 1) ∣ f := by
  have hfin : FiniteMultiplicity (Polynomial.X : k[X]) f :=
    by simpa using (Polynomial.finiteMultiplicity_X_sub_C (p := f) 0 hf)
  simpa [ordZeroPolynomial] using hfin.multiplicity_eq_iff

/-- A nonzero polynomial has positive order exactly when it vanishes at the origin. -/
theorem ordZeroPolynomial_pos_iff_eval_zero {f : k[X]} (hf : f ≠ 0) :
    0 < ordZeroPolynomial f ↔ Polynomial.eval 0 f = 0 := by
  simp [ordZeroPolynomial, Nat.pos_iff_ne_zero, multiplicity_ne_zero,
    Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]

/-- The order of a nonvanishing polynomial at the origin is zero. -/
theorem ordZeroPolynomial_eq_zero_iff_eval_ne_zero {f : k[X]} (hf : f ≠ 0) :
    ordZeroPolynomial f = 0 ↔ Polynomial.eval 0 f ≠ 0 := by
  simp [ordZeroPolynomial, multiplicity_eq_zero, Polynomial.X_dvd_iff,
    Polynomial.coeff_zero_eq_eval_zero]
/-- The order of a product is the sum of the polynomial orders. -/
theorem ordZeroPolynomial_mul {f g : k[X]} (hf : f ≠ 0) (hg : g ≠ 0) :
    ordZeroPolynomial (f * g) = ordZeroPolynomial f + ordZeroPolynomial g := by
  unfold ordZeroPolynomial
  rw [multiplicity_mul Polynomial.prime_X
    (FiniteMultiplicity.of_prime_left Polynomial.prime_X (mul_ne_zero hf hg))]

/-- The polynomial order satisfies the additive valuation inequality when the
sum is nonzero. -/
theorem ordZeroPolynomial_add_lower {f g : k[X]} (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : f + g ≠ 0) :
    min (ordZeroPolynomial f) (ordZeroPolynomial g) ≤ ordZeroPolynomial (f + g) := by
  have hff : FiniteMultiplicity (Polynomial.X : k[X]) f :=
    FiniteMultiplicity.of_prime_left Polynomial.prime_X hf
  have hgg : FiniteMultiplicity (Polynomial.X : k[X]) g :=
    FiniteMultiplicity.of_prime_left Polynomial.prime_X hg
  have hsum : FiniteMultiplicity (Polynomial.X : k[X]) (f + g) :=
    FiniteMultiplicity.of_prime_left Polynomial.prime_X hfg
  have hmin := min_le_emultiplicity_add
    (p := (Polynomial.X : k[X])) (a := f) (b := g)
  rw [hff.emultiplicity_eq_multiplicity, hgg.emultiplicity_eq_multiplicity,
    hsum.emultiplicity_eq_multiplicity] at hmin
  have hmin' : min (multiplicity (Polynomial.X : k[X]) f)
      (multiplicity (Polynomial.X : k[X]) g) ≤
      multiplicity (Polynomial.X : k[X]) (f + g) := by
    rcases le_total (multiplicity (Polynomial.X : k[X]) f)
        (multiplicity (Polynomial.X : k[X]) g) with hfg' | hgf'
    · have hminTop :
          (min (multiplicity (Polynomial.X : k[X]) f)
            (multiplicity (Polynomial.X : k[X]) g) : WithTop ℕ) ≤
          (multiplicity (Polynomial.X : k[X]) (f + g) : WithTop ℕ) := by
        change min (multiplicity (Polynomial.X : k[X]) f : WithTop ℕ)
            (multiplicity (Polynomial.X : k[X]) g : WithTop ℕ) ≤
          (multiplicity (Polynomial.X : k[X]) (f + g) : WithTop ℕ) at hmin
        exact hmin
      have hfgTop :
          (multiplicity (Polynomial.X : k[X]) f : WithTop ℕ) ≤
            (multiplicity (Polynomial.X : k[X]) g : WithTop ℕ) :=
        WithTop.coe_le_coe.mpr hfg'
      rw [min_eq_left hfgTop] at hminTop
      have hnat : multiplicity (Polynomial.X : k[X]) f ≤
          multiplicity (Polynomial.X : k[X]) (f + g) :=
        WithTop.coe_le_coe.mp hminTop
      simpa [min_eq_left hfg'] using hnat
    · have hminTop :
          (min (multiplicity (Polynomial.X : k[X]) f)
            (multiplicity (Polynomial.X : k[X]) g) : WithTop ℕ) ≤
          (multiplicity (Polynomial.X : k[X]) (f + g) : WithTop ℕ) := by
        change min (multiplicity (Polynomial.X : k[X]) f : WithTop ℕ)
            (multiplicity (Polynomial.X : k[X]) g : WithTop ℕ) ≤
          (multiplicity (Polynomial.X : k[X]) (f + g) : WithTop ℕ) at hmin
        exact hmin
      have hgfTop :
          (multiplicity (Polynomial.X : k[X]) g : WithTop ℕ) ≤
            (multiplicity (Polynomial.X : k[X]) f : WithTop ℕ) :=
        WithTop.coe_le_coe.mpr hgf'
      rw [min_eq_right hgfTop] at hminTop
      have hnat : multiplicity (Polynomial.X : k[X]) g ≤
          multiplicity (Polynomial.X : k[X]) (f + g) :=
        WithTop.coe_le_coe.mp hminTop
      simpa [min_eq_right hgf'] using hnat
  simpa [ordZeroPolynomial] using hmin'

/-- Unequal polynomial orders cannot cancel in a sum. -/
theorem ordZeroPolynomial_add_of_ne {f g : k[X]} (hf : f ≠ 0) (hg : g ≠ 0)
    (hne : ordZeroPolynomial f ≠ ordZeroPolynomial g) :
    ordZeroPolynomial (f + g) = min (ordZeroPolynomial f) (ordZeroPolynomial g) := by
  have hff : FiniteMultiplicity (Polynomial.X : k[X]) f :=
    FiniteMultiplicity.of_prime_left Polynomial.prime_X hf
  have hgg : FiniteMultiplicity (Polynomial.X : k[X]) g :=
    FiniteMultiplicity.of_prime_left Polynomial.prime_X hg
  have hne' : multiplicity (Polynomial.X : k[X]) f ≠
      multiplicity (Polynomial.X : k[X]) g := by
    simpa [ordZeroPolynomial] using hne
  simpa [ordZeroPolynomial] using (multiplicity_add_eq_min hff hgg hne')

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
    Nonempty (RatFuncZeroOrderFactorization x) := by
  classical
  have hnum : x.num ≠ 0 := RatFunc.num_ne_zero hx
  have hden : x.denom ≠ 0 := RatFunc.denom_ne_zero x
  obtain ⟨m, a, ha, hfa⟩ := WfDvdMonoid.max_power_factor hnum
    (Polynomial.prime_X.irreducible : Irreducible (Polynomial.X : k[X]))
  obtain ⟨n, b, hb, hfb⟩ := WfDvdMonoid.max_power_factor hden
    (Polynomial.prime_X.irreducible : Irreducible (Polynomial.X : k[X]))
  have ha0 : Polynomial.eval 0 a ≠ 0 := by
    intro h
    apply ha
    rw [Polynomial.X_dvd_iff]
    simpa [Polynomial.coeff_zero_eq_eval_zero] using h
  have hb0 : Polynomial.eval 0 b ≠ 0 := by
    intro h
    apply hb
    rw [Polynomial.X_dvd_iff]
    simpa [Polynomial.coeff_zero_eq_eval_zero] using h
  have hane : a ≠ 0 := by
    intro h
    apply ha0
    simp [h]
  have hbne : b ≠ 0 := by
    intro h
    apply hb0
    simp [h]
  let e : ℤ := (m : ℤ) - (n : ℤ)
  let u : RatFunc k := algebraMap k[X] (RatFunc k) a /
    algebraMap k[X] (RatFunc k) b
  have hu : IsRegularAtZeroRatFunc u := by
    constructor
    · intro h
      apply ha
      exact dvd_trans (by
        rw [Polynomial.X_dvd_iff]
        simpa [u, Polynomial.coeff_zero_eq_eval_zero] using h)
        (RatFunc.num_div_dvd a hbne)
    · intro h
      apply hb
      exact dvd_trans (by
        rw [Polynomial.X_dvd_iff]
        simpa [u, Polynomial.coeff_zero_eq_eval_zero] using h)
        (RatFunc.denom_div_dvd a b)
  have hxe : x = ratFuncCoordinate ^ e * u := by
    dsimp [ratFuncCoordinate, u, e]
    calc
      x = algebraMap k[X] (RatFunc k) x.num /
          algebraMap k[X] (RatFunc k) x.denom := (RatFunc.num_div_denom x).symm
      _ = algebraMap k[X] (RatFunc k) ((Polynomial.X : k[X]) ^ m * a) /
          algebraMap k[X] (RatFunc k) ((Polynomial.X : k[X]) ^ n * b) := by
        rw [hfa, hfb]
      _ = (algebraMap k[X] (RatFunc k) (Polynomial.X : k[X])) ^
          ((m : ℤ) - (n : ℤ)) *
          (algebraMap k[X] (RatFunc k) a /
            algebraMap k[X] (RatFunc k) b) := by
        simp only [map_mul, map_pow]
        rw [zpow_natCast_sub_natCast₀
          (RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero) m n]
        field_simp [RatFunc.algebraMap_ne_zero hane, RatFunc.algebraMap_ne_zero hbne]
  exact ⟨⟨e, u, hxe, hu⟩⟩

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
    ordZeroFraction (f * h) (g * h) = ordZeroFraction f g := by
  have hfh : FiniteMultiplicity (Polynomial.X : k[X]) (f * h) :=
    FiniteMultiplicity.of_prime_left Polynomial.prime_X (mul_ne_zero hf hh)
  have hgh : FiniteMultiplicity (Polynomial.X : k[X]) (g * h) :=
    FiniteMultiplicity.of_prime_left Polynomial.prime_X (mul_ne_zero hg hh)
  unfold ordZeroFraction
  rw [multiplicity_mul Polynomial.prime_X hfh,
    multiplicity_mul Polynomial.prime_X hgh]
  simp only [Nat.cast_add]
  ring

/-- The normalized numerator/denominator definition agrees with the fraction
definition whenever the displayed fraction represents `x`. -/
theorem ordZeroRatFunc_eq_ordZeroFraction {x : RatFunc k} {f g : k[X]}
    (hg : g ≠ 0) (hx0 : x ≠ 0)
    (hx : x = algebraMap k[X] (RatFunc k) f /
      algebraMap k[X] (RatFunc k) g) :
    ordZeroRatFunc x = ordZeroFraction f g := by
  classical
  have hf : f ≠ 0 := by
    intro hf
    apply hx0
    rw [hx, hf, map_zero, zero_div]
  have hnum : x.num ≠ 0 := RatFunc.num_ne_zero hx0
  have hden : x.denom ≠ 0 := RatFunc.denom_ne_zero x
  have hcross : x.num * g = f * x.denom :=
    (RatFunc.num_mul_eq_mul_denom_iff hg).2 hx
  have hfin1 : FiniteMultiplicity (Polynomial.X : k[X]) (x.num * g) :=
    FiniteMultiplicity.of_prime_left Polynomial.prime_X (mul_ne_zero hnum hg)
  have hfin2 : FiniteMultiplicity (Polynomial.X : k[X]) (f * x.denom) :=
    FiniteMultiplicity.of_prime_left Polynomial.prime_X (mul_ne_zero hf hden)
  have hm := congrArg (fun z : k[X] =>
    (multiplicity (Polynomial.X : k[X]) z : ℤ)) hcross
  rw [multiplicity_mul Polynomial.prime_X hfin1,
    multiplicity_mul Polynomial.prime_X hfin2] at hm
  simp only [ordZeroRatFunc, if_neg hx0, ordZeroFraction]
  omega

/-- The order of a product is the sum of the orders. -/
theorem ordZeroRatFunc_mul {x y : RatFunc k} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordZeroRatFunc (x * y) = ordZeroRatFunc x + ordZeroRatFunc y := by
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  have hfrac : x * y =
      algebraMap k[X] (RatFunc k) (x.num * y.num) /
        algebraMap k[X] (RatFunc k) (x.denom * y.denom) :=
    (RatFunc.num_mul_eq_mul_denom_iff
      (mul_ne_zero (RatFunc.denom_ne_zero x) (RatFunc.denom_ne_zero y))).1
      (RatFunc.num_denom_mul x y)
  have hxfrac := ordZeroRatFunc_eq_ordZeroFraction
    (RatFunc.denom_ne_zero x) hx (RatFunc.num_div_denom x).symm
  have hyfrac := ordZeroRatFunc_eq_ordZeroFraction
    (RatFunc.denom_ne_zero y) hy (RatFunc.num_div_denom y).symm
  have hnum : FiniteMultiplicity (Polynomial.X : k[X]) (x.num * y.num) :=
    FiniteMultiplicity.of_prime_left Polynomial.prime_X
      (mul_ne_zero (RatFunc.num_ne_zero hx) (RatFunc.num_ne_zero hy))
  have hden : FiniteMultiplicity (Polynomial.X : k[X]) (x.denom * y.denom) :=
    FiniteMultiplicity.of_prime_left Polynomial.prime_X
      (mul_ne_zero (RatFunc.denom_ne_zero x) (RatFunc.denom_ne_zero y))
  calc
    ordZeroRatFunc (x * y) = ordZeroFraction (x.num * y.num) (x.denom * y.denom) :=
      ordZeroRatFunc_eq_ordZeroFraction
        (mul_ne_zero (RatFunc.denom_ne_zero x) (RatFunc.denom_ne_zero y)) hxy hfrac
    _ = ordZeroFraction x.num x.denom + ordZeroFraction y.num y.denom := by
      unfold ordZeroFraction
      rw [multiplicity_mul Polynomial.prime_X hnum,
        multiplicity_mul Polynomial.prime_X hden]
      simp only [Nat.cast_add]
      ring
    _ = ordZeroRatFunc x + ordZeroRatFunc y := by rw [hxfrac, hyfrac]

/-- The order of a reciprocal is the negative of the order. -/
theorem ordZeroRatFunc_inv {x : RatFunc k} (hx : x ≠ 0) :
    ordZeroRatFunc x⁻¹ = -ordZeroRatFunc x := by
  have hfrac : x⁻¹ = algebraMap k[X] (RatFunc k) x.denom /
      algebraMap k[X] (RatFunc k) x.num := by
    calc
      x⁻¹ = (algebraMap k[X] (RatFunc k) x.num /
          algebraMap k[X] (RatFunc k) x.denom)⁻¹ := by
            rw [RatFunc.num_div_denom]
      _ = algebraMap k[X] (RatFunc k) x.denom /
          algebraMap k[X] (RatFunc k) x.num := by rw [inv_div]
  have hleft := ordZeroRatFunc_eq_ordZeroFraction
    (RatFunc.num_ne_zero hx) (inv_ne_zero hx) hfrac
  have hright := ordZeroRatFunc_eq_ordZeroFraction
    (RatFunc.denom_ne_zero x) hx (RatFunc.num_div_denom x).symm
  calc
    ordZeroRatFunc x⁻¹ = ordZeroFraction x.denom x.num := hleft
    _ = -ordZeroFraction x.num x.denom := by
      unfold ordZeroFraction
      ring
    _ = -ordZeroRatFunc x := by rw [hright]

theorem ordZeroRatFunc_zpow {x : RatFunc k} (hx : x ≠ 0) (n : ℤ) :
    ordZeroRatFunc (x ^ n) = n * ordZeroRatFunc x := by
  have hpow : ∀ m : ℕ,
      ordZeroRatFunc (x ^ m) = (m : ℤ) * ordZeroRatFunc x := by
    intro m
    induction m with
    | zero => simp [ordZeroRatFunc]
    | succ m ih =>
        rw [pow_succ, ordZeroRatFunc_mul (pow_ne_zero m hx) hx, ih]
        simp only [Nat.cast_succ]
        ring
  cases n with
  | ofNat m =>
      simpa [zpow_ofNat] using hpow m
  | negSucc m =>
      rw [zpow_negSucc, ordZeroRatFunc_inv (pow_ne_zero (m + 1) hx), hpow]
      simp only [Int.negSucc_eq, Nat.cast_add]
      ring

/-- The order of a quotient is the difference of the orders. -/
theorem ordZeroRatFunc_div {x y : RatFunc k} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordZeroRatFunc (x / y) = ordZeroRatFunc x - ordZeroRatFunc y := by
  rw [div_eq_mul_inv, ordZeroRatFunc_mul hx (inv_ne_zero hy),
    ordZeroRatFunc_inv hy]
  ring

theorem ordZeroRatFunc_add_lower {x y : RatFunc k} (hx : x ≠ 0)
    (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (ordZeroRatFunc x) (ordZeroRatFunc y) ≤ ordZeroRatFunc (x + y) := by
  classical
  have hD : x.denom * y.denom ≠ 0 :=
    mul_ne_zero (RatFunc.denom_ne_zero x) (RatFunc.denom_ne_zero y)
  have hfrac : x + y =
      algebraMap k[X] (RatFunc k) (x.num * y.denom + x.denom * y.num) /
        algebraMap k[X] (RatFunc k) (x.denom * y.denom) :=
    (RatFunc.num_mul_eq_mul_denom_iff hD).1 (RatFunc.num_denom_add x y)
  have hN : x.num * y.denom + x.denom * y.num ≠ 0 := by
    intro h
    apply hxy
    rw [hfrac, h, map_zero, zero_div]
  have hs := ordZeroRatFunc_eq_ordZeroFraction hD hxy hfrac
  have hxfrac := ordZeroRatFunc_eq_ordZeroFraction
    (RatFunc.denom_ne_zero x) hx (RatFunc.num_div_denom x).symm
  have hyfrac := ordZeroRatFunc_eq_ordZeroFraction
    (RatFunc.denom_ne_zero y) hy (RatFunc.num_div_denom y).symm
  have h1 : FiniteMultiplicity (Polynomial.X : k[X]) (x.num * y.denom) :=
    FiniteMultiplicity.of_prime_left Polynomial.prime_X
      (mul_ne_zero (RatFunc.num_ne_zero hx) (RatFunc.denom_ne_zero y))
  have h2 : FiniteMultiplicity (Polynomial.X : k[X]) (x.denom * y.num) :=
    FiniteMultiplicity.of_prime_left Polynomial.prime_X
      (mul_ne_zero (RatFunc.denom_ne_zero x) (RatFunc.num_ne_zero hy))
  have hNfin : FiniteMultiplicity (Polynomial.X : k[X])
      (x.num * y.denom + x.denom * y.num) :=
    FiniteMultiplicity.of_prime_left Polynomial.prime_X hN
  have hDfin : FiniteMultiplicity (Polynomial.X : k[X]) (x.denom * y.denom) :=
    FiniteMultiplicity.of_prime_left Polynomial.prime_X hD
  have hmin := min_le_emultiplicity_add
    (p := (Polynomial.X : k[X])) (a := x.num * y.denom) (b := x.denom * y.num)
  rw [h1.emultiplicity_eq_multiplicity, h2.emultiplicity_eq_multiplicity,
    hNfin.emultiplicity_eq_multiplicity] at hmin
  have hmin' : min (multiplicity (Polynomial.X : k[X]) (x.num * y.denom))
      (multiplicity (Polynomial.X : k[X]) (x.denom * y.num)) ≤
      multiplicity (Polynomial.X : k[X])
        (x.num * y.denom + x.denom * y.num) := by
    rcases le_total (multiplicity (Polynomial.X : k[X]) (x.num * y.denom))
        (multiplicity (Polynomial.X : k[X]) (x.denom * y.num)) with h12 | h21
    · have hminTop :
          (min (multiplicity (Polynomial.X : k[X]) (x.num * y.denom))
            (multiplicity (Polynomial.X : k[X]) (x.denom * y.num)) : WithTop ℕ) ≤
            (multiplicity (Polynomial.X : k[X])
              (x.num * y.denom + x.denom * y.num) : WithTop ℕ) := by
        change min (multiplicity (Polynomial.X : k[X]) (x.num * y.denom) : WithTop ℕ)
            (multiplicity (Polynomial.X : k[X]) (x.denom * y.num) : WithTop ℕ) ≤
          (multiplicity (Polynomial.X : k[X])
            (x.num * y.denom + x.denom * y.num) : WithTop ℕ) at hmin
        exact hmin
      have h12Top :
          (multiplicity (Polynomial.X : k[X]) (x.num * y.denom) : WithTop ℕ) ≤
            (multiplicity (Polynomial.X : k[X]) (x.denom * y.num) : WithTop ℕ) :=
        WithTop.coe_le_coe.mpr h12
      rw [min_eq_left h12Top] at hminTop
      have hnat := WithTop.coe_le_coe.mp hminTop
      simpa [min_eq_left h12] using hnat
    · have hminTop :
          (min (multiplicity (Polynomial.X : k[X]) (x.num * y.denom))
            (multiplicity (Polynomial.X : k[X]) (x.denom * y.num)) : WithTop ℕ) ≤
            (multiplicity (Polynomial.X : k[X])
              (x.num * y.denom + x.denom * y.num) : WithTop ℕ) := by
        change min (multiplicity (Polynomial.X : k[X]) (x.num * y.denom) : WithTop ℕ)
            (multiplicity (Polynomial.X : k[X]) (x.denom * y.num) : WithTop ℕ) ≤
          (multiplicity (Polynomial.X : k[X])
            (x.num * y.denom + x.denom * y.num) : WithTop ℕ) at hmin
        exact hmin
      have h21Top :
          (multiplicity (Polynomial.X : k[X]) (x.denom * y.num) : WithTop ℕ) ≤
            (multiplicity (Polynomial.X : k[X]) (x.num * y.denom) : WithTop ℕ) :=
        WithTop.coe_le_coe.mpr h21
      rw [min_eq_right h21Top] at hminTop
      have hnat := WithTop.coe_le_coe.mp hminTop
      simpa [min_eq_right h21] using hnat
  have h1m := multiplicity_mul Polynomial.prime_X h1
  have h2m := multiplicity_mul Polynomial.prime_X h2
  have hDm := multiplicity_mul Polynomial.prime_X hDfin
  rw [hs, hxfrac, hyfrac]
  unfold ordZeroFraction
  rw [hDm]
  rw [h1m, h2m] at hmin'
  simp only [Nat.cast_add] at hmin' ⊢
  rcases le_total (multiplicity (Polynomial.X : k[X]) x.num +
      multiplicity (Polynomial.X : k[X]) y.denom)
      (multiplicity (Polynomial.X : k[X]) x.denom +
      multiplicity (Polynomial.X : k[X]) y.num) with h12 | h21
  · rw [min_eq_left h12] at hmin'
    omega
  · rw [min_eq_right h21] at hmin'
    omega

/-- The total order satisfies the additive valuation inequality. -/
theorem ordZeroRatFuncWithTop_add {x y : RatFunc k} :
    min (ordZeroRatFuncWithTop x) (ordZeroRatFuncWithTop y) ≤
      ordZeroRatFuncWithTop (x + y) := by
  classical
  by_cases hx : x = 0
  · subst x
    simp [ordZeroRatFuncWithTop]
  by_cases hy : y = 0
  · subst y
    simp [ordZeroRatFuncWithTop]
  by_cases hxy : x + y = 0
  · simp [ordZeroRatFuncWithTop, hx, hy, hxy]
  have h := ordZeroRatFunc_add_lower hx hy hxy
  simpa [ordZeroRatFuncWithTop, hx, hy, hxy] using
    (WithTop.coe_le_coe.mpr h)

/-- If two nonzero rational functions have different orders, their sum has the
smaller order; unequal orders cannot cancel. -/
theorem ordZeroRatFunc_add_of_ne {x y : RatFunc k} (hx : x ≠ 0) (hy : y ≠ 0)
    (hne : ordZeroRatFunc x ≠ ordZeroRatFunc y) :
    ordZeroRatFunc (x + y) = min (ordZeroRatFunc x) (ordZeroRatFunc y) := by
  classical
  have hxy : x + y ≠ 0 := by
    intro hxy
    apply hne
    have hyneg : y = -x := eq_neg_of_add_eq_zero_right hxy
    have hone : ordZeroRatFunc (-1 : RatFunc k) = 0 := by
      calc
        ordZeroRatFunc (-1 : RatFunc k) =
            ordZeroFraction (-1 : k[X]) 1 := by
          apply ordZeroRatFunc_eq_ordZeroFraction
            (f := (-1 : k[X])) (g := 1) (by simp) (by simp)
          simp
        _ = 0 := by simp [ordZeroFraction]
    rw [hyneg]
    calc
      ordZeroRatFunc x = ordZeroRatFunc ((-1 : RatFunc k) * x) := by
        rw [ordZeroRatFunc_mul (x := (-1 : RatFunc k)) (y := x) (by simp) hx,
          hone, zero_add]
      _ = ordZeroRatFunc (-1 : RatFunc k) + ordZeroRatFunc x :=
        ordZeroRatFunc_mul (by simp) hx
      _ = ordZeroRatFunc x := by rw [hone, zero_add]
      _ = ordZeroRatFunc (-x) := by
        rw [show -x = (-1 : RatFunc k) * x by ring,
          ordZeroRatFunc_mul (by simp) hx, hone, zero_add]
  have hD : x.denom * y.denom ≠ 0 :=
    mul_ne_zero (RatFunc.denom_ne_zero x) (RatFunc.denom_ne_zero y)
  have hfrac : x + y =
      algebraMap k[X] (RatFunc k) (x.num * y.denom + x.denom * y.num) /
        algebraMap k[X] (RatFunc k) (x.denom * y.denom) :=
    (RatFunc.num_mul_eq_mul_denom_iff hD).1 (RatFunc.num_denom_add x y)
  have hN : x.num * y.denom + x.denom * y.num ≠ 0 := by
    intro h
    apply hxy
    rw [hfrac, h, map_zero, zero_div]
  have hs := ordZeroRatFunc_eq_ordZeroFraction hD hxy hfrac
  have hxfrac := ordZeroRatFunc_eq_ordZeroFraction
    (RatFunc.denom_ne_zero x) hx (RatFunc.num_div_denom x).symm
  have hyfrac := ordZeroRatFunc_eq_ordZeroFraction
    (RatFunc.denom_ne_zero y) hy (RatFunc.num_div_denom y).symm
  have h1 : FiniteMultiplicity (Polynomial.X : k[X]) (x.num * y.denom) :=
    FiniteMultiplicity.of_prime_left Polynomial.prime_X
      (mul_ne_zero (RatFunc.num_ne_zero hx) (RatFunc.denom_ne_zero y))
  have h2 : FiniteMultiplicity (Polynomial.X : k[X]) (x.denom * y.num) :=
    FiniteMultiplicity.of_prime_left Polynomial.prime_X
      (mul_ne_zero (RatFunc.denom_ne_zero x) (RatFunc.num_ne_zero hy))
  have hNfin : FiniteMultiplicity (Polynomial.X : k[X])
      (x.num * y.denom + x.denom * y.num) :=
    FiniteMultiplicity.of_prime_left Polynomial.prime_X hN
  have hDfin : FiniteMultiplicity (Polynomial.X : k[X]) (x.denom * y.denom) :=
    FiniteMultiplicity.of_prime_left Polynomial.prime_X hD
  have h1m := multiplicity_mul Polynomial.prime_X h1
  have h2m := multiplicity_mul Polynomial.prime_X h2
  have hneq : multiplicity (Polynomial.X : k[X]) (x.num * y.denom) ≠
      multiplicity (Polynomial.X : k[X]) (x.denom * y.num) := by
    intro heq
    apply hne
    rw [hxfrac, hyfrac]
    unfold ordZeroFraction
    rw [h1m, h2m] at heq
    omega
  have hsum := multiplicity_add_eq_min h1 h2 hneq
  have hDm := multiplicity_mul Polynomial.prime_X hDfin
  rw [hs, hxfrac, hyfrac]
  unfold ordZeroFraction
  rw [hDm, hsum, h1m, h2m]
  simp only [Nat.cast_add]
  rcases le_total (multiplicity (Polynomial.X : k[X]) x.num +
      multiplicity (Polynomial.X : k[X]) y.denom)
      (multiplicity (Polynomial.X : k[X]) x.denom +
      multiplicity (Polynomial.X : k[X]) y.num) with h12 | h21
  · have h12Z :
        (multiplicity (Polynomial.X : k[X]) x.num : ℤ) -
            (multiplicity (Polynomial.X : k[X]) x.denom : ℤ) ≤
          (multiplicity (Polynomial.X : k[X]) y.num : ℤ) -
            (multiplicity (Polynomial.X : k[X]) y.denom : ℤ) := by
      omega
    rw [min_eq_left h12, min_eq_left h12Z]
    simp only [Nat.cast_add]
    ring
  · have h21Z :
        (multiplicity (Polynomial.X : k[X]) y.num : ℤ) -
            (multiplicity (Polynomial.X : k[X]) y.denom : ℤ) ≤
          (multiplicity (Polynomial.X : k[X]) x.num : ℤ) -
            (multiplicity (Polynomial.X : k[X]) x.denom : ℤ) := by
      omega
    rw [min_eq_right h21, min_eq_right h21Z]
    simp only [Nat.cast_add]
    ring

/-- A regular local unit contributes order zero. -/
theorem ordZeroRatFunc_of_regular_unit {u : RatFunc k}
    (hu : IsRegularAtZeroRatFunc u) :
    ordZeroRatFunc u = 0 := by
  have hu0 : u ≠ 0 := by
    intro h
    apply hu.1
    simp [h]
  have hnum : multiplicity (Polynomial.X : k[X]) u.num = 0 :=
    multiplicity_eq_zero.mpr (by
      intro hdiv
      apply hu.1
      rw [Polynomial.X_dvd_iff] at hdiv
      simpa [Polynomial.coeff_zero_eq_eval_zero] using hdiv)
  have hden : multiplicity (Polynomial.X : k[X]) u.denom = 0 :=
    multiplicity_eq_zero.mpr (by
      intro hdiv
      apply hu.2
      rw [Polynomial.X_dvd_iff] at hdiv
      simpa [Polynomial.coeff_zero_eq_eval_zero] using hdiv)
  simp [ordZeroRatFunc, hu0, hnum, hden]

/-- The unit part of a nonzero rational function is locally invertible and has
order zero. -/
theorem ordZeroRatFunc_factorization_unit_part {x : RatFunc k} (hx : x ≠ 0) :
    ∃ n : ℤ, ∃ u : RatFunc k,
      x = ratFuncCoordinate ^ n * u ∧
        IsRegularAtZeroRatFunc u ∧ ordZeroRatFunc u = 0 := by
  let d := ratFuncZeroOrderFactorization hx
  exact ⟨d.exponent, d.unit, d.equation, d.unit_regular_at_zero,
    ordZeroRatFunc_of_regular_unit d.unit_regular_at_zero⟩

/-- Positive, negative, and zero order mean zero, pole, and nonvanishing regular
behavior, respectively. -/
theorem ordZeroRatFunc_sign_classification {x : RatFunc k} (hx : x ≠ 0) :
    (0 < ordZeroRatFunc x ↔ Polynomial.eval 0 x.num = 0) ∧
    (ordZeroRatFunc x < 0 ↔ Polynomial.eval 0 x.denom = 0) ∧
    (ordZeroRatFunc x = 0 ↔
      Polynomial.eval 0 x.num ≠ 0 ∧ Polynomial.eval 0 x.denom ≠ 0) := by
  let m := multiplicity (Polynomial.X : k[X]) x.num
  let n := multiplicity (Polynomial.X : k[X]) x.denom
  have hm_eval : m = 0 ↔ Polynomial.eval 0 x.num ≠ 0 := by
    simpa [m, ordZeroPolynomial] using
      (ordZeroPolynomial_eq_zero_iff_eval_ne_zero (RatFunc.num_ne_zero hx))
  have hn_eval : n = 0 ↔ Polynomial.eval 0 x.denom ≠ 0 := by
    simpa [n, ordZeroPolynomial] using
      (ordZeroPolynomial_eq_zero_iff_eval_ne_zero (RatFunc.denom_ne_zero x))
  have hnotboth : ¬(m ≠ 0 ∧ n ≠ 0) := by
    intro h
    have hmx : (Polynomial.X : k[X]) ∣ x.num :=
      multiplicity_ne_zero.mp h.1
    have hnx : (Polynomial.X : k[X]) ∣ x.denom :=
      multiplicity_ne_zero.mp h.2
    have hu : IsUnit (Polynomial.X : k[X]) :=
      (RatFunc.isCoprime_num_denom x).isUnit_of_dvd' hmx hnx
    exact Polynomial.prime_X.not_unit hu
  have hpos : (0 < (m : ℤ) - (n : ℤ)) ↔ m ≠ 0 := by
    constructor
    · intro hmn hm0
      subst m
      omega
    · intro hm0
      have hn0 : n = 0 := by
        by_contra hn0
        exact hnotboth ⟨hm0, hn0⟩
      omega
  have hneg : ((m : ℤ) - (n : ℤ) < 0) ↔ n ≠ 0 := by
    constructor
    · intro hmn hn0
      subst n
      omega
    · intro hn0
      have hm0 : m = 0 := by
        by_contra hm0
        exact hnotboth ⟨hm0, hn0⟩
      omega
  have hzero : ((m : ℤ) - (n : ℤ) = 0) ↔ m = 0 ∧ n = 0 := by
    constructor
    · intro hmn
      by_cases hm0 : m = 0
      · have : n = 0 := by omega
        exact ⟨hm0, this⟩
      · by_cases hn0 : n = 0
        · omega
        · exact (hnotboth ⟨hm0, hn0⟩).elim
    · rintro ⟨hm0, hn0⟩
      omega
  have hm_zero : m ≠ 0 ↔ Polynomial.eval 0 x.num = 0 := by
    constructor
    · intro hm0
      by_contra hne
      exact hm0 (hm_eval.mpr hne)
    · intro hzero hm0
      exact (hm_eval.mp hm0) hzero
  have hn_zero : n ≠ 0 ↔ Polynomial.eval 0 x.denom = 0 := by
    constructor
    · intro hn0
      by_contra hne
      exact hn0 (hn_eval.mpr hne)
    · intro hzero hn0
      exact (hn_eval.mp hn0) hzero
  have hzero_eval : ((m : ℤ) - (n : ℤ) = 0) ↔
      Polynomial.eval 0 x.num ≠ 0 ∧ Polynomial.eval 0 x.denom ≠ 0 := by
    rw [hzero, hm_eval, hn_eval]
  constructor
  · simpa [ordZeroRatFunc, hx, m, n] using hpos.trans hm_zero
  constructor
  · simpa [ordZeroRatFunc, hx, m, n] using hneg.trans hn_zero
  · simpa [ordZeroRatFunc, hx, m, n] using hzero_eval

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
      ordZeroPolynomial (f.comp (Polynomial.X + Polynomial.C a)) := by
  by_cases hf : f = 0
  · simp [hf, ordAtPolynomial, ordZeroPolynomial]
  have hcomp : f.comp (Polynomial.X + Polynomial.C a) ≠ 0 :=
    Polynomial.comp_X_add_C_ne_zero_iff.mpr hf
  have hfa : FiniteMultiplicity (Polynomial.X - Polynomial.C a : k[X]) f :=
    Polynomial.finiteMultiplicity_X_sub_C a hf
  have hfb : FiniteMultiplicity (Polynomial.X : k[X])
      (f.comp (Polynomial.X + Polynomial.C a)) := by
    simpa using (Polynomial.finiteMultiplicity_X_sub_C 0 hcomp)
  unfold ordAtPolynomial ordZeroPolynomial
  have hm := (hfa.multiplicity_eq_iff (n :=
      multiplicity (Polynomial.X - Polynomial.C a : k[X]) f)).1 rfl
  have hcomp_eq : multiplicity (Polynomial.X : k[X])
      (f.comp (Polynomial.X + Polynomial.C a)) =
      multiplicity (Polynomial.X - Polynomial.C a : k[X]) f :=
    (hfb.multiplicity_eq_iff).2 ⟨(Polynomial.X_sub_C_pow_dvd_iff).1 hm.1,
      fun h => hm.2 ((Polynomial.X_sub_C_pow_dvd_iff).2 h)⟩
  exact hcomp_eq.symm

/-- A local parameter is a generator of the maximal ideal of a one-dimensional
regular local ring. -/
def IsLocalParameter {R : Type*} [CommRing R] (𝔪 : Ideal R) (t : R) : Prop :=
  𝔪.IsMaximal ∧ Ideal.span ({t} : Set R) = 𝔪

/-- Two local parameters differ by a local unit. -/
theorem local_parameters_differ_by_unit {R : Type*} [CommRing R] [IsDomain R]
    [IsLocalRing R] {𝔪 : Ideal R} {s t : R}
    (hs : IsLocalParameter 𝔪 s) (ht : IsLocalParameter 𝔪 t) :
    ∃ u : Rˣ, s = (u : R) * t := by
  have hst : s ∈ Ideal.span ({t} : Set R) := by
    rw [ht.2, ← hs.2]
    exact Ideal.mem_span_singleton_self s
  have hts : t ∈ Ideal.span ({s} : Set R) := by
    rw [hs.2, ← ht.2]
    exact Ideal.mem_span_singleton_self t
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hst
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hts
  by_cases hs0 : s = 0
  · have ht0 : t = 0 := by
      rw [← hb, hs0, mul_zero]
    exact ⟨1, by simp [hs0, ht0]⟩
  have ht0 : t ≠ 0 := by
    intro ht0
    apply hs0
    rw [← ha, ht0, mul_zero]
  have hba : b * a = 1 := by
    apply mul_right_cancel₀ ht0
    calc
      (b * a) * t = b * (a * t) := by ring
      _ = b * s := by rw [ha]
      _ = t := hb
      _ = 1 * t := by simp
  have hunit : IsUnit a := IsUnit.of_mul_eq_one_right b hba
  rcases hunit with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  calc
    s = a * t := ha.symm
    _ = (u : R) * t := by rw [← hu]

/-- Multiplication by a local unit does not change an additive order. -/
theorem additive_order_invariant_under_local_unit {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (u : Kˣ) (x : K)
    (hu : v (u : K) = 0) :
    v ((u : K) * x) = v x := by
  rw [v.map_mul, hu, zero_add]

end LocalQuestion

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter01
