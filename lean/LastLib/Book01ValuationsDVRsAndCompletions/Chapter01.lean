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

private theorem ordZeroRatFunc_zpow {x : RatFunc k} (hx : x ≠ 0) (n : ℤ) :
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

private theorem ordZeroRatFunc_add_lower {x y : RatFunc k} (hx : x ≠ 0)
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
    (hx : x ≠ 0) : Nonempty (PrimeAdicDecomposition p x) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hn : x.num ≠ 0 := Rat.num_ne_zero.mpr hx
  have hd : (x.den : ℤ) ≠ 0 := by exact_mod_cast Rat.den_nz x
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  obtain ⟨m, a, ha, hma⟩ := WfDvdMonoid.max_power_factor hn hprime.irreducible
  obtain ⟨n, b, hb, hnb⟩ := WfDvdMonoid.max_power_factor hd hprime.irreducible
  have hfm : FiniteMultiplicity (p : ℤ) x.num :=
    FiniteMultiplicity.of_prime_left hprime hn
  have hfd : FiniteMultiplicity (p : ℤ) (x.den : ℤ) :=
    FiniteMultiplicity.of_prime_left hprime hd
  have hm : multiplicity (p : ℤ) x.num = m := by
    apply (hfm.multiplicity_eq_iff).2
    refine ⟨⟨a, hma⟩, ?_⟩
    intro hpow
    obtain ⟨c, hc⟩ := hpow
    apply ha
    refine ⟨c, ?_⟩
    apply mul_left_cancel₀ (pow_ne_zero m (show (p : ℤ) ≠ 0 by exact_mod_cast hp.ne_zero))
    calc
      (p : ℤ) ^ m * a = x.num := hma.symm
      _ = (p : ℤ) ^ (m + 1) * c := hc
      _ = (p : ℤ) ^ m * ((p : ℤ) * c) := by
        rw [pow_succ]
        ring
  have hn' : multiplicity (p : ℤ) (x.den : ℤ) = n := by
    apply (hfd.multiplicity_eq_iff).2
    refine ⟨⟨b, hnb⟩, ?_⟩
    intro hpow
    obtain ⟨c, hc⟩ := hpow
    apply hb
    refine ⟨c, ?_⟩
    apply mul_left_cancel₀ (pow_ne_zero n (show (p : ℤ) ≠ 0 by exact_mod_cast hp.ne_zero))
    calc
      (p : ℤ) ^ n * b = (x.den : ℤ) := hnb.symm
      _ = (p : ℤ) ^ (n + 1) * c := hc
      _ = (p : ℤ) ^ n * ((p : ℤ) * c) := by
        rw [pow_succ]
        ring
  have ha0 : a ≠ 0 := by
    intro ha0
    apply hn
    rw [hma, ha0, mul_zero]
  have hb0 : b ≠ 0 := by
    intro hb0
    apply hd
    rw [hnb, hb0, mul_zero]
  let e : ℤ := (m : ℤ) - (n : ℤ)
  refine ⟨⟨e, a, b, ha0, hb0, ha, hb, ?_⟩⟩
  calc
    x = Rat.divInt x.num x.den := (Rat.num_divInt_den x).symm
    _ = Rat.divInt ((p : ℤ) ^ m * a) ((p : ℤ) ^ n * b) := by rw [hma, hnb]
    _ = (p : ℚ) ^ e * (a : ℚ) / (b : ℚ) := by
      rw [Rat.divInt_eq_div]
      norm_num [Int.cast_mul, Int.cast_pow]
      dsimp [e]
      rw [zpow_natCast_sub_natCast₀ (by exact_mod_cast hp.ne_zero) m n]
      field_simp [ha0, hb0]

/-- The exponent in every `p`-free presentation is the `p`-adic order. -/
theorem primeAdicDecomposition_exponent_eq_pAdicOrder {p : ℕ} (hp : p.Prime)
    {x : ℚ} (hx : x ≠ 0) (d : PrimeAdicDecomposition p x) :
    d.exponent = pAdicOrder p x := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpa : pAdicOrder p (d.numerator : ℚ) = 0 := by
    simp [pAdicOrder, padicValRat.of_int_multiplicity hp.ne_one d.numerator_ne_zero,
      multiplicity_eq_zero.mpr d.numerator_p_free]
  have hpb : pAdicOrder p (d.denominator : ℚ) = 0 := by
    simp [pAdicOrder, padicValRat.of_int_multiplicity hp.ne_one d.denominator_ne_zero,
      multiplicity_eq_zero.mpr d.denominator_p_free]
  have hxval := congrArg (pAdicOrder p) d.equation
  have hxval' : pAdicOrder p x = pAdicOrder p
      ((p : ℚ) ^ d.exponent *
            ((d.numerator : ℚ) / (d.denominator : ℚ))) := by
    calc
      pAdicOrder p x = pAdicOrder p
          ((p : ℚ) ^ d.exponent * (d.numerator : ℚ) /
            (d.denominator : ℚ)) := hxval
      _ = pAdicOrder p
          ((p : ℚ) ^ d.exponent *
            ((d.numerator : ℚ) / (d.denominator : ℚ))) := by
        congr 1
        ring
  calc
    d.exponent = pAdicOrder p
        ((p : ℚ) ^ d.exponent *
          ((d.numerator : ℚ) / (d.denominator : ℚ))) := by
      rw [pAdicOrder, padicValRat.mul (zpow_ne_zero _ (by exact_mod_cast hp.ne_zero))
        (div_ne_zero (by exact_mod_cast d.numerator_ne_zero)
          (by exact_mod_cast d.denominator_ne_zero)), padicValRat.zpow,
        padicValRat.div (by exact_mod_cast d.numerator_ne_zero)
          (by exact_mod_cast d.denominator_ne_zero),
        (show padicValRat p (d.numerator : ℚ) = 0 from hpa),
        (show padicValRat p (d.denominator : ℚ) = 0 from hpb),
        padicValRat.self hp.one_lt]
      ring
    _ = pAdicOrder p x := hxval'.symm

/-- The exponent and the `p`-free rational unit are unique. The presentation
by an integer numerator and denominator is understood up to their usual
common rescaling, so the invariant unit is the rational fraction itself. -/
theorem primeAdicDecomposition_unique_exponent_and_unit {p : ℕ} (hp : p.Prime)
    {x : ℚ} (hx : x ≠ 0) {d e : PrimeAdicDecomposition p x} :
    d.exponent = e.exponent ∧
      (d.numerator : ℚ) / d.denominator =
      (e.numerator : ℚ) / e.denominator := by
  have hd := primeAdicDecomposition_exponent_eq_pAdicOrder hp hx d
  have he := primeAdicDecomposition_exponent_eq_pAdicOrder hp hx e
  have hexp : d.exponent = e.exponent := hd.trans he.symm
  have heq : (p : ℚ) ^ d.exponent * ((d.numerator : ℚ) / d.denominator) =
      (p : ℚ) ^ e.exponent * ((e.numerator : ℚ) / e.denominator) := by
    have hdunit : x = (p : ℚ) ^ d.exponent *
        ((d.numerator : ℚ) / d.denominator) := by
      calc
        x = (p : ℚ) ^ d.exponent * (d.numerator : ℚ) /
            (d.denominator : ℚ) := d.equation
        _ = (p : ℚ) ^ d.exponent * ((d.numerator : ℚ) / d.denominator) := by ring
    have heunit : x = (p : ℚ) ^ e.exponent *
        ((e.numerator : ℚ) / e.denominator) := by
      calc
        x = (p : ℚ) ^ e.exponent * (e.numerator : ℚ) /
            (e.denominator : ℚ) := e.equation
        _ = (p : ℚ) ^ e.exponent * ((e.numerator : ℚ) / e.denominator) := by ring
    calc
      (p : ℚ) ^ d.exponent * ((d.numerator : ℚ) / d.denominator) = x := hdunit.symm
      _ = (p : ℚ) ^ e.exponent * ((e.numerator : ℚ) / e.denominator) := heunit
  refine ⟨hexp, ?_⟩
  rw [hexp] at heq
  exact mul_left_cancel₀ (zpow_ne_zero _ (by exact_mod_cast hp.ne_zero)) heq

/-- Multiplication adds `p`-adic orders. -/
theorem pAdicOrder_mul {p : ℕ} (hp : p.Prime) {x y : ℚ}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    pAdicOrder p (x * y) = pAdicOrder p x + pAdicOrder p y := by
  letI : Fact p.Prime := ⟨hp⟩
  simpa [pAdicOrder] using (padicValRat.mul hx hy)

/-- Inversion negates `p`-adic order. -/
theorem pAdicOrder_inv {p : ℕ} (hp : p.Prime) {x : ℚ} (hx : x ≠ 0) :
    pAdicOrder p x⁻¹ = -pAdicOrder p x := by
  letI : Fact p.Prime := ⟨hp⟩
  simpa [pAdicOrder] using (padicValRat.inv x)

/-- The additive valuation inequality for `p`-adic order. -/
theorem pAdicOrderWithTop_add {p : ℕ} (hp : p.Prime) (x y : ℚ) :
    min (pAdicOrderWithTop p x) (pAdicOrderWithTop p y) ≤
      pAdicOrderWithTop p (x + y) := by
  by_cases hx : x = 0
  · subst x
    simp [pAdicOrderWithTop]
  by_cases hy : y = 0
  · subst y
    simp [pAdicOrderWithTop]
  by_cases hxy : x + y = 0
  · simp [pAdicOrderWithTop, hx, hy, hxy]
  letI : Fact p.Prime := ⟨hp⟩
  have h := padicValRat.min_le_padicValRat_add (p := p) hxy
  simpa [pAdicOrderWithTop, pAdicOrder, hx, hy, hxy] using
    (WithTop.coe_le_coe.mpr h)

/-- The ordinary integer form of the triangle inequality when the sum is
nonzero. -/
theorem pAdicOrder_add {p : ℕ} (hp : p.Prime) {x y : ℚ}
    (hxy : x + y ≠ 0) :
    min (pAdicOrder p x) (pAdicOrder p y) ≤ pAdicOrder p (x + y) := by
  letI : Fact p.Prime := ⟨hp⟩
  simpa [pAdicOrder] using (padicValRat.min_le_padicValRat_add (p := p) hxy)

/-- Unequal `p`-adic orders force equality with the lower order. -/
theorem pAdicOrder_add_of_ne {p : ℕ} (hp : p.Prime) {x y : ℚ}
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hne : pAdicOrder p x ≠ pAdicOrder p y) :
    pAdicOrder p (x + y) = min (pAdicOrder p x) (pAdicOrder p y) := by
  have hxy : x + y ≠ 0 := by
    intro hxy
    apply hne
    rw [eq_neg_of_add_eq_zero_right hxy]
    change padicValRat p x = padicValRat p (-x)
    rw [padicValRat.neg]
  letI : Fact p.Prime := ⟨hp⟩
  simpa [pAdicOrder] using (padicValRat.add_eq_min hxy hx hy hne)

/-- The `p`-adic order of `p` itself is one. -/
theorem pAdicOrder_self {p : ℕ} (hp : p.Prime) :
    pAdicOrder p (p : ℚ) = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  simpa [pAdicOrder] using padicValRat.self hp.one_lt

/-- The strict inequality in `v₃(1+2)` records cancellation modulo `3`. -/
theorem pAdic_cancellation_at_three :
    pAdicOrder 3 (1 + 2 : ℚ) >
      min (pAdicOrder 3 (1 : ℚ)) (pAdicOrder 3 (2 : ℚ)) := by
  have hp : Nat.Prime 3 := by norm_num
  have h3 : pAdicOrder 3 (3 : ℚ) = 1 := pAdicOrder_self hp
  have h1 : pAdicOrder 3 (1 : ℚ) = 0 := by
    rw [pAdicOrder, padicValRat.one]
  have h2 : pAdicOrder 3 (2 : ℚ) = 0 := by
    have h2' : padicValRat 3 (2 : ℚ) = multiplicity (3 : ℤ) (2 : ℤ) :=
      padicValRat.of_int_multiplicity (p := 3) (z := 2) (by norm_num) (by norm_num)
    rw [pAdicOrder, h2', multiplicity_eq_zero.mpr (by norm_num)]
    norm_num
  rw [show (1 + 2 : ℚ) = 3 by norm_num, h3]
  rw [h1, h2]
  norm_num

/-- The standard numerical example `v₃(45/14) = 2`. -/
example : pAdicOrder 3 (45 / 14 : ℚ) = 2 := by
  have h3 : padicValRat 3 (3 : ℚ) = 1 := padicValRat.self (by norm_num)
  have h5 : padicValRat 3 (5 : ℚ) = 0 := by
    rw [show (5 : ℚ) = ((5 : ℤ) : ℚ) by norm_num,
      padicValRat.of_int_multiplicity (p := 3) (z := 5) (by norm_num) (by norm_num),
      multiplicity_eq_zero.mpr (by norm_num)]
    norm_num
  have h2 : padicValRat 3 (2 : ℚ) = 0 := by
    rw [show (2 : ℚ) = ((2 : ℤ) : ℚ) by norm_num,
      padicValRat.of_int_multiplicity (p := 3) (z := 2) (by norm_num) (by norm_num),
      multiplicity_eq_zero.mpr (by norm_num)]
    norm_num
  have h7 : padicValRat 3 (7 : ℚ) = 0 := by
    rw [show (7 : ℚ) = ((7 : ℤ) : ℚ) by norm_num,
      padicValRat.of_int_multiplicity (p := 3) (z := 7) (by norm_num) (by norm_num),
      multiplicity_eq_zero.mpr (by norm_num)]
    norm_num
  have h45 : padicValRat 3 (45 : ℚ) = 2 := by
    rw [show (45 : ℚ) = 3 * 3 * 5 by norm_num,
      padicValRat.mul (by norm_num) (by norm_num),
      padicValRat.mul (by norm_num) (by norm_num), h3, h5]
    norm_num
  have h14 : padicValRat 3 (14 : ℚ) = 0 := by
    rw [show (14 : ℚ) = 2 * 7 by norm_num,
      padicValRat.mul (by norm_num) (by norm_num), h2, h7]
    norm_num
  rw [pAdicOrder, padicValRat.div (p := 3) (q := (45 : ℚ)) (r := 14)
    (by norm_num) (by norm_num), h45, h14]
  norm_num

/-- The standard cancellation example `v₃(1+2) = 1`. -/
example : pAdicOrder 3 (1 + 2 : ℚ) = 1 := by
  norm_num [pAdicOrder, padicValRat_def, padicValInt, padicValNat]

/-- The `p`-adic unit part of a nonzero rational number. -/
def pAdicUnitPart (p : ℕ) (x : ℚ) : ℚ :=
  x / (p : ℚ) ^ pAdicOrder p x

/-- A rational number is its `p`-power magnitude times its unit part. -/
theorem pAdic_magnitude_unit_decomposition {p : ℕ} (hp : p.Prime)
    {x : ℚ} (hx : x ≠ 0) :
    x = (p : ℚ) ^ pAdicOrder p x * pAdicUnitPart p x := by
  unfold pAdicUnitPart
  field_simp [show (p : ℚ) ≠ 0 by exact_mod_cast hp.ne_zero]

/-- The unit part has zero `p`-adic order. -/
theorem pAdicUnitPart_order_zero {p : ℕ} (hp : p.Prime)
    {x : ℚ} (hx : x ≠ 0) :
    pAdicOrder p (pAdicUnitPart p x) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpow : (p : ℚ) ^ pAdicOrder p x ≠ 0 := zpow_ne_zero _ hpq
  rw [pAdicUnitPart]
  change padicValRat p (x / (p : ℚ) ^ pAdicOrder p x) = 0
  rw [padicValRat.div hx hpow,
    padicValRat.zpow, padicValRat.self hp.one_lt]
  change padicValRat p x - padicValRat p x * 1 = 0
  ring

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
  simpa [originPrimeIdeal] using
    (Ideal.isPrime_span_singleton_of_prime
      (Polynomial.prime_X : Prime (Polynomial.X : k[X])))

/-- The prime ideal `(p)` in the integers. -/
def integerPrimeIdeal (p : ℕ) : Ideal ℤ :=
  Ideal.span ({(p : ℤ)} : Set ℤ)
instance integerPrimeIdeal_isPrime_inst (p : ℕ) [Fact p.Prime] :
    (integerPrimeIdeal p).IsPrime := by
  simpa [integerPrimeIdeal] using
    (Ideal.isPrime_span_singleton_of_prime
      (Nat.prime_iff_prime_int.1 (Fact.out : p.Prime)))

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
theorem originPrimeIdeal_isPrime : (originPrimeIdeal (k := k)).IsPrime := by
  exact inferInstance

/-- The integer ideal `(p)` is prime for a prime `p`. -/
theorem integerPrimeIdeal_isPrime {p : ℕ} (hp : p.Prime) :
    (integerPrimeIdeal p).IsPrime := by
  letI : Fact p.Prime := ⟨hp⟩
  exact inferInstance

/-- Localization at a prime is local. -/
theorem chapterLocalizationAtPrime_isLocalRing {A : Type*} [CommRing A]
    (P : Ideal A) [P.IsPrime] :
    IsLocalRing (chapterLocalizationAtPrime A P) := by
  exact IsLocalization.AtPrime.isLocalRing (Localization P.primeCompl) P

/-- The polynomial localization `k[t]_(t)` is a local ring. -/
theorem polynomialLocalRingAtZero_isLocalRing :
    IsLocalRing (polynomialLocalRingAtZero (k := k)) := by
  exact inferInstance

/-- The arithmetic localization `ℤ_(p)` is a local ring for prime `p`. -/
theorem integerLocalRingAtPrime_isLocalRing {p : ℕ} [Fact p.Prime] (hp : p.Prime) :
    IsLocalRing (integerLocalRingAtPrime p) := by
  exact inferInstance

/-- An affine-line denominator is a local unit precisely when it does not vanish
at the chosen point. -/
theorem polynomial_local_elements_are_fractions_with_unit_denominator (x : RatFunc k) :
    x ∈ polynomialLocalElementsAtZero (k := k) ↔
      ∃ f g : k[X], IsRegularAtZero g ∧
        x = algebraMap k[X] (RatFunc k) f / algebraMap k[X] (RatFunc k) g := by
  rfl

/-- The `p`-adic integral set is the set of rationals whose denominator is
prime to `p`. -/
theorem integer_local_elements_iff_nonnegative_pAdicOrder {p : ℕ}
    (hp : p.Prime) {x : ℚ} :
    x ∈ integerLocalElementsAtPrime p ↔ 0 ≤ pAdicOrder p x := by
  letI : Fact p.Prime := ⟨hp⟩
  constructor
  · rintro ⟨a, b, hb, hfree, hq⟩
    by_cases hx : x = 0
    · subst x
      simp [hx, pAdicOrder]
    have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
    have hq' : x = Rat.divInt a b := by
      rw [hq, Rat.intCast_div_eq_divInt]
    rw [pAdicOrder, padicValRat.defn p hx hq',
      multiplicity_eq_zero.mpr hfree]
    omega
  · intro h
    by_cases hx : x = 0
    · subst x
      have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
      exact ⟨0, 1, by norm_num, hprime.not_dvd_one, by simp⟩
    let d := Classical.choice (exists_primeAdicDecomposition hp hx)
    have hdexp : d.exponent = pAdicOrder p x :=
      primeAdicDecomposition_exponent_eq_pAdicOrder hp hx d
    have hnonneg : 0 ≤ d.exponent := by rw [hdexp]; exact h
    let n : ℕ := d.exponent.toNat
    have hncast : (n : ℤ) = d.exponent := Int.toNat_of_nonneg hnonneg
    refine ⟨(p : ℤ) ^ n * d.numerator, d.denominator,
      d.denominator_ne_zero, d.denominator_p_free, ?_⟩
    calc
      x = (p : ℚ) ^ d.exponent * (d.numerator : ℚ) /
          (d.denominator : ℚ) := d.equation
      _ = (((p : ℤ) ^ n * d.numerator : ℤ) : ℚ) /
          (d.denominator : ℚ) := by
        rw [← hncast, zpow_natCast]
        push_cast
        ring

/-- The no-pole part of the rational-function field is the nonnegative-order
part of the order at the origin. -/
noncomputable def rationalFunctionValuationRingAtZero : Subring (RatFunc k) :=
  { carrier := {x | x = 0 ∨ 0 ≤ ordZeroRatFunc x}
    zero_mem' := by simp
    one_mem' := by
      right
      simp [ordZeroRatFunc]
    add_mem' := by
      intro x y hx hy
      change x = 0 ∨ 0 ≤ ordZeroRatFunc x at hx
      change y = 0 ∨ 0 ≤ ordZeroRatFunc y at hy
      change x + y = 0 ∨ 0 ≤ ordZeroRatFunc (x + y)
      by_cases hx0 : x = 0
      · rcases hy with hy0 | hy
        · exact Or.inl (by simp [hx0, hy0])
        · exact Or.inr (by simpa [hx0] using hy)
      by_cases hy0 : y = 0
      · rcases hx with hx0' | hx
        · exact Or.inl (by simp [hx0', hy0])
        · exact Or.inr (by simpa [hy0] using hx)
      have hx' : 0 ≤ ordZeroRatFunc x := hx.resolve_left hx0
      have hy' : 0 ≤ ordZeroRatFunc y := hy.resolve_left hy0
      by_cases hxy : x + y = 0
      · simp [hxy]
      right
      exact (le_min hx' hy').trans (ordZeroRatFunc_add_lower hx0 hy0 hxy)
    mul_mem' := by
      intro x y hx hy
      rcases hx with rfl | hx
      · simp
      rcases hy with rfl | hy
      · simp
      by_cases hx0 : x = 0
      · simp [hx0]
      by_cases hy0 : y = 0
      · simp [hy0]
      right
      rw [ordZeroRatFunc_mul hx0 hy0]
      exact add_nonneg hx hy
    neg_mem' := by
      intro x hx
      rcases hx with rfl | hx
      · simp
      by_cases hx0 : x = 0
      · simp [hx0]
      right
      have hone : ordZeroRatFunc (-1 : RatFunc k) = 0 := by
        calc
          ordZeroRatFunc (-1 : RatFunc k) =
              ordZeroFraction (-1 : k[X]) 1 := by
            apply ordZeroRatFunc_eq_ordZeroFraction
              (f := (-1 : k[X])) (g := 1) (by simp) (by simp)
            simp
          _ = 0 := by simp [ordZeroFraction]
      rw [show -x = (-1 : RatFunc k) * x by ring,
        ordZeroRatFunc_mul (by simp) hx0, hone, zero_add]
      exact hx }

/-- The local units at the origin are the nonzero functions of order zero. -/
def rationalFunctionUnitsAtZero : Set (RatFunc k) :=
  {x | x ≠ 0 ∧ ordZeroRatFunc x = 0}

/-- The affine-line local set is exactly the set of rational functions without a
pole at the origin. -/
theorem polynomial_local_elements_iff_no_pole (x : RatFunc k) :
    x ∈ polynomialLocalElementsAtZero (k := k) ↔
      x ∈ rationalFunctionValuationRingAtZero (k := k) := by
  constructor
  · rintro ⟨f, g, hg, hx⟩
    by_cases hf : f = 0
    · left
      rw [hx, hf, map_zero, zero_div]
    right
    have hg0 : g ≠ 0 := by
      intro hg0
      apply hg
      simp [hg0]
    have hx0 : x ≠ 0 := by
      intro hx0
      apply hf
      have hmap : algebraMap k[X] (RatFunc k) f = 0 := by
        have hfrac : algebraMap k[X] (RatFunc k) f /
            algebraMap k[X] (RatFunc k) g = 0 := by
          calc
            algebraMap k[X] (RatFunc k) f /
                algebraMap k[X] (RatFunc k) g = x := hx.symm
            _ = 0 := hx0
        rcases (div_eq_zero_iff).mp hfrac with h | h
        · exact h
        · exact (RatFunc.algebraMap_ne_zero hg0 h).elim
      exact (map_eq_zero_iff (algebraMap k[X] (RatFunc k))
        (RatFunc.algebraMap_injective k)).mp hmap
    have horder := ordZeroRatFunc_eq_ordZeroFraction hg0 hx0 hx
    have hden : ordZeroPolynomial g = 0 :=
      (ordZeroPolynomial_eq_zero_iff_eval_ne_zero hg0).2 hg
    have hnonneg : 0 ≤ ordZeroFraction f g := by
      unfold ordZeroFraction
      have hden' : multiplicity (Polynomial.X : k[X]) g = 0 := by
        simpa [ordZeroPolynomial] using hden
      rw [hden']
      omega
    exact horder ▸ hnonneg
  · intro hx
    rcases hx with rfl | hx
    · exact ⟨0, 1, by simp, by simp⟩
    by_cases hx0 : x = 0
    · subst x
      exact ⟨0, 1, by simp, by simp⟩
    let d := ratFuncZeroOrderFactorization hx0
    have hX : algebraMap k[X] (RatFunc k) (Polynomial.X : k[X]) ≠ 0 :=
      RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
    have hcoord : ordZeroRatFunc (k := k) (ratFuncCoordinate (k := k)) = 1 := by
      calc
        ordZeroRatFunc (k := k) (ratFuncCoordinate (k := k)) = ordZeroFraction
            (Polynomial.X : k[X]) 1 := by
          apply ordZeroRatFunc_eq_ordZeroFraction (f := Polynomial.X) (g := 1)
            one_ne_zero hX
          simp [ratFuncCoordinate]
        _ = 1 := by
          simp [ordZeroFraction, multiplicity_of_one_right
            Polynomial.prime_X.not_isUnit]
    have hxe : ordZeroRatFunc x = d.exponent := by
      calc
        ordZeroRatFunc x =
            ordZeroRatFunc (ratFuncCoordinate ^ d.exponent * d.unit) :=
          congrArg ordZeroRatFunc d.equation
        _ = ordZeroRatFunc (ratFuncCoordinate ^ d.exponent) +
            ordZeroRatFunc d.unit := by
          simpa [ratFuncCoordinate] using
            (ordZeroRatFunc_mul
              (x := (algebraMap k[X] (RatFunc k) (Polynomial.X : k[X])) ^ d.exponent)
              (y := d.unit) (zpow_ne_zero _ hX)
              (by
                intro hunit
                apply hx0
                calc
                  x = ratFuncCoordinate ^ d.exponent * d.unit := d.equation
                  _ = 0 := by rw [hunit, mul_zero]))
        _ = d.exponent := by
          have hz : ordZeroRatFunc (ratFuncCoordinate (k := k) ^ d.exponent) =
              d.exponent * ordZeroRatFunc (ratFuncCoordinate (k := k)) := by
            simpa [ratFuncCoordinate] using
              (ordZeroRatFunc_zpow
                (x := algebraMap k[X] (RatFunc k) (Polynomial.X : k[X])) hX
                d.exponent)
          rw [hz, hcoord,
            ordZeroRatFunc_of_regular_unit d.unit_regular_at_zero]
          simp
    have he : 0 ≤ d.exponent := by rw [← hxe]; exact hx
    cases hd : d.exponent with
    | ofNat n =>
        refine ⟨(Polynomial.X : k[X]) ^ n * d.unit.num, d.unit.denom,
          d.unit_regular_at_zero.2, ?_⟩
        calc
          x = ratFuncCoordinate ^ d.exponent * d.unit := d.equation
          _ = algebraMap k[X] (RatFunc k)
              ((Polynomial.X : k[X]) ^ n * d.unit.num) /
              algebraMap k[X] (RatFunc k) d.unit.denom := by
            rw [hd]
            change ratFuncCoordinate ^ (n : ℤ) * d.unit = _
            rw [zpow_natCast, ratFuncCoordinate]
            conv_lhs =>
              rw [← RatFunc.num_div_denom d.unit]
            simp only [map_pow, map_mul]
            ring
    | negSucc n =>
        omega

/-- In additive notation, the maximal ideal of a valuation subring consists of
the positive-valued elements. -/
theorem additive_valuation_subring_maximalIdeal_iff_positive
    {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ))
    (x : v.toValuation.valuationSubring) :
    x ∈ IsLocalRing.maximalIdeal v.toValuation.valuationSubring ↔
      (0 : WithTop ℤ) < v (x : K) := by
  rw [ValuationSubring.valuation_lt_one_iff]
  calc
    v.toValuation.valuationSubring.valuation (x : K) < 1 ↔
        v.toValuation (x : K) < 1 :=
      (Valuation.isEquiv_valuation_valuationSubring v.toValuation).lt_one_iff_lt_one.symm
    _ ↔ (0 : WithTop ℤ) < v (x : K) := by
      change OrderDual.toDual (v (x : K)) <
        OrderDual.toDual (0 : WithTop ℤ) ↔ _
      exact OrderDual.toDual_lt_toDual

/-- The nonzero elements of a discrete additive valuation ring are powers of a
uniformizer times units. -/
theorem discrete_additive_valuation_factorization {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (π : K) (hπ : v π = 1)
    (x : v.toValuation.valuationSubring) (hx : x ≠ 0) :
    ∃ n : ℕ, ∃ u : v.toValuation.valuationSubringˣ,
      (x : K) = π ^ n * (u : K) := by
  have hxK : (x : K) ≠ 0 := by
    intro h
    apply hx
    exact Subtype.ext h
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, v.map_zero] at hπ
    simp at hπ
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp (v.ne_top_iff.mpr hxK)
  have hqx : (0 : WithTop ℤ) ≤ v (x : K) := by
    have hxmem : v.toValuation (x : K) ≤ 1 := x.property
    change OrderDual.toDual (v (x : K)) ≤
      OrderDual.toDual (0 : WithTop ℤ) at hxmem
    exact OrderDual.toDual_le_toDual.mp hxmem
  have hqnonneg : (0 : ℤ) ≤ q := by
    apply WithTop.coe_le_coe.mp
    simpa [hq]
  let n : ℕ := q.toNat
  have hnq : (n : ℤ) = q := Int.toNat_of_nonneg hqnonneg
  let u0 : K := π ^ (-q) * (x : K)
  have hu0val : v u0 = 0 := by
    dsimp [u0]
    have hsmul : ∀ z : ℤ, z • (1 : WithTop ℤ) = (z : WithTop ℤ) := by
      intro z
      cases z with
      | ofNat n =>
          rw [Int.ofNat_eq_natCast, natCast_zsmul]
          calc
            n • (1 : WithTop ℤ) =
                ((n • (1 : ℤ) : ℤ) : WithTop ℤ) := by
              rw [WithTop.coe_nsmul, WithTop.coe_one]
            _ = (Int.ofNat n : WithTop ℤ) := by
              rw [Nat.smul_one_eq_cast, Int.ofNat_eq_natCast]
      | negSucc n =>
          rw [negSucc_zsmul]
          calc
            -((n + 1) • (1 : WithTop ℤ)) =
                -(((n + 1) • (1 : ℤ) : ℤ) : WithTop ℤ) := by
              rw [WithTop.coe_nsmul, WithTop.coe_one]
            _ = (Int.negSucc n : WithTop ℤ) := by
              rw [Nat.smul_one_eq_cast]
              simp [Int.negSucc_eq,
                WithTop.LinearOrderedAddCommGroup.coe_neg]
    have hv_zpow : ∀ z : ℤ, v (π ^ z) = z • v π := by
      intro z
      cases z with
      | ofNat n => simp [v.map_pow, hπ]
      | negSucc n =>
          rw [zpow_negSucc, v.map_inv, v.map_pow, hπ]
          rw [hsmul (Int.negSucc n)]
          simp [Int.negSucc_eq]
    rw [v.map_mul, hv_zpow, hπ, ← hq]
    rw [hsmul (-q)]
    simp
  have hu0invval : v u0⁻¹ = 0 := by
    rw [v.map_inv, hu0val, neg_zero]
  have hu0mem : u0 ∈ v.toValuation.valuationSubring := by
    change OrderDual.toDual (v u0) ≤ OrderDual.toDual (0 : WithTop ℤ)
    rw [hu0val]
  have hu0invmem : u0⁻¹ ∈ v.toValuation.valuationSubring := by
    change OrderDual.toDual (v u0⁻¹) ≤ OrderDual.toDual (0 : WithTop ℤ)
    rw [hu0invval]
  have hu0 : u0 ≠ 0 := by
    dsimp [u0]
    exact mul_ne_zero (zpow_ne_zero _ hπ0) hxK
  let u : v.toValuation.valuationSubringˣ :=
    { val := ⟨u0, hu0mem⟩
      inv := ⟨u0⁻¹, hu0invmem⟩
      val_inv := by ext; exact mul_inv_cancel₀ hu0
      inv_val := by ext; exact inv_mul_cancel₀ hu0 }
  refine ⟨n, u, ?_⟩
  dsimp [u, u0]
  rw [← hnq]
  calc
    (x : K) = (π ^ (n : ℤ) * π ^ (-(n : ℤ))) * (x : K) := by
      rw [← zpow_add₀ hπ0, add_neg_cancel, zpow_zero, one_mul]
    _ = π ^ n * (π ^ (-(n : ℤ)) * (x : K)) := by
      rw [zpow_natCast]
      ring

/-- The corresponding factorization for a nonzero `p`-adic integral rational. -/
theorem pAdic_integral_factorization {p : ℕ} (hp : p.Prime) {x : ℚ}
    (hx : x ≠ 0) (hIntegral : 0 ≤ pAdicOrder p x) :
    ∃ n : ℕ, ∃ u : ℚ,
      pAdicOrder p u = 0 ∧ x = (p : ℚ) ^ n * u := by
  letI : Fact p.Prime := ⟨hp⟩
  let d := Classical.choice (exists_primeAdicDecomposition hp hx)
  have hdexp : d.exponent = pAdicOrder p x :=
    primeAdicDecomposition_exponent_eq_pAdicOrder hp hx d
  have he : 0 ≤ d.exponent := by rw [hdexp]; exact hIntegral
  let n : ℕ := d.exponent.toNat
  have hn : (n : ℤ) = d.exponent := Int.toNat_of_nonneg he
  let u : ℚ := (d.numerator : ℚ) / d.denominator
  refine ⟨n, u, ?_, ?_⟩
  · dsimp [u, pAdicOrder]
    rw [padicValRat.div (by exact_mod_cast d.numerator_ne_zero)
      (by exact_mod_cast d.denominator_ne_zero),
      padicValRat.of_int_multiplicity hp.ne_one d.numerator_ne_zero,
      padicValRat.of_int_multiplicity hp.ne_one d.denominator_ne_zero,
      multiplicity_eq_zero.mpr d.numerator_p_free,
      multiplicity_eq_zero.mpr d.denominator_p_free]
    ring
  · have deq : x = (p : ℚ) ^ d.exponent * u := by
      calc
        x = (p : ℚ) ^ d.exponent * (d.numerator : ℚ) /
            (d.denominator : ℚ) := d.equation
        _ = (p : ℚ) ^ d.exponent * u := by
          dsimp [u]
          ring
    calc
      x = (p : ℚ) ^ d.exponent * u := deq
      _ = (p : ℚ) ^ n * u := by rw [← hn, zpow_natCast]

/-- The corresponding factorization for a rational function without a pole at
the origin. -/
theorem zero_order_integral_factorization {x : RatFunc k}
    (hx : x ≠ 0) (hIntegral : 0 ≤ ordZeroRatFunc x) :
    ∃ n : ℕ, ∃ u : RatFunc k,
      ordZeroRatFunc u = 0 ∧ x = ratFuncCoordinate ^ n * u := by
  let d := ratFuncZeroOrderFactorization hx
  have hX : algebraMap k[X] (RatFunc k) (Polynomial.X : k[X]) ≠ 0 :=
    RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
  have hcoord : ordZeroRatFunc (k := k) (ratFuncCoordinate (k := k)) = 1 := by
    calc
      ordZeroRatFunc (k := k) (ratFuncCoordinate (k := k)) = ordZeroFraction
          (Polynomial.X : k[X]) 1 := by
        apply ordZeroRatFunc_eq_ordZeroFraction (f := Polynomial.X) (g := 1)
          one_ne_zero hX
        simp [ratFuncCoordinate]
      _ = 1 := by
        simp [ordZeroFraction, multiplicity_of_one_right
          Polynomial.prime_X.not_isUnit]
  have hxe : ordZeroRatFunc x = d.exponent := by
    calc
      ordZeroRatFunc x =
          ordZeroRatFunc (ratFuncCoordinate ^ d.exponent * d.unit) :=
        congrArg ordZeroRatFunc d.equation
      _ = ordZeroRatFunc (ratFuncCoordinate ^ d.exponent) +
          ordZeroRatFunc d.unit := by
        simpa [ratFuncCoordinate] using
          (ordZeroRatFunc_mul
            (x := (algebraMap k[X] (RatFunc k) (Polynomial.X : k[X])) ^ d.exponent)
            (y := d.unit) (zpow_ne_zero _ hX)
            (by
              intro hunit
              apply hx
              calc
                x = ratFuncCoordinate ^ d.exponent * d.unit := d.equation
                _ = 0 := by rw [hunit, mul_zero]))
      _ = d.exponent := by
        have hz : ordZeroRatFunc (ratFuncCoordinate (k := k) ^ d.exponent) =
            d.exponent * ordZeroRatFunc (ratFuncCoordinate (k := k)) := by
          simpa [ratFuncCoordinate] using
            (ordZeroRatFunc_zpow
              (x := algebraMap k[X] (RatFunc k) (Polynomial.X : k[X])) hX
              d.exponent)
        rw [hz, hcoord,
          ordZeroRatFunc_of_regular_unit d.unit_regular_at_zero]
        simp
  have he : 0 ≤ d.exponent := by rw [← hxe]; exact hIntegral
  let n : ℕ := d.exponent.toNat
  have hn : (n : ℤ) = d.exponent := Int.toNat_of_nonneg he
  refine ⟨n, d.unit, ordZeroRatFunc_of_regular_unit d.unit_regular_at_zero, ?_⟩
  calc
    x = ratFuncCoordinate ^ d.exponent * d.unit := d.equation
    _ = ratFuncCoordinate ^ n * d.unit := by rw [← hn, zpow_natCast]

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
    ValuationRing (chapterValuationSubring V hV) := by
  exact inferInstance

/-- The order on a valuation subring is recovered from divisibility by principal
fractional ideals. -/
def ChapterPrincipalIdealDivides {K : Type*} [Field K]
    (V : ValuationSubring K) (x y : K) : Prop :=
  ∃ a : V, (a : K) * y = x

/-- Principal-ideal divisibility and the valuation order agree. -/
theorem chapterPrincipalIdealDivides_iff_valuation_le {K : Type*} [Field K]
    (V : ValuationSubring K) (x y : K) :
    ChapterPrincipalIdealDivides V x y ↔ V.valuation x ≤ V.valuation y := by
  exact (V.valuation_le_iff x y).symm

/-- Principal fractional ideals are totally ordered in a valuation ring. -/
theorem chapterPrincipalIdealDivides_total {K : Type*} [Field K]
    (V : ValuationSubring K) (x y : K) :
    ChapterPrincipalIdealDivides V x y ∨ ChapterPrincipalIdealDivides V y x := by
  rcases le_total (V.valuation x) (V.valuation y) with h | h
  · exact Or.inl ((chapterPrincipalIdealDivides_iff_valuation_le V x y).2 h)
  · exact Or.inr ((chapterPrincipalIdealDivides_iff_valuation_le V y x).2 h)

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

private theorem dedekindExponent_valuation
    (P : IsDedekindDomain.HeightOneSpectrum A) {x : K} (hx : x ≠ 0) :
    P.valuation K x = WithZero.exp (-(dedekindExponent P x)) := by
  obtain ⟨a, d, hd, hxrep⟩ := IsFractionRing.div_surjective A x
  have ha : a ≠ 0 := by
    intro ha
    apply hx
    rw [← hxrep, ha, map_zero, zero_div]
  have hI : FractionalIdeal.spanSingleton A⁰ x ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx
  have hfac : FractionalIdeal.spanSingleton A⁰ x =
      FractionalIdeal.spanSingleton A⁰ (algebraMap A K d)⁻¹ *
        (Ideal.span ({a} : Set A) : FractionalIdeal A⁰ K) := by
    rw [← hxrep, FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    apply congr_arg
    rw [div_eq_mul_inv, mul_comm]
  have hcount := FractionalIdeal.count_well_defined K P hI hfac
  have hcount' : dedekindExponent P x =
      (multiplicity P.asIdeal (Ideal.span ({a} : Set A)) : ℤ) -
        multiplicity P.asIdeal (Ideal.span ({d} : Set A)) := by
    unfold dedekindExponent
    rw [hcount, Ideal.count_associates_factors_eq
      (Submodule.span_singleton_eq_bot.mp.mt ha) P.isPrime P.ne_bot,
      IsDedekindDomain.HeightOneSpectrum.count_normalizedFactors_eq_multiplicity
        (Submodule.span_singleton_eq_bot.mp.mt ha) P,
      Ideal.count_associates_factors_eq
        (Submodule.span_singleton_eq_bot.mp.mt
          (mem_nonZeroDivisors_iff_ne_zero.mp hd)) P.isPrime P.ne_bot,
      IsDedekindDomain.HeightOneSpectrum.count_normalizedFactors_eq_multiplicity
        (Submodule.span_singleton_eq_bot.mp.mt
          (mem_nonZeroDivisors_iff_ne_zero.mp hd)) P]
  have hmk : IsLocalization.mk' K a ⟨d, hd⟩ =
      algebraMap A K a / algebraMap A K d :=
    IsFractionRing.mk'_eq_div ⟨d, hd⟩
  conv_lhs => rw [← hxrep, ← hmk]
  rw [P.valuation_of_mk',
    P.intValuation_eq_exp_neg_multiplicity ha,
    P.intValuation_eq_exp_neg_multiplicity
      (mem_nonZeroDivisors_iff_ne_zero.mp hd), ← WithZero.exp_sub]
  congr 1
  rw [hcount']
  ring

/-- A nonzero principal fractional ideal factors over the height-one primes. -/
theorem dedekind_principal_fractional_ideal_factorization {x : K} (hx : x ≠ 0) :
    ∏ᶠ P : IsDedekindDomain.HeightOneSpectrum A,
      (P.asIdeal : FractionalIdeal A⁰ K) ^ dedekindExponent P x =
        chapterPrincipalFractionalIdeal x := by
  unfold chapterPrincipalFractionalIdeal dedekindExponent
  apply FractionalIdeal.finprod_heightOneSpectrum_factorization'
  exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx

/-- Only finitely many height-one exponents of a nonzero principal fractional
ideal are nonzero. -/
theorem dedekindExponent_finite_support {x : K} (hx : x ≠ 0) :
    {P : IsDedekindDomain.HeightOneSpectrum A | dedekindExponent P x ≠ 0}.Finite := by
  have h := FractionalIdeal.finite_factors
    (FractionalIdeal.spanSingleton A⁰ x)
  have h' : ∀ᶠ P : IsDedekindDomain.HeightOneSpectrum A in Filter.cofinite,
      dedekindExponent P x = 0 := by
    simpa [dedekindExponent] using h
  exact (Filter.eventually_cofinite.1 h')

/-- The exponent is additive under multiplication of nonzero elements. -/
theorem dedekindExponent_mul (P : IsDedekindDomain.HeightOneSpectrum A)
    {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    dedekindExponent P (x * y) = dedekindExponent P x + dedekindExponent P y := by
  unfold dedekindExponent
  rw [show FractionalIdeal.spanSingleton A⁰ (x * y) =
      FractionalIdeal.spanSingleton A⁰ x * FractionalIdeal.spanSingleton A⁰ y by
        rw [← FractionalIdeal.spanSingleton_mul_spanSingleton]]
  exact FractionalIdeal.count_mul K P
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy)

/-- The exponent of an element that is a unit of the Dedekind domain is zero. -/
theorem dedekindExponent_unit (P : IsDedekindDomain.HeightOneSpectrum A)
    (u : Aˣ) :
    dedekindExponent P (algebraMap A K (u : A)) = 0 := by
  unfold dedekindExponent
  rw [show FractionalIdeal.spanSingleton A⁰ (algebraMap A K (u : A)) =
      FractionalIdeal.spanSingleton A⁰ (1 : K) by
        apply FractionalIdeal.spanSingleton_eq_spanSingleton.mpr
        refine ⟨u⁻¹, ?_⟩
        rw [Units.smul_def, Algebra.smul_def]
        simp,
    FractionalIdeal.spanSingleton_one]
  exact FractionalIdeal.count_one K P

/-- The Dedekind exponent satisfies the valuation inequality under addition. -/
theorem dedekindExponent_add (P : IsDedekindDomain.HeightOneSpectrum A)
    {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (dedekindExponent P x) (dedekindExponent P y) ≤
      dedekindExponent P (x + y) := by
  have hval := map_add_le_max (P.valuation K) x y
  rw [dedekindExponent_valuation P hx, dedekindExponent_valuation P hy,
    dedekindExponent_valuation P hxy] at hval
  rcases le_total (dedekindExponent P x) (dedekindExponent P y) with hxy' | hyx'
  · have hmax : max (WithZero.exp (-(dedekindExponent P x)))
        (WithZero.exp (-(dedekindExponent P y))) =
        WithZero.exp (-(dedekindExponent P x)) := by
      rw [max_eq_left]
      simp only [WithZero.exp_le_exp]
      omega
    rw [hmax] at hval
    rw [WithZero.exp_le_exp] at hval
    omega
  · have hmax : max (WithZero.exp (-(dedekindExponent P x)))
        (WithZero.exp (-(dedekindExponent P y))) =
        WithZero.exp (-(dedekindExponent P y)) := by
      rw [max_eq_right]
      simp only [WithZero.exp_le_exp]
      omega
    rw [hmax] at hval
    rw [WithZero.exp_le_exp] at hval
    omega

/-- Unequal Dedekind exponents cannot cancel in a sum. -/
theorem dedekindExponent_add_of_ne (P : IsDedekindDomain.HeightOneSpectrum A)
    {x y : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hne : dedekindExponent P x ≠ dedekindExponent P y) :
    dedekindExponent P (x + y) = min (dedekindExponent P x) (dedekindExponent P y) := by
  have hxy : x + y ≠ 0 := by
    intro hxy
    apply hne
    have hyneg : y = -x := eq_neg_of_add_eq_zero_right hxy
    have hnegone : dedekindExponent P (-1 : K) = 0 := by
      simpa using (dedekindExponent_unit (A := A) (K := K) P (-1 : Aˣ))
    rw [hyneg]
    calc
      dedekindExponent P x =
          dedekindExponent P ((-1 : K) * x) := by
        rw [dedekindExponent_mul P (by simp) hx, hnegone, zero_add]
      _ = dedekindExponent P (-x) := by
        rw [show -x = (-1 : K) * x by ring,
          dedekindExponent_mul P (by simp) hx, hnegone, zero_add]
  have hneval : P.valuation K x ≠ P.valuation K y := by
    intro hval
    rw [dedekindExponent_valuation P hx, dedekindExponent_valuation P hy] at hval
    have : dedekindExponent P x = dedekindExponent P y := by
      rw [WithZero.exp_inj] at hval
      omega
    exact hne this
  have hval := Valuation.map_add_of_distinct_val (P.valuation K) hneval
  rw [dedekindExponent_valuation P hx, dedekindExponent_valuation P hy,
    dedekindExponent_valuation P hxy] at hval
  rcases le_total (dedekindExponent P x) (dedekindExponent P y) with hxy' | hyx'
  · rw [max_eq_left] at hval
    · rw [WithZero.exp_inj] at hval
      omega
    · simp only [WithZero.exp_le_exp]
      omega
  · rw [max_eq_right] at hval
    · rw [WithZero.exp_inj] at hval
      omega
    · simp only [WithZero.exp_le_exp]
      omega

/-- The exponent of an inverse is the negative exponent. -/
theorem dedekindExponent_inv (P : IsDedekindDomain.HeightOneSpectrum A)
    {x : K} (hx : x ≠ 0) :
    dedekindExponent P x⁻¹ = -dedekindExponent P x := by
  unfold dedekindExponent
  rw [show FractionalIdeal.spanSingleton A⁰ x⁻¹ =
      (FractionalIdeal.spanSingleton A⁰ x)⁻¹ by
        rw [← FractionalIdeal.spanSingleton_inv]]
  exact FractionalIdeal.count_inv K P _

/-- Every element of the fraction field can be tested in a localization at a
prime using a denominator outside that prime. -/
def IsInChapterLocalizationAtPrime (P : Ideal A) [P.IsPrime] (x : K) : Prop :=
  ∃ a : A, ∃ s : P.primeCompl,
    x * algebraMap A K (s : A) = algebraMap A K a

/-- A denominator outside `P` contributes no `P`-factor. -/
theorem dedekindExponent_primeCompl_eq_zero
    (P : IsDedekindDomain.HeightOneSpectrum A) (s : P.asIdeal.primeCompl) :
    dedekindExponent P (algebraMap A K (s : A)) = 0 := by
  have hs : algebraMap A K (s : A) ≠ 0 :=
    map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective A K)
      (P.asIdeal.primeCompl_le_nonZeroDivisors s.2)
  have hval := dedekindExponent_valuation P hs
  rw [P.valuation_of_algebraMap,
    P.intValuation_eq_one_iff.mpr s.2, ← WithZero.exp_zero] at hval
  rw [WithZero.exp_inj] at hval
  omega

/-- Membership in the localization at `P` is exactly nonnegative `P`-adic
exponent. -/
theorem localization_membership_iff_dedekindExponent_nonnegative
    (P : IsDedekindDomain.HeightOneSpectrum A) (x : K) :
    IsInChapterLocalizationAtPrime P.asIdeal x ↔ 0 ≤ dedekindExponent P x := by
  by_cases hx : x = 0
  · subst x
    constructor
    · intro _
      simp [dedekindExponent, FractionalIdeal.spanSingleton_zero,
        FractionalIdeal.count_zero]
    · intro _
      exact ⟨0, ⟨1, P.asIdeal.primeCompl.one_mem⟩, by simp⟩
  constructor
  · rintro ⟨a, s, hxs⟩
    have hval : P.valuation K x ≤ 1 := by
      calc
        P.valuation K x = P.valuation K x * 1 := by simp
        _ = P.valuation K (x * algebraMap A K (s : A)) := by
          rw [map_mul, P.valuation_of_algebraMap,
            P.intValuation_eq_one_iff.mpr s.2]
        _ = P.valuation K (algebraMap A K a) := by rw [hxs]
        _ ≤ 1 := P.valuation_le_one a
    have hval' := dedekindExponent_valuation P hx
    rw [hval', ← WithZero.exp_zero, WithZero.exp_le_exp] at hval
    omega
  · intro h
    exact P.exists_primeCompl_mul_eq_of_integer x (by
      have hval := dedekindExponent_valuation P hx
      rw [hval, ← WithZero.exp_zero, WithZero.exp_le_exp]
      omega)

/-- A general nonzero prime of a Dedekind domain gives a height-one spectrum
point. -/
def chapterHeightOneSpectrumOfPrime (P : Ideal A) [P.IsPrime] (hP : P ≠ ⊥) :
    IsDedekindDomain.HeightOneSpectrum A :=
  ⟨P, inferInstance, hP⟩

/-- The localization at a nonzero prime is a discrete valuation ring. -/
theorem dedekind_localization_at_nonzero_prime_isDVR (P : Ideal A) [P.IsPrime]
    (hP : P ≠ ⊥) :
    IsDiscreteValuationRing (chapterLocalizationAtPrime A P) := by
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    A hP (Localization P.primeCompl)

end DedekindLocalizations

/-! ## 1.5 Measurements that are not discrete -/

section PuiseuxValuation

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- A denominator stage of the Puiseux tower is modeled by a Laurent series in
the variable `t^(1/n)`.  The stage embeddings, their nesting under divisibility,
and the valuation are packaged as an interface since Mathlib does not select
one concrete construction of the full Puiseux union. -/
structure PuiseuxValuationModel where
  stage : ∀ n : ℕ, 0 < n → LaurentSeries k →ₐ[k] K
  stage_injective : ∀ (n : ℕ) (hn : 0 < n), Function.Injective (stage n hn)
  stage_image_nested : ∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), m ∣ n →
    ∀ f : LaurentSeries k, ∃ g : LaurentSeries k,
      stage n hn g = stage m hm f
  union : ∀ x : K, ∃ n : ℕ, ∃ hn : 0 < n, ∃ f : LaurentSeries k,
    stage n hn f = x
  valuation : AddValuation K (WithTop ℚ)
  stage_valuation : ∀ (n : ℕ) (hn : 0 < n) (f : LaurentSeries k), f ≠ 0 →
    valuation (stage n hn f) =
      (((f.order : ℚ) / (n : ℚ)) : WithTop ℚ)

/-- The lowest exponent in the `n`th stage lies in `(1/n)ℤ`. -/
def puiseuxStageExponent (n : ℕ) (hn : 0 < n) (f : LaurentSeries k) : ℚ :=
  (f.order : ℚ) / (n : ℚ)

/-- The `n`th Laurent-series stage has exponents in `1/n · ℤ`. -/
theorem puiseuxStageExponent_mem_one_div_n_z {n : ℕ} (hn : 0 < n)
    (f : LaurentSeries k) :
    puiseuxStageExponent n hn f ∈ Set.range (fun z : ℤ => (z : ℚ) / (n : ℚ)) := by
  exact ⟨f.order, rfl⟩

/-- Every rational exponent is realized by a nonzero single-term Laurent
series in a suitable stage. -/
theorem puiseuxStageExponent_surjective (q : ℚ) :
    ∃ n : ℕ, ∃ hn : 0 < n, ∃ f : LaurentSeries k, f ≠ 0 ∧
      ((f.order : ℚ) / (n : ℚ)) = q := by
  let f : LaurentSeries k := HahnSeries.single q.num (1 : k)
  refine ⟨q.den, q.den_pos, f, ?_, ?_⟩
  · dsimp [f]
    exact HahnSeries.single_ne_zero one_ne_zero
  · dsimp [f]
    rw [HahnSeries.order_single one_ne_zero]
    exact q.num_div_den

/-- The valuation is well-defined on overlaps of the stages. -/
theorem puiseux_overlap_valuation_well_defined (M : PuiseuxValuationModel (k := k) (K := K))
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {f g : LaurentSeries k}
    (hf : f ≠ 0) (hg : g ≠ 0) (hfg : M.stage m hm f = M.stage n hn g) :
    puiseuxStageExponent m hm f = puiseuxStageExponent n hn g := by
  change ((f.order : ℚ) / (m : ℚ)) = ((g.order : ℚ) / (n : ℚ))
  have hval := congrArg M.valuation hfg
  rw [M.stage_valuation m hm f hf, M.stage_valuation n hn g hg] at hval
  exact WithTop.coe_eq_coe.mp hval

/-- The value group of the Puiseux valuation is represented by the rationals. -/
def puiseuxValueSet (M : PuiseuxValuationModel (k := k) (K := K)) : Set ℚ :=
  {q | ∃ x : K, x ≠ 0 ∧ M.valuation x = (q : WithTop ℚ)}

/-- Every rational value occurs in the Puiseux tower. -/
theorem puiseuxValueSet_eq_univ (M : PuiseuxValuationModel (k := k) (K := K)) :
    puiseuxValueSet M = Set.univ := by
  ext q
  constructor
  · intro _
    exact Set.mem_univ q
  · intro _
    obtain ⟨n, hn, f, hf, hq⟩ := puiseuxStageExponent_surjective (k := k) q
    refine ⟨M.stage n hn f, ?_, ?_⟩
    · intro hzero
      apply hf
      apply M.stage_injective n hn
      simpa using hzero
    · simpa [M.stage_valuation n hn f hf] using hq

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
    IsChapterRankOneOrderedGroup ℚ := by
  intro a b ha hb
  obtain ⟨n, hn⟩ := exists_nat_ge (a / b)
  refine ⟨n, ?_⟩
  norm_num [nsmul_eq_mul]
  exact (div_le_iff₀ hb).mp hn

/-- The rational value group has no least positive element. -/
theorem rational_value_group_has_no_least_positive :
    ¬IsChapterDiscreteOrderedGroup ℚ := by
  rintro ⟨q, hq, hleast⟩
  let r : ℚ := q / 2
  have hr : 0 < r := by
    dsimp [r]
    linarith
  have hrq : r < q := by
    dsimp [r]
    linarith
  exact (not_lt_of_ge (hleast r hr)) hrq

/-- Explicitly, every positive rational has a smaller positive rational. -/
theorem exists_smaller_positive_rational {q : ℚ} (hq : 0 < q) :
    ∃ r : ℚ, 0 < r ∧ r < q := by
  refine ⟨q / 2, by linarith, by linarith⟩

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
    x ∈ puiseuxValuationRing M ↔ (0 : WithTop ℚ) ≤ M.valuation x := by
  change M.valuation.toValuation x ≤ 1 ↔ _
  change OrderDual.toDual (M.valuation x) ≤
    OrderDual.toDual (0 : WithTop ℚ) ↔ _
  exact OrderDual.toDual_le_toDual

/-- Positive-valued elements are exactly the maximal ideal of the Puiseux ring. -/
theorem puiseux_mem_maximalIdeal_iff_positive
    (M : PuiseuxValuationModel (k := k) (K := K))
    (x : puiseuxValuationRing M) :
    x ∈ puiseuxMaximalIdeal M ↔
      (0 : WithTop ℚ) < M.valuation (x : K) := by
  change x ∈ IsLocalRing.maximalIdeal (puiseuxValuationRing M) ↔ _
  rw [ValuationSubring.valuation_lt_one_iff]
  calc
    (puiseuxValuationRing M).valuation (x : K) < 1 ↔
        M.valuation.toValuation (x : K) < 1 :=
      (Valuation.isEquiv_valuation_valuationSubring
        M.valuation.toValuation).lt_one_iff_lt_one.symm
    _ ↔ (0 : WithTop ℚ) < M.valuation (x : K) := by
      change OrderDual.toDual (M.valuation (x : K)) <
        OrderDual.toDual (0 : WithTop ℚ) ↔ _
      exact OrderDual.toDual_lt_toDual

/-- Given a positive value, a smaller positive rational value is realized by an
element of the tower. -/
theorem puiseux_exists_strictly_smaller_positive_element
    (M : PuiseuxValuationModel (k := k) (K := K))
    {a : puiseuxValuationRing M}
    (ha : (0 : WithTop ℚ) < M.valuation (a : K)) :
    ∃ b : puiseuxValuationRing M,
      (0 : WithTop ℚ) < M.valuation (b : K) ∧
        M.valuation (b : K) < M.valuation (a : K) := by
  by_cases htop : M.valuation (a : K) = ⊤
  · obtain ⟨n, hn, f, hf, hq⟩ := puiseuxStageExponent_surjective (k := k) 1
    have hval : M.valuation (M.stage n hn f) = (1 : WithTop ℚ) := by
      rw [M.stage_valuation n hn f hf]
      simpa using hq
    have hmem : M.stage n hn f ∈ puiseuxValuationRing M :=
      (puiseux_mem_valuationRing_iff (M := M) _).2 (by
        rw [hval]
        norm_num)
    refine ⟨⟨M.stage n hn f, hmem⟩, ?_, ?_⟩
    · rw [hval]
      norm_num
    · rw [hval, htop]
      exact WithTop.coe_lt_top (1 : ℚ)
  · obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp htop
    have hqpos : 0 < q := by
      apply WithTop.coe_lt_coe.mp
      simpa [hq] using ha
    obtain ⟨r, hr, hrq⟩ := exists_smaller_positive_rational hqpos
    obtain ⟨n, hn, f, hf, hrf⟩ := puiseuxStageExponent_surjective (k := k) r
    have hval : M.valuation (M.stage n hn f) = (r : WithTop ℚ) := by
      rw [M.stage_valuation n hn f hf]
      simpa using hrf
    have hmem : M.stage n hn f ∈ puiseuxValuationRing M :=
      (puiseux_mem_valuationRing_iff (M := M) _).2 (by
        rw [hval]
        exact WithTop.coe_nonneg.mpr (le_of_lt hr))
    refine ⟨⟨M.stage n hn f, hmem⟩, ?_, ?_⟩
    · rw [hval]
      exact WithTop.coe_pos.mpr hr
    · rw [hval, ← hq]
      exact WithTop.coe_lt_coe.mpr hrq

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
        b ∉ Ideal.span ({a} : Set (puiseuxValuationRing M)) := by
  obtain ⟨b, hbpos, hba⟩ := puiseux_exists_strictly_smaller_positive_element M ha
  have hvle : (puiseuxValuationRing M).valuation (a : K) ≤
      (puiseuxValuationRing M).valuation (b : K) := by
    have hmul : M.valuation.toValuation (a : K) ≤
        M.valuation.toValuation (b : K) := by
      change Multiplicative.ofAdd (OrderDual.toDual (M.valuation (a : K))) ≤
        Multiplicative.ofAdd (OrderDual.toDual (M.valuation (b : K)))
      simpa only [Multiplicative.ofAdd_le, OrderDual.toDual_le_toDual] using hba.le
    exact (Valuation.isEquiv_valuation_valuationSubring
      M.valuation.toValuation).le_iff_le.mp hmul
  obtain ⟨c, hc⟩ := (puiseuxValuationRing M).valuation_le_iff (a : K) (b : K) |>.1 hvle
  have hamem : a ∈ Ideal.span ({b} : Set (puiseuxValuationRing M)) := by
    apply Ideal.mem_span_singleton'.2
    refine ⟨c, ?_⟩
    apply Subtype.ext
    exact hc
  refine ⟨b, hbpos, hba, hamem, ?_⟩
  intro hbmem
  obtain ⟨c, hcb⟩ := Ideal.mem_span_singleton'.1 hbmem
  have hcpos : (0 : WithTop ℚ) ≤ M.valuation (c : K) :=
    (puiseux_mem_valuationRing_iff (M := M) _).1 c.property
  have hval : M.valuation (b : K) =
      M.valuation (c : K) + M.valuation (a : K) := by
    have hcb' : (c : K) * (a : K) = (b : K) := congrArg Subtype.val hcb
    calc
      M.valuation (b : K) = M.valuation ((c : K) * (a : K)) := by rw [hcb']
      _ = M.valuation (c : K) + M.valuation (a : K) := M.valuation.map_mul _ _
  have havb : M.valuation (a : K) ≤ M.valuation (b : K) := by
    calc
      M.valuation (a : K) = 0 + M.valuation (a : K) := by simp
      _ ≤ M.valuation (c : K) + M.valuation (a : K) :=
        add_le_add_left hcpos (M.valuation (a : K))
      _ = M.valuation (b : K) := hval.symm
  exact (not_lt_of_ge havb) hba

/-- The positive maximal ideal is not generated by one element. -/
theorem puiseux_maximalIdeal_not_principal
    (M : PuiseuxValuationModel (k := k) (K := K)) :
    ¬∃ π : puiseuxValuationRing M,
      puiseuxMaximalIdeal M = Ideal.span ({π} : Set (puiseuxValuationRing M)) := by
  rintro ⟨π, hπ⟩
  have hπmem : π ∈ puiseuxMaximalIdeal M := by
    rw [hπ]
    exact Ideal.mem_span_singleton_self π
  have hπpos : (0 : WithTop ℚ) < M.valuation (π : K) :=
    (puiseux_mem_maximalIdeal_iff_positive M π).1 hπmem
  obtain ⟨b, hbpos, _, _, hbnot⟩ :=
    puiseux_strict_divisibility_in_maximalIdeal M hπpos
  have hbmem : b ∈ puiseuxMaximalIdeal M :=
    (puiseux_mem_maximalIdeal_iff_positive M b).2 hbpos
  exact hbnot (hπ ▸ hbmem)

/-- The Puiseux valuation ring is nevertheless a valuation ring. -/
theorem puiseux_valuationRing_is_valuationRing
    (M : PuiseuxValuationModel (k := k) (K := K)) :
    ValuationRing (puiseuxValuationRing M) := by
  exact inferInstance

/-- The Puiseux valuation ring is not a discrete valuation ring. -/
theorem puiseux_valuationRing_not_discrete_valuation_ring
    (M : PuiseuxValuationModel (k := k) (K := K)) :
    ¬IsDiscreteValuationRing (puiseuxValuationRing M) := by
  intro hD
  letI : IsDiscreteValuationRing (puiseuxValuationRing M) := hD
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible
    (puiseuxValuationRing M)
  apply puiseux_maximalIdeal_not_principal M
  exact ⟨π, hπ.maximalIdeal_eq⟩

/-- The same strict chain prevents the Puiseux valuation ring from being
Noetherian. -/
theorem puiseux_valuationRing_not_noetherian
    (M : PuiseuxValuationModel (k := k) (K := K)) :
    ¬IsNoetherianRing (puiseuxValuationRing M) := by
  intro hN
  letI : IsNoetherianRing (puiseuxValuationRing M) := hN
  letI : IsPrincipalIdealRing (puiseuxValuationRing M) :=
    ((IsBezout.TFAE (R := puiseuxValuationRing M)).out 0 1).mp hN
  obtain ⟨π, hπ⟩ := IsPrincipalIdealRing.principal (puiseuxMaximalIdeal M)
  exact puiseux_maximalIdeal_not_principal M ⟨π, hπ⟩

/-- Rank one and discreteness are different properties: the Puiseux value group
is Archimedean but has no least positive value. -/
theorem puiseux_rank_one_but_not_discrete :
    IsChapterRankOneOrderedGroup ℚ ∧
      ¬IsChapterDiscreteOrderedGroup ℚ := by
  exact ⟨rational_value_group_is_rank_one,
    rational_value_group_has_no_least_positive⟩

end PuiseuxValuation

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter01
