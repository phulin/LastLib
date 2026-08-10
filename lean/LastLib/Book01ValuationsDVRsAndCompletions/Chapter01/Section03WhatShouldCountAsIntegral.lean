import LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.Section02OrderOfVanishingOnALine

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter01

open scoped Polynomial RatFunc nonZeroDivisors
open Set Function Ideal
open scoped BigOperators

noncomputable section

/-! # Chapter 1: Measuring vanishing

This file is a statement-generation pass for Chapter 1 of *Valuations, DVRs, and
Completions*.  The declarations below follow Sections 1.1--1.5 in order. -/

/-! # Book 1, Chapter 1, Section 1.3: What Should Count as Integral
-/

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

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter01
