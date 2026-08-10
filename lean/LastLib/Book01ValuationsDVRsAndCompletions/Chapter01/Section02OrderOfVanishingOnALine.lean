import LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.Section01ALocalQuestion
import Mathlib.Tactic.NormNum.Prime

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter01

open scoped Polynomial RatFunc nonZeroDivisors
open Set Function Ideal
open scoped BigOperators

noncomputable section

/-! # Chapter 1: Measuring vanishing

This file is a statement-generation pass for Chapter 1 of *Valuations, DVRs, and
Completions*.  The declarations below follow Sections 1.1--1.5 in order. -/

/-! # Book 1, Chapter 1, Section 1.2: Order of Vanishing on a Line
-/

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

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter01
