import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter01

open scoped Polynomial nonZeroDivisors
open Set Function Ideal
open scoped BigOperators

noncomputable section

/-! # Chapter 1: Measuring vanishing

This file is a statement-generation pass for Chapter 1 of *Valuations, DVRs, and
Completions*.  The declarations below follow Sections 1.1--1.5 in order. -/

/-! # Book 1, Chapter 1, Section 1.1: A Local Question
-/

/-! ## 1.1 The prime-adic model -/

section PrimeAdicModel

/-- The canonical `p`-free presentation of a nonzero rational number.  The
exponent and the reduced numerator/denominator are all normalized. -/
structure PrimeAdicDecomposition (p : ℕ) (x : ℚ) where
  exponent : ℤ
  numerator : ℤ
  denominator : ℤ
  numerator_ne_zero : numerator ≠ 0
  denominator_ne_zero : denominator ≠ 0
  numerator_p_free : ¬(p : ℤ) ∣ numerator
  denominator_p_free : ¬(p : ℤ) ∣ denominator
  numerator_denominator_coprime : IsCoprime numerator denominator
  denominator_pos : 0 < denominator
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
  have hnum : x.num ≠ 0 := Rat.num_ne_zero.mpr hx
  have hden : (x.den : ℤ) ≠ 0 := by exact_mod_cast x.den_nz
  have hpint : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  obtain ⟨m, a, ha, hma⟩ := WfDvdMonoid.max_power_factor hnum hpint.irreducible
  obtain ⟨n, b, hb, hnb⟩ :=
    WfDvdMonoid.max_power_factor hden hpint.irreducible
  have ha0 : a ≠ 0 := by
    intro ha0
    apply hnum
    rw [hma, ha0, mul_zero]
  have hb0 : b ≠ 0 := by
    intro hb0
    apply hden
    rw [hnb, hb0, mul_zero]
  have hadvd : a ∣ x.num := by
    rw [hma]
    exact dvd_mul_left _ _
  have hbdvd : b ∣ (x.den : ℤ) := by
    rw [hnb]
    exact dvd_mul_left _ _
  have hcop : IsCoprime a b :=
    (Rat.isCoprime_num_den x).mono hadvd hbdvd
  have hpnp : 0 < (p : ℤ) ^ n := pow_pos (by exact_mod_cast hp.pos) _
  have hprod : 0 < (p : ℤ) ^ n * b := by
    rw [← hnb]
    exact_mod_cast x.pos
  have hbpos : 0 < b := by
    rcases (mul_pos_iff.mp hprod) with ⟨_, h⟩ | ⟨h, _⟩
    · exact h
    · exact False.elim ((not_lt_of_ge (le_of_lt hpnp)) h)
  let e : ℤ := (m : ℤ) - (n : ℤ)
  refine ⟨⟨e, a, b, ha0, hb0, ha, hb, hcop, hbpos, ?_⟩⟩
  · dsimp [e]
    calc
      x = (x.num : ℚ) / (x.den : ℚ) := Rat.num_div_den x |>.symm
      _ = (((p : ℤ) ^ m * a : ℤ) : ℚ) /
          (((p : ℤ) ^ n * b : ℤ) : ℚ) := by
        rw [hma]
        congr 1
        exact_mod_cast hnb
      _ = (p : ℚ) ^ ((m : ℤ) - (n : ℤ)) * (a : ℚ) / (b : ℚ) := by
        push_cast
        rw [zpow_natCast_sub_natCast₀ (by exact_mod_cast hp.ne_zero) m n]
        field_simp [show (p : ℚ) ≠ 0 by exact_mod_cast hp.ne_zero,
          show (b : ℚ) ≠ 0 by exact_mod_cast hb0]

/-- The exponent in every `p`-free presentation is the `p`-adic order. -/
theorem primeAdicDecomposition_exponent_eq_pAdicOrder {p : ℕ} (hp : p.Prime)
    {x : ℚ} (_hx : x ≠ 0) (d : PrimeAdicDecomposition p x) :
    d.exponent = pAdicOrder p x := by
  let _ : Fact p.Prime := ⟨hp⟩
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

/-- The exponent and the `p`-free rational unit are unique. -/
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

/-- The normalized numerator and denominator are unique as well. -/
theorem primeAdicDecomposition_unique {p : ℕ} (hp : p.Prime)
    {x : ℚ} (hx : x ≠ 0) {d e : PrimeAdicDecomposition p x} :
    d.exponent = e.exponent ∧ d.numerator = e.numerator ∧
      d.denominator = e.denominator := by
  have hunit := primeAdicDecomposition_unique_exponent_and_unit hp hx
    (d := d) (e := e)
  have hcopd : Nat.Coprime d.numerator.natAbs d.denominator.natAbs :=
    (Int.isCoprime_iff_nat_coprime).mp d.numerator_denominator_coprime
  have hcope : Nat.Coprime e.numerator.natAbs e.denominator.natAbs :=
    (Int.isCoprime_iff_nat_coprime).mp e.numerator_denominator_coprime
  have hnumden := Rat.div_int_inj d.denominator_pos e.denominator_pos
    hcopd hcope hunit.2
  exact ⟨hunit.1, hnumden⟩

/-- Multiplication adds `p`-adic orders. -/
theorem pAdicOrder_mul {p : ℕ} (hp : p.Prime) {x y : ℚ}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    pAdicOrder p (x * y) = pAdicOrder p x + pAdicOrder p y := by
  let _ : Fact p.Prime := ⟨hp⟩
  simpa [pAdicOrder] using (padicValRat.mul hx hy)

/-- Inversion negates `p`-adic order. -/
theorem pAdicOrder_inv {p : ℕ} (hp : p.Prime) {x : ℚ} (_hx : x ≠ 0) :
    pAdicOrder p x⁻¹ = -pAdicOrder p x := by
  let _ : Fact p.Prime := ⟨hp⟩
  change padicValRat p x⁻¹ = -padicValRat p x
  exact padicValRat.inv x

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
  let _ : Fact p.Prime := ⟨hp⟩
  have h := padicValRat.min_le_padicValRat_add (p := p) hxy
  simpa [pAdicOrderWithTop, pAdicOrder, hx, hy, hxy] using
    (WithTop.coe_le_coe.mpr h)

/-! The total version records the zero cases in the multiplicative valuation
law, rather than requiring separate nonzero hypotheses. -/
theorem pAdicOrderWithTop_mul {p : ℕ} (hp : p.Prime) (x y : ℚ) :
    pAdicOrderWithTop p (x * y) =
      pAdicOrderWithTop p x + pAdicOrderWithTop p y := by
  by_cases hx : x = 0
  · subst x
    simp [pAdicOrderWithTop]
  by_cases hy : y = 0
  · subst y
    simp [pAdicOrderWithTop]
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  simpa [pAdicOrderWithTop, hx, hy, hxy] using
    congrArg (fun z : ℤ => (z : WithTop ℤ)) (pAdicOrder_mul hp hx hy)

/-- The ordinary integer form of the triangle inequality when the sum is
nonzero. -/
theorem pAdicOrder_add {p : ℕ} (hp : p.Prime) {x y : ℚ}
    (hxy : x + y ≠ 0) :
    min (pAdicOrder p x) (pAdicOrder p y) ≤ pAdicOrder p (x + y) := by
  let _ : Fact p.Prime := ⟨hp⟩
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
  let _ : Fact p.Prime := ⟨hp⟩
  simpa [pAdicOrder] using (padicValRat.add_eq_min hxy hx hy hne)

/-- The `p`-adic order of `p` itself is one. -/
theorem pAdicOrder_self {p : ℕ} (hp : p.Prime) :
    pAdicOrder p (p : ℚ) = 1 := by
  let _ : Fact p.Prime := ⟨hp⟩
  change padicValRat p (p : ℚ) = 1
  exact padicValRat.self hp.one_lt

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
  let _ : Fact p.Prime := ⟨hp⟩
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
