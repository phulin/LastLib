import LastLib.Book04AdelesAndIdeles.Chapter02.Core
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

namespace LastLib.Book04AdelesAndIdeles.Chapter02

noncomputable section

open Rat
open scoped BigOperators WithZero

/-! ## 2.3. The rational model for all normalizations -/

/-- The usual real absolute value on `ℚ`. -/
noncomputable def Chapter02RationalRealAbsoluteValue : AbsoluteValue ℚ ℝ :=
  Rat.AbsoluteValue.real

/-- The usual `p`-adic absolute value on `ℚ`, indexed by a bundled prime. -/
noncomputable def Chapter02RationalPadicAbsoluteValue
    (p : Chapter02RationalPrime) : AbsoluteValue ℚ ℝ :=
  letI : Fact p.1.Prime := ⟨p.2⟩
  Rat.AbsoluteValue.padic p.1

def Chapter02RationalRealValue (a : ℚ) : ℝ :=
  Chapter02RationalRealAbsoluteValue a

noncomputable def Chapter02RationalPadicValue
    (p : Chapter02RationalPrime) (a : ℚ) : ℝ :=
  Chapter02RationalPadicAbsoluteValue p a

/-- The chosen normalized rational places. -/
inductive Chapter02RationalNormalizedPlace
  | real
  | finite (p : Chapter02RationalPrime)

noncomputable def Chapter02RationalNormalizedValue :
    Chapter02RationalNormalizedPlace → ℚ → ℝ
  | .real => Chapter02RationalRealValue
  | .finite p => Chapter02RationalPadicValue p

def Chapter02RationalGlobalProduct (a : ℚ) : ℝ :=
  Chapter02RationalRealValue a *
    ∏ᶠ p : Chapter02RationalPrime, Chapter02RationalPadicValue p a

noncomputable def Chapter02RationalPAdicExponent
    (p : Chapter02RationalPrime) (a : ℚ) : ℤ :=
  letI : Fact p.1.Prime := ⟨p.2⟩
  if ha : a = 0 then 0 else
    -((WithZero.unzero ((Rat.padicValuation p.1).ne_zero_iff.mpr ha)).toAdd)

theorem chapter02_rational_real_value_formula (a : ℚ) :
    Chapter02RationalRealValue a = |a| := by
  simp [Chapter02RationalRealValue, Chapter02RationalRealAbsoluteValue,
    Rat.AbsoluteValue.real_eq_abs]

theorem chapter02_rational_padic_value_formula
    (p : Chapter02RationalPrime) (a : ℚ) :
    Chapter02RationalPadicValue p a =
      if ha : a = 0 then 0 else
        (p.1 : ℝ) ^ (-Chapter02RationalPAdicExponent p a) := by
  sorry

/-- Ostrowski's theorem in the book's absolute-value language. -/
theorem chapter02_rational_absolute_value_classification
    (v : AbsoluteValue ℚ ℝ) (hv : v.IsNontrivial) :
    v.IsEquiv Rat.AbsoluteValue.real ∨
      ∃! p : ℕ, ∃ (_ : Fact p.Prime),
        v.IsEquiv (Rat.AbsoluteValue.padic p) := by
  exact Rat.AbsoluteValue.equiv_real_or_padic v hv

theorem chapter02_real_and_padic_absolute_values_are_inequivalent
    (p : ℕ) [Fact p.Prime] :
    ¬Rat.AbsoluteValue.real.IsEquiv (Rat.AbsoluteValue.padic p) := by
  exact Rat.AbsoluteValue.not_real_isEquiv_padic p

theorem chapter02_rational_archimedean_absolute_value_is_a_real_power
    (v : AbsoluteValue ℚ ℝ) (_hv : v.IsNontrivial)
    (harch : v.IsEquiv Rat.AbsoluteValue.real) :
    ∃ c : ℝ, 0 < c ∧ (v · ^ c) = Rat.AbsoluteValue.real := by
  exact (AbsoluteValue.isEquiv_iff_exists_rpow_eq).mp harch

theorem chapter02_rational_archimedean_has_a_positive_integer_witness
    (v : AbsoluteValue ℚ ℝ)
    (harch : v.IsEquiv Rat.AbsoluteValue.real) :
    ∃ n : ℕ, 1 < n ∧ 1 < v n := by
  obtain ⟨c, hc, hpow⟩ :=
    (AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp harch)
  refine ⟨2, by norm_num, ?_⟩
  have hpow2 : v (2 : ℚ) ^ c = 2 := by
    simpa [Rat.AbsoluteValue.real_eq_abs] using congrFun hpow 2
  apply (Real.rpow_lt_rpow_iff (x := 1) (y := v (2 : ℚ)) (z := c)
    (by norm_num) (v.nonneg _) hc).mp
  simpa [Real.one_rpow] using
    (show 1 < v (2 : ℚ) ^ c by rw [hpow2]; norm_num)

theorem chapter02_rational_nonarchimedean_integers_are_bounded
    (v : AbsoluteValue ℚ ℝ) (hv : IsNonarchimedean v) (n : ℕ) :
    v n ≤ 1 := by
  exact hv.apply_natCast_le_one

theorem chapter02_rational_nonarchimedean_has_a_small_prime
    (v : AbsoluteValue ℚ ℝ) (hv : v.IsNontrivial)
    (hnonarch : IsNonarchimedean v) :
    ∃ p : Chapter02RationalPrime, v p.1 < 1 := by
  have hbdd : ∀ n : ℕ, v n ≤ 1 := fun n => hnonarch.apply_natCast_le_one
  obtain ⟨q, hq, hmin⟩ :=
    Rat.AbsoluteValue.exists_minimal_nat_zero_lt_and_lt_one hv hbdd
  have hqprime :=
    Rat.AbsoluteValue.is_prime_of_minimal_nat_zero_lt_and_lt_one hq.1 hq.2 hmin
  exact ⟨⟨q, hqprime⟩, hq.2⟩

theorem chapter02_rational_nonarchimedean_two_distinct_primes_cannot_both_be_small
    (v : AbsoluteValue ℚ ℝ) (hnonarch : IsNonarchimedean v)
    (p q : Chapter02RationalPrime) (hpq : p.1 ≠ q.1) :
    ¬(v p.1 < 1 ∧ v q.1 < 1) := by
  rintro ⟨hp, hq⟩
  obtain ⟨a, b, hbez⟩ : IsCoprime (p.1 : ℤ) (q.1 : ℤ) :=
    (Nat.coprime_primes p.2 q.2).mpr hpq |>.isCoprime
  have hsum := hnonarch ((a : ℚ) * p.1) ((b : ℚ) * q.1)
  have hbezq : (a : ℚ) * p.1 + (b : ℚ) * q.1 = 1 := by
    exact_mod_cast hbez
  rw [hbezq, map_one] at hsum
  have hpa : v ((a : ℚ) * p.1) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right
      hnonarch.apply_intCast_le_one (v.nonneg _)) (by simpa using hp)
  have hqb : v ((b : ℚ) * q.1) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right
      hnonarch.apply_intCast_le_one (v.nonneg _)) (by simpa using hq)
  exact (not_le_of_gt (max_lt hpa hqb)) hsum

theorem chapter02_rational_nonarchimedean_coprime_integer_has_value_one
    (v : AbsoluteValue ℚ ℝ) (p : Chapter02RationalPrime)
    (h : v.IsEquiv (Chapter02RationalPadicAbsoluteValue p))
    (m : ℕ) (hm : Nat.Coprime m p.1) :
    v m = 1 := by
  obtain ⟨c, hc, hpow⟩ :=
    (AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp h)
  have hpm : ¬p.1 ∣ m := (p.2.coprime_iff_not_dvd).mp hm.symm
  have hpadic : Chapter02RationalPadicAbsoluteValue p m = 1 := by
    change (padicNorm p.1 (m : ℚ) : ℝ) = 1
    rw [(@padicNorm.nat_eq_one_iff p.1 ⟨p.2⟩ m).2 hpm]
    norm_num
  have hmval : v (m : ℚ) ^ c = 1 := by
    rw [congrFun hpow m, hpadic]
  apply (Real.rpow_left_inj (x := v (m : ℚ)) (y := 1) (z := c)
    (v.nonneg _) (by norm_num) hc.ne').mp
  simpa using hmval

theorem chapter02_rational_nonarchimedean_prime_isolation
    (v : AbsoluteValue ℚ ℝ) (p : Chapter02RationalPrime)
    (h : v.IsEquiv (Chapter02RationalPadicAbsoluteValue p))
    (q : Chapter02RationalPrime) (hpq : q.1 ≠ p.1) :
    v q.1 = 1 := by
  exact chapter02_rational_nonarchimedean_coprime_integer_has_value_one v p h q.1
    ((Nat.coprime_primes q.2 p.2).mpr hpq)

theorem chapter02_rational_nonarchimedean_absolute_value_is_a_padic_power
    (v : AbsoluteValue ℚ ℝ) (hv : v.IsNontrivial)
    (hnonarch : IsNonarchimedean v) :
    ∃ p : Chapter02RationalPrime, ∃ c : ℝ, 0 < c ∧
      (v · ^ c) = Chapter02RationalPadicAbsoluteValue p := by
  have hbdd : ∀ n : ℕ, v n ≤ 1 := fun n => hnonarch.apply_natCast_le_one
  obtain ⟨q, ⟨hq, hqv⟩, _⟩ :=
    Rat.AbsoluteValue.equiv_padic_of_bounded hv hbdd
  obtain ⟨c, hc, hpow⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp hqv
  refine ⟨⟨q, hq.out⟩, c, hc, ?_⟩
  simpa [Chapter02RationalPadicAbsoluteValue] using hpow

/-- The rational product formula for the selected representatives. -/
theorem chapter02_rational_product_formula
    {a : ℚ} (ha : a ≠ 0) :
    Chapter02RationalGlobalProduct a = 1 := by
  sorry

theorem chapter02_rational_padic_factors_have_finite_support
    {a : ℚ} (ha : a ≠ 0) :
    (fun p : Chapter02RationalPrime =>
      Chapter02RationalPadicValue p a).HasFiniteMulSupport := by
  classical
  let N : ℕ := a.num.natAbs * a.den
  have hN : N ≠ 0 := by
    dsimp [N]
    exact mul_ne_zero (Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.2 ha)) a.den_ne_zero
  let S : Set Chapter02RationalPrime := {p | p.1 ∈ N.primeFactors}
  have hS : S.Finite := by
    apply Set.Finite.of_finite_image (f := fun p : Chapter02RationalPrime => p.1)
    · apply N.primeFactors.finite_toSet.subset
      intro n hn
      rcases hn with ⟨p, hp, rfl⟩
      simpa [S] using hp
    · exact Subtype.val_injective.injOn
  refine hS.subset ?_
  intro p hp
  change Chapter02RationalPadicValue p a ≠ 1 at hp
  change p.1 ∈ N.primeFactors
  by_contra hpNmem
  apply hp
  change (padicNorm p.1 a : ℝ) = 1
  have hpN : ¬p.1 ∣ N := by
    intro hdiv
    apply hpNmem
    exact Nat.mem_primeFactors_of_ne_zero hN |>.2 ⟨p.2, hdiv⟩
  have hpnum : ¬p.1 ∣ a.num.natAbs := by
    intro hdiv
    apply hpN
    exact dvd_mul_of_dvd_left hdiv _
  have hpden : ¬p.1 ∣ a.den := by
    intro hdiv
    apply hpN
    exact dvd_mul_of_dvd_right hdiv _
  have hpnumZ : ¬(p.1 : ℤ) ∣ a.num := by
    rw [Int.natCast_dvd]
    exact hpnum
  have hval : padicValRat p.1 a = 0 := by
    rw [padicValRat_def, padicValInt.eq_zero_of_not_dvd hpnumZ,
      padicValNat.eq_zero_of_not_dvd hpden]
    norm_num
  rw [padicNorm.eq_zpow_of_nonzero ha, hval]
  norm_num

/-- Restriction to `ℚ` is allowed to acquire a local-degree exponent. -/
def Chapter02RestrictionHasDegreeExponent
    {K : Type*} [Field K] [NumberField K]
    (v : Chapter02Place K) (u : Chapter02RationalNormalizedPlace) (d : ℕ) : Prop :=
  ∀ a : ℚ,
    Chapter02PlaceValue v (algebraMap ℚ K a) =
      Chapter02RationalNormalizedValue u a ^ d

theorem chapter02_restriction_to_Q_has_local_degree_weight
    {K : Type*} [Field K] [NumberField K]
    (v : Chapter02Place K) :
    ∃ u : Chapter02RationalNormalizedPlace, ∃ d : ℕ,
      Chapter02RestrictionHasDegreeExponent v u d := by
  sorry

theorem chapter02_restriction_weights_are_local_degrees
    {K : Type*} [Field K] [NumberField K]
    (v : Chapter02Place K) (u : Chapter02RationalNormalizedPlace) (d : ℕ)
    (h : Chapter02RestrictionHasDegreeExponent v u d) :
    0 < d := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter02
