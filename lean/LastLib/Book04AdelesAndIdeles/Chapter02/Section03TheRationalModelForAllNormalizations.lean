import LastLib.Book04AdelesAndIdeles.Chapter02.Core
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.NumberTheory.Ostrowski
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.RingTheory.Ideal.Int

namespace LastLib.Book04AdelesAndIdeles.Chapter02

noncomputable section

open NumberField
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
  letI : Fact p.1.Prime := ⟨p.2⟩
  by_cases ha : a = 0
  · simp [Chapter02RationalPadicValue, Chapter02RationalPadicAbsoluteValue,
      Chapter02RationalPAdicExponent, ha]
  · have h_toAdd :
        (WithZero.unzero ((Rat.padicValuation p.1).ne_zero_iff.mpr ha)).toAdd =
          -padicValRat p.1 a := by
      rw [WithZero.toAdd_unzero_eq_iff]
      simp [Rat.padicValuation, ha, WithZero.exp_eq_coe_ofAdd]
    have h_exp : Chapter02RationalPAdicExponent p a = padicValRat p.1 a := by
      simp [Chapter02RationalPAdicExponent, h_toAdd, ha]
    change (padicNorm p.1 a : ℝ) = _
    rw [padicNorm.eq_zpow_of_nonzero ha]
    simp [h_exp, ha]

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
  classical
  let N : ℕ := a.num.natAbs
  let D : ℕ := a.den
  let M : ℕ := N * D + 1
  have hN : N ≠ 0 := by
    dsimp [N]
    exact Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.2 ha)
  have hD : D ≠ 0 := by
    dsimp [D]
    exact a.den_ne_zero
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  have hDpos : 0 < D := Nat.pos_of_ne_zero hD
  have hM_N : N < M :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_right N hDpos) (Nat.lt_succ_self _)
  have hM_D : D < M :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_left D hNpos) (Nat.lt_succ_self _)
  have hval (p : Chapter02RationalPrime) :
      padicValRat p.1 a =
        (padicValNat p.1 N : ℤ) - padicValNat p.1 D := by
    simp [N, D, padicValRat, padicValInt]
  have hnorm (p : Chapter02RationalPrime) :
      Chapter02RationalPadicValue p a =
        (p.1 : ℝ) ^ (-(padicValNat p.1 N : ℤ) + padicValNat p.1 D) := by
    letI : Fact p.1.Prime := ⟨p.2⟩
    change (padicNorm p.1 a : ℝ) = _
    rw [padicNorm.eq_zpow_of_nonzero ha, hval, Rat.cast_zpow, Rat.cast_natCast]
    congr 1
    ring
  have hsupp (p : Chapter02RationalPrime)
      (hp : Chapter02RationalPadicValue p a ≠ 1) : p.1 < M := by
    by_contra hpm
    have hMle : M ≤ p.1 := Nat.le_of_not_gt hpm
    have hpND : ¬p.1 ∣ N * D := by
      intro hdiv
      have hle : p.1 ≤ N * D :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero (mul_ne_zero hN hD)) hdiv
      change N * D + 1 ≤ p.1 at hMle
      omega
    have hpN : ¬p.1 ∣ N := by
      intro hdiv
      apply hpND
      exact dvd_mul_of_dvd_left hdiv _
    have hpD : ¬p.1 ∣ D := by
      intro hdiv
      apply hpND
      exact dvd_mul_of_dvd_right hdiv _
    have hpnumZ : ¬(p.1 : ℤ) ∣ a.num := by
      rw [Int.natCast_dvd]
      exact hpN
    have hval0 : padicValRat p.1 a = 0 := by
      rw [padicValRat_def, padicValInt.eq_zero_of_not_dvd hpnumZ,
        padicValNat.eq_zero_of_not_dvd hpD]
      norm_num
    apply hp
    change (padicNorm p.1 a : ℝ) = 1
    rw [padicNorm.eq_zpow_of_nonzero ha, hval0]
    norm_num
  have hprod :
      (∏ᶠ p : Chapter02RationalPrime, Chapter02RationalPadicValue p a) =
        ∏ p ∈ (Finset.range M).subtype Nat.Prime,
          Chapter02RationalPadicValue p a := by
    apply finprod_eq_prod_of_mulSupport_subset
    intro p hp
    have hp' : Chapter02RationalPadicValue p a ≠ 1 := by
      simpa [Function.mulSupport] using hp
    exact Finset.mem_subtype.mpr (Finset.mem_range.mpr (hsupp p hp'))
  have hNprod :
      ∏ p ∈ (Finset.range M).subtype Nat.Prime,
          (p.1 : ℝ) ^ (padicValNat p.1 N : ℤ) = (N : ℝ) := by
    change ∏ p ∈ (Finset.range M).subtype Nat.Prime,
      (fun n : ℕ => (n : ℝ) ^ (padicValNat n N : ℤ)) p.1 = (N : ℝ)
    have hfilter := Finset.prod_subtype_eq_prod_filter
      (s := Finset.range M) (p := Nat.Prime)
      (fun n : ℕ => (n : ℝ) ^ (padicValNat n N : ℤ))
    rw [hfilter]
    simp_rw [zpow_natCast]
    norm_cast
    exact Nat.prod_pow_prime_padicValNat N hN M hM_N
  have hDprod :
      ∏ p ∈ (Finset.range M).subtype Nat.Prime,
          (p.1 : ℝ) ^ (padicValNat p.1 D : ℤ) = (D : ℝ) := by
    change ∏ p ∈ (Finset.range M).subtype Nat.Prime,
      (fun n : ℕ => (n : ℝ) ^ (padicValNat n D : ℤ)) p.1 = (D : ℝ)
    have hfilter := Finset.prod_subtype_eq_prod_filter
      (s := Finset.range M) (p := Nat.Prime)
      (fun n : ℕ => (n : ℝ) ^ (padicValNat n D : ℤ))
    rw [hfilter]
    simp_rw [zpow_natCast]
    norm_cast
    exact Nat.prod_pow_prime_padicValNat D hD M hM_D
  have hneg :
      (∏ p ∈ (Finset.range M).subtype Nat.Prime,
          (p.1 : ℝ) ^ (-(padicValNat p.1 N : ℤ))) =
        (∏ p ∈ (Finset.range M).subtype Nat.Prime,
          (p.1 : ℝ) ^ (padicValNat p.1 N : ℤ))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    rw [zpow_neg]
  have hfinite :
      (∏ p ∈ (Finset.range M).subtype Nat.Prime,
          Chapter02RationalPadicValue p a) =
        (N : ℝ)⁻¹ * (D : ℝ) := by
    calc
      _ = ∏ p ∈ (Finset.range M).subtype Nat.Prime,
          (p.1 : ℝ) ^ (-(padicValNat p.1 N : ℤ) + padicValNat p.1 D) := by
        apply Finset.prod_congr rfl
        intro p hp
        exact hnorm p
      _ = (∏ p ∈ (Finset.range M).subtype Nat.Prime,
          (p.1 : ℝ) ^ (-(padicValNat p.1 N : ℤ))) *
          (∏ p ∈ (Finset.range M).subtype Nat.Prime,
            (p.1 : ℝ) ^ (padicValNat p.1 D : ℤ)) := by
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro p hp
        rw [zpow_add₀]
        exact_mod_cast p.2.ne_zero
      _ = (N : ℝ)⁻¹ * (D : ℝ) := by
        rw [hneg, hNprod, hDprod]
  have hreal :
      Chapter02RationalRealValue a = (N : ℝ) / (D : ℝ) := by
    rw [chapter02_rational_real_value_formula]
    rw [Rat.cast_def, Rat.num_abs_eq_abs_num, Rat.den_abs_eq_den]
    simp [N, D]
  unfold Chapter02RationalGlobalProduct
  rw [hprod, hfinite, hreal]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD
  field_simp

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
  rcases v with w | w
  · let P : IsDedekindDomain.HeightOneSpectrum (𝓞 K) := w.maximalIdeal
    let p0 : Ideal ℤ := P.asIdeal.under ℤ
    have hp0 : p0.IsPrime := by
      dsimp [p0]
      infer_instance
    have hp0bot : p0 ≠ ⊥ := by
      dsimp [p0]
      exact Ideal.under_ne_bot ℤ P.ne_bot
    have hp0' : Prime p0 := Ideal.prime_of_isPrime hp0bot hp0
    have hp : p0.absNorm.Prime := (Int.prime_absNorm p0).2 hp0'
    let p : Chapter02RationalPrime := ⟨p0.absNorm, hp⟩
    have hPover : P.asIdeal.LiesOver (Ideal.span {(p.1 : ℤ)}) := by
      simpa [p, p0] using (Int.liesOver_span_absNorm P.asIdeal)
    letI : P.asIdeal.LiesOver (Ideal.span {(p.1 : ℤ)}) := hPover
    let V : IsDedekindDomain.HeightOneSpectrum ℤ := .ofPrime hp0'
    have hV : V.asIdeal = p0 := by
      simp [V]
    have hp0span : Ideal.span {(p.1 : ℤ)} = p0 := by
      simpa [p] using (Int.ideal_span_absNorm_eq_self p0)
    have hVP : P.asIdeal.LiesOver V.asIdeal := by
      rw [hV]
      rw [← hp0span]
      exact hPover
    letI : P.asIdeal.LiesOver V.asIdeal := hVP
    letI : Fact p.1.Prime := ⟨p.2⟩
    have hVint {z : ℤ} (hz : z ≠ 0) :
        V.intValuation z = WithZero.exp (-(padicValInt p.1 z : ℤ)) := by
      rw [V.intValuation_if_neg hz]
      rw [hV]
      have hcount : (Associates.mk p0).count
          (Associates.mk (Ideal.span {z} : Ideal ℤ)).factors =
          padicValNat p.1 z.natAbs := by
        rw [← hp0span]
        let n : ℕ := padicValNat p.1 z.natAbs
        have hle : (p.1 : ℤ) ^ n ∣ z := by
          rw [← Nat.cast_pow, Int.natCast_dvd]
          exact (Nat.pow_dvd_iff_le_padicValNat p.2.ne_one
            (Int.natAbs_ne_zero.mpr hz)).2 (le_rfl)
        have hlt : ¬(p.1 : ℤ) ^ (n + 1) ∣ z := by
          intro hdiv
          rw [← Nat.cast_pow, Int.natCast_dvd] at hdiv
          have hle' := (Nat.pow_dvd_iff_le_padicValNat p.2.ne_one
            (Int.natAbs_ne_zero.mpr hz)).1 hdiv
          exact (Nat.not_succ_le_self n) (by simpa [n] using hle')
        have hpz : Prime (p.1 : ℤ) := Nat.prime_iff_prime_int.mp p.2
        simpa [n] using
          (Ideal.count_associates_eq' (R := ℤ) (x := (p.1 : ℤ)) (a := z)
            hpz hle hlt)
      rw [hcount]
      simp [padicValInt]
    have hVval : ∀ a : ℚ, V.valuation ℚ a = Rat.padicValuation p.1 a := by
      intro a
      obtain ⟨r, s, h⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors ℤ) a
      rw [← h, IsDedekindDomain.HeightOneSpectrum.valuation_of_mk']
      by_cases hr : r = 0
      · simp [hr]
      · have hs : (s : ℤ) ≠ 0 := nonZeroDivisors.ne_zero s.property
        rw [hVint hr, hVint hs]
        simp [Rat.padicValuation, padicValRat, padicValInt, hr]
    have hram : V.asIdeal.ramificationIdx' P.asIdeal =
        P.asIdeal.ramificationIdx ℤ := by
      apply Ideal.ramificationIdx'_eq_ramificationIdx
      exact V.ne_bot
    have hval : ∀ a : ℚ, V.valuation ℚ a ^ P.asIdeal.ramificationIdx ℤ =
        P.valuation K (algebraMap ℚ K a) := by
      intro a
      rw [← hram]
      exact IsDedekindDomain.HeightOneSpectrum.valuation_liesOver
        (L := K) (v := V) (w := P) a
    let d : ℕ := P.asIdeal.ramificationIdx ℤ * P.asIdeal.inertiaDeg ℤ
    refine ⟨.finite p, d, ?_⟩
    intro a
    change w (algebraMap ℚ K a) = (padicNorm p.1 a : ℝ) ^ d
    have hwval : w (algebraMap ℚ K a) =
        (WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero P)
          (P.valuation K (algebraMap ℚ K a)) : ℝ) := by
      calc
        w (algebraMap ℚ K a) =
            ‖NumberField.FinitePlace.embedding P (algebraMap ℚ K a)‖ := by
              simpa [P] using
                (NumberField.FinitePlace.norm_embedding_eq w
                  (algebraMap ℚ K a)).symm
        _ = _ := NumberField.FinitePlace.norm_embedding' (v := P)
          (algebraMap ℚ K a)
    have hnorm : p.1 ^ P.asIdeal.inertiaDeg ℤ = P.asIdeal.absNorm :=
      Ideal.pow_inertiaDeg p.1 P.asIdeal
    rw [hwval, ← hval a]
    simp only [map_pow]
    simp only [← hnorm, hVval a]
    have he : P.asIdeal.ramificationIdx ℤ ≠ 0 :=
      (P.asIdeal.ramificationIdx_pos ℤ).ne'
    have hf : P.asIdeal.inertiaDeg ℤ ≠ 0 :=
      (P.asIdeal.inertiaDeg_pos ℤ).ne'
    have hd : d ≠ 0 := by
      simp [d, he, hf]
    by_cases ha : a = 0
    · simp [ha, he, hd]
    · have hpa : Rat.padicValuation p.1 a ≠ 0 :=
        (Rat.padicValuation p.1).ne_zero_iff.mpr ha
      rw [WithZeroMulInt.toNNReal_neg_apply _ hpa]
      have htoAdd : (WithZero.unzero hpa).toAdd = -padicValRat p.1 a := by
        rw [WithZero.toAdd_unzero_eq_iff]
        simp [Rat.padicValuation, ha, WithZero.exp_eq_coe_ofAdd]
      rw [htoAdd]
      rw [padicNorm.eq_zpow_of_nonzero ha, Rat.cast_zpow, Rat.cast_natCast]
      simp only [NNReal.coe_pow, NNReal.coe_zpow, NNReal.coe_natCast]
      simp only [Nat.cast_pow]
      norm_cast
      push_cast
      change (((p.1 : ℝ) ^ P.asIdeal.inertiaDeg ℤ) ^
          (-padicValRat p.1 a)) ^ P.asIdeal.ramificationIdx ℤ =
        ((p.1 : ℝ) ^ (-padicValRat p.1 a)) ^ d
      rw [← zpow_natCast, ← zpow_mul]
      rw [← zpow_natCast, ← zpow_mul]
      rw [← zpow_natCast, ← zpow_mul]
      congr 1
      simp [d]
      ring
  · refine ⟨.real, w.mult, ?_⟩
    intro a
    change w (algebraMap ℚ K a) ^ w.mult =
      Chapter02RationalRealValue a ^ w.mult
    rw [show algebraMap ℚ K a = (a : K) by rfl, w.map_ratCast]
    rw [← Rat.norm_cast_real, Real.norm_eq_abs]
    rw [chapter02_rational_real_value_formula]
    rw [Rat.cast_abs]

theorem chapter02_restriction_weight_is_positive
    {K : Type*} [Field K] [NumberField K]
    (v : Chapter02Place K) (u : Chapter02RationalNormalizedPlace) (d : ℕ)
    (h : Chapter02RestrictionHasDegreeExponent v u d) :
    0 < d := by
  have hd : d ≠ 0 := by
    intro hd
    rcases v with w | w
    · let P : IsDedekindDomain.HeightOneSpectrum (𝓞 K) := w.maximalIdeal
      let n : ℕ := (P.asIdeal.under ℤ).absNorm
      have hnmem : (n : 𝓞 K) ∈ P.asIdeal := by
        dsimp [n]
        exact Int.absNorm_under_mem P.asIdeal
      have hltP :
          ‖NumberField.FinitePlace.embedding P (n : K)‖ < 1 :=
        (NumberField.FinitePlace.norm_lt_one_iff_mem K P (n : 𝓞 K)).2 hnmem
      have hlt : w (algebraMap ℚ K (n : ℚ)) < 1 := by
        calc
          w (algebraMap ℚ K (n : ℚ)) = w (n : K) := by simp
          _ = ‖NumberField.FinitePlace.embedding P (n : K)‖ := by
            simpa [P] using
              (NumberField.FinitePlace.norm_embedding_eq w (n : K)).symm
          _ < 1 := hltP
      have heq : w (algebraMap ℚ K (n : ℚ)) = 1 := by
        simpa [Chapter02RestrictionHasDegreeExponent, Chapter02PlaceValue, hd] using
          h (n : ℚ)
      exact (ne_of_lt hlt) heq
    · have hlt :
          1 < Chapter02PlaceValue (Sum.inr w : Chapter02Place K)
            (algebraMap ℚ K (2 : ℚ)) := by
        change 1 < w (algebraMap ℚ K (2 : ℚ)) ^ w.mult
        rw [show algebraMap ℚ K (2 : ℚ) = (2 : K) by norm_num]
        have hw2 : w (2 : K) = 2 := w.map_natCast 2
        rw [hw2]
        exact one_lt_pow₀ (by norm_num) NumberField.InfinitePlace.mult_ne_zero
      have heq :
          Chapter02PlaceValue (Sum.inr w : Chapter02Place K)
            (algebraMap ℚ K (2 : ℚ)) = 1 := by
        simpa [Chapter02RestrictionHasDegreeExponent, Chapter02PlaceValue, hd] using
          h (2 : ℚ)
      exact (ne_of_gt hlt) heq
  exact Nat.pos_of_ne_zero hd

end

end LastLib.Book04AdelesAndIdeles.Chapter02
