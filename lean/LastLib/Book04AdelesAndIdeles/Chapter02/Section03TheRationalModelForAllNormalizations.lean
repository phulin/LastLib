import LastLib.Book04AdelesAndIdeles.Chapter02.Core

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
    (WithZero.unzero ((Rat.padicValuation p.1).ne_zero_iff.mpr ha)).toAdd

theorem chapter02_rational_real_value_formula (a : ℚ) :
    Chapter02RationalRealValue a = |a| := by
  sorry

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
    (v : AbsoluteValue ℚ ℝ) (hv : v.IsNontrivial)
    (harch : v.IsEquiv Rat.AbsoluteValue.real) :
    ∃ n : ℕ, 1 < n ∧ 1 < v n := by
  sorry

theorem chapter02_rational_nonarchimedean_integers_are_bounded
    (v : AbsoluteValue ℚ ℝ) (hv : IsNonarchimedean v) (n : ℕ) :
    v n ≤ 1 := by
  sorry

theorem chapter02_rational_nonarchimedean_has_a_small_prime
    (v : AbsoluteValue ℚ ℝ) (hv : v.IsNontrivial)
    (hnonarch : IsNonarchimedean v) :
    ∃ p : Chapter02RationalPrime, v p.1 < 1 := by
  sorry

theorem chapter02_rational_nonarchimedean_two_distinct_primes_cannot_both_be_small
    (v : AbsoluteValue ℚ ℝ) (hnonarch : IsNonarchimedean v)
    (p q : Chapter02RationalPrime) (hpq : p.1 ≠ q.1) :
    ¬(v p.1 < 1 ∧ v q.1 < 1) := by
  sorry

theorem chapter02_rational_nonarchimedean_coprime_integer_has_value_one
    (v : AbsoluteValue ℚ ℝ) (p : Chapter02RationalPrime)
    (h : v.IsEquiv (Chapter02RationalPadicAbsoluteValue p))
    (m : ℕ) (hm : Nat.Coprime m p.1) :
    v m = 1 := by
  sorry

theorem chapter02_rational_nonarchimedean_prime_isolation
    (v : AbsoluteValue ℚ ℝ) (p : Chapter02RationalPrime)
    (h : v.IsEquiv (Chapter02RationalPadicAbsoluteValue p))
    (q : Chapter02RationalPrime) (hpq : q.1 ≠ p.1) :
    v q.1 = 1 := by
  sorry

theorem chapter02_rational_nonarchimedean_absolute_value_is_a_padic_power
    (v : AbsoluteValue ℚ ℝ) (hv : v.IsNontrivial)
    (hnonarch : IsNonarchimedean v) :
    ∃ p : Chapter02RationalPrime, ∃ c : ℝ, 0 < c ∧
      (v · ^ c) = Chapter02RationalPadicAbsoluteValue p := by
  sorry

/-- The rational product formula for the selected representatives. -/
theorem chapter02_rational_product_formula
    {a : ℚ} (ha : a ≠ 0) :
    Chapter02RationalGlobalProduct a = 1 := by
  sorry

theorem chapter02_rational_padic_factors_have_finite_support
    {a : ℚ} (ha : a ≠ 0) :
    (fun p : Chapter02RationalPrime =>
      Chapter02RationalPadicValue p a).HasFiniteMulSupport := by
  sorry

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
