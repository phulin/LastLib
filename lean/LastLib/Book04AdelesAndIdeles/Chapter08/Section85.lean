import LastLib.Book04AdelesAndIdeles.Chapter08.Section84

namespace LastLib.Book04AdelesAndIdeles.Chapter08

noncomputable section

open scoped BigOperators nonZeroDivisors RestrictedProduct WithZero
open IsDedekindDomain

/-! ## 8.5 What ideals forget -/

def chapter08SameLocalIdealAt {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (Chapter08Integers K))
    (x y : v.adicCompletion K) : Prop :=
  chapter08LocalOrder v x = chapter08LocalOrder v y

def chapter08LocalUnitMultipleAt {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (Chapter08Integers K))
    (x y : v.adicCompletion K) : Prop :=
  ∃ u : (v.adicCompletion K)ˣ, y = (u : v.adicCompletion K) * x

theorem chapter08_local_order_ignores_unit
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (Chapter08Integers K))
    (u : (v.adicCompletion K)ˣ) (x : v.adicCompletion K) :
    chapter08LocalOrder v ((u : v.adicCompletion K) * x) = chapter08LocalOrder v x := by
  sorry

theorem chapter08_local_ideal_eq_iff_unit_multiple
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (Chapter08Integers K))
    {x y : v.adicCompletion K} (hx : x ≠ 0) (hy : y ≠ 0) :
    chapter08SameLocalIdealAt v x y ↔ chapter08LocalUnitMultipleAt v x y := by
  sorry

theorem chapter08_finite_idele_ideal_eq_iff_same_orders
    {K : Type*} [Field K] [NumberField K]
    {x y : Chapter08FiniteIdeles K} :
    chapter08FiniteIdeleIdealMap K x = chapter08FiniteIdeleIdealMap K y ↔
      ∀ v : HeightOneSpectrum (Chapter08Integers K),
        chapter08FiniteIdeleOrder x v = chapter08FiniteIdeleOrder y v := by
  sorry

theorem chapter08_finite_idele_ideal_forgets_local_units
    {K : Type*} [Field K] [NumberField K]
    (x y : Chapter08FiniteIdeles K)
    (h : ∀ v : HeightOneSpectrum (Chapter08Integers K),
      chapter08FiniteIdeleOrder x v = chapter08FiniteIdeleOrder y v) :
    chapter08FiniteIdeleIdealMap K x = chapter08FiniteIdeleIdealMap K y := by
  exact (chapter08_finite_idele_ideal_eq_iff_same_orders).2 h

/-! A small abstract congruence interface records the finite data retained by ray conditions. -/

def chapter08CongruentModulo {R : Type*} [Ring R]
    (I : Ideal R) (m : ℕ) (a b : R) : Prop :=
  a - b ∈ I ^ m

def chapter08RayClassFiniteCongruence (p m a b : ℕ) : Prop :=
  Nat.ModEq (p ^ m) a b

theorem chapter08_one_two_not_congruent_mod_prime_pow
    {p m : ℕ} (hp : Nat.Prime p) (hm : 0 < m) (hp2 : p ≠ 2) :
    ¬ chapter08RayClassFiniteCongruence p m 1 2 := by
  sorry

theorem chapter08_one_two_same_local_ideal_when_two_is_a_unit
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (Chapter08Integers K))
    (h2 : (Valued.v (2 : v.adicCompletion K) : ℤᵐ⁰) = 1) :
    chapter08SameLocalIdealAt v (1 : v.adicCompletion K) (2 : v.adicCompletion K) := by
  sorry

theorem chapter08_unit_pair_has_same_local_ideal
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (Chapter08Integers K))
    (u w : (v.adicCompletion K)ˣ) :
    chapter08SameLocalIdealAt v (u : v.adicCompletion K) (w : v.adicCompletion K) := by
  sorry

/-! Infinite coordinates are absent from the ideal map; signs at real places and arguments at
complex places therefore require separate quotient or character data. -/

theorem chapter08_ordinary_ideal_map_forgets_archimedean_coordinate
    {K : Type*} [Field K] [NumberField K]
    (x y : Chapter08Ideles K) (h : x.2 = y.2) :
    chapter08IdeleIdealHom K x = chapter08IdeleIdealHom K y := by
  exact chapter08_idele_ideal_map_ignores_infinite h

def chapter08ArchimedeanUnitData {K : Type*} [Field K] [NumberField K] :=
  Chapter08InfiniteIdeles K

theorem chapter08_archimedean_unit_data_is_not_recorded_by_finite_ideal_map
    {K : Type*} [Field K] [NumberField K]
    (u : chapter08ArchimedeanUnitData (K := K))
    (x : Chapter08FiniteIdeles K) :
    chapter08IdeleIdealHom K (u, x) = chapter08IdeleIdealHom K (1, x) := by
  apply chapter08_ordinary_ideal_map_forgets_archimedean_coordinate
  rfl

end

end LastLib.Book04AdelesAndIdeles.Chapter08
