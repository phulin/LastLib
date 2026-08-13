import LastLib.Book04AdelesAndIdeles.Chapter08.Section82

namespace LastLib.Book04AdelesAndIdeles.Chapter08

noncomputable section

open scoped BigOperators nonZeroDivisors RestrictedProduct WithZero
open IsDedekindDomain

/-! ## 8.5 What ideals forget -/

def chapter08SameLocalIdealAt {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (Chapter08Integers K))
    (x y : v.adicCompletion K) : Prop :=
  x ≠ 0 ∧ y ≠ 0 ∧ chapter08LocalOrder v x = chapter08LocalOrder v y

def chapter08LocalUnitMultipleAt {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (Chapter08Integers K))
    (x y : v.adicCompletion K) : Prop :=
  ∃ u : (v.adicCompletionIntegers K)ˣ,
    y = ((u : v.adicCompletionIntegers K) : v.adicCompletion K) * x

theorem chapter08_local_order_ignores_unit
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (Chapter08Integers K))
    (u : (v.adicCompletionIntegers K)ˣ) (x : v.adicCompletion K) :
    chapter08LocalOrder v
        (((u : v.adicCompletionIntegers K) : v.adicCompletion K) * x) =
      chapter08LocalOrder v x := by
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
  constructor
  · intro h v
    have hc := congrArg (fun I : Chapter08IdealGroup K =>
      FractionalIdeal.count K v (I : Chapter08FractionalIdeal K)) h
    rw [chapter08_finite_idele_ideal_count x v,
      chapter08_finite_idele_ideal_count y v] at hc
    exact hc
  · intro h
    apply Units.ext
    change chapter08FiniteIdeleFractionalIdeal x =
      chapter08FiniteIdeleFractionalIdeal y
    have hfacx := FractionalIdeal.finprod_heightOneSpectrum_factorization' K
      (I := chapter08FiniteIdeleFractionalIdeal x)
      (chapter08_finite_idele_fractionalIdeal_ne_zero x)
    have hfacy := FractionalIdeal.finprod_heightOneSpectrum_factorization' K
      (I := chapter08FiniteIdeleFractionalIdeal y)
      (chapter08_finite_idele_fractionalIdeal_ne_zero y)
    calc
      chapter08FiniteIdeleFractionalIdeal x =
          ∏ᶠ v : HeightOneSpectrum (Chapter08Integers K),
            (v.asIdeal : Chapter08FractionalIdeal K) ^
              FractionalIdeal.count K v (chapter08FiniteIdeleFractionalIdeal x) :=
        hfacx.symm
      _ = ∏ᶠ v : HeightOneSpectrum (Chapter08Integers K),
          (v.asIdeal : Chapter08FractionalIdeal K) ^
            FractionalIdeal.count K v (chapter08FiniteIdeleFractionalIdeal y) := by
        apply finprod_congr
        intro v
        have hcx : FractionalIdeal.count K v
            (chapter08FiniteIdeleFractionalIdeal x) = chapter08FiniteIdeleOrder x v := by
          exact chapter08_finite_idele_ideal_count x v
        have hcy : FractionalIdeal.count K v
            (chapter08FiniteIdeleFractionalIdeal y) = chapter08FiniteIdeleOrder y v := by
          exact chapter08_finite_idele_ideal_count y v
        rw [hcx, hcy, h v]
      _ = chapter08FiniteIdeleFractionalIdeal y := hfacy

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
    {p m : ℕ} (hp : Nat.Prime p) (hm : 0 < m) :
    ¬ chapter08RayClassFiniteCongruence p m 1 2 := by
  intro h
  have hpow : (p ^ m : ℤ) ∣ (1 : ℤ) := by
    simpa using (Nat.modEq_iff_dvd.mp h)
  have hpz : (p : ℤ) ∣ (1 : ℤ) := by
    exact dvd_trans (by exact_mod_cast dvd_pow_self p (Nat.ne_of_gt hm)) hpow
  have hp' : p ∣ 1 := by exact_mod_cast hpz
  exact hp.not_dvd_one hp'

theorem chapter08_one_two_same_local_ideal_when_two_is_a_unit
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (Chapter08Integers K))
    (h2 : (Valued.v (2 : v.adicCompletion K) : ℤᵐ⁰) = 1) :
    chapter08SameLocalIdealAt v (1 : v.adicCompletion K) (2 : v.adicCompletion K) := by
  unfold chapter08SameLocalIdealAt
  have h2ne : (2 : v.adicCompletion K) ≠ 0 := by
    intro hzero
    have hvzero : (Valued.v (2 : v.adicCompletion K) : ℤᵐ⁰) = 0 := by
      rw [hzero, map_zero]
    exact one_ne_zero (h2.symm.trans hvzero)
  refine ⟨one_ne_zero, h2ne, ?_⟩
  exact ((chapter08_local_order_eq_zero_iff_valued_eq_one v
      (1 : v.adicCompletion K) one_ne_zero).2 (Valuation.map_one _)).trans
    ((chapter08_local_order_eq_zero_iff_valued_eq_one v
      (2 : v.adicCompletion K) h2ne).2 h2).symm

theorem chapter08_unit_pair_has_same_local_ideal
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (Chapter08Integers K))
    (u w : (v.adicCompletionIntegers K)ˣ) :
    chapter08SameLocalIdealAt v
      ((u : v.adicCompletionIntegers K) : v.adicCompletion K)
      ((w : v.adicCompletionIntegers K) : v.adicCompletion K) := by
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
