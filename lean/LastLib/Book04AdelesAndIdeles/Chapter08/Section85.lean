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
  have huval : Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 := by
    exact (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).1
      u.isUnit
  by_cases hx : x = 0
  · simp [hx, chapter08LocalOrder]
  · have huxv :
        (Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) : ℤᵐ⁰) ≠ 0 := by
      rw [huval]
      exact one_ne_zero
    have hxv : (Valued.v x : ℤᵐ⁰) ≠ 0 := by simpa using hx
    have hmulv :
        Valued.v (((u : v.adicCompletionIntegers K) : v.adicCompletion K) * x) =
          Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) * Valued.v x :=
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).map_mul _ _
    have hprodv :
        (Valued.v (((u : v.adicCompletionIntegers K) : v.adicCompletion K) * x) : ℤᵐ⁰) ≠ 0 := by
      rw [hmulv]
      exact mul_ne_zero huxv hxv
    unfold chapter08LocalOrder
    rw [dif_neg hprodv, dif_neg hxv]
    have hu :
        WithZero.unzero hprodv =
          WithZero.unzero huxv * WithZero.unzero hxv := by
      rw [← WithZero.coe_inj, WithZero.coe_unzero, WithZero.coe_mul,
        WithZero.coe_unzero, WithZero.coe_unzero]
      exact hmulv
    have huadd : Multiplicative.toAdd (WithZero.unzero huxv) = 0 := by
      apply (WithZero.toAdd_unzero_eq_iff huxv (0 : ℤ)).2
      simpa only [ofAdd_zero, WithZero.coe_one] using huval
    rw [hu, toAdd_mul, huadd, zero_add]

theorem chapter08_local_ideal_eq_iff_unit_multiple
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (Chapter08Integers K))
    {x y : v.adicCompletion K} (hx : x ≠ 0) (hy : y ≠ 0) :
    chapter08SameLocalIdealAt v x y ↔ chapter08LocalUnitMultipleAt v x y := by
  unfold chapter08SameLocalIdealAt chapter08LocalUnitMultipleAt
  constructor
  · rintro ⟨_, _, hxy⟩
    have hxv : (Valued.v x : ℤᵐ⁰) ≠ 0 := by simpa using hx
    have hyv : (Valued.v y : ℤᵐ⁰) ≠ 0 := by simpa using hy
    unfold chapter08LocalOrder at hxy
    rw [dif_neg hxv, dif_neg hyv] at hxy
    have hadd :
        Multiplicative.toAdd (WithZero.unzero hxv) =
          Multiplicative.toAdd (WithZero.unzero hyv) := by
      exact neg_injective hxy
    have hun : WithZero.unzero hxv = WithZero.unzero hyv :=
      Multiplicative.toAdd.injective hadd
    have hval : Valued.v x = Valued.v y := by
      rw [← WithZero.coe_unzero hxv, ← WithZero.coe_unzero hyv, hun]
    let q : (v.adicCompletion K)ˣ :=
      Units.mk0 (y * x⁻¹) (mul_ne_zero hy (inv_ne_zero hx))
    have hqval : Valued.v (q : v.adicCompletion K) = 1 := by
      change Valued.v (y * x⁻¹) = 1
      calc
        Valued.v (y * x⁻¹) = Valued.v y * (Valued.v x)⁻¹ := by
          rw [(Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).map_mul,
            (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).map_inv]
        _ = Valued.v x * (Valued.v x)⁻¹ := by rw [hval]
        _ = 1 := mul_inv_cancel₀ hxv
    have hqmem : q ∈ (v.adicCompletionIntegers K).units :=
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one).2
        hqval
    let uq : (v.adicCompletionIntegers K).units := ⟨q, hqmem⟩
    let u : (v.adicCompletionIntegers K)ˣ :=
      (v.adicCompletionIntegers K).unitsEquivUnitsType uq
    refine ⟨u, ?_⟩
    change y = (y * x⁻¹) * x
    rw [mul_assoc, inv_mul_cancel₀ hx, mul_one]
  · intro h
    rcases h with ⟨u, hu⟩
    rw [hu]
    have hu0 : ((u : v.adicCompletionIntegers K) : v.adicCompletion K) ≠ 0 := by
      intro hzero
      have hzero' : (u : v.adicCompletionIntegers K) = 0 := Subtype.ext hzero
      exact u.isUnit.ne_zero hzero'
    constructor
    · exact hx
    constructor
    · exact mul_ne_zero hu0 hx
    · exact (chapter08_local_order_ignores_unit v u x).symm

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

/-! A prime-power congruence interface records the finite data retained by ray conditions. -/

def chapter08CongruentModulo {R : Type*} [Ring R]
    (I : Ideal R) (m : ℕ) (a b : R) : Prop :=
  a - b ∈ I ^ m

/-! This is only a natural-number illustration; it is not the ray-class congruence for
the ring of integers of a number field. -/
def chapter08NatPrimePowerCongruence (p m a b : ℕ) : Prop :=
  Nat.ModEq (p ^ m) a b

theorem chapter08_one_two_not_nat_congruent_mod_prime_pow
    {p m : ℕ} (hp : Nat.Prime p) (hm : 0 < m) :
    ¬ chapter08NatPrimePowerCongruence p m 1 2 := by
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
  unfold chapter08SameLocalIdealAt
  have hu0 : ((u : v.adicCompletionIntegers K) : v.adicCompletion K) ≠ 0 := by
    intro hzero
    have hzero' : (u : v.adicCompletionIntegers K) = 0 := Subtype.ext hzero
    exact u.isUnit.ne_zero hzero'
  have hw0 : ((w : v.adicCompletionIntegers K) : v.adicCompletion K) ≠ 0 := by
    intro hzero
    have hzero' : (w : v.adicCompletionIntegers K) = 0 := Subtype.ext hzero
    exact w.isUnit.ne_zero hzero'
  have huv : Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 := by
    exact (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).1
      u.isUnit
  have hwv : Valued.v ((w : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 := by
    exact (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).1
      w.isUnit
  constructor
  · exact hu0
  constructor
  · exact hw0
  · exact ((chapter08_local_order_eq_zero_iff_valued_eq_one v
        ((u : v.adicCompletionIntegers K) : v.adicCompletion K) hu0).2 huv).trans
      ((chapter08_local_order_eq_zero_iff_valued_eq_one v
        ((w : v.adicCompletionIntegers K) : v.adicCompletion K) hw0).2 hwv).symm

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
