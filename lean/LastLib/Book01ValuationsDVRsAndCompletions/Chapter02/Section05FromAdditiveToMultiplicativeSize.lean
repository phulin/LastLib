import Mathlib
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter02.Section04EquivalenceAndNormalization

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter02

/-!
# Chapter 2: Valuations

This file is a statement-generation pass for Chapter 2 of *Valuations, DVRs,
and Completions*.  The declarations are deliberately self-contained: they
use Mathlib's `AddValuation` where it has the required interface and introduce
chapter-local names for the constructions that are specific to the exposition.
-/

noncomputable section

open Set Function
open scoped BigOperators LaurentSeries
open HahnSeries Polynomial

/-! # Book 1, Chapter 2, Section 2.5: From Additive to Multiplicative Size
-/

/-! ## 2.5. From additive values to multiplicative absolute values -/

def Chapter02RealSizeFromValuation
    {K : Type*} [Field K] (c : ℝ) (_hc : 0 < c) (_hc1 : c < 1)
    (v : AddValuation K (WithTop ℝ)) (x : K) : ℝ :=
  if hx : v x = ⊤ then 0 else Real.rpow c ((v x).untop hx)

theorem chapter02_real_size_of_zero
    {K : Type*} [Field K] {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (v : AddValuation K (WithTop ℝ)) :
    Chapter02RealSizeFromValuation c hc hc1 v 0 = 0 := by
  simp [Chapter02RealSizeFromValuation]

theorem chapter02_real_size_of_one
    {K : Type*} [Field K] {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (v : AddValuation K (WithTop ℝ)) :
    Chapter02RealSizeFromValuation c hc hc1 v 1 = 1 := by
  simp [Chapter02RealSizeFromValuation]

theorem chapter02_real_size_is_multiplicative
    {K : Type*} [Field K] {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (v : AddValuation K (WithTop ℝ)) (x y : K) :
    Chapter02RealSizeFromValuation c hc hc1 v (x * y) =
      Chapter02RealSizeFromValuation c hc hc1 v x *
        Chapter02RealSizeFromValuation c hc hc1 v y := by
  classical
  by_cases hx : x = 0
  · simp [Chapter02RealSizeFromValuation, hx]
  by_cases hy : y = 0
  · simp [Chapter02RealSizeFromValuation, hy]
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  have hxv : v x ≠ (⊤ : WithTop ℝ) := (AddValuation.ne_top_iff v).2 hx
  have hyv : v y ≠ (⊤ : WithTop ℝ) := (AddValuation.ne_top_iff v).2 hy
  have hxyv : v (x * y) ≠ (⊤ : WithTop ℝ) :=
    (AddValuation.ne_top_iff v).2 hxy
  have hun : (v (x * y)).untop hxyv =
      (v x).untop hxv + (v y).untop hyv := by
    apply WithTop.coe_injective
    simp [v.map_mul]
  simp only [Chapter02RealSizeFromValuation, dif_neg hxv, dif_neg hyv, dif_neg hxyv]
  rw [hun]
  exact Real.rpow_add hc _ _

theorem chapter02_real_size_is_ultrametric
    {K : Type*} [Field K] {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (v : AddValuation K (WithTop ℝ)) (x y : K) :
    Chapter02RealSizeFromValuation c hc hc1 v (x + y) ≤
      max (Chapter02RealSizeFromValuation c hc hc1 v x)
        (Chapter02RealSizeFromValuation c hc hc1 v y) := by
  classical
  by_cases hx : x = 0
  · simp [Chapter02RealSizeFromValuation, hx]
  by_cases hy : y = 0
  · simp [Chapter02RealSizeFromValuation, hy]
  by_cases hxy : x + y = 0
  · have hxyv0 : v (x + y) = (⊤ : WithTop ℝ) := by
      rw [hxy]
      exact v.map_zero
    simp only [Chapter02RealSizeFromValuation, dif_pos hxyv0]
    apply le_max_of_le_left
    split_ifs with hzero
    · simp
    · exact Real.rpow_nonneg hc.le _
  have hxv : v x ≠ (⊤ : WithTop ℝ) := (AddValuation.ne_top_iff v).2 hx
  have hyv : v y ≠ (⊤ : WithTop ℝ) := (AddValuation.ne_top_iff v).2 hy
  have hxyv : v (x + y) ≠ (⊤ : WithTop ℝ) :=
    (AddValuation.ne_top_iff v).2 hxy
  have hsum := v.map_add x y
  rcases le_total (v x) (v y) with hxyval | hyxval
  · have hsumx : v x ≤ v (x + y) := by
      simpa [min_eq_left hxyval] using hsum
    have hxexp : (v x).untop hxv ≤ (v (x + y)).untop hxyv := by
      exact WithTop.coe_le_coe.mp (by
        simpa only [WithTop.coe_untop] using hsumx)
    have hyexp : (v x).untop hxv ≤ (v y).untop hyv := by
      exact WithTop.coe_le_coe.mp (by
        simpa only [WithTop.coe_untop] using hxyval)
    have hpow_sum := Real.rpow_le_rpow_of_exponent_ge hc hc1.le hxexp
    have hpow_y := Real.rpow_le_rpow_of_exponent_ge hc hc1.le hyexp
    have hmax : max (Real.rpow c ((v x).untop hxv))
        (Real.rpow c ((v y).untop hyv)) =
        Real.rpow c ((v x).untop hxv) := max_eq_left hpow_y
    have hbound : Real.rpow c ((v (x + y)).untop hxyv) ≤
        max (Real.rpow c ((v x).untop hxv))
          (Real.rpow c ((v y).untop hyv)) := by
      rw [hmax]
      exact hpow_sum
    simpa only [Chapter02RealSizeFromValuation, dif_neg hxv, dif_neg hyv,
      dif_neg hxyv] using hbound
  · have hsumy : v y ≤ v (x + y) := by
      simpa [min_eq_right hyxval] using hsum
    have hyexp : (v y).untop hyv ≤ (v (x + y)).untop hxyv := by
      exact WithTop.coe_le_coe.mp (by
        simpa only [WithTop.coe_untop] using hsumy)
    have hxexp : (v y).untop hyv ≤ (v x).untop hxv := by
      exact WithTop.coe_le_coe.mp (by
        simpa only [WithTop.coe_untop] using hyxval)
    have hpow_sum := Real.rpow_le_rpow_of_exponent_ge hc hc1.le hyexp
    have hpow_x := Real.rpow_le_rpow_of_exponent_ge hc hc1.le hxexp
    have hmax : max (Real.rpow c ((v x).untop hxv))
        (Real.rpow c ((v y).untop hyv)) =
        Real.rpow c ((v y).untop hyv) := max_eq_right hpow_x
    have hbound : Real.rpow c ((v (x + y)).untop hxyv) ≤
        max (Real.rpow c ((v x).untop hxv))
          (Real.rpow c ((v y).untop hyv)) := by
      rw [hmax]
      exact hpow_sum
    simpa only [Chapter02RealSizeFromValuation, dif_neg hxv, dif_neg hyv,
      dif_neg hxyv] using hbound

def Chapter02PadicAdditiveValuation (p : ℕ) [Fact p.Prime] :
    AddValuation ℚ (WithTop ℤ) :=
  AddValuation.of
    (fun x : ℚ => if x = 0 then ⊤ else (padicValRat p x : WithTop ℤ))
    (by simp)
    (by simp)
    (by
      intro x y
      by_cases hxy : x + y = 0
      · simp [hxy]
      by_cases hx : x = 0
      · simp [hx]
      by_cases hy : y = 0
      · simp [hy]
      simp only [if_neg hx, if_neg hy, if_neg hxy]
      exact_mod_cast (padicValRat.min_le_padicValRat_add (p := p) hxy))
    (by
      intro x y
      by_cases hx : x = 0
      · simp [hx]
      by_cases hy : y = 0
      · simp [hy]
      simp [hx, hy, padicValRat.mul])

def Chapter02PadicAbsoluteValue (p : ℕ) [Fact p.Prime] (x : ℚ) : ℝ :=
  if x = 0 then 0 else Real.rpow (p : ℝ) (-(padicValRat p x : ℝ))
theorem chapter02_padic_value_of_p
    (p : ℕ) [Fact p.Prime] :
    Chapter02PadicAdditiveValuation p p = (1 : WithTop ℤ) := by
  have hp : Nat.Prime p := Fact.out
  simp [Chapter02PadicAdditiveValuation, hp.ne_zero, padicValRat.self hp.one_lt]

theorem chapter02_padic_absolute_value_of_p
    (p : ℕ) [Fact p.Prime] :
    Chapter02PadicAbsoluteValue p p = (p : ℝ)⁻¹ := by
  have hp : Nat.Prime p := Fact.out
  simp [Chapter02PadicAbsoluteValue, hp.ne_zero, padicValRat.self hp.one_lt,
    Real.rpow_neg_one]


theorem chapter02_padic_absolute_value_of_p_pow_times_prime_to_p
    (p n : ℕ) [Fact p.Prime] (a b : ℤ) (hb : b ≠ 0)
    (ha : ¬ (p : ℤ) ∣ a) (hbp : ¬ (p : ℤ) ∣ b) :
    Chapter02PadicAbsoluteValue p
        (((p : ℚ) ^ n) * (a : ℚ) / (b : ℚ)) =
      Real.rpow (p : ℝ) (-(n : ℝ)) := by
  have ha0 : a ≠ 0 := by
    intro ha0
    subst a
    simp at ha
  have hpn0 : (p : ℚ) ^ n ≠ 0 := by
    have hp : Nat.Prime p := Fact.out
    exact pow_ne_zero n (by exact_mod_cast hp.ne_zero)
  have hpa0 : (a : ℚ) ≠ 0 := by exact_mod_cast ha0
  have hpb0 : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  have hq0 : ((p : ℚ) ^ n) * (a : ℚ) / (b : ℚ) ≠ 0 :=
    div_ne_zero (mul_ne_zero hpn0 hpa0) hpb0
  have hva : padicValRat p (a : ℚ) = 0 := by
    rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd ha]
    norm_num
  have hvb : padicValRat p (b : ℚ) = 0 := by
    rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hbp]
    norm_num
  simp only [Chapter02PadicAbsoluteValue, if_neg hq0]
  rw [padicValRat.div (mul_ne_zero hpn0 hpa0) hpb0,
    padicValRat.mul hpn0 hpa0, padicValRat.pow,
    padicValRat.self (show 1 < p from (Fact.out : Nat.Prime p).one_lt), hva, hvb]
  norm_num

def Chapter02IsUltrametricAbsoluteValue {K : Type*} [Ring K]
    (f : K → ℝ) : Prop :=
  ∀ x y : K, f (x + y) ≤ max (f x) (f y)

def Chapter02LogarithmicValueFromAbsoluteValue
    {K : Type*} [Field K] (c : ℝ) (_hc : 0 < c) (_hc1 : c < 1)
    (f : K → ℝ) (x : K) : WithTop ℝ := by
  classical
  exact if hx : x = 0 then ⊤ else (Real.log (f x) / Real.log c : ℝ)

theorem chapter02_ultrametric_absolute_value_gives_additive_value
    {K : Type*} [Field K] (f : AbsoluteValue K ℝ)
    (hf : Chapter02IsUltrametricAbsoluteValue (f : K → ℝ))
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    ∃! v : AddValuation K (WithTop ℝ),
      ∀ x : K, v x =
        Chapter02LogarithmicValueFromAbsoluteValue c hc hc1 (f : K → ℝ) x := by
  have hlogc : Real.log c < 0 := Real.log_neg hc hc1
  have hmul : ∀ x y : K,
      Chapter02LogarithmicValueFromAbsoluteValue c hc hc1 (f : K → ℝ) (x * y) =
        Chapter02LogarithmicValueFromAbsoluteValue c hc hc1 (f : K → ℝ) x +
          Chapter02LogarithmicValueFromAbsoluteValue c hc hc1 (f : K → ℝ) y := by
    intro x y
    classical
    by_cases hx : x = 0
    · simp [Chapter02LogarithmicValueFromAbsoluteValue, hx]
    by_cases hy : y = 0
    · simp [Chapter02LogarithmicValueFromAbsoluteValue, hy]
    have hxy : x * y ≠ 0 := mul_ne_zero hx hy
    simp only [Chapter02LogarithmicValueFromAbsoluteValue, dif_neg hx, dif_neg hy,
      dif_neg hxy]
    rw [f.map_mul, Real.log_mul (f.ne_zero hx) (f.ne_zero hy), add_div]
    exact (WithTop.coe_add _ _).symm
  have hadd : ∀ x y : K,
      min (Chapter02LogarithmicValueFromAbsoluteValue c hc hc1 (f : K → ℝ) x)
          (Chapter02LogarithmicValueFromAbsoluteValue c hc hc1 (f : K → ℝ) y) ≤
        Chapter02LogarithmicValueFromAbsoluteValue c hc hc1 (f : K → ℝ) (x + y) := by
    intro x y
    classical
    by_cases hxy : x + y = 0
    · have htop : Chapter02LogarithmicValueFromAbsoluteValue c hc hc1
          (f : K → ℝ) (x + y) = ⊤ := by
        simp [Chapter02LogarithmicValueFromAbsoluteValue, hxy]
      rw [htop]
      exact le_top
    by_cases hx : x = 0
    · subst x
      simp [Chapter02LogarithmicValueFromAbsoluteValue]
    by_cases hy : y = 0
    · subst y
      simp [Chapter02LogarithmicValueFromAbsoluteValue]
    simp only [Chapter02LogarithmicValueFromAbsoluteValue, dif_neg hx, dif_neg hy,
      dif_neg hxy]
    rcases le_total (f x) (f y) with hxyf | hyxf
    · have hlogxy : Real.log (f x) ≤ Real.log (f y) :=
        Real.strictMonoOn_log.monotoneOn (f.pos hx) (f.pos hy) hxyf
      have hmin : min (Real.log (f x) / Real.log c)
            (Real.log (f y) / Real.log c) =
          Real.log (f y) / Real.log c := by
        rw [min_eq_right]
        exact (div_le_div_right_of_neg hlogc).2 hlogxy
      have hsum : f (x + y) ≤ f y := by
        simpa [max_eq_right hxyf] using hf x y
      have hlogsum : Real.log (f (x + y)) ≤ Real.log (f y) :=
        Real.strictMonoOn_log.monotoneOn (f.pos hxy) (f.pos hy) hsum
      have hdiv : Real.log (f y) / Real.log c ≤
          Real.log (f (x + y)) / Real.log c :=
        (div_le_div_right_of_neg hlogc).2 hlogsum
      exact (min_le_iff.mpr (Or.inr (WithTop.coe_le_coe.mpr hdiv)))
    · have hlogyx : Real.log (f y) ≤ Real.log (f x) :=
        Real.strictMonoOn_log.monotoneOn (f.pos hy) (f.pos hx) hyxf
      have hmin : min (Real.log (f x) / Real.log c)
            (Real.log (f y) / Real.log c) =
          Real.log (f x) / Real.log c := by
        rw [min_eq_left]
        exact (div_le_div_right_of_neg hlogc).2 hlogyx
      have hsum : f (x + y) ≤ f x := by
        simpa [max_eq_left hyxf] using hf x y
      have hlogsum : Real.log (f (x + y)) ≤ Real.log (f x) :=
        Real.strictMonoOn_log.monotoneOn (f.pos hxy) (f.pos hx) hsum
      have hdiv : Real.log (f x) / Real.log c ≤
          Real.log (f (x + y)) / Real.log c :=
        (div_le_div_right_of_neg hlogc).2 hlogsum
      exact (min_le_iff.mpr (Or.inl (WithTop.coe_le_coe.mpr hdiv)))
  let v : AddValuation K (WithTop ℝ) :=
    AddValuation.of
      (fun x => Chapter02LogarithmicValueFromAbsoluteValue c hc hc1
        (f : K → ℝ) x)
      (by simp [Chapter02LogarithmicValueFromAbsoluteValue])
      (by simp [Chapter02LogarithmicValueFromAbsoluteValue])
      hadd hmul
  refine ⟨v, ?_, ?_⟩
  · intro x
    rfl
  · intro w hw
    apply AddValuation.ext
    intro x
    rw [hw x]
    rfl

def Chapter02PositiveValueRescaling
    {K : Type*} [Field K] (v w : K → WithTop ℝ) : Prop := by
  classical
  exact ∃ r : ℝ, 0 < r ∧ ∀ x : K,
    w x = if h : v x = ⊤ then ⊤ else (r * (v x).untop h : WithTop ℝ)

theorem chapter02_changing_the_base_rescales_values
    {K : Type*} [Field K] (f : AbsoluteValue K ℝ)
    (_hf : Chapter02IsUltrametricAbsoluteValue (f : K → ℝ))
    {c d : ℝ} (hc : 0 < c) (hc1 : c < 1) (hd : 0 < d) (hd1 : d < 1) :
    Chapter02PositiveValueRescaling
      (fun x => Chapter02LogarithmicValueFromAbsoluteValue c hc hc1 (f : K → ℝ) x)
      (fun x => Chapter02LogarithmicValueFromAbsoluteValue d hd hd1 (f : K → ℝ) x) := by
  have hlogc : Real.log c < 0 := Real.log_neg hc hc1
  have hlogd : Real.log d < 0 := Real.log_neg hd hd1
  refine ⟨Real.log c / Real.log d, div_pos_of_neg_of_neg hlogc hlogd, ?_⟩
  intro x
  by_cases hx : x = 0
  · simp [Chapter02LogarithmicValueFromAbsoluteValue, hx]
  simp only [Chapter02LogarithmicValueFromAbsoluteValue, dif_neg hx]
  have hsrc : (Real.log (f x) / Real.log c : WithTop ℝ) ≠ ⊤ :=
    WithTop.coe_ne_top
  simp only [dif_neg hsrc, WithTop.coe_untop]
  rw [← WithTop.coe_mul]
  apply WithTop.coe_injective
  field_simp [ne_of_lt hlogc, ne_of_lt hlogd]

theorem chapter02_positive_rescaling_preserves_comparisons
    {K : Type*} [Field K] (v w : K → WithTop ℝ)
    (h : Chapter02PositiveValueRescaling v w) (x y : K) :
    v x ≤ v y ↔ w x ≤ w y := by
  rcases h with ⟨r, hr, hw⟩
  by_cases hx : v x = ⊤
  · by_cases hy : v y = ⊤
    · simp [hw, hx, hy]
    · simp only [hw, dif_pos hx, dif_neg hy]
      have hne : (↑r * v y : WithTop ℝ) ≠ ⊤ := by
        cases hval : v y with
        | top => exact (hy hval).elim
        | coe z =>
            rw [← WithTop.coe_mul]
            exact WithTop.coe_ne_top
      simp [hx, hy, hne]
  · by_cases hy : v y = ⊤
    · simp [hw, hx, hy]
    · simp only [hw, dif_neg hx, dif_neg hy]
      constructor
      · intro hxy
        have hxy' :
            (v x).untop hx ≤ (v y).untop hy :=
          WithTop.coe_le_coe.mp (by
            simpa only [WithTop.coe_untop] using hxy)
        exact WithTop.coe_le_coe.mpr
          ((mul_le_mul_iff_of_pos_left hr).2 hxy')
      · intro hxy
        have hxy' : (v x).untop hx ≤ (v y).untop hy :=
          (mul_le_mul_iff_of_pos_left hr).1
            (WithTop.coe_le_coe.mp hxy)
        exact by
          simpa only [WithTop.coe_untop] using
            (WithTop.coe_le_coe.mpr hxy')

end
end LastLib.Book01ValuationsDVRsAndCompletions.Chapter02
