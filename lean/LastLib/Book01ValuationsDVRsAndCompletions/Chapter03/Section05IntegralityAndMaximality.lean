import LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.Section01BoundedElements
import Mathlib.Algebra.BigOperators.Field
import Mathlib.RingTheory.Valuation.Integers
import Mathlib.RingTheory.Valuation.Integral

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter03

open Set
open scoped BigOperators WithZero LaurentSeries PowerSeries

/-!
# Chapter 3: Valuation rings and divisibility

Mathlib uses multiplicative valuations, so bounded elements are written `v x ≤ 1`.
The additive convention in the book is recorded below with `AddValuation`; under the
usual sign change, `v x ≤ 1` is the same assertion as `0 ≤ v x`.
-/

universe u v w

/-! # Book 1, Chapter 3, Section 3.5: Integrality and Maximality
-/

section IntegralityAndMaximality

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

/-! ### 3.5. Integrality and maximality -/

theorem valuationRingOf_isIntegrallyClosed (v : Valuation K Γ) :
    IsIntegrallyClosed (valuationRingOf v) := by
  infer_instance

theorem element_outside_valuationRing_has_inverse_in_maximalIdeal
    (v : Valuation K Γ) {x : K} (hxV : x ∉ valuationRingOf v) :
    x⁻¹ ∈ valuationRingOf v ∧
      ∃ y : valuationRingOf v, y ∈ maximalIdealOf v ∧ (y : K) = x⁻¹ := by
  have hx0 : x ≠ 0 := by
    intro hx
    apply hxV
    simp [hx]
  obtain hxinv | hxinv := Valuation.val_le_one_or_val_inv_le_one v x
  · exact False.elim (hxV ((mem_valuationRingOf_iff v x).2 hxinv))
  · refine ⟨(mem_valuationRingOf_iff v x⁻¹).2 hxinv, ?_⟩
    refine ⟨⟨x⁻¹, (mem_valuationRingOf_iff v x⁻¹).2 hxinv⟩, ?_, rfl⟩
    apply (mem_maximalIdealOf_iff v _).2
    apply (Valuation.one_lt_val_iff v hx0).mp
    exact lt_of_not_ge (fun h => hxV ((mem_valuationRingOf_iff v x).2 h))

theorem monic_relation_divide_by_top_power
    (v : Valuation K Γ) (p : Polynomial (valuationRingOf v)) {x : K}
    (hx : x ≠ 0) (hp : p.Monic)
    (hroot : p.eval₂ (algebraMap (valuationRingOf v) K) x = 0) :
    1 + ∑ i ∈ Finset.range p.natDegree,
      (algebraMap (valuationRingOf v) K (p.coeff i) * x ^ i) / x ^ p.natDegree = 0 := by
  have hsum :
      (∑ i ∈ Finset.range p.natDegree,
        algebraMap (valuationRingOf v) K (p.coeff i) * x ^ i) + x ^ p.natDegree = 0 := by
    rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ,
      hp.coeff_natDegree, map_one, one_mul] at hroot
    exact hroot
  have hdiv := congrArg (fun z : K => z / x ^ p.natDegree) hsum
  field_simp [hx] at hdiv
  calc
    1 + ∑ i ∈ Finset.range p.natDegree,
        (algebraMap (valuationRingOf v) K (p.coeff i) * x ^ i) / x ^ p.natDegree =
      ((∑ i ∈ Finset.range p.natDegree,
        algebraMap (valuationRingOf v) K (p.coeff i) * x ^ i) + x ^ p.natDegree) /
        x ^ p.natDegree := by
          rw [add_div, Finset.sum_div]
          simp [hx, add_comm]
    _ = 0 := by rw [hsum, zero_div]

theorem monic_relation_divided_tail_is_infinitesimal
    (v : Valuation K Γ) (p : Polynomial (valuationRingOf v)) {x : K}
    (hxV : x ∉ valuationRingOf v) :
    ∀ i ∈ Finset.range p.natDegree,
      (algebraMap (valuationRingOf v) K (p.coeff i) * x ^ i) / x ^ p.natDegree ∈
        maximalIdealImageOf v := by
  intro i hi
  have hx0 : x ≠ 0 := by
    intro hx
    apply hxV
    simp [hx]
  let z : K :=
    (algebraMap (valuationRingOf v) K (p.coeff i) * x ^ i) / x ^ p.natDegree
  have hcoeff : v (algebraMap (valuationRingOf v) K (p.coeff i)) ≤ 1 :=
    (mem_valuationRingOf_iff v _).1 (p.coeff i).property
  have hxgt : 1 < v x :=
    lt_of_not_ge (fun h => hxV ((mem_valuationRingOf_iff v x).2 h))
  have hpow : v x ^ i < v x ^ p.natDegree :=
    pow_lt_pow_right₀ hxgt (Finset.mem_range.mp hi)
  have hz : v z < 1 := by
    dsimp [z]
    rw [v.map_div]
    apply (div_lt_one₀ (v.pos_iff.mpr (pow_ne_zero _ hx0))).2
    rw [v.map_mul, v.map_pow, v.map_pow]
    exact mul_lt_of_le_one_of_lt hcoeff hpow
  have hzV : z ∈ valuationRingOf v := (mem_valuationRingOf_iff v z).2 hz.le
  refine ⟨⟨z, hzV⟩, (mem_maximalIdealOf_iff v ⟨z, hzV⟩).2 hz, ?_⟩
  rfl

theorem local_sum_of_maximal_ideal_terms_ne_neg_one
    {R : Type*} [CommRing R] [IsLocalRing R]
    {ι : Type*} (s : Finset ι) (f : ι → R)
    (hf : ∀ i ∈ s, f i ∈ IsLocalRing.maximalIdeal R) :
    (∑ i ∈ s, f i) ≠ -1 := by
  intro hsum
  have hmem : (∑ i ∈ s, f i) ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalRing.maximalIdeal R).sum_mem (fun i hi => hf i hi)
  have hneg := (IsLocalRing.maximalIdeal R).neg_mem hmem
  rw [hsum] at hneg
  exact (Ideal.ne_top_iff_one _).mp
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top (by
        rw [neg_neg] at hneg
        exact hneg)

theorem integral_element_outside_valuationRing_contradiction
    (v : Valuation K Γ) {x : K} (hx : IsIntegral (valuationRingOf v) x)
    (hxV : x ∉ valuationRingOf v) : False := by
  have hxle : v x ≤ 1 :=
    (Valuation.Integers.isIntegral_iff_v_le_one
      (Valuation.integer.integers v)).mp hx
  exact hxV ((mem_valuationRingOf_iff v x).2 hxle)

theorem integral_element_mem_valuationRing
    (v : Valuation K Γ) {x : K} (hx : IsIntegral (valuationRingOf v) x) :
    x ∈ valuationRingOf v := by
  apply (mem_valuationRingOf_iff v x).2
  exact (Valuation.Integers.isIntegral_iff_v_le_one
    (Valuation.integer.integers v)).mp hx

/- Maximality among local subrings dominated by the same place. -/

def contractedMaximalIdeal {V W : Subring K} (hVW : V ≤ W) [IsLocalRing W] : Ideal V :=
  (IsLocalRing.maximalIdeal W).comap (Subring.inclusion hVW)

theorem local_subring_inverse_obstruction
    (v : Valuation K Γ) (W : Subring K) [IsLocalRing W]
    (hVW : valuationRingOf v ≤ W)
    (hcontract : contractedMaximalIdeal hVW = maximalIdealOf v)
    {x : K} (hxW : x ∈ W) (hxV : x ∉ valuationRingOf v) : False := by
  have hx0 : x ≠ 0 := by
    intro hx
    apply hxV
    simp [hx]
  obtain ⟨hxiV, ⟨y, hyM, hyx⟩⟩ :=
    element_outside_valuationRing_has_inverse_in_maximalIdeal v hxV
  have hxiM : (⟨x⁻¹, hxiV⟩ : valuationRingOf v) ∈ maximalIdealOf v := by
    convert hyM using 1
    apply Subtype.ext
    exact hyx.symm
  have hxiW : x⁻¹ ∈ W := hVW hxiV
  have hxiMWV : (⟨x⁻¹, hxiV⟩ : valuationRingOf v) ∈ contractedMaximalIdeal hVW := by
    rw [hcontract]
    exact hxiM
  have hxiMW : (⟨x⁻¹, hxiW⟩ : W) ∈ IsLocalRing.maximalIdeal W := by
    exact hxiMWV
  have hunit : IsUnit (⟨x⁻¹, hxiW⟩ : W) := by
    apply IsUnit.of_mul_eq_one (⟨x, hxW⟩ : W)
    apply Subtype.ext
    simp [hx0]
  rw [IsLocalRing.mem_maximalIdeal] at hxiMW
  exact hxiMW hunit

theorem valuationRingOf_maximal_among_dominated_local_subrings
    (v : Valuation K Γ) (W : Subring K) [IsLocalRing W]
    (hVW : valuationRingOf v ≤ W)
    (hcontract : contractedMaximalIdeal hVW = maximalIdealOf v) :
    W = valuationRingOf v := by
  apply le_antisymm
  · intro x hxW
    by_contra hxV
    exact local_subring_inverse_obstruction v W hVW hcontract hxW hxV
  · exact hVW

end IntegralityAndMaximality

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter03
