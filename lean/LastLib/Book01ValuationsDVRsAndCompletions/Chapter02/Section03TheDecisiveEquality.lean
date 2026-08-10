import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic.Push

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
open scoped BigOperators

/-! # Book 1, Chapter 2, Section 2.3: The Decisive Equality
-/

/-! ## 2.3. The decisive equality -/

theorem chapter02_unequal_values_do_not_cancel
    {R Γ : Type*} [Ring R] [LinearOrderedAddCommMonoidWithTop Γ]
    (v : AddValuation R Γ) {x y : R} (hxy : v x ≠ v y) :
    v (x + y) = min (v x) (v y) := by
  exact v.map_add_of_distinct_val hxy

theorem chapter02_strictly_smallest_term_controls_finite_sum
    {R Γ ι : Type*} [Ring R] [LinearOrderedAddCommMonoidWithTop Γ]
    [DecidableEq ι] (v : AddValuation R Γ) (s : Finset ι) (f : ι → R) (j : ι)
    (hj : j ∈ s)
    (hmin : ∀ i ∈ s, i ≠ j → v (f j) < v (f i)) :
    v (∑ i ∈ s, f i) = v (f j) := by
  classical
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hj]
  let t := s \ {j}
  by_cases ht : t.Nonempty
  · have hfjtop : v (f j) ≠ (⊤ : Γ) := by
      obtain ⟨i, hi⟩ := ht
      exact ne_of_lt <| (hmin i (Finset.mem_sdiff.mp hi).1 (by
        intro hij
        exact (Finset.mem_sdiff.mp hi).2 (by simp [hij]))).trans_le le_top
    apply v.map_add_eq_of_lt_left
    apply v.map_lt_sum hfjtop
    intro i hi
    exact hmin i (Finset.mem_sdiff.mp hi).1 (by
      intro hij
      exact (Finset.mem_sdiff.mp hi).2 (by simp [hij]))
  · have ht0 : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    simp [t, ht0]

/-- For a finite zero-sum of nonzero terms, the minimum valuation occurs at
least twice. The nonzero condition makes explicit the usual convention that
zero terms have first been discarded from the sum. -/
theorem chapter02_zero_finite_sum_has_repeated_minimum
    {R Γ ι : Type*} [Ring R] [LinearOrderedAddCommMonoidWithTop Γ]
    [DecidableEq ι] (v : AddValuation R Γ) (s : Finset ι) (f : ι → R)
    (hs : s.Nonempty) (hz : ∑ i ∈ s, f i = 0)
    (hnz : ∀ i ∈ s, f i ≠ 0) :
    ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧
      v (f i) = v (f j) ∧ ∀ k ∈ s, v (f i) ≤ v (f k) := by
  obtain ⟨i, hi, himin⟩ := Finset.exists_min_image s (fun k => v (f k)) hs
  by_cases hstrict : ∀ k ∈ s, k ≠ i → v (f i) < v (f k)
  · have hsum := chapter02_strictly_smallest_term_controls_finite_sum v s f i hi hstrict
    have hfi_top : v (f i) ≠ (⊤ : Γ) := by
      intro htop
      by_cases hsone : s = {i}
      · apply hnz i hi
        simpa [hsone] using hz
      · have hs_sub : s ⊆ {i} := by
          intro k hk
          by_contra hki
          have hki' : k ≠ i := by
            intro hki'
            exact hki (Finset.mem_singleton.mpr hki')
          exact (not_lt_of_ge (by simp [htop])) (hstrict k hk hki')
        have hs_eq : s = {i} := Finset.eq_singleton_iff_unique_mem.mpr
          ⟨hi, fun k hk => Finset.mem_singleton.mp (hs_sub hk)⟩
        exact hsone hs_eq
    exfalso
    apply hfi_top
    simpa [hz] using hsum.symm
  · push Not at hstrict
    obtain ⟨j, hj, hji, hjnot⟩ := hstrict
    refine ⟨i, hi, j, hj, hji.symm, le_antisymm (himin j hj) hjnot, ?_⟩
    exact himin

theorem chapter02_minimum_occurs_twice_in_zero_sum
    {R Γ ι : Type*} [Ring R] [LinearOrderedAddCommMonoidWithTop Γ]
    [DecidableEq ι] (v : AddValuation R Γ) (s : Finset ι) (f : ι → R)
    (hz : ∑ i ∈ s, f i = 0) (hunique : ∃ j ∈ s,
      ∀ i ∈ s, i ≠ j → v (f j) < v (f i)) :
    ¬ (∀ i ∈ s, f i ≠ 0) := by
  intro hnz
  rcases hunique with ⟨j, hj, hjmin⟩
  have hsum := chapter02_strictly_smallest_term_controls_finite_sum v s f j hj hjmin
  have hfjtop : v (f j) ≠ (⊤ : Γ) := by
    intro htop
    by_cases hsone : s = {j}
    · apply hnz j hj
      simpa [hsone] using hz
    · have hs_sub : s ⊆ {j} := by
        intro k hk
        by_contra hkj
        have hkj' : k ≠ j := by
          intro hkj'
          exact hkj (Finset.mem_singleton.mpr hkj')
        exact (not_lt_of_ge (by simp [htop])) (hjmin k hk hkj')
      have hs_eq : s = {j} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hj, fun k hk => Finset.mem_singleton.mp (hs_sub hk)⟩
      exact hsone hs_eq
  apply hfjtop
  simpa [hz] using hsum.symm

end
end LastLib.Book01ValuationsDVRsAndCompletions.Chapter02
