import LastLib.Book01ValuationsDVRsAndCompletions.Chapter06.Section03CauchySequences
import Mathlib.Tactic.Ring

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter06

open Set Filter Function
open scoped BigOperators Pointwise Topology WithZero NNReal Valued

noncomputable section

/-! # Book 1, Chapter 6, Section 6.5: Infinite Products
-/

/-! ### 6.5 Infinite products -/

section Products

variable {K : Type*} [Field K]

/-- The `n`th partial product of factors `1 + aₙ`. -/
def chapter06PartialProducts (a : ℕ → K) (n : ℕ) : K :=
  Finset.prod (Finset.range n) (fun i => (1 + a i))

/-- Convergence of the infinite product `∏ (1+aₙ)`. -/
def chapter06InfiniteProductConverges
    (v : AbsoluteValue K ℝ) (a : ℕ → K) (p : K) : Prop :=
  chapter06ConvergesTo v (chapter06PartialProducts a) p

/-- The finite tail product between two indices. -/
def chapter06ProductTail (a : ℕ → K) (n m : ℕ) : K :=
  Finset.prod (Finset.Ico n m) (fun i => (1 + a i))

/-- The product-tail analogue of the ultrametric maximum estimate. -/
theorem chapter06_product_tail_minus_one_bound
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {a : ℕ → K} {n m : ℕ} (_hnm : n < m)
    (hsmall : ∀ i ∈ Finset.Ico n m, v (a i) < 1)
    (hs : (Finset.Ico n m).Nonempty) :
    v (chapter06ProductTail a n m - 1) ≤
      (Finset.Ico n m).sup' hs (fun i => v (a i)) := by
  classical
  have hfactor : ∀ i : ℕ, v (a i) < 1 → v (1 + a i) = 1 := by
    intro i hi
    have hlocal : chapter06Distance v (1 + a i) 1 < v 1 := by
      change v ((1 + a i) - 1) < v 1
      simpa using hi
    simpa using
      (chapter06_abs_value_locally_constant_at_nonzero v hv
        (x := (1 : K)) (y := 1 + a i) one_ne_zero hlocal)
  have hprod : ∀ t : Finset ℕ, (∀ i ∈ t, v (a i) < 1) →
      v (Finset.prod t (fun i => (1 + a i))) = 1 := by
    intro t ht
    rw [map_prod]
    apply Finset.prod_eq_one
    intro i hi
    exact hfactor i (ht i hi)
  have hbound : ∀ (t : Finset ℕ) (ht : t.Nonempty),
      (∀ i ∈ t, v (a i) < 1) →
        v (Finset.prod t (fun i => (1 + a i)) - 1) ≤
          t.sup' ht (fun i => v (a i)) := by
    intro t ht
    induction t using Finset.induction_on with
    | empty => exact (Finset.not_nonempty_empty ht).elim
    | @insert i t hi ih =>
        intro hti
        by_cases htn : t.Nonempty
        · have htail := ih htn (fun j hj => hti j (Finset.mem_insert_of_mem hj))
          have hdecomp :
              Finset.prod (insert i t) (fun j => (1 + a j)) - 1 =
                a i * Finset.prod t (fun j => (1 + a j)) +
                  (Finset.prod t (fun j => (1 + a j)) - 1) := by
            rw [Finset.prod_insert hi]
            ring
          rw [hdecomp]
          calc
            v (a i * Finset.prod t (fun j => (1 + a j)) +
                (Finset.prod t (fun j => (1 + a j)) - 1)) ≤
                max (v (a i * Finset.prod t (fun j => (1 + a j))))
                  (v (Finset.prod t (fun j => (1 + a j)) - 1)) := hv _ _
            _ = max (v (a i) * v (Finset.prod t (fun j => (1 + a j))))
                  (v (Finset.prod t (fun j => (1 + a j)) - 1)) := by
              rw [v.map_mul]
            _ = max (v (a i))
                  (v (Finset.prod t (fun j => (1 + a j)) - 1)) := by
              rw [hprod t (fun j hj => hti j (Finset.mem_insert_of_mem hj))]
              simp
            _ ≤ max (v (a i)) (t.sup' htn (fun j => v (a j))) :=
              max_le (le_max_left _ _)
                (htail.trans (le_max_right _ _))
            _ = (insert i t).sup' (by simp) (fun j => v (a j)) := by
              simp [Finset.sup'_insert, htn]
        · have hte : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp htn
          subst t
          simp
  unfold chapter06ProductTail
  exact hbound (Finset.Ico n m) hs hsmall

/-- Eventually, factors in a product with `aₙ → 0` are units of absolute value one. -/
theorem chapter06_eventual_product_factors_are_units
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) {a : ℕ → K}
    (hzero : chapter06TendsToZero v a) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → v (a n) < 1 ∧ v (1 + a n) = 1 := by
  obtain ⟨N, hN⟩ := hzero 1 zero_lt_one
  refine ⟨N, ?_⟩
  intro n hn
  refine ⟨hN n hn, ?_⟩
  have hlocal : chapter06Distance v (1 + a n) 1 < v 1 := by
    change v ((1 + a n) - 1) < v 1
    simpa using hN n hn
  simpa using
    (chapter06_abs_value_locally_constant_at_nonzero v hv
      (x := (1 : K)) (y := 1 + a n) one_ne_zero hlocal)

/-- In a complete nonarchimedean field, `aₙ → 0` makes the product converge. -/
theorem chapter06_infinite_product_converges_of_terms_tend_to_zero
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (hcomplete : chapter06CompleteValuedSpace v) {a : ℕ → K}
    (hzero : chapter06TendsToZero v a) :
    ∃ p : K, chapter06InfiniteProductConverges v a p := by
  obtain ⟨N, hN⟩ := chapter06_eventual_product_factors_are_units v hv hzero
  have hnorm : ∀ q : ℕ, N ≤ q →
      v (chapter06PartialProducts a q) = v (chapter06PartialProducts a N) := by
    intro q hq
    have hdecomp : chapter06PartialProducts a q =
        chapter06PartialProducts a N * chapter06ProductTail a N q := by
      unfold chapter06PartialProducts chapter06ProductTail
      rw [← Finset.prod_range_mul_prod_Ico _ hq]
    have htail : v (chapter06ProductTail a N q) = 1 := by
      unfold chapter06ProductTail
      rw [map_prod]
      apply Finset.prod_eq_one
      intro i hi
      exact (hN i (Finset.mem_Ico.mp hi).1).2
    rw [hdecomp, v.map_mul, htail, mul_one]
  have hinc : chapter06TendsToZero v
      (fun n => chapter06PartialProducts a (n + 1) - chapter06PartialProducts a n) := by
    intro ε hε
    by_cases hC : v (chapter06PartialProducts a N) = 0
    · refine ⟨N, ?_⟩
      intro n hn
      have hident : chapter06PartialProducts a (n + 1) - chapter06PartialProducts a n =
          chapter06PartialProducts a n * a n := by
        unfold chapter06PartialProducts
        rw [Finset.prod_range_succ]
        ring
      change v (chapter06PartialProducts a (n + 1) - chapter06PartialProducts a n) < ε
      rw [hident, v.map_mul, hnorm n hn, hC, zero_mul]
      exact hε
    · have hCpos : 0 < v (chapter06PartialProducts a N) :=
        have hP0 : chapter06PartialProducts a N ≠ 0 := by
          intro hP
          apply hC
          simp [hP]
        v.pos hP0
      obtain ⟨N', hN'⟩ := hzero (ε / v (chapter06PartialProducts a N))
        (div_pos hε hCpos)
      refine ⟨max N N', ?_⟩
      intro n hn
      have hnN : N ≤ n := le_trans (le_max_left _ _) hn
      have hnN' : N' ≤ n := le_trans (le_max_right _ _) hn
      have hident : chapter06PartialProducts a (n + 1) - chapter06PartialProducts a n =
          chapter06PartialProducts a n * a n := by
        unfold chapter06PartialProducts
        rw [Finset.prod_range_succ]
        ring
      change v (chapter06PartialProducts a (n + 1) - chapter06PartialProducts a n) < ε
      rw [hident, v.map_mul, hnorm n hnN]
      simpa [mul_comm] using (lt_div_iff₀ hCpos).1 (hN' n hnN')
  obtain ⟨p, hp⟩ := hcomplete (chapter06PartialProducts a)
    (chapter06_cauchy_of_consecutive_differences_tend_to_zero v hv hinc)
  exact ⟨p, hp⟩

/-- A product with vanishing corrections is nonzero when no factor is zero. -/
theorem chapter06_infinite_product_nonzero
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {a : ℕ → K} (hzero : chapter06TendsToZero v a)
    {p : K} (hp : chapter06InfiniteProductConverges v a p)
    (hfactor : ∀ n : ℕ, 1 + a n ≠ 0) :
    p ≠ 0 := by
  obtain ⟨N, hN⟩ := chapter06_eventual_product_factors_are_units v hv hzero
  have hPN : chapter06PartialProducts a N ≠ 0 := by
    intro hP
    have hP' : ∃ i ∈ Finset.range N, 1 + a i = 0 := by
      simpa [chapter06PartialProducts, Finset.prod_eq_zero_iff] using hP
    rcases hP' with ⟨i, hi, hfac⟩
    exact hfactor i (by simpa [chapter06PartialProducts] using hfac)
  have hCpos : 0 < v (chapter06PartialProducts a N) := v.pos hPN
  obtain ⟨M, hM⟩ := hp (v (chapter06PartialProducts a N)) hCpos
  let q := max N M
  have hqN : N ≤ q := le_max_left _ _
  have hqM : M ≤ q := le_max_right _ _
  have hnorm : v (chapter06PartialProducts a q) =
      v (chapter06PartialProducts a N) := by
    have hdecomp : chapter06PartialProducts a q =
        chapter06PartialProducts a N * chapter06ProductTail a N q := by
      unfold chapter06PartialProducts chapter06ProductTail
      rw [← Finset.prod_range_mul_prod_Ico _ hqN]
    have htail : v (chapter06ProductTail a N q) = 1 := by
      unfold chapter06ProductTail
      rw [map_prod]
      apply Finset.prod_eq_one
      intro i hi
      exact (hN i (Finset.mem_Ico.mp hi).1).2
    rw [hdecomp, v.map_mul, htail, mul_one]
  intro hp0
  have hdist := hM q hqM
  have hdist' : v (chapter06PartialProducts a q) <
      v (chapter06PartialProducts a N) := by
    simpa [chapter06Distance, hp0] using hdist
  exact (lt_irrefl _) (hnorm ▸ hdist')

/-- The convergence criterion for products needs vanishing corrections, not real summability. -/
theorem chapter06_product_criterion_is_vanishing_not_summability
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (hcomplete : chapter06CompleteValuedSpace v) {a : ℕ → K} :
    chapter06TendsToZero v a →
      ∃ p : K, chapter06InfiniteProductConverges v a p := by
  intro hzero
  exact chapter06_infinite_product_converges_of_terms_tend_to_zero v hv hcomplete hzero

end Products

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter06
