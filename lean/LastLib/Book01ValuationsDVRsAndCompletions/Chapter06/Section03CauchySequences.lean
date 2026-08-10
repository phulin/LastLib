import LastLib.Book01ValuationsDVRsAndCompletions.Chapter06.Section02ContinuityOfAlgebraicOperations

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter06

open Set Filter Function
open scoped BigOperators Pointwise Topology WithZero NNReal Valued PowerSeries

noncomputable section

/-! # Book 1, Chapter 6, Section 6.3: Cauchy Sequences
-/

/-! ### 6.3 Cauchy sequences -/

section CauchySequences

variable {K : Type*} [Field K]

/-- Epsilon definition of a Cauchy sequence for an absolute value. -/
def chapter06CauchySeq (v : AbsoluteValue K ℝ) (x : ℕ → K) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
    N ≤ m → N ≤ n → chapter06Distance v (x m) (x n) < ε

/-- Epsilon definition of convergence in the valuation metric. -/
def chapter06ConvergesTo (v : AbsoluteValue K ℝ) (x : ℕ → K) (l : K) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ,
    N ≤ n → chapter06Distance v (x n) l < ε

/-- The terms of a sequence tend to zero. -/
def chapter06TendsToZero (v : AbsoluteValue K ℝ) (a : ℕ → K) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → v (a n) < ε

/-- Completeness stated only in terms of the chapter's valuation metric. -/
def chapter06CompleteValuedSpace (v : AbsoluteValue K ℝ) : Prop :=
  ∀ x : ℕ → K, chapter06CauchySeq v x → ∃ l : K, chapter06ConvergesTo v x l

/-- Convergent sequences are Cauchy. -/
theorem chapter06_convergent_is_cauchy
    (v : AbsoluteValue K ℝ) {x : ℕ → K} {l : K}
    (h : chapter06ConvergesTo v x l) : chapter06CauchySeq v x := by
  intro ε hε
  obtain ⟨N, hN⟩ := h (ε / 2) (half_pos hε)
  refine ⟨N, ?_⟩
  intro m n hm hn
  change v (x m - x n) < ε
  calc
    v (x m - x n) ≤ v (x m - l) + v (l - x n) := v.sub_le (x m) l (x n)
    _ = v (x m - l) + v (x n - l) := by
      congr 1
      exact v.map_sub l (x n)
    _ < ε := by
      have hm' : v (x m - l) < ε / 2 := by simpa [chapter06Distance] using hN m hm
      have hn' : v (x n - l) < ε / 2 := by simpa [chapter06Distance] using hN n hn
      linarith

/-- Limits in the valuation metric are unique. -/
theorem chapter06_limit_unique
    (v : AbsoluteValue K ℝ) {x : ℕ → K} {l l' : K}
    (hl : chapter06ConvergesTo v x l) (hl' : chapter06ConvergesTo v x l') :
    l = l' := by
  by_contra hne
  have hpos : 0 < v (l - l') := v.pos (sub_ne_zero.mpr hne)
  obtain ⟨N, hN⟩ := hl (v (l - l') / 2) (half_pos hpos)
  obtain ⟨N', hN'⟩ := hl' (v (l - l') / 2) (half_pos hpos)
  let M := max N N'
  have hm : v (x M - l) < v (l - l') / 2 := by
    simpa [chapter06Distance] using hN M (le_max_left _ _)
  have hm' : v (x M - l') < v (l - l') / 2 := by
    simpa [chapter06Distance] using hN' M (le_max_right _ _)
  have hbound : v (l - l') ≤ v (l - x M) + v (x M - l') :=
    v.sub_le l (x M) l'
  have hsum : v (l - x M) + v (x M - l') < v (l - l') := by
    calc
      v (l - x M) + v (x M - l') =
          v (x M - l) + v (x M - l') := by
        congr 1
        exact v.map_sub l (x M)
      _ < v (l - l') / 2 + v (l - l') / 2 := add_lt_add hm hm'
      _ = v (l - l') := by ring
  exact (not_lt_of_ge hbound) hsum

/-- The finite-tail maximum estimate for consecutive increments. -/
theorem chapter06_consecutive_increment_tail_bound
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {x : ℕ → K} {n m : ℕ} (hnm : n < m)
    (hs : (Finset.Ico n m).Nonempty) :
    chapter06Distance v (x m) (x n) ≤
      (Finset.Ico n m).sup' hs
        (fun i => chapter06Distance v (x (i + 1)) (x i)) := by
  change v (x m - x n) ≤ _
  have hsum : ∀ k, n ≤ k →
      (Finset.sum (Finset.Ico n k) (fun i => x (i + 1) - x i)) = x k - x n := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
        rw [Finset.sum_Ico_succ_top hk, ih]
        ring
  rw [← hsum m hnm.le]
  change v (Finset.sum (Finset.Ico n m) (fun i => x (i + 1) - x i)) ≤
    (Finset.Ico n m).sup' hs (fun i => v (x (i + 1) - x i))
  exact IsNonarchimedean.apply_sum_le_sup hv hs

/-- Vanishing consecutive differences imply that a sequence is Cauchy. -/
theorem chapter06_cauchy_of_consecutive_differences_tend_to_zero
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) {x : ℕ → K}
    (hinc : chapter06TendsToZero v (fun n => x (n + 1) - x n)) :
    chapter06CauchySeq v x := by
  intro ε hε
  obtain ⟨N, hN⟩ := hinc ε hε
  refine ⟨N, ?_⟩
  intro m n hm hn
  change v (x m - x n) < ε
  by_cases hmn : m < n
  · have htail₀ := chapter06_consecutive_increment_tail_bound (x := x) v hv hmn
      ⟨m, Finset.mem_Ico.mpr ⟨le_rfl, hmn⟩⟩
    have htail : v (x m - x n) ≤
        (Finset.Ico m n).sup'
          ⟨m, Finset.mem_Ico.mpr ⟨le_rfl, hmn⟩⟩
          (fun i => v (x (i + 1) - x i)) := by
      simpa only [chapter06Distance, v.map_sub] using htail₀
    apply lt_of_le_of_lt htail
    apply (Finset.sup'_lt_iff _).2
    intro i hi
    exact hN i (hm.trans (Finset.mem_Ico.mp hi).1)
  · by_cases hnm : n < m
    · have htail₀ := chapter06_consecutive_increment_tail_bound (x := x) v hv hnm
        ⟨n, Finset.mem_Ico.mpr ⟨le_rfl, hnm⟩⟩
      have htail : v (x m - x n) ≤
          (Finset.Ico n m).sup'
            ⟨n, Finset.mem_Ico.mpr ⟨le_rfl, hnm⟩⟩
            (fun i => v (x (i + 1) - x i)) := by
        simpa [chapter06Distance] using htail₀
      apply lt_of_le_of_lt htail
      apply (Finset.sup'_lt_iff _).2
      intro i hi
      exact hN i (hn.trans (Finset.mem_Ico.mp hi).1)
    · have heq : m = n := by omega
      subst n
      simpa [chapter06Distance] using hε

/-- A valuation-language version of “tends uniformly to infinity”. -/
def chapter06ValuationTendsToInfinity
    {Γ : Type*} [LinearOrder Γ] (w : K → Γ) (x : ℕ → K) : Prop :=
  ∀ M : Γ, ∃ N : ℕ, ∀ m n : ℕ,
    N ≤ m → N ≤ n → M < w (x m - x n)

/-- Compatibility of an absolute value and an additive valuation at their neighborhoods of zero. -/
def chapter06AbsoluteValueValuationCompatibility
    {Γ : Type*} [LinearOrder Γ] (v : AbsoluteValue K ℝ) (w : K → Γ) : Prop :=
  (∀ ε : ℝ, 0 < ε → ∃ M : Γ, ∀ z : K,
      M < w z → v z < ε) ∧
    (∀ M : Γ, ∃ ε : ℝ, 0 < ε ∧ ∀ z : K,
      v z < ε → M < w z)

/-- Cauchy convergence is equivalent to valuation differences tending to infinity. -/
theorem chapter06_cauchy_iff_valuation_tends_to_infinity
    {Γ : Type*} [LinearOrder Γ]
    (v : AbsoluteValue K ℝ) (w : K → Γ)
    (hcompat : chapter06AbsoluteValueValuationCompatibility v w) (x : ℕ → K) :
    chapter06CauchySeq v x ↔ chapter06ValuationTendsToInfinity w x := by
  constructor
  · intro hc M
    obtain ⟨ε, hε, hεw⟩ := hcompat.2 M
    obtain ⟨N, hN⟩ := hc ε hε
    refine ⟨N, ?_⟩
    intro m n hm hn
    exact hεw (x m - x n) (hN m n hm hn)
  · intro hw ε hε
    obtain ⟨M, hM⟩ := hcompat.1 ε hε
    obtain ⟨N, hN⟩ := hw M
    refine ⟨N, ?_⟩
    intro m n hm hn
    exact hM (x m - x n) (hN m n hm hn)

/-- A convergent sequence approaching a nonzero point eventually has constant absolute value. -/
theorem chapter06_eventual_absolute_value_eq_of_converges_to_nonzero
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {x : ℕ → K} {l : K} (hl : chapter06ConvergesTo v x l) (hl0 : l ≠ 0) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → v (x n) = v l := by
  obtain ⟨N, hN⟩ := hl (v l) (v.pos hl0)
  refine ⟨N, ?_⟩
  intro n hn
  exact chapter06_abs_value_locally_constant_at_nonzero v hv hl0 (hN n hn)

/-- The absolute value is locally constant on `Kˣ`; no discreteness is needed. -/
theorem chapter06_absolute_value_locally_constant_on_nonzero
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) :
    ∀ x : K, x ≠ 0 →
      ∃ U : Set K, @IsOpen K v.uniformSpace.toTopologicalSpace U ∧ x ∈ U ∧
        ∀ y ∈ U, v y = v x := by
  intro x hx
  let U := chapter06OpenBall v x (v x)
  refine ⟨U, chapter06_openBall_isOpen v x (v x), ?_, ?_⟩
  · change v (x - x) < v x
    simp [hx]
  · intro y hy
    exact chapter06_abs_value_locally_constant_at_nonzero v hv hx hy

end CauchySequences

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter06
