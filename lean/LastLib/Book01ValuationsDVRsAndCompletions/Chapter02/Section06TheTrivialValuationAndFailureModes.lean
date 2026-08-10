import LastLib.Book01ValuationsDVRsAndCompletions.Chapter02.Section05FromAdditiveToMultiplicativeSize

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

/-! # Book 1, Chapter 2, Section 2.6: The Trivial Valuation and Failure Modes
-/

/-! ## 2.6. Trivial valuations and a failure of the ordinary absolute value -/

def Chapter02TrivialAdditiveValuation {K : Type*} [Field K] :
    AddValuation K (WithTop ℤ) := by
  classical
  exact AddValuation.of (fun x : K => if x = 0 then ⊤ else 0)
    (by simp) (by simp)
    (by
      intro x y
      by_cases hx : x = 0
      · by_cases hy : y = 0 <;> simp [hx, hy]
      by_cases hy : y = 0
      · simp [hy]
      by_cases hxy : x + y = 0 <;> simp [hx, hy, hxy])
    (by
      intro x y
      by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy])

theorem chapter02_trivial_valuation_ring_is_the_whole_field
    {K : Type*} [Field K] :
    Chapter02ValuationRing (Chapter02TrivialAdditiveValuation :
      AddValuation K (WithTop ℤ)) = (⊤ : Subring K) := by
  ext x
  by_cases hx : x = 0 <;>
    simp [Chapter02ValuationRing, Chapter02TrivialAdditiveValuation, hx]

def Chapter02TrivialAbsoluteValue {K : Type*} [Field K] (x : K) : ℝ := by
  classical
  exact if x = 0 then 0 else 1

theorem chapter02_trivial_absolute_value_is_one_off_zero
    {K : Type*} [Field K] {x : K} (hx : x ≠ 0) :
    Chapter02TrivialAbsoluteValue x = 1 := by
  simp [Chapter02TrivialAbsoluteValue, hx]

def Chapter02TrivialDistance {K : Type*} [Field K] (x y : K) : ℝ := by
  classical
  exact if x = y then 0 else 1

theorem chapter02_trivial_distance_characterization
    {K : Type*} [Field K] (x y : K) :
    Chapter02TrivialDistance x y = 0 ↔ x = y := by
  simp [Chapter02TrivialDistance]

theorem chapter02_trivial_distance_of_distinct_points
    {K : Type*} [Field K] {x y : K} (hxy : x ≠ y) :
    Chapter02TrivialDistance x y = 1 := by
  simp [Chapter02TrivialDistance, hxy]

def Chapter02OrdinaryRationalAbsoluteValue (x : ℚ) : ℝ :=
  |(x : ℝ)|

theorem chapter02_ordinary_absolute_value_fails_ultrametricity :
    ¬ Chapter02IsUltrametricAbsoluteValue Chapter02OrdinaryRationalAbsoluteValue := by
  intro h
  have hh := h 1 1
  norm_num [Chapter02OrdinaryRationalAbsoluteValue] at hh

theorem chapter02_ordinary_absolute_value_one_plus_one :
    Chapter02OrdinaryRationalAbsoluteValue (1 + 1) = 2 ∧
      Chapter02OrdinaryRationalAbsoluteValue 1 = 1 := by
  norm_num [Chapter02OrdinaryRationalAbsoluteValue]

theorem chapter02_rational_completion_is_real_model :
    Nonempty (UniformSpace.Completion ℚ ≃ₜ ℝ) := by
  have hU := Rat.uniformSpace_eq
  have hB :
      CompareReals.Bourbaki.uniformSpace =
        @UniformSpace.Completion.uniformSpace ℚ
          (@AbsoluteValue.abs ℚ _).uniformSpace := by
    unfold CompareReals.Bourbaki.uniformSpace CompareReals.uniformSpace
    rfl
  have eAbs :
    @Homeomorph
        (@UniformSpace.Completion ℚ (@AbsoluteValue.abs ℚ _).uniformSpace) ℝ
        (@UniformSpace.Completion.uniformSpace ℚ
          (@AbsoluteValue.abs ℚ _).uniformSpace).toTopologicalSpace
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
    have e := CompareReals.compareEquiv.toHomeomorph
    have htop := congrArg
      (fun u : UniformSpace CompareReals.Bourbakiℝ => u.toTopologicalSpace) hB
    rw [htop] at e
    change @Homeomorph
      (@UniformSpace.Completion ℚ (@AbsoluteValue.abs ℚ _).uniformSpace) ℝ
      (@UniformSpace.Completion.uniformSpace ℚ
        (@AbsoluteValue.abs ℚ _).uniformSpace).toTopologicalSpace
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace at e
    exact e
  exact ⟨hU ▸ eAbs⟩

def Chapter02UltrametricDistance {K : Type*} [Ring K]
    (f : K → ℝ) (x y : K) : ℝ := f (x - y)

theorem chapter02_ultrametric_longest_side
    {K : Type*} [Ring K] (f : K → ℝ)
    (hf : Chapter02IsUltrametricAbsoluteValue f) (x y z : K) :
    Chapter02UltrametricDistance f x z ≤
      max (Chapter02UltrametricDistance f x y)
        (Chapter02UltrametricDistance f y z) := by
  simpa [Chapter02UltrametricDistance, sub_eq_add_neg, add_assoc, add_comm,
    add_left_comm] using hf (x - y) (y - z)

theorem chapter02_ultrametric_series_criterion
    {K : Type*} [NormedAddCommGroup K] [CompleteSpace K]
    (htri : ∀ x y : K, ‖x + y‖ ≤ max ‖x‖ ‖y‖) (u : ℕ → K)
    (hu : Filter.Tendsto (fun n => ‖u n‖) Filter.atTop (nhds 0)) :
    Summable u := by
  rw [summable_iff_vanishing_norm]
  intro ε hε
  have hev : ∀ᶠ n in Filter.atTop, ‖u n‖ < ε :=
    hu.eventually (Iio_mem_nhds hε)
  have hev' : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ‖u n‖ < ε := by
    simpa only [Filter.eventually_atTop] using hev
  rcases hev' with ⟨N, hN⟩
  refine ⟨Finset.range N, ?_⟩
  intro t hdis
  induction t using Finset.induction_on with
  | empty => simp [hε]
  | @insert a t ha ih =>
      rw [Finset.sum_insert ha]
      apply lt_of_le_of_lt (htri (u a) (∑ i ∈ t, u i))
      apply max_lt
      · apply hN
        by_contra hna
        have haN : a ∈ Finset.range N :=
          Finset.mem_range.mpr (Nat.lt_of_not_ge hna)
        exact Finset.disjoint_left.mp hdis (Finset.mem_insert_self a t) haN
      · apply ih
        exact Finset.disjoint_left.2 (by
          intro i hi hiN
          exact Finset.disjoint_left.mp hdis
            (Finset.mem_insert_of_mem hi) hiN)

end
end LastLib.Book01ValuationsDVRsAndCompletions.Chapter02
