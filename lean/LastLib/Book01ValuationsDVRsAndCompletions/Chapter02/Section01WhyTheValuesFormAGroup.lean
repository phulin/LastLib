import Mathlib.Algebra.Order.Ring.Archimedean
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Group.Subgroup.Order
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Real.Embedding
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.Section05MeasurementsThatAreNotDiscrete

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter02

/-!
# Chapter 2: Valuations

This file is a statement-generation pass for Chapter 2 of *Valuations, DVRs,
and Completions*.  The declarations are deliberately self-contained: they
use Mathlib's `AddValuation` where it has the required interface and introduce
chapter-local names for the constructions that are specific to the exposition.
-/

noncomputable section

/-! # Book 1, Chapter 2, Section 2.1: Why the Values Form a Group
-/

/-! ## 2.1. Why values form a group -/

/- The top element is absorbing for addition in the extended group. -/
theorem chapter02_top_add_value
    {Γ : Type*} [Add Γ] (γ : Γ) :
    (γ : WithTop Γ) + ⊤ = ⊤ := by
  simp

theorem chapter02_add_value_top
    {Γ : Type*} [Add Γ] (γ : Γ) :
    (⊤ : WithTop Γ) + γ = ⊤ := by
  simp

/-- The ordered-group formulation of the rank-one/Archimedean condition. -/
theorem chapter02_finite_values_are_translation_ordered
    {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    (α β γ : Γ) (h : α ≤ β) : α + γ ≤ β + γ := by
  exact add_le_add_left h γ

theorem chapter02_every_finite_value_is_below_infinity
    {Γ : Type*} [LinearOrder Γ] (γ : Γ) : (γ : WithTop Γ) < ⊤ := by
  exact WithTop.coe_lt_top γ

theorem chapter02_archimedean_value_group_iff
    {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] :
    Chapter01.IsChapterRankOneOrderedGroup Γ ↔ Archimedean Γ := by
  constructor
  · intro h
    refine ⟨fun x {y} hy => ?_⟩
    by_cases hx : x ≤ 0
    · exact ⟨0, by simpa using hx⟩
    · obtain ⟨n, hn, hxy⟩ := h x y (lt_of_not_ge hx) hy
      exact ⟨n, hxy⟩
  · intro h α β hα hβ
    obtain ⟨n, hn⟩ := h.arch α hβ
    refine ⟨n, ?_, hn⟩
    by_contra hnot
    have hn0 : n = 0 := by omega
    subst n
    exact (not_le_of_gt hα) (by simpa using hn)

theorem chapter02_archimedean_values_embed_in_reals
    {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    (hΓ : Chapter01.IsChapterRankOneOrderedGroup Γ) :
    ∃ f : Γ →+o ℝ, Function.Injective f := by
  let _ : Archimedean Γ := (chapter02_archimedean_value_group_iff).1 hΓ
  exact Archimedean.exists_orderAddMonoidHom_real_injective Γ

/-- A convenient name for the lexicographically ordered copy of `ℤ × ℤ`. -/
abbrev Chapter02LexicographicIntegers := ℤ ×ₗ ℤ

instance {α β : Type*} [AddCommMonoid α] [LinearOrder α] [IsOrderedAddMonoid α]
    [AddLeftStrictMono α]
    [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β] :
    IsOrderedAddMonoid (α ×ₗ β) where
  add_le_add_left a b hab c := by
    rw [Prod.Lex.le_iff] at hab ⊢
    rcases hab with hab | ⟨hfirst, hsecond⟩
    · apply Or.inl
      change (ofLex a).1 + (ofLex c).1 < (ofLex b).1 + (ofLex c).1
      simpa [add_comm] using add_lt_add_right hab (ofLex c).1
    · apply Or.inr
      constructor
      · change (ofLex a).1 + (ofLex c).1 = (ofLex b).1 + (ofLex c).1
        exact congrArg (fun x => x + (ofLex c).1) hfirst
      · change (ofLex a).2 + (ofLex c).2 ≤ (ofLex b).2 + (ofLex c).2
        simpa [add_comm] using add_le_add_right hsecond (ofLex c).2

theorem chapter02_lexicographic_order_formula (a b c d : ℤ) :
    toLex (a, b) < toLex (c, d) ↔
      a < c ∨ (a = c ∧ b < d) := by
  exact Prod.Lex.toLex_lt_toLex

theorem chapter02_lex_second_coordinate_refines_first (n : ℤ) :
    toLex ((0 : ℤ), 1) < toLex (1, n) := by
  exact (chapter02_lexicographic_order_formula 0 1 1 n).2 (Or.inl (by omega))

theorem chapter02_lexicographic_integers_nonarchimedean :
    ¬ Chapter01.IsChapterRankOneOrderedGroup Chapter02LexicographicIntegers := by
  intro h
  obtain ⟨n, hn, hle⟩ := h (toLex ((1 : ℤ), 0)) (toLex ((0 : ℤ), 1))
    (by change toLex ((0 : ℤ), 0) < toLex ((1 : ℤ), 0)
        rw [Prod.Lex.toLex_lt_toLex]; omega)
    (by change toLex ((0 : ℤ), 0) < toLex ((0 : ℤ), 1)
        rw [Prod.Lex.toLex_lt_toLex]; omega)
  have hsmul : n • toLex ((0 : ℤ), 1) = toLex ((0 : ℤ), (n : ℤ)) := by
    change toLex (n • ((0 : ℤ), (1 : ℤ))) =
      toLex ((0 : ℤ), (n : ℤ))
    simp
  have hle' : toLex ((1 : ℤ), 0) ≤ toLex ((0 : ℤ), (n : ℤ)) := by
    rw [← hsmul]
    exact hle
  have hlt : toLex ((0 : ℤ), (n : ℤ)) < toLex (1, 0) :=
    (chapter02_lexicographic_order_formula 0 n 1 0).2 (Or.inl (by omega))
  exact (not_le_of_gt hlt) hle'

theorem chapter02_lexicographic_integers_have_coarse_and_refining_coordinates :
    ∃ q : Chapter02LexicographicIntegers →+o ℤ,
      (∀ a b : ℤ, q (toLex (a, b)) = a) ∧
      (∀ n : ℤ, q (toLex (0, n)) = 0) := by
  let q : Chapter02LexicographicIntegers →+o ℤ :=
    { toFun := fun p => (ofLex p).1
      map_zero' := by simp
      map_add' := by intro p r; simp
      monotone' := Prod.Lex.monotone_fst_ofLex }
  refine ⟨q, ?_, ?_⟩
  · intro a b
    rfl
  · intro n
    rfl

/-- The subgroup `ℤ + √2 ℤ` of the real line. -/
def Chapter02SqrtTwoIntegerSubgroup : AddSubgroup ℝ :=
  AddSubgroup.closure ({(1 : ℝ), Real.sqrt 2} : Set ℝ)

theorem chapter02_sqrt_two_integer_subgroup_is_archimedean :
    Chapter01.IsChapterRankOneOrderedGroup (↥Chapter02SqrtTwoIntegerSubgroup) := by
  intro α β hα hβ
  obtain ⟨n, hn⟩ := Archimedean.arch (α : ℝ) (show 0 < (β : ℝ) from hβ)
  refine ⟨n, ?_, ?_⟩
  · by_contra hnot
    have hn0 : n = 0 := by omega
    subst n
    simpa using (not_le_of_gt (show 0 < (α : ℝ) from hα) hn)
  · exact hn

theorem chapter02_rank_one_need_not_be_discrete :
    Chapter01.IsChapterRankOneOrderedGroup ℚ ∧
      DenselyOrdered ℚ ∧
      ¬ ∃ d : ℚ, 0 < d ∧ ∀ x : ℚ, 0 < x → d ≤ x := by
  refine ⟨?_, inferInstance, ?_⟩
  · exact (chapter02_archimedean_value_group_iff).2 inferInstance
  · rintro ⟨d, hd, hleast⟩
    have hhalf : 0 < d / 2 := by linarith
    have := hleast (d / 2) hhalf
    linarith

theorem chapter02_lexicographic_group_has_no_real_order_embedding :
    ¬ ∃ f : Chapter02LexicographicIntegers →+o ℝ, Function.Injective f := by
  rintro ⟨f, hf⟩
  have hmono : Monotone f := f.monotone'
  have hsmall : 0 ≤ f (toLex ((0 : ℤ), 1)) := by
    have hzero : (0 : Chapter02LexicographicIntegers) ≤
        toLex ((0 : ℤ), 1) := by
      change toLex ((0 : ℤ), 0) ≤ toLex ((0 : ℤ), 1)
      rw [Prod.Lex.toLex_le_toLex]
      omega
    simpa using hmono hzero
  by_cases hsmall0 : f (toLex ((0 : ℤ), 1)) = 0
  · have heq : f (toLex ((0 : ℤ), 1)) = f (toLex ((0 : ℤ), 0)) := by
      calc
        f (toLex ((0 : ℤ), 1)) = 0 := hsmall0
        _ = f (toLex ((0 : ℤ), 0)) := by
          change 0 = f 0
          exact (f.map_zero).symm
    have hbad : toLex ((0 : ℤ), (1 : ℤ)) =
        toLex ((0 : ℤ), (0 : ℤ)) := hf heq
    have hne : toLex ((0 : ℤ), (1 : ℤ)) ≠
        toLex ((0 : ℤ), (0 : ℤ)) := by
      intro h
      have := congrArg (fun p : Chapter02LexicographicIntegers =>
        (ofLex p).2) h
      norm_num at this
    exact hne hbad
  · have hsmallpos : 0 < f (toLex ((0 : ℤ), 1)) :=
      lt_of_le_of_ne hsmall (Ne.symm hsmall0)
    obtain ⟨n, hn⟩ := Archimedean.arch (f (toLex ((1 : ℤ), 0))) hsmallpos
    have hltlex : toLex ((0 : ℤ), (n : ℤ)) < toLex ((1 : ℤ), 0) :=
      (chapter02_lexicographic_order_formula 0 n 1 0).2 (Or.inl (by omega))
    have hlt : f (toLex ((0 : ℤ), (n : ℤ))) < f (toLex ((1 : ℤ), 0)) :=
      (hmono.strictMono_of_injective hf) hltlex
    have hsmul : n • toLex ((0 : ℤ), 1) = toLex ((0 : ℤ), (n : ℤ)) := by
      change toLex (n • ((0 : ℤ), (1 : ℤ))) =
        toLex ((0 : ℤ), (n : ℤ))
      simp
    have hmap : f (toLex ((0 : ℤ), (n : ℤ))) =
        n • f (toLex ((0 : ℤ), 1)) := by
      rw [← hsmul]
      exact f.map_nsmul _ _
    rw [hmap] at hlt
    exact (not_lt_of_ge hn) hlt

end
end LastLib.Book01ValuationsDVRsAndCompletions.Chapter02
