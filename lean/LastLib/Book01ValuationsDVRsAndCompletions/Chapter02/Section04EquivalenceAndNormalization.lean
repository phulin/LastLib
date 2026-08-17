import LastLib.Book01ValuationsDVRsAndCompletions.Chapter02.Section01WhyTheValuesFormAGroup
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter02.Section02AdditiveValuations
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.Section05MeasurementsThatAreNotDiscrete
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter02

/-!
# Chapter 2: Valuations

This file is a statement-generation pass for Chapter 2 of *Valuations, DVRs,
and Completions*.  The declarations are deliberately self-contained: they
use Mathlib's `AddValuation` where it has the required interface and introduce
chapter-local names for the constructions that are specific to the exposition.
-/

noncomputable section

/-! # Book 1, Chapter 2, Section 2.4: Equivalence and Normalization
-/

/-! ## 2.4. Equivalence and normalization -/

theorem chapter02_equivalent_iff_same_comparisons
    {K Γ Δ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Δ] [LinearOrder Δ] [IsOrderedAddMonoid Δ]
    (v : AddValuation K (WithTop Γ)) (w : AddValuation K (WithTop Δ)) :
    AddValuation.IsEquiv v w ↔
      ∀ x y : K, v x ≤ v y ↔ w x ≤ w y := by
  change (∀ x y : K, v y ≤ v x ↔ w y ≤ w x) ↔
    ∀ x y : K, v x ≤ v y ↔ w x ≤ w y
  constructor <;> intro h x y
  · exact h y x
  · exact h y x

def Chapter02OrderRelabelValue
    {Γ Δ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Δ] [LinearOrder Δ] [IsOrderedAddMonoid Δ]
    (e : Γ ≃+o Δ) (γ : WithTop Γ) : WithTop Δ :=
  if hγ : γ = ⊤ then ⊤ else (e (γ.untop hγ) : WithTop Δ)

def Chapter02EquivalentByOrderedRelabeling
    {K Γ Δ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Δ] [LinearOrder Δ] [IsOrderedAddMonoid Δ]
    (v : AddValuation K (WithTop Γ))
    (w : AddValuation K (WithTop Δ)) : Prop :=
  ∃ e : Γ ≃+o Δ, ∀ x : K, w x = Chapter02OrderRelabelValue e (v x)

theorem chapter02_order_relabeling_implies_equivalence
    {K Γ Δ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Δ] [LinearOrder Δ] [IsOrderedAddMonoid Δ]
    {v : AddValuation K (WithTop Γ)} {w : AddValuation K (WithTop Δ)}
    (h : Chapter02EquivalentByOrderedRelabeling v w) :
    AddValuation.IsEquiv v w := by
  rcases h with ⟨e, he⟩
  apply (chapter02_equivalent_iff_same_comparisons v w).2
  intro x y
  rw [he x, he y]
  by_cases hx : v x = ⊤ <;> by_cases hy : v y = ⊤
  · simp [Chapter02OrderRelabelValue, hx, hy]
  · simp [Chapter02OrderRelabelValue, hx, hy]
  · simp [Chapter02OrderRelabelValue, hx, hy]
  · simp only [Chapter02OrderRelabelValue, dif_neg hx, dif_neg hy]
    constructor
    · intro hxy
      apply WithTop.coe_le_coe.mpr
      apply (map_le_map_iff e).2
      exact WithTop.coe_le_coe.mp (by
        simpa only [WithTop.coe_untop] using hxy)
    · intro hxy
      have hfinite : (v x).untop hx ≤ (v y).untop hy :=
        (map_le_map_iff e).1 (WithTop.coe_le_coe.mp hxy)
      simpa only [WithTop.coe_untop] using (WithTop.coe_le_coe.mpr hfinite)

theorem chapter02_equivalence_and_surjectivity_give_order_relabeling
    {K Γ Δ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Δ] [LinearOrder Δ] [IsOrderedAddMonoid Δ]
    {v : AddValuation K (WithTop Γ)} {w : AddValuation K (WithTop Δ)}
    (hv : Chapter02SurjectiveValuation v)
    (hw : Chapter02SurjectiveValuation w)
    (he : AddValuation.IsEquiv v w) :
    Chapter02EquivalentByOrderedRelabeling v w := by
  classical
  have hcomp (a b : K) : v a ≤ v b ↔ w a ≤ w b :=
    (chapter02_equivalent_iff_same_comparisons v w).1 he a b
  let xv : Γ → K := fun γ => Classical.choose (hv γ)
  have hxv : ∀ γ : Γ, xv γ ≠ 0 ∧ v (xv γ) = (γ : WithTop Γ) := by
    intro γ
    exact Classical.choose_spec (hv γ)
  let yw : Δ → K := fun δ => Classical.choose (hw δ)
  have hyw : ∀ δ : Δ, yw δ ≠ 0 ∧ w (yw δ) = (δ : WithTop Δ) := by
    intro δ
    exact Classical.choose_spec (hw δ)
  have heq {a b : K} (h : v a = v b) : w a = w b := by
    apply le_antisymm
    · exact (hcomp a b).1 (by rw [h])
    · exact (hcomp b a).1 (by rw [h])
  have heqv {a b : K} (h : w a = w b) : v a = v b := by
    apply le_antisymm
    · exact (hcomp a b).2 (by rw [h])
    · exact (hcomp b a).2 (by rw [h])
  let e : Γ ≃+o Δ :=
    { toFun := fun γ =>
        (w (xv γ)).untop ((AddValuation.ne_top_iff w).2 (hxv γ).1)
      invFun := fun δ =>
        (v (yw δ)).untop ((AddValuation.ne_top_iff v).2 (hyw δ).1)
      left_inv := by
        intro γ
        apply WithTop.coe_injective
        have hval : v (yw ((w (xv γ)).untop
            ((AddValuation.ne_top_iff w).2 (hxv γ).1))) = v (xv γ) := by
          apply heqv
          calc
            w (yw ((w (xv γ)).untop _)) =
                ((w (xv γ)).untop _ : WithTop Δ) := (hyw _).2
            _ = w (xv γ) := WithTop.coe_untop _ _
        simpa only [WithTop.coe_untop, (hxv γ).2] using hval
      right_inv := by
        intro δ
        apply WithTop.coe_injective
        have hval : w (xv ((v (yw δ)).untop
            ((AddValuation.ne_top_iff v).2 (hyw δ).1))) = w (yw δ) := by
          apply heq
          calc
            v (xv ((v (yw δ)).untop _)) =
                ((v (yw δ)).untop _ : WithTop Γ) := (hxv _).2
            _ = v (yw δ) := WithTop.coe_untop _ _
        simpa only [WithTop.coe_untop, (hyw δ).2] using hval
      map_add' := by
        intro γ γ'
        apply WithTop.coe_injective
        have hval : w (xv (γ + γ')) =
            w (xv γ) + w (xv γ') := by
          rw [← w.map_mul]
          apply heq
          rw [v.map_mul, (hxv γ).2, (hxv γ').2, (hxv (γ + γ')).2]
          simp
        simpa only [WithTop.coe_untop, WithTop.coe_add] using hval
      map_le_map_iff' := by
        intro γ γ'
        constructor
        · intro hγ
          apply WithTop.coe_le_coe.mp
          have hvle : v (xv γ) ≤ v (xv γ') :=
            (hcomp (xv γ) (xv γ')).2 (by
              simpa only [WithTop.coe_untop] using
                (WithTop.coe_le_coe.mpr hγ))
          simpa only [(hxv γ).2, (hxv γ').2] using hvle
        · intro hγ
          apply WithTop.coe_le_coe.mp
          have hwle : w (xv γ) ≤ w (xv γ') :=
            (hcomp (xv γ) (xv γ')).1 (by
              simpa only [(hxv γ).2, (hxv γ').2] using
                (WithTop.coe_le_coe.mpr hγ))
          simpa only [WithTop.coe_untop] using hwle }
  refine ⟨e, ?_⟩
  intro x
  by_cases hx : x = 0
  · simp [hx, Chapter02OrderRelabelValue]
  have hvx : v x ≠ (⊤ : WithTop Γ) := (AddValuation.ne_top_iff v).2 hx
  have hval : w x = w (xv ((v x).untop hvx)) := by
    apply heq
    calc
      v x = ((v x).untop hvx : WithTop Γ) := (WithTop.coe_untop _ _).symm
      _ = v (xv ((v x).untop hvx)) := ((hxv _).2).symm
  simpa [Chapter02OrderRelabelValue, hvx, e, WithTop.coe_untop] using hval

theorem chapter02_discrete_value_group_has_unique_smallest_positive
    {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    (hΓ : Chapter01.IsChapterDiscreteOrderedGroup Γ) :
    ∃! π : Γ, 0 < π ∧ ∀ γ : Γ, 0 < γ → π ≤ γ := by
  rcases hΓ with ⟨π, hπ, hleast⟩
  refine ⟨π, ⟨hπ, hleast⟩, ?_⟩
  intro π' hπ'
  exact le_antisymm (hπ'.2 π hπ) (hleast π' hπ'.1)

theorem chapter02_discrete_value_group_equiv_int
    {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    (hΓ : Chapter01.IsChapterDiscreteOrderedGroup Γ)
    (hRank : Chapter01.IsChapterRankOneOrderedGroup Γ) :
    Nonempty (Γ ≃+o ℤ) := by
  sorry

noncomputable def Chapter02NormalizedValuation
    {K Γ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    (e : Γ ≃+o ℤ) (v : AddValuation K (WithTop Γ)) :
    AddValuation K (WithTop ℤ) := by
  exact v.map (AddMonoidHom.withTopMap (e : Γ →+ ℤ)) (by simp)
    (OrderHomClass.monotone e).withTop_map

theorem chapter02_normalized_valuation_uses_unit_step
    {K Γ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    (e : Γ ≃+o ℤ) (v : AddValuation K (WithTop Γ))
    {x : K} {π : Γ}
    (hπ : 0 < π) (hleast : ∀ γ : Γ, 0 < γ → π ≤ γ)
    (hv : v x = (π : WithTop Γ)) :
    Chapter02NormalizedValuation e v x = (1 : WithTop ℤ) := by
  have heπ : e π = 1 := by
    have hpos : 0 < e π := by
      rw [← e.map_zero]
      exact (map_lt_map_iff e).2 hπ
    have hle : (1 : ℤ) ≤ e π := by omega
    have hnot : e π ≤ 1 := by
      by_contra hnot
      have h1pos : 0 < e.symm 1 := by
        rw [← e.symm.map_zero]
        exact (map_lt_map_iff e.symm).2 (by omega)
      have hlt : e.symm 1 < π := by
        apply (map_lt_map_iff e).1
        have h1lt : (1 : ℤ) < e π := lt_of_not_ge hnot
        simpa using h1lt
      exact (not_lt_of_ge (hleast (e.symm 1) h1pos)) hlt
    exact le_antisymm hnot hle
  change (AddMonoidHom.withTopMap (e : Γ →+ ℤ)) (v x) =
    (1 : WithTop ℤ)
  rw [hv]
  change (e π : WithTop ℤ) = (1 : WithTop ℤ)
  rw [heπ]
  simp

noncomputable def Chapter02TwiceValuation
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : AddValuation K (WithTop ℤ) :=
  AddValuation.of (fun x => 2 • v x)
    (by rw [v.map_zero]; change 2 • (⊤ : WithTop ℤ) = ⊤; rfl)
    (by simp)
    (by
      intro x y
      have h := nsmul_le_nsmul_right (v.map_add x y) 2
      rw [smul_min_of_nonneg (by norm_num : (0 : ℕ) ≤ 2)] at h
      exact h)
    (by
      intro x y
      simp [v.map_mul])

theorem chapter02_twice_valuation_formula
    {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ)) (x : K) :
    Chapter02TwiceValuation v x = 2 • v x := by
  rfl

def Chapter02ValuationRing
    {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ]
    (v : AddValuation K (WithTop Γ)) : ValuationSubring K :=
  v.toValuation.valuationSubring

theorem chapter02_equivalent_scalings_have_same_valuation_ring
    {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ)) :
    Chapter02ValuationRing (Chapter02TwiceValuation v) =
      Chapter02ValuationRing v := by
  ext x
  change (0 ≤ 2 • v x) ↔ 0 ≤ v x
  cases h : v x with
  | top =>
      have htop : (2 : ℕ) • (⊤ : WithTop ℤ) = ⊤ := by rfl
      rw [htop]
  | coe z =>
      change (((0 : ℤ) : WithTop ℤ) ≤ ((2 * z : ℤ) : WithTop ℤ)) ↔
        (((0 : ℤ) : WithTop ℤ) ≤ ((z : ℤ) : WithTop ℤ))
      rw [WithTop.coe_le_coe, WithTop.coe_le_coe]
      constructor
      · intro hz
        nlinarith
      · intro hz
        nlinarith

theorem chapter02_ramification_labels_depend_on_normalization
    {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ))
    {x : K} (hx : v x = (1 : WithTop ℤ)) :
    Chapter02TwiceValuation v x = (2 : WithTop ℤ) ∧
      Chapter02TwiceValuation v x ≠ v x := by
  constructor
  · simp [Chapter02TwiceValuation, hx]
  · simp [Chapter02TwiceValuation, hx]

def Chapter02ConvexAddSubgroup
    {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    (H : AddSubgroup Γ) : Prop :=
  ∀ ⦃a b c : Γ⦄, a ≤ b → b ≤ c → a ∈ H → c ∈ H → b ∈ H

def Chapter02ConvexQuotientInterface
    {Γ Λ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (H : AddSubgroup Γ) (q : Γ →+o Λ) : Prop :=
  Chapter02ConvexAddSubgroup H ∧
    Function.Surjective q ∧
    (∀ γ : Γ, q γ = 0 ↔ γ ∈ H) ∧
    (∀ a b : Γ, q a ≤ q b ↔
      ∃ h : H, a ≤ b + (h : Γ)) ∧
    ∀ {Ω : Type*} [AddCommGroup Ω] [LinearOrder Ω]
      [IsOrderedAddMonoid Ω] (f : Γ →+o Ω),
      (∀ h : Γ, h ∈ H → f h = 0) →
        ∃! g : Λ →+o Ω, f = g.comp q

def Chapter02CoarsenedValuation
    {K Γ Λ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (q : Γ →+o Λ) (v : AddValuation K (WithTop Γ)) :
    AddValuation K (WithTop Λ) := by
  exact v.map (AddMonoidHom.withTopMap (q : Γ →+ Λ)) (by simp)
    (OrderHomClass.monotone q).withTop_map

theorem chapter02_convex_subgroup_gives_ordered_quotient
    {Γ Λ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (H : AddSubgroup Γ) (hH : Chapter02ConvexAddSubgroup H)
    (q : Γ →+o Λ) (hq : Function.Surjective q)
    (hker : ∀ γ : Γ, q γ = 0 ↔ γ ∈ H)
    (horder : ∀ a b : Γ, q a ≤ q b ↔
      ∃ h : H, a ≤ b + (h : Γ)) :
    Chapter02ConvexQuotientInterface H q := by
  refine ⟨hH, hq, hker, horder, ?_⟩
  intro Ω _ _ _ f hfH
  have hwell : ∀ {a b : Γ}, q a = q b → f a = f b := by
    intro a b hab
    have hqsub : q (a - b) = 0 := by simp [map_sub, hab]
    have hmem : a - b ∈ H := (hker (a - b)).1 hqsub
    have hf0 := hfH (a - b) hmem
    have : f a - f b = 0 := by simpa [map_sub] using hf0
    exact sub_eq_zero.mp this
  let g : Λ →+o Ω :=
    { toFun := fun z => f (Classical.choose (hq z))
      map_zero' := by
        have hz : q (Classical.choose (hq 0)) = q 0 := by simp [Classical.choose_spec (hq 0)]
        simpa using (hwell hz).trans f.map_zero
      map_add' := by
        intro z t
        have hz : q (Classical.choose (hq (z + t))) =
            q (Classical.choose (hq z) + Classical.choose (hq t)) := by
          simp [Classical.choose_spec (hq (z + t)),
            Classical.choose_spec (hq z), Classical.choose_spec (hq t)]
        have hzg := hwell hz
        simpa [map_add] using hzg
      monotone' := by
        intro z t hzt
        have hqt : q (Classical.choose (hq z)) ≤ q (Classical.choose (hq t)) := by
          simpa [Classical.choose_spec (hq z), Classical.choose_spec (hq t)] using hzt
        rcases (horder (Classical.choose (hq z)) (Classical.choose (hq t))).1 hqt with
          ⟨h, hab⟩
        calc
          f (Classical.choose (hq z)) ≤
              f (Classical.choose (hq t) + (h : Γ)) :=
                (OrderHomClass.monotone f) hab
          _ = f (Classical.choose (hq t)) := by
            simp only [map_add, hfH (h : Γ) h.property, add_zero] }
  have hfactor : f = g.comp q := by
    ext a
    have hz : q (Classical.choose (hq (q a))) = q a :=
      Classical.choose_spec (hq (q a))
    change f a = f (Classical.choose (hq (q a)))
    exact (hwell hz).symm
  refine ⟨g, hfactor, ?_⟩
  intro g' hg'
  ext z
  rcases hq z with ⟨a, rfl⟩
  have h₁ := congrArg (fun F => F a) hg'
  have h₂ := congrArg (fun F => F a) hfactor
  exact h₁.symm.trans h₂

theorem chapter02_coarsening_is_composition_with_quotient
    {K Γ Λ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (q : Γ →+o Λ)
    (v : AddValuation K (WithTop Γ)) :
    ∀ x : K, Chapter02CoarsenedValuation q v x =
      (if h : v x = ⊤ then ⊤ else (q ((v x).untop h) : WithTop Λ)) := by
  intro x
  by_cases hx : v x = ⊤
  · have hx0 : x = 0 := (AddValuation.top_iff v).1 hx
    simp [Chapter02CoarsenedValuation, hx0]
  · simp only [Chapter02CoarsenedValuation, dif_neg hx]
    change (AddMonoidHom.withTopMap (q : Γ →+ Λ)) (v x) =
      (q ((v x).untop hx) : WithTop Λ)
    have hvx : v x = ((v x).untop hx : WithTop Γ) :=
      (WithTop.coe_untop (v x) hx).symm
    calc
      (AddMonoidHom.withTopMap (q : Γ →+ Λ)) (v x) =
          (AddMonoidHom.withTopMap (q : Γ →+ Λ))
            ((v x).untop hx : WithTop Γ) := congrArg _ hvx
      _ = (q ((v x).untop hx) : WithTop Λ) := rfl

def Chapter02LexSecondCoordinateSubgroup :
    AddSubgroup Chapter02LexicographicIntegers :=
  { carrier := {p | (ofLex p).1 = 0}
    zero_mem' := by simp
    add_mem' := by
      intro p q hp hq
      simp_all
    neg_mem' := by
      intro p hp
      simp_all }

def Chapter02LexFirstCoordinate :
    Chapter02LexicographicIntegers →+o ℤ :=
  { toFun := fun p => (ofLex p).1
    map_zero' := by simp
    map_add' := by
      intro p q
      simp
    monotone' := Prod.Lex.monotone_fst_ofLex }

theorem chapter02_lex_second_coordinate_is_convex :
    Chapter02ConvexAddSubgroup Chapter02LexSecondCoordinateSubgroup := by
  intro a b c hab hbc ha hc
  change (ofLex b).1 = 0
  have hab' : (ofLex a).1 ≤ (ofLex b).1 :=
    Prod.Lex.monotone_fst a b hab
  have hbc' : (ofLex b).1 ≤ (ofLex c).1 :=
    Prod.Lex.monotone_fst b c hbc
  have ha' : (ofLex a).1 = 0 := ha
  have hc' : (ofLex c).1 = 0 := hc
  omega

theorem chapter02_lex_quotient_remembers_first_coordinate :
    Function.Surjective Chapter02LexFirstCoordinate ∧
      ∀ p : Chapter02LexicographicIntegers,
        Chapter02LexFirstCoordinate p = 0 ↔
          p ∈ Chapter02LexSecondCoordinateSubgroup := by
  constructor
  · intro z
    exact ⟨toLex (z, (0 : ℤ)), rfl⟩
  · intro p
    rfl

theorem chapter02_lex_quotient_is_an_ordered_convex_quotient :
    Chapter02ConvexQuotientInterface Chapter02LexSecondCoordinateSubgroup
      Chapter02LexFirstCoordinate := by
  apply chapter02_convex_subgroup_gives_ordered_quotient
    Chapter02LexSecondCoordinateSubgroup
    chapter02_lex_second_coordinate_is_convex
    Chapter02LexFirstCoordinate
    (chapter02_lex_quotient_remembers_first_coordinate).1
    (chapter02_lex_quotient_remembers_first_coordinate).2
  intro a b
  change (ofLex a).1 ≤ (ofLex b).1 ↔
    ∃ h : Chapter02LexSecondCoordinateSubgroup,
      a ≤ b + (h : Chapter02LexicographicIntegers)
  constructor
  · intro hab
    rcases hab.lt_or_eq with hablt | habeq
    · refine ⟨0, ?_⟩
      simpa using (Prod.Lex.toLex_le_toLex.mpr (Or.inl hablt))
    · let h : Chapter02LexSecondCoordinateSubgroup :=
        ⟨toLex ((0 : ℤ), (ofLex a).2 - (ofLex b).2), by
          change (ofLex (toLex ((0 : ℤ), (ofLex a).2 - (ofLex b).2))).1 = 0
          simp⟩
      refine ⟨h, ?_⟩
      dsimp [h]
      change toLex ((ofLex a).1, (ofLex a).2) ≤
        toLex ((ofLex b).1 + 0,
          (ofLex b).2 + ((ofLex a).2 - (ofLex b).2))
      rw [Prod.Lex.toLex_le_toLex]
      exact Or.inr ⟨by omega, by omega⟩
  · rintro ⟨h, hab⟩
    have hle := Prod.Lex.monotone_fst a (b + (h : Chapter02LexicographicIntegers)) hab
    have hh : (ofLex (h : Chapter02LexicographicIntegers)).1 = 0 := by
      exact h.property
    simpa [hh] using hle

theorem chapter02_discrete_rank_one_has_no_proper_coarsening
    {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    (hΓ : Chapter01.IsChapterDiscreteOrderedGroup Γ)
    (hRank : Chapter01.IsChapterRankOneOrderedGroup Γ) (H : AddSubgroup Γ)
    (hH : Chapter02ConvexAddSubgroup H) : H = ⊥ ∨ H = ⊤ := by
  rcases chapter02_discrete_value_group_equiv_int hΓ hRank with ⟨e⟩
  by_cases hp : ∃ h : Γ, h ∈ H ∧ 0 < h
  · right
    rcases hp with ⟨h, hh, hpos⟩
    let p : Γ := e.symm 1
    have hppos : 0 < p := by
      dsimp [p]
      rw [← e.symm.map_zero]
      exact (map_lt_map_iff e.symm).2 (by omega)
    have hple : p ≤ h := by
      apply (map_le_map_iff e).1
      have hep : e p = 1 := by simp [p]
      have : 0 < e h := by
        rw [← e.map_zero]
        exact (map_lt_map_iff e).2 hpos
      rw [hep]
      omega
    have hpH : p ∈ H := hH (le_of_lt hppos) hple H.zero_mem hh
    apply le_antisymm le_top
    intro γ _
    have hγ : (e γ) • p = γ := by
      apply e.injective
      simp [p]
    rw [← hγ]
    exact H.zsmul_mem hpH (e γ)
  · left
    apply le_antisymm ?_ bot_le
    intro h hh
    have hnotpos : ¬ 0 < h := by
      intro hpos
      exact hp ⟨h, hh, hpos⟩
    have hnotneg : ¬ h < 0 := by
      intro hneg
      apply hp
      refine ⟨-h, H.neg_mem hh, ?_⟩
      exact neg_pos.mpr hneg
    have : h = 0 := le_antisymm (le_of_not_gt hnotpos) (le_of_not_gt hnotneg)
    simp [this]

end
end LastLib.Book01ValuationsDVRsAndCompletions.Chapter02
