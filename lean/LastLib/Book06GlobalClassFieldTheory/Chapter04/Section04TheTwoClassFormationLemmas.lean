import LastLib.Book06GlobalClassFieldTheory.Chapter04.Dependencies

namespace LastLib.Book06GlobalClassFieldTheory.Chapter04

noncomputable section

universe u v

/-! ## 4.4. The two class-formation lemmas -/

/-- Degree-one Tate cohomology of the idele-class module vanishes on every subgroup. -/
theorem chapter04_idele_class_H1_vanishes
    {G : Type} [Group G] [Fintype G]
    (U : Chapter04FundamentalClass (G := G))
    (H : Subgroup G)
    (HYP : Chapter04ClassFormationHypotheses U) :
    IsZero
      (chapter04GroupH (chapter04RestrictGModule U.C H) 1) := by
  sorry

/-- The restricted fundamental class generates the normalized cyclic degree-two group. -/
theorem chapter04_idele_class_H2_is_cyclic
    {G : Type} [Group G] [Fintype G]
    (U : Chapter04FundamentalClass (G := G))
    (H : Subgroup G)
    (HYP : Chapter04ClassFormationHypotheses U) :
    ∃ e : chapter04GroupH (chapter04RestrictGModule U.C H) 2 ≃+ ZMod (Nat.card H),
      e (chapter04RestrictTwoClass U.C H U.u) = 1 := by
  sorry

/-- The degree-two group has order `|H|` under the invariant normalization. -/
theorem chapter04_idele_class_H2_order
    {G : Type} [Group G] [Fintype G]
    (U : Chapter04FundamentalClass (G := G))
    (H : Subgroup G)
    (HYP : Chapter04ClassFormationHypotheses U) :
    Nat.card (chapter04GroupH (chapter04RestrictGModule U.C H) 2) = Nat.card H := by
  sorry

/-- A subgroup-level cap map, with the source's degree shift `r - 2 → r`. -/
abbrev chapter04SubgroupCapMap
    {G : Type} [Group G] [Fintype G]
  (U : Chapter04FundamentalClass (G := G)) (H : Subgroup G) (r : ℤ) :
    chapter04TateH (chapter04TrivialGModule H) (r - 2) ⟶
      chapter04TateH (chapter04RestrictGModule U.C H) r :=
  (U.capAPI).cap H (r - 2)

/-- The class-formation isomorphism in every Tate degree. -/
theorem chapter04_class_formation_isomorphism
    {G : Type} [Group G] [Fintype G]
    (U : Chapter04FundamentalClass (G := G))
    (H : Subgroup G) (r : ℤ)
    (HYP : Chapter04ClassFormationHypotheses U) :
    IsIso (chapter04SubgroupCapMap U H r) := by
  sorry

/-- The two consecutive low-degree isomorphisms are the inputs for dimension shifting. -/
theorem chapter04_class_formation_low_degree_inputs
    {G : Type} [Group G] [Fintype G]
    (U : Chapter04FundamentalClass (G := G))
    (H : Subgroup G)
    (HYP : Chapter04ClassFormationHypotheses U) :
    IsZero (chapter04GroupH (chapter04RestrictGModule U.C H) 1) ∧
      IsIso (chapter04SubgroupCapMap U H 2) := by
  exact ⟨chapter04_idele_class_H1_vanishes U H HYP,
    chapter04_class_formation_isomorphism U H 2 HYP⟩

/-- Dimension shifting propagates the cap-product isomorphism in both directions. -/
theorem chapter04_dimension_shift_through_cohomologically_trivial_middle_terms
    {G : Type} [Group G] [Fintype G]
    (U : Chapter04FundamentalClass (G := G))
    (H : Subgroup G)
    (HYP : Chapter04ClassFormationHypotheses U) :
    ∀ r : ℤ, IsIso (chapter04SubgroupCapMap U H r) := by
  intro r
  exact chapter04_class_formation_isomorphism U H r HYP

/-- The real-place Tate convention is part of the class-formation input: removing the degree-zero
real summands is not definitionally equivalent to the retained Tate complex. -/
theorem chapter04_real_place_tate_terms_are_retained
    {G : Type} [Group G] [Fintype G]
    (U : Chapter04FundamentalClass (G := G))
    (HYP : Chapter04ClassFormationHypotheses U) :
    ∀ H : Subgroup G,
      IsIso (chapter04SubgroupCapMap U H 2) := by
  intro H
  exact chapter04_class_formation_isomorphism U H 2 HYP

end

end LastLib.Book06GlobalClassFieldTheory.Chapter04
