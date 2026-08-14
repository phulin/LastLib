import LastLib.Book03RamificationTheory.Chapter05.Section02HerbrandsQuotientTheorem

namespace LastLib.Book03RamificationTheory.Chapter05

noncomputable section

/-! ## 5.3. Tower transitivity -/

/--
 A group-theoretic profile for a Galois tower.  The subgroup profile is the
 lower filtration on `L/M`; its lower groups are required to be the
 restrictions of the top profile.  The quotient setup supplies the
 displacement identity needed for the `M/K` stage.
-/
structure Chapter05HerbrandTowerSetup
    (G : Type*) [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal] where
  quotientSetup : Chapter05QuotientRamificationSetup G H
  subextension : Chapter05RamificationFiltration H
  subgroup_lower_formula :
    ∀ u : ℝ, (-1 : ℝ) ≤ u →
      subextension.lowerGroup u =
        (quotientSetup.upstairs.lowerGroup u).comap (Subgroup.subtype H)

namespace Chapter05HerbrandTowerSetup

variable {G : Type*} [Group G] [Fintype G]
variable (H : Subgroup G) [H.Normal]

theorem lower_subgroup_formula
    (T : Chapter05HerbrandTowerSetup G H) {u : ℝ}
    (hu : (-1 : ℝ) ≤ u) :
    T.subextension.lowerGroup u =
      (T.quotientSetup.upstairs.lowerGroup u).comap (Subgroup.subtype H) := by
  exact T.subgroup_lower_formula u hu

end Chapter05HerbrandTowerSetup

/-- Lower numbering is functorial for the subgroup stage of the tower. -/
theorem chapter05_lower_subgroup_formula
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (T : Chapter05HerbrandTowerSetup G H) {u : ℝ}
    (hu : (-1 : ℝ) ≤ u) :
    T.subextension.lowerGroup u =
      (T.quotientSetup.upstairs.lowerGroup u).comap (Subgroup.subtype H) := by
  exact T.subgroup_lower_formula u hu

/-!
 The analytic transitivity formulas.  In the field interpretation the three
 profiles are attached to `L/K`, `L/M`, and `M/K`, respectively.
-/
theorem chapter05_herbrand_tower_transitivity
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (T : Chapter05HerbrandTowerSetup G H)
    (hLK : Function.Bijective
      (chapter05HerbrandFunction T.quotientSetup.upstairs))
    (hLM : Function.Bijective
      (chapter05HerbrandFunction T.subextension))
    (hMK : Function.Bijective
      (chapter05HerbrandFunction T.quotientSetup.downstairs))
    {u : ℝ} (hu : (-1 : ℝ) ≤ u) :
    chapter05HerbrandFunction T.quotientSetup.upstairs u =
      chapter05HerbrandFunction T.quotientSetup.downstairs
        (chapter05HerbrandFunction T.subextension u) := by
  sorry

theorem chapter05_herbrand_inverse_tower_transitivity
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (T : Chapter05HerbrandTowerSetup G H)
    (hLK : Function.Bijective
      (chapter05HerbrandFunction T.quotientSetup.upstairs))
    (hLM : Function.Bijective
      (chapter05HerbrandFunction T.subextension))
    (hMK : Function.Bijective
      (chapter05HerbrandFunction T.quotientSetup.downstairs))
    {v : ℝ} (hv : (-1 : ℝ) ≤ v) :
    chapter05HerbrandInverse T.quotientSetup.upstairs v =
      chapter05HerbrandInverse T.subextension
        (chapter05HerbrandInverse T.quotientSetup.downstairs v) := by
  sorry

/-- A closure-independent invariant is the formal interface for descent from a Galois closure. -/
structure Chapter05ClosureIndependentInvariant (C X : Type*) where
  nonempty : Nonempty C
  value : C → X
  independent : ∀ c₁ c₂ : C, value c₁ = value c₂

namespace Chapter05ClosureIndependentInvariant

variable {C X : Type*}

theorem value_eq (I : Chapter05ClosureIndependentInvariant C X)
    (c₁ c₂ : C) : I.value c₁ = I.value c₂ := by
  exact I.independent c₁ c₂

end Chapter05ClosureIndependentInvariant

/-
 The non-Galois protocol used later in the book is recorded as a reusable
 interface: choose a finite Galois closure, apply subgroup and quotient
 formulas there, and descend only invariants equipped with the independence
 witness.  Different and discriminant ideals are the principal later
 instances of this interface.
-/
theorem chapter05_galois_closure_descent_of_independent_invariant
    {C X : Type*}
    (I : Chapter05ClosureIndependentInvariant C X)
    (c₁ c₂ : C) : I.value c₁ = I.value c₂ := by
  exact I.independent c₁ c₂

end
end LastLib.Book03RamificationTheory.Chapter05
