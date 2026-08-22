import LastLib.Book03RamificationTheory.Chapter09.Section03TameAndWildPartsOfTheDifferent

namespace LastLib.Book03RamificationTheory.Chapter09

noncomputable section

open LastLib.Book03RamificationTheory.Chapter05
open scoped Classical
open scoped BigOperators

/-! ## 9.4. A tower check -/

def chapter09HerbrandIndexWeight
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (u : ℝ) : ℝ :=
  (Nat.card (D.lowerGroup u) : ℝ) /
    (Nat.card (D.lowerGroup 0) : ℝ)

theorem chapter09_herbrand_slope_is_index_weight
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (u : ℝ) (hu : 0 < u) :
    chapter05HerbrandSlope D u = chapter09HerbrandIndexWeight D u := by
  simp [chapter05HerbrandSlope, chapter09HerbrandIndexWeight, hu]

structure Chapter09TowerDifferentCheck
    (G : Type*) [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal] where
  tower : Chapter05HerbrandTowerSetup G H
  dLK : ℕ
  dLM : ℕ
  dMK : ℕ
  dLK_hilbert :
    dLK = chapter09GroupCountSum tower.quotientSetup.upstairs
  dLM_hilbert :
    dLM = chapter09GroupCountSum tower.subextension
  dMK_hilbert :
    dMK = chapter09GroupCountSum tower.quotientSetup.downstairs

theorem chapter09_tower_lower_subgroup_formula
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (T : Chapter05HerbrandTowerSetup G H) {u : ℝ}
    (hu : (-1 : ℝ) ≤ u) :
    T.subextension.lowerGroup u =
      (T.quotientSetup.upstairs.lowerGroup u).comap
        (Subgroup.subtype H) := by
  exact chapter05_lower_subgroup_formula H T hu

theorem chapter09_tower_quotient_upper_formula
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (T : Chapter05HerbrandTowerSetup G H)
    (_hup : Function.Bijective
      (chapter05HerbrandFunction T.quotientSetup.upstairs))
    (_hdown : Function.Bijective
      (chapter05HerbrandFunction T.quotientSetup.downstairs))
    {v : ℝ} (hv : (-1 : ℝ) ≤ v) :
    chapter05UpperRamificationGroup T.quotientSetup.downstairs v =
      chapter05UpperQuotientImage H T.quotientSetup.upstairs v := by
  exact chapter05_herbrand_quotient_theorem H T.quotientSetup hv

theorem chapter09_tower_quotient_exact_sequence
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal] :
    Function.MulExact (Subgroup.subtype H)
        (chapter05QuotientMap H) ∧
      Function.Surjective (chapter05QuotientMap H) := by
  exact Chapter05QuotientRamificationSetup.quotient_exact_sequence H

theorem chapter09_tower_fixed_field_quotient_equiv
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup (Gal(L / K))) [H.Normal] :
    Nonempty
      ((Gal(L / K) ⧸ H) ≃*
        Gal(LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FixedField H / K)) := by
  exact chapter05_fixed_field_quotient_galois_equiv H

theorem chapter09_different_transitivity_from_tower_check
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (C : Chapter09TowerDifferentCheck G H)
    (hLK : Function.Bijective
      (chapter05HerbrandFunction C.tower.quotientSetup.upstairs))
    (hLM : Function.Bijective
      (chapter05HerbrandFunction C.tower.subextension))
    (hMK : Function.Bijective
      (chapter05HerbrandFunction C.tower.quotientSetup.downstairs)) :
    C.dLK = C.dLM + C.tower.quotientSetup.eLM * C.dMK := by
  sorry

theorem chapter09_different_transitivity_field_form
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (C : Chapter09TowerDifferentCheck G H)
    (hLK : Function.Bijective
      (chapter05HerbrandFunction C.tower.quotientSetup.upstairs))
    (hLM : Function.Bijective
      (chapter05HerbrandFunction C.tower.subextension))
    (hMK : Function.Bijective
      (chapter05HerbrandFunction C.tower.quotientSetup.downstairs)) :
    C.dLK = C.dLM + C.tower.quotientSetup.eLM * C.dMK := by
  exact chapter09_different_transitivity_from_tower_check H C hLK hLM hMK

end

end LastLib.Book03RamificationTheory.Chapter09
