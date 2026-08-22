import LastLib.Book03RamificationTheory.Chapter03.Dependencies
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.ZMod.Basic

namespace LastLib.Book03RamificationTheory.Chapter03

noncomputable section

open scoped BigOperators

/-! ## 3.7. Same degree, arbitrarily different depth -/

/- The normal-form condition on a family member. -/
def chapter03ArtinSchreierFamilyMember (p m : ℕ) : Prop :=
  0 < m ∧ Nat.Coprime m p

/- The common abstract cyclic group of the Artin--Schreier family. -/
abbrev chapter03ArtinSchreierAbstractGaloisGroup (p : ℕ) :=
  Multiplicative (ZMod p)

/- The numerical profile recorded for one family member. -/
structure Chapter03RamificationExampleProfile where
  degree : ℕ
  ramificationIndex : ℕ
  residueDegree : ℕ
  galoisGroupOrder : ℕ
  lowerBreak : ℕ
  differentExponent : ℕ

def chapter03ArtinSchreierNumericalProfile
    (p m : ℕ) : Chapter03RamificationExampleProfile :=
  { degree := p
    ramificationIndex := p
    residueDegree := 1
    galoisGroupOrder := p
    lowerBreak := m
    differentExponent := (m + 1) * (p - 1) }

theorem chapter03_artin_schreier_family_profile_values
    (p m : ℕ) (_hm : chapter03ArtinSchreierFamilyMember p m) :
    let P := chapter03ArtinSchreierNumericalProfile p m
    P.degree = p ∧ P.ramificationIndex = p ∧ P.residueDegree = 1 ∧
      P.galoisGroupOrder = p ∧ P.lowerBreak = m ∧
        P.differentExponent = (m + 1) * (p - 1) := by
  simp [chapter03ArtinSchreierNumericalProfile]

theorem chapter03_artin_schreier_abstract_group_has_order_p
    (p : ℕ) [Fact p.Prime] :
    Nat.card (chapter03ArtinSchreierAbstractGaloisGroup p) = p := by
  sorry

theorem chapter03_artin_schreier_profile_has_same_degree_and_group
    (p m : ℕ) [Fact p.Prime]
    (_hm : chapter03ArtinSchreierFamilyMember p m) :
    let P := chapter03ArtinSchreierNumericalProfile p m
    P.degree = P.ramificationIndex ∧ P.degree = P.galoisGroupOrder ∧
      P.residueDegree = 1 := by
  simp [chapter03ArtinSchreierNumericalProfile]

theorem chapter03_artin_schreier_different_exponent_formula
    (p m : ℕ) :
    (chapter03ArtinSchreierNumericalProfile p m).differentExponent =
      (m + 1) * (p - 1) := by
  rfl

theorem chapter03_artin_schreier_family_has_unbounded_breaks
    (p : ℕ) [Fact p.Prime] :
    ∀ B : ℕ, ∃ m : ℕ,
      chapter03ArtinSchreierFamilyMember p m ∧ B < m := by
  sorry

theorem chapter03_artin_schreier_family_different_exponents_are_unbounded
    (p : ℕ) [Fact p.Prime] :
    ∀ B : ℕ, ∃ m : ℕ,
      chapter03ArtinSchreierFamilyMember p m ∧
        B < (chapter03ArtinSchreierNumericalProfile p m).differentExponent := by
  sorry

theorem chapter03_no_different_bound_from_degree_only
    (p : ℕ) [Fact p.Prime] :
    ¬ ∃ B : ℕ, ∀ m : ℕ,
      chapter03ArtinSchreierFamilyMember p m →
        (chapter03ArtinSchreierNumericalProfile p m).differentExponent ≤ B := by
  sorry

theorem chapter03_artin_schreier_family_lower_breaks
    {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime]
    (F : ℕ → Chapter03LowerDisplacementFiltration G)
    (hgroup : Nat.card G = p)
    (hdisp : ∀ m : ℕ, chapter03ArtinSchreierFamilyMember p m →
      ∀ {σ : G}, σ ≠ 1 → (F m).displacement σ = m + 1) :
    ∀ B : ℕ, ∃ m : ℕ,
      chapter03ArtinSchreierFamilyMember p m ∧ B < m ∧
        chapter03LowerBreak (F m) m := by
  sorry

/- SOURCE_WARNING (3.7): The phrase “same degree” is not a discriminant
   bound.  The profile and the two unboundedness theorems make the missing
   parameter explicit: the lower break (equivalently, the different exponent)
   must also be controlled. -/

end
end LastLib.Book03RamificationTheory.Chapter03
