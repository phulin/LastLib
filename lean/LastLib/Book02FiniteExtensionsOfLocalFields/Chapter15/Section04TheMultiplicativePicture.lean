import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter15.Section03TheGaloisPicture
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section01WhyUnitsNeedTheirOwnFiltration
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section03HigherQuotientsAreAdditiveResidueFields
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section02TheCompletedProductTheorem

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter15
noncomputable section

open Ideal IsLocalRing
open scoped BigOperators WithZero

universe u

/-! ## 15.4. The multiplicative picture -/

/-
Prior attempt retained for provenance: this chapter initially rebuilt the
congruence subgroup and its quotient locally.  The active declarations below
use Chapter 10's established `chapter10UnitFiltration` and
`Chapter10UnitLayerQuotient` interfaces instead.
-/

/-- Membership in the filtration is the defining congruence condition. -/
theorem mem_unit_filtration_iff
    (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ) (u : Aˣ) :
    u ∈ LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10UnitFiltration A n ↔
      (u : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ n :=
  Iff.rfl

/-- Tame and wild alternatives, with `p = 0` covering residue characteristic zero. -/
def tameRamification (e p : ℕ) : Prop :=
  p = 0 ∨ Nat.Coprime e p

def wildRamification (e p : ℕ) : Prop :=
  p ≠ 0 ∧ ¬ Nat.Coprime e p

/-- Book 2, §15.4: a uniformizer separates the value-group coordinate from units. -/
theorem units_split_by_uniformizer
    {L Γ : Type u} [Field L] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation L Γ) [Valuation.IsRankOneDiscrete v] :
    ∃ π : L, v.IsUniformizer π ∧
      Nonempty (Lˣ ≃* Multiplicative ℤ × v.valuationSubring.unitGroup) := by
  sorry

/-- Book 2, §15.4: the unit filtration is descending. -/
theorem unit_filtration_is_nested
    (A : Type u) [CommRing A] [IsLocalRing A] :
    ∀ n : ℕ,
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10UnitFiltration A (n + 1) ≤
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10UnitFiltration A n := by
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_unit_filtration_descending A

/-- Book 2, §15.4: the zeroth layer is the residue-field multiplicative group. -/
theorem unit_zero_layer_is_residue_units
    (A : Type u) [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] :
    Nonempty
      ((Aˣ ⧸
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10UnitFiltration A 1) ≃*
        (IsLocalRing.ResidueField A)ˣ) := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.chapter08_units_mod_principal_units A

/-- Book 2, §15.4: every positive layer is the additive residue field. -/
/-
The quotient is a multiplicative group, so the additive residue group is
represented by `Multiplicative (Additive k)`.  This is the standard Lean
wrapper for the source's notation `k⁺`.
-/
theorem positive_unit_layer_is_residue_additive
    {L : Type u} [Field L] (A : ValuationSubring L)
    [IsDiscreteValuationRing A] (n : ℕ) (hn : 0 < n) :
    Nonempty
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Chapter10UnitLayerQuotient A n ≃*
        Multiplicative (Additive (IsLocalRing.ResidueField A))) := by
  sorry

/-- Book 2, §15.4: the valuation coordinate of a norm is multiplied by `f`. -/
-- SOURCE_ISSUE: The §15.4 norm-coordinate statement inherits the finite
-- defect obstruction from §15.1.  This wrapper therefore assumes a perfect
-- base residue field and completeness through the canonical structural norm
-- interface.
theorem norm_valuation_coordinate
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰) (f : ℕ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [Module.Finite K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    [PerfectField (IsLocalRing.ResidueField vK.valuationSubring)]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (hf : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
      vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring) = f)
    (hrestriction : normalizedValuationRestriction vK vL
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
        vK.valuationSubring vL.valuationSubring
          (IsLocalRing.maximalIdeal vL.valuationSubring))) (x : L) :
    vK (Algebra.norm K x) = (vL x) ^ f := by
  exact structural_norm_valuation_formula vK vL f hcomplete hf hrestriction x

/-- Book 2, §15.4: the residue-unit coordinate is the residue norm raised to `e`. -/
theorem norm_residue_unit_coordinate
    {A B k l : Type u} [CommRing A] [CommRing B] [Field k] [Field l]
    [Algebra A B] [Algebra k l]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra.IsIntegral A B]
    [Module.Finite A B] [Module.Free A B]
    [Module.Finite k l] [Module.Free k l]
    (d : Chapter15ResidueArithmeticShadow) (u : Bˣ) :
    d.baseResidue (Algebra.norm A (u : B)) =
      (Algebra.norm k ((Units.map d.extensionResidue.toMonoidHom u : lˣ) : l)) ^ d.e := by
  exact residue_norm_shadow_formula d u

/-- The congruence expressing the first-order principal-unit norm term. -/
def normPrincipalUnitLinearization
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] (mB : Ideal B) (n : ℕ) : Prop :=
  ∀ x : B, x ∈ mB ^ n →
    algebraMap A B (Algebra.norm A (1 + x)) - 1 -
        algebraMap A B (Algebra.trace A B x) ∈ mB ^ (n + 1)

/-- Book 2, §15.4: the norm on principal units is linearized by trace to first order. -/
theorem norm_principal_units_are_trace_linearized
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra.IsIntegral A B]
    [Module.Finite A B] [Module.Free A B]
    (n : ℕ) (hn : 0 < n) :
    normPrincipalUnitLinearization (A := A) (B := B)
      (IsLocalRing.maximalIdeal B) n := by
  sorry

/-- Book 2, §15.4: in the unramified case the residue norm is not exponentiated. -/
theorem unramified_residue_norm_coordinate
    {A B k l : Type u} [CommRing A] [CommRing B] [Field k] [Field l]
    [Algebra A B] [Algebra k l]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra.IsIntegral A B]
    [Module.Finite A B] [Module.Free A B]
    [Module.Finite k l] [Module.Free k l]
    (d : Chapter15ResidueArithmeticShadow) (he : d.e = 1) (u : Bˣ) :
    d.baseResidue (Algebra.norm A (u : B)) =
      Algebra.norm k ((Units.map d.extensionResidue.toMonoidHom u : lˣ) : l) := by
  simpa [he] using norm_residue_unit_coordinate d u

/-- Book 2, §15.4: after identifying residue fields, total ramification gives the `e`-th power. -/
theorem totally_ramified_residue_norm_is_eth_power
    {A B k l : Type u} [CommRing A] [CommRing B] [Field k] [Field l]
    [Algebra A B] [Algebra k l]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra.IsIntegral A B]
    [Module.Finite A B] [Module.Free A B]
    [Module.Finite k l] [Module.Free k l]
    (d : Chapter15ResidueArithmeticShadow) (ι : l →+* k)
    (hι : ∀ z : k, ι (algebraMap k l z) = z)
    (hdegree : Module.finrank k l = 1) (u : Bˣ) :
    d.baseResidue (Algebra.norm A (u : B)) =
      (ι (d.extensionResidue (u : B))) ^ d.e := by
  rw [residue_norm_shadow_formula d u]
  obtain ⟨z, hz⟩ :=
    (Module.Free.bijective_algebraMap_of_finrank_eq_one hdegree).2
      (d.extensionResidue (u : B))
  rw [show ((Units.map d.extensionResidue.toMonoidHom u : lˣ) : l) =
      d.extensionResidue (u : B) by rfl, ← hz, Algebra.norm_algebraMap,
    hdegree, pow_one, hι]

/-- Book 2, §15.4: every ramification index is either tame or wild. -/
theorem tame_or_wild_ramification (e p : ℕ) :
    tameRamification e p ∨ wildRamification e p := by
  by_cases hp : p = 0
  · exact Or.inl (Or.inl hp)
  by_cases hc : Nat.Coprime e p
  · exact Or.inl (Or.inr hc)
  · exact Or.inr ⟨hp, hc⟩

/-- Book 2, §15.4: tame and wild alternatives are disjoint. -/
theorem tame_and_wild_ramification_are_disjoint (e p : ℕ) :
    ¬ (tameRamification e p ∧ wildRamification e p) := by
  intro h
  rcases h with ⟨ht, hw⟩
  rcases ht with hp | hc
  · exact hw.1 hp
  · exact hw.2 hc

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter15
