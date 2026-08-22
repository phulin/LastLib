import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter15.Section03TheGaloisPicture
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section01WhyUnitsNeedTheirOwnFiltration
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section03HigherQuotientsAreAdditiveResidueFields
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section02TheCompletedProductTheorem
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Algebra.Order.Group.Cyclic

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
  classical
  let V := MonoidWithZeroHom.valueGroup (.ofClass v)
  obtain ⟨eVal⟩ :=
    (LinearOrderedCommGroup.isCyclic_iff_nonempty_equiv_int).mp
      (inferInstance : IsCyclic V)
  let γ : V := eVal.symm (Multiplicative.ofAdd (-1))
  have hγlt : γ < 1 := by
    have hsource : Multiplicative.ofAdd (-1) < Multiplicative.ofAdd (0 : ℤ) := by
      exact Multiplicative.ofAdd_strictMono (by norm_num)
    change eVal.symm (Multiplicative.ofAdd (-1)) < 1
    rw [← eVal.symm.map_one]
    exact eVal.symm.toOrderIso.strictMono hsource
  have hγgen : Subgroup.zpowers γ = ⊤ := by
    apply le_antisymm le_top
    intro x hx
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨-(eVal x).toAdd, ?_⟩
    apply eVal.injective
    simp [γ, Int.toAdd_zpow]
    rw [← Int.ofAdd_mul, one_mul]
    exact ofAdd_toAdd _
  have hγeq : γ = LinearOrderedCommGroup.genLTOne V :=
    LinearOrderedCommGroup.genLTOne_unique V hγlt hγgen
  obtain ⟨π, hπ⟩ :=
    Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial v
  let πunit : Lˣ := Units.mk0 (π : L) hπ.ne_zero
  let γunit : Γˣ := Units.mk0 (v (π : L)) hπ.val_ne_zero
  have hπunit : γunit = Valuation.IsRankOneDiscrete.generator v := by
    apply Units.ext
    exact hπ.val
  let δ : V :=
    ⟨γunit,
      (MonoidWithZeroHom.ofClass v).mem_valueGroup (Set.mem_range_self (π : L))⟩
  have hδlt : δ < 1 := by
    change v (π : L) < 1
    exact hπ.val_lt_one
  have hδgen : Subgroup.zpowers δ = ⊤ := by
    apply le_antisymm le_top
    intro x hx
    rw [Subgroup.mem_zpowers_iff]
    have hx' : (x : Γˣ) ∈ Subgroup.zpowers
        (Valuation.IsRankOneDiscrete.generator v) := by
      rw [Valuation.IsRankOneDiscrete.generator_zpowers_eq_valueGroup]
      exact x.property
    rw [Subgroup.mem_zpowers_iff] at hx'
    obtain ⟨n, hn⟩ := hx'
    refine ⟨n, ?_⟩
    apply Subtype.ext
    change ((δ : Γˣ) ^ n) = (x : Γˣ)
    rw [show (δ : Γˣ) = γunit by rfl, hπunit]
    exact hn
  have hδeq : δ = γ := by
    exact (LinearOrderedCommGroup.genLTOne_unique V hδlt hδgen).trans hγeq.symm
  let valUnit : Lˣ →* V :=
    { toFun := fun x =>
        ⟨Units.mk0 (v (x : L)) (v.ne_zero_iff.mpr x.ne_zero),
          (MonoidWithZeroHom.ofClass v).mem_valueGroup (Set.mem_range_self (x : L))⟩
      map_one' := by
        apply Subtype.ext
        apply Units.ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        apply Units.ext
        simp }
  have hvalπ : valUnit πunit = γ := by
    calc
      valUnit πunit = δ := by
        apply Subtype.ext
        apply Units.ext
        rfl
      _ = γ := hδeq
  let degree : Lˣ →* Multiplicative ℤ := eVal.toMonoidHom.comp valUnit
  have hdegreeπ : degree πunit = Multiplicative.ofAdd (-1) := by
    simp [degree, hvalπ, γ]
  let unitPart : Lˣ → v.valuationSubring.unitGroup := fun x =>
    ⟨πunit ^ (degree x).toAdd * x, by
      rw [ValuationSubring.mem_unitGroup_iff]
      have hvg : valUnit (πunit ^ (degree x).toAdd * x) = 1 := by
        rw [map_mul, map_zpow, hvalπ]
        apply eVal.injective
        simp [degree, γ, Int.toAdd_zpow]
        rw [← Int.ofAdd_mul, one_mul, ← ofAdd_toAdd (eVal (valUnit x))]
        simp
      have hvg' := congrArg (fun y : V => (y : Γˣ).1) hvg
      exact (Valuation.isEquiv_valuation_valuationSubring v).symm.eq_one_iff_eq_one.mpr
        (by simpa [valUnit] using hvg')⟩
  refine ⟨(π : L), hπ, ?_⟩
  have hunitPart_mul (x y : Lˣ) :
      unitPart (x * y) = unitPart x * unitPart y := by
    apply Subtype.ext
    apply Units.ext
    dsimp [unitPart]
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val]
    have hπne : (πunit : L) ≠ 0 := πunit.ne_zero
    change (πunit : L) ^ (degree (x * y)).toAdd *
        ((x : L) * (y : L)) =
      ((πunit : L) ^ (degree x).toAdd * (x : L)) *
        ((πunit : L) ^ (degree y).toAdd * (y : L))
    rw [show (degree (x * y)).toAdd = (degree x).toAdd + (degree y).toAdd by
      simp [degree]]
    rw [zpow_add₀ hπne]
    ac_rfl
  have hdegree_unit (u : v.valuationSubring.unitGroup) :
      degree (u : Lˣ) = 1 := by
    have hu : v ((u : Lˣ) : L) = 1 := by
      exact (Valuation.isEquiv_valuation_valuationSubring v).eq_one_iff_eq_one.mpr
        (by
          simpa using
            (ValuationSubring.mem_unitGroup_iff v.valuationSubring (u : Lˣ)).mp
              u.property)
    have hvalUnit_u : valUnit (u : Lˣ) = 1 := by
      apply Subtype.ext
      apply Units.ext
      simp [valUnit, hu]
    simp [degree, hvalUnit_u]
  let toCoord : Lˣ →* (Multiplicative ℤ × v.valuationSubring.unitGroup) :=
    { toFun := fun x => (degree x, unitPart x)
      map_one' := by
        apply Prod.ext
        · simp [degree]
        · apply Subtype.ext
          apply Units.ext
          simp [unitPart, degree]
      map_mul' := by
        intro x y
        apply Prod.ext
        · simp [degree]
        · exact hunitPart_mul x y }
  let fromCoord :
      (Multiplicative ℤ × v.valuationSubring.unitGroup) →* Lˣ :=
    { toFun := fun z => πunit ^ (-(z.1.toAdd)) * (z.2 : Lˣ)
      map_one' := by simp
      map_mul' := by
        intro x y
        change πunit ^ (-(x.1.toAdd + y.1.toAdd)) *
            ((x.2 : Lˣ) * (y.2 : Lˣ)) =
          (πunit ^ (-x.1.toAdd) * (x.2 : Lˣ)) *
            (πunit ^ (-y.1.toAdd) * (y.2 : Lˣ))
        rw [neg_add, zpow_add]
        ac_rfl }
  have hleft (x : Lˣ) : fromCoord (toCoord x) = x := by
    change πunit ^ (-(degree x).toAdd) *
        (πunit ^ (degree x).toAdd * x) = x
    calc
      πunit ^ (-(degree x).toAdd) *
          (πunit ^ (degree x).toAdd * x) =
          (πunit ^ (degree x).toAdd)⁻¹ *
            (πunit ^ (degree x).toAdd * x) := by rw [zpow_neg]
      _ = x := by simp
  have hdegree_from (z : Multiplicative ℤ × v.valuationSubring.unitGroup) :
      degree (fromCoord z) = z.1 := by
    change degree (πunit ^ (-(z.1.toAdd)) * (z.2 : Lˣ)) = z.1
    rw [map_mul, map_zpow, hdegreeπ, hdegree_unit]
    rw [← Int.ofAdd_mul]
    simpa only [neg_one_mul, neg_neg, ofAdd_toAdd, mul_one]
  have hright (z : Multiplicative ℤ × v.valuationSubring.unitGroup) :
      toCoord (fromCoord z) = z := by
    apply Prod.ext
    · exact hdegree_from z
    · apply Subtype.ext
      apply Units.ext
      dsimp [toCoord, unitPart, fromCoord]
      change ↑(πunit ^ (degree (fromCoord z)).toAdd) *
          (fromCoord z : L) = ((z.2 : Lˣ) : L)
      rw [hdegree_from]
      change ↑(πunit ^ z.1.toAdd) *
          (fromCoord z : L) = ((z.2 : Lˣ) : L)
      rw [show fromCoord z = πunit ^ (-(z.1.toAdd)) * (z.2 : Lˣ) by rfl]
      simp only [Units.val_mul, Units.val_zpow_eq_zpow_val]
      rw [zpow_neg]
      rw [← mul_assoc]
      rw [mul_inv_cancel₀]
      simp
      exact zpow_ne_zero _ πunit.ne_zero
  exact ⟨{
    toFun := toCoord
    invFun := fromCoord
    left_inv := hleft
    right_inv := hright
    map_mul' := by
      intro x y
      exact toCoord.map_mul x y
  }⟩

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
    d.baseResidue (Algebra.intNorm A B (u : B)) =
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
    d.baseResidue (Algebra.intNorm A B (u : B)) =
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
    d.baseResidue (Algebra.intNorm A B (u : B)) =
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
