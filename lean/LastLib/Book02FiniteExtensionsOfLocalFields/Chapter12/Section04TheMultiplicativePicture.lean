import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12.Section03TheGaloisPicture

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12

noncomputable section

open Ideal IsLocalRing
open scoped BigOperators WithZero

universe u

/-! ## 12.4. The multiplicative picture -/

/--
The unit filtration on a local ring.  For a valuation ring this is
`U^0 = O^×` and, for positive indices, `U^n = 1 + m^n`.
-/
def unitFiltration
    (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ) : Subgroup Aˣ where
  carrier := {u | (u : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ n}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv
    change ((u : A) * (v : A) - 1) ∈ (IsLocalRing.maximalIdeal A) ^ n
    change (u : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ n at hu
    change (v : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ n at hv
    rw [show (u : A) * (v : A) - 1 =
      ((u : A) - 1) * (v : A) + ((v : A) - 1) by ring]
    exact (IsLocalRing.maximalIdeal A).mul_mem_right (v : A) hu |>.add_mem hv
  inv_mem' := by
    intro u hu
    change ((↑(u⁻¹) : A) - 1) ∈ (IsLocalRing.maximalIdeal A) ^ n
    change (u : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ n at hu
    simpa [sub_mul] using
      (IsLocalRing.maximalIdeal A).neg_mem
        ((IsLocalRing.maximalIdeal A).mul_mem_right (↑(u⁻¹) : A) hu)

/-- The successive quotient of two adjacent unit-filtration terms. -/
abbrev unitFiltrationLayer
    (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ) : Type u :=
  (unitFiltration A n : Type u) ⧸
    ((unitFiltration A (n + 1)).comap (unitFiltration A n).subtype)

/-- Tame and wild alternatives, with `p = 0` covering residue characteristic zero. -/
def tameRamification (e p : ℕ) : Prop :=
  p = 0 ∨ Nat.Coprime e p

def wildRamification (e p : ℕ) : Prop :=
  p ≠ 0 ∧ ¬ Nat.Coprime e p

/-- Book 2, §12.4: a uniformizer separates the value-group coordinate from units. -/
theorem units_split_by_uniformizer
    {L Γ : Type u} [Field L] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation L Γ) [Valuation.IsRankOneDiscrete v] :
    ∃ π : L, v.IsUniformizer π ∧
      Nonempty (Lˣ ≃* Multiplicative ℤ × v.valuationSubring.unitGroup) := by
  sorry

/-- Book 2, §12.4: the unit filtration is descending. -/
theorem unit_filtration_is_nested
    (A : Type u) [CommRing A] [IsLocalRing A] :
    ∀ n : ℕ, unitFiltration A (n + 1) ≤ unitFiltration A n := by
  intro n u hu
  change (u : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ n
  change (u : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ (n + 1) at hu
  exact Ideal.pow_le_pow_right (Nat.le_add_right n 1) hu

/-- Book 2, §12.4: the zeroth layer is the residue-field multiplicative group. -/
theorem unit_zero_layer_is_residue_units
    (A : Type u) [CommRing A] [IsLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] :
    Nonempty
      (unitFiltrationLayer A 0 ≃*
        (IsLocalRing.ResidueField A)ˣ) := by
  let ρ : (unitFiltration A 0 : Type u) →*
      (IsLocalRing.ResidueField A)ˣ :=
    (Units.map (IsLocalRing.residue A).toMonoidHom).comp
      (unitFiltration A 0).subtype
  have hρ : Function.Surjective ρ := by
    intro y
    obtain ⟨u, hu⟩ :=
      IsLocalRing.surjective_units_map_of_local_ringHom
        (IsLocalRing.residue A) IsLocalRing.residue_surjective
        (inferInstanceAs (IsLocalHom (IsLocalRing.residue A))) y
    refine ⟨⟨u, ?_⟩, ?_⟩
    · simp [unitFiltration]
    · exact hu
  have hker : ρ.ker =
      (unitFiltration A 1).comap (unitFiltration A 0).subtype := by
    classical
    ext u
    constructor
    · intro hu
      change ρ u = 1 at hu
      have hval : IsLocalRing.residue A (u : A) = 1 := by
        have h := congrArg Units.val hu
        simpa [ρ] using h
      change (u : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ 1
      rw [pow_one]
      rw [← IsLocalRing.residue_eq_zero_iff]
      simpa [map_sub] using sub_eq_zero.mpr hval
    · intro hu
      change (u : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ 1 at hu
      rw [pow_one] at hu
      have hzero : IsLocalRing.residue A (u : A) - 1 = 0 := by
        have hz : IsLocalRing.residue A ((u : A) - 1) = 0 :=
          (IsLocalRing.residue_eq_zero_iff _).2 hu
        simpa [map_sub] using hz
      have hval : IsLocalRing.residue A (u : A) = 1 :=
        sub_eq_zero.mp hzero
      apply MonoidHom.mem_ker.mpr
      apply Units.ext
      change IsLocalRing.residue A (u : A) = 1
      exact hval
  refine ⟨?_⟩
  rw [← hker]
  exact QuotientGroup.quotientKerEquivOfSurjective ρ hρ

/-- Book 2, §12.4: every positive layer is the additive residue field. -/
-- STATEMENT_NEEDS_UPDATE: `Multiplicative (Additive k)` carries the
-- multiplicative group law of the field `k`, not its additive group law, so
-- it cannot be the positive unit layer in general.  The minimal correction is
-- to state the codomain as `Multiplicative k`.
theorem positive_unit_layer_is_residue_additive
    (A : Type u) [CommRing A] [IsLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] (n : ℕ) (hn : 0 < n) :
    Nonempty
      (unitFiltrationLayer A n ≃*
        Multiplicative (Additive (IsLocalRing.ResidueField A))) := by
  sorry

/-- Book 2, §12.4: the valuation coordinate of a norm is multiplied by `f`. -/
-- SOURCE_ISSUE: The §12.4 norm-coordinate statement inherits the finite
-- defect obstruction from §12.1.  This wrapper therefore assumes a perfect
-- base residue field and completeness through the canonical structural norm
-- interface.
theorem norm_valuation_coordinate
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰) (f : ℕ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [Module.Finite K L]
    [FiniteDimensional K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    [PerfectField (IsLocalRing.ResidueField vK.valuationSubring)]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (hf : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
      vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring) = f) (x : L) :
    vK (Algebra.norm K x) = (vL x) ^ f := by
  exact structural_norm_valuation_formula vK vL f hcomplete hf x

/-- Book 2, §12.4: the residue-unit coordinate is the residue norm raised to `e`. -/
theorem norm_residue_unit_coordinate
    {A B k l : Type u} [CommRing A] [CommRing B] [Field k] [Field l]
    [Algebra A B] [Algebra k l]
    [IsLocalRing A] [IsLocalRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra.IsIntegral A B]
    [Module.Finite A B] [Module.Free A B]
    [Module.Finite k l] [Module.Free k l]
    (d : Chapter12ResidueArithmeticShadow) (u : Bˣ) :
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

/-- Book 2, §12.4: the norm on principal units is linearized by trace to first order. -/
theorem norm_principal_units_are_trace_linearized
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra.IsIntegral A B]
    [Module.Finite A B] [Module.Free A B]
    (n : ℕ) (hn : 0 < n) :
    normPrincipalUnitLinearization (A := A) (B := B)
      (IsLocalRing.maximalIdeal B) n := by
  sorry

/-- Book 2, §12.4: in the unramified case the residue norm is not exponentiated. -/
theorem unramified_residue_norm_coordinate
    {A B k l : Type u} [CommRing A] [CommRing B] [Field k] [Field l]
    [Algebra A B] [Algebra k l]
    [IsLocalRing A] [IsLocalRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra.IsIntegral A B]
    [Module.Finite A B] [Module.Free A B]
    [Module.Finite k l] [Module.Free k l]
    (d : Chapter12ResidueArithmeticShadow) (he : d.e = 1) (u : Bˣ) :
    d.baseResidue (Algebra.norm A (u : B)) =
      Algebra.norm k ((Units.map d.extensionResidue.toMonoidHom u : lˣ) : l) := by
  simpa [he] using norm_residue_unit_coordinate d u

/-- Book 2, §12.4: after identifying residue fields, total ramification gives the `e`-th power. -/
theorem totally_ramified_residue_norm_is_eth_power
    {A B k l : Type u} [CommRing A] [CommRing B] [Field k] [Field l]
    [Algebra A B] [Algebra k l]
    [IsLocalRing A] [IsLocalRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra.IsIntegral A B]
    [Module.Finite A B] [Module.Free A B]
    [Module.Finite k l] [Module.Free k l]
    (d : Chapter12ResidueArithmeticShadow) (ι : l →+* k)
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

/-- Book 2, §12.4: every ramification index is either tame or wild. -/
theorem tame_or_wild_ramification (e p : ℕ) :
    tameRamification e p ∨ wildRamification e p := by
  by_cases hp : p = 0
  · exact Or.inl (Or.inl hp)
  by_cases hc : Nat.Coprime e p
  · exact Or.inl (Or.inr hc)
  · exact Or.inr ⟨hp, hc⟩

/-- Book 2, §12.4: tame and wild alternatives are disjoint. -/
theorem tame_and_wild_ramification_are_disjoint (e p : ℕ) :
    ¬ (tameRamification e p ∧ wildRamification e p) := by
  intro h
  rcases h with ⟨ht, hw⟩
  rcases ht with hp | hc
  · exact hw.1 hp
  · exact hw.2 hc

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12
