import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12.Section03TheGaloisPicture

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12

noncomputable section

open Ideal IsLocalRing
open scoped BigOperators

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
    sorry
  inv_mem' := by
    sorry

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
      Nonempty (Lˣ ≃* ℤ × v.valuationSubring.unitGroup) := by
  sorry

/-- Book 2, §12.4: the unit filtration is descending. -/
theorem unit_filtration_is_nested
    (A : Type u) [CommRing A] [IsLocalRing A] :
    ∀ n : ℕ, unitFiltration A (n + 1) ≤ unitFiltration A n := by
  sorry

/-- Book 2, §12.4: the zeroth layer is the residue-field multiplicative group. -/
theorem unit_zero_layer_is_residue_units
    (A : Type u) [CommRing A] [IsLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] :
    Nonempty
      (unitFiltrationLayer A 0 ≃*
        (IsLocalRing.ResidueField A)ˣ) := by
  sorry

/-- Book 2, §12.4: every positive layer is the additive residue field. -/
theorem positive_unit_layer_is_residue_additive
    (A : Type u) [CommRing A] [IsLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] (n : ℕ) (hn : 0 < n) :
    Nonempty
      (unitFiltrationLayer A n ≃*
        Multiplicative (IsLocalRing.ResidueField A)) := by
  sorry

/-- Book 2, §12.4: the valuation coordinate of a norm is multiplied by `f`. -/
theorem norm_valuation_coordinate
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ) (f : ℕ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [Module.Finite K L]
    (hf : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
      vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring) = f) (x : L) :
    vK (Algebra.norm K x) = (vL x) ^ f := by
  sorry

/-- Book 2, §12.4: the residue-unit coordinate is the residue norm raised to `e`. -/
theorem norm_residue_unit_coordinate
    {A B k l : Type u} [CommRing A] [CommRing B] [Field k] [Field l]
    [Algebra A B] [Algebra k l]
    [Module.Finite A B] [Module.Free A B]
    [Module.Finite k l] [Module.Free k l]
    (d : Chapter12ResidueArithmeticShadow) (u : Bˣ) :
    d.baseResidue (Algebra.norm A (u : B)) =
      (Algebra.norm k ((Units.map d.extensionResidue.toMonoidHom u : lˣ) : l)) ^ d.e := by
  exact d.norm_shadow u

/-- The congruence expressing the first-order principal-unit norm term. -/
def normPrincipalUnitLinearization
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] (mA : Ideal A) (mB : Ideal B) (n : ℕ) : Prop :=
  ∀ x : B, x ∈ mB ^ n →
    algebraMap A B (Algebra.norm A (1 + x)) - 1 -
        algebraMap A B (Algebra.trace A B x) ∈ mB ^ (n + 1)

/-- Book 2, §12.4: the norm on principal units is linearized by trace to first order. -/
theorem norm_principal_units_are_trace_linearized
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [Module.Free A B] (mA : Ideal A) (mB : Ideal B)
    (n : ℕ) (hn : 0 < n) :
    normPrincipalUnitLinearization mA mB n := by
  sorry

/-- Book 2, §12.4: in the unramified case the residue norm is not exponentiated. -/
theorem unramified_residue_norm_coordinate
    {A B k l : Type u} [CommRing A] [CommRing B] [Field k] [Field l]
    [Algebra A B] [Algebra k l]
    [Module.Finite A B] [Module.Free A B]
    [Module.Finite k l] [Module.Free k l]
    (d : Chapter12ResidueArithmeticShadow) (he : d.e = 1) (u : Bˣ) :
    d.baseResidue (Algebra.norm A (u : B)) =
      Algebra.norm k ((Units.map d.extensionResidue.toMonoidHom u : lˣ) : l) := by
  simpa [he] using d.norm_shadow u

/-- Book 2, §12.4: after identifying residue fields, total ramification gives the `e`-th power. -/
theorem totally_ramified_residue_norm_is_eth_power
    {A B k l : Type u} [CommRing A] [CommRing B] [Field k] [Field l]
    [Algebra A B] [Algebra k l]
    [Module.Finite A B] [Module.Free A B]
    [Module.Finite k l] [Module.Free k l]
    (d : Chapter12ResidueArithmeticShadow) (ι : l →+* k)
    (hres : ∀ u : Bˣ,
      Algebra.norm k ((Units.map d.extensionResidue.toMonoidHom u : lˣ) : l) =
        ι (d.extensionResidue (u : B))) (u : Bˣ) :
    d.baseResidue (Algebra.norm A (u : B)) =
      (ι (d.extensionResidue (u : B))) ^ d.e := by
  rw [d.norm_shadow u, hres]

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
