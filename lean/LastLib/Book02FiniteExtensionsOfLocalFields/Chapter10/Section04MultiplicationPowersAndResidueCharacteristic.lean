import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section03HigherQuotientsAreAdditiveResidueFields

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10

noncomputable section

open Ideal IsLocalRing
open scoped BigOperators

/-! ## 10.4. Multiplication, powers, and the residue characteristic -/

/-- First-order power congruence, including the integer-power formulation. -/
theorem chapter10_unit_power_first_order_congruence
    {L : Type*} [Field L] (A : ValuationSubring L) (m : ℤ) (n : ℕ)
    (hn : 0 < n) (x : A) (hx : x ∈ (IsLocalRing.maximalIdeal A) ^ n)
    (u : Aˣ) (hu : (u : A) = 1 + x) :
    ((u ^ m : Aˣ) : A) - (1 + (m : A) * x) ∈
      (IsLocalRing.maximalIdeal A) ^ (2 * n) := by
  sorry

/-- The induced power map on a multiplicative graded layer. -/
noncomputable def chapter10UnitLayerPowerMap
    {L : Type*} [Field L] (A : ValuationSubring L) (m n : ℕ) :
    Chapter10UnitLayerQuotient A n →* Chapter10UnitLayerQuotient A n := by
  sorry

/- The scalar action on the additive ideal layer is kept explicit so that the
   comparison below does not identify a power map with the identity map. -/
noncomputable def chapter10IdealLayerScalarMap
    {L : Type*} [Field L] (A : ValuationSubring L) (m n : ℕ) :
    Chapter10IdealLayer A (IsLocalRing.maximalIdeal A) n →+
      Chapter10IdealLayer A (IsLocalRing.maximalIdeal A) n := by
  sorry

/-- On a layer, the power map is represented by scalar multiplication by the residue of `m`. -/
theorem chapter10_unit_layer_power_is_residue_scalar
    {L : Type*} [Field L] (A : ValuationSubring L) (m n : ℕ) (hn : 0 < n) :
    ∃ e : Multiplicative
        (Chapter10IdealLayer A (IsLocalRing.maximalIdeal A) n) ≃*
        Chapter10UnitLayerQuotient A n,
      ∀ z : Chapter10IdealLayer A (IsLocalRing.maximalIdeal A) n,
        e (Multiplicative.ofAdd (chapter10IdealLayerScalarMap A m n z)) =
          chapter10UnitLayerPowerMap A m n (e (Multiplicative.ofAdd z)) := by
  sorry

/-- The hypothesis that an integer is a unit of the valuation ring. -/
def Chapter10IntegerIsUnit
    {L : Type*} [Field L] (A : ValuationSubring L) (m : ℕ) : Prop :=
  IsUnit (m : A)

/-- Prime-to-residue-characteristic powers are automorphisms of principal units. -/
theorem chapter10_principal_unit_power_isomorphism
    {L : Type*} [Field L] (A : ValuationSubring L) (m : ℕ)
    (hm : Chapter10IntegerIsUnit A m)
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hDVR : IsDiscreteValuationRing A) :
    ∃ e : chapter10UnitFiltration A 1 ≃* chapter10UnitFiltration A 1,
      ∀ u, e u = u ^ m := by
  sorry

/-- Solving `yᵐ=u` is unique on principal units when `m` is a ring unit. -/
theorem chapter10_principal_unit_power_root_exists_unique
    {L : Type*} [Field L] (A : ValuationSubring L) (m : ℕ)
    (hm : Chapter10IntegerIsUnit A m)
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hDVR : IsDiscreteValuationRing A) :
    ∀ u : chapter10UnitFiltration A 1, ∃! y,
      y ^ m = u := by
  sorry

/-- The binomial expansion displays the terms competing in a residue-characteristic power. -/
theorem chapter10_residue_characteristic_binomial_expansion
    {L : Type*} [Field L] (A : ValuationSubring L) (p : ℕ) (x : A) :
    (1 + x) ^ p =
      Finset.sum (Finset.range (p + 1))
        (fun k => (p.choose k : A) * x ^ k) := by
  sorry

/-- If the residue of `m` vanishes, the first-order map on every layer vanishes. -/
theorem chapter10_residue_characteristic_layer_map_can_vanish
    {L : Type*} [Field L] (A : ValuationSubring L) (m n : ℕ) (hn : 0 < n)
    (hzero : (m : Chapter10ResidueField A) = 0) :
    ∃ f : Chapter10ResidueField A →+ Chapter10ResidueField A,
      (∀ a, f a = (m : Chapter10ResidueField A) * a) ∧
        (∀ a, f a = 0) ∧
        ∀ z : Chapter10IdealLayer A (IsLocalRing.maximalIdeal A) n,
          chapter10IdealLayerScalarMap A m n z = 0 := by
  let f : Chapter10ResidueField A →+ Chapter10ResidueField A := {
    toFun := fun a => (m : Chapter10ResidueField A) * a
    map_zero' := by simp
    map_add' := by intro a b; simp [mul_add] }
  refine ⟨f, ?_, ?_, ?_⟩
  · intro a
    rfl
  · intro a
    change (m : Chapter10ResidueField A) * a = 0
    simp [hzero]
  · intro z
    sorry

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10
