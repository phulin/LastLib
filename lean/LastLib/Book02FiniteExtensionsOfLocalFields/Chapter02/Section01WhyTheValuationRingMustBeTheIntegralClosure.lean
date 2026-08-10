import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02

noncomputable section

open Set
open Ideal IsLocalRing
open scoped BigOperators Polynomial WithZero

/-! # Book 2, Chapter 2, §2.1

The source uses additive valuations and writes the unit ball as `v ≥ 0`.
Mathlib's `Valuation` is multiplicative, so the same unit ball is written
`v x ≤ 1`.  The valuation subrings below are the canonical Mathlib objects.
-/

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- The base valuation ring attached to a valuation on `K`. -/
abbrev baseValuationRing {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) : Type u :=
  vK.valuationSubring

/-- The extension valuation ring attached to a valuation on `L`. -/
abbrev extensionValuationRing {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (vL : Valuation L Γ) : Type v :=
  vL.valuationSubring

/-- The residue field of the base valuation ring. -/
abbrev baseResidueField {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) : Type u :=
  IsLocalRing.ResidueField vK.valuationSubring

/-- The residue field of the extension valuation ring. -/
abbrev extensionResidueField {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (vL : Valuation L Γ) : Type v :=
  IsLocalRing.ResidueField vL.valuationSubring

/--
The fixed-value-group version of uniqueness used by Theorem 2.1.  Existence is
provided by the `Valuation.HasExtension` instance for the chosen `vL`.
-/
def chapter2UniqueValuationExtension
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰) : Prop :=
  ∀ w : Valuation L ℤᵐ⁰,
    vK.IsEquiv (w.comap (algebraMap K L)) → vL.IsEquiv w

/--
The family `w` represents all valuation extensions of `vK`, up to equivalence.
This is the precise interface behind the intersection description when
uniqueness fails.
-/
def chapter2IntegralClosureIntersection
    {ι : Type*} (vK : Valuation K ℤᵐ⁰) (w : ι → Valuation L ℤᵐ⁰) : Prop :=
  ∀ z : Valuation L ℤᵐ⁰,
    vK.IsEquiv (z.comap (algebraMap K L)) ↔
      ∃ i, z.IsEquiv (w i)

/-- The integral closure is the unit ball of the unique normalized extension. -/
theorem integral_closure_eq_extension_valuation_subring
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [FiniteDimensional K L]
    (hunique : chapter2UniqueValuationExtension vK vL) :
    (integralClosure vK.valuationSubring L : Set L) =
      (vL.valuationSubring : Set L) := by
  sorry

/--
The non-unique situation is recorded by the valuation-ring intersection
interface from §2.1.  It is deliberately not replaced by a single valuation
subring.
-/
theorem integral_closure_eq_chosen_extension_intersection
    {ι : Type*} (vK : Valuation K ℤᵐ⁰) (w : ι → Valuation L ℤᵐ⁰)
    [FiniteDimensional K L]
    (hfamily : chapter2IntegralClosureIntersection vK w) :
    (integralClosure vK.valuationSubring L : Set L) =
      ⋂ i, (w i).valuationSubring := by
  sorry

/-- `A = B ∩ K`, expressed as a preimage because `K` is not a subtype of `L`. -/
theorem base_valuation_ring_is_comap_of_extension_ring
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] :
    (algebraMap K L) ⁻¹' (vL.valuationSubring : Set L) =
      (vK.valuationSubring : Set K) := by
  ext x
  exact (Valuation.mem_valuationSubring_iff vL (algebraMap K L x)).trans
    ((Valuation.HasExtension.val_map_le_one_iff vK vL x).trans
      (Valuation.mem_valuationSubring_iff vK x).symm)

/-- The maximal ideal of the extension contracts to the maximal ideal below. -/
theorem extension_maximal_ideal_comap_eq_base_maximal_ideal
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] :
    (IsLocalRing.maximalIdeal vL.valuationSubring).comap
        (algebraMap vK.valuationSubring vL.valuationSubring) =
      IsLocalRing.maximalIdeal vK.valuationSubring := by
  exact Valuation.HasExtension.maximalIdeal_comap_algebraMap_eq_maximalIdeal vK vL

/-- The residue-field inclusion `k ↪ l` induced by the local algebra map. -/
theorem residue_field_map_is_injective
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] :
    Function.Injective
      (algebraMap (IsLocalRing.ResidueField vK.valuationSubring)
        (IsLocalRing.ResidueField vL.valuationSubring)) := by
  sorry

/-- The unit-ball characterization is independent of separability assumptions. -/
theorem integral_closure_characterization_without_separability
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [FiniteDimensional K L]
    (hunique : chapter2UniqueValuationExtension vK vL) :
    (integralClosure vK.valuationSubring L : Set L) =
      (vL.valuationSubring : Set L) := by
  exact integral_closure_eq_extension_valuation_subring vK vL hunique

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02
