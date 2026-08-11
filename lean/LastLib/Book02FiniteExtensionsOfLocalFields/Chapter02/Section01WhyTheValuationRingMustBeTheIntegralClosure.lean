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

/-! The basic book-facing names for the valuation rings and residue fields. -/

-- SOURCE_ISSUE: §2.1 states Theorem 2.1 only for a finite extension, but its
-- proof uses uniqueness of the extension valuation.  Without a henselian (in
-- particular complete local-field) hypothesis, the integral closure can be
-- semilocal rather than one valuation ring.  The statement should specify
-- the unique normalized extension, or assume the corresponding uniqueness.

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

/-- The image of the base valuation ring inside the extension field. -/
def chapter2BaseImage
    (vK : Valuation K ℤᵐ⁰) : Set L :=
  Set.range (fun x : vK.valuationSubring => algebraMap K L (x : K))

/-- Mathlib's valuation subring is the multiplicative unit ball. -/
theorem extension_valuation_subring_eq_unit_ball
    (vL : Valuation L ℤᵐ⁰) :
    (vL.valuationSubring : Set L) = {x : L | vL x ≤ 1} := by
  rfl

/-- A valuation subring of `L` extends the base valuation ring exactly when
the induced subring of `K` is the base valuation ring. -/
def chapter2ValuationSubringExtends
    (vK : Valuation K ℤᵐ⁰) (W : ValuationSubring L) : Prop :=
  (algebraMap K L) ⁻¹' (W : Set L) = (vK.valuationSubring : Set K)

/-- Uniqueness of the valuation ring above the base valuation ring. -/
def chapter2UniqueValuationExtension
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰) : Prop :=
  ∀ W : ValuationSubring L,
    chapter2ValuationSubringExtends vK W →
      (W : Set L) = (vL.valuationSubring : Set L)

/-- A family of valuation rings enumerating all extensions of the base ring. -/
def chapter2IntegralClosureIntersection
    {ι : Type*} (vK : Valuation K ℤᵐ⁰) (W : ι → ValuationSubring L) : Prop :=
  (∀ i, chapter2ValuationSubringExtends vK (W i)) ∧
    (∀ V : ValuationSubring L,
      chapter2ValuationSubringExtends vK V →
        ∃ i, (W i : Set L) = (V : Set L))

/-- Completeness of the base supplies the valuation-subring uniqueness used in
the integral-closure characterization. -/
-- LOCAL_DEPENDENCY_GUESS: this packages the complete-base uniqueness route
-- from the earlier valuation API into the book-facing subring predicate.
theorem chapter2_complete_base_has_unique_valuation_subring_extension
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [FiniteDimensional K L]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring) :
    chapter2UniqueValuationExtension vK vL := by
  sorry

/-- The integral closure is the unit ball of the unique normalized extension. -/
theorem integral_closure_eq_extension_valuation_subring
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [FiniteDimensional K L]
    (hunique : chapter2UniqueValuationExtension vK vL) :
    (integralClosure vK.valuationSubring L : Set L) =
      (vL.valuationSubring : Set L) := by
  sorry

/-- The non-unique valuation-ring form of the integral-closure intersection. -/
theorem integral_closure_eq_chosen_extension_intersection
    {ι : Type*} (vK : Valuation K ℤᵐ⁰) (W : ι → ValuationSubring L)
    [FiniteDimensional K L]
    (hfamily : chapter2IntegralClosureIntersection vK W) :
    (integralClosure vK.valuationSubring L : Set L) =
      ⋂ i, (W i : Set L) := by
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
  intro x y hxy
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective y
  have hzero : IsLocalRing.residue vL.valuationSubring
      (algebraMap vK.valuationSubring vL.valuationSubring (x - y)) = 0 := by
    rw [← IsLocalRing.ResidueField.algebraMap_residue]
    rw [← sub_eq_zero, ← map_sub] at hxy
    simpa [map_sub] using hxy
  have hmemL : algebraMap vK.valuationSubring vL.valuationSubring (x - y) ∈
      IsLocalRing.maximalIdeal vL.valuationSubring :=
    (IsLocalRing.residue_eq_zero_iff _).mp hzero
  have hmemK : x - y ∈ IsLocalRing.maximalIdeal vK.valuationSubring := by
    rw [← extension_maximal_ideal_comap_eq_base_maximal_ideal vK vL]
    exact hmemL
  rw [← sub_eq_zero, ← map_sub]
  exact (IsLocalRing.residue_eq_zero_iff _).mpr hmemK

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
