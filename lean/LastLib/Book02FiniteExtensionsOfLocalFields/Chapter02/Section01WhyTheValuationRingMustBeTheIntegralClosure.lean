import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section01SeparatingBranchesByCompletion
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.Section04HenselianLocalRings
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section03IntegralElementsAreBounded

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
  chapter2ValuationSubringExtends vK vL.valuationSubring ∧
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
  have hDVR : LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.CompleteDVR
      vK.valuationSubring :=
    { isAdicComplete' := hcomplete }
  have hhens :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.HenselianFactorizationProperty
        vK.valuationSubring :=
    @LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.complete_DVR_is_henselian
      _ _ _ hDVR
  have hL : vK.IsEquiv (vL.comap (algebraMap K L)) :=
    Valuation.HasExtension.val_isEquiv_comap
  refine ⟨?_, ?_⟩
  · ext x
    exact (Valuation.mem_valuationSubring_iff vL (algebraMap K L x)).trans
      ((Valuation.HasExtension.val_map_le_one_iff vK vL x).trans
        (Valuation.mem_valuationSubring_iff vK x).symm)
  · intro W hW
    have hW' : (algebraMap K L) ⁻¹' (W : Set L) =
        (vK.valuationSubring : Set K) := hW
    have hWext : vK.HasExtension W.valuation := by
      apply Valuation.HasExtension.ofComapInteger
      rw [ValuationSubring.integer_valuation W]
      ext x
      change algebraMap K L x ∈ W ↔ x ∈ vK.valuationSubring
      exact Set.ext_iff.mp hW' x
    have hW' : vK.IsEquiv (W.valuation.comap (algebraMap K L)) :=
      hWext.val_isEquiv_comap
    have hval :=
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_henselian_valuation_has_unique_branch
        vK hhens vL W.valuation hL hW'
    have hsub := (Valuation.isEquiv_iff_valuationSubring vL W.valuation).mp hval
    simpa only [ValuationSubring.valuationSubring_valuation] using
      congrArg (fun V : ValuationSubring L => (V : Set L)) hsub.symm

/-- The integral closure is the unit ball of the unique normalized extension. -/
theorem integral_closure_eq_extension_valuation_subring
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [FiniteDimensional K L]
    (hunique : chapter2UniqueValuationExtension vK vL) :
    (integralClosure vK.valuationSubring L : Set L) =
      (vL.valuationSubring : Set L) := by
  ext x
  change IsIntegral vK.valuationSubring x ↔ x ∈ vL.valuationSubring
  have hcrit := Set.ext_iff.mp
    (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_integral_closure_valuative_criterion
      (K := K) (L := L) vK)
  let W₀ :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValuationOnField L :=
    { valueGroup := vL.valuationSubring.ValueGroup
      valuation := vL.valuationSubring.valuation }
  have hW₀ : vK.IsEquiv (W₀.valuation.comap (algebraMap K L)) :=
    by
      exact (Valuation.HasExtension.val_isEquiv_comap).trans
        (Valuation.IsEquiv.comap (algebraMap K L)
          (Valuation.isEquiv_valuation_valuationSubring vL))
  constructor
  · intro hx
    have hxall := (hcrit x).mp hx
    simpa [W₀] using hxall W₀ hW₀
  · intro hx
    apply (hcrit x).mpr
    intro W hW
    have hWext : chapter2ValuationSubringExtends vK W.valuation.valuationSubring := by
      ext y
      change W.valuation (algebraMap K L y) ≤ 1 ↔ vK y ≤ 1
      exact (hW.le_one_iff_le_one).symm
    have heq := hunique.2 W.valuation.valuationSubring hWext
    change x ∈ (W.valuation.valuationSubring : Set L)
    rw [heq]
    exact hx

/-- The non-unique valuation-ring form of the integral-closure intersection. -/
theorem integral_closure_eq_chosen_extension_intersection
    {ι : Type*} (vK : Valuation K ℤᵐ⁰) (W : ι → ValuationSubring L)
    [FiniteDimensional K L]
  (hfamily : chapter2IntegralClosureIntersection vK W) :
    (integralClosure vK.valuationSubring L : Set L) =
      ⋂ i, (W i : Set L) := by
  ext x
  change IsIntegral vK.valuationSubring x ↔ x ∈ ⋂ i, (W i : Set L)
  simp only [Set.mem_iInter]
  have hcrit := Set.ext_iff.mp
    (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_integral_closure_valuative_criterion
      (K := K) (L := L) vK)
  constructor
  · intro hx i
    have hWi : (algebraMap K L) ⁻¹' (W i : Set L) =
        (vK.valuationSubring : Set K) := hfamily.1 i
    have hWext : vK.HasExtension (W i).valuation := by
      apply Valuation.HasExtension.ofComapInteger
      rw [ValuationSubring.integer_valuation (W i)]
      ext y
      change algebraMap K L y ∈ W i ↔ y ∈ vK.valuationSubring
      exact Set.ext_iff.mp hWi y
    have hbound :=
      @LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_integral_elements_are_bounded
        K L ℤᵐ⁰ (W i).ValueGroup _ _ _ _ _ vK (W i).valuation hWext x hx
    simpa [ValuationSubring.valuationSubring_valuation] using hbound
  · intro hx
    apply (hcrit x).mpr
    intro V hV
    have hVext : chapter2ValuationSubringExtends vK V.valuation.valuationSubring := by
      ext y
      change V.valuation (algebraMap K L y) ≤ 1 ↔ vK y ≤ 1
      exact (hV.le_one_iff_le_one).symm
    obtain ⟨i, hi⟩ := hfamily.2 V.valuation.valuationSubring hVext
    change x ∈ (V.valuation.valuationSubring : Set L)
    rw [← hi]
    exact hx i

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
