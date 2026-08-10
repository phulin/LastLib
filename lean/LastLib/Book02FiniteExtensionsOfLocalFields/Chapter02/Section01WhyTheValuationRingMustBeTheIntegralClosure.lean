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

/--
The valuation-ring version of uniqueness used by Theorem 2.1.  It quantifies
over all valuation subrings of `L` whose restriction is exactly the base
valuation ring, so it is not tied to one value-group normalization.
-/
def chapter2UniqueValuationExtension
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰) : Prop :=
  ∀ W : ValuationSubring L,
    chapter2ValuationSubringExtends vK W →
      (W : Set L) = (vL.valuationSubring : Set L)

/--
The family `W` represents exactly all valuation subrings of `L` extending the
base valuation ring.  This is the precise interface behind the intersection
description when uniqueness fails.
-/
def chapter2IntegralClosureIntersection
    {ι : Type*} (vK : Valuation K ℤᵐ⁰) (W : ι → ValuationSubring L) : Prop :=
  (∀ i, chapter2ValuationSubringExtends vK (W i)) ∧
    (∀ V : ValuationSubring L,
      chapter2ValuationSubringExtends vK V →
        ∃ i, (W i : Set L) = (V : Set L))

/-- The integral closure is the unit ball of the unique normalized extension. -/
theorem integral_closure_eq_extension_valuation_subring
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [FiniteDimensional K L]
    (hunique : chapter2UniqueValuationExtension vK vL) :
    (integralClosure vK.valuationSubring L : Set L) =
      (vL.valuationSubring : Set L) := by
  ext x
  constructor
  · intro hx
    let f : vK.valuationSubring →+* vL.valuationSubring :=
      (algebraMap vK.valuationSubring L).codRestrict vL.valuationSubring (by
        intro a
        exact Valuation.HasExtension.algebraMap_mem_valuationSubring vK vL a)
    have hcomp : vL.valuationSubring.subtype.comp f =
        algebraMap vK.valuationSubring L := by
      ext a
      change algebraMap vK.valuationSubring L a =
        algebraMap vK.valuationSubring L a
      rfl
    have hx' : IsIntegral vL.valuationSubring x := by
      change (vL.valuationSubring.subtype :
        vL.valuationSubring →+* L).IsIntegralElem x
      apply RingHom.IsIntegralElem.of_comp (f := f)
      rw [hcomp]
      exact hx
    exact LocalSubring.mem_of_isMax_of_isIntegral
      vL.valuationSubring.isMax_toLocalSubring hx'
  · intro hx
    by_contra hnot
    let C := integralClosure vK.valuationSubring L
    let fAC : vK.valuationSubring →+* C.toSubring :=
      (algebraMap vK.valuationSubring L).codRestrict C.toSubring (by
        intro a
        change algebraMap vK.valuationSubring L a ∈ C
        simpa using (Subalgebra.algebraMap_mem C a))
    letI : Algebra vK.valuationSubring C.toSubring := fAC.toAlgebra
    letI : IsScalarTower vK.valuationSubring C.toSubring L :=
      IsScalarTower.of_algebraMap_eq (fun a => by
        change algebraMap C.toSubring L (fAC a) =
          algebraMap vK.valuationSubring L a
        rfl)
    letI : Algebra.IsIntegral vK.valuationSubring C.toSubring :=
      ⟨fun y => by
        apply (isIntegral_algebraMap_iff
          (R := vK.valuationSubring) (A := C.toSubring) (B := L)
          (FaithfulSMul.algebraMap_injective C.toSubring L)).mp
        exact y.property⟩
    letI : IsIntegrallyClosedIn C.toSubring L := by
      refine isIntegrallyClosedIn_iff.mpr ⟨?_, ?_⟩
      · exact FaithfulSMul.algebraMap_injective _ _
      · intro y hy
        have hy' : IsIntegral vK.valuationSubring y :=
          isIntegral_trans (R := vK.valuationSubring) y hy
        exact ⟨⟨y, hy'⟩, rfl⟩
    obtain ⟨V, hCV, hxV⟩ :=
      Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
        (R := C.toSubring) (x := x) (by simpa [C] using hnot)
    have hVbase : vK.valuationSubring ≤
        V.comap (algebraMap K L) := by
      intro a ha
      change algebraMap K L (a : K) ∈ (V : Set L)
      apply hCV
      change algebraMap K L
        (algebraMap vK.valuationSubring K (⟨a, ha⟩ : vK.valuationSubring)) ∈ C
      rw [← IsScalarTower.algebraMap_apply vK.valuationSubring K L]
      exact Subalgebra.algebraMap_mem C ⟨a, ha⟩
    have hVtop_of_comap_top (hCtop :
        V.comap (algebraMap K L) = ⊤) : V = ⊤ := by
      apply top_unique
      intro y hy
      have hyK : IsIntegral K y := IsIntegral.of_finite K y
      have hKmem : ∀ a : K, algebraMap K L a ∈ (V : Set L) := by
        intro a
        have ha : a ∈ V.comap (algebraMap K L) := by
          rw [hCtop]
          trivial
        exact ha
      let f : K →+* V.toSubring :=
        (algebraMap K L).codRestrict V.toSubring hKmem
      have hcomp : V.subtype.comp f = algebraMap K L := by
        ext a
        rfl
      have hy' : IsIntegral V.toSubring y := by
        change (V.subtype : V →+* L).IsIntegralElem y
        apply RingHom.IsIntegralElem.of_comp (f := f)
        rw [hcomp]
        exact hyK
      exact LocalSubring.mem_of_isMax_of_isIntegral
        V.isMax_toLocalSubring hy'
    have hVtop_or_exact : V = ⊤ ∨
        chapter2ValuationSubringExtends vK V := by
      by_cases hVtop : V = ⊤
      · exact Or.inl hVtop
      right
      have hCneqtop : V.comap (algebraMap K L) ≠ ⊤ := by
        intro hCtop
        exact hVtop (hVtop_of_comap_top hCtop)
      have hcomap : V.comap (algebraMap K L) = vK.valuationSubring := by
        by_cases hnontrivial : vK.IsNontrivial
        · letI : vK.IsNontrivial := hnontrivial
          letI : IsCyclic
              (MonoidWithZeroHom.valueGroup (.ofClass vK)) := inferInstance
          letI : vK.IsRankOneDiscrete :=
            Valuation.IsRankOneDiscrete.mk' vK
          exact (ValuationSubring.eq_of_le_of_ne_top
            vK.valuationSubring hVbase hCneqtop).symm
        · have hAtop : vK.valuationSubring = ⊤ :=
            (Valuation.valuationSubring_eq_top_iff vK).mpr hnontrivial
          have hCtop : V.comap (algebraMap K L) = ⊤ := by
            apply top_unique
            simpa [hAtop] using hVbase
          exact False.elim (hVtop (hVtop_of_comap_top hCtop))
      change (algebraMap K L) ⁻¹' (V : Set L) =
        (vK.valuationSubring : Set K)
      change (V.comap (algebraMap K L) : Set K) =
        (vK.valuationSubring : Set K)
      rw [hcomap]
    rcases hVtop_or_exact with hVtop | hVexact
    · exact hxV (hVtop ▸ Set.mem_univ x)
    · apply hxV
      change x ∈ (V : Set L)
      rw [hunique V hVexact]
      exact hx

/--
The non-unique situation is recorded by the valuation-ring intersection
interface from §2.1.  It is deliberately not replaced by a single valuation
subring.
-/
theorem integral_closure_eq_chosen_extension_intersection
    {ι : Type*} (vK : Valuation K ℤᵐ⁰) (W : ι → ValuationSubring L)
    [FiniteDimensional K L]
    (hfamily : chapter2IntegralClosureIntersection vK W) :
    (integralClosure vK.valuationSubring L : Set L) =
      ⋂ i, (W i : Set L) := by
  ext x
  constructor
  · intro hx
    rw [mem_iInter]
    intro i
    let f : vK.valuationSubring →+* W i :=
      (algebraMap vK.valuationSubring L).codRestrict (W i) (by
        intro a
        change algebraMap K L (a : K) ∈ (W i : Set L)
        have ha : (a : K) ∈ (algebraMap K L) ⁻¹' (W i : Set L) := by
          rw [hfamily.1 i]
          exact a.property
        exact ha)
    have hcomp : (W i).subtype.comp f =
        algebraMap vK.valuationSubring L := by
      ext a
      change algebraMap vK.valuationSubring L a =
        algebraMap vK.valuationSubring L a
      rfl
    have hx' : IsIntegral (W i) x := by
      change ((W i).subtype : W i →+* L).IsIntegralElem x
      apply RingHom.IsIntegralElem.of_comp (f := f)
      rw [hcomp]
      exact hx
    exact LocalSubring.mem_of_isMax_of_isIntegral
      (W i).isMax_toLocalSubring hx'
  · intro hx
    have hx' : ∀ i, x ∈ (W i : Set L) := (mem_iInter.mp hx)
    by_contra hnot
    let C := integralClosure vK.valuationSubring L
    let fAC : vK.valuationSubring →+* C.toSubring :=
      (algebraMap vK.valuationSubring L).codRestrict C.toSubring (by
        intro a
        change algebraMap vK.valuationSubring L a ∈ C
        simpa using (Subalgebra.algebraMap_mem C a))
    letI : Algebra vK.valuationSubring C.toSubring := fAC.toAlgebra
    letI : IsScalarTower vK.valuationSubring C.toSubring L :=
      IsScalarTower.of_algebraMap_eq (fun a => by
        change algebraMap C.toSubring L (fAC a) =
          algebraMap vK.valuationSubring L a
        rfl)
    letI : Algebra.IsIntegral vK.valuationSubring C.toSubring :=
      ⟨fun y => by
        apply (isIntegral_algebraMap_iff
          (R := vK.valuationSubring) (A := C.toSubring) (B := L)
          (FaithfulSMul.algebraMap_injective C.toSubring L)).mp
        exact y.property⟩
    letI : IsIntegrallyClosedIn C.toSubring L := by
      refine isIntegrallyClosedIn_iff.mpr ⟨?_, ?_⟩
      · exact FaithfulSMul.algebraMap_injective _ _
      · intro y hy
        have hy' : IsIntegral vK.valuationSubring y :=
          isIntegral_trans (R := vK.valuationSubring) y hy
        exact ⟨⟨y, hy'⟩, rfl⟩
    obtain ⟨V, hCV, hxV⟩ :=
      Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
        (R := C.toSubring) (x := x) (by simpa [C] using hnot)
    have hVbase : vK.valuationSubring ≤
        V.comap (algebraMap K L) := by
      intro a ha
      change algebraMap K L (a : K) ∈ (V : Set L)
      apply hCV
      change algebraMap K L
        (algebraMap vK.valuationSubring K (⟨a, ha⟩ : vK.valuationSubring)) ∈ C
      rw [← IsScalarTower.algebraMap_apply vK.valuationSubring K L]
      exact Subalgebra.algebraMap_mem C ⟨a, ha⟩
    have hVtop_of_comap_top (hCtop :
        V.comap (algebraMap K L) = ⊤) : V = ⊤ := by
      apply top_unique
      intro y hy
      have hyK : IsIntegral K y := IsIntegral.of_finite K y
      have hKmem : ∀ a : K, algebraMap K L a ∈ (V : Set L) := by
        intro a
        have ha : a ∈ V.comap (algebraMap K L) := by
          rw [hCtop]
          trivial
        exact ha
      let f : K →+* V.toSubring :=
        (algebraMap K L).codRestrict V.toSubring hKmem
      have hcomp : V.subtype.comp f = algebraMap K L := by
        ext a
        rfl
      have hy' : IsIntegral V.toSubring y := by
        change (V.subtype : V →+* L).IsIntegralElem y
        apply RingHom.IsIntegralElem.of_comp (f := f)
        rw [hcomp]
        exact hyK
      exact LocalSubring.mem_of_isMax_of_isIntegral
        V.isMax_toLocalSubring hy'
    have hVtop_or_exact : V = ⊤ ∨
        chapter2ValuationSubringExtends vK V := by
      by_cases hVtop : V = ⊤
      · exact Or.inl hVtop
      right
      have hCneqtop : V.comap (algebraMap K L) ≠ ⊤ := by
        intro hCtop
        exact hVtop (hVtop_of_comap_top hCtop)
      have hcomap : V.comap (algebraMap K L) = vK.valuationSubring := by
        by_cases hnontrivial : vK.IsNontrivial
        · letI : vK.IsNontrivial := hnontrivial
          letI : IsCyclic
              (MonoidWithZeroHom.valueGroup (.ofClass vK)) := inferInstance
          letI : vK.IsRankOneDiscrete :=
            Valuation.IsRankOneDiscrete.mk' vK
          exact (ValuationSubring.eq_of_le_of_ne_top
            vK.valuationSubring hVbase hCneqtop).symm
        · have hAtop : vK.valuationSubring = ⊤ :=
            (Valuation.valuationSubring_eq_top_iff vK).mpr hnontrivial
          have hCtop : V.comap (algebraMap K L) = ⊤ := by
            apply top_unique
            simpa [hAtop] using hVbase
          exact False.elim (hVtop (hVtop_of_comap_top hCtop))
      change (algebraMap K L) ⁻¹' (V : Set L) =
        (vK.valuationSubring : Set K)
      change (V.comap (algebraMap K L) : Set K) =
        (vK.valuationSubring : Set K)
      rw [hcomap]
    rcases hVtop_or_exact with hVtop | hVexact
    · exact hxV (hVtop ▸ Set.mem_univ x)
    · obtain ⟨i, hi⟩ := hfamily.2 V hVexact
      apply hxV
      change x ∈ (V : Set L)
      rw [← hi]
      exact hx' i

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
