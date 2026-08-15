import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section04RamificationIndexAndResidueDegree
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.FieldTheory.Separable
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.IrreducibleRing
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter10

universe u10K u10L u10Γ

open scoped BigOperators TensorProduct WithZero PowerSeries
open Polynomial

noncomputable section

/-!
# Chapter 10: Extensions of valuations

This file is a statement-generation formalization of Sections 10.1--10.7 of
Book 1.  The declarations deliberately keep the valuation-theoretic data
explicit: this makes the extension, residue, and ramification assertions
usable independently of the other generated chapters.
-/

/-! # Book 1, Chapter 10, Section 10.7: Concrete Finite Extensions
-/

/-! ## 10.7. Concrete finite extensions -/

/-- A compact profile for the examples in this section. -/
structure Chapter10FiniteExtensionProfile where
  degree : ℕ
  ramificationIndex : ℕ
  residueDegree : ℕ

/-- A numerical profile records the invariants of a specified finite branch. -/
def Chapter10ProfileRealizedByData
    {K L ΓK ΓL : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓL] [FiniteDimensional K L]
    {v : Valuation K ΓK} {w : Valuation L ΓL}
    {h : v.IsEquiv (w.comap (algebraMap K L))}
    (d : Chapter10HeterogeneousExtensionData v w h)
    (p : Chapter10FiniteExtensionProfile) : Prop :=
  p.degree = Module.finrank K L ∧
  p.ramificationIndex = d.ramificationIndex ∧
    p.residueDegree = d.residueDegree

/-- The profile of a totally ramified extension. -/
def Chapter10TotallyRamified (p : Chapter10FiniteExtensionProfile) : Prop :=
  p.ramificationIndex = p.degree ∧ p.residueDegree = 1

/-- The numerical part of an unramified profile.

This predicate deliberately does not assert separability of the residue
extension; `Chapter10UnramifiedBranch` is the branch-level predicate below.
-/
def Chapter10Unramified (p : Chapter10FiniteExtensionProfile) : Prop :=
  p.ramificationIndex = 1 ∧ p.residueDegree = p.degree

/-- The equal-characteristic relation t = uⁿ. -/
def Chapter10PowerParameterRelation
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (t : K) (u : L) (n : ℕ) : Prop :=
  algebraMap K L t = u ^ n

/-- Scaling of the normalized value on the base field. -/
def Chapter10ValueScaling
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (n : ℕ) : Prop :=
  ∀ x : K, x ≠ 0 → vL (algebraMap K L x) = n • vK x

/-- Separability of the residue-field extension attached to a valuation branch. -/
def Chapter10ResidueExtensionIsSeparable
    {K L ΓK ΓL : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓL]
    (v : Valuation K ΓK) (w : Valuation L ΓL)
    [Valuation.HasExtension v w] : Prop :=
  ∀ x : Chapter10ResidueField w, IsSeparable (Chapter10ResidueField v) x

/-- The intrinsic unramified condition for a specified valuation branch. -/
def Chapter10UnramifiedBranch
    {K L ΓK ΓL : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓL] [FiniteDimensional K L]
    (v : Valuation K ΓK) (w : Valuation L ΓL)
    (h : v.IsEquiv (w.comap (algebraMap K L)))
    (d : Chapter10HeterogeneousExtensionData v w h) : Prop := by
  letI : Valuation.HasExtension v w := ⟨h⟩
  exact d.ramificationIndex = 1 ∧ Chapter10ResidueExtensionIsSeparable v w

/-! The profile interface for an unramified base change packages the field
theoretic realization with the numerical compatibilities.  This is the common
input for later total-ramification and Herbrand arguments. -/

/-- The numerical profile supplied by an unramified base change. -/
def Chapter10UnramifiedBaseChangeProfile
    (base p p' : Chapter10FiniteExtensionProfile) : Prop :=
  Chapter10Unramified base ∧
    p'.degree = p.degree ∧
    p'.ramificationIndex = p.ramificationIndex ∧
    p'.residueDegree = p.residueDegree

/-- Profile compatibility for the changed branch of a base change.  This is
the comparison supplied by the field-theoretic base-change construction, and
is only required for a totally ramified original branch. -/
def Chapter10BaseChangeProfileCompatibility
    (p p' : Chapter10FiniteExtensionProfile) : Prop :=
  p'.degree = p.degree ∧
    p'.ramificationIndex = p.ramificationIndex ∧
    p'.residueDegree = p.residueDegree

/-- A chosen field-theoretic compositum square for an unramified base change.

The four valuation branches, their heterogeneous invariant data, and the
generation of the compositum are retained explicitly.  In particular, a
later profile theorem cannot silently replace the changed field by a bare
tuple of natural numbers. -/
structure Chapter10UnramifiedBaseChangeData
    {K L K' L' ΓK ΓL ΓK' ΓL' : Type*}
    [Field K] [Field L] [Field K'] [Field L']
    [Algebra K L] [Algebra K K'] [Algebra K L']
    [Algebra L L'] [Algebra K' L']
    [IsScalarTower K L L'] [IsScalarTower K K' L']
    [FiniteDimensional K L] [FiniteDimensional K K']
    [FiniteDimensional K' L'] [FiniteDimensional L L']
    [Algebra.IsSeparable K K'] [Algebra.IsSeparable K L]
    [Algebra.IsSeparable K' L']
    [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓL]
    [LinearOrderedCommGroupWithZero ΓK']
    [LinearOrderedCommGroupWithZero ΓL']
    (vK : Valuation K ΓK) (vL : Valuation L ΓL)
    (vK' : Valuation K' ΓK') (vL' : Valuation L' ΓL')
    (hL : vK.IsEquiv (vL.comap (algebraMap K L)))
    (hK' : vK.IsEquiv (vK'.comap (algebraMap K K')))
    (hL' : vK'.IsEquiv (vL'.comap (algebraMap K' L')))
    (hLL' : vL.IsEquiv (vL'.comap (algebraMap L L'))) where
  /-- `L'` is the field generated by the two displayed factors over `K'`. -/
  compositum :
    Algebra.adjoin K' (Set.range (algebraMap L L')) = ⊤
  baseData : Chapter10HeterogeneousExtensionData vK vK' hK'
  baseProfile : Chapter10FiniteExtensionProfile
  baseProfile_realized : Chapter10ProfileRealizedByData baseData baseProfile
  baseProfile_unramified : Chapter10Unramified baseProfile
  /-- The base branch is unramified in the intrinsic residue/value sense. -/
  baseUnramifiedBranch : Chapter10UnramifiedBranch vK vK' hK' baseData
  extensionData : Chapter10HeterogeneousExtensionData vK vL hL
  extensionProfile : Chapter10FiniteExtensionProfile
  extensionProfile_realized :
    Chapter10ProfileRealizedByData extensionData extensionProfile
  changedData : Chapter10HeterogeneousExtensionData vK' vL' hL'
  changedProfile : Chapter10FiniteExtensionProfile
  changedProfile_realized :
    Chapter10ProfileRealizedByData changedData changedProfile
  relativeData : Chapter10HeterogeneousExtensionData vL vL' hLL'
  /-- The changed field is the algebraic base change of the original field.
  This is the structural input from which degree and local-invariant
  compatibility are proved; the numerical profile equality is not stored as
  an assumption. -/
  baseChangeEquiv :
    let : Algebra K' (L ⊗[K] K') := Algebra.TensorProduct.rightAlgebra
    L' ≃ₐ[K'] (L ⊗[K] K')
  /-- The chosen tensor equivalence is aligned with the displayed copy of `L`.
  Without this compatibility, an abstract `K'`-algebra equivalence need not
  describe the given compositum square. -/
  baseChangeEquiv_on_L :
    letI : Algebra K' (L ⊗[K] K') := Algebra.TensorProduct.rightAlgebra
    ∀ x : L,
      baseChangeEquiv (algebraMap L L' x) =
        ((Algebra.TensorProduct.includeLeft :
          L →ₐ[K] (L ⊗[K] K')) x)

private theorem chapter10_unramified_base_change_composite_extension
    {K L L' ΓK ΓL ΓL' : Type*} [Field K] [Field L] [Field L']
    [Algebra K L] [Algebra L L'] [Algebra K L'] [IsScalarTower K L L']
    [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓL]
    [LinearOrderedCommGroupWithZero ΓL']
    (vK : Valuation K ΓK) (vL : Valuation L ΓL) (vL' : Valuation L' ΓL')
    (hL : vK.IsEquiv (vL.comap (algebraMap K L)))
    (hLL' : vL.IsEquiv (vL'.comap (algebraMap L L'))) :
    vK.IsEquiv (vL'.comap (algebraMap K L')) := by
  apply Valuation.isEquiv_of_val_le_one
  intro x
  calc
    vK x ≤ 1 ↔ vL (algebraMap K L x) ≤ 1 := hL.le_one_iff_le_one
    _ ↔ vL' (algebraMap L L' (algebraMap K L x)) ≤ 1 :=
      hLL'.le_one_iff_le_one
    _ ↔ vL' (algebraMap K L' x) ≤ 1 := by
      rw [IsScalarTower.algebraMap_apply K L L']

/-- The four valuation branches in a base-change square induce the same map
from the original value group to the changed value group along either path. -/
theorem chapter10_unramified_base_change_value_group_map_square
    {K L K' L' ΓK ΓL ΓK' ΓL' : Type*}
    [Field K] [Field L] [Field K'] [Field L']
    [Algebra K L] [Algebra K K'] [Algebra K L']
    [Algebra L L'] [Algebra K' L']
    [IsScalarTower K L L'] [IsScalarTower K K' L']
    [FiniteDimensional K L] [FiniteDimensional K K']
    [FiniteDimensional K' L'] [FiniteDimensional L L']
    [Algebra.IsSeparable K K'] [Algebra.IsSeparable K L]
    [Algebra.IsSeparable K' L']
    [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓL]
    [LinearOrderedCommGroupWithZero ΓK']
    [LinearOrderedCommGroupWithZero ΓL']
    (vK : Valuation K ΓK) (vL : Valuation L ΓL)
    (vK' : Valuation K' ΓK') (vL' : Valuation L' ΓL')
    (hL : vK.IsEquiv (vL.comap (algebraMap K L)))
    (hK' : vK.IsEquiv (vK'.comap (algebraMap K K')))
    (hL' : vK'.IsEquiv (vL'.comap (algebraMap K' L')))
    (hLL' : vL.IsEquiv (vL'.comap (algebraMap L L')))
    (D : Chapter10UnramifiedBaseChangeData vK vL vK' vL' hL hK' hL' hLL') :
    D.relativeData.valueGroupMap.comp D.extensionData.valueGroupMap =
      D.changedData.valueGroupMap.comp D.baseData.valueGroupMap := by
  have hfiniteKL' : FiniteDimensional K L' := FiniteDimensional.trans K L L'
  let hKLL' := chapter10_unramified_base_change_composite_extension
    vK vL vL' hL hLL'
  obtain ⟨d⟩ := chapter10_heterogeneous_extension_data_exists vK vL' hKLL'
  have hleft := chapter10_heterogeneous_value_group_map_comp
    (vK := vK) (vL := vL) (vM := vL')
    (hKL := hL) (hLM := hLL') (hKM := hKLL')
    (dKL := D.extensionData) (dLM := D.relativeData) (dKM := d)
  have hright := chapter10_heterogeneous_value_group_map_comp
    (vK := vK) (vL := vK') (vM := vL')
    (hKL := hK') (hLM := hL') (hKM := hKLL')
    (dKL := D.baseData) (dLM := D.changedData) (dKM := d)
  exact hleft.trans hright.symm

/-- The residue-field maps in a base-change square commute with the two
displayed paths from the original residue field to the changed one. -/
theorem chapter10_unramified_base_change_residue_field_map_square
    {K L K' L' ΓK ΓL ΓK' ΓL' : Type*}
    [Field K] [Field L] [Field K'] [Field L']
    [Algebra K L] [Algebra K K'] [Algebra K L']
    [Algebra L L'] [Algebra K' L']
    [IsScalarTower K L L'] [IsScalarTower K K' L']
    [FiniteDimensional K L] [FiniteDimensional K K']
    [FiniteDimensional K' L'] [FiniteDimensional L L']
    [Algebra.IsSeparable K K'] [Algebra.IsSeparable K L]
    [Algebra.IsSeparable K' L']
    [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓL]
    [LinearOrderedCommGroupWithZero ΓK']
    [LinearOrderedCommGroupWithZero ΓL']
    (vK : Valuation K ΓK) (vL : Valuation L ΓL)
    (vK' : Valuation K' ΓK') (vL' : Valuation L' ΓL')
    (hL : vK.IsEquiv (vL.comap (algebraMap K L)))
    (hK' : vK.IsEquiv (vK'.comap (algebraMap K K')))
    (hL' : vK'.IsEquiv (vL'.comap (algebraMap K' L')))
    (hLL' : vL.IsEquiv (vL'.comap (algebraMap L L')))
    (D : Chapter10UnramifiedBaseChangeData vK vL vK' vL' hL hK' hL' hLL') :
    letI : Valuation.HasExtension vK vL := ⟨hL⟩
    letI : Valuation.HasExtension vK vK' := ⟨hK'⟩
    letI : Valuation.HasExtension vK' vL' := ⟨hL'⟩
    letI : Valuation.HasExtension vL vL' := ⟨hLL'⟩
    (Chapter10ResidueFieldMap vL vL').comp
          (Chapter10ResidueFieldMap vK vL) =
        (Chapter10ResidueFieldMap vK' vL').comp
          (Chapter10ResidueFieldMap vK vK') := by
  cases D
  have hfiniteKL' : FiniteDimensional K L' := FiniteDimensional.trans K L L'
  have hKLL' := chapter10_unramified_base_change_composite_extension
    vK vL vL' hL hLL'
  have hleft := chapter10_heterogeneous_residue_field_map_comp
    (vK := vK) (vL := vL) (vM := vL')
    (hKL := hL) (hLM := hLL') (hKM := hKLL')
  have hright := chapter10_heterogeneous_residue_field_map_comp
    (vK := vK) (vL := vK') (vM := vL')
    (hKL := hK') (hLM := hL') (hKM := hKLL')
  simpa using hleft.trans hright.symm

/-- Ramification indices and residue degrees satisfy the multiplicative
square relations associated with the four branches of a base change. -/
theorem chapter10_unramified_base_change_invariant_square
    {K L K' L' ΓK ΓL ΓK' ΓL' : Type*}
    [Field K] [Field L] [Field K'] [Field L']
    [Algebra K L] [Algebra K K'] [Algebra K L']
    [Algebra L L'] [Algebra K' L']
    [IsScalarTower K L L'] [IsScalarTower K K' L']
    [FiniteDimensional K L] [FiniteDimensional K K']
    [FiniteDimensional K' L'] [FiniteDimensional L L']
    [Algebra.IsSeparable K K'] [Algebra.IsSeparable K L]
    [Algebra.IsSeparable K' L']
    [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓL]
    [LinearOrderedCommGroupWithZero ΓK']
    [LinearOrderedCommGroupWithZero ΓL']
    (vK : Valuation K ΓK) (vL : Valuation L ΓL)
    (vK' : Valuation K' ΓK') (vL' : Valuation L' ΓL')
    (hL : vK.IsEquiv (vL.comap (algebraMap K L)))
    (hK' : vK.IsEquiv (vK'.comap (algebraMap K K')))
    (hL' : vK'.IsEquiv (vL'.comap (algebraMap K' L')))
    (hLL' : vL.IsEquiv (vL'.comap (algebraMap L L')))
    (D : Chapter10UnramifiedBaseChangeData vK vL vK' vL' hL hK' hL' hLL') :
    D.extensionData.ramificationIndex * D.relativeData.ramificationIndex =
        D.baseData.ramificationIndex * D.changedData.ramificationIndex ∧
      D.extensionData.residueDegree * D.relativeData.residueDegree =
        D.baseData.residueDegree * D.changedData.residueDegree := by
  have hfiniteKL' : FiniteDimensional K L' := FiniteDimensional.trans K L L'
  have hKLL' := chapter10_unramified_base_change_composite_extension
    vK vL vL' hL hLL'
  obtain ⟨d⟩ := chapter10_heterogeneous_extension_data_exists vK vL' hKLL'
  have hleftRam := chapter10_heterogeneous_tower_ramification_quotient_card_mul
    (vK := vK) (vL := vL) (vM := vL')
    (hKL := hL) (hLM := hLL') (hKM := hKLL')
    (dKL := D.extensionData) (dLM := D.relativeData) (dKM := d)
    (chapter10_heterogeneous_value_group_map_comp
      (vK := vK) (vL := vL) (vM := vL')
      (hKL := hL) (hLM := hLL') (hKM := hKLL')
      (dKL := D.extensionData) (dLM := D.relativeData) (dKM := d))
  have hrightRam := chapter10_heterogeneous_tower_ramification_quotient_card_mul
    (vK := vK) (vL := vK') (vM := vL')
    (hKL := hK') (hLM := hL') (hKM := hKLL')
    (dKL := D.baseData) (dLM := D.changedData) (dKM := d)
    (chapter10_heterogeneous_value_group_map_comp
      (vK := vK) (vL := vK') (vM := vL')
      (hKL := hK') (hLM := hL') (hKM := hKLL')
      (dKL := D.baseData) (dLM := D.changedData) (dKM := d))
  have hleftRes := chapter10_heterogeneous_tower_residue_degree_mul
    (vK := vK) (vL := vL) (vM := vL')
    (hKL := hL) (hLM := hLL') (hKM := hKLL')
    (dKL := D.extensionData) (dLM := D.relativeData) (dKM := d)
  have hrightRes := chapter10_heterogeneous_tower_residue_degree_mul
    (vK := vK) (vL := vK') (vM := vL')
    (hKL := hK') (hLM := hL') (hKM := hKLL')
    (dKL := D.baseData) (dLM := D.changedData) (dKM := d)
  constructor
  · rw [D.extensionData.ramificationIndex_eq,
      D.relativeData.ramificationIndex_eq,
      D.baseData.ramificationIndex_eq,
      D.changedData.ramificationIndex_eq]
    exact hleftRam.symm.trans hrightRam
  · exact hleftRes.symm.trans hrightRes

/-- The profile compatibilities furnished by an actual unramified base change
of a totally ramified branch. -/
theorem chapter10_unramified_base_change_profile_of_data
    {K L K' L' ΓK ΓL ΓK' ΓL' : Type*}
    [Field K] [Field L] [Field K'] [Field L']
    [Algebra K L] [Algebra K K'] [Algebra K L']
    [Algebra L L'] [Algebra K' L']
    [IsScalarTower K L L'] [IsScalarTower K K' L']
    [FiniteDimensional K L] [FiniteDimensional K K']
    [FiniteDimensional K' L'] [FiniteDimensional L L']
    [Algebra.IsSeparable K K'] [Algebra.IsSeparable K L]
    [Algebra.IsSeparable K' L']
    [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓL]
    [LinearOrderedCommGroupWithZero ΓK']
    [LinearOrderedCommGroupWithZero ΓL']
    (vK : Valuation K ΓK) (vL : Valuation L ΓL)
    (vK' : Valuation K' ΓK') (vL' : Valuation L' ΓL')
    (hL : vK.IsEquiv (vL.comap (algebraMap K L)))
    (hK' : vK.IsEquiv (vK'.comap (algebraMap K K')))
    (hL' : vK'.IsEquiv (vL'.comap (algebraMap K' L')))
    (hLL' : vL.IsEquiv (vL'.comap (algebraMap L L')))
    (D : Chapter10UnramifiedBaseChangeData vK vL vK' vL' hL hK' hL' hLL')
    (htotal : Chapter10TotallyRamified D.extensionProfile) :
    Chapter10UnramifiedBaseChangeProfile D.baseProfile
      D.extensionProfile D.changedProfile := by
  unfold Chapter10UnramifiedBaseChangeProfile
  rcases D.baseProfile_realized with ⟨hbase_degree, hbase_ramification, hbase_residue⟩
  rcases D.extensionProfile_realized with
    ⟨hextension_degree, hextension_ramification, hextension_residue⟩
  rcases D.changedProfile_realized with
    ⟨hchanged_profile_degree, hchanged_profile_ramification,
      hchanged_profile_residue⟩
  rcases D.baseProfile_unramified with ⟨hbase_unramified_ramification,
    hbase_unramified_residue⟩
  rcases htotal with ⟨htotal_ramification, htotal_residue⟩
  have hbase_equiv_degree : Module.finrank K' L' = Module.finrank K L := by
    let : Algebra K' (L ⊗[K] K') := Algebra.TensorProduct.rightAlgebra
    calc
      Module.finrank K' L' = Module.finrank K' (L ⊗[K] K') :=
        D.baseChangeEquiv.toLinearEquiv.finrank_eq
      _ = Module.finrank K L := by
        rw [← Module.finrank_baseChange (R := K') (S := K) (M' := L)]
        exact (Algebra.TensorProduct.commRight K K' L).toLinearEquiv.finrank_eq.symm
  have hdegree_rel : Module.finrank L L' = Module.finrank K K' := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < Module.finrank K L by
      exact Module.finrank_pos)
    calc
      Module.finrank K L * Module.finrank L L' = Module.finrank K L' :=
        Module.finrank_mul_finrank K L L'
      _ = Module.finrank K K' * Module.finrank K' L' := by
        exact (Module.finrank_mul_finrank K K' L').symm
      _ = Module.finrank K K' * Module.finrank K L := by
        rw [hbase_equiv_degree]
      _ = Module.finrank K L * Module.finrank K K' := by
        rw [Nat.mul_comm]
  have hbase_degree_pos : 0 < Module.finrank K K' := by
    exact Module.finrank_pos
  have hrelative_quotient_finite :
      Finite (Chapter10ValueGroup vL' ⧸ D.relativeData.valueGroupMap.range) :=
    D.relativeData.finite_quotient
  have hrelative_ramification_pos : 0 < D.relativeData.ramificationIndex := by
    rw [D.relativeData.ramificationIndex_eq]
    exact Nat.card_pos
  let vLcomap : Valuation L ΓL' := vL'.comap (algebraMap L L')
  have hrelative_subring : vL.valuationSubring = vLcomap.valuationSubring :=
    (Valuation.isEquiv_iff_valuationSubring (v₁ := vL)
      (v₂ := vLcomap)).mp hLL'
  have hrelative_extension : Valuation.HasExtension vLcomap vL' :=
    ⟨Valuation.IsEquiv.refl⟩
  have hrelative_extension_original : Valuation.HasExtension vL vL' :=
    ⟨hLL'⟩
  have hrelative_residue_finite :
      FiniteDimensional (Chapter10ResidueField vL)
        (Chapter10ResidueField vL') := by
    have hfinite : FiniteDimensional (Chapter10ResidueField vLcomap)
        (Chapter10ResidueField vL') :=
      chapter10_residue_degree_finite vLcomap vL'
    let eSub : vL.valuationSubring ≃+* vLcomap.valuationSubring :=
      { toFun := fun x =>
          ⟨(x : L), by
            rw [← hrelative_subring]
            exact x.property⟩
        invFun := fun x =>
          ⟨(x : L), by
            rw [hrelative_subring]
            exact x.property⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl
        map_add' := by intro x y; rfl
        map_mul' := by intro x y; rfl }
    let eA : Chapter10ResidueField vLcomap ≃+*
        Chapter10ResidueField vL :=
      (IsLocalRing.ResidueField.mapEquiv eSub).symm
    let e : Chapter10ResidueField vL' ≃+*
        Chapter10ResidueField vL' := RingEquiv.refl _
    apply Module.Finite.of_equiv_equiv eA e
    apply RingHom.ext
    intro a
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective a
    simp [eA, e, eSub]
    apply congrArg (fun z : vL'.valuationSubring =>
      IsLocalRing.residue vL'.valuationSubring z)
    apply Subtype.ext
    rfl
  have hrelative_residue_pos : 0 < D.relativeData.residueDegree := by
    rw [D.relativeData.residueDegree_eq]
    exact Module.finrank_pos
  let vKcomap : Valuation K' ΓL' := vL'.comap (algebraMap K' L')
  have hchanged_subring : vK'.valuationSubring = vKcomap.valuationSubring :=
    (Valuation.isEquiv_iff_valuationSubring (v₁ := vK')
      (v₂ := vKcomap)).mp hL'
  have hchanged_extension : Valuation.HasExtension vKcomap vL' :=
    ⟨Valuation.IsEquiv.refl⟩
  have hchanged_extension_original : Valuation.HasExtension vK' vL' :=
    ⟨hL'⟩
  have hchanged_residue_finite :
      FiniteDimensional (Chapter10ResidueField vK')
        (Chapter10ResidueField vL') := by
    have hfinite : FiniteDimensional (Chapter10ResidueField vKcomap)
        (Chapter10ResidueField vL') :=
      chapter10_residue_degree_finite vKcomap vL'
    let eSub : vK'.valuationSubring ≃+* vKcomap.valuationSubring :=
      { toFun := fun x =>
          ⟨(x : K'), by
            rw [← hchanged_subring]
            exact x.property⟩
        invFun := fun x =>
          ⟨(x : K'), by
            rw [hchanged_subring]
            exact x.property⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl
        map_add' := by intro x y; rfl
        map_mul' := by intro x y; rfl }
    let eA : Chapter10ResidueField vKcomap ≃+*
        Chapter10ResidueField vK' :=
      (IsLocalRing.ResidueField.mapEquiv eSub).symm
    let e : Chapter10ResidueField vL' ≃+*
        Chapter10ResidueField vL' := RingEquiv.refl _
    apply Module.Finite.of_equiv_equiv eA e
    apply RingHom.ext
    intro a
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective a
    simp [eA, e, eSub]
    apply congrArg (fun z : vL'.valuationSubring =>
      IsLocalRing.residue vL'.valuationSubring z)
    apply Subtype.ext
    rfl
  have hchanged_residue_pos : 0 < D.changedData.residueDegree := by
    rw [D.changedData.residueDegree_eq]
    exact Module.finrank_pos
  have hinvariant := chapter10_unramified_base_change_invariant_square
    (vK := vK) (vL := vL) (vK' := vK') (vL' := vL')
    (hL := hL) (hK' := hK') (hL' := hL') (hLL' := hLL') (D := D)
  have hbase_ramification_one : D.baseData.ramificationIndex = 1 := by
    calc
      D.baseData.ramificationIndex = D.baseProfile.ramificationIndex :=
        hbase_ramification.symm
      _ = 1 := hbase_unramified_ramification
  have hbase_residue_degree :
      D.baseData.residueDegree = Module.finrank K K' := by
    calc
      D.baseData.residueDegree = D.baseProfile.residueDegree :=
        hbase_residue.symm
      _ = D.baseProfile.degree := hbase_unramified_residue
      _ = Module.finrank K K' := hbase_degree
  have hextension_ramification_degree :
      D.extensionData.ramificationIndex = Module.finrank K L := by
    calc
      D.extensionData.ramificationIndex = D.extensionProfile.ramificationIndex :=
        hextension_ramification.symm
      _ = D.extensionProfile.degree := htotal_ramification
      _ = Module.finrank K L := hextension_degree
  have hextension_residue_one : D.extensionData.residueDegree = 1 := by
    calc
      D.extensionData.residueDegree = D.extensionProfile.residueDegree :=
        hextension_residue.symm
      _ = 1 := htotal_residue
  have hrelative_residue_eq :
      D.relativeData.residueDegree =
        Module.finrank K K' * D.changedData.residueDegree := by
    calc
      D.relativeData.residueDegree = 1 * D.relativeData.residueDegree :=
        (Nat.one_mul _).symm
      _ = D.extensionData.residueDegree * D.relativeData.residueDegree := by
        rw [hextension_residue_one]
      _ = D.baseData.residueDegree * D.changedData.residueDegree :=
        hinvariant.2
      _ = Module.finrank K K' * D.changedData.residueDegree := by
        rw [hbase_residue_degree]
  have hrelative_residue_le :
      D.relativeData.residueDegree ≤ Module.finrank K K' := by
    calc
      D.relativeData.residueDegree = 1 * D.relativeData.residueDegree :=
        (Nat.one_mul _).symm
      _ ≤ D.relativeData.ramificationIndex * D.relativeData.residueDegree :=
        Nat.mul_le_mul_right _
          (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hrelative_ramification_pos))
      _ ≤ Module.finrank L L' :=
        chapter10_heterogeneous_single_extension_fundamental_inequality
          vL vL' hLL' D.relativeData
      _ = Module.finrank K K' := hdegree_rel
  have hchanged_residue_le_one : D.changedData.residueDegree ≤ 1 := by
    apply Nat.le_of_mul_le_mul_left
      (by simpa [Nat.mul_one] using
        (show Module.finrank K K' * D.changedData.residueDegree ≤
          Module.finrank K K' by
          rw [← hrelative_residue_eq]
          exact hrelative_residue_le))
    exact hbase_degree_pos
  have hchanged_residue_one : D.changedData.residueDegree = 1 :=
    Nat.le_antisymm hchanged_residue_le_one
      (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hchanged_residue_pos))
  have hrelative_residue_base :
      D.relativeData.residueDegree = Module.finrank K K' := by
    simpa [hchanged_residue_one] using hrelative_residue_eq
  have hrelative_ramification_le_one : D.relativeData.ramificationIndex ≤ 1 := by
    apply Nat.le_of_mul_le_mul_left
      (by simpa [Nat.mul_one] using
        (show Module.finrank K K' * D.relativeData.ramificationIndex ≤
          Module.finrank K K' by
          calc
            Module.finrank K K' * D.relativeData.ramificationIndex =
                D.relativeData.ramificationIndex * Module.finrank K K' := by
              rw [Nat.mul_comm]
            _ = D.relativeData.ramificationIndex * D.relativeData.residueDegree := by
              rw [hrelative_residue_base]
            _ ≤ Module.finrank L L' :=
              chapter10_heterogeneous_single_extension_fundamental_inequality
                vL vL' hLL' D.relativeData
            _ = Module.finrank K K' := hdegree_rel))
    exact hbase_degree_pos
  have hrelative_ramification_one : D.relativeData.ramificationIndex = 1 :=
    Nat.le_antisymm hrelative_ramification_le_one
      (Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt hrelative_ramification_pos))
  have hchanged_ramification_data :
      D.changedData.ramificationIndex = D.extensionData.ramificationIndex := by
    simpa [hbase_ramification_one, hrelative_ramification_one] using hinvariant.1.symm
  have hchanged_degree_profile :
      D.changedProfile.degree = D.extensionProfile.degree := by
    calc
      D.changedProfile.degree = Module.finrank K' L' := hchanged_profile_degree
      _ = Module.finrank K L := hbase_equiv_degree
      _ = D.extensionProfile.degree := hextension_degree.symm
  have hchanged_ramification_profile :
      D.changedProfile.ramificationIndex = D.extensionProfile.ramificationIndex := by
    calc
      D.changedProfile.ramificationIndex = D.changedData.ramificationIndex :=
        hchanged_profile_ramification
      _ = D.extensionData.ramificationIndex := hchanged_ramification_data
      _ = D.extensionProfile.ramificationIndex := hextension_ramification.symm
  have hchanged_residue_profile :
      D.changedProfile.residueDegree = D.extensionProfile.residueDegree := by
    calc
      D.changedProfile.residueDegree = D.changedData.residueDegree :=
        hchanged_profile_residue
      _ = 1 := hchanged_residue_one
      _ = D.extensionProfile.residueDegree := htotal_residue.symm
  exact ⟨D.baseProfile_unramified, hchanged_degree_profile,
    hchanged_ramification_profile, hchanged_residue_profile⟩

/-- Total ramification is preserved by the profile supplied by an unramified
base change. -/
theorem chapter10_total_ramification_preserved_under_unramified_base_change
    (base p p' : Chapter10FiniteExtensionProfile)
    (hbase : Chapter10UnramifiedBaseChangeProfile base p p')
    (htotal : Chapter10TotallyRamified p) :
    Chapter10TotallyRamified p' := by
  unfold Chapter10UnramifiedBaseChangeProfile at hbase
  unfold Chapter10TotallyRamified at htotal
  unfold Chapter10TotallyRamified
  rcases hbase with ⟨hbase_unram, hdeg, heram, hres⟩
  rcases htotal with ⟨htotal_e, htotal_f⟩
  constructor
  · calc
      p'.ramificationIndex = p.ramificationIndex := heram
      _ = p.degree := htotal_e
      _ = p'.degree := hdeg.symm
  · exact hres.trans htotal_f

/-- The Laurent-series valuation used in the equal-characteristic model. -/
def Chapter10LaurentSeriesValuation (k : Type*) [Field k] :
    Valuation (LaurentSeries k) ℤᵐ⁰ :=
  Valued.v

/-- Value of a power of the Laurent-series parameter. -/
theorem chapter10_laurent_series_parameter_value
    {k : Type*} [Field k] (n : ℕ) :
    Chapter10LaurentSeriesValuation k
        (((PowerSeries.X : PowerSeries k) : LaurentSeries k) ^ n) =
      WithZero.exp (-(n : ℤ)) := by
  exact LaurentSeries.valuation_X_pow k n

/-- The power polynomial is separable exactly away from the residue
characteristic divisors of its exponent. -/
theorem chapter10_power_polynomial_separable_iff
    {K : Type*} [Field K] {p n : ℕ} [CharP K p]
    (a : K) (hn : 0 < n) (ha : a ≠ 0) :
    (X ^ n - C a : K[X]).Separable ↔ ¬ p ∣ n := by
  rw [X_pow_sub_C_separable_iff hn ha]
  exact not_congr (CharP.cast_eq_zero_iff K p n)

/-- In a simple power extension, separability of the field extension is the
separability criterion for its defining power polynomial. -/
theorem chapter10_power_extension_separable_iff
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {p n : ℕ} [CharP K p] [FiniteDimensional K L]
    (a : K) (α : L) (hn : 0 < n) (ha : a ≠ 0)
    (hirreducible : Irreducible (X ^ n - C a : K[X]))
    (hroot : Polynomial.eval₂ (algebraMap K L) α (X ^ n - C a) = 0)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤) :
    Algebra.IsSeparable K L ↔ ¬ p ∣ n := by
  have hαroot : Polynomial.aeval α (X ^ n - C a : K[X]) = 0 := by
    simpa [Polynomial.aeval_def] using hroot
  have hαint : IsIntegral K α := by
    exact ⟨X ^ n - C a, monic_X_pow_sub_C a (Nat.ne_of_gt hn), hαroot⟩
  have hαalg : IsAlgebraic K α := hαint.isAlgebraic
  have htop : IntermediateField.adjoin K ({α} : Set L) = ⊤ := by
    exact (IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic hαalg).2 hgen
  have hminpoly : minpoly K α = X ^ n - C a := by
    exact (minpoly.eq_of_irreducible_of_monic hirreducible hαroot
      (monic_X_pow_sub_C a (Nat.ne_of_gt hn))).symm
  have hαsep : IsSeparable K α ↔ ¬ p ∣ n := by
    rw [IsSeparable, hminpoly, chapter10_power_polynomial_separable_iff a hn ha]
  constructor
  · intro hsep
    exact hαsep.mp (Algebra.IsSeparable.isSeparable K α)
  · intro hp
    have hsep_adjoin : Algebra.IsSeparable K (IntermediateField.adjoin K ({α} : Set L)) :=
      (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K L).2 (hαsep.mpr hp)
    have hsep_top : Algebra.IsSeparable K (⊤ : IntermediateField K L) := by
      rw [← htop]
      exact hsep_adjoin
    refine ⟨fun x => ?_⟩
    have hx : IsSeparable K (IntermediateField.topEquiv.symm x) :=
      Algebra.IsSeparable.isSeparable' (self := hsep_top) _
    simpa using (IntermediateField.topEquiv.isSeparable_iff.mpr hx)

/-- The extension k((u))/k((t)) with t = uⁿ has e = n and f = 1. -/
theorem chapter10_equal_characteristic_totally_ramified_profile
    {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L]
    [FiniteDimensional K L]
    (t : K) (u : L) (n : ℕ)
    (hn : 0 < n)
    (hparameter : Chapter10PowerParameterRelation t u n)
    (hirreducible : Irreducible (X ^ n - C t : K[X]))
    (hdegree : Module.finrank K L = n)
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hvK : Chapter10DiscreteAddValuation vK)
    (hvL : Chapter10DiscreteAddValuation vL)
    (hext : vK.IsEquiv (vL.comap (algebraMap K L)))
    (ht : vK t = 1) (hu : vL u = 1) :
    ∃ d : Chapter10HeterogeneousExtensionData vK vL hext,
      ∃ p : Chapter10FiniteExtensionProfile,
        Chapter10ProfileRealizedByData d p ∧
          p.degree = n ∧ p.ramificationIndex = n ∧ p.residueDegree = 1 ∧
          Chapter10TotallyRamified p := by
  obtain ⟨d⟩ := chapter10_heterogeneous_extension_data_exists
    vK.toValuation vL.toValuation hext
  refine ⟨d, { degree := n, ramificationIndex := n, residueDegree := 1 }, ?_⟩
  have ht0 : t ≠ 0 := by
    intro ht0
    rw [ht0, vK.map_zero] at ht
    simp at ht
  obtain ⟨e, he, hscale⟩ :=
    chapter10_normalized_restriction_formula vK vL hvK hvL hext
  have heq : e = n := by
    have hval : (e : WithTop ℤ) = (n : WithTop ℤ) := by
      calc
        (e : WithTop ℤ) = e • (1 : WithTop ℤ) := by simp
        _ = e • vK t := by rw [ht]
        _ = vL (algebraMap K L t) := (hscale t ht0).symm
        _ = vL (u ^ n) := by rw [hparameter]
        _ = n • vL u := by rw [vL.map_pow]
        _ = n • (1 : WithTop ℤ) := by rw [hu]
        _ = (n : WithTop ℤ) := by simp
    exact_mod_cast hval
  have hram : d.ramificationIndex = n := by
    have hri := @chapter10_normalized_ramification_index_eq_scale K L _ _ _ _
      vK vL hvK hvL hext d n hn (by
        intro x hx
        simpa [heq] using hscale x hx) d.finite_quotient
    exact hri.2
  have hrespos : 0 < d.residueDegree := by
    rw [d.residueDegree_eq]
    let : Valuation.HasExtension vK.toValuation vL.toValuation := ⟨hext⟩
    let : FiniteDimensional (Chapter10ResidueField vK.toValuation)
        (Chapter10ResidueField vL.toValuation) :=
      chapter10_residue_degree_finite vK.toValuation vL.toValuation
    exact Module.finrank_pos
  have hineq := chapter10_heterogeneous_single_extension_fundamental_inequality
    vK.toValuation vL.toValuation hext d
  have hres : d.residueDegree = 1 := by
    have hle : n * d.residueDegree ≤ n := by
      simpa [hram, hdegree] using hineq
    have hle' : d.residueDegree ≤ 1 := by
      apply Nat.le_of_mul_le_mul_left
        (by simpa [Nat.mul_one] using hle)
      exact hn
    exact Nat.le_antisymm hle' (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hrespos))
  by_cases hpoly : (X ^ n - C t : K[X]) = 0
  · exact (hirreducible.ne_zero hpoly).elim
  · simp [Chapter10ProfileRealizedByData, Chapter10TotallyRamified,
      hdegree, hram, hres]

/-- Constants identify the residue field of a Laurent-series valuation with
the coefficient field. -/
noncomputable def Chapter10LaurentSeriesResidueRingEquiv
    (F : Type*) [Field F] :
    F ≃+* Chapter10ResidueField (Chapter10LaurentSeriesValuation F) := by
  let c : F →+* (Chapter10LaurentSeriesValuation F).valuationSubring :=
    (algebraMap F (LaurentSeries F)).codRestrict _ (by
      intro a
      rw [Valuation.mem_valuationSubring_iff]
      change Valued.v (algebraMap F (LaurentSeries F) a) ≤ 1
      rw [LaurentSeries.val_le_one_iff_eq_coe]
      exact ⟨PowerSeries.C a, by
        simp [HahnSeries.algebraMap_apply', PowerSeries.C_eq_algebraMap]⟩)
  have hc (a : F) : c a =
      ⟨algebraMap F (LaurentSeries F) a, by
        rw [Valuation.mem_valuationSubring_iff]
        change Valued.v (algebraMap F (LaurentSeries F) a) ≤ 1
        rw [LaurentSeries.val_le_one_iff_eq_coe]
        exact ⟨PowerSeries.C a, by
          simp [HahnSeries.algebraMap_apply', PowerSeries.C_eq_algebraMap]⟩⟩ := by
    rfl
  let cr : F →+* Chapter10ResidueField (Chapter10LaurentSeriesValuation F) :=
    (IsLocalRing.residue _).comp c
  have hconst_coe (a : F) :
      algebraMap F (LaurentSeries F) a = (PowerSeries.C a : LaurentSeries F) := by
    simp [HahnSeries.algebraMap_apply', PowerSeries.C_eq_algebraMap]
  have hconst (a : F) (ha : a ≠ 0) :
      Chapter10LaurentSeriesValuation F (algebraMap F (LaurentSeries F) a) = 1 := by
    have hmul : c a * c a⁻¹ = 1 := by
      apply Subtype.ext
      change algebraMap F (LaurentSeries F) a *
        algebraMap F (LaurentSeries F) a⁻¹ = 1
      rw [← map_mul, mul_inv_cancel₀ ha, map_one]
    let ua := Units.mkOfMulEqOne (c a) (c a⁻¹) hmul
    have hu : IsUnit (c a) :=
      ⟨ua, Units.val_mkOfMulEqOne hmul⟩
    have hval := ((Chapter10LaurentSeriesValuation F).valuationSubring.valuation_eq_one_iff
      (c a)).mp hu
    exact (Valuation.isEquiv_valuation_valuationSubring
      (Chapter10LaurentSeriesValuation F)).eq_one_iff_eq_one.mpr (by
        simpa [hc] using hval)
  have hcoeff (G : PowerSeries F) (n : ℤ) (hn : n < 1) :
      ((G : LaurentSeries F) -
          algebraMap F (LaurentSeries F) (PowerSeries.constantCoeff G)).coeff n = 0 := by
    rw [hconst_coe, HahnSeries.coeff_sub]
    obtain n | n := n
    · have hn' : (n : ℤ) < (1 : ℤ) := by simpa using hn
      have hnlt : n < 1 := Int.ofNat_lt.mp hn'
      have hn0z : (n : ℤ) = 0 := by omega
      have hn0 : n = 0 := by exact_mod_cast hn0z
      subst n
      rw [Int.ofNat_eq_natCast, LaurentSeries.coeff_coe_powerSeries]
      rw [LaurentSeries.coeff_coe_powerSeries]
      simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    · change ((G : LaurentSeries F).coeff (Int.negSucc n) -
        (PowerSeries.C (PowerSeries.constantCoeff G) : LaurentSeries F).coeff
          (Int.negSucc n)) = 0
      simp [PowerSeries.coeff_coe]
  have hcr_surj : Function.Surjective cr := by
    intro y
    obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective y
    have hsval : Valued.v (s : LaurentSeries F) ≤ 1 := by
      exact (Valuation.mem_valuationSubring_iff
        (Chapter10LaurentSeriesValuation F) (s : LaurentSeries F)).mp s.property
    obtain ⟨G, hG⟩ :=
      (LaurentSeries.val_le_one_iff_eq_coe F (s : LaurentSeries F)).mp hsval
    have hsmall : Valued.v
        ((s : LaurentSeries F) -
          algebraMap F (LaurentSeries F) (PowerSeries.constantCoeff G)) ≤
        WithZero.exp (-(1 : ℤ)) := by
      apply (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero F).mpr
      intro n hn
      rw [← hG]
      exact hcoeff G n hn
    have hlt : Valued.v
        ((s : LaurentSeries F) -
          algebraMap F (LaurentSeries F) (PowerSeries.constantCoeff G)) < 1 := by
      apply lt_of_le_of_lt hsmall
      simpa only [← WithZero.exp_zero, WithZero.exp_lt_exp] using
        (show (-(1 : ℤ)) < 0 by norm_num)
    have hmem : s - c (PowerSeries.constantCoeff G) ∈
        IsLocalRing.maximalIdeal (Chapter10LaurentSeriesValuation F).valuationSubring := by
      apply (Valuation.mem_maximalIdeal_iff (K := LaurentSeries F)
        (Chapter10LaurentSeriesValuation F)).2
      change Valued.v
          ((s : LaurentSeries F) -
            algebraMap F (LaurentSeries F) (PowerSeries.constantCoeff G)) < 1
      exact hlt
    have hzero := (IsLocalRing.residue_eq_zero_iff _).mpr hmem
    rw [map_sub] at hzero
    refine ⟨PowerSeries.constantCoeff G, ?_⟩
    change IsLocalRing.residue _ (c (PowerSeries.constantCoeff G)) =
      IsLocalRing.residue _ s
    exact (sub_eq_zero.mp hzero).symm
  have hcr_inj : Function.Injective cr := by
    intro a b hab
    have hzero : cr (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    have hmem : c (a - b) ∈
        IsLocalRing.maximalIdeal (Chapter10LaurentSeriesValuation F).valuationSubring := by
      apply (IsLocalRing.residue_eq_zero_iff _).mp
      simpa [cr] using hzero
    have hlt : Chapter10LaurentSeriesValuation F
        (algebraMap F (LaurentSeries F) (a - b)) < 1 := by
      have hlt' := (Valuation.mem_maximalIdeal_iff (K := LaurentSeries F)
        (Chapter10LaurentSeriesValuation F)).mp hmem
      simpa [hc] using hlt'
    by_contra habne
    exact (ne_of_lt hlt) (hconst (a - b) (sub_ne_zero.mpr habne))
  exact RingEquiv.ofBijective cr ⟨hcr_inj, hcr_surj⟩

/-! Constant-field extensions have the numerical profile e = 1 and
f = [k' : k] without a separability hypothesis.  The separable refinement
below additionally identifies the branch as intrinsically unramified. -/
theorem chapter10_constant_field_extension_numerical_profile
    {k k' : Type*} [Field k] [Field k'] [Algebra k k'] [FiniteDimensional k k']
    [Algebra (LaurentSeries k) (LaurentSeries k')]
    [FiniteDimensional (LaurentSeries k) (LaurentSeries k')]
    [IsScalarTower k (LaurentSeries k) (LaurentSeries k')]
    (hparameter :
      algebraMap (LaurentSeries k) (LaurentSeries k')
          (((PowerSeries.X : PowerSeries k) : LaurentSeries k)) =
        ((PowerSeries.X : PowerSeries k') : LaurentSeries k'))
    (h : (Chapter10LaurentSeriesValuation k).IsEquiv
      ((Chapter10LaurentSeriesValuation k').comap
        (algebraMap (LaurentSeries k) (LaurentSeries k')))) :
    ∃ d : Chapter10HeterogeneousExtensionData
        (Chapter10LaurentSeriesValuation k)
        (Chapter10LaurentSeriesValuation k') h,
      ∃ p : Chapter10FiniteExtensionProfile,
        Chapter10ProfileRealizedByData d p ∧
          p.degree = Module.finrank k k' ∧ p.ramificationIndex = 1 ∧
          p.residueDegree = Module.finrank k k' ∧ Chapter10Unramified p := by
  obtain ⟨d⟩ := chapter10_heterogeneous_extension_data_exists
    (Chapter10LaurentSeriesValuation k)
    (Chapter10LaurentSeriesValuation k') h
  let Xk : LaurentSeries k :=
    ((PowerSeries.X : PowerSeries k) : LaurentSeries k)
  let Xk' : LaurentSeries k' :=
    ((PowerSeries.X : PowerSeries k') : LaurentSeries k')
  have hXk_value : Chapter10LaurentSeriesValuation k Xk =
      WithZero.exp (-(1 : ℤ)) := by
    simpa [Xk] using chapter10_laurent_series_parameter_value (k := k) 1
  have hXk'_value : Chapter10LaurentSeriesValuation k' Xk' =
      WithZero.exp (-(1 : ℤ)) := by
    simpa [Xk'] using chapter10_laurent_series_parameter_value (k := k') 1
  have hXk : Chapter10LaurentSeriesValuation k Xk ≠ 0 := by
    rw [hXk_value]
    simp
  have hXk' : Chapter10LaurentSeriesValuation k' Xk' ≠ 0 := by
    rw [hXk'_value]
    simp
  let g : Chapter10ValueGroup (Chapter10LaurentSeriesValuation k) :=
    Chapter10ValueGroupGenerator (Chapter10LaurentSeriesValuation k) Xk hXk
  let g' : Chapter10ValueGroup (Chapter10LaurentSeriesValuation k') :=
    Chapter10ValueGroupGenerator (Chapter10LaurentSeriesValuation k') Xk' hXk'
  have hgenmap : d.valueGroupMap g = g' := by
    dsimp [g, g']
    apply Subtype.ext
    rw [d.valueGroupMap_spec Xk hXk]
    congr 1
    rw [hparameter]
  have hsurj : Function.Surjective d.valueGroupMap := by
    intro u
    let n : ℤ := -WithZero.log (u.1 : ℤᵐ⁰)
    have hu : u = g' ^ n := by
      dsimp [g']
      apply Subtype.ext
      apply Units.ext
      simp [Chapter10ValueGroupGenerator, Units.val_zpow_eq_zpow_val]
      rw [hXk'_value]
      rw [← WithZero.exp_zsmul]
      simp [n, WithZero.exp_log (u.1.ne_zero)]
    refine ⟨g ^ n, ?_⟩
    rw [map_zpow, hgenmap, hu]
  let : Valuation.HasExtension (Chapter10LaurentSeriesValuation k)
      (Chapter10LaurentSeriesValuation k') := ⟨h⟩
  have hresdegree : d.residueDegree = Module.finrank k k' := by
    rw [d.residueDegree_eq]
    symm
    apply Algebra.finrank_eq_of_equiv_equiv
      (Chapter10LaurentSeriesResidueRingEquiv k)
      (Chapter10LaurentSeriesResidueRingEquiv k')
    apply RingHom.ext
    intro a
    have htower : IsScalarTower k (LaurentSeries k) (LaurentSeries k') :=
      inferInstance
    have hAlgebraTower :
        @IsScalarTower k (LaurentSeries k) (LaurentSeries k')
          (inferInstance : Algebra k (LaurentSeries k)).toSMul
          (inferInstance : Algebra (LaurentSeries k) (LaurentSeries k')).toSMul
          (inferInstance : Algebra k (LaurentSeries k')).toSMul := by
      apply IsScalarTower.of_algebraMap_eq
      intro r
      have hs := htower.smul_assoc r (1 : LaurentSeries k) (1 : LaurentSeries k')
      have hrS : r • (1 : LaurentSeries k) =
          algebraMap k (LaurentSeries k) r := by
        rw [← HahnSeries.C_mul_eq_smul, mul_one]
        exact (LaurentSeries.algebraMap_apply k r).symm
      have hrA : r • (1 : LaurentSeries k') =
          algebraMap k (LaurentSeries k') r := by
        rw [HahnSeries.algebraMap_apply']
        ext n
        cases n <;> simp [Algebra.smul_def, HahnSeries.coeff_single,
          PowerSeries.algebraMap_apply]
      calc
        algebraMap k (LaurentSeries k') r = r • (1 : LaurentSeries k') := hrA.symm
        _ = (r • (1 : LaurentSeries k)) • (1 : LaurentSeries k') := by
          simpa only [one_smul] using hs.symm
        _ = algebraMap (LaurentSeries k) (LaurentSeries k')
            (r • (1 : LaurentSeries k)) := by
          rw [Algebra.smul_def, mul_one]
        _ = algebraMap (LaurentSeries k) (LaurentSeries k')
            (algebraMap k (LaurentSeries k) r) := by rw [hrS]
    have hscalar :
        algebraMap k (LaurentSeries k') a =
          algebraMap k' (LaurentSeries k') (algebraMap k k' a) := by
      change HahnSeries.ofPowerSeries ℤ k' (algebraMap k (PowerSeries k') a) =
        HahnSeries.ofPowerSeries ℤ k' (PowerSeries.C (algebraMap k k' a))
      congr 1
      ext n
      cases n <;> simp [PowerSeries.algebraMap_apply]
    rw [RingHom.comp_apply, RingHom.comp_apply]
    change IsLocalRing.residue _ _ = IsLocalRing.residue _ _
    congr 1
    apply Subtype.ext
    calc
      algebraMap (LaurentSeries k) (LaurentSeries k')
          (algebraMap k (LaurentSeries k) a) =
          algebraMap k (LaurentSeries k') a :=
        (@IsScalarTower.algebraMap_apply k (LaurentSeries k)
          (LaurentSeries k') _ _ _ _ _ _ hAlgebraTower a).symm
      _ = algebraMap k' (LaurentSeries k') (algebraMap k k' a) :=
        hscalar
  have hvalue_range : d.valueGroupMap.range = ⊤ := by
    apply top_unique
    intro u hu
    obtain ⟨x, hx⟩ := hsurj u
    exact ⟨x, hx⟩
  have hram : d.ramificationIndex = 1 := by
    rw [d.ramificationIndex_eq, hvalue_range]
    simp
  let p : Chapter10FiniteExtensionProfile :=
    { degree := Module.finrank (LaurentSeries k) (LaurentSeries k'),
      ramificationIndex := 1, residueDegree := Module.finrank k k' }
  have hdegree : Module.finrank (LaurentSeries k) (LaurentSeries k') =
      Module.finrank k k' := by
    sorry
  refine ⟨d, p, ?_⟩
  refine ⟨?_, hdegree, rfl, rfl, ?_⟩
  · simp [p, Chapter10ProfileRealizedByData, hram, hresdegree]
  · simp [p, Chapter10Unramified, hdegree]

/-! Constant-field extensions have e = 1 and residue degree equal to the field degree. -/
theorem chapter10_constant_field_extension_profile
    {k k' : Type*} [Field k] [Field k'] [Algebra k k'] [FiniteDimensional k k']
    [Algebra (LaurentSeries k) (LaurentSeries k')]
    [FiniteDimensional (LaurentSeries k) (LaurentSeries k')]
    [IsScalarTower k (LaurentSeries k) (LaurentSeries k')]
    (hparameter :
      algebraMap (LaurentSeries k) (LaurentSeries k')
          (((PowerSeries.X : PowerSeries k) : LaurentSeries k)) =
        ((PowerSeries.X : PowerSeries k') : LaurentSeries k'))
    (hseparable : Algebra.IsSeparable k k')
    (h : (Chapter10LaurentSeriesValuation k).IsEquiv
      ((Chapter10LaurentSeriesValuation k').comap
        (algebraMap (LaurentSeries k) (LaurentSeries k')))) :
    ∃ d : Chapter10HeterogeneousExtensionData
        (Chapter10LaurentSeriesValuation k)
        (Chapter10LaurentSeriesValuation k') h,
      ∃ p : Chapter10FiniteExtensionProfile,
        Chapter10ProfileRealizedByData d p ∧
          p.degree = Module.finrank k k' ∧ p.ramificationIndex = 1 ∧
          p.residueDegree = Module.finrank k k' ∧ Chapter10Unramified p ∧
          Chapter10UnramifiedBranch
            (Chapter10LaurentSeriesValuation k)
            (Chapter10LaurentSeriesValuation k') h d := by
  sorry

/-- Combining a constant extension and a totally ramified extension gives ef. -/
theorem chapter10_combined_equal_characteristic_profile
    {e f : ℕ} {K L ΓK ΓL : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓL] [FiniteDimensional K L]
    (v : Valuation K ΓK) (w : Valuation L ΓL)
    (h : v.IsEquiv (w.comap (algebraMap K L)))
    (d : Chapter10HeterogeneousExtensionData v w h)
    (he : 0 < e) (hf : 0 < f)
    (hdegree : Module.finrank K L = e * f)
    (heq : d.ramificationIndex = e) (hfq : d.residueDegree = f) :
    ∃ p : Chapter10FiniteExtensionProfile,
      Chapter10ProfileRealizedByData d p ∧ p.degree = e * f ∧
        p.ramificationIndex = e ∧ p.residueDegree = f := by
  refine ⟨{ degree := e * f, ramificationIndex := e, residueDegree := f }, ?_⟩
  have hprod : 0 < e * f := Nat.mul_pos he hf
  have hprod_ne : e * f ≠ 0 := Nat.ne_of_gt hprod
  have hprod_eq : (if e * f = 0 then 0 else e * f) = e * f := if_neg hprod_ne
  rw [← hprod_eq]
  simp [Chapter10ProfileRealizedByData, hdegree, heq, hfq]

/-- A local polynomial criterion spelling out the Eisenstein coefficient conditions. -/
def Chapter10EisensteinAtUniformizer {A : Type*} [CommRing A]
    (P : A[X]) (π : A) : Prop :=
  P.Monic ∧ P.natDegree ≠ 0 ∧
    (∀ i < P.natDegree, π ∣ P.coeff i) ∧
    ¬ π ^ 2 ∣ P.constantCoeff

/-- Eisenstein irreducibility. -/
theorem chapter10_eisenstein_irreducible
    {A : Type*} [CommRing A] [IsDomain A]
    (P : A[X]) (π : A) (hπ : Prime π)
    (hE : Chapter10EisensteinAtUniformizer P π) :
    Irreducible P := by
  rcases hE with ⟨hmonic, hdegree, hcoeff, hconstant⟩
  let p : Ideal A := Ideal.span ({π} : Set A)
  have hp : p.IsPrime := Ideal.isPrime_span_singleton_of_prime hπ
  have hleading : P.leadingCoeff ∉ p := by
    rw [hmonic.leadingCoeff]
    exact (Ideal.ne_top_iff_one p).mp hp.ne_top
  have hcoeff' : ∀ i < P.natDegree, P.coeff i ∈ p := by
    intro i hi
    exact Ideal.mem_span_singleton.mpr (hcoeff i hi)
  have hconstant' : P.coeff 0 ∉ p ^ 2 := by
    intro h
    apply hconstant
    rw [Ideal.span_singleton_pow] at h
    exact Ideal.mem_span_singleton.mp h
  have hdegree' : 0 < P.degree := by
    exact Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdegree)
  apply Polynomial.irreducible_of_eisenstein_criterion hp hleading
    (fun i hi => hcoeff' i (Polynomial.coe_lt_degree.mp hi)) hdegree' hconstant'
  exact hmonic.isPrimitive

/-- The minimal-value comparison for an Eisenstein root. -/
theorem chapter10_eisenstein_root_value_comparison
    {A L : Type*} [CommRing A] [IsDomain A] [Field L]
    [Algebra A L]
    (vL : AddValuation L (WithTop ℤ))
    (P : A[X]) (π : A) (α : L) (n : ℕ)
    (hroot : Polynomial.eval₂ (algebraMap A L) α P = 0)
    (hdegree : P.natDegree = n)
    (hE : Chapter10EisensteinAtUniformizer P π)
    (hπ : 0 < vL (algebraMap A L π))
    (hconstant : vL (algebraMap A L P.constantCoeff) =
      vL (algebraMap A L π))
    (hcoeff : ∀ i < n,
      vL (algebraMap A L (P.coeff i)) ≥ vL (algebraMap A L π)) :
    n • vL α = vL (algebraMap A L π) := by
  rcases hE with ⟨hmonic, hdegree0, _hcoeffdiv, _hconstantdiv⟩
  have hn : 0 < n := by
    rw [← hdegree]
    exact Nat.pos_of_ne_zero hdegree0
  have hdeg_lt : P.natDegree < n + 1 := by
    rw [hdegree]
    exact Nat.lt_succ_self n
  let term : ℕ → L := fun i =>
    algebraMap A L (P.coeff i) * α ^ i
  have hsum : (∑ i ∈ Finset.range (n + 1), term i) = 0 := by
    rw [← Polynomial.eval₂_eq_sum_range' (algebraMap A L) hdeg_lt α]
    exact hroot
  have hcoeff_n : P.coeff n = 1 := by
    rw [← hdegree]
    exact hmonic.leadingCoeff
  by_cases hc_top : vL (algebraMap A L π) = ⊤
  · have hterm_low : ∀ i < n, term i = 0 := by
      intro i hi
      dsimp [term]
      have hi_top : vL (algebraMap A L (P.coeff i)) = ⊤ := by
        apply top_unique
        simpa [hc_top] using hcoeff i hi
      rw [(AddValuation.top_iff vL).mp hi_top]
      simp
    have hsum' := hsum
    rw [Finset.sum_range_succ] at hsum'
    have hsum_low : (∑ i ∈ Finset.range n, term i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact hterm_low i (Finset.mem_range.mp hi)
    rw [hsum_low, zero_add] at hsum'
    have hpow : α ^ n = 0 := by
      simpa [term, hcoeff_n] using hsum'
    have hα : α = 0 := (pow_eq_zero_iff hn.ne').mp hpow
    rw [hα, AddValuation.map_zero, hc_top]
    rcases Nat.exists_eq_succ_of_ne_zero hn.ne' with ⟨k, rfl⟩
    simp [succ_nsmul]
  · have hπtop : vL (algebraMap A L π) ≠ ⊤ := hc_top
    have hα0 : α ≠ 0 := by
      intro hα0
      have hroot0 : Polynomial.eval₂ (algebraMap A L) 0 P = 0 := by
        simpa [hα0] using hroot
      have hconstL : algebraMap A L P.constantCoeff = 0 := by
        simpa using hroot0
      have hconstVal : vL (algebraMap A L P.constantCoeff) = ⊤ := by
        rw [hconstL, AddValuation.map_zero]
      have hπ_top : vL (algebraMap A L π) = ⊤ := by
        calc
          vL (algebraMap A L π) = vL (algebraMap A L P.constantCoeff) :=
            hconstant.symm
          _ = ⊤ := hconstVal
      exact hπtop hπ_top
    have hαtop : vL α ≠ ⊤ := (AddValuation.ne_top_iff vL).mpr hα0
    have hterm_val (i : ℕ) :
        vL (term i) = vL (algebraMap A L (P.coeff i)) + i • vL α := by
      simp [term, AddValuation.map_mul, AddValuation.map_pow]
    have hterm_n : term n = α ^ n := by
      dsimp [term]
      rw [hcoeff_n]
      simp
    have hterm_n_val : vL (term n) = n • vL α := by
      rw [hterm_n, AddValuation.map_pow]
    have hsmul_top (k : ℕ) : k • vL α ≠ ⊤ := by
      obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hαtop
      rw [← ha, ← WithTop.coe_nsmul]
      exact WithTop.coe_ne_top
    have hterm_n_top : vL (term n) ≠ ⊤ := by
      rw [hterm_n_val]
      exact hsmul_top n
    have hterm_zero_val : vL (term 0) = vL (algebraMap A L π) := by
      rw [hterm_val]
      simpa [hconstant, add_zero]
    have hterm_zero_top : vL (term 0) ≠ ⊤ := by
      rw [hterm_zero_val]
      exact hπtop
    have hunique_min {j : ℕ} (hj : j ∈ Finset.range (n + 1))
        (hstrict : ∀ i ∈ Finset.range (n + 1) \ {j},
          vL (term j) < vL (term i))
        (hjtop : vL (term j) ≠ ⊤) : False := by
      have hv := (AddValuation.toValuation vL).map_sum_eq_of_lt hj (by
        intro i hi
        have hdual : OrderDual.toDual (vL (term i)) <
            OrderDual.toDual (vL (term j)) :=
          OrderDual.toDual_lt_toDual.mpr (hstrict i hi)
        simpa only [AddValuation.toValuation_apply] using
          (Multiplicative.ofAdd_lt.mpr hdual)
        : ∀ i ∈ Finset.range (n + 1) \ {j},
            AddValuation.toValuation vL (term i) <
              AddValuation.toValuation vL (term j))
      simp only [AddValuation.toValuation_apply] at hv
      change OrderDual.toDual (vL (∑ i ∈ Finset.range (n + 1), term i)) =
        OrderDual.toDual (vL (term j)) at hv
      have hv' : vL (∑ i ∈ Finset.range (n + 1), term i) = vL (term j) := by
        simpa using hv
      rw [hsum, AddValuation.map_zero] at hv'
      exact hjtop hv'.symm
    have hαpos : 0 < vL α := by
      by_contra hαpos
      have hαnonpos : vL α ≤ 0 := le_of_not_gt hαpos
      apply hunique_min (j := n) (Finset.mem_range.mpr (Nat.lt_succ_self n)) ?_
        hterm_n_top
      intro i hi
      have hi_lt : i < n := by
        have hi_le : i ≤ n := by
          have hi_succ : i < n + 1 :=
            Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1
          omega
        exact Nat.lt_of_le_of_ne hi_le (by
          intro hin
          exact (Finset.mem_sdiff.mp hi).2 (by simp [hin]))
      have hni : i ≤ n := Nat.le_of_lt hi_lt
      have hna : n • vL α ≤ i • vL α := by
        rw [← Nat.add_sub_of_le hni, add_nsmul]
        exact add_le_of_nonpos_right (nsmul_nonpos hαnonpos _)
      have hia0 : i • vL α <
          vL (algebraMap A L π) + i • vL α := by
        have hi_top : i • vL α ≠ ⊤ := hsmul_top i
        simpa using WithTop.add_lt_add_right hi_top hπ
      have hci := hcoeff i hi_lt
      have hia : i • vL α <
          vL (algebraMap A L (P.coeff i)) + i • vL α :=
        hia0.trans_le (by
          have h := add_le_add_left hci (i • vL α)
          simpa [add_comm] using h)
      calc
        vL (term n) = n • vL α := hterm_n_val
        _ < vL (algebraMap A L (P.coeff i)) + i • vL α := hna.trans_lt hia
        _ = vL (term i) := (hterm_val i).symm
    have hEq : n • vL α = vL (algebraMap A L π) := by
      rcases lt_trichotomy (n • vL α) (vL (algebraMap A L π)) with hlt | heq | hgt
      · exfalso
        apply hunique_min (j := n) (Finset.mem_range.mpr (Nat.lt_succ_self n)) ?_
          hterm_n_top
        intro i hi
        have hi_lt : i < n := by
          have hi_le : i ≤ n := by
            have hi_succ : i < n + 1 :=
              Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1
            omega
          exact Nat.lt_of_le_of_ne hi_le (by
            intro hin
            exact (Finset.mem_sdiff.mp hi).2 (by simp [hin]))
        have hia : (0 : WithTop ℤ) ≤ i • vL α :=
          nsmul_nonneg (le_of_lt hαpos) i
        have hci := hcoeff i hi_lt
        calc
          vL (term n) = n • vL α := hterm_n_val
          _ < vL (algebraMap A L π) := hlt
          _ ≤ vL (algebraMap A L (P.coeff i)) := hci
          _ ≤ vL (algebraMap A L (P.coeff i)) + i • vL α :=
            le_add_of_nonneg_right hia
          _ = vL (term i) := (hterm_val i).symm
      · exact heq
      · exfalso
        apply hunique_min (j := 0) (Finset.mem_range.mpr (Nat.zero_lt_succ n)) ?_
          hterm_zero_top
        intro i hi
        have hi_pos : 0 < i := by
          have hi_ne : i ≠ 0 := by simpa using (Finset.mem_sdiff.mp hi).2
          exact Nat.pos_of_ne_zero hi_ne
        by_cases hi_n : i = n
        · subst i
          rw [hterm_n_val, hterm_zero_val]
          exact hgt
        · have hi_lt : i < n := by
            have hi_le : i ≤ n := by
              have hi_succ : i < n + 1 :=
                Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1
              omega
            exact Nat.lt_of_le_of_ne hi_le hi_n
          have hia : (0 : WithTop ℤ) < i • vL α := by
            exact nsmul_pos hαpos hi_pos.ne'
          have hci := hcoeff i hi_lt
          have hia0 : vL (algebraMap A L π) <
              vL (algebraMap A L π) + i • vL α := by
            simpa using WithTop.add_lt_add_left hπtop hia
          calc
            vL (term 0) = vL (algebraMap A L π) := hterm_zero_val
            _ < vL (algebraMap A L π) + i • vL α := hia0
            _ ≤ vL (algebraMap A L (P.coeff i)) + i • vL α := by
              have h := add_le_add_left hci (i • vL α)
              simpa [add_comm] using h
            _ = vL (term i) := (hterm_val i).symm
    exact hEq

/-- Eisenstein extensions are totally ramified of the polynomial degree. -/
theorem chapter10_eisenstein_totally_ramified_profile
    {A K L : Type*} [CommRing A] [IsDomain A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [IsDiscreteValuationRing A] [IsFractionRing A K]
    [FiniteDimensional K L]
    (P : A[X]) (π : A) (α : L)
    (hE : Chapter10EisensteinAtUniformizer P π)
    (hroot : Polynomial.eval₂ (algebraMap A L) α P = 0)
    (_hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (hdegree : Module.finrank K L = P.natDegree)
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hvK : Chapter10DiscreteAddValuation vK)
    (hvL : Chapter10DiscreteAddValuation vL)
    (hext : vK.IsEquiv (vL.comap (algebraMap K L)))
    (hA : vK.Integers A)
    (hπ : vK (algebraMap A K π) = 1) :
    ∃ d : Chapter10HeterogeneousExtensionData vK vL hext,
      ∃ p : Chapter10FiniteExtensionProfile,
        Chapter10ProfileRealizedByData d p ∧
          p.degree = P.natDegree ∧ p.ramificationIndex = P.natDegree ∧
          p.residueDegree = 1 ∧ Chapter10TotallyRamified p := by
  classical
  rcases hE with ⟨hmonic, hdegree0, hcoeffdiv, hconstantdiv⟩
  have hnonneg (a : A) : 0 ≤ vK (algebraMap A K a) := by
    have ha := hA.map_le_one a
    change Multiplicative.ofAdd (OrderDual.toDual (vK (algebraMap A K a))) ≤
      Multiplicative.ofAdd (OrderDual.toDual (0 : WithTop ℤ)) at ha
    have ha' : OrderDual.toDual (vK (algebraMap A K a)) ≤
        OrderDual.toDual (0 : WithTop ℤ) :=
      (Multiplicative.ofAdd_le).mp ha
    exact OrderDual.toDual_le_toDual.mp ha'
  obtain ⟨d⟩ := chapter10_heterogeneous_extension_data_exists
    vK.toValuation vL.toValuation hext
  obtain ⟨e, he, hscale⟩ :=
    chapter10_normalized_restriction_formula vK vL hvK hvL hext
  have hn : 0 < P.natDegree := Nat.pos_of_ne_zero hdegree0
  have hπK0 : algebraMap A K π ≠ 0 := by
    intro hzero
    rw [hzero] at hπ
    simp at hπ
  have hπA0 : π ≠ 0 := by
    intro hzero
    apply hπK0
    simp [hzero]
  have hπL0 : algebraMap A L π ≠ 0 := by
    simpa [IsScalarTower.algebraMap_apply A K L] using
      (RingHom.injective (algebraMap K L)).ne hπK0
  have hle_one (x : K) (hx : 0 ≤ vK x) : vK.toValuation x ≤ 1 := by
    change Multiplicative.ofAdd (OrderDual.toDual (vK x)) ≤
      Multiplicative.ofAdd (OrderDual.toDual (0 : WithTop ℤ))
    exact (Multiplicative.ofAdd_le).mpr (OrderDual.toDual_le_toDual.mpr hx)
  have hcoeffK : ∀ i < P.natDegree,
      1 ≤ vK (algebraMap A K (P.coeff i)) := by
    intro i hi
    obtain ⟨c, hc⟩ := hcoeffdiv i hi
    rw [hc, map_mul, vK.map_mul, hπ]
    exact le_add_of_nonneg_right (hnonneg c)
  have hcoeffL : ∀ i < P.natDegree,
      vL (algebraMap A L (P.coeff i)) ≥ vL (algebraMap A L π) := by
    intro i hi
    by_cases hc0 : P.coeff i = 0
    · simp [hc0]
    · have hcK0 : algebraMap A K (P.coeff i) ≠ 0 := by
        intro hzero
        apply hc0
        apply hA.hom_inj
        simpa using hzero
      have hscoeff := hscale (algebraMap A K (P.coeff i)) hcK0
      have hsπ := hscale (algebraMap A K π) hπK0
      rw [IsScalarTower.algebraMap_apply A K L, hscoeff,
        IsScalarTower.algebraMap_apply A K L, hsπ, hπ]
      exact nsmul_le_nsmul_right (hcoeffK i hi) e
  have hconst0 : P.constantCoeff ≠ 0 := by
    intro hc
    apply hconstantdiv
    simp [hc]
  obtain ⟨q, hq⟩ := hcoeffdiv 0 hn
  have hq' : P.constantCoeff = π * q := by
    simpa [Polynomial.constantCoeff] using hq
  have hq0A : q ≠ 0 := by
    intro hq0
    apply hconst0
    rw [hq', hq0, mul_zero]
  have hvK_data := hvK
  obtain ⟨πK, hπK0', hπK, hvKdisc⟩ := hvK_data
  have hqK0 : algebraMap A K q ≠ 0 := by
    intro hzero
    apply hq0A
    apply hA.hom_inj
    simpa using hzero
  have hqval : vK (algebraMap A K q) = 0 := by
    by_contra hqne
    have hqpos : 0 < vK (algebraMap A K q) :=
      lt_of_le_of_ne (hnonneg q) (Ne.symm hqne)
    obtain ⟨m, hm⟩ := hvKdisc (algebraMap A K q) hqK0
    have hmpos : (0 : ℤ) < m := by
      have hmpos' : (0 : WithTop ℤ) < (m : WithTop ℤ) := by
        rw [← hm]
        exact hqpos
      exact_mod_cast hmpos'
    have hmone : (1 : ℤ) ≤ m := by omega
    have hqquot_nonneg : 0 ≤
        vK (algebraMap A K q / algebraMap A K π) := by
      rw [vK.map_div, hm, hπ]
      have hmnonneg : (0 : ℤ) ≤ m - 1 := by omega
      exact_mod_cast hmnonneg
    obtain ⟨r, hr⟩ := hA.exists_of_le_one
      (hle_one _ hqquot_nonneg)
    have hqrK : algebraMap A K q =
        algebraMap A K π * algebraMap A K r := by
      calc
        algebraMap A K q =
            (algebraMap A K q / algebraMap A K π) * algebraMap A K π :=
          (div_mul_cancel₀ _ hπK0).symm
        _ = algebraMap A K r * algebraMap A K π := by rw [← hr]
        _ = algebraMap A K π * algebraMap A K r := mul_comm _ _
    have hqr : q = π * r := by
      apply hA.hom_inj
      simpa [map_mul] using hqrK
    apply hconstantdiv
    refine ⟨r, ?_⟩
    calc
      P.constantCoeff = P.coeff 0 := rfl
      _ = π * q := hq
      _ = π * (π * r) := by rw [hqr]
      _ = π ^ 2 * r := by ring
  have hE' : Chapter10EisensteinAtUniformizer P π :=
    ⟨hmonic, hdegree0, hcoeffdiv, hconstantdiv⟩
  have hconstK : vK (algebraMap A K P.constantCoeff) = 1 := by
    rw [show P.constantCoeff = P.coeff 0 by rfl, hq, map_mul,
      vK.map_mul, hπ, hqval, add_zero]
  have hconstK0 : algebraMap A K P.constantCoeff ≠ 0 := by
    intro hz
    apply hconst0
    apply hA.hom_inj
    simpa using hz
  have hconstL0 : algebraMap A L P.constantCoeff ≠ 0 := by
    simpa [IsScalarTower.algebraMap_apply A K L] using
      (RingHom.injective (algebraMap K L)).ne hconstK0
  have hconstL : vL (algebraMap A L P.constantCoeff) =
      vL (algebraMap A L π) := by
    rw [IsScalarTower.algebraMap_apply A K L,
      hscale (algebraMap A K P.constantCoeff) hconstK0,
      IsScalarTower.algebraMap_apply A K L,
      hscale (algebraMap A K π) hπK0, hconstK, hπ]
  have hπL : 0 < vL (algebraMap A L π) := by
    rw [IsScalarTower.algebraMap_apply A K L,
      hscale (algebraMap A K π) hπK0, hπ]
    exact nsmul_pos zero_lt_one he.ne'
  have hrootval := chapter10_eisenstein_root_value_comparison
    vL P π α P.natDegree hroot rfl hE' hπL hconstL hcoeffL
  have hα0 : α ≠ 0 := by
    intro hα
    have hroot0 : Polynomial.eval₂ (algebraMap A L) 0 P = 0 := by
      simpa [hα] using hroot
    have hconstLzero : algebraMap A L P.constantCoeff = 0 := by
      simpa using hroot0
    exact hconstL0 hconstLzero
  have hαpos : 0 < vL α := by
    by_contra hαpos
    have hαnonpos : vL α ≤ 0 := le_of_not_gt hαpos
    have hlezero : vL (algebraMap A L π) ≤ 0 := by
      rw [← hrootval]
      exact nsmul_nonpos hαnonpos _
    exact (not_le_of_gt hπL) hlezero
  have hvL_data := hvL
  obtain ⟨PiL, hPiL0, hPiL, hvLdisc⟩ := hvL_data
  obtain ⟨m, hm⟩ := hvLdisc α hα0
  have hmpos : (0 : ℤ) < m := by
    have hmpos' : (0 : WithTop ℤ) < (m : WithTop ℤ) := by
      rw [← hm]
      exact hαpos
    exact_mod_cast hmpos'
  have hmone : (1 : ℤ) ≤ m := by omega
  have hne_val : (P.natDegree : WithTop ℤ) ≤ (e : WithTop ℤ) := by
    have hmone' : (1 : WithTop ℤ) ≤ (m : WithTop ℤ) := by
      exact_mod_cast hmone
    calc
      (P.natDegree : WithTop ℤ) = P.natDegree • (1 : WithTop ℤ) := by simp
      _ ≤ P.natDegree • (m : WithTop ℤ) :=
        nsmul_le_nsmul_right hmone' P.natDegree
      _ = P.natDegree • vL α := by rw [hm]
      _ = vL (algebraMap A L π) := hrootval
      _ = e • vK (algebraMap A K π) := by
        simpa [IsScalarTower.algebraMap_apply A K L] using
          hscale (algebraMap A K π) hπK0
      _ = e • (1 : WithTop ℤ) := by rw [hπ]
      _ = (e : WithTop ℤ) := by simp
  have hne : P.natDegree ≤ e := by
    exact_mod_cast hne_val
  have hram_e : d.ramificationIndex = e := by
    have hri := @chapter10_normalized_ramification_index_eq_scale K L _ _ _ _
      vK vL hvK hvL hext d e he hscale d.finite_quotient
    exact hri.2
  have hrespos : 0 < d.residueDegree := by
    rw [d.residueDegree_eq]
    let : Valuation.HasExtension vK.toValuation vL.toValuation := ⟨hext⟩
    let : FiniteDimensional (Chapter10ResidueField vK.toValuation)
        (Chapter10ResidueField vL.toValuation) :=
      chapter10_residue_degree_finite vK.toValuation vL.toValuation
    exact Module.finrank_pos
  have hineq := chapter10_heterogeneous_single_extension_fundamental_inequality
    vK.toValuation vL.toValuation hext d
  have hle_e : e * d.residueDegree ≤ P.natDegree := by
    simpa [hram_e, hdegree] using hineq
  have he_le : e ≤ P.natDegree := by
    exact (Nat.le_mul_of_pos_right e hrespos).trans hle_e
  have heq : e = P.natDegree := Nat.le_antisymm he_le hne
  have hram : d.ramificationIndex = P.natDegree := by
    simpa [heq] using hram_e
  have hres : d.residueDegree = 1 := by
    have hle : P.natDegree * d.residueDegree ≤ P.natDegree := by
      simpa [hram, hdegree] using hineq
    have hle' : d.residueDegree ≤ 1 := by
      apply Nat.le_of_mul_le_mul_left
        (by simpa [Nat.mul_one] using hle)
      exact hn
    exact Nat.le_antisymm hle' (Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt hrespos))
  let p : Chapter10FiniteExtensionProfile :=
    { degree := P.natDegree, ramificationIndex := P.natDegree,
      residueDegree := 1 }
  refine ⟨d, p, ?_⟩
  simp [p, Chapter10ProfileRealizedByData, Chapter10TotallyRamified,
    hdegree, hram, hres]

/-- A polynomial has irreducible separable reduction through a chosen residue map. -/
def Chapter10IrreducibleSeparableReduction
    {A k : Type*} [CommRing A] [Field k]
    (res : A →+* k) (P : A[X]) (f : ℕ) : Prop :=
  let Q := P.map res
  P.Monic ∧ Q.Monic ∧ Q.natDegree = f ∧ Irreducible Q ∧ Q.Separable

/-- Irreducible separable reduction gives an unramified extension. -/
theorem chapter10_unramified_lift_profile
    {A K L k ΓK ΓL : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    [Field K] [Field L] [Field k]
    [Algebra A K] [IsFractionRing A K]
    [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L]
    [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓL]
    (res : A →+* k) (P : A[X]) (f : ℕ)
    (hred : Chapter10IrreducibleSeparableReduction res P f)
    (hres : ∃ e : IsLocalRing.ResidueField A ≃+* k,
      e.toRingHom.comp (IsLocalRing.residue A) = res)
    (α : L)
    (hroot : Polynomial.eval₂ (algebraMap A L) α P = 0)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (hdegree : Module.finrank K L = f)
    (v : Valuation K ΓK) (w : Valuation L ΓL)
    (hA : v.Integers A)
    (hext : v.IsEquiv (w.comap (algebraMap K L))) :
    ∃ d : Chapter10HeterogeneousExtensionData v w hext,
      ∃ p : Chapter10FiniteExtensionProfile,
        Chapter10ProfileRealizedByData d p ∧
          Irreducible P ∧
          p.degree = f ∧ p.ramificationIndex = 1 ∧
          p.residueDegree = f ∧ Chapter10Unramified p ∧
      Chapter10UnramifiedBranch v w hext d ∧
            (P.map res).Separable := by
  rcases hred with ⟨hPmonic, hQmonic, hQdegree, hQirr, hQsep⟩
  let : (nilradical A).IsPrime := by
    rw [nilradical_eq_zero A, Ideal.zero_eq_bot]
    exact Ideal.isPrime_bot
  have hPirr : Irreducible P :=
    hPmonic.irreducible_of_irreducible_map_of_isPrime_nilradical res P hQirr
  obtain ⟨d⟩ := chapter10_heterogeneous_extension_data_exists v w hext
  let p : Chapter10FiniteExtensionProfile :=
    { degree := f, ramificationIndex := 1, residueDegree := f }
  have hhard :
      Chapter10ProfileRealizedByData d p ∧
        Chapter10UnramifiedBranch v w hext d := by
    sorry
  refine ⟨d, p, hhard.1, hPirr, rfl, rfl, rfl, ?_, hhard.2, hQsep⟩
  simp [p, Chapter10Unramified]

/-- The p-adic uniformizer has normalized valuation one. -/
theorem chapter10_padic_uniformizer_value
    {p : ℕ} [Fact p.Prime] :
    Padic.valuation (p : ℚ_[p]) = 1 := by
  exact Padic.valuation_p

/-- The standard p-adic integers are the bounded elements for the additive
p-adic valuation. -/
theorem chapter10_padic_integers_are_add_valuation_integers
    {p : ℕ} [Fact p.Prime] :
    (Padic.addValuation (p := p)).Integers (ℤ_[p]) := by
  refine { hom_inj := ?_, map_le_one := ?_, exists_of_le_one := ?_ }
  · intro x y hxy
    apply PadicInt.ext
    exact hxy
  · intro x
    rw [show algebraMap ℤ_[p] ℚ_[p] x = (x : ℚ_[p]) by rfl]
    change Multiplicative.ofAdd (OrderDual.toDual (Padic.addValuation (x : ℚ_[p]))) ≤ 1
    by_cases hx : (x : ℚ_[p]) = 0
    · simp [hx]
    · rw [Padic.addValuation.apply hx]
      change (0 : WithTop ℤ) ≤ (x : ℚ_[p]).valuation
      exact_mod_cast (Padic.norm_le_one_iff_val_nonneg (x : ℚ_[p])).mp x.property
  · intro r hr
    change Multiplicative.ofAdd (OrderDual.toDual (Padic.addValuation r)) ≤
      Multiplicative.ofAdd (0 : OrderDual (WithTop ℤ)) at hr
    rw [Multiplicative.ofAdd_le] at hr
    change (0 : WithTop ℤ) ≤ Padic.addValuation r at hr
    have hrval : 0 ≤ r.valuation := by
      by_cases hr0 : r = 0
      · simp [hr0]
      · rw [Padic.addValuation.apply hr0] at hr
        exact_mod_cast hr
    refine ⟨⟨r, (Padic.norm_le_one_iff_val_nonneg r).mpr hrval⟩, ?_⟩
    rfl

/-- The p-adic Eisenstein setup is the preceding theorem with π = p. -/
theorem chapter10_padic_eisenstein_profile
    {p : ℕ} [Fact p.Prime] {L : Type*} [Field L]
    [Algebra ℤ_[p] L] [Algebra ℚ_[p] L]
    [IsScalarTower ℤ_[p] ℚ_[p] L]
    [FiniteDimensional ℚ_[p] L]
    (P : (ℤ_[p])[X]) (α : L)
    (hE : Chapter10EisensteinAtUniformizer P (p : ℤ_[p]))
    (hroot : Polynomial.eval₂ (algebraMap ℤ_[p] L) α P = 0)
    (hgen : Algebra.adjoin ℚ_[p] ({α} : Set L) = ⊤)
    (hdegree : Module.finrank ℚ_[p] L = P.natDegree)
    (vL : AddValuation L (WithTop ℤ))
    (hvL : Chapter10DiscreteAddValuation vL)
    (hext : (Padic.addValuation (p := p)).IsEquiv
      (vL.comap (algebraMap ℚ_[p] L))) :
    ∃ d : Chapter10HeterogeneousExtensionData
        (Padic.addValuation (p := p)) vL hext,
      ∃ q : Chapter10FiniteExtensionProfile,
        Chapter10ProfileRealizedByData d q ∧
          q.degree = P.natDegree ∧ q.ramificationIndex = P.natDegree ∧
          q.residueDegree = 1 ∧ Chapter10TotallyRamified q := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hvK : Chapter10DiscreteAddValuation (Padic.addValuation (p := p)) := by
    refine ⟨(p : ℚ_[p]), hp0, ?_, ?_⟩
    · simpa using (Padic.addValuation.apply hp0).trans
        (by
          convert chapter10_padic_uniformizer_value (p := p) using 1; simp)
    · intro x hx
      refine ⟨x.valuation, ?_⟩
      exact Padic.addValuation.apply hx
  have hπ : Padic.addValuation (p := p)
      (algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p])) = 1 := by
    simpa using (Padic.addValuation.apply hp0).trans
      (by
        convert chapter10_padic_uniformizer_value (p := p) using 1; simp)
  have hA : (Padic.addValuation (p := p)).Integers (ℤ_[p]) :=
    chapter10_padic_integers_are_add_valuation_integers (p := p)
  exact chapter10_eisenstein_totally_ramified_profile
    (A := ℤ_[p]) (K := ℚ_[p]) (L := L) P (p : ℤ_[p]) α
    hE hroot hgen hdegree (Padic.addValuation (p := p)) vL hvK hvL hext hA hπ

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter10
