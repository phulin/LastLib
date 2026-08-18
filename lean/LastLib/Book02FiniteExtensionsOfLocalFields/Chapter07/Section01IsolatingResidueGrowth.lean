import Mathlib.GroupTheory.Index
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Unramified.LocalRing
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section01TheExtensionProblem
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section05SeveralExtensionsAndTheFundamentalEquality
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section02TheCompletedProductTheorem
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section06TheValuationRingInAFiniteCompleteExtension

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07

open scoped BigOperators Polynomial TensorProduct WithZero
open Polynomial

noncomputable section

/-! # Book 2, Chapter 7, §7.1: isolating residue growth -/

/--
`Chapter07FiniteLocalExtensionData` records the numerical data used throughout
this chapter.  The residue fields `k` and `l` are explicit parameters rather
than being hidden behind a particular valuation presentation; the surrounding
theorems supply the identifications with the residue fields of the valuation
rings.  The degree equality is included because it is a defectless-local
extension interface, not a theorem for arbitrary valued fields.
-/
structure Chapter07FiniteLocalExtensionData
    (K L k l : Type*) [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l]
    [FiniteDimensional K L] [FiniteDimensional k l] where
  ramificationIndex : ℕ
  ramificationIndex_pos : 0 < ramificationIndex
  residueDegree : ℕ
  residueDegree_pos : 0 < residueDegree
  -- Keep the degree equality explicit as the bridge from this abstract profile
  -- to the defectless complete-DVR theorem proved in the preceding book.
  degree_eq_ramification_residue :
    Module.finrank K L = ramificationIndex * residueDegree
  residueDegree_eq : residueDegree = Module.finrank k l

/-- Separability of a finite residue-field extension, without requiring a
separability typeclass to be installed for the explicit residue algebra. -/
def Chapter07ResidueExtensionIsSeparable
    (k l : Type*) [Field k] [Field l] [Algebra k l] : Prop :=
  ∀ x : l, IsSeparable k x

/-- Purely inseparable residue growth, expressed using Mathlib's standard
extension predicate rather than merely the failure of separability. -/
def Chapter07ResidueExtensionIsPurelyInseparable
    (k l : Type*) [Field k] [Field l] [Algebra k l] : Prop :=
  IsPurelyInseparable k l

/-! The book's definition and its deliberately separate warning case. -/

/-- A finite local extension is unramified exactly when `e = 1` and its
residue extension is separable. -/
def Chapter07UnramifiedExtension
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l]
    [FiniteDimensional K L] [FiniteDimensional k l]
    (E : Chapter07FiniteLocalExtensionData K L k l) : Prop :=
  E.ramificationIndex = 1 ∧
    Chapter07ResidueExtensionIsSeparable k l

/-- The `e = 1`/inseparable-residue warning case mentioned in §7.1.  The
  source deliberately does not assign this case a special name; purely
  inseparable examples are treated separately in §7.5. -/
def Chapter07EOneInseparableResidueExtension
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l]
    [FiniteDimensional K L] [FiniteDimensional k l]
    (E : Chapter07FiniteLocalExtensionData K L k l) : Prop :=
  E.ramificationIndex = 1 ∧
    ¬Chapter07ResidueExtensionIsSeparable k l

/-- The residue-field perfection condition used in the perfect-residue
specialization. -/
def Chapter07PerfectResidueField (k : Type*) [Field k] : Prop :=
  PerfectField k

/-! Reuse Book 1's valuation-group and residue-field constructions when a
valuation presentation is available. -/

abbrev Chapter07ValuationRing {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) : Subring K :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValuationRing v

abbrev Chapter07ResidueField {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ResidueField v

noncomputable def Chapter07RamificationIndex
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [Finite (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vL ⧸
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vK).subgroupOf
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vL))]
    (hΓ : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vK ≤
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vL) : ℕ :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10RamificationIndex vK vL hΓ

noncomputable def Chapter07ResidueDegree
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    (h : vK.IsEquiv (vL.comap (algebraMap K L))) : ℕ :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ResidueDegreeOfExtension vK vL h

/-! §7.1 assertions. -/

/-- The degree formula for an unramified extension is the residue degree. -/
theorem chapter07_unramified_degree_eq_residue_degree
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l]
    [FiniteDimensional K L] [FiniteDimensional k l]
    (E : Chapter07FiniteLocalExtensionData K L k l)
    (hE : Chapter07UnramifiedExtension E) :
    Module.finrank K L = Module.finrank k l := by
  rw [E.degree_eq_ramification_residue, hE.1, Nat.one_mul, E.residueDegree_eq]

/-- In the complete discrete valuation setting, the separability assertion uses
the actual residue fields and the defectless degree equality, rather than only
the abstract numerical profile from this section. -/
theorem chapter07_unramified_is_separable
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (hdegree : Module.finrank K L =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
          vK.valuationSubring vL.valuationSubring
          (IsLocalRing.maximalIdeal vL.valuationSubring) *
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
          vK.valuationSubring vL.valuationSubring
          (IsLocalRing.maximalIdeal vL.valuationSubring))
    (hresidueDegree :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
          vK.valuationSubring vL.valuationSubring
          (IsLocalRing.maximalIdeal vL.valuationSubring) =
        Module.finrank (IsLocalRing.ResidueField vK.valuationSubring)
          (IsLocalRing.ResidueField vL.valuationSubring))
    (he : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
          vK.valuationSubring vL.valuationSubring
          (IsLocalRing.maximalIdeal vL.valuationSubring) = 1)
    (hresidue : ∀ x : IsLocalRing.ResidueField vL.valuationSubring,
      IsSeparable (IsLocalRing.ResidueField vK.valuationSubring) x) :
    Algebra.IsSeparable K L := by
  let hfinite : Module.Finite vK.valuationSubring vL.valuationSubring :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.complete_extension_unit_ball_is_finite
      vK vL hcomplete
  letI : Module.Finite vK.valuationSubring vL.valuationSubring := hfinite
  letI : Algebra.IsSeparable (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring) := ⟨hresidue⟩
  have hformulas :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.complete_extension_ideal_and_residue_formulas
      vK vL 1 (Module.finrank (IsLocalRing.ResidueField vK.valuationSubring)
        (IsLocalRing.ResidueField vL.valuationSubring)) he hresidueDegree hcomplete
  have hmap :
      (IsLocalRing.maximalIdeal vK.valuationSubring).map
          (algebraMap vK.valuationSubring vL.valuationSubring) =
        IsLocalRing.maximalIdeal vL.valuationSubring := by
    simpa only [pow_one] using hformulas.1
  letI : Algebra.FormallyUnramified vK.valuationSubring vL.valuationSubring :=
    Algebra.FormallyUnramified.of_map_maximalIdeal hmap
  let T :=
    Localization (Algebra.algebraMapSubmonoid vL.valuationSubring
      (nonZeroDivisors vK.valuationSubring))
  have hinj : Function.Injective
      (algebraMap vK.valuationSubring vL.valuationSubring) := by
    exact Valuation.HasExtension.algebraMap_injective (vK := vK) (vA := vL)
  have hbaseMap :
      Algebra.algebraMapSubmonoid vL.valuationSubring
          (nonZeroDivisors vK.valuationSubring) ≤
        nonZeroDivisors vL.valuationSubring := by
    exact map_le_nonZeroDivisors_of_injective _ hinj le_rfl
  letI : Algebra K T :=
    localizationAlgebra (nonZeroDivisors vK.valuationSubring)
      vL.valuationSubring
  letI : IsScalarTower vK.valuationSubring K T :=
    isScalarTower_localizationAlgebra
      (nonZeroDivisors vK.valuationSubring) vL.valuationSubring
  letI : Module.Finite K T :=
    Module.Finite.of_isLocalization vK.valuationSubring vL.valuationSubring
      (nonZeroDivisors vK.valuationSubring)
  letI : IsLocalization
      ((nonZeroDivisors vK.valuationSubring).map
        (algebraMap vK.valuationSubring vL.valuationSubring)) T :=
    inferInstanceAs (IsLocalization
      (Algebra.algebraMapSubmonoid vL.valuationSubring
        (nonZeroDivisors vK.valuationSubring)) T)
  letI : IsDomain T := IsLocalization.isDomain_localization hbaseMap
  have hfieldT : IsField T :=
    isField_of_isIntegral_of_isField' (R := K) (S := T) (Field.toIsField K)
  letI : IsField T := hfieldT
  letI : Field T := hfieldT.toField
  have hformalT : Algebra.FormallyUnramified K T := by
    exact Algebra.FormallyUnramified.localization_map
      (R := vK.valuationSubring) (S := vL.valuationSubring)
      (Rₘ := K) (Sₘ := T) (M := nonZeroDivisors vK.valuationSubring)
  have hsepT : Algebra.IsSeparable K T :=
    (Algebra.FormallyUnramified.iff_isSeparable K T).mp hformalT
  letI : IsFractionRing vL.valuationSubring T :=
    IsLocalization.of_le
      (M := Algebra.algebraMapSubmonoid vL.valuationSubring
        (nonZeroDivisors vK.valuationSubring))
      (nonZeroDivisors vL.valuationSubring) hbaseMap (fun x hx => by
        apply isUnit_iff_ne_zero.mpr
        exact map_ne_zero_of_mem_nonZeroDivisors _
          (IsLocalization.injective T hbaseMap) hx)
  let eTL : T ≃ₐ[vL.valuationSubring] L :=
    IsFractionRing.algEquivOfAlgEquiv
      (R := vL.valuationSubring) (A := vL.valuationSubring)
      (B := vL.valuationSubring) (K := T) (L := L)
      (AlgEquiv.refl : (↥vL.valuationSubring) ≃ₐ[vL.valuationSubring]
        (↥vL.valuationSubring))
  apply Algebra.IsSeparable.of_equiv_equiv (RingEquiv.refl K) eTL.toRingEquiv
  ext x
  simp only [RingHom.comp_apply]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective vK.valuationSubring x
  simp [map_div₀, ← IsScalarTower.algebraMap_apply vK.valuationSubring K T,
    ← IsScalarTower.algebraMap_apply vK.valuationSubring vL.valuationSubring L]
  congr 1
  · have haK : (a : K) = algebraMap vK.valuationSubring K a := rfl
    have haL : (algebraMap K L) (a : K) =
        (algebraMap vL.valuationSubring L)
          (algebraMap vK.valuationSubring vL.valuationSubring a) := by
      rw [haK, ← IsScalarTower.algebraMap_apply vK.valuationSubring K L,
        ← IsScalarTower.algebraMap_apply vK.valuationSubring vL.valuationSubring L]
    have haT : (algebraMap K T) (a : K) =
        (algebraMap vL.valuationSubring T)
          (algebraMap vK.valuationSubring vL.valuationSubring a) := by
      rw [haK, ← IsScalarTower.algebraMap_apply vK.valuationSubring K T,
        ← IsScalarTower.algebraMap_apply vK.valuationSubring vL.valuationSubring T]
    rw [haL, haT]
    exact (eTL.commutes (algebraMap vK.valuationSubring vL.valuationSubring a)).symm
  · have hbK : (b : K) = algebraMap vK.valuationSubring K b := rfl
    have hbL : (algebraMap K L) (b : K) =
        (algebraMap vL.valuationSubring L)
          (algebraMap vK.valuationSubring vL.valuationSubring b) := by
      rw [hbK, ← IsScalarTower.algebraMap_apply vK.valuationSubring K L,
        ← IsScalarTower.algebraMap_apply vK.valuationSubring vL.valuationSubring L]
    have hbT : (algebraMap K T) (b : K) =
        (algebraMap vL.valuationSubring T)
          (algebraMap vK.valuationSubring vL.valuationSubring b) := by
      rw [hbK, ← IsScalarTower.algebraMap_apply vK.valuationSubring K T,
        ← IsScalarTower.algebraMap_apply vK.valuationSubring vL.valuationSubring T]
    rw [hbL, hbT]
    exact (eTL.commutes (algebraMap vK.valuationSubring vL.valuationSubring b)).symm

theorem chapter07_e_one_inseparable_residue_is_not_unramified
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l]
    [FiniteDimensional K L] [FiniteDimensional k l]
    (E : Chapter07FiniteLocalExtensionData K L k l)
    (hE : Chapter07EOneInseparableResidueExtension E) :
    ¬Chapter07UnramifiedExtension E := by
  intro hU
  exact hE.2 hU.2

/-- Over a perfect residue field, the separability clause is automatic. -/
theorem chapter07_perfect_residue_unramified_iff_e_one
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l]
    [FiniteDimensional K L] [FiniteDimensional k l]
    (E : Chapter07FiniteLocalExtensionData K L k l)
    (hk : Chapter07PerfectResidueField k) :
    Chapter07UnramifiedExtension E ↔ E.ramificationIndex = 1 := by
  constructor
  · intro h
    exact h.1
  · intro he
    refine ⟨he, ?_⟩
    intro x
    let _ : PerfectField k := hk
    exact Algebra.IsSeparable.isSeparable k x

/-- Every finite field is perfect; this statement deliberately has no
characteristic-zero hypothesis. -/
theorem chapter07_finite_field_is_perfect
    (k : Type*) [Field k] [Finite k] : Chapter07PerfectResidueField k := by
  exact PerfectField.ofFinite

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07
