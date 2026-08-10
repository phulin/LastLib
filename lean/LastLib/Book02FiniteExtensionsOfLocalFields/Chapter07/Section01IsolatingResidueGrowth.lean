import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dimension.Finite
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10

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
  residueDegree : ℕ
  degree_eq_ramification_residue :
    Module.finrank K L = ramificationIndex * residueDegree
  residueDegree_eq : residueDegree = Module.finrank k l

/-- Separability of a finite residue-field extension, without requiring a
separability typeclass to be installed for the explicit residue algebra. -/
def Chapter07ResidueExtensionIsSeparable
    (k l : Type*) [Field k] [Field l] [Algebra k l] : Prop :=
  ∀ x : l, IsSeparable k x

/-- Separability of the generic finite extension. -/
def Chapter07FiniteExtensionIsSeparable
    (K L : Type*) [Field K] [Field L] [Algebra K L] : Prop :=
  ∀ x : L, IsSeparable K x

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

/-- The `e = 1`/purely inseparable-residue warning case mentioned in §7.1. -/
def Chapter07FiercelyRamifiedExtension
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
    (hΓ : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vK ≤
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vL) : ℕ :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10RamificationIndex vK vL hΓ

noncomputable def Chapter07ResidueDegree
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
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
  rcases hE with ⟨he, _⟩
  rw [E.degree_eq_ramification_residue, he, one_mul, E.residueDegree_eq]

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
      (IsLocalRing.maximalIdeal vL.valuationSubring).ramificationIdx
          vK.valuationSubring *
        (IsLocalRing.maximalIdeal vL.valuationSubring).inertiaDeg
          vK.valuationSubring)
    (he : (IsLocalRing.maximalIdeal vL.valuationSubring).ramificationIdx
          vK.valuationSubring = 1)
    (hresidue : ∀ x : IsLocalRing.ResidueField vL.valuationSubring,
      IsSeparable (IsLocalRing.ResidueField vK.valuationSubring) x) :
    Chapter07FiniteExtensionIsSeparable K L := by
  sorry

theorem chapter07_fierce_is_not_unramified
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l]
    [FiniteDimensional K L] [FiniteDimensional k l]
    (E : Chapter07FiniteLocalExtensionData K L k l)
    (hE : Chapter07FiercelyRamifiedExtension E) :
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
  · intro hE
    exact hE.1
  · intro he
    refine ⟨he, ?_⟩
    change ∀ x : l, IsSeparable k x
    letI : PerfectField k := hk
    exact Algebra.IsSeparable.isSeparable k

/-- Every finite field is perfect; this statement deliberately has no
characteristic-zero hypothesis. -/
theorem chapter07_finite_field_is_perfect
    (k : Type*) [Field k] [Finite k] : Chapter07PerfectResidueField k := by
  change PerfectField k
  infer_instance

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07
