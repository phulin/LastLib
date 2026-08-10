import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02.Section02FiniteFreeness

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02

noncomputable section

open Ideal IsLocalRing
open LastLib.Book01ValuationsDVRsAndCompletions.Chapter12
open scoped BigOperators WithZero

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-! ## Book 2, Chapter 2, §2.3

`chapterRamificationIndex` and `chapterResidueDegree` are the Book 1
Chapter 12 wrappers around Mathlib's `Ideal.ramificationIdx` and
`Ideal.inertiaDeg`.  Under the complete DVR hypotheses these are the
ideal-theoretic realizations of the value-group index and residue-field
dimension in the source.
-/

/-- The normalized restriction formula in Mathlib's multiplicative notation. -/
def chapter2NormalizedValuationRestriction
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰) (e : ℕ) : Prop :=
  ∀ x : K, vL (algebraMap K L x) = vK x ^ e

/-- The residue-field extension attached to two extending valuation rings. -/
def chapter2ResidueFieldExtension
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] : Prop :=
  Module.Finite (IsLocalRing.ResidueField vK.valuationSubring)
    (IsLocalRing.ResidueField vL.valuationSubring)

/-- In the normalized convention, restriction scales by the ramification index. -/
theorem valuation_restriction_is_power_of_ramification_index
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL]
    (e : ℕ)
    (he : chapterRamificationIndex vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = e) :
    ∀ x : K, vL (algebraMap K L x) = vK x ^ e := by
  sorry

/-- Uniformizers give the principal-ideal factorization `π_K = u π_L^e`. -/
theorem uniformizer_factorization
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL]
    (e : ℕ)
    (he : chapterRamificationIndex vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = e)
    (πK : vK.valuationSubring) (πL : vL.valuationSubring)
    (hπK : vK.IsUniformizer πK) (hπL : vL.IsUniformizer πL) :
    ∃ u : vL.valuationSubringˣ,
      algebraMap vK.valuationSubring vL.valuationSubring πK =
        (u : vL.valuationSubring) * (πL : vL.valuationSubring) ^ e := by
  sorry

/-- The extension of the base maximal ideal is the `e`th power upstairs. -/
theorem maximal_ideal_extension_is_power
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL]
    (e : ℕ)
    (he : chapterRamificationIndex vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = e) :
    (IsLocalRing.maximalIdeal vK.valuationSubring).map
        (algebraMap vK.valuationSubring vL.valuationSubring) =
      (IsLocalRing.maximalIdeal vL.valuationSubring) ^ e := by
  sorry

/-- The residue degree is the finite-dimensional degree of `l/k`. -/
theorem residue_degree_is_residue_field_finrank
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL]
    [FiniteDimensional K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring] :
    chapterResidueDegree vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring) =
      Module.finrank (IsLocalRing.ResidueField vK.valuationSubring)
        (IsLocalRing.ResidueField vL.valuationSubring) := by
  sorry

/-- The residue-degree formula has no separability hypothesis. -/
theorem residue_degree_formula_without_separability
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL]
    [FiniteDimensional K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring] :
    chapterResidueDegree vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring) =
      Module.finrank (IsLocalRing.ResidueField vK.valuationSubring)
        (IsLocalRing.ResidueField vL.valuationSubring) := by
  exact residue_degree_is_residue_field_finrank vK vL

/-- A residue degree is not replaced by a count of embeddings without separability. -/
def chapter2ResidueDegreeUsesVectorSpaceDimension
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] (f : ℕ) : Prop :=
  f = Module.finrank (IsLocalRing.ResidueField vK.valuationSubring)
    (IsLocalRing.ResidueField vL.valuationSubring)

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02
