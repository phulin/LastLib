import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02.Section03RamificationIndexAndResidueDegree

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02

noncomputable section

open Ideal IsLocalRing
open LastLib.Book01ValuationsDVRsAndCompletions.Chapter12
open scoped BigOperators WithZero

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-! ## Book 2, Chapter 2, §2.4

The length statements below use Mathlib's `Module.length` and its `toNat`
projection.  This retains the source proof's two counts: finite freeness over
the base and the `e` successive residue-field layers upstairs.
-/

/-- The central degree formula, with no separability or residue perfection assumption. -/
theorem fundamental_equality
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring) :
    Module.finrank K L =
      chapterRamificationIndex vK.valuationSubring vL.valuationSubring
          (IsLocalRing.maximalIdeal vL.valuationSubring) *
      chapterResidueDegree vK.valuationSubring vL.valuationSubring
          (IsLocalRing.maximalIdeal vL.valuationSubring) := by
  sorry

/-- The first base-precision quotient has length equal to the field degree. -/
theorem first_precision_length_is_field_degree
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    [Module.Free vK.valuationSubring vL.valuationSubring] :
    (Module.length vK.valuationSubring
      (vL.valuationSubring ⧸
        (IsLocalRing.maximalIdeal vK.valuationSubring).map
          (algebraMap vK.valuationSubring vL.valuationSubring))).toNat =
      Module.finrank K L := by
  sorry

/-- The nested ideal quotient representing a maximal-ideal power layer. -/
abbrev chapter2PrimePowerLayer
    (B : Type*) [CommRing B] (P : Ideal B) (i : ℕ) : Type _ :=
  (P ^ i : Ideal B) ⧸ (P • ⊤ : Submodule B (P ^ i : Ideal B))

/-- Each nonzero maximal-ideal layer is one copy of the extension residue field. -/
theorem maximal_ideal_layers_are_residue_lines
    (B : Type*) [CommRing B] [IsDedekindDomain B]
    (P : Ideal B) [P.IsPrime] [P.IsMaximal] [IsPrincipalIdealRing B]
    (i : ℕ) (hi : 0 < i + 1) (hP0 : P ≠ ⊥) :
    Nonempty
      (chapter2PrimePowerLayer B P i ≃+
        (B ⧸ P)) := by
  sorry

/-- The length comparison behind `[L : K] = e f`. -/
theorem first_precision_length_is_ramification_times_residue
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    [Module.Free vK.valuationSubring vL.valuationSubring]
    (e f : ℕ)
    (he : chapterRamificationIndex vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = e)
    (hf : chapterResidueDegree vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = f) :
    (Module.length vK.valuationSubring
      (vL.valuationSubring ⧸
        (IsLocalRing.maximalIdeal vK.valuationSubring).map
          (algebraMap vK.valuationSubring vL.valuationSubring))).toNat =
      e * f := by
  sorry

/-- The layer count is the finite sum `∑_{i < e} f = e f`. -/
theorem fundamental_equality_as_layer_sum
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    (e f : ℕ)
    (he : chapterRamificationIndex vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = e)
    (hf : chapterResidueDegree vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = f)
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring) :
    Module.finrank K L = (∑ _ : Fin e, f) ∧
      (∑ _ : Fin e, f) = e * f := by
  sorry

/-- Completeness and discreteness remove the defect factor in the equality. -/
theorem fundamental_equality_without_separability_or_perfectness
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring) :
    Module.finrank K L =
      chapterRamificationIndex vK.valuationSubring vL.valuationSubring
          (IsLocalRing.maximalIdeal vL.valuationSubring) *
      chapterResidueDegree vK.valuationSubring vL.valuationSubring
          (IsLocalRing.maximalIdeal vL.valuationSubring) := by
  exact fundamental_equality vK vL hcomplete

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02
