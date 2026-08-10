import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02.Section05ExamplesAndWarnings

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02

noncomputable section

open Ideal IsLocalRing
open LastLib.Book01ValuationsDVRsAndCompletions.Chapter12
open scoped BigOperators WithZero

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-! ## Book 2, Chapter 2, §2.6

Finite precision is expressed with powers of maximal ideals.  This avoids
choosing uniformizers in the statements that concern arbitrary precision;
the uniformizer form is recovered from §2.3.
-/

/-- A finite-precision quotient at an ideal. -/
abbrev chapter2FinitePrecisionQuotient
    (R : Type*) [CommRing R] (I : Ideal R) (n : ℕ) : Type _ :=
  R ⧸ I ^ n

/-- The `r`-digit version of the ideal-power formula. -/
theorem finite_precision_ideal_power_formula
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    (r e : ℕ)
    (he : chapterRamificationIndex vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = e) :
      ((IsLocalRing.maximalIdeal vK.valuationSubring).map
        (algebraMap vK.valuationSubring vL.valuationSubring)) ^ r =
      (IsLocalRing.maximalIdeal vL.valuationSubring) ^ (r * e) := by
  sorry

/-- Finite freeness identifies the `r`-digit quotient with `n` copies upstairs. -/
theorem finite_precision_quotient_linear_equiv
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    [Module.Free vK.valuationSubring vL.valuationSubring]
    (r : ℕ) :
    Nonempty
      ((vL.valuationSubring ⧸
          ((IsLocalRing.maximalIdeal vK.valuationSubring).map
            (algebraMap vK.valuationSubring vL.valuationSubring)) ^ r) ≃ₗ[
          vK.valuationSubring]
        (Fin (Module.finrank K L) →
          (vK.valuationSubring ⧸
            (IsLocalRing.maximalIdeal vK.valuationSubring) ^ r))) := by
  sorry

/-- The two length computations agree at every positive base precision. -/
theorem finite_precision_length_formula
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    [Module.Free vK.valuationSubring vL.valuationSubring]
    (r e f : ℕ)
    (hr : 0 < r)
    (he : chapterRamificationIndex vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = e)
    (hf : chapterResidueDegree vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = f) :
    (Module.length vK.valuationSubring
      (vL.valuationSubring ⧸
        ((IsLocalRing.maximalIdeal vK.valuationSubring).map
          (algebraMap vK.valuationSubring vL.valuationSubring)) ^ r)).toNat =
        r * Module.finrank K L ∧
    (Module.length vK.valuationSubring
      (vL.valuationSubring ⧸
        ((IsLocalRing.maximalIdeal vK.valuationSubring).map
          (algebraMap vK.valuationSubring vL.valuationSubring)) ^ r)).toNat =
        (r * e) * f := by
  sorry

/-- The intrinsic `L`-adic quotient has `f n` residue-field coordinates. -/
theorem extension_precision_cardinality_exponent
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    [Fintype (IsLocalRing.ResidueField vK.valuationSubring)]
    [Fintype (IsLocalRing.ResidueField vL.valuationSubring)]
    (q f n : ℕ)
    (hq : Fintype.card (IsLocalRing.ResidueField vK.valuationSubring) = q)
    (hf : chapterResidueDegree vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = f)
    [Fintype (vL.valuationSubring ⧸
      (IsLocalRing.maximalIdeal vL.valuationSubring) ^ n)] :
    Fintype.card (vL.valuationSubring ⧸
        (IsLocalRing.maximalIdeal vL.valuationSubring) ^ n) =
      q ^ (f * n) := by
  sorry

/-- The base-precision quotient retains `r e` uniformizer digits upstairs. -/
theorem base_precision_cardinality_formula
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    [Fintype (IsLocalRing.ResidueField vK.valuationSubring)]
    [Fintype (IsLocalRing.ResidueField vL.valuationSubring)]
    (q e f r : ℕ)
    (hq : Fintype.card (IsLocalRing.ResidueField vK.valuationSubring) = q)
    (he : chapterRamificationIndex vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = e)
    (hf : chapterResidueDegree vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = f)
    (hdegree : Module.finrank K L = e * f)
    [Fintype (vL.valuationSubring ⧸
      ((IsLocalRing.maximalIdeal vK.valuationSubring).map
        (algebraMap vK.valuationSubring vL.valuationSubring)) ^ r)] :
    Fintype.card (vL.valuationSubring ⧸
        ((IsLocalRing.maximalIdeal vK.valuationSubring).map
          (algebraMap vK.valuationSubring vL.valuationSubring)) ^ r) =
      q ^ (r * f * e) ∧
    Fintype.card (vL.valuationSubring ⧸
        ((IsLocalRing.maximalIdeal vK.valuationSubring).map
          (algebraMap vK.valuationSubring vL.valuationSubring)) ^ r) =
      q ^ (r * Module.finrank K L) := by
  sorry

/-- The compatible four-map diagram of base and residue precision. -/
structure Chapter2FinitePrecisionResidueDiagram
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰) (r : ℕ)
    [vK.HasExtension vL] where
  topHorizontal :
    (vK.valuationSubring ⧸
      (IsLocalRing.maximalIdeal vK.valuationSubring) ^ r) →+*
      (vL.valuationSubring ⧸
        ((IsLocalRing.maximalIdeal vK.valuationSubring).map
          (algebraMap vK.valuationSubring vL.valuationSubring)) ^ r)
  leftVertical :
    (vK.valuationSubring ⧸
      (IsLocalRing.maximalIdeal vK.valuationSubring) ^ r) →+*
      IsLocalRing.ResidueField vK.valuationSubring
  bottomHorizontal :
    IsLocalRing.ResidueField vK.valuationSubring →+*
      IsLocalRing.ResidueField vL.valuationSubring
  rightVertical :
    (vL.valuationSubring ⧸
      ((IsLocalRing.maximalIdeal vK.valuationSubring).map
        (algebraMap vK.valuationSubring vL.valuationSubring)) ^ r) →+*
      IsLocalRing.ResidueField vL.valuationSubring
  commutes :
    rightVertical.comp topHorizontal = bottomHorizontal.comp leftVertical

/-- The diagram in §2.6 exists for every finite precision. -/
theorem finite_precision_residue_diagram_exists
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    (r : ℕ) (hr : 0 < r) :
    Nonempty (Chapter2FinitePrecisionResidueDiagram vK vL r) := by
  sorry

/-- For `r > 1`, the base precision quotient has nonzero nilpotent thickness. -/
theorem base_precision_quotient_has_nonzero_nilpotent
    (vK : Valuation K ℤᵐ⁰) [Valuation.IsRankOneDiscrete vK]
    (r : ℕ) (hr : 1 < r) :
    ∃ x : vK.valuationSubring ⧸
        (IsLocalRing.maximalIdeal vK.valuationSubring) ^ r,
      x ≠ 0 ∧ IsNilpotent x := by
  sorry

/-- If `e > 1`, ramification makes the first upstairs quotient nonreduced. -/
theorem ramified_first_quotient_has_nonzero_nilpotent
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    (e : ℕ)
    (he : chapterRamificationIndex vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = e)
    (hepos : 1 < e) :
    ∃ x : vL.valuationSubring ⧸
        (IsLocalRing.maximalIdeal vK.valuationSubring).map
          (algebraMap vK.valuationSubring vL.valuationSubring),
      x ≠ 0 ∧ IsNilpotent x := by
  sorry

/-- In the unramified case the first quotient is exactly the residue field. -/
theorem unramified_first_quotient_is_residue_field
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    (he : chapterRamificationIndex vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = 1) :
    Nonempty
      ((vL.valuationSubring ⧸
          (IsLocalRing.maximalIdeal vK.valuationSubring).map
            (algebraMap vK.valuationSubring vL.valuationSubring)) ≃+*
        IsLocalRing.ResidueField vL.valuationSubring) := by
  sorry

/-- The nilpotence index of the maximal ideal in `B / π_K B` is `e`. -/
theorem ramification_is_nilpotence_index
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    (e : ℕ)
    (he : chapterRamificationIndex vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = e)
    (hepos : 0 < e) :
    let I := Ideal.map
      (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal vK.valuationSubring).map
          (algebraMap vK.valuationSubring vL.valuationSubring)))
      (IsLocalRing.maximalIdeal vL.valuationSubring)
    I ^ e = ⊥ ∧ I ^ (e - 1) ≠ ⊥ := by
  sorry

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02
