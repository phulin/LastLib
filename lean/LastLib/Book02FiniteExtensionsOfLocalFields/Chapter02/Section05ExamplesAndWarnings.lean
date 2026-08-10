import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02.Section04TheFundamentalEquality

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02

noncomputable section

open Set
open Ideal IsLocalRing Polynomial
open LastLib.Book01ValuationsDVRsAndCompletions.Chapter12
open scoped BigOperators WithZero

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-! ## Book 2, Chapter 2, §2.5

The concrete examples in the source are applications of the two endpoint
corollaries below.  The polynomial constructor is kept concrete so that the
Eisenstein example can be reused later without rebuilding `X^n - π`.
-/

/-- The polynomial `X^n - π` used for the totally ramified example. -/
def chapter2PowerRootPolynomial
    {A : Type*} [CommRing A] (π : A) (n : ℕ) : A[X] :=
  X ^ n - C π

/-- A finite valued extension has a defect precisely when its degree is not `e f`. -/
def chapter2HasDefect (degree e f : ℕ) : Prop :=
  degree ≠ e * f

/-- The assertion that two valuation subrings above the base give distinct
branches. -/
def chapter2HasSeveralValuationExtensions
    (vK : Valuation K ℤᵐ⁰) : Prop :=
  ∃ W₁ W₂ : ValuationSubring L,
    chapter2ValuationSubringExtends vK W₁ ∧
      chapter2ValuationSubringExtends vK W₂ ∧ W₁ ≠ W₂

/-- In an unramified extension the whole degree is residue degree. -/
-- STATEMENT_NEEDS_UPDATE: The hypotheses allow a nontrivial defect, so `finrank K L = f` does not follow from `e = 1` and `hcomplete`. Add a defectless hypothesis (or a standard sufficient one), or weaken the conclusion to include the defect factor.
theorem unramified_extension_degree_is_residue_degree
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    (f : ℕ)
    (he : chapterRamificationIndex vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = 1)
    (hf : chapterResidueDegree vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = f)
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring) :
    Module.finrank K L = f := by
  sorry

/-- In a totally ramified extension the whole degree is ramification index. -/
-- STATEMENT_NEEDS_UPDATE: The hypotheses allow a nontrivial defect, so `finrank K L = e` does not follow from `f = 1` and `hcomplete`. Add a defectless hypothesis (or a standard sufficient one), or weaken the conclusion to include the defect factor.
theorem totally_ramified_extension_degree_is_ramification_index
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    (e : ℕ)
    (he : chapterRamificationIndex vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = e)
    (hf : chapterResidueDegree vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = 1)
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring) :
    Module.finrank K L = e := by
  sorry

/-- The Eisenstein power-root example has `e = n`, `f = 1`, and degree `n`. -/
theorem eisenstein_power_root_example
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A K] [IsFractionRing A K]
    [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L]
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL]
    (π : A) (piRoot : L) (n : ℕ)
    (hvaluationRing : (vK.valuationSubring : Set K) = Set.range (algebraMap A K))
    (hf : IsEisensteinAt π (chapter2PowerRootPolynomial π n))
    (hirreducible : Irreducible (chapter2PowerRootPolynomial π n))
    (hroot : aeval piRoot (chapter2PowerRootPolynomial π n) = 0)
    (hgenerates : Algebra.adjoin K ({piRoot} : Set L) = ⊤)
    (hvaluation : vL piRoot = Valuation.IsRankOneDiscrete.generator vL)
    (hbase : vK (algebraMap A K π) = (vL piRoot) ^ n)
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring) :
    chapterRamificationIndex vK.valuationSubring vL.valuationSubring
          (IsLocalRing.maximalIdeal vL.valuationSubring) = n ∧
      chapterResidueDegree vK.valuationSubring vL.valuationSubring
          (IsLocalRing.maximalIdeal vL.valuationSubring) = 1 ∧
      Module.finrank K L = n := by
  have hdegreePoly :
      (chapter2PowerRootPolynomial π n).natDegree = n := by
    simpa [chapter2PowerRootPolynomial] using
      (Polynomial.natDegree_X_pow_sub_C (R := A) (n := n) (r := π))
  have hmain := eisenstein_root_is_uniformizer_and_totally_ramified
    vK vL π (chapter2PowerRootPolynomial π n) piRoot hf hroot hdegreePoly
      hgenerates hvaluation hbase
  have hrootK :
      Polynomial.aeval piRoot
        ((chapter2PowerRootPolynomial π n).map (algebraMap A K)) = 0 := by
    rw [Polynomial.aeval_map_algebraMap]
    exact hroot
  have hirreducibleK : Irreducible
      ((chapter2PowerRootPolynomial π n).map (algebraMap A K)) :=
    (hf.1.irreducible_iff_irreducible_map_fraction_map).mp hirreducible
  have hminpoly :
      (chapter2PowerRootPolynomial π n).map (algebraMap A K) = minpoly K piRoot :=
    minpoly.eq_of_irreducible_of_monic hirreducibleK hrootK (hf.1.map _)
  let pb : PowerBasis K L := PowerBasis.ofAdjoinEqTop
    (IsIntegral.of_finite K piRoot) hgenerates
  have hdegree : Module.finrank K L = n := by
    calc
      Module.finrank K L = pb.dim := pb.finrank
      _ = (minpoly K piRoot).natDegree := by
        dsimp [pb]
      _ = ((chapter2PowerRootPolynomial π n).map (algebraMap A K)).natDegree := by
        rw [hminpoly]
      _ = (chapter2PowerRootPolynomial π n).natDegree := by
        exact Polynomial.natDegree_map_eq_of_injective
          (IsFractionRing.injective A K) _
      _ = n := hdegreePoly
  obtain ⟨_, he, hf'⟩ := hmain
  exact ⟨he, hf', hdegree⟩

/-- The fundamental equality still applies to purely inseparable examples. -/
-- STATEMENT_NEEDS_UPDATE: Purely inseparable finite extensions can still have defect over an imperfect residue field, so pure inseparability does not imply the displayed equality. Add a defectless hypothesis (or a standard sufficient one), or weaken the conclusion to include the defect factor.
theorem purely_inseparable_extension_still_satisfies_fundamental_equality
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    [IsPurelyInseparable K L]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring) :
    Module.finrank K L =
      chapterRamificationIndex vK.valuationSubring vL.valuationSubring
          (IsLocalRing.maximalIdeal vL.valuationSubring) *
      chapterResidueDegree vK.valuationSubring vL.valuationSubring
          (IsLocalRing.maximalIdeal vL.valuationSubring) := by
  sorry

/-- Complete discrete extensions have no defect factor. -/
-- STATEMENT_NEEDS_UPDATE: Complete discrete finite extensions need not be defectless when the residue field is imperfect, so the negated-defect conclusion is false. Add a defectless hypothesis (or a standard hypothesis implying it), or remove this conclusion.
theorem complete_discrete_extension_has_no_defect
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring) :
    ¬ chapter2HasDefect
      (Module.finrank K L)
      (chapterRamificationIndex vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring))
      (chapterResidueDegree vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring)) := by
  sorry

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02
