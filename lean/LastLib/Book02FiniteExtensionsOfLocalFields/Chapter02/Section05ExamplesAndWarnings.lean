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

/-- The assertion that two fixed-valued valuations give distinct branches. -/
def chapter2HasSeveralValuationExtensions
    (vK : Valuation K ℤᵐ⁰) : Prop :=
  ∃ w₁ w₂ : Valuation L ℤᵐ⁰,
    vK.IsEquiv (w₁.comap (algebraMap K L)) ∧
      vK.IsEquiv (w₂.comap (algebraMap K L)) ∧
      ¬ w₁.IsEquiv w₂

/-- In an unramified extension the whole degree is residue degree. -/
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
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vL]
    (π : A) (piRoot : L) (n : ℕ)
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
  sorry

/-- The fundamental equality still applies to purely inseparable examples. -/
theorem purely_inseparable_extension_still_satisfies_fundamental_equality
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    (hnotseparable : ¬ Algebra.IsSeparable K L)
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring) :
    Module.finrank K L =
      chapterRamificationIndex vK.valuationSubring vL.valuationSubring
          (IsLocalRing.maximalIdeal vL.valuationSubring) *
      chapterResidueDegree vK.valuationSubring vL.valuationSubring
          (IsLocalRing.maximalIdeal vL.valuationSubring) := by
  exact fundamental_equality vK vL hcomplete

/-- Complete discrete extensions have no defect factor. -/
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
  intro hdefect
  apply hdefect
  exact fundamental_equality vK vL hcomplete

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02
