import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section02TheCompletedProductTheorem
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02.Section01WhyTheValuationRingMustBeTheIntegralClosure
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02.Section03RamificationIndexAndResidueDegree
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.Section01WhyTowerFormulasMatter
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.Section03Transitivity
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.Section07NormsAndIdeals

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter15
noncomputable section

open Ideal IsLocalRing
open scoped BigOperators TensorProduct WithZero

universe u

/-! ## 15.1. The structural dictionary -/

/--
The multiplicative form of the normalized restriction formula.  Mathlib's
`Valuation` is multiplicative, so the additive identity
`v_L|_K = e • v_K` is represented by `v_L(x) = v_K(x)^e`.
-/
def normalizedValuationRestriction
    {K L Γ : Type*} [Field K] [Field L]
    [Algebra K L] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ) (e : ℕ) : Prop :=
  ∀ x : K, vL (algebraMap K L x) = (vK x) ^ e

/-- The ideal-theoretic form of `m_K B = m_L^e`. -/
def maximalIdealExtensionIsPower
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (mA : Ideal A) (mB : Ideal B) (e : ℕ) : Prop :=
  Ideal.map (algebraMap A B) mA = mB ^ e

/-
The source's opening paragraph is a bundle of compatible data rather than a
single equality.  This structure keeps the rank, ideal, valuation, and
completeness interfaces together while retaining the explicit normalization
choice required by `Valuation.HasExtension`.
-/
structure Chapter15LocalExtensionProfile
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [Module.Finite K L]
    [Algebra vK.valuationSubring L]
    [Algebra vK.valuationSubring vL.valuationSubring]
    [IsScalarTower vK.valuationSubring K L]
    [IsScalarTower vK.valuationSubring vL.valuationSubring L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    [PerfectField (IsLocalRing.ResidueField vK.valuationSubring)] where
  e : ℕ
  f : ℕ
  complete_base :
    IsAdicComplete (IsLocalRing.maximalIdeal vK.valuationSubring)
      vK.valuationSubring
  integral_closure :
    (integralClosure vK.valuationSubring L : Set L) =
      (vL.valuationSubring : Set L)
  finite_free :
    Module.Finite vK.valuationSubring vL.valuationSubring ∧
      Module.Free vK.valuationSubring vL.valuationSubring
  upstairs_complete :
    IsAdicComplete (IsLocalRing.maximalIdeal vL.valuationSubring)
      vL.valuationSubring
  upstairs_dvr : IsDiscreteValuationRing vL.valuationSubring
  e_eq_ramification_index :
    e = LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
      vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring)
  f_eq_residue_degree :
    f = LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
      vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring)
  degree_eq_ef : Module.finrank K L = e * f
  normalized_restriction : normalizedValuationRestriction vK vL e
  maximal_ideal_extension :
    maximalIdealExtensionIsPower
      (IsLocalRing.maximalIdeal vK.valuationSubring)
      (IsLocalRing.maximalIdeal vL.valuationSubring) e

/- The profile is the book-facing constructor/eliminator for the dictionary. -/
theorem complete_extension_has_local_extension_profile
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ) (e f : ℕ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [Module.Finite K L]
    [Algebra vK.valuationSubring L]
    [Algebra vK.valuationSubring vL.valuationSubring]
    [IsScalarTower vK.valuationSubring K L]
    [IsScalarTower vK.valuationSubring vL.valuationSubring L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    [PerfectField (IsLocalRing.ResidueField vK.valuationSubring)]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (he : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
      vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring) = e)
    (hf : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
      vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring) = f)
    (hrestriction : normalizedValuationRestriction vK vL e) :
    ∃ d : Chapter15LocalExtensionProfile vK vL,
      d.e = e ∧ d.f = f ∧
        IsAdicComplete (IsLocalRing.maximalIdeal vK.valuationSubring)
          vK.valuationSubring := by
  have hstruct :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.finite_complete_extension_valuation_ring
      vK vL hcomplete
  have hfinite : Module.Finite vK.valuationSubring vL.valuationSubring :=
    inferInstance
  have hfree : Module.Free vK.valuationSubring vL.valuationSubring := by
    apply LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.finite_torsion_free_over_dvr_is_free
    intro a x ha hax
    apply Subtype.ext
    have haK : (a : K) ≠ 0 := by
      intro haK
      apply ha
      exact Subtype.ext haK
    have haL : algebraMap vK.valuationSubring L a ≠ 0 := by
      intro hzero
      apply haK
      apply FaithfulSMul.algebraMap_injective K L
      simpa [IsScalarTower.algebraMap_eq vK.valuationSubring K L] using hzero
    have haB : algebraMap vK.valuationSubring vL.valuationSubring a ≠ 0 := by
      intro hzero
      apply haL
      have hcomp := IsScalarTower.algebraMap_eq
        vK.valuationSubring vL.valuationSubring L
      have hcomp_a := congrArg (fun g => g a) hcomp
      have hzeroL : algebraMap vK.valuationSubring L a = 0 := by
        calc
          algebraMap vK.valuationSubring L a =
              ((algebraMap vL.valuationSubring L).comp
                (algebraMap vK.valuationSubring vL.valuationSubring)) a :=
            hcomp_a
          _ = algebraMap vL.valuationSubring L
                (algebraMap vK.valuationSubring vL.valuationSubring a) := by rfl
          _ = 0 := by rw [hzero, map_zero]
      exact hzeroL
    have hax' :
        algebraMap vK.valuationSubring vL.valuationSubring a = 0 ∨ x = 0 := by
      have h := congrArg (fun y : vL.valuationSubring => (y : L)) hax
      simpa [Algebra.smul_def,
        Valuation.HasExtension.coe_algebraMap_valuationSubring_eq] using h
    rcases hax' with hzero | hzero
    · exact (haB hzero).elim
    · simpa using hzero
  have hAB :
      (algebraMap vK.valuationSubring vL.valuationSubring) =
        @algebraMap vK.valuationSubring vL.valuationSubring _ _
          (Valuation.HasExtension.instAlgebra_valuationSubring vK vL) := by
    ext a
    have hAK : algebraMap vK.valuationSubring K a = (a : K) := rfl
    calc
      ((algebraMap vK.valuationSubring vL.valuationSubring) a : L) =
          algebraMap vL.valuationSubring L
            ((algebraMap vK.valuationSubring vL.valuationSubring) a) := rfl
      _ = algebraMap vK.valuationSubring L a := by
        have hcomp := IsScalarTower.algebraMap_eq
          vK.valuationSubring vL.valuationSubring L
        have hcomp_a := congrArg (fun g => g a) hcomp
        simpa only [RingHom.coe_comp, Function.comp_apply] using hcomp_a.symm
      _ = algebraMap K L (a : K) := by
        have hcomp := IsScalarTower.algebraMap_eq
          vK.valuationSubring K L
        have hcomp_a := congrArg (fun g => g a) hcomp
        simpa only [RingHom.coe_comp, Function.comp_apply, hAK] using hcomp_a
      _ = ((@algebraMap vK.valuationSubring vL.valuationSubring _ _
          (Valuation.HasExtension.instAlgebra_valuationSubring vK vL) a : L)) := by
        symm
        simp [Valuation.HasExtension.coe_algebraMap_valuationSubring_eq]
  have hAlg :
      (inferInstance : Algebra vK.valuationSubring vL.valuationSubring) =
        Valuation.HasExtension.instAlgebra_valuationSubring vK vL := by
    apply IsScalarTower.Algebra.ext
      (inferInstance : Algebra vK.valuationSubring vL.valuationSubring)
      (Valuation.HasExtension.instAlgebra_valuationSubring vK vL)
    intro a x
    rw [@Algebra.smul_def _ _ _ _
      (inferInstance : Algebra vK.valuationSubring vL.valuationSubring)]
    rw [@Algebra.smul_def _ _ _ _
      (Valuation.HasExtension.instAlgebra_valuationSubring vK vL)]
    rw [hAB]
  have hram :
      @LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
        vK.valuationSubring vL.valuationSubring _ _
        (Valuation.HasExtension.instAlgebra_valuationSubring vK vL)
        (IsLocalRing.maximalIdeal vL.valuationSubring) =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
        vK.valuationSubring vL.valuationSubring
          (IsLocalRing.maximalIdeal vL.valuationSubring) := by
    unfold LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
    cases hAlg
    rfl
  have hintertia :
      @LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
        vK.valuationSubring vL.valuationSubring _ _
        (Valuation.HasExtension.instAlgebra_valuationSubring vK vL)
        (IsLocalRing.maximalIdeal vL.valuationSubring) =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
        vK.valuationSubring vL.valuationSubring
          (IsLocalRing.maximalIdeal vL.valuationSubring) := by
    unfold LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
    cases hAlg
    rfl
  have hstructDegree :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.complete_extension_ideal_and_residue_formulas
      vK vL e f (by simpa only [hram] using he)
      (by simpa only [hintertia] using hf) hcomplete
  have hdegree : Module.finrank K L = e * f := by
    simpa only [hram, hintertia, he, hf] using
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.complete_extension_defectless_without_separability
        vK vL hcomplete)
  have hALmap :
      (algebraMap vK.valuationSubring L) =
        @algebraMap vK.valuationSubring L _ _
          (Algebra.ofSubsemiring vK.valuationSubring) := by
    ext a
    have hAK : algebraMap vK.valuationSubring K a = (a : K) := rfl
    have hcomp := IsScalarTower.algebraMap_eq
      vK.valuationSubring K L
    have hcomp_a := congrArg (fun g => g a) hcomp
    calc
      algebraMap vK.valuationSubring L a =
          algebraMap K L (a : K) := by
            simpa only [RingHom.coe_comp, Function.comp_apply, hAK] using hcomp_a
      _ = (@algebraMap vK.valuationSubring L _ _
          (Algebra.ofSubsemiring vK.valuationSubring)) a := by rfl
  have hAL :
      (inferInstance : Algebra vK.valuationSubring L) =
        Algebra.ofSubsemiring vK.valuationSubring := by
    apply IsScalarTower.Algebra.ext
      (inferInstance : Algebra vK.valuationSubring L)
      (Algebra.ofSubsemiring vK.valuationSubring)
    intro a x
    rw [@Algebra.smul_def _ _ _ _
      (inferInstance : Algebra vK.valuationSubring L)]
    rw [@Algebra.smul_def _ _ _ _
      (Algebra.ofSubsemiring vK.valuationSubring)]
    rw [hALmap]
  have hc :
      (integralClosure vK.valuationSubring L : Set L) =
        (vL.valuationSubring : Set L) := by
    cases hAL
    exact hstruct.2.2.2.2.symm
  have hfinrank : Module.finrank vK.valuationSubring vL.valuationSubring =
      Module.finrank K L := by
    let _ : IsFractionRing vK.valuationSubring K :=
      (Valuation.valuationSubring.integers vK).isFractionRing
    let _ : IsFractionRing vL.valuationSubring L :=
      (Valuation.valuationSubring.integers vL).isFractionRing
    exact (IsFractionRing.finrank_eq vK.valuationSubring K
      vL.valuationSubring L).symm
  let _ : Module.Free vK.valuationSubring vL.valuationSubring := hfree
  have b : Module.Basis (Fin (Module.finrank K L))
      vK.valuationSubring vL.valuationSubring :=
    Module.finBasisOfFinrankEq vK.valuationSubring
      vL.valuationSubring hfinrank
  have hideal :
      Ideal.map (algebraMap vK.valuationSubring vL.valuationSubring)
        (IsLocalRing.maximalIdeal vK.valuationSubring) =
        (IsLocalRing.maximalIdeal vL.valuationSubring) ^ e := by
    simpa only [hAB] using hstructDegree.1
  refine ⟨
    { e := e
      f := f
      complete_base := hcomplete
      integral_closure := hc
      finite_free := ⟨hfinite, hfree⟩
      upstairs_complete := hstruct.2.2.1
      upstairs_dvr := hstruct.2.2.2.1
      e_eq_ramification_index := he.symm
      f_eq_residue_degree := hf.symm
      degree_eq_ef := hdegree
      normalized_restriction := hrestriction
      maximal_ideal_extension := hideal },
    rfl, rfl, hcomplete⟩

/--
Residue trace and norm formulas are stated with the residue maps explicit.
This avoids pretending that Mathlib can infer a map between arbitrary
quotients from ideals alone; in the local-field application these maps are
the canonical quotient residue maps.
-/
-- SOURCE_ISSUE: The residue trace and norm identities in §15.1 also rely on
-- defectlessness: applying the trace identity to a base element detects the
-- degree factor.  The shadow data therefore records the independent
-- defectless rank equality instead of asserting the identities from only the
-- ring and residue maps.
structure Chapter15ResidueArithmeticShadow
    {A B k l : Type*} [CommRing A] [CommRing B] [Field k] [Field l]
    [Algebra A B] [Algebra k l]
    [IsLocalRing A] [IsLocalRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsIntegrallyClosed A] [IsIntegrallyClosed B]
    [Algebra.IsIntegral A B]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [FiniteDimensional k l] where
  e : ℕ
  f : ℕ
  e_eq_ramification_index :
    e = LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
      A B (IsLocalRing.maximalIdeal B)
  f_eq_residue_degree :
    f = LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
      A B (IsLocalRing.maximalIdeal B)
  f_eq_residue_finrank : f = Module.finrank k l
  degree_eq_ef : Module.finrank A B = e * f
  baseResidue : A →+* k
  extensionResidue : B →+* l
  baseResidue_is_residue_map :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11ResidueMap
      A k (IsLocalRing.maximalIdeal A) baseResidue
  extensionResidue_is_residue_map :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11ResidueMap
      B l (IsLocalRing.maximalIdeal B) extensionResidue
  residueCompatibility : ∀ a : A,
    extensionResidue (algebraMap A B a) = algebraMap k l (baseResidue a)

/--
Book 2, §15.1: in a finite extension of complete discretely valued fields,
the valuation ring upstairs is the integral closure and is finite free.  The
rank is exposed by a basis indexed by the field degree.
-/
theorem complete_extension_has_finite_free_integral_closure
    {K L Γ : Type*} [Field K] [Field L]
    [Algebra K L] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [Module.Finite K L]
    [Algebra vK.valuationSubring L]
    [IsScalarTower vK.valuationSubring K L]
    [IsScalarTower vK.valuationSubring vL.valuationSubring L]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring) :
    (integralClosure vK.valuationSubring L : Set L) =
        (vL.valuationSubring : Set L) ∧
      Module.Finite vK.valuationSubring vL.valuationSubring ∧
      Module.Free vK.valuationSubring vL.valuationSubring ∧
    Nonempty (Module.Basis (Fin (Module.finrank K L))
        vK.valuationSubring vL.valuationSubring) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal vL.valuationSubring)
        vL.valuationSubring ∧
      IsDiscreteValuationRing vL.valuationSubring := by
  have hstruct :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.finite_complete_extension_valuation_ring
      vK vL hcomplete
  let _ : Module.Finite vK.valuationSubring vL.valuationSubring := hstruct.1
  let _ : Module.Free vK.valuationSubring vL.valuationSubring := hstruct.2.1
  let _ : IsFractionRing vK.valuationSubring K :=
    (Valuation.valuationSubring.integers vK).isFractionRing
  let _ : IsFractionRing vL.valuationSubring L :=
    (Valuation.valuationSubring.integers vL).isFractionRing
  have hfinrank : Module.finrank vK.valuationSubring vL.valuationSubring =
      Module.finrank K L :=
    (IsFractionRing.finrank_eq vK.valuationSubring K
      vL.valuationSubring L).symm
  have b : Module.Basis (Fin (Module.finrank K L))
      vK.valuationSubring vL.valuationSubring :=
    Module.finBasisOfFinrankEq vK.valuationSubring
      vL.valuationSubring hfinrank
  have halg : algebraMap vK.valuationSubring L =
      (Algebra.ofSubsemiring vK.valuationSubring).algebraMap := by
    apply RingHom.ext
    intro a
    exact IsScalarTower.algebraMap_apply
      vK.valuationSubring K L a
  have hclosure : (integralClosure vK.valuationSubring L : Set L) =
      (vL.valuationSubring : Set L) := by
    ext z
    have hz := Set.ext_iff.mp hstruct.2.2.2.2.symm z
    change (algebraMap vK.valuationSubring L).IsIntegralElem z ↔
      z ∈ vL.valuationSubring
    rw [halg]
    exact hz
  refine ⟨hclosure, hstruct.1, hstruct.2.1, ⟨b⟩, ?_, ?_⟩
  · exact hstruct.2.2.1
  · exact hstruct.2.2.2.1

/-
The class `Valuation.HasExtension` identifies the restriction only up to
valuation equivalence.  It therefore does not by itself justify the literal
normalization used in the displayed power formula.
-/
-- API_NOTE: The source writes a literal equality for normalized
-- valuations, but the canonical extension interface supplies only valuation
-- equivalence.  The bridge below records that canonical weaker fact; the
-- displayed normalization is exposed with an explicit normalization datum.
theorem restriction_is_equivalent_to_base_valuation
    {K L : Type*} [Field K] [Field L]
    [Algebra K L]
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] :
    vK.IsEquiv (vL.comap (algebraMap K L)) :=
  Valuation.HasExtension.val_isEquiv_comap

/- The explicit normalization datum needed for a literal power formula. -/
structure Chapter15NormalizedValuationChoice
    {K L : Type*} [Field K] [Field L]
    [Algebra K L]
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [Module.Finite K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring] where
  e : ℕ
  e_eq_ramification_index :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
      vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring) = e
  restriction : normalizedValuationRestriction vK vL e

/- Book 2, §15.1: the normalized valuation restriction carries the factor
`e`, once the chosen representatives have been normalized literally. -/
theorem normalized_restriction_has_ramification_factor
    {K L : Type*} [Field K] [Field L]
    [Algebra K L]
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL]
    [Module.Finite K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    (d : Chapter15NormalizedValuationChoice vK vL) :
    normalizedValuationRestriction vK vL d.e :=
  d.restriction

/-- Book 2, §15.1: extension of the base maximal ideal. -/
theorem maximal_ideal_extension_is_ramification_power
    {K L : Type*} [Field K] [Field L]
    [Algebra K L]
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰) (e : ℕ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [Module.Finite K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    (he : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
      vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring) = e) :
    maximalIdealExtensionIsPower
      (IsLocalRing.maximalIdeal vK.valuationSubring)
      (IsLocalRing.maximalIdeal vL.valuationSubring) e := by
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02.maximal_ideal_extension_is_power
      vK vL e he

/-- Book 2, §15.1: one valuation/residue block accounts for `e * f` dimensions. -/
-- SOURCE_ISSUE: §§15.1–15.2 state `[L : K] = e f` for every finite extension of a complete discretely valued field without a defectless or perfect-residue hypothesis. Complete discretely valued fields with imperfect residue field can have finite defect extensions, so the equality is false as stated; the minimally corrected interface below assumes a perfect base residue field, a standard hypothesis implying defectlessness.
theorem complete_extension_degree_is_ramification_times_residue_degree
    {K L Γ : Type*} [Field K] [Field L]
    [Algebra K L] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ) (e f : ℕ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [Module.Finite K L]
    [PerfectField (IsLocalRing.ResidueField vK.valuationSubring)]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (he : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
      vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring) = e)
    (hf : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
      vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring) = f)
    :
    Module.finrank K L = e * f := by
  simpa only [he, hf] using
    (LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.complete_extension_defectless_without_separability
      vK vL hcomplete)

/-- Book 2, §15.1: both local indices multiply in a tower. -/
theorem ramification_and_residue_degrees_multiply_in_a_tower
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T]
    (p : Ideal R) (q : Ideal S) (r : Ideal T)
    [p.IsPrime] [q.IsPrime] [r.IsPrime]
    [q.LiesOver p] [r.LiesOver q] [Module.Flat S T] :
    r.ramificationIdx R = q.ramificationIdx R * r.ramificationIdx S ∧
      r.inertiaDeg R = q.inertiaDeg R * r.inertiaDeg S := by
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03_tower_ramification_and_residue_laws
      p q r

/-- Book 2, §15.1: trace and norm transfer through a finite tower. -/
theorem trace_and_norm_transfer_in_a_tower
    {K M L : Type*} [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]
    [Module.Finite K M] [Module.Finite M L] [Module.Finite K L] (x : L) :
    Algebra.trace K L x = Algebra.trace K M (Algebra.trace M L x) ∧
      Algebra.norm K x = Algebra.norm K (Algebra.norm M x) := by
  exact ⟨
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04_trace_transitive
      K M L x,
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04_norm_transitive
      K M L x⟩

private noncomputable def chapter15_additive_valuation_of_multiplicative
    {R : Type*} [Field R] (v : Valuation R ℤᵐ⁰) :
    AddValuation R (WithTop ℤ) := by
  apply AddValuation.of
    (fun z => if hz : v z = 0 then ⊤ else
      ((- (WithZero.log (M := ℤ) (v z) : ℤ)) : WithTop ℤ))
  · simp
  · simp
  · intro a b
    by_cases ha : a = 0
    · subst a
      rw [zero_add]
      simp [v.map_zero]
    by_cases hb : b = 0
    · subst b
      rw [add_zero]
      simp [v.map_zero]
    have haV : v a ≠ 0 := v.ne_zero_iff.mpr ha
    have hbV : v b ≠ 0 := v.ne_zero_iff.mpr hb
    by_cases hab : a + b = 0
    · rw [hab]
      simp
    have habV : v (a + b) ≠ 0 := v.ne_zero_iff.mpr hab
    by_cases horder : v a ≤ v b
    · have hsum : v (a + b) ≤ v b := by
        simpa [max_eq_right horder] using map_add_le_max v a b
      have hlog : WithZero.log (M := ℤ) (v (a + b)) ≤
          WithZero.log (M := ℤ) (v b) :=
        (WithZero.log_le_log habV hbV).2 hsum
      have hlogab : WithZero.log (M := ℤ) (v a) ≤
          WithZero.log (M := ℤ) (v b) :=
        (WithZero.log_le_log haV hbV).2 horder
      simp only [dif_neg haV, dif_neg hbV, dif_neg habV]
      change min ((-(WithZero.log (M := ℤ) (v a) : ℤ) : WithTop ℤ))
          ((-(WithZero.log (M := ℤ) (v b) : ℤ) : WithTop ℤ)) ≤
        ((-(WithZero.log (M := ℤ) (v (a + b)) : ℤ) : WithTop ℤ))
      rw [min_eq_right (by exact_mod_cast (neg_le_neg hlogab))]
      exact_mod_cast (neg_le_neg hlog)
    · have horder' : v b ≤ v a := le_of_not_ge horder
      have hsum : v (a + b) ≤ v a := by
        simpa [max_eq_left horder'] using map_add_le_max v a b
      have hlog : WithZero.log (M := ℤ) (v (a + b)) ≤
          WithZero.log (M := ℤ) (v a) :=
        (WithZero.log_le_log habV haV).2 hsum
      have hlogab : WithZero.log (M := ℤ) (v b) ≤
          WithZero.log (M := ℤ) (v a) :=
        (WithZero.log_le_log hbV haV).2 horder'
      simp only [dif_neg haV, dif_neg hbV, dif_neg habV]
      change min ((-(WithZero.log (M := ℤ) (v a) : ℤ) : WithTop ℤ))
          ((-(WithZero.log (M := ℤ) (v b) : ℤ) : WithTop ℤ)) ≤
        ((-(WithZero.log (M := ℤ) (v (a + b)) : ℤ) : WithTop ℤ))
      rw [min_eq_left (by exact_mod_cast (neg_le_neg hlogab))]
      exact_mod_cast (neg_le_neg hlog)
  · intro a b
    by_cases hab : v (a * b) = 0
    · have hm : v a * v b = 0 := by simpa only [← v.map_mul] using hab
      rcases mul_eq_zero.mp hm with ha | hb
      · simp [hab, ha]
      · simp [hab, hb]
    · have ha : v a ≠ 0 := by
        intro ha
        apply hab
        rw [v.map_mul, ha, zero_mul]
      have hb : v b ≠ 0 := by
        intro hb
        apply hab
        rw [v.map_mul, hb, mul_zero]
      simp only [dif_neg hab, dif_neg ha, dif_neg hb]
      rw [v.map_mul, WithZero.log_mul ha hb]
      push_cast
      exact_mod_cast (neg_add (v a).log (v b).log)

private theorem chapter15_additive_valuation_equiv
    {R : Type*} [Field R] (v : Valuation R ℤᵐ⁰) :
    v.IsEquiv (chapter15_additive_valuation_of_multiplicative v).toValuation := by
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  by_cases hx : x = 0
  · simp [hx, chapter15_additive_valuation_of_multiplicative]
  · have hvx : v x ≠ 0 := v.ne_zero_iff.mpr hx
    simp only [chapter15_additive_valuation_of_multiplicative,
      AddValuation.toValuation_apply, AddValuation.of_apply, dif_neg hvx]
    change v x ≤ 1 ↔
      Multiplicative.ofAdd (OrderDual.toDual
        ((-(WithZero.log (M := ℤ) (v x) : ℤ) : WithTop ℤ))) ≤ 1
    change v x ≤ 1 ↔
      (0 : WithTop ℤ) ≤
        -((WithZero.log (M := ℤ) (v x) : ℤ) : WithTop ℤ)
    constructor
    · intro h
      have hlog :=
        (WithZero.log_le_log hvx (by exact one_ne_zero)).2 h
      have hlog' : WithZero.log (M := ℤ) (v x) ≤ 0 := by
        simpa using hlog
      exact_mod_cast (neg_nonneg.mpr hlog')
    · intro h
      have hneg : (0 : ℤ) ≤ -(WithZero.log (M := ℤ) (v x)) := by
        exact_mod_cast h
      have hlog : WithZero.log (M := ℤ) (v x) ≤ 0 := neg_nonneg.mp hneg
      apply (WithZero.log_le_log hvx (by exact one_ne_zero)).1
      simpa using hlog

private theorem chapter15_additive_extension_equiv
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] :
    (chapter15_additive_valuation_of_multiplicative vK).IsEquiv
      (AddValuation.comap (algebraMap K L)
        (chapter15_additive_valuation_of_multiplicative vL)) := by
  let vK' := chapter15_additive_valuation_of_multiplicative vK
  let vL' := chapter15_additive_valuation_of_multiplicative vL
  have hK : vK.IsEquiv vK'.toValuation :=
    chapter15_additive_valuation_equiv vK
  have hL : vL.IsEquiv vL'.toValuation :=
    chapter15_additive_valuation_equiv vL
  change vK'.toValuation.IsEquiv
    (Valuation.comap (algebraMap K L) vL'.toValuation)
  exact hK.symm.trans ((Valuation.HasExtension.val_isEquiv_comap).trans
    (hL.comap (algebraMap K L)))

private theorem chapter15_additive_value_eq_of_multiplicative_value_eq
    {R : Type*} [Field R] (v : Valuation R ℤᵐ⁰) {x y : R}
    (hxy : v x = v y) :
    chapter15_additive_valuation_of_multiplicative v x =
      chapter15_additive_valuation_of_multiplicative v y := by
  change (if v x = 0 then (⊤ : WithTop ℤ) else
      (- (WithZero.log (M := ℤ) (v x) : ℤ) : WithTop ℤ)) =
    (if v y = 0 then (⊤ : WithTop ℤ) else
      (- (WithZero.log (M := ℤ) (v y) : ℤ) : WithTop ℤ))
  rw [hxy]

private theorem chapter15_additive_valuation_rank_one
    {R : Type*} [Field R] (v : Valuation R ℤᵐ⁰)
    [Valuation.IsRankOneDiscrete v] :
    Valuation.IsRankOneDiscrete
      (chapter15_additive_valuation_of_multiplicative v).toValuation := by
  let w := chapter15_additive_valuation_of_multiplicative v
  let g := Valuation.IsRankOneDiscrete.generator v
  obtain ⟨π, hπ⟩ := Valuation.IsRankOneDiscrete.generator_mem_range R v
  have hπ0 : π ≠ 0 := by
    intro h
    apply Units.ne_zero (Valuation.IsRankOneDiscrete.generator v)
    rw [← hπ, h]
    exact map_zero v
  let γ : (Multiplicative (WithTop ℤ)ᵒᵈ)ˣ :=
    Units.mk0 (w.toValuation π) (w.toValuation.ne_zero_iff.mpr hπ0)
  have hK : v.IsEquiv w.toValuation :=
    chapter15_additive_valuation_equiv v
  have hγlt : γ < 1 := by
    rw [← Units.val_lt_val]
    change w.toValuation π < 1
    have hlt := (Valuation.isEquiv_iff_val_lt_val.mp hK).1
      (show v π < v 1 by
        rw [hπ]
        simpa using ((Units.val_lt_val).2
          (Valuation.IsRankOneDiscrete.generator_lt_one v)))
    simpa only [map_one] using hlt
  refine ⟨γ, ?_, hγlt⟩
  apply le_antisymm
  · intro u hu
    rcases Subgroup.mem_zpowers_iff.mp hu with ⟨n, rfl⟩
    apply MonoidWithZeroHom.mem_valueGroup
    refine ⟨π ^ n, ?_⟩
    change w.toValuation (π ^ n) = (γ ^ n).val
    simp [γ, w, AddValuation.toValuation_apply]
  · intro u hu
    have hu' : u.val ∈
        Set.range (MonoidWithZeroHom.ofClass w.toValuation) \ {0} := by
      rw [← MonoidWithZeroHom.valueGroup_eq_range]
      exact ⟨u, hu, rfl⟩
    rcases hu' with ⟨⟨x, hx⟩, hux0⟩
    change w.toValuation x = u.val at hx
    have hfx : w.toValuation x ≠ 0 := by
      rw [hx]
      exact hux0
    have hx0 : x ≠ 0 := w.toValuation.ne_zero_iff.mp hfx
    have hgen : v x ∈
        Units.val '' (Subgroup.zpowers (Valuation.IsRankOneDiscrete.generator v)) := by
      rw [Valuation.IsRankOneDiscrete.generator_zpowers_eq_range R v]
      exact ⟨⟨x, rfl⟩, v.ne_zero_iff.mpr hx0⟩
    rcases hgen with ⟨z, hz, hzx⟩
    rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, rfl⟩
    apply (Subgroup.mem_zpowers_iff).2
    refine ⟨n, ?_⟩
    apply (Units.ext_iff).2
    have hval : v x = v (π ^ n) := by
      calc
        v x = (↑(Valuation.IsRankOneDiscrete.generator v ^ n) : ℤᵐ⁰) := hzx.symm
        _ = (↑(Valuation.IsRankOneDiscrete.generator v) : ℤᵐ⁰) ^ n := by simp
        _ = v (π ^ n) := by rw [map_zpow₀ v π n, hπ]
    have hadd : w x = w (π ^ n) := by
      exact chapter15_additive_value_eq_of_multiplicative_value_eq v hval
    symm
    rw [← hx]
    have hadd' : w.toValuation x = w.toValuation (π ^ n) := by
      exact congrArg (fun z : WithTop ℤ =>
        Multiplicative.ofAdd (OrderDual.toDual z)) hadd
    change w.toValuation x = (γ ^ n).val
    rw [hadd']
    simp [γ, w, AddValuation.toValuation_apply]

/-- Book 2, §15.1: the valuation of a norm records the residue degree. -/
-- SOURCE_ISSUE: The norm valuation identity in §15.1 implies the degree
-- equality when applied to a nonzero base element, so it is also false for a
-- finite defect extension.  The corrected interface assumes a perfect base
-- residue field and completeness, which imply defectlessness in this setting.
-- It also requires the literal normalized restriction: `HasExtension` alone
-- provides only valuation equivalence and cannot determine the displayed
-- power formula.
theorem structural_norm_valuation_formula
    {K L : Type*} [Field K] [Field L]
    [Algebra K L]
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰) (f : ℕ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [Module.Finite K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    [PerfectField (IsLocalRing.ResidueField vK.valuationSubring)]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (hf : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
      vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring) = f)
    (hrestriction : normalizedValuationRestriction vK vL
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
        vK.valuationSubring vL.valuationSubring
          (IsLocalRing.maximalIdeal vL.valuationSubring)))
    (x : L) :
    vK (Algebra.norm K x) = (vL x) ^ f := by
  let e : ℕ :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
      vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring)
  let wK := chapter15_additive_valuation_of_multiplicative vK
  let wL := chapter15_additive_valuation_of_multiplicative vL
  let _ : Valuation.IsRankOneDiscrete wK.toValuation :=
    chapter15_additive_valuation_rank_one vK
  let _ : Valuation.IsRankOneDiscrete wL.toValuation :=
    chapter15_additive_valuation_rank_one vL
  have hK : vK.IsEquiv wK.toValuation :=
    chapter15_additive_valuation_equiv vK
  have hL : vL.IsEquiv wL.toValuation :=
    chapter15_additive_valuation_equiv vL
  have hext : wK.IsEquiv (AddValuation.comap (algebraMap K L) wL) := by
    exact chapter15_additive_extension_equiv vK vL
  have he : 0 < e := by
    dsimp [e]
    unfold LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
    exact Ideal.ramificationIdx_pos _ _
  have hfpos : 0 < f := by
    rw [← hf]
    unfold LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
    exact Ideal.inertiaDeg_pos _ _
  have hdegree : Module.finrank K L = e * f := by
    have h :=
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.complete_extension_defectless_without_separability
        vK vL hcomplete
    simpa only [e, hf] using h
  have hKring : vK.valuationSubring = wK.toValuation.valuationSubring :=
    (Valuation.isEquiv_iff_valuationSubring vK wK.toValuation).mp hK
  have hLring : vL.valuationSubring = wL.toValuation.valuationSubring :=
    (Valuation.isEquiv_iff_valuationSubring vL wL.toValuation).mp hL
  have hfadd : f =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
        wK wL hext := by
    have hres :=
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02.residue_degree_is_residue_field_finrank
        vK vL
    have hres' : f =
        Module.finrank (IsLocalRing.ResidueField vK.valuationSubring)
          (IsLocalRing.ResidueField vL.valuationSubring) :=
      hf.symm.trans hres
    let _ : Valuation.HasExtension wK.toValuation wL.toValuation := ⟨hext⟩
    simp only [
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree,
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField]
    let eK0hom : vK.valuationSubring →+* wK.toValuation.valuationSubring :=
      { toFun := fun a =>
          ⟨(a : K), by
            rw [← hKring]
            exact a.property⟩
        map_one' := by ext; rfl
        map_mul' := by intro a b; ext; rfl
        map_zero' := by ext; rfl
        map_add' := by intro a b; ext; rfl }
    have heK0bij : Function.Bijective eK0hom := by
      constructor
      · intro a b hab
        apply Subtype.ext
        exact congrArg (fun z : wK.toValuation.valuationSubring => (z : K)) hab
      · intro b
        refine ⟨⟨(b : K), ?_⟩, ?_⟩
        · rw [hKring]
          exact b.property
        · exact Subtype.ext rfl
    let eK0 : vK.valuationSubring ≃+* wK.toValuation.valuationSubring :=
      RingEquiv.ofBijective eK0hom heK0bij
    let eL0hom : vL.valuationSubring →+* wL.toValuation.valuationSubring :=
      { toFun := fun a =>
          ⟨(a : L), by
            rw [← hLring]
            exact a.property⟩
        map_one' := by ext; rfl
        map_mul' := by intro a b; ext; rfl
        map_zero' := by ext; rfl
        map_add' := by intro a b; ext; rfl }
    have heL0bij : Function.Bijective eL0hom := by
      constructor
      · intro a b hab
        apply Subtype.ext
        exact congrArg (fun z : wL.toValuation.valuationSubring => (z : L)) hab
      · intro b
        refine ⟨⟨(b : L), ?_⟩, ?_⟩
        · rw [hLring]
          exact b.property
        · exact Subtype.ext rfl
    let eL0 : vL.valuationSubring ≃+* wL.toValuation.valuationSubring :=
      RingEquiv.ofBijective eL0hom heL0bij
    let eK : IsLocalRing.ResidueField vK.valuationSubring ≃+*
        IsLocalRing.ResidueField wK.toValuation.valuationSubring :=
      IsLocalRing.ResidueField.mapEquiv eK0
    let eL : IsLocalRing.ResidueField vL.valuationSubring ≃+*
        IsLocalRing.ResidueField wL.toValuation.valuationSubring :=
      IsLocalRing.ResidueField.mapEquiv eL0
    have hfin :
        Module.finrank (IsLocalRing.ResidueField vK.valuationSubring)
            (IsLocalRing.ResidueField vL.valuationSubring) =
          Module.finrank (IsLocalRing.ResidueField wK.toValuation.valuationSubring)
            (IsLocalRing.ResidueField wL.toValuation.valuationSubring) := by
      apply Algebra.finrank_eq_of_equiv_equiv eK eL
      apply RingHom.ext
      intro a
      exact Quotient.inductionOn' a (fun _ => rfl)
    exact hres'.trans hfin
  have hrestrict_add : ∀ y : K,
      wL (algebraMap K L y) = (e : WithTop ℤ) * wK y := by
    intro y
    by_cases hy : y = 0
    · subst y
      have he0 : (e : WithTop ℤ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt he)
      simpa [wK, wL, chapter15_additive_valuation_of_multiplicative] using
        (WithTop.mul_top he0).symm
    · have hyK : vK y ≠ 0 := vK.ne_zero_iff.mpr hy
      have hyL : vL (algebraMap K L y) ≠ 0 := by
        rw [hrestriction y]
        exact pow_ne_zero _ hyK
      simp only [wK, wL, chapter15_additive_valuation_of_multiplicative,
        AddValuation.of_apply, dif_neg hyL, dif_neg hyK]
      rw [hrestriction y, WithZero.log_pow]
      dsimp [e]
      have hz :
          -((LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
                vK.valuationSubring vL.valuationSubring
                  (IsLocalRing.maximalIdeal vL.valuationSubring) : ℤ) *
              WithZero.log (M := ℤ) (vK y)) =
            (LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
                vK.valuationSubring vL.valuationSubring
                  (IsLocalRing.maximalIdeal vL.valuationSubring) : ℤ) *
              -WithZero.log (M := ℤ) (vK y) := by
        ring
      exact_mod_cast hz
  have hunique : ∀ w : AddValuation L (WithTop ℤ),
      wK.IsEquiv (AddValuation.comap (algebraMap K L) w) → wL.IsEquiv w := by
    intro w hw
    have hwv : vK.IsEquiv (Valuation.comap (algebraMap K L) w.toValuation) := by
      change vK.IsEquiv (AddValuation.comap (algebraMap K L) w).toValuation
      exact hK.trans hw
    let W : ValuationSubring L := w.toValuation.valuationSubring
    have hW :
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02.chapter2ValuationSubringExtends
          vK W := by
      ext y
      change w.toValuation (algebraMap K L y) ≤ 1 ↔ vK y ≤ 1
      simpa only [Valuation.comap_apply] using
        (Valuation.isEquiv_iff_val_le_one.mp hwv (x := y)).symm
    have hWuniq :=
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02.chapter2_complete_base_has_unique_valuation_subring_extension
        vK vL hcomplete
    have hsub : w.toValuation.valuationSubring = vL.valuationSubring := by
      ext z
      exact Set.ext_iff.mp (hWuniq.2 W hW) z
    have hwvL : vL.IsEquiv w.toValuation :=
      (Valuation.isEquiv_iff_valuationSubring vL w.toValuation).2 hsub.symm
    change wL.toValuation.IsEquiv w.toValuation
    exact hL.symm.trans hwvL
  by_cases hx : x = 0
  · subst x
    simp [hfpos.ne']
  · have hnorm :=
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11_single_branch_norm_valuation_formula
        K L e f hext he hrestrict_add hfadd hunique hdegree x hx
    have hnorm0 : Algebra.norm K x ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx
    have hvnorm0 : vK (Algebra.norm K x) ≠ 0 := vK.ne_zero_iff.mpr hnorm0
    have hlog :
        (-(WithZero.log (M := ℤ) (vK (Algebra.norm K x)) : ℤ) : WithTop ℤ) =
          (f : WithTop ℤ) *
            (-(WithZero.log (M := ℤ) (vL x) : ℤ) : WithTop ℤ) := by
      simpa only [wK, wL, chapter15_additive_valuation_of_multiplicative,
        AddValuation.of_apply, dif_neg hvnorm0,
        dif_neg (vL.ne_zero_iff.mpr hx)] using hnorm
    have hneg :
        -WithZero.log (M := ℤ) (vK (Algebra.norm K x)) =
          (f : ℤ) * -WithZero.log (M := ℤ) (vL x) := by
      exact_mod_cast hlog
    have hlogpow :
        WithZero.log (M := ℤ) (vK (Algebra.norm K x)) =
          WithZero.log (M := ℤ) ((vL x) ^ f) := by
      rw [WithZero.log_pow]
      simpa [smul_eq_mul] using (show
        WithZero.log (M := ℤ) (vK (Algebra.norm K x)) =
          (f : ℤ) * WithZero.log (M := ℤ) (vL x) by
            calc
              WithZero.log (M := ℤ) (vK (Algebra.norm K x)) =
                  -(-WithZero.log (M := ℤ) (vK (Algebra.norm K x))) := by ring
              _ = -((f : ℤ) * -WithZero.log (M := ℤ) (vL x)) := by rw [hneg]
              _ = (f : ℤ) * WithZero.log (M := ℤ) (vL x) := by ring)
    calc
      vK (Algebra.norm K x) =
          WithZero.exp (WithZero.log (M := ℤ) (vK (Algebra.norm K x))) :=
        (WithZero.exp_log hvnorm0).symm
      _ = WithZero.exp (WithZero.log (M := ℤ) ((vL x) ^ f)) := by rw [hlogpow]
      _ = (vL x) ^ f :=
        WithZero.exp_log (pow_ne_zero _ (vL.ne_zero_iff.mpr hx))

/-- Book 2, §15.1: the residue trace shadow, with no separability assumption. -/
theorem residue_trace_shadow_formula
    {A B k l : Type*} [CommRing A] [CommRing B] [Field k] [Field l]
    [Algebra A B] [Algebra k l]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra.IsIntegral A B]
    [Module.Finite A B] [Module.Free A B]
    [Module.Finite k l] [Module.Free k l]
    (d : Chapter15ResidueArithmeticShadow) (x : B) :
    d.baseResidue (Algebra.intTrace A B x) =
      (d.e : k) * Algebra.trace k l (d.extensionResidue x) := by
  have he : d.e =
      (IsLocalRing.maximalIdeal B).ramificationIdx A := by
    simpa only [LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex]
      using d.e_eq_ramification_index
  have h :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11_finite_dvr_residue_trace_and_norm
      A B k l d.baseResidue d.extensionResidue
      d.baseResidue_is_residue_map d.extensionResidue_is_residue_map
      d.residueCompatibility d.e x 0 he
  exact h.1

/-- Book 2, §15.1: the residue norm shadow, with no separability assumption. -/
theorem residue_norm_shadow_formula
    {A B k l : Type*} [CommRing A] [CommRing B] [Field k] [Field l]
    [Algebra A B] [Algebra k l]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra.IsIntegral A B]
    [Module.Finite A B] [Module.Free A B]
    [Module.Finite k l] [Module.Free k l]
    (d : Chapter15ResidueArithmeticShadow) (u : Bˣ) :
    d.baseResidue (Algebra.intNorm A B (u : B)) =
      (Algebra.norm k ((Units.map d.extensionResidue.toMonoidHom u : lˣ) : l)) ^ d.e := by
  have he : d.e =
      (IsLocalRing.maximalIdeal B).ramificationIdx A := by
    simpa only [LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex]
      using d.e_eq_ramification_index
  have h :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11_finite_dvr_residue_trace_and_norm
      A B k l d.baseResidue d.extensionResidue
      d.baseResidue_is_residue_map d.extensionResidue_is_residue_map
      d.residueCompatibility d.e 0 (u : B) he
  simpa using h.2

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter15
