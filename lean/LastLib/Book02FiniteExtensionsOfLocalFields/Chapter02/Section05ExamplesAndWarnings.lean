import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02.Section04TheFundamentalEquality
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02.Section01WhyTheValuationRingMustBeTheIntegralClosure
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section07UnramifiedAndTotallyRamifiedEndpoints

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

/-- The numerical defect condition for a single chosen valuation branch. -/
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
  have hdegree := fundamental_equality vK vL hcomplete
  rw [he, hf] at hdegree
  simpa using hdegree

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
  have hdegree := fundamental_equality vK vL hcomplete
  rw [he, hf] at hdegree
  simpa using hdegree

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
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring) :
    vL.IsUniformizer piRoot ∧
      chapterRamificationIndex vK.valuationSubring vL.valuationSubring
          (IsLocalRing.maximalIdeal vL.valuationSubring) = n ∧
      chapterResidueDegree vK.valuationSubring vL.valuationSubring
          (IsLocalRing.maximalIdeal vL.valuationSubring) = 1 ∧
      Module.finrank K L = n := by
  have hbaseIntegers : vK.Integers A := by
    refine
      { hom_inj := IsFractionRing.injective A K
        map_le_one := ?_
        exists_of_le_one := ?_ }
    · intro a
      have ha : algebraMap A K a ∈ (vK.valuationSubring : Set K) := by
        rw [hvaluationRing]
        exact ⟨a, rfl⟩
      exact (Valuation.mem_valuationSubring_iff vK (algebraMap A K a)).mp ha
    · intro x hx
      have hx' : x ∈ (vK.valuationSubring : Set K) :=
        (Valuation.mem_valuationSubring_iff vK x).mpr hx
      rw [hvaluationRing] at hx'
      exact hx'
  let f : A →+* vK.valuationSubring :=
    RingHom.codRestrict (algebraMap A K) vK.valuationSubring (by
      intro a
      change algebraMap A K a ∈ (vK.valuationSubring : Set K)
      rw [hvaluationRing]
      exact ⟨a, rfl⟩)
  have hf_inj : Function.Injective f := by
    intro a b hab
    apply IsFractionRing.injective A K
    exact congrArg (fun z : vK.valuationSubring => (z : K)) hab
  have hf_surj : Function.Surjective f := by
    intro a
    have ha : (a : K) ∈ (vK.valuationSubring : Set K) := a.property
    rw [hvaluationRing] at ha
    rcases ha with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    exact Subtype.ext hb
  let eA : A ≃+* vK.valuationSubring :=
    RingEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have heA_coe (a : A) : (eA a : K) = algebraMap A K a := by
    change (f a : K) = algebraMap A K a
    rfl
  have hcomp :
      (algebraMap vK.valuationSubring L).comp eA.toRingHom =
        algebraMap A L := by
    ext a
    change algebraMap vK.valuationSubring L (eA a) = algebraMap A L a
    rw [IsScalarTower.algebraMap_apply vK.valuationSubring K L]
    change algebraMap K L (eA a : K) = algebraMap A L a
    rw [heA_coe]
    exact congrArg (fun g : A →+* L => g a)
      (IsScalarTower.algebraMap_eq A K L).symm
  have hunique :=
    chapter2_complete_base_has_unique_valuation_subring_extension vK vL hcomplete
  have hclosureV :=
    integral_closure_eq_extension_valuation_subring vK vL hunique
  have hupperIntegralClosure :
      (vL.valuationSubring : Set L) = (integralClosure A L : Set L) := by
    ext x
    have hV := Set.ext_iff.mp hclosureV x
    change IsIntegral vK.valuationSubring x ↔ x ∈ vL.valuationSubring at hV
    change x ∈ vL.valuationSubring ↔ IsIntegral A x
    exact hV.symm.trans (RingEquiv.isIntegral_iff eA hcomp x).symm
  have hdegree :
      (chapter2PowerRootPolynomial π n).natDegree = n := by
    by_cases hzero : chapter2PowerRootPolynomial π n = 0
    · exact (hirreducible.ne_zero hzero).elim
    · simp [chapter2PowerRootPolynomial]
  have hendpoint :=
    eisenstein_root_is_uniformizer_and_totally_ramified
      (A := A) (K := K) (L := L) (Γ := ℤᵐ⁰) vK vL π
      (chapter2PowerRootPolynomial π n) piRoot hf hroot hdegree hgenerates
      hbaseIntegers hvaluationRing hupperIntegralClosure
  rcases hendpoint with ⟨huniformizer, hramification, hresidue, _, hfinrank⟩
  exact ⟨huniformizer, hramification, hresidue, hfinrank⟩

/-- The fundamental equality still applies to purely inseparable examples. -/
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
  unfold chapter2HasDefect
  intro hdefect
  exact hdefect (fundamental_equality vK vL hcomplete)

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02
