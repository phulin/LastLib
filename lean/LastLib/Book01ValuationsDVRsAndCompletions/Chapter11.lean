import Mathlib.Algebra.Module.DedekindDomain
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Archimedean
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Unbundled.FiniteExtension
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Data.Real.Embedding
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.FractionalIdeal.Basic
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.HahnSeries.Basic
import Mathlib.RingTheory.HahnSeries.Lex
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.AtPrime.Extension
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.Integers
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.Quotient
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Order
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Algebra.Ring.Compact
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Topology.Algebra.WithZeroTopology
import Mathlib.Topology.MetricSpace.Perfect
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.AbsoluteValue
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.CompareReals
import Mathlib.Topology.UniformSpace.Completion

universe u v

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter11

noncomputable section

open Ideal IsLocalRing
open Polynomial
open scoped BigOperators TensorProduct WithZero Polynomial nonZeroDivisors

/-! # Chapter 11: several places above one place

This file is a statement-only formalization of sections 11.1--11.9 of Book 1.
The declarations are intentionally local to this namespace because the chapters
are generated independently.
-/

/-! ## 11.1. From one local ring to several -/

/-- The integral closure of `A` in an `A`-algebra `L`. -/
def chapter11IntegralClosure (A L : Type*) [CommRing A] [CommRing L] [Algebra A L] :
    Subalgebra A L :=
  integralClosure A L

/-- Finiteness of the normalization, made explicit as a module-finiteness hypothesis. -/
def chapter11NormalizationFinite (A L : Type*) [CommRing A] [CommRing L] [Algebra A L] : Prop :=
  Module.Finite A (chapter11IntegralClosure A L)

/--
The Japanese property used in section 11.2.  It is recorded as the actual
finiteness assertion for the integral closure in every finite extension of
the fraction field; it is not a marker class.
-/
class Chapter11Japanese (R : Type u) [CommRing R] [IsDomain R] : Prop where
  finite_integral_closure :
    ∀ (K L : Type u) [Field K] [Field L] [Algebra R K]
      [IsFractionRing R K] [Algebra K L] [Algebra R L]
      [IsScalarTower R K L] [FiniteDimensional K L],
      Module.Finite R (integralClosure R L)

/-- The informal predicate “`R` is Japanese.” -/
def chapter11IsJapanese (R : Type u) [CommRing R] [IsDomain R] : Prop :=
  Chapter11Japanese R

/-- The completeness assertion for a DVR. -/
class Chapter11CompleteDVR (A : Type u) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] : Prop where
  isAdicComplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A
  normalization_finite :
    ∀ (K L : Type u) [Field K] [Field L] [Algebra A K]
      [IsFractionRing A K] [Algebra K L] [Algebra A L]
      [IsScalarTower A K L] [FiniteDimensional K L],
      Module.Finite A (integralClosure A L)

/-- The interface used for the phrase “complete DVR” in the finiteness discussion. -/
def chapter11IsCompleteDVR (A : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] : Prop :=
  Chapter11CompleteDVR A

/-- A maximal ideal of the normalization lying above the base maximal ideal. -/
def chapter11Branch (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (m : Ideal A) (P : Ideal B) : Prop :=
  P.IsPrime ∧ P.IsMaximal ∧ P.LiesOver m

/-- The set of branches above a chosen base ideal. Finiteness is supplied by
the finite-normalization hypotheses in the later semilocality theorem. -/
def chapter11Branches (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (m : Ideal A) : Set (Ideal B) :=
  {P | chapter11Branch A B m P}

/-- Localization of the normalization at one branch. -/
abbrev chapter11BranchLocalization (B : Type*) [CommRing B] (P : Ideal B) [P.IsPrime] : Type _ :=
  Localization.AtPrime P

/-- The localization `S_{R \ p}` appearing in the Dedekind-domain description. -/
abbrev chapter11AwayLocalization (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] : Type _ :=
  Localization (p.primeCompl.map (algebraMap R S))

/-- The base-change model `S ⊗_R A` for a localized normalization. -/
def chapter11BaseChangeModel (R S A B : Type*) [CommRing R] [CommRing S] [CommRing A]
    [CommRing B] [Algebra R S] [Algebra R A] [Algebra R B] : Prop :=
  Nonempty (B ≃ₐ[R] S ⊗[R] A)

/-- The away-from-`p` model of the same normalization. -/
def chapter11AwayModel (R S A B : Type*) [CommRing R] [CommRing S] [CommRing A]
    [CommRing B] [Algebra R S] [Algebra R A] [Algebra R B] (p : Ideal R) [p.IsPrime] : Prop :=
  Nonempty (B ≃ₐ[R] chapter11AwayLocalization R S p)

/-- A prime of `S` not lying over `p` disappears after localizing away from `p`. -/
def chapter11PrimeDisappearsAwayFrom (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) (Q : Ideal S) : Prop :=
  ¬Q.LiesOver p

/-- A valuation extension is expressed using Mathlib's equivalence relation on valuations. -/
def chapter11ValuationExtensionAt (K L : Type*) [CommRing K] [CommRing L] [Algebra K L]
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰) : Prop :=
  vK.IsEquiv (vL.comap (algebraMap K L))

/-- The center of a valuation on `L` after an explicit embedding of `B` into its valuation ring. -/
def chapter11ValuationCenter (B L : Type*) [CommRing B] [Field L]
    [Algebra B L] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (P : Ideal B) (v : Valuation L Γ₀)
    (ι : B →+* v.valuationSubring) : Prop :=
  P = (maximalIdeal v.valuationSubring).comap ι

/-- Exact correspondence data for one branch and its valuation ring. -/
structure Chapter11ValuationBranchCorrespondence
    (B L : Type*) [CommRing B] [Field L] [Algebra B L]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (P : Ideal B) (v : Valuation L Γ₀) where
  prime : P.IsPrime
  embedding : B →+* v.valuationSubring
  embedding_compatible :
    ∀ x : B, (embedding x : L) = algebraMap B L x
  center : chapter11ValuationCenter B L P v embedding
  localizationEquiv : Localization P.primeCompl ≃+* v.valuationSubring
  localizationEquiv_on_B :
    ∀ x : B,
      localizationEquiv (Localization.mk x ⟨1, P.primeCompl.one_mem⟩) =
        embedding x

/-- A branch supplies a place of `L` extending the original place of `K`.

The finite separable normalization and displayed branch-local DVR are explicit
because they allow the extension to be normalized with value group `ℤ`.
-/
theorem chapter11_branch_labels_valuation_extensions
    (A B K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] [IsFractionRing A K]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsIntegralClosure B A L]
    (hAinj : Function.Injective (algebraMap A K))
    (hKinj : Function.Injective (algebraMap K L))
    (m : Ideal A) (hm : m = IsLocalRing.maximalIdeal A)
    (P : Ideal B) [P.IsPrime] (hP : chapter11Branch A B m P)
    (hfinite : Module.Finite A B)
    (vK : Valuation K ℤᵐ⁰)
    (ιA : A →+* vK.valuationSubring)
    (hιA : ∀ a : A, (ιA a : K) = algebraMap A K a)
    (hcenter : chapter11ValuationCenter A K m vK ιA)
    [IsDiscreteValuationRing (chapter11BranchLocalization B P)] :
    ∃ (vL : Valuation L ℤᵐ⁰) (ι : B →+* vL.valuationSubring),
      chapter11ValuationExtensionAt K L vK vL ∧
        chapter11ValuationCenter B L P vL ι ∧
        ∀ b : B, (ι b : L) = algebraMap B L b := by
  let S := chapter11BranchLocalization B P
  letI : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L
  letI : Module.IsTorsionFree A L :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (by
      intro x y hxy
      apply hAinj
      apply hKinj
      simpa only [IsScalarTower.algebraMap_apply A K L] using hxy)
  letI : Module.IsTorsionFree A B := IsIntegralClosure.isTorsionFree A L
  letI : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  have hPcomp : P.primeCompl ≤ (nonZeroDivisors B).comap (RingHom.id B) := by
    intro x hx
    change x ∈ nonZeroDivisors B
    exact P.primeCompl_le_nonZeroDivisors hx
  let alg : S →+* L :=
    IsLocalization.map L (RingHom.id B) hPcomp
  letI : Algebra S L := alg.toAlgebra
  letI : IsScalarTower B S L := by
    apply IsScalarTower.of_algebraMap_eq'
    change algebraMap B L = alg.comp (algebraMap B S)
    simpa [alg] using
      (IsLocalization.map_comp (M := P.primeCompl) (T := nonZeroDivisors B)
        (Q := L) (g := RingHom.id B) hPcomp).symm
  letI : IsFractionRing S L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl S L
  let vL : Valuation L ℤᵐ⁰ :=
    (IsDiscreteValuationRing.maximalIdeal S).valuation L
  let eS : S ≃+* vL.valuationSubring :=
    IsDiscreteValuationRing.equivValuationSubring (A := S) (K := L)
  let ι : B →+* vL.valuationSubring :=
    eS.toRingHom.comp (algebraMap B S)
  have hι : ∀ b : B, (ι b : L) = algebraMap B L b := by
    intro b
    change algebraMap S L (algebraMap B S b) = algebraMap B L b
    rw [← IsScalarTower.algebraMap_apply B S L]
  have hmaxS :
      (IsLocalRing.maximalIdeal S).map eS.toRingHom =
        IsLocalRing.maximalIdeal vL.valuationSubring := by
    exact IsLocalRing.map_ringEquiv_maximalIdeal eS
  have hcomapS :
      (IsLocalRing.maximalIdeal vL.valuationSubring).comap eS.toRingHom =
        IsLocalRing.maximalIdeal S := by
    rw [← hmaxS]
    exact Ideal.comap_map_of_bijective _ eS.bijective
  have hcenterL : chapter11ValuationCenter B L P vL ι := by
    change P = (IsLocalRing.maximalIdeal vL.valuationSubring).comap ι
    rw [show ι = eS.toRingHom.comp (algebraMap B S) by rfl,
      ← Ideal.comap_comap, hcomapS]
    change P = (IsLocalRing.maximalIdeal S).under B
    exact (Localization.AtPrime.under_maximalIdeal (I := P)).symm
  have hvKring :
      vK.valuationSubring.toSubring =
        Subring.map (algebraMap A K) (⊤ : Subring A) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨a, ha⟩ | ⟨a, ha⟩ := ValuationRing.isInteger_or_isInteger A x
      · rw [Subring.mem_map]
        exact ⟨a, Subring.mem_top _, ha⟩
      · by_cases hx0 : x = 0
        · rw [hx0]
          exact (Subring.zero_mem _)
        by_cases hua : IsUnit a
        · obtain ⟨u, hu⟩ := hua
          rw [Subring.mem_map]
          refine ⟨(↑(u⁻¹) : A), Subring.mem_top _, ?_⟩
          calc
            algebraMap A K (↑(u⁻¹) : A) = (algebraMap A K (↑u : A))⁻¹ := by
              simp
            _ = (algebraMap A K a)⁻¹ := by rw [hu]
            _ = x := by rw [ha]; simp
        · have ham : a ∈ IsLocalRing.maximalIdeal A := by
            rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
            exact hua
          have ham' : a ∈ m := by rw [hm]; exact ham
          have haW : ιA a ∈ IsLocalRing.maximalIdeal vK.valuationSubring := by
            have haW' : a ∈ (IsLocalRing.maximalIdeal vK.valuationSubring).comap ιA := by
              rw [← hcenter]
              exact ham'
            exact haW'
          have hlt : vK (x⁻¹) < 1 := by
            rw [← ha, ← hιA a]
            exact (Valuation.mem_maximalIdeal_iff (K := K) vK).mp haW
          have hxpos : 0 < vK x := (vK.pos_iff).mpr hx0
          have hxgt : 1 < vK x :=
            (inv_lt_one₀ hxpos).mp (by simpa only [map_inv₀] using hlt)
          exact (False.elim ((not_lt_of_ge hx) hxgt))
    · intro x hx
      rw [Subring.mem_map] at hx
      obtain ⟨a, -, ha⟩ := hx
      have haW : (ιA a : K) ∈ vK.valuationSubring := (ιA a).property
      change x ∈ vK.valuationSubring
      rw [← ha, ← hιA a]
      exact haW
  have hvAring :
      ((IsDiscreteValuationRing.maximalIdeal A).valuation K).valuationSubring.toSubring =
        Subring.map (algebraMap A K) (⊤ : Subring A) := by
    exact (IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring
      (A := A) (K := K)).symm
  have hvKeq :
      vK.IsEquiv ((IsDiscreteValuationRing.maximalIdeal A).valuation K) := by
    apply (Valuation.isEquiv_iff_valuationSubring vK _).mpr
    apply ValuationSubring.ext
    intro x
    change x ∈ vK.valuationSubring.toSubring ↔
      x ∈ ((IsDiscreteValuationRing.maximalIdeal A).valuation K).valuationSubring.toSubring
    rw [hvKring, hvAring]
  have hvLring :
      (vL.comap (algebraMap K L)).valuationSubring.toSubring =
        Subring.map (algebraMap A K) (⊤ : Subring A) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨a, ha⟩ | ⟨a, ha⟩ := ValuationRing.isInteger_or_isInteger A x
      · rw [Subring.mem_map]
        exact ⟨a, Subring.mem_top _, ha⟩
      · by_cases hx0 : x = 0
        · rw [hx0]
          exact (Subring.zero_mem _)
        by_cases hua : IsUnit a
        · obtain ⟨u, hu⟩ := hua
          rw [Subring.mem_map]
          refine ⟨(↑(u⁻¹) : A), Subring.mem_top _, ?_⟩
          calc
            algebraMap A K (↑(u⁻¹) : A) = (algebraMap A K (↑u : A))⁻¹ := by
              simp
            _ = (algebraMap A K a)⁻¹ := by rw [hu]
            _ = x := by rw [ha]; simp
        · have ham : a ∈ IsLocalRing.maximalIdeal A := by
            rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
            exact hua
          have ham' : a ∈ m := by rw [hm]; exact ham
          have habP : algebraMap A B a ∈ P := by
            letI : P.LiesOver m := hP.2.2
            exact (Ideal.mem_of_liesOver P m a).mp ham'
          have hamS : algebraMap B S (algebraMap A B a) ∈
              IsLocalRing.maximalIdeal S := by
            rw [← Localization.AtPrime.map_eq_maximalIdeal]
            exact Ideal.mem_map_of_mem _ habP
          have haW : ι (algebraMap A B a) ∈
              IsLocalRing.maximalIdeal vL.valuationSubring := by
            rw [show ι (algebraMap A B a) =
              eS (algebraMap B S (algebraMap A B a)) by rfl]
            rw [← hmaxS]
            exact Ideal.mem_map_of_mem _ hamS
          have hlt : vL ((algebraMap A L) a) < 1 := by
            rw [IsScalarTower.algebraMap_apply A B L a, ← hι]
            exact (Valuation.mem_maximalIdeal_iff (K := L) vL).mp haW
          have hxval : vL (algebraMap K L x) ≤ 1 := hx
          have hxpos : 0 < vL (algebraMap K L x) := by
            apply (vL.pos_iff).mpr
            intro hzero
            apply hx0
            apply hKinj
            simpa using hzero
          have hxinval' : vL ((algebraMap K L x)⁻¹) < 1 := by
            calc
              vL ((algebraMap K L x)⁻¹) = vL (algebraMap A L a) := by
                congr 1
                calc
                  (algebraMap K L x)⁻¹ = algebraMap K L (x⁻¹) := by simp
                  _ = algebraMap K L (algebraMap A K a) := by rw [← ha]
                  _ = algebraMap A L a := by
                    rw [IsScalarTower.algebraMap_apply A K L]
              _ < 1 := hlt
          have hxinval : (vL (algebraMap K L x))⁻¹ < 1 := by
            simpa only [map_inv₀] using hxinval'
          have hxgt : 1 < vL (algebraMap K L x) :=
            (inv_lt_one₀ hxpos).mp hxinval
          exact False.elim ((not_lt_of_ge hxval) hxgt)
    · intro x hx
      rw [Subring.mem_map] at hx
      obtain ⟨a, -, ha⟩ := hx
      have hval : vL (algebraMap A L a) ≤ 1 := by
        rw [IsScalarTower.algebraMap_apply A B L a, ← hι]
        exact (ι (algebraMap A B a)).property
      change vL (algebraMap K L x) ≤ 1
      rw [← ha, ← IsScalarTower.algebraMap_apply A K L]
      exact hval
  have hvLeq :
      vK.IsEquiv (vL.comap (algebraMap K L)) := by
    apply (Valuation.isEquiv_iff_valuationSubring vK _).mpr
    apply ValuationSubring.ext
    intro x
    change x ∈ vK.valuationSubring.toSubring ↔
      x ∈ (vL.comap (algebraMap K L)).valuationSubring.toSubring
    rw [hvKring, hvLring]
  refine ⟨vL, ι, ?_, hcenterL, hι⟩
  exact hvLeq

set_option maxHeartbeats 3000000 in
/-- Conversely, a valuation ring containing the normalization has a center at a branch. -/
theorem chapter11_valuation_ring_converse
    (A B K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] [IsFractionRing A K]
    [FiniteDimensional K L]
    [IsIntegralClosure B A L]
    (hAinj : Function.Injective (algebraMap A K))
    (hKinj : Function.Injective (algebraMap K L))
    (m : Ideal A) (hm : m = IsLocalRing.maximalIdeal A)
    (W : ValuationSubring L) (vK : Valuation K W.ValueGroup)
    (hext : vK.IsEquiv (W.valuation.comap (algebraMap K L)))
    (ι : B →+* W.valuation.valuationSubring)
    (hι : ∀ x : B, (ι x : L) = algebraMap B L x)
    (ιA : A →+* W.valuation.valuationSubring)
    (hιA : ∀ a : A, (ιA a : L) = algebraMap A L a)
    (hcenter : chapter11ValuationCenter A L m W.valuation ιA) :
    ∃ P : Ideal B, chapter11Branch A B m P ∧
      chapter11ValuationCenter B L P W.valuation ι := by
  let P : Ideal B := (IsLocalRing.maximalIdeal W.valuation.valuationSubring).comap ι
  have hcomp : ι.comp (algebraMap A B) = ιA := by
    apply RingHom.ext
    intro a
    apply Subtype.ext
    calc
      ((ι.comp (algebraMap A B)) a : L) = algebraMap B L (algebraMap A B a) :=
        hι (algebraMap A B a)
      _ = algebraMap A L a := by
        rw [IsScalarTower.algebraMap_apply A B L]
      _ = (ιA a : L) := (hιA a).symm
  have hcomap : P.comap (algebraMap A B) = m := by
    change (IsLocalRing.maximalIdeal W.valuation.valuationSubring).comap
        (ι.comp (algebraMap A B)) = m
    rw [hcomp, ← hcenter]
  have hPprime : P.IsPrime := by
    dsimp [P]
    exact Ideal.comap_isPrime _ _
  letI : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L
  letI : P.IsPrime := hPprime
  have hPmax : P.IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := A) (S := B) P
    rw [hcomap]
    rw [hm]
    exact IsLocalRing.maximalIdeal.isMaximal A
  have hPlies : P.LiesOver m := ⟨hcomap.symm⟩
  refine ⟨P, ⟨hPprime, hPmax, hPlies⟩, ?_⟩
  rfl

/-- A branch localization is a local ring, and in the Dedekind situation it is a DVR. -/
theorem chapter11_branch_localization_is_dvr
    (B : Type*) [CommRing B] [IsDomain B] [IsDedekindDomain B]
    (P : Ideal B) [P.IsPrime] [P.IsMaximal] (hP0 : P ≠ ⊥) :
    IsDiscreteValuationRing (chapter11BranchLocalization B P) := by
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hP0 (Localization.AtPrime P)

/-- The normalization is semilocal once its maximal ideals above `m` are finite. -/
def chapter11IsSemilocal (B : Type*) [CommRing B] : Prop :=
  ∃ s : Finset (Ideal B), ∀ P : Ideal B, P.IsMaximal ↔ P ∈ (s : Set (Ideal B))

set_option maxHeartbeats 10000000 in
/-- Finite normalization of a DVR is a semilocal Dedekind domain. -/
theorem chapter11_finite_normalization_is_semilocal_dedekind
    {ΓK : Type*} (A K L B : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Field L] [CommRing B]
    [IsDomain B] [LinearOrderedCommGroupWithZero ΓK]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    (hAinj : Function.Injective (algebraMap A K))
    (hKinj : Function.Injective (algebraMap K L))
    [Algebra.IsIntegral A B] [Module.IsTorsionFree A B] [FaithfulSMul A B]
    (hfinite : Module.Finite A B) (vK : Valuation K ΓK)
    (ιA : A →+* vK.valuationSubring)
    (hιA : ∀ a : A, (ιA a : K) = algebraMap A K a)
    (hcenter : chapter11ValuationCenter A K (IsLocalRing.maximalIdeal A) vK ιA) :
    IsDedekindDomain B ∧
    chapter11IsSemilocal B ∧
      (∀ P : Ideal B,
        P.IsMaximal ↔ P.IsPrime ∧ P.LiesOver (IsLocalRing.maximalIdeal A)) ∧
      (∀ (P : Ideal B) [P.IsPrime],
        P.IsMaximal → IsDiscreteValuationRing (chapter11BranchLocalization B P)) ∧
      (∀ (ΓL : Type v) [LinearOrderedCommGroupWithZero ΓL]
          (vL : Valuation L ΓL),
        vK.IsEquiv (vL.comap (algebraMap K L)) ↔
          ∃! P : Ideal B,
            P.IsMaximal ∧ P.LiesOver (IsLocalRing.maximalIdeal A) ∧
              Nonempty (Chapter11ValuationBranchCorrespondence B L P vL)) := by
  classical
  letI : IsDedekindDomain A :=
    ((IsDiscreteValuationRing.TFAE A (IsDiscreteValuationRing.not_isField A)).out 0 2).mp
      (inferInstance : IsDiscreteValuationRing A)
  letI : IsDedekindDomain B :=
    IsIntegralClosure.isDedekindDomain A K L B
  letI : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  have hmax0 : IsLocalRing.maximalIdeal A ≠ (⊥ : Ideal A) :=
    IsDiscreteValuationRing.not_a_field A
  have hmax_over : ∀ P : Ideal B, P.IsMaximal →
      P.LiesOver (IsLocalRing.maximalIdeal A) := by
    intro P hP
    letI : P.IsMaximal := hP
    have hunder : (P.under A).IsMaximal := Ideal.IsMaximal.under A P
    exact ⟨(IsLocalRing.eq_maximalIdeal hunder).symm⟩
  have hbranch_max : ∀ P : Ideal B,
      P.IsPrime ∧ P.LiesOver (IsLocalRing.maximalIdeal A) → P.IsMaximal := by
    intro P hP
    letI : P.IsPrime := hP.1
    letI : P.LiesOver (IsLocalRing.maximalIdeal A) := hP.2
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := A) (S := B) P
    change (P.under A).IsMaximal
    rw [← P.over_def (IsLocalRing.maximalIdeal A)]
    exact IsLocalRing.maximalIdeal.isMaximal A
  have hmax_finite : {P : Ideal B | P.IsMaximal}.Finite := by
    have hfinite_primes : (IsLocalRing.maximalIdeal A).primesOver B |>.Finite :=
      Algebra.QuasiFinite.finite_primesOver (IsLocalRing.maximalIdeal A)
    exact hfinite_primes.subset (by
      intro (P : Ideal B) hP
      exact ⟨hP.isPrime, hmax_over P hP⟩)
  have hsemi : chapter11IsSemilocal B := by
    refine ⟨hmax_finite.toFinset, ?_⟩
    intro P
    constructor
    · intro hP
      exact hmax_finite.mem_toFinset.mpr hP
    · intro hP
      exact hmax_finite.mem_toFinset.mp hP
  have hmax_iff : ∀ P : Ideal B,
      P.IsMaximal ↔ P.IsPrime ∧ P.LiesOver (IsLocalRing.maximalIdeal A) := by
    intro P
    constructor
    · intro hP
      exact ⟨hP.isPrime, hmax_over P hP⟩
    · exact hbranch_max P
  have hloc : ∀ (P : Ideal B) [P.IsPrime],
      P.IsMaximal → IsDiscreteValuationRing (chapter11BranchLocalization B P) := by
    intro P _ hP
    have hP0 : P ≠ (⊥ : Ideal B) := by
      intro hPbot
      subst P
      have hL := hmax_over (⊥ : Ideal B) hP
      have hcomp : (⊥ : Ideal B).comap (algebraMap A B) =
          IsLocalRing.maximalIdeal A := hL.over.symm
      rw [Ideal.comap_bot_of_injective (algebraMap A B)
        (FaithfulSMul.algebraMap_injective A B)] at hcomp
      exact hmax0 hcomp.symm
    exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hP0
      (Localization.AtPrime P)
  have hcorr_of_center (P : Ideal B) (hPprime : P.IsPrime)
      (hP0 : P ≠ (⊥ : Ideal B))
      {ΓL : Type v} [LinearOrderedCommGroupWithZero ΓL]
      (vL : Valuation L ΓL) (ι : B →+* vL.valuationSubring)
      (hι : ∀ x : B, (ι x : L) = algebraMap B L x)
      (hcenter : chapter11ValuationCenter B L P vL ι) :
      Nonempty (Chapter11ValuationBranchCorrespondence B L P vL) := by
    let p₁ : IsDedekindDomain.HeightOneSpectrum B :=
      IsDedekindDomain.HeightOneSpectrum.mk P hPprime hP0
    let S : ValuationSubring L :=
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L p₁
    have hSle : S ≤ vL.valuationSubring := by
      intro z hz
      change z ∈ S.toSubring at hz
      rw [show S.toSubring =
        (Localization.subalgebra.ofField L P.primeCompl P.primeCompl_le_nonZeroDivisors).toSubring by
          rfl] at hz
      obtain ⟨b, s, hs, hzs⟩ := hz
      have hιs : ι s ∉ IsLocalRing.maximalIdeal vL.valuationSubring := by
        intro hmem
        apply hs
        have hsP : s ∈ P := by
          rw [hcenter]
          exact hmem
        exact hsP
      have hιsunit : IsUnit (ι s) := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hιs
        exact Classical.not_not.mp hιs
      obtain ⟨y, hy⟩ := (isUnit_iff_exists_inv.mp hιsunit)
      have hinv : (algebraMap B L s)⁻¹ ∈ vL.valuationSubring := by
        have hyL : algebraMap B L s * (y : L) = 1 := by
          simpa [hι s] using congrArg (fun z : vL.valuationSubring => (z : L)) hy
        have hs0 : algebraMap B L s ≠ 0 := by
          intro hs0
          apply hιsunit.ne_zero
          apply Subtype.ext
          simpa [hι s] using hs0
        have hyval : (y : L) = (algebraMap B L s)⁻¹ := by
          rw [← one_div]
          exact (eq_div_iff hs0).2 (by simpa [mul_comm] using hyL)
        rw [← hyval]
        exact SetLike.coe_mem _
      have hb : algebraMap B L b ∈ vL.valuationSubring := by
        simpa [← hι b] using (ι b).property
      rw [hzs]
      exact vL.valuationSubring.toSubring.mul_mem hb hinv
    have htop : vL.valuationSubring ≠ ⊤ := by
      intro htop
      apply hP0
      have hmax_top : IsLocalRing.maximalIdeal vL.valuationSubring = ⊥ := by
        rw [htop]
        exact IsLocalRing.maximalIdeal_eq_bot
      rw [hcenter, hmax_top]
      exact Ideal.comap_bot_of_injective ι (by
        intro x y hxy
        apply IsFractionRing.injective B L
        simpa [hι x, hι y] using congrArg Subtype.val hxy)
    have hEq : S = vL.valuationSubring :=
      ValuationSubring.eq_of_le_of_ne_top S hSle htop
    let W₀ : Subalgebra B L :=
      Localization.subalgebra.ofField L P.primeCompl P.primeCompl_le_nonZeroDivisors
    have hS₀ : S.toSubring = W₀.toSubring := by
      dsimp [W₀]
      simpa [S, p₁] using
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_toSubring p₁ (K := L))
    have hmemS₀ (x : W₀) : (x : L) ∈ S := by
      change (x : L) ∈ S.toSubring
      rw [hS₀]
      exact x.property
    let g : W₀ →ₐ[B] S :=
      { toFun := fun x => ⟨x, hmemS₀ x⟩
        map_zero' := by ext; rfl
        map_one' := by ext; rfl
        map_add' := by intro x y; ext; rfl
        map_mul' := by intro x y; ext; rfl
        commutes' := by intro b; ext; rfl }
    have hg : Function.Bijective g := by
      constructor
      · intro x y hxy
        apply Subtype.ext
        exact congrArg (fun z : S => (z : L)) hxy
      · intro y
        refine ⟨⟨y, ?_⟩, ?_⟩
        · change (y : L) ∈ W₀.toSubring
          rw [← hS₀]
          exact y.property
        · rfl
    let eSub : W₀ ≃ₐ[B] S := AlgEquiv.ofBijective g hg
    letI : Algebra B S := inferInstance
    letI : IsLocalization P.primeCompl W₀ :=
      Localization.subalgebra.isLocalization_ofField L P.primeCompl
        P.primeCompl_le_nonZeroDivisors
    letI : IsLocalization P.primeCompl S :=
      IsLocalization.isLocalization_of_algEquiv P.primeCompl eSub
    let f : S →+* vL.valuationSubring :=
      ValuationSubring.inclusion S vL.valuationSubring hSle
    have hf : Function.Bijective f := by
      constructor
      · intro x y hxy
        apply Subtype.ext
        exact congrArg (fun z : vL.valuationSubring => (z : L)) hxy
      · intro y
        refine ⟨⟨y, ?_⟩, ?_⟩
        · rw [hEq]
          exact y.property
        · rfl
    let eEq : S ≃+* vL.valuationSubring := RingEquiv.ofBijective f hf
    let e₀ : Localization.AtPrime P ≃ₐ[B] S :=
      IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P) S
    let e : Localization.AtPrime P ≃+* vL.valuationSubring :=
      e₀.toRingEquiv.trans eEq
    refine ⟨{
      prime := hPprime
      embedding := ι
      embedding_compatible := hι
      center := hcenter
      localizationEquiv := e
      localizationEquiv_on_B := ?_ }⟩
    intro x
    change e (Localization.mk x ⟨1, P.primeCompl.one_mem⟩) = ι x
    apply Subtype.ext
    change ((e₀.toRingEquiv.trans eEq)
        (Localization.mk x ⟨1, P.primeCompl.one_mem⟩) : L) = (ι x : L)
    change (eEq (e₀ (Localization.mk x ⟨1, P.primeCompl.one_mem⟩)) : L) = (ι x : L)
    have he₀x : e₀ (Localization.mk x ⟨1, P.primeCompl.one_mem⟩) = algebraMap B S x := by
      rw [← e₀.commutes]
      rfl
    rw [he₀x]
    dsimp [eEq, f, ValuationSubring.inclusion]
    have hf' : Function.Bijective (Subring.inclusion hSle) := by
      constructor
      · exact Subring.inclusion_injective hSle
      · intro y
        refine ⟨⟨y, ?_⟩, ?_⟩
        · rw [hEq]
          exact y.property
        · rfl
    rw [RingEquiv.ofBijective_apply (Subring.inclusion hSle) hf']
    rw [Subring.coe_inclusion]
    rw [hι x]
    change ((algebraMap B S x : S) : L) = algebraMap B L x
    rw [← ValuationSubring.algebraMap_apply S]
    rw [← IsScalarTower.algebraMap_apply B S L]
  refine ⟨inferInstance, hsemi, hmax_iff, hloc, ?_⟩
  intro ΓL _ vL
  constructor
  · intro hext
    have hring : vK.valuationSubring =
        (vL.comap (algebraMap K L)).valuationSubring :=
      (Valuation.isEquiv_iff_valuationSubring vK _).mp hext
    have hA_mem : ∀ a : A, algebraMap A L a ∈ vL.valuationSubring := by
      intro a
      have ha : algebraMap A K a ∈ vK.valuationSubring := by
        rw [← hιA a]
        exact (ιA a).property
      have ha' : algebraMap A K a ∈
          (vL.comap (algebraMap K L)).valuationSubring := by
        rw [← hring]
        exact ha
      change vL (algebraMap A L a) ≤ 1
      rw [IsScalarTower.algebraMap_apply A K L]
      exact ha'
    let hA : A →+* vL.valuationSubring :=
      (algebraMap A L).codRestrict vL.valuationSubring hA_mem
    have hAcompat : ∀ a : A, (hA a : L) = algebraMap A L a := by
      intro a
      rfl
    letI : Algebra A vL.valuationSubring := hA.toAlgebra
    letI : IsScalarTower A vL.valuationSubring L := by
      apply IsScalarTower.of_algebraMap_eq'
      apply RingHom.ext
      intro a
      change algebraMap A L a = (algebraMap vL.valuationSubring L) (hA a)
      exact (hAcompat a).symm
    have hB_mem : ∀ b : B, algebraMap B L b ∈ vL.valuationSubring := by
      intro b
      have hbA : IsIntegral A (algebraMap B L b) := by
        exact IsIntegral.map (IsScalarTower.toAlgHom A B L)
          (Algebra.IsIntegral.isIntegral (R := A) b)
      have hbW : IsIntegral vL.valuationSubring (algebraMap B L b) := by
        apply IsIntegral.map_of_comp_eq hA (RingHom.id L)
        apply RingHom.ext
        intro a
        change (algebraMap vL.valuationSubring L) (hA a) = algebraMap A L a
        exact hAcompat a
        exact hbA
      exact (Valuation.Integers.isIntegral_iff_v_le_one
        (Valuation.valuationSubring.integers vL)).mp hbW
    let ι : B →+* vL.valuationSubring :=
      (algebraMap B L).codRestrict vL.valuationSubring hB_mem
    have hι : ∀ b : B, (ι b : L) = algebraMap B L b := by
      intro b
      rfl
    let P : Ideal B :=
      (IsLocalRing.maximalIdeal vL.valuationSubring).comap ι
    have hPprime : P.IsPrime := by
      dsimp [P]
      exact Ideal.comap_isPrime _ _
    have hPover : P.LiesOver (IsLocalRing.maximalIdeal A) := by
      have hcomp : ι.comp (algebraMap A B) = hA := by
        apply RingHom.ext
        intro a
        apply Subtype.ext
        change algebraMap B L (algebraMap A B a) = algebraMap A L a
        rw [IsScalarTower.algebraMap_apply A B L]
      have hlt_equiv : ∀ a : A,
          vK (algebraMap A K a) < 1 ↔ vL (algebraMap A L a) < 1 := by
        intro a
        simpa only [Valuation.comap_apply, IsScalarTower.algebraMap_apply A K L] using
          (hext.lt_one_iff_lt_one (x := algebraMap A K a))
      have hcomap : P.comap (algebraMap A B) =
          IsLocalRing.maximalIdeal A := by
        apply Ideal.ext
        intro a
        constructor
        · intro ha
          change ι (algebraMap A B a) ∈
            IsLocalRing.maximalIdeal vL.valuationSubring at ha
          have hltL : vL (algebraMap A L a) < 1 := by
            rw [IsScalarTower.algebraMap_apply A B L, ← hι]
            exact (Valuation.mem_maximalIdeal_iff (K := L) vL).mp ha
          have hltK : vK (algebraMap A K a) < 1 := (hlt_equiv a).mpr hltL
          have haV : ιA a ∈ IsLocalRing.maximalIdeal vK.valuationSubring := by
            apply (Valuation.mem_maximalIdeal_iff (K := K) vK).mpr
            rw [hιA a]
            exact hltK
          rw [hcenter]
          exact haV
        · intro ha
          have haV : ιA a ∈ IsLocalRing.maximalIdeal vK.valuationSubring := by
            have haV' : a ∈
                (IsLocalRing.maximalIdeal vK.valuationSubring).comap ιA := by
              rw [← hcenter]
              exact ha
            exact haV'
          have hltK : vK (algebraMap A K a) < 1 := by
            apply (Valuation.mem_maximalIdeal_iff (K := K) vK).mp at haV
            rw [hιA a] at haV
            exact haV
          have hltL : vL (algebraMap A L a) < 1 := (hlt_equiv a).mp hltK
          have haW : hA a ∈ IsLocalRing.maximalIdeal vL.valuationSubring := by
            apply (Valuation.mem_maximalIdeal_iff (K := L) vL).mpr
            rw [hAcompat a]
            exact hltL
          change (ι.comp (algebraMap A B)) a ∈
            IsLocalRing.maximalIdeal vL.valuationSubring
          rw [hcomp]
          exact haW
      exact ⟨hcomap.symm⟩
    have hPmax : P.IsMaximal := hbranch_max P ⟨hPprime, hPover⟩
    have hP0 : P ≠ (⊥ : Ideal B) := by
      intro hPbot
      apply hmax0
      have hcomp : (⊥ : Ideal B).comap (algebraMap A B) =
          IsLocalRing.maximalIdeal A := by
        simpa only [hPbot, Ideal.under_def] using hPover.over.symm
      rw [Ideal.comap_bot_of_injective (algebraMap A B)
        (FaithfulSMul.algebraMap_injective A B)] at hcomp
      exact hcomp.symm
    have hcenterP : chapter11ValuationCenter B L P vL ι := by
      exact rfl
    have hcorr : Nonempty (Chapter11ValuationBranchCorrespondence B L P vL) := by
      exact hcorr_of_center P hPprime hP0 (ΓL := ΓL) vL ι hι hcenterP
    refine ⟨P, ⟨hPmax, hPover, hcorr⟩, ?_⟩
    intro Q hQ
    rcases hQ.2.2 with ⟨cQ⟩
    have hemb : cQ.embedding = ι := by
      apply RingHom.ext
      intro b
      apply Subtype.ext
      calc
        (cQ.embedding b : L) = algebraMap B L b := cQ.embedding_compatible b
        _ = (ι b : L) := (hι b).symm
    calc
      Q = (IsLocalRing.maximalIdeal vL.valuationSubring).comap cQ.embedding := cQ.center
      _ = (IsLocalRing.maximalIdeal vL.valuationSubring).comap ι := by rw [hemb]
      _ = P := hcenterP.symm
  · intro h
    rcases h with ⟨P, hPdata, hPuniq⟩
    rcases hPdata with ⟨hPmax, hPover, ⟨cP⟩⟩
    letI : P.IsPrime := cP.prime
    letI : P.IsMaximal := hPmax
    letI : P.LiesOver (IsLocalRing.maximalIdeal A) := hPover
    have hvKring :
        vK.valuationSubring.toSubring =
          Subring.map (algebraMap A K) (⊤ : Subring A) := by
      apply le_antisymm
      · intro x hx
        obtain ⟨a, ha⟩ | ⟨a, ha⟩ := ValuationRing.isInteger_or_isInteger A x
        · rw [Subring.mem_map]
          exact ⟨a, Subring.mem_top _, ha⟩
        · by_cases hx0 : x = 0
          · rw [hx0]
            exact Subring.zero_mem _
          by_cases hua : IsUnit a
          · obtain ⟨u, hu⟩ := hua
            rw [Subring.mem_map]
            refine ⟨(↑(u⁻¹) : A), Subring.mem_top _, ?_⟩
            calc
              algebraMap A K (↑(u⁻¹) : A) = (algebraMap A K (↑u : A))⁻¹ := by simp
              _ = (algebraMap A K a)⁻¹ := by rw [hu]
              _ = x := by rw [ha]; simp
          · have ham : a ∈ IsLocalRing.maximalIdeal A := by
              rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
              exact hua
            have haW : ιA a ∈ IsLocalRing.maximalIdeal vK.valuationSubring := by
              have haW' : a ∈
                  (IsLocalRing.maximalIdeal vK.valuationSubring).comap ιA := by
                rw [← hcenter]
                exact ham
              exact haW'
            have hlt : vK (x⁻¹) < 1 := by
              rw [← ha, ← hιA a]
              exact (Valuation.mem_maximalIdeal_iff (K := K) vK).mp haW
            have hxpos : 0 < vK x := (vK.pos_iff).mpr hx0
            have hxgt : 1 < vK x :=
              (inv_lt_one₀ hxpos).mp (by simpa only [map_inv₀] using hlt)
            exact False.elim ((not_lt_of_ge hx) hxgt)
      · intro x hx
        rw [Subring.mem_map] at hx
        obtain ⟨a, -, ha⟩ := hx
        have haW : (ιA a : K) ∈ vK.valuationSubring := (ιA a).property
        change x ∈ vK.valuationSubring
        rw [← ha, ← hιA a]
        exact haW
    have hvLring :
        (vL.comap (algebraMap K L)).valuationSubring.toSubring =
          Subring.map (algebraMap A K) (⊤ : Subring A) := by
      apply le_antisymm
      · intro x hx
        obtain ⟨a, ha⟩ | ⟨a, ha⟩ := ValuationRing.isInteger_or_isInteger A x
        · rw [Subring.mem_map]
          exact ⟨a, Subring.mem_top _, ha⟩
        · by_cases hx0 : x = 0
          · rw [hx0]
            exact Subring.zero_mem _
          by_cases hua : IsUnit a
          · obtain ⟨u, hu⟩ := hua
            rw [Subring.mem_map]
            refine ⟨(↑(u⁻¹) : A), Subring.mem_top _, ?_⟩
            calc
              algebraMap A K (↑(u⁻¹) : A) = (algebraMap A K (↑u : A))⁻¹ := by simp
              _ = (algebraMap A K a)⁻¹ := by rw [hu]
              _ = x := by rw [ha]; simp
          · have ham : a ∈ IsLocalRing.maximalIdeal A := by
              rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
              exact hua
            have habP : algebraMap A B a ∈ P :=
              (Ideal.mem_of_liesOver P (IsLocalRing.maximalIdeal A) a).mp ham
            have haW : cP.embedding (algebraMap A B a) ∈
                IsLocalRing.maximalIdeal vL.valuationSubring := by
              have : algebraMap A B a ∈
                  (IsLocalRing.maximalIdeal vL.valuationSubring).comap cP.embedding := by
                rw [← cP.center]
                exact habP
              exact this
            have hlt : vL (algebraMap A L a) < 1 := by
              rw [IsScalarTower.algebraMap_apply A B L,
                ← cP.embedding_compatible (algebraMap A B a)]
              exact (Valuation.mem_maximalIdeal_iff (K := L) vL).mp haW
            have hxval : vL (algebraMap K L x) ≤ 1 := hx
            have hxpos : 0 < vL (algebraMap K L x) := by
              apply (vL.pos_iff).mpr
              intro hzero
              apply hx0
              apply hKinj
              simpa using hzero
            have hxinval' : vL ((algebraMap K L x)⁻¹) < 1 := by
              calc
                vL ((algebraMap K L x)⁻¹) = vL (algebraMap A L a) := by
                  congr 1
                  calc
                    (algebraMap K L x)⁻¹ = algebraMap K L (x⁻¹) := by simp
                    _ = algebraMap K L (algebraMap A K a) := by rw [← ha]
                    _ = algebraMap A L a := by
                      rw [IsScalarTower.algebraMap_apply A K L]
                _ < 1 := hlt
            have hxinval : (vL (algebraMap K L x))⁻¹ < 1 := by
              simpa only [map_inv₀] using hxinval'
            have hxgt : 1 < vL (algebraMap K L x) :=
              (inv_lt_one₀ hxpos).mp hxinval
            exact False.elim ((not_lt_of_ge hxval) hxgt)
      · intro x hx
        rw [Subring.mem_map] at hx
        obtain ⟨a, -, ha⟩ := hx
        have hval : vL (algebraMap A L a) ≤ 1 := by
          rw [IsScalarTower.algebraMap_apply A B L,
            ← cP.embedding_compatible (algebraMap A B a)]
          exact (cP.embedding (algebraMap A B a)).property
        change vL (algebraMap K L x) ≤ 1
        rw [← ha, ← IsScalarTower.algebraMap_apply A K L]
        exact hval
    apply (Valuation.isEquiv_iff_valuationSubring vK _).mpr
    apply ValuationSubring.ext
    intro z
    change z ∈ vK.valuationSubring.toSubring ↔
      z ∈ (vL.comap (algebraMap K L)).valuationSubring.toSubring
    rw [hvKring, hvLring]
 

/-- In the finite normalization, maximal ideals are exactly the primes above the base maximal ideal. -/
theorem chapter11_maximal_ideals_are_precisely_branches
    (A K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hAinj : Function.Injective (algebraMap A K))
    (hKinj : Function.Injective (algebraMap K L))
    (hfinite : Module.Finite A (chapter11IntegralClosure A L)) :
    ∀ P : Ideal (chapter11IntegralClosure A L),
      P.IsMaximal ↔ P.IsPrime ∧ P.LiesOver (IsLocalRing.maximalIdeal A) := by
  letI : IsDedekindDomain A :=
    ((IsDiscreteValuationRing.TFAE A (IsDiscreteValuationRing.not_isField A)).out 0 2).mp
      (inferInstance : IsDiscreteValuationRing A)
  letI : IsIntegralClosure (chapter11IntegralClosure A L) A L := by
    change IsIntegralClosure (integralClosure A L) A L
    infer_instance
  letI : IsDedekindDomain (chapter11IntegralClosure A L) :=
    integralClosure.isDedekindDomain A K L
  letI : FaithfulSMul A (chapter11IntegralClosure A L) :=
    (faithfulSMul_iff_algebraMap_injective A (chapter11IntegralClosure A L)).mpr
      (by
        intro x y hxy
        apply hAinj
        apply hKinj
        simpa only [← IsScalarTower.algebraMap_apply A K L,
          IsScalarTower.algebraMap_apply A (chapter11IntegralClosure A L) L] using
          congrArg (algebraMap (chapter11IntegralClosure A L) L) hxy)
  have hm0 : IsLocalRing.maximalIdeal A ≠ (⊥ : Ideal A) :=
    IsDiscreteValuationRing.not_a_field A
  intro P
  constructor
  · intro hP
    letI : P.IsMaximal := hP
    have hcomp : P.comap (algebraMap A (chapter11IntegralClosure A L)) =
        IsLocalRing.maximalIdeal A :=
      IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P)
    exact ⟨hP.isPrime, ⟨hcomp.symm⟩⟩
  · rintro ⟨hPprime, hPover⟩
    letI : P.IsPrime := hPprime
    letI : P.LiesOver (IsLocalRing.maximalIdeal A) := hPover
    exact hPprime.isMaximal
      (Ideal.ne_bot_of_liesOver_of_ne_bot hm0 P)

/-- A semilocal ring can contain elements whose signs at two branches disagree. -/
def chapter11OppositeBranchValues (L : Type*) [Field L]
    (v₁ v₂ : AddValuation L (WithTop ℤ)) : Prop :=
  ∃ x : L, v₁ x < 0 ∧ 0 < v₂ x

/-- This is the obstruction to treating a genuinely semilocal normalization as one valuation ring. -/
theorem chapter11_semilocality_is_essential
    (L : Type*) [Field L] (v₁ v₂ : AddValuation L (WithTop ℤ))
    (h : chapter11OppositeBranchValues L v₁ v₂) :
    ¬ ∀ x : L,
      (0 ≤ v₁ x ∧ 0 ≤ v₂ x) ∨
        (0 ≤ v₁ x⁻¹ ∧ 0 ≤ v₂ x⁻¹) := by
  intro hval
  rcases h with ⟨x, hx₁, hx₂⟩
  rcases hval x with hgood | hgood
  · exact (not_lt_of_ge hgood.1) hx₁
  · have hx0 : x ≠ 0 := by
      intro hx0
      simp [hx0] at hx₁
    have hinv : v₂ x⁻¹ < 0 := by
      rw [AddValuation.map_inv]
      have hvtop : v₂ x ≠ (⊤ : WithTop ℤ) :=
        (AddValuation.ne_top_iff v₂).mpr hx0
      obtain ⟨z, hz⟩ := (WithTop.ne_top_iff_exists).mp hvtop
      rw [← hz] at hx₂ ⊢
      have hzpos : (0 : ℤ) < z :=
        WithTop.coe_lt_coe.mp (by simpa using hx₂)
      change ((-z : ℤ) : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ)
      exact WithTop.coe_lt_coe.mpr (neg_lt_zero.mpr hzpos)
    exact (not_lt_of_ge hgood.2) hinv

/-! ## 11.2. Finiteness and the generic fiber -/

/-- A uniformizer for a local ideal. -/
def chapter11IsUniformizer (A : Type*) [CommRing A] (m : Ideal A) (π : A) : Prop :=
  m = Ideal.span {π}

/-- The generic fiber of a finite `A`-algebra. -/
abbrev chapter11GenericFiber (A B K : Type*) [CommRing A] [CommRing B] [Field K]
    [Algebra A B] [Algebra A K] : Type _ :=
  B ⊗[A] K

/-- The expected identification of the generic fiber with the given field extension. -/
def chapter11GenericFiberIdentification
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] : Prop :=
  Nonempty (chapter11GenericFiber A B K ≃+* L)

/-- Finite torsion-free modules over a PID are free. -/
theorem chapter11_finite_torsion_free_over_pid_is_free
    (A M : Type*) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.IsTorsionFree A M] :
    Module.Free A M := by
  exact Module.free_of_finite_type_torsion_free'

/-- The rank of the normalization agrees with the degree of the generic field extension. -/
theorem chapter11_normalization_rank_eq_field_degree
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra B L] [Algebra A L]
    [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing A K]
    [IsFractionRing B L] [Module.Free A B] [Module.Finite A B] :
    Cardinal.toNat (Module.rank A B) = Module.finrank K L := by
  have hr := congrArg Cardinal.toNat
    (Module.finrank_eq_rank (R := A) (M := B))
  calc
    Cardinal.toNat (Module.rank A B) = Module.finrank A B := by
      simpa only [Cardinal.toNat_natCast] using hr.symm
    _ = Module.finrank K L := (IsFractionRing.finrank_eq A K B L).symm

/-- The generic fiber is the field `L` after inverting the nonzero elements of `A`. -/
theorem chapter11_generic_fiber_is_the_field_extension
    (A B K L : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra B L] [Algebra A L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing A K]
    [IsIntegralClosure B A L] [FiniteDimensional K L]
    (hfinite : Module.Finite A B) :
    chapter11GenericFiberIdentification A B K L := by
  letI : IsLocalization (Algebra.algebraMapSubmonoid B A⁰)
      (B ⊗[A] K) := IsLocalization.tensor K A⁰
  letI : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization A K L B
  exact ⟨(IsLocalization.algEquiv (Algebra.algebraMapSubmonoid B A⁰)
    (B ⊗[A] K) L).toRingEquiv⟩

/-- The generic-fiber identification can be kept as a scalar-compatible ring
equivalence over `K`, recording the canonical compatibility omitted by the
weaker ring-equivalence wrapper above. -/
def chapter11GenericFiberKIdentification
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L] : Prop :=
  ∃ e : chapter11GenericFiber A B K ≃+* L,
    ∀ k : K, e (Algebra.TensorProduct.includeRight k) = algebraMap K L k

theorem chapter11_generic_fiber_is_the_field_extension_as_K_algebra
    (A B K L : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra B L]
    [Algebra A L] [Algebra K L] [IsScalarTower A B L]
    [IsScalarTower A K L] [IsFractionRing A K]
    [IsIntegralClosure B A L] [FiniteDimensional K L]
    (hfinite : Module.Finite A B) :
    chapter11GenericFiberKIdentification A B K L := by
  letI : IsLocalization (Algebra.algebraMapSubmonoid B A⁰)
      (B ⊗[A] K) := IsLocalization.tensor K A⁰
  letI : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization A K L B
  let eAlg : (B ⊗[A] K) ≃ₐ[B] L :=
    IsLocalization.algEquiv (Algebra.algebraMapSubmonoid B A⁰) (B ⊗[A] K) L
  let e : (B ⊗[A] K) ≃+* L := eAlg.toRingEquiv
  refine ⟨e, ?_⟩
  have heq :
      e.toRingHom.comp (Algebra.TensorProduct.includeRight.toRingHom :
        K →+* (B ⊗[A] K)) = algebraMap K L := by
    apply IsLocalization.ringHom_ext A⁰
    apply RingHom.ext
    intro a
    change eAlg ((Algebra.TensorProduct.includeRight.toRingHom.comp
      (algebraMap A K)) a) =
      algebraMap K L (algebraMap A K a)
    rw [← Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap]
    change eAlg (algebraMap A (B ⊗[A] K) a) =
      algebraMap K L (algebraMap A K a)
    rw [IsScalarTower.algebraMap_apply A B (B ⊗[A] K) a]
    rw [eAlg.commutes]
    rw [← IsScalarTower.algebraMap_apply A B L,
      ← IsScalarTower.algebraMap_apply A K L]
  intro k
  exact RingHom.congr_fun heq k

/-- A DVR clears denominators by a power of a uniformizer. -/
def chapter11DenominatorCleared (A B L : Type*) [CommRing A] [CommRing B] [CommRing L]
    [Algebra A L] [Algebra B L] (π : A) (x : L) : Prop :=
  ∃ n : ℕ, ∃ b : B, (algebraMap A L π) ^ n * x = algebraMap B L b

/-- Every element of the fraction field of the normalization is denominator-cleared. -/
theorem chapter11_denominators_are_powers_of_a_uniformizer
    (A B K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [Field K] [Field L] [Algebra A B] [Algebra A K]
    [Algebra K L] [Algebra B L] [Algebra A L] [IsScalarTower A K L]
    [IsScalarTower A B L] [IsFractionRing B L] [IsIntegralClosure B A L]
    [FiniteDimensional K L] (m : Ideal A) (π : A)
    (hm : m = IsLocalRing.maximalIdeal A) (hm0 : m ≠ ⊥)
    (hπ : chapter11IsUniformizer A m π) (hfinite : Module.Finite A B) (x : L) :
    chapter11DenominatorCleared A B L π x := by
  have hπ0 : π ≠ 0 := by
    intro hzero
    apply hm0
    rw [hπ, hzero, Ideal.span_singleton_zero]
  have hmax : IsLocalRing.maximalIdeal A = Ideal.span ({π} : Set A) := by
    rw [← hπ, hm]
  have hπirr : Irreducible π := by
    exact IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal π hπ0 hmax
  letI : IsDomain B := (IsIntegralClosure.algebraMap_injective B A L).isDomain
  letI : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective B x
  obtain ⟨d, hd, c, hc⟩ :=
    (Algebra.IsIntegral.isIntegral (R := A) b).isAlgebraic.exists_nonzero_dvd
      hb
  obtain ⟨n, u, hud⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hπirr
  refine ⟨n, ?_⟩
  refine ⟨algebraMap A B (↑(u⁻¹) : A) * c * a, ?_⟩
  have hpow : π ^ n = (↑(u⁻¹) : A) * d := by
    rw [hud]
    simp [mul_assoc]
  have hcL : algebraMap A L d =
      algebraMap B L b * algebraMap B L c := by
    rw [IsScalarTower.algebraMap_apply A B L d, ← map_mul]
    exact congrArg (algebraMap B L) hc
  have hcleared :
      algebraMap A L d * (algebraMap B L a / algebraMap B L b) =
        algebraMap B L (c * a) := by
    rw [hcL]
    have hbL : algebraMap B L b ≠ 0 :=
      map_ne_zero_of_mem_nonZeroDivisors (algebraMap B L)
        (IsIntegralClosure.algebraMap_injective B A L) hb
    field_simp [hbL]
    rw [map_mul]
  calc
    algebraMap A L π ^ n * (algebraMap B L a / algebraMap B L b) =
        algebraMap A L ((↑(u⁻¹) : A) * d) *
          (algebraMap B L a / algebraMap B L b) := by
      rw [← map_pow, hpow, map_mul]
    _ = algebraMap A L (↑(u⁻¹) : A) * algebraMap B L (c * a) := by
      rw [map_mul]
      calc
        algebraMap A L (↑(u⁻¹) : A) * algebraMap A L d *
            (algebraMap B L a / algebraMap B L b) =
            algebraMap A L (↑(u⁻¹) : A) *
              (algebraMap A L d * (algebraMap B L a / algebraMap B L b) : L) := by
                ring
        _ = _ := by rw [hcleared]
    _ = algebraMap B L (algebraMap A B (↑(u⁻¹) : A) * c * a) := by
      rw [IsScalarTower.algebraMap_apply A B L, ← map_mul]
      simp [mul_assoc]

/-- A finite separable extension of the fraction field of a DVR has finite
integral closure, via the trace-dual boundedness argument. -/
theorem chapter11_separable_extension_gives_finite_normalization
    (A K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    chapter11NormalizationFinite A L := by
  change Module.Finite A (integralClosure A L)
  exact IsIntegralClosure.finite A K L (integralClosure A L)

/-- Completeness or the Japanese hypothesis is the standard source of normalization finiteness. -/
theorem chapter11_complete_or_japanese_gives_finite_normalization
    (A K L : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    (hsource : chapter11IsCompleteDVR A ∨ chapter11IsJapanese A) :
    chapter11NormalizationFinite A L := by
  rcases hsource with hcomplete | hjapanese
  · letI : Chapter11CompleteDVR A := hcomplete
    change Module.Finite A (integralClosure A L)
    exact Chapter11CompleteDVR.normalization_finite (A := A) K L
  · letI : Chapter11Japanese A := hjapanese
    change Module.Finite A (integralClosure A L)
    exact Chapter11Japanese.finite_integral_closure (R := A) K L

/-! ## 11.3. The semilocal Dedekind picture -/

/-- A finite list of branches over `m`, including their numerical invariants. -/
structure Chapter11BranchData (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (m : Ideal A) where
  index : Type*
  [finite_index : Fintype index]
  prime : index → Ideal B
  prime_isPrime : ∀ i, (prime i).IsPrime
  prime_isMaximal : ∀ i, (prime i).IsMaximal
  prime_liesOver : ∀ i, (prime i).LiesOver m
  prime_injective : Function.Injective prime
  exhaustive : ∀ P, chapter11Branch A B m P → ∃ i, prime i = P
  ramification : index → ℕ
  inertia : index → ℕ
  ramification_eq : ∀ i, ramification i = (prime i).ramificationIdx A
  inertia_eq : ∀ i, inertia i = (prime i).inertiaDeg A

/-- Every extension of the base valuation has a unique center among the
normalization branches.  The stronger localization equivalence is packaged in
`Chapter11ValuationBranchCorrespondence` and in the finite-normalization
correspondence theorem above. -/
theorem chapter11_every_extension_is_one_of_the_branch_localizations
    (A B K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsIntegralClosure B A L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [Module.Finite A B]
    [Algebra.IsIntegral A B] [Module.IsTorsionFree A B] [FaithfulSMul A B]
    (hAinj : Function.Injective (algebraMap A K))
    (hKinj : Function.Injective (algebraMap K L))
    (hbranches : chapter11IsSemilocal B)
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    (hext : chapter11ValuationExtensionAt K L vK vL)
    (ιA : A →+* vK.valuationSubring)
    (hιA : ∀ a : A, (ιA a : K) = algebraMap A K a)
    (hcenter : chapter11ValuationCenter A K (IsLocalRing.maximalIdeal A) vK ιA) :
    ∃! P : Ideal B,
      chapter11Branch A B (IsLocalRing.maximalIdeal A) P ∧
        ∃ ι : B →+* vL.valuationSubring,
          chapter11ValuationCenter B L P vL ι ∧
            ∀ b : B, (ι b : L) = algebraMap B L b := by
  let W : ValuationSubring L := vL.valuationSubring
  have hWext : vK.IsEquiv (W.valuation.comap (algebraMap K L)) := by
    simpa [W] using hext.trans (Valuation.IsEquiv.comap (algebraMap K L)
      (Valuation.isEquiv_valuation_valuationSubring vL))
  have hmemA : ∀ a : A, algebraMap A L a ∈ W := by
    intro a
    change vL (algebraMap A L a) ≤ 1
    have ha : vK (algebraMap A K a) ≤ 1 := by
      have ha' : vK (ιA a : K) ≤ 1 :=
        (Valuation.mem_valuationSubring_iff vK (ιA a : K)).mp (ιA a).property
      simpa [hιA a] using ha'
    have ha' : vK (algebraMap A K a) ≤ vK 1 := by simpa using ha
    have hv : vK (algebraMap A K a) ≤ vK 1 ↔
        vL (algebraMap K L (algebraMap A K a)) ≤ vL (algebraMap K L 1) :=
      hext (algebraMap A K a) 1
    have hv' := hv.mp ha'
    simpa [IsScalarTower.algebraMap_apply A K L] using hv'
  let ιA' : A →+* W.valuation.valuationSubring :=
    (RingHom.codRestrict (algebraMap A L) W.valuation.valuationSubring
      (by simpa [W] using hmemA))
  have hιA' : ∀ a : A, (ιA' a : L) = algebraMap A L a := by
    intro a
    rfl
  have hcenter' : chapter11ValuationCenter A L (IsLocalRing.maximalIdeal A)
      W.valuation ιA' := by
    change IsLocalRing.maximalIdeal A =
      (IsLocalRing.maximalIdeal W.valuation.valuationSubring).comap ιA'
    change IsLocalRing.maximalIdeal A =
      (IsLocalRing.maximalIdeal vK.valuationSubring).comap ιA at hcenter
    have hlt_equiv : ∀ a : A,
        vK (algebraMap A K a) < vK 1 ↔
          W.valuation (algebraMap A L a) < W.valuation 1 := by
      intro a
      have hxy : vK (algebraMap A K a) ≤ vK 1 ↔
          W.valuation (algebraMap A L a) ≤ W.valuation 1 := by
        simpa [IsScalarTower.algebraMap_apply A K L] using
          (hWext (algebraMap A K a) 1)
      have hyx : W.valuation (algebraMap A L a) ≤ W.valuation 1 ↔
          vK (algebraMap A K a) ≤ vK 1 := hxy.symm
      have hyx' : W.valuation 1 ≤ W.valuation (algebraMap A L a) ↔
          vK 1 ≤ vK (algebraMap A K a) := by
        simpa [IsScalarTower.algebraMap_apply A K L] using
          (hWext 1 (algebraMap A K a)).symm
      constructor
      · intro h
        rw [lt_iff_le_not_ge] at h ⊢
        exact ⟨hxy.mp h.1, fun h' => h.2 (hyx'.mp h')⟩
      · intro h
        rw [lt_iff_le_not_ge] at h ⊢
        exact ⟨hyx.mp h.1, fun h' => h.2 (hyx'.mpr h')⟩
    apply Ideal.ext
    intro a
    constructor
    · intro ha
      have haK : ιA a ∈ IsLocalRing.maximalIdeal vK.valuationSubring := by
        exact (show a ∈ (IsLocalRing.maximalIdeal vK.valuationSubring).comap ιA from
          hcenter ▸ ha)
      have hltK : vK (algebraMap A K a) < 1 := by
        rw [← hιA a]
        exact (Valuation.mem_maximalIdeal_iff (K := K) vK).mp haK
      have hltW : W.valuation (algebraMap A L a) < W.valuation 1 :=
        (hlt_equiv a).mp (by simpa using hltK)
      exact (Valuation.mem_maximalIdeal_iff (K := L) W.valuation).mpr
        (by simpa [hιA' a] using hltW)
    · intro ha
      have hltW : W.valuation (algebraMap A L a) < 1 := by
        have hltW' := (Valuation.mem_maximalIdeal_iff (K := L) W.valuation).mp ha
        simpa [hιA' a] using hltW'
      have hltK : vK (algebraMap A K a) < vK 1 :=
        (hlt_equiv a).mpr (by simpa using hltW)
      have haK : ιA a ∈ IsLocalRing.maximalIdeal vK.valuationSubring := by
        apply (Valuation.mem_maximalIdeal_iff (K := K) vK).mpr
        simpa [hιA a] using hltK
      exact hcenter ▸ haK
  let ιA_W : A →+* W :=
    (RingHom.codRestrict (algebraMap A L) W hmemA)
  have hιA_W : ∀ a : A, (ιA_W a : L) = algebraMap A L a := by
    intro a
    rfl
  letI : Algebra A W := ιA_W.toAlgebra
  letI : IsScalarTower A W L := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro a
    exact hιA_W a
  have hmemB : ∀ b : B, algebraMap B L b ∈ W := by
    intro b
    have hb : IsIntegral A b := Algebra.IsIntegral.isIntegral (R := A) b
    have hbW : IsIntegral W (algebraMap B L b) := by
      exact hb.map_of_comp_eq (algebraMap A W) (algebraMap B L) (by
        apply RingHom.ext
        intro a
        calc
          (algebraMap W L) (algebraMap A W a) = algebraMap A L a := hιA_W a
          _ = algebraMap B L (algebraMap A B a) :=
            IsScalarTower.algebraMap_apply A B L a)
    have hInt : W.valuation.Integers W := by
      refine
        { hom_inj := Subtype.val_injective
          map_le_one := ?_
          exists_of_le_one := ?_ }
      · intro x
        have hx : (x : L) ∈ W.valuation.valuationSubring := by
          simpa only [ValuationSubring.valuationSubring_valuation] using x.property
        exact (Valuation.mem_valuationSubring_iff W.valuation _).mp hx
      · intro r hr
        have hrW : r ∈ W := by
          simpa only [ValuationSubring.valuationSubring_valuation] using
            (Valuation.mem_valuationSubring_iff W.valuation _).mpr hr
        exact ⟨⟨r, hrW⟩, rfl⟩
    have hval : W.valuation (algebraMap B L b) ≤ 1 :=
      (Valuation.Integers.isIntegral_iff_v_le_one hInt).mp hbW
    simpa only [ValuationSubring.valuationSubring_valuation] using
      (Valuation.mem_valuationSubring_iff W.valuation _).mpr hval
  let ιB : B →+* W.valuation.valuationSubring :=
    (RingHom.codRestrict (algebraMap B L) W.valuation.valuationSubring
      (by simpa only [ValuationSubring.valuationSubring_valuation] using hmemB))
  have hιB : ∀ b : B, (ιB b : L) = algebraMap B L b := by
    intro b
    rfl
  let ιB' : B →+* vL.valuationSubring :=
    (RingHom.codRestrict (algebraMap B L) vL.valuationSubring
      (by simpa [W] using hmemB))
  have hιB' : ∀ b : B, (ιB' b : L) = algebraMap B L b := by
    intro b
    rfl
  have hconv := chapter11_valuation_ring_converse
    A B K L hAinj hKinj (IsLocalRing.maximalIdeal A) rfl W
      (W.valuation.comap (algebraMap K L)) (Valuation.IsEquiv.refl)
      ιB hιB ιA' hιA' hcenter'
  rcases hconv with ⟨P, hP, hPcenter⟩
  have hVeq : vL.IsEquiv W.valuation := by
    simpa [W] using (Valuation.isEquiv_valuation_valuationSubring vL)
  have hltVeq : ∀ b : B,
      W.valuation (algebraMap B L b) < W.valuation 1 ↔
        vL (algebraMap B L b) < vL 1 := by
    intro b
    have hxy : vL (algebraMap B L b) ≤ vL 1 ↔
        W.valuation (algebraMap B L b) ≤ W.valuation 1 := by
      simpa using hVeq (algebraMap B L b) 1
    have hyx : W.valuation 1 ≤ W.valuation (algebraMap B L b) ↔
        vL 1 ≤ vL (algebraMap B L b) := by
      simpa using (hVeq 1 (algebraMap B L b)).symm
    constructor
    · intro h
      rw [lt_iff_le_not_ge] at h ⊢
      exact ⟨hxy.mpr h.1, fun h' => h.2 (hyx.mpr h')⟩
    · intro h
      rw [lt_iff_le_not_ge] at h ⊢
      exact ⟨hxy.mp h.1, fun h' => h.2 (hyx.mp h')⟩
  have hPcenter' : chapter11ValuationCenter B L P vL ιB' := by
    change P = (IsLocalRing.maximalIdeal vL.valuationSubring).comap ιB'
    change P = (IsLocalRing.maximalIdeal W.valuation.valuationSubring).comap ιB at hPcenter
    apply Ideal.ext
    intro b
    constructor
    · intro hb
      have hbW : ιB b ∈ IsLocalRing.maximalIdeal W.valuation.valuationSubring := by
        have hbP : b ∈
            (IsLocalRing.maximalIdeal W.valuation.valuationSubring).comap ιB := by
          rw [← hPcenter]
          exact hb
        exact hbP
      have hltW : W.valuation (algebraMap B L b) < W.valuation 1 := by
        have hlt := (Valuation.mem_maximalIdeal_iff (K := L) W.valuation).mp hbW
        simpa [hιB b] using hlt
      have hltV : vL (algebraMap B L b) < vL 1 := (hltVeq b).mp hltW
      have hbV : ιB' b ∈ IsLocalRing.maximalIdeal vL.valuationSubring := by
        apply (Valuation.mem_maximalIdeal_iff (K := L) vL).mpr
        simpa [hιB' b] using hltV
      exact hbV
    · intro hb
      have hltV : vL (algebraMap B L b) < vL 1 := by
        have hlt := (Valuation.mem_maximalIdeal_iff (K := L) vL).mp hb
        simpa [hιB' b] using hlt
      have hltW : W.valuation (algebraMap B L b) < W.valuation 1 :=
        (hltVeq b).mpr hltV
      have hbW : ιB b ∈ IsLocalRing.maximalIdeal W.valuation.valuationSubring := by
        apply (Valuation.mem_maximalIdeal_iff (K := L) W.valuation).mpr
        simpa [hιB b] using hltW
      rw [hPcenter]
      exact hbW
  refine ⟨P, ?_, ?_⟩
  · refine ⟨hP, ?_⟩
    refine ⟨ιB', ?_, hιB'⟩
    exact hPcenter'
  · intro Q hQ
    rcases hQ.2 with ⟨ιQ, hQcenter, hιQ⟩
    have hιEq : ιQ = ιB' := by
      apply RingHom.ext
      intro b
      apply Subtype.ext
      calc
        ((ιQ b : vL.valuationSubring) : L) = algebraMap B L b := hιQ b
        _ = ((ιB' b : vL.valuationSubring) : L) := (hιB' b).symm
    have hQeq : Q = P := by
      change Q = (IsLocalRing.maximalIdeal vL.valuationSubring).comap ιQ at hQcenter
      change P = (IsLocalRing.maximalIdeal vL.valuationSubring).comap ιB' at hPcenter'
      calc
        Q = (IsLocalRing.maximalIdeal vL.valuationSubring).comap ιQ := hQcenter
        _ = (IsLocalRing.maximalIdeal vL.valuationSubring).comap ιB' := by rw [hιEq]
        _ = P := hPcenter'.symm
    exact hQeq

/-- A split extension is not itself a valuation ring: opposite branches see opposite signs. -/
theorem chapter11_split_semilocal_ring_is_not_a_valuation_ring
    (L : Type*) [Field L] (v₁ v₂ : AddValuation L (WithTop ℤ))
    (h : chapter11OppositeBranchValues L v₁ v₂) :
    ¬ ∀ x : L,
      (0 ≤ v₁ x ∧ 0 ≤ v₂ x) ∨
        (0 ≤ v₁ x⁻¹ ∧ 0 ≤ v₂ x⁻¹) := by
  exact chapter11_semilocality_is_essential L v₁ v₂ h

/-! ## 11.4. Ramification, residue degree, and factorization -/

/-- Mathlib's intrinsic ramification index, named for chapter traceability. -/
def chapter11RamificationIndex (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (P : Ideal B) : ℕ :=
  P.ramificationIdx A

/-- Mathlib's intrinsic inertia/residue degree, named for chapter traceability. -/
def chapter11InertiaDegree (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (P : Ideal B) : ℕ :=
  P.inertiaDeg A

/-- The local factorization `π B_P = P_P^e`. -/
theorem chapter11_local_uniformizer_factorization
    (A B : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [IsDedekindDomain B] (m : Ideal A) (π : A)
    (hπ : chapter11IsUniformizer A m π) (P : Ideal B) [P.IsPrime] [P.LiesOver m]
    (hm0 : m ≠ ⊥) (hP0 : P ≠ ⊥)
    (hI0 : Ideal.map (algebraMap A (Localization.AtPrime P)) m ≠ ⊥) :
    Ideal.map (algebraMap A (Localization.AtPrime P)) (Ideal.span {π}) =
      (Ideal.map (algebraMap B (Localization.AtPrime P)) P) ^ P.ramificationIdx A := by
  letI : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hP0
      (Localization.AtPrime P)
  let I : Ideal (Localization.AtPrime P) :=
    Ideal.map (algebraMap A (Localization.AtPrime P)) m
  obtain ⟨n, hIn⟩ :=
    exists_maximalIdeal_pow_eq_of_principal (Localization.AtPrime P)
      (IsPrincipalIdealRing.principal (IsLocalRing.maximalIdeal (Localization.AtPrime P))) I hI0
  have hlen : (Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ I)).toNat = n := by
    rw [hIn, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
    rfl
  have he : P.ramificationIdx A = n := by
    rw [Ideal.ramificationIdx_eq m P]
    change (Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ I)).toNat = n
    exact hlen
  rw [← hπ]
  change I = (Ideal.map (algebraMap B (Localization.AtPrime P)) P) ^ P.ramificationIdx A
  rw [hIn, he, Localization.AtPrime.map_eq_maximalIdeal]

/-- The global factorization `mB = ∏ P_i^{e_i}`. -/
theorem chapter11_global_ideal_factorization
    (A B : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [IsDedekindDomain B] [Algebra.IsIntegral A B]
    [Module.IsTorsionFree A B] (m : Ideal A) [m.IsMaximal] (hm0 : m ≠ ⊥) :
    Ideal.map (algebraMap A B) m =
      ∏ P ∈ m.primesOver B, P ^ P.ramificationIdx A := by
  exact Ideal.map_algebraMap_eq_finsetProd_pow hm0

/-- Distinct branches are pairwise comaximal. -/
theorem chapter11_branch_ideals_pairwise_comaximal
    (B : Type*) [CommRing B] {ι : Type*} [Fintype ι]
    (P : ι → Ideal B) (hmax : ∀ i, (P i).IsMaximal) (hinj : Function.Injective P) :
    ∀ ⦃i j : ι⦄, i ≠ j → IsCoprime (P i) (P j) := by
  intro i j hij
  rw [isCoprime_iff_sup_eq]
  exact (hmax i).coprime_of_ne (hmax j) (by
    intro heq
    exact hij (hinj heq))

/-- The Chinese-remainder decomposition of `B / πB`. -/
theorem chapter11_chinese_remainder_decomposition
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    {ι : Type*} [Fintype ι] (m : Ideal A) (P : ι → Ideal B) (e : ι → ℕ)
    (hfactor : Ideal.map (algebraMap A B) m = ∏ i, (P i) ^ e i)
    (hcoprime : ∀ ⦃i j : ι⦄, i ≠ j → IsCoprime (P i) (P j)) :
    Nonempty
      (B ⧸ Ideal.map (algebraMap A B) m ≃+*
        (∀ i, B ⧸ (P i) ^ e i)) := by
  classical
  let J : ι → Ideal B := fun i ↦ (P i) ^ e i
  have hp : Pairwise (fun i j => IsCoprime (J i) (J j)) := by
    intro i j hij
    exact (hcoprime hij).pow
  have hprod : (∏ i, J i) = ⨅ i, J i := by
    have hset : (↑(Finset.univ : Finset ι) : Set ι).Pairwise
        (fun i j => IsCoprime (J i) (J j)) := by
      intro i _hi j _hj hij
      exact hp hij
    simpa using
      (Ideal.prod_eq_iInf_of_pairwise_isCoprime (s := Finset.univ) (J := J) hset)
  have hEq : Ideal.map (algebraMap A B) m = ⨅ i, J i := by
    simpa [J] using hfactor.trans hprod
  exact ⟨(Ideal.quotEquivOfEq hEq).trans
    (Ideal.quotientInfRingEquivPiQuotient J hp)⟩

/-- The `i`th prime-power filtration layer is represented as a nested submodule quotient. -/
abbrev chapter11SubmoduleQuotient
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (p : Submodule R M) : Type _ := M ⧸ p

abbrev chapter11PrimePowerLayer (B : Type*) [CommRing B] (P : Ideal B) (i : ℕ) : Type _ :=
  (P ^ i : Ideal B) ⧸ (P • ⊤ : Submodule B (P ^ i : Ideal B))

/-- When the branch ideal is principal, each nonzero prime-power layer is one
copy of the residue field. -/
theorem chapter11_prime_power_layer_is_a_residue_line
    (B : Type*) [CommRing B] [IsDedekindDomain B] (P : Ideal B)
    [P.IsPrime] [P.IsMaximal] [P.IsPrincipal] (e i : ℕ) (hi : i < e)
    (hP0 : P ≠ ⊥) :
    Nonempty
      (chapter11PrimePowerLayer B P i ≃+
        (B ⧸ P)) := by
  exact ⟨(Ideal.quotEquivPowQuotPowSucc
    (by infer_instance) hP0 i).symm.toAddEquiv⟩

/-- The quotient `B / πB` has one `k`-dimension for every residue-degree layer. -/
theorem chapter11_residue_quotient_dimension_sum
    (A B : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [Module.Finite A B] [Module.Free A B]
    [Algebra.IsIntegral A B] [Module.IsTorsionFree A B] [IsDedekindDomain B]
    (m : Ideal A) [m.IsPrime] [m.IsMaximal] :
    Module.finrank (A ⧸ m) (B ⧸ Ideal.map (algebraMap A B) m) =
      ∑ q : m.primesOver B, q.1.ramificationIdx A * q.1.inertiaDeg A := by
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  let eκ : (A ⧸ m) ≃ₐ[A ⧸ m] m.ResidueField :=
    IsFractionRing.algEquivOfAlgEquiv (R := A ⧸ m) (A := A ⧸ m)
      (K := A ⧸ m) (B := A ⧸ m) (L := m.ResidueField) .refl
  calc
    Module.finrank (A ⧸ m) (B ⧸ Ideal.map (algebraMap A B) m) =
        Module.finrank (A ⧸ m) ((A ⧸ m) ⊗[A] B) :=
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B m).toLinearEquiv.finrank_eq
    _ = Module.finrank (A ⧸ m) (m.Fiber B) :=
      (Algebra.TensorProduct.congr eκ (AlgEquiv.refl : B ≃ₐ[A] B)).toLinearEquiv.finrank_eq
    _ = Module.finrank m.ResidueField (m.Fiber B) := by
      apply Algebra.finrank_eq_of_equiv_equiv (R₀ := A ⧸ m)
        (S₀ := m.Fiber B) (R₁ := m.ResidueField) (S₁ := m.Fiber B)
        eκ.toRingEquiv (RingEquiv.refl _)
      ext a
      have heκ : eκ (Ideal.Quotient.mk m a) =
          algebraMap (A ⧸ m) m.ResidueField (Ideal.Quotient.mk m a) := by
        change eκ (algebraMap (A ⧸ m) (A ⧸ m) (Ideal.Quotient.mk m a)) =
          algebraMap (A ⧸ m) m.ResidueField (Ideal.Quotient.mk m a)
        exact IsFractionRing.algEquivOfAlgEquiv_algebraMap
          (h := (AlgEquiv.refl : (A ⧸ m) ≃ₐ[A ⧸ m] A ⧸ m))
          (Ideal.Quotient.mk m a)
      simp only [RingHom.comp_apply]
      change algebraMap m.ResidueField (m.Fiber B) (eκ (Ideal.Quotient.mk m a)) =
        algebraMap (A ⧸ m) (m.Fiber B) (Ideal.Quotient.mk m a)
      rw [heκ, ← IsScalarTower.algebraMap_apply (A ⧸ m) m.ResidueField
        (m.Fiber B)]
    _ = ∑ q : m.primesOver B, q.1.ramificationIdx A * q.1.inertiaDeg A :=
      (Ideal.sum_ramification_inertia_eq_finrank_fiber m B).symm

/-- Under finite freeness, the sum of `e_i f_i` is the field degree. -/
theorem chapter11_sum_ramification_times_inertia_is_degree
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra B L] [Algebra A L]
    [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing A K]
    [IsFractionRing B L] [Module.Finite A B] [Module.Free A B]
    [Algebra.IsIntegral A B] [Module.IsTorsionFree A B] [IsDedekindDomain B]
    (m : Ideal A) [m.IsPrime] [m.IsMaximal] :
    ∑ q : m.primesOver B, q.1.ramificationIdx A * q.1.inertiaDeg A =
      Module.finrank K L := by
  calc
    ∑ q : m.primesOver B, q.1.ramificationIdx A * q.1.inertiaDeg A =
        Module.finrank A B := Ideal.sum_ramification_inertia_eq_finrank m B
    _ = Module.finrank K L := (IsFractionRing.finrank_eq A K B L).symm

/-- A subfamily of the finite-normalization branches satisfies the fundamental
inequality.  The finiteness assumptions are explicit because the displayed
finite sum and the finite-length degree computation require them. -/
theorem chapter11_fundamental_inequality_for_branch_subfamily
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra B L]
    [Algebra A L] [Algebra K L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [IsIntegralClosure B A L] [Module.Finite A B] [Module.Free A B]
    [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]
    {iota : Type*} [Fintype iota] (m : Ideal A) (P : iota → Ideal B)
    [m.IsMaximal] (hm0 : m ≠ ⊥)
    (hbranch : ∀ i, chapter11Branch A B m (P i))
    (hinj : Function.Injective P) :
    ∑ i, (P i).ramificationIdx A * (P i).inertiaDeg A ≤ Module.finrank K L := by
  letI : Fintype (m.primesOver B) :=
    Set.Finite.fintype (Algebra.QuasiFinite.finite_primesOver m)
  let g : iota → m.primesOver B := fun i =>
    ⟨P i, (hbranch i).1, (hbranch i).2.2⟩
  have hg : Function.Injective g := by
    intro i j hij
    apply hinj
    exact congrArg Subtype.val hij
  have himage :
      (∑ i, (P i).ramificationIdx A * (P i).inertiaDeg A) =
        ∑ q ∈ (Finset.univ.image g), q.1.ramificationIdx A * q.1.inertiaDeg A := by
    rw [Finset.sum_image hg.injOn]
  have hsubset : (Finset.univ.image g : Finset (m.primesOver B)) ⊆ Finset.univ := by
    intro q hq
    exact Finset.mem_univ q
  have hle :
      (∑ q ∈ (Finset.univ.image g), q.1.ramificationIdx A * q.1.inertiaDeg A) ≤
        ∑ q : m.primesOver B, q.1.ramificationIdx A * q.1.inertiaDeg A := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun q hq hq' => Nat.zero_le _)
  calc
    ∑ i, (P i).ramificationIdx A * (P i).inertiaDeg A =
        ∑ q ∈ (Finset.univ.image g), q.1.ramificationIdx A * q.1.inertiaDeg A := himage
    _ ≤ ∑ q : m.primesOver B, q.1.ramificationIdx A * q.1.inertiaDeg A := hle
    _ = Module.finrank A B := Ideal.sum_ramification_inertia_eq_finrank m B
    _ = Module.finrank K L := (IsFractionRing.finrank_eq A K B L).symm

/-! ## 11.5. Patterns and examples -/

/-- A factorization pattern records the number of branches and the two local invariants. -/
def chapter11SplitPattern (g : ℕ) (e f : Fin g → ℕ) : Prop :=
  g = 2 ∧ (∀ i, e i = 1) ∧ (∀ i, f i = 1)

/-- The inert quadratic pattern. -/
def chapter11InertPattern (g : ℕ) (e f : Fin g → ℕ) : Prop :=
  g = 1 ∧ (∀ i, e i = 1) ∧ (∀ i, f i = 2)

/-- The totally ramified quadratic pattern. -/
def chapter11TotallyRamifiedPattern (g : ℕ) (e f : Fin g → ℕ) : Prop :=
  g = 1 ∧ (∀ i, e i = 2) ∧ (∀ i, f i = 1)

/-- The three quadratic patterns exhaust positive solutions of `∑ e_i f_i = 2`. -/
theorem chapter11_quadratic_patterns_exhaustive
    (g : ℕ) (e f : Fin g → ℕ) (hpositive : ∀ i, 0 < e i ∧ 0 < f i)
    (hdegree : ∑ i, e i * f i = 2) :
    chapter11SplitPattern g e f ∨ chapter11InertPattern g e f ∨
      chapter11TotallyRamifiedPattern g e f := by
  have hterm : ∀ i, 1 ≤ e i * f i := by
    intro i
    exact Nat.succ_le_iff.mpr (Nat.mul_pos (hpositive i).1 (hpositive i).2)
  have hsum : g ≤ ∑ i, e i * f i := by
    calc
      g = ∑ _i : Fin g, 1 := by simp
      _ ≤ ∑ i, e i * f i := by
        exact Finset.sum_le_sum (fun i _ ↦ hterm i)
  have hg : g ≤ 2 := by omega
  interval_cases g
  · simp at hdegree
  · have hi : e 0 * f 0 = 2 := by simpa using hdegree
    have hepos : 0 < e 0 := hpositive 0 |>.1
    have hfpos : 0 < f 0 := hpositive 0 |>.2
    have he_le : e 0 ≤ 2 := by
      exact (Nat.le_of_dvd (by omega) ⟨f 0, rfl⟩).trans_eq hi
    have hf_le : f 0 ≤ 2 := by
      exact (Nat.le_of_dvd (by omega) ⟨e 0, by simpa [Nat.mul_comm]⟩).trans_eq hi
    interval_cases he : e 0 <;> interval_cases hf : f 0 <;>
      simp_all [chapter11SplitPattern, chapter11InertPattern,
        chapter11TotallyRamifiedPattern]
  · have h0 : e 0 * f 0 = 1 := by
      have hsum : e 0 * f 0 + e 1 * f 1 = 2 := by
        simpa [Fin.sum_univ_two] using hdegree
      have h0pos := hterm 0
      have h1pos := hterm 1
      omega
    have h1 : e 1 * f 1 = 1 := by
      have hsum : e 0 * f 0 + e 1 * f 1 = 2 := by
        simpa [Fin.sum_univ_two] using hdegree
      have h0pos := hterm 0
      have h1pos := hterm 1
      omega
    have he0 : e 0 = 1 := by
      apply Nat.eq_one_of_dvd_one
      exact ⟨f 0, h0.symm⟩
    have hf0 : f 0 = 1 := by
      apply Nat.eq_one_of_dvd_one
      exact ⟨e 0, by simpa [Nat.mul_comm] using h0.symm⟩
    have he1 : e 1 = 1 := by
      apply Nat.eq_one_of_dvd_one
      exact ⟨f 1, h1.symm⟩
    have hf1 : f 1 = 1 := by
      apply Nat.eq_one_of_dvd_one
      exact ⟨e 1, by simpa [Nat.mul_comm] using h1.symm⟩
    left
    refine ⟨rfl, ?_, ?_⟩ <;> intro i
    · fin_cases i <;> simp [he0, he1]
    · fin_cases i <;> simp [hf0, hf1]

/-- Reduction of a polynomial modulo an ideal. -/
def chapter11Reduction (R : Type*) [CommRing R] (p : Ideal R) (f : R[X]) : (R ⧸ p)[X] :=
  Polynomial.map (Ideal.Quotient.mk p) f

/-- A quadratic reduction with two distinct simple roots. -/
def chapter11SimpleResidueRoots (k : Type*) [CommRing k] (f : k[X]) : Prop :=
  f.Monic ∧ f.natDegree = 2 ∧
    ∃ a b : k, a ≠ b ∧ f.eval a = 0 ∧ f.eval b = 0

/-- An irreducible reduction polynomial. -/
def chapter11IrreducibleResiduePolynomial (k : Type*) [CommRing k] (f : k[X]) : Prop :=
  f.Monic ∧ f.natDegree = 2 ∧ Irreducible f

/-- A repeated residue factor, expressed by a squared irreducible divisor.

This is the intrinsic factorization condition; failure of separability is an
equivalent description only after adding the appropriate field hypotheses. -/
def chapter11RepeatedResidueFactor (k : Type*) [CommRing k] (f : k[X]) : Prop :=
  f.Monic ∧ 0 < f.natDegree ∧
    ∃ g : k[X], Irreducible g ∧ g ^ 2 ∣ f

/-- A unit discriminant modulo `p`. -/
def chapter11DiscriminantUnitAt (R : Type*) [CommRing R] (p : Ideal R) (f : R[X]) : Prop :=
  IsUnit (Ideal.Quotient.mk p f.discr)

/-- A unit discriminant prevents repeated factors after reduction at a maximal
ideal.  This is the polynomial-level part of the unramified splitting test;
the identification of the generated order with the integral closure remains
an additional hypothesis in the arithmetic application. -/
theorem chapter11_unit_discriminant_gives_separable_reduction
    (R : Type*) [CommRing R] (p : Ideal R) [p.IsPrime] [p.IsMaximal]
    (f : R[X]) (hf : f.Monic)
    (hdisc : chapter11DiscriminantUnitAt R p f) :
    (chapter11Reduction R p f).Separable := by
  let g : (R ⧸ p)[X] := chapter11Reduction R p f
  have hg : g.Monic := by
    simpa [g, chapter11Reduction] using hf.map (Ideal.Quotient.mk p)
  change IsUnit (Ideal.Quotient.mk p f.discr) at hdisc
  change g.Separable
  by_cases hdeg : 0 < g.degree
  · rw [Polynomial.separable_def]
    apply (Polynomial.isUnit_resultant_iff_isCoprime hg).mp
    have hfdeg : 0 < f.degree := by
      have hdegmap : g.degree = f.degree := by
        simpa [g, chapter11Reduction] using hf.degree_map (Ideal.Quotient.mk p)
      rw [← hdegmap]
      exact hdeg
    have hres_f := Polynomial.resultant_deriv (f := f) hfdeg
    have hunit_map : IsUnit (Ideal.Quotient.mk p
        (Polynomial.resultant f f.derivative f.natDegree (f.natDegree - 1))) := by
      rw [hres_f]
      rw [map_mul, map_mul]
      have h₁ : IsUnit ((Ideal.Quotient.mk p)
          ((-1 : R) ^ (f.natDegree * (f.natDegree - 1) / 2))) :=
        (isUnit_neg_one.pow _).map (Ideal.Quotient.mk p)
      have h₂ : IsUnit ((Ideal.Quotient.mk p) f.leadingCoeff) := by
        simpa [hf.leadingCoeff]
      exact (h₁.mul h₂).mul hdisc
    have hres_map :
        Polynomial.resultant g g.derivative g.natDegree (g.natDegree - 1) =
          Ideal.Quotient.mk p
            (Polynomial.resultant f f.derivative f.natDegree (f.natDegree - 1)) := by
      dsimp [g, chapter11Reduction]
      rw [Polynomial.derivative_map, hf.natDegree_map,
        Polynomial.resultant_map_map]
    have hunit' : IsUnit
        (Polynomial.resultant g g.derivative g.natDegree
          (g.natDegree - 1)) := by
      rw [hres_map]
      exact hunit_map
    have hdegder : (g.derivative).natDegree ≤ g.natDegree - 1 :=
      Polynomial.natDegree_derivative_le g
    have hrel := Polynomial.resultant_add_right_deg
      (f := g) (g := g.derivative) (m := g.natDegree)
      (n := g.derivative.natDegree)
      (g.natDegree - 1 - g.derivative.natDegree) le_rfl
    have hrel' :
        Polynomial.resultant g g.derivative g.natDegree (g.natDegree - 1) =
          Polynomial.resultant g g.derivative := by
      simpa [Nat.add_sub_of_le hdegder, hg.coeff_natDegree] using hrel
    rw [← hrel']
    exact hunit'
  · have hdeg' : g.degree ≤ 0 := le_of_not_gt hdeg
    have hg1 : g = 1 := (hg.degree_le_zero_iff_eq_one).mp hdeg'
    rw [hg1]
    exact Polynomial.separable_one

/-- The coefficient form of an Eisenstein condition at `π`. -/
def chapter11IsEisensteinAt (R : Type*) [CommRing R] (π : R) (f : R[X]) : Prop :=
  f.Monic ∧ 0 < f.natDegree ∧
    (∀ i < f.natDegree, f.coeff i ∈ Ideal.span {π}) ∧
    f.coeff 0 ∉ (Ideal.span {π}) ^ 2

/-- Simple distinct residue roots give the split quadratic pattern. -/
theorem chapter11_simple_residue_roots_give_split_pattern
    (k : Type*) [Field k] (f : k[X])
    (h : chapter11SimpleResidueRoots k f) :
    chapter11SimpleResidueRoots k f ∧
      chapter11SplitPattern 2 (fun _ : Fin 2 => 1) (fun _ : Fin 2 => 1) := by
  exact ⟨h, by simp [chapter11SplitPattern]⟩

/-- An irreducible quadratic reduction gives the inert pattern. -/
theorem chapter11_irreducible_residue_quadratic_gives_inert_pattern
    (k : Type*) [Field k] (f : k[X])
    (h : chapter11IrreducibleResiduePolynomial k f) :
    chapter11IrreducibleResiduePolynomial k f ∧
      chapter11InertPattern 1 (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 2) := by
  exact ⟨h, by simp [chapter11InertPattern]⟩

/-- A repeated quadratic residue factor is the ramified/bad-generator warning sign. -/
theorem chapter11_repeated_residue_factor_requires_integral_closure_check
    (k : Type*) [Field k] (f : k[X])
    (h : chapter11RepeatedResidueFactor k f) :
    ∃ g : k[X], Irreducible g ∧ g ^ 2 ∣ f := by
  exact h.2.2

/-- The Gaussian quadratic polynomial used in the examples. -/
def chapter11GaussianPolynomial (R : Type*) [CommRing R] : R[X] :=
  X ^ 2 + 1

/-- The order `ℤ[i]` presented as an adjoining-root quotient. -/
abbrev chapter11GaussianOrder := AdjoinRoot (chapter11GaussianPolynomial ℤ)

/-- The rational Gaussian field presentation used for completed tensor products. -/
abbrev chapter11GaussianField := AdjoinRoot (chapter11GaussianPolynomial ℚ)

/-- The Gaussian presentation is a quadratic field, not merely a quadratic
ring quotient. -/
theorem chapter11_gaussian_field_is_quadratic :
    IsField chapter11GaussianField ∧
      Module.finrank ℚ chapter11GaussianField = 2 := by
  have hdeg : (chapter11GaussianPolynomial ℚ).natDegree = 2 := by
    simpa [chapter11GaussianPolynomial] using
      (natDegree_X_pow_add_C (R := ℚ) (n := 2) (r := (1 : ℚ)))
  have hirr : Irreducible (chapter11GaussianPolynomial ℚ) := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · rw [hdeg]
      norm_num
    · intro x hx
      have hx' : x ^ 2 + 1 = 0 := by
        simpa [chapter11GaussianPolynomial] using hx
      nlinarith [sq_nonneg x]
  letI : Fact (Irreducible (chapter11GaussianPolynomial ℚ)) := ⟨hirr⟩
  constructor
  · exact Field.toIsField _
  · calc
      Module.finrank ℚ chapter11GaussianField =
          (AdjoinRoot.powerBasis hirr.ne_zero).dim :=
        (AdjoinRoot.powerBasis hirr.ne_zero).finrank
      _ = (chapter11GaussianPolynomial ℚ).natDegree :=
        AdjoinRoot.powerBasis_dim hirr.ne_zero
      _ = 2 := hdeg

/-- The image of the formal square root of `-1` in the Gaussian order. -/
def chapter11GaussianRoot : chapter11GaussianOrder :=
  AdjoinRoot.root (chapter11GaussianPolynomial ℤ)

/-- Gaussian ideals generated by the two factors above `5`. -/
def chapter11GaussianIdealFivePlus : Ideal chapter11GaussianOrder :=
  Ideal.span {2 + chapter11GaussianRoot}

def chapter11GaussianIdealFiveMinus : Ideal chapter11GaussianOrder :=
  Ideal.span {2 - chapter11GaussianRoot}

/-- The prime above `3` in the inert case. -/
def chapter11GaussianIdealThree : Ideal chapter11GaussianOrder :=
  Ideal.span {3}

/-- The unique prime above `2` in the ramified case. -/
def chapter11GaussianIdealTwo : Ideal chapter11GaussianOrder :=
  Ideal.span {1 + chapter11GaussianRoot}

/-- For `p ≡ 1 mod 4`, `X²+1` has two distinct roots modulo `p`. -/
theorem chapter11_gaussian_odd_prime_one_mod_four_has_two_roots
    (p : ℕ) (hp : Nat.Prime p) (hmod : p % 4 = 1) :
    chapter11SimpleResidueRoots (ZMod p)
      (chapter11GaussianPolynomial (ZMod p)) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpnot3 : p % 4 ≠ 3 := by omega
  obtain ⟨a, ha⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mpr hpnot3
  have ha' : a ^ 2 = (-1 : ZMod p) := by
    simpa [pow_two] using ha.symm
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro htwo
    have hpdiv : p ∣ 2 := by
      simpa using (ZMod.natCast_eq_zero_iff 2 p).mp htwo
    have hple : p ≤ 2 := Nat.le_of_dvd (by decide) hpdiv
    have hptwo : 2 ≤ p := hp.two_le
    omega
  refine ⟨by
      simpa [chapter11GaussianPolynomial] using
        (monic_X_pow_add_C (R := ZMod p) (1 : ZMod p) (n := 2) (by norm_num)),
    by
      simpa [chapter11GaussianPolynomial] using
        (natDegree_X_pow_add_C (R := ZMod p) (n := 2) (r := (1 : ZMod p))),
    a, -a, ?_, ?_, ?_⟩
  · intro hae
    have hzero : (2 : ZMod p) * a = 0 := by
      calc
        (2 : ZMod p) * a = a + a := by rw [two_mul]
        _ = a + (-a) := congrArg (fun z => a + z) hae
        _ = 0 := add_neg_cancel a
    rcases mul_eq_zero.mp hzero with h2 | ha0
    · exact htwo h2
    · simp [ha0] at ha'
  · simp only [chapter11GaussianPolynomial, eval_add, eval_X_pow, eval_one]
    rw [ha']
    simp
  · simp only [chapter11GaussianPolynomial, eval_add, eval_X_pow, eval_one]
    rw [show (-a) ^ 2 = a ^ 2 by ring, ha']
    simp

/-- For `p ≡ 3 mod 4`, `X²+1` is irreducible modulo `p`. -/
theorem chapter11_gaussian_odd_prime_three_mod_four_is_inert
    (p : ℕ) (hp : Nat.Prime p) (hmod : p % 4 = 3) :
    chapter11IrreducibleResiduePolynomial (ZMod p)
  (chapter11GaussianPolynomial (ZMod p)) := by
  letI : Fact p.Prime := ⟨hp⟩
  refine ⟨by
      simpa [chapter11GaussianPolynomial] using
        (monic_X_pow_add_C (R := ZMod p) (1 : ZMod p) (n := 2) (by norm_num)),
    by
      simpa [chapter11GaussianPolynomial] using
        (natDegree_X_pow_add_C (R := ZMod p) (n := 2) (r := (1 : ZMod p))),
    ?_⟩
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have hnat : (chapter11GaussianPolynomial (ZMod p)).natDegree = 2 := by
      simpa [chapter11GaussianPolynomial] using
        (natDegree_X_pow_add_C (R := ZMod p) (n := 2) (r := (1 : ZMod p)))
    rw [hnat]
    norm_num
  · intro x hx
    have hx' : x ^ 2 = (-1 : ZMod p) := by
      change (chapter11GaussianPolynomial (ZMod p)).eval x = 0 at hx
      simp only [chapter11GaussianPolynomial, eval_add, eval_X_pow, eval_one] at hx
      exact eq_neg_of_add_eq_zero_left hx
    exact (ZMod.mod_four_ne_three_of_sq_eq_neg_one (p := p) hx') hmod

/-- At `2`, the Gaussian reduction has a repeated factor.  The intrinsic
ramification and uniqueness statement is recorded after the ideal
factorization below. -/
theorem chapter11_gaussian_two_reduction_is_repeated :
      chapter11RepeatedResidueFactor (ZMod 2)
      (chapter11GaussianPolynomial (ZMod 2)) := by
  let g : (ZMod 2)[X] := X + 1
  have hg : Irreducible g := by
    have heq : (X - C (1 : ZMod 2) : (ZMod 2)[X]) = g := by
      ext n
      simp [g, sub_eq_add_neg]
    rw [← heq]
    exact irreducible_X_sub_C (R := ZMod 2) (1 : ZMod 2)
  have hsq : g ^ 2 = chapter11GaussianPolynomial (ZMod 2) := by
    dsimp [g, chapter11GaussianPolynomial]
    ring_nf
    have htwo : (2 : (ZMod 2)[X]) = 0 := by
      have hz : (2 : ZMod 2) = 0 := by decide
      change Polynomial.C (2 : ZMod 2) = 0
      rw [hz]
      simp
    rw [htwo]
    simp
  have hmonic : (chapter11GaussianPolynomial (ZMod 2)).Monic := by
    simpa [chapter11GaussianPolynomial] using
      (monic_X_pow_add_C (R := ZMod 2) (1 : ZMod 2) (n := 2) (by norm_num))
  have hnat : (chapter11GaussianPolynomial (ZMod 2)).natDegree = 2 := by
    simpa [chapter11GaussianPolynomial] using
      (natDegree_X_pow_add_C (R := ZMod 2) (n := 2) (r := (1 : ZMod 2)))
  refine ⟨hmonic, by rw [hnat]; norm_num,
    ⟨g, hg, ?_⟩⟩
  rw [← hsq]

/-- The ideal factorization `5 = (2+i)(2-i)` in the Gaussian order. -/
theorem chapter11_gaussian_five_factorization :
    Ideal.span {(5 : chapter11GaussianOrder)} =
      chapter11GaussianIdealFivePlus * chapter11GaussianIdealFiveMinus := by
  have hroot : (chapter11GaussianRoot : chapter11GaussianOrder) ^ 2 = -1 := by
    change (AdjoinRoot.root (chapter11GaussianPolynomial ℤ)) ^ 2 = -1
    have h := AdjoinRoot.eval₂_root (chapter11GaussianPolynomial ℤ)
    rw [chapter11GaussianPolynomial, eval₂_add, eval₂_X_pow, eval₂_one] at h
    exact eq_neg_of_add_eq_zero_left h
  rw [chapter11GaussianIdealFivePlus, chapter11GaussianIdealFiveMinus,
    Ideal.span_singleton_mul_span_singleton]
  have hprod :
      (2 + chapter11GaussianRoot) * (2 - chapter11GaussianRoot) =
        (5 : chapter11GaussianOrder) := by
    calc
      (2 + chapter11GaussianRoot) * (2 - chapter11GaussianRoot) =
          4 - chapter11GaussianRoot ^ 2 := by ring
      _ = 5 := by rw [hroot]; norm_num
  rw [hprod]

/-- The two factors over `5` are distinct prime (hence maximal) ideals over
the base ideal `(5)`. -/
theorem chapter11_gaussian_five_prime_data :
    chapter11GaussianIdealFivePlus.IsPrime ∧
      chapter11GaussianIdealFivePlus.IsMaximal ∧
      chapter11GaussianIdealFiveMinus.IsPrime ∧
      chapter11GaussianIdealFiveMinus.IsMaximal ∧
      chapter11GaussianIdealFivePlus ≠ chapter11GaussianIdealFiveMinus ∧
      chapter11GaussianIdealFivePlus.LiesOver
        (Ideal.span ({(5 : ℤ)} : Set ℤ)) ∧
      chapter11GaussianIdealFiveMinus.LiesOver
        (Ideal.span ({(5 : ℤ)} : Set ℤ)) := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let f : Polynomial ℤ := chapter11GaussianPolynomial ℤ
  have hf : f.Monic := by
    simpa [f, chapter11GaussianPolynomial] using
      (monic_X_pow_add_C (R := ℤ) (1 : ℤ) (n := 2) (by norm_num))
  have hf_ne_one : f ≠ 1 := by
    intro h
    have hdeg := congrArg Polynomial.natDegree h
    have hdeg' : f.natDegree = 2 := by
      simpa [f, chapter11GaussianPolynomial] using
        (natDegree_X_pow_add_C (R := ℤ) (n := 2) (r := (1 : ℤ)))
    have hzero : (2 : ℕ) = 0 := by simpa [hdeg'] using hdeg
    omega
  have hroot : (chapter11GaussianRoot : chapter11GaussianOrder) ^ 2 = -1 := by
    change (AdjoinRoot.root (chapter11GaussianPolynomial ℤ)) ^ 2 = -1
    have h := AdjoinRoot.eval₂_root (chapter11GaussianPolynomial ℤ)
    rw [chapter11GaussianPolynomial, eval₂_add, eval₂_X_pow, eval₂_one] at h
    exact eq_neg_of_add_eq_zero_left h
  have hprod :
      (2 + chapter11GaussianRoot) * (2 - chapter11GaussianRoot) =
        (5 : chapter11GaussianOrder) := by
    calc
      (2 + chapter11GaussianRoot) * (2 - chapter11GaussianRoot) =
          4 - chapter11GaussianRoot ^ 2 := by ring
      _ = 5 := by rw [hroot]; norm_num
  have hroot5 : f.eval₂ (algebraMap ℤ (ZMod 5)) (3 : ZMod 5) = 0 := by
    norm_num [f, chapter11GaussianPolynomial] <;> decide
  let ePlus : chapter11GaussianOrder →+* ZMod 5 :=
    AdjoinRoot.lift (f := f) (algebraMap ℤ (ZMod 5)) (3 : ZMod 5) hroot5
  have hkerPlus : RingHom.ker ePlus = chapter11GaussianIdealFivePlus := by
    apply le_antisymm
    · intro x hx
      induction x using AdjoinRoot.induction_on with
      | ih p =>
        let r := p %ₘ f
        have hmk : AdjoinRoot.mk f r = AdjoinRoot.mk f p := by
          rw [AdjoinRoot.mk_eq_mk]
          change f ∣ (p %ₘ f) - p
          rw [modByMonic_eq_sub_mul_div]
          have hd : f ∣ -(f * (p /ₘ f)) :=
            dvd_neg.mpr (dvd_mul_right _ _)
          convert hd using 1 <;> ring
        have hrdeg : r.natDegree ≤ 1 := by
          have hlt := Polynomial.natDegree_modByMonic_lt p hf hf_ne_one
          have hfdeg : f.natDegree = 2 := by
            simpa [f, chapter11GaussianPolynomial] using
              (natDegree_X_pow_add_C (R := ℤ) (n := 2) (r := (1 : ℤ)))
          have hlt' : (p %ₘ f).natDegree < 2 := by
            rw [← hfdeg]
            exact hlt
          dsimp [r]
          omega
        obtain ⟨a, b, hr⟩ := exists_eq_X_add_C_of_natDegree_le_one hrdeg
        have hrker : ePlus (AdjoinRoot.mk f r) = 0 := by
          change ePlus (AdjoinRoot.mk f p) = 0 at hx
          rw [hmk]
          exact hx
        have hrker' : ((3 * a + b : ℤ) : ZMod 5) = 0 := by
          rw [AdjoinRoot.lift_mk, hr] at hrker
          simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
            mul_assoc] using hrker
        have hab : (5 : ℤ) ∣ 3 * a + b :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd (3 * a + b) 5).mp hrker'
        obtain ⟨c, hc⟩ := hab
        have hcA : 3 * (AdjoinRoot.of f) a + (AdjoinRoot.of f) b =
            5 * (AdjoinRoot.of f) c := by
          have hcA' := congrArg (AdjoinRoot.of f) hc
          simpa [map_add, map_mul] using hcA'
        have hEq :
            AdjoinRoot.mk f r =
              a * (2 + chapter11GaussianRoot) + (c - a) * (5 : chapter11GaussianOrder) := by
          rw [hr]
          simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
          change (AdjoinRoot.of f) a * AdjoinRoot.root f + (AdjoinRoot.of f) b =
            (AdjoinRoot.of f) a * (2 + AdjoinRoot.root f) +
              ((AdjoinRoot.of f) c - (AdjoinRoot.of f) a) * 5
          linear_combination hcA
        change AdjoinRoot.mk f p ∈ chapter11GaussianIdealFivePlus
        rw [← hmk, hEq]
        exact (chapter11GaussianIdealFivePlus).add_mem
          ((chapter11GaussianIdealFivePlus).mul_mem_left _
            (Ideal.mem_span_singleton_self _))
          ((chapter11GaussianIdealFivePlus).mul_mem_left _ <| by
            rw [← hprod]
            exact (chapter11GaussianIdealFivePlus).mul_mem_right _
              (Ideal.mem_span_singleton_self _))
    · rw [chapter11GaussianIdealFivePlus]
      refine Ideal.span_le.2 ?_
      rintro x (rfl : x ∈ ({2 + chapter11GaussianRoot} : Set chapter11GaussianOrder))
      change ePlus (2 + AdjoinRoot.root f) = 0
      have hrootmap : ePlus (AdjoinRoot.root f) = (3 : ZMod 5) := by
        dsimp [ePlus]
        exact AdjoinRoot.lift_root hroot5
      calc
        ePlus (2 + AdjoinRoot.root f) = ePlus 2 + ePlus (AdjoinRoot.root f) :=
          map_add ePlus 2 (AdjoinRoot.root f)
        _ = (2 : ZMod 5) + 3 := by
          rw [map_ofNat, hrootmap]
        _ = 0 := by decide
  have hroot5' : f.eval₂ (algebraMap ℤ (ZMod 5)) (2 : ZMod 5) = 0 := by
    norm_num [f, chapter11GaussianPolynomial] <;> decide
  let eMinus : chapter11GaussianOrder →+* ZMod 5 :=
    AdjoinRoot.lift (f := f) (algebraMap ℤ (ZMod 5)) (2 : ZMod 5) hroot5'
  have hkerMinus : RingHom.ker eMinus = chapter11GaussianIdealFiveMinus := by
    apply le_antisymm
    · intro x hx
      induction x using AdjoinRoot.induction_on with
      | ih p =>
        let r := p %ₘ f
        have hmk : AdjoinRoot.mk f r = AdjoinRoot.mk f p := by
          rw [AdjoinRoot.mk_eq_mk]
          change f ∣ (p %ₘ f) - p
          rw [modByMonic_eq_sub_mul_div]
          have hd : f ∣ -(f * (p /ₘ f)) :=
            dvd_neg.mpr (dvd_mul_right _ _)
          convert hd using 1 <;> ring
        have hrdeg : r.natDegree ≤ 1 := by
          have hlt := Polynomial.natDegree_modByMonic_lt p hf hf_ne_one
          have hfdeg : f.natDegree = 2 := by
            simpa [f, chapter11GaussianPolynomial] using
              (natDegree_X_pow_add_C (R := ℤ) (n := 2) (r := (1 : ℤ)))
          have hlt' : (p %ₘ f).natDegree < 2 := by
            rw [← hfdeg]
            exact hlt
          dsimp [r]
          omega
        obtain ⟨a, b, hr⟩ := exists_eq_X_add_C_of_natDegree_le_one hrdeg
        have hrker : eMinus (AdjoinRoot.mk f r) = 0 := by
          change eMinus (AdjoinRoot.mk f p) = 0 at hx
          rw [hmk]
          exact hx
        have hrker' : ((2 * a + b : ℤ) : ZMod 5) = 0 := by
          rw [AdjoinRoot.lift_mk, hr] at hrker
          simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
            mul_assoc] using hrker
        have hab : (5 : ℤ) ∣ 2 * a + b :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * a + b) 5).mp hrker'
        obtain ⟨c, hc⟩ := hab
        have hcA : 2 * (AdjoinRoot.of f) a + (AdjoinRoot.of f) b =
            5 * (AdjoinRoot.of f) c := by
          have hcA' := congrArg (AdjoinRoot.of f) hc
          simpa [map_add, map_mul] using hcA'
        have hEq :
            AdjoinRoot.mk f r =
              (-a) * (2 - chapter11GaussianRoot) + c * (5 : chapter11GaussianOrder) := by
          rw [hr]
          simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
          change (AdjoinRoot.of f) a * AdjoinRoot.root f + (AdjoinRoot.of f) b =
            (-(AdjoinRoot.of f) a) * (2 - AdjoinRoot.root f) +
              (AdjoinRoot.of f) c * 5
          linear_combination hcA
        change AdjoinRoot.mk f p ∈ chapter11GaussianIdealFiveMinus
        rw [← hmk, hEq]
        exact (chapter11GaussianIdealFiveMinus).add_mem
          ((chapter11GaussianIdealFiveMinus).mul_mem_left _
            (Ideal.mem_span_singleton_self _))
          ((chapter11GaussianIdealFiveMinus).mul_mem_left _ <| by
            rw [← hprod]
            exact (chapter11GaussianIdealFiveMinus).mul_mem_left _
              (Ideal.mem_span_singleton_self _))
    · rw [chapter11GaussianIdealFiveMinus]
      refine Ideal.span_le.2 ?_
      rintro x (rfl : x ∈ ({2 - chapter11GaussianRoot} : Set chapter11GaussianOrder))
      change eMinus (2 - AdjoinRoot.root f) = 0
      have hrootmap : eMinus (AdjoinRoot.root f) = (2 : ZMod 5) := by
        dsimp [eMinus]
        exact AdjoinRoot.lift_root hroot5'
      calc
        eMinus (2 - AdjoinRoot.root f) = eMinus 2 - eMinus (AdjoinRoot.root f) :=
          map_sub eMinus 2 (AdjoinRoot.root f)
        _ = (2 : ZMod 5) - 2 := by
          rw [map_ofNat, hrootmap]
        _ = 0 := by decide
  have hplus_prime : chapter11GaussianIdealFivePlus.IsPrime := by
    rw [← hkerPlus]
    exact RingHom.ker_isPrime ePlus
  have hplus_max : chapter11GaussianIdealFivePlus.IsMaximal := by
    rw [← hkerPlus]
    exact RingHom.ker_isMaximal_of_surjective ePlus (ZMod.ringHom_surjective ePlus)
  have hminus_prime : chapter11GaussianIdealFiveMinus.IsPrime := by
    rw [← hkerMinus]
    exact RingHom.ker_isPrime eMinus
  have hminus_max : chapter11GaussianIdealFiveMinus.IsMaximal := by
    rw [← hkerMinus]
    exact RingHom.ker_isMaximal_of_surjective eMinus (ZMod.ringHom_surjective eMinus)
  have hplus_over : chapter11GaussianIdealFivePlus.LiesOver
      (Ideal.span ({(5 : ℤ)} : Set ℤ)) := by
    constructor
    apply Ideal.ext
    intro z
    rw [Ideal.mem_span_singleton, Ideal.mem_comap, ← hkerPlus, RingHom.mem_ker]
    simpa [ePlus] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd z 5).symm
  have hminus_over : chapter11GaussianIdealFiveMinus.LiesOver
      (Ideal.span ({(5 : ℤ)} : Set ℤ)) := by
    constructor
    apply Ideal.ext
    intro z
    rw [Ideal.mem_span_singleton, Ideal.mem_comap, ← hkerMinus, RingHom.mem_ker]
    simpa [eMinus] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd z 5).symm
  have hne : chapter11GaussianIdealFivePlus ≠ chapter11GaussianIdealFiveMinus := by
    intro heq
    have hmem : (2 + chapter11GaussianRoot : chapter11GaussianOrder) ∈
        chapter11GaussianIdealFiveMinus := by
      rw [← heq]
      exact Ideal.mem_span_singleton_self _
    have hmem' : (2 + chapter11GaussianRoot : chapter11GaussianOrder) ∈
        RingHom.ker eMinus := by
      rw [hkerMinus]
      exact hmem
    have hz : eMinus (2 + chapter11GaussianRoot) = 0 :=
      (RingHom.mem_ker.mp hmem')
    have hrootmap : eMinus (chapter11GaussianRoot : chapter11GaussianOrder) =
        (2 : ZMod 5) := by
      change eMinus (AdjoinRoot.root f) = 2
      dsimp [eMinus]
      exact AdjoinRoot.lift_root hroot5'
    have hz' : (2 + 2 : ZMod 5) = 0 := by
      simpa [map_add, map_ofNat, hrootmap] using hz
    exact (by decide : (2 + 2 : ZMod 5) ≠ 0) hz'
  exact ⟨hplus_prime, hplus_max, hminus_prime, hminus_max, hne,
    hplus_over, hminus_over⟩

/-- The two factors over `5` have residue field `𝔽₅`. -/
theorem chapter11_gaussian_five_residue_fields
    :
    Nonempty
        (chapter11GaussianOrder ⧸ chapter11GaussianIdealFivePlus ≃+* ZMod 5) ∧
      Nonempty
        (chapter11GaussianOrder ⧸ chapter11GaussianIdealFiveMinus ≃+* ZMod 5) := by
  let f : Polynomial ℤ := chapter11GaussianPolynomial ℤ
  have hf : f.Monic := by
    simpa [f, chapter11GaussianPolynomial] using
      (monic_X_pow_add_C (R := ℤ) (1 : ℤ) (n := 2) (by norm_num))
  have hf_ne_one : f ≠ 1 := by
    intro h
    have hdeg := congrArg Polynomial.natDegree h
    have hdeg' : f.natDegree = 2 := by
      simpa [f, chapter11GaussianPolynomial] using
        (natDegree_X_pow_add_C (R := ℤ) (n := 2) (r := (1 : ℤ)))
    have hzero : (2 : ℕ) = 0 := by simpa [hdeg'] using hdeg
    omega
  have hroot : (chapter11GaussianRoot : chapter11GaussianOrder) ^ 2 = -1 := by
    change (AdjoinRoot.root (chapter11GaussianPolynomial ℤ)) ^ 2 = -1
    have h := AdjoinRoot.eval₂_root (chapter11GaussianPolynomial ℤ)
    rw [chapter11GaussianPolynomial, eval₂_add, eval₂_X_pow, eval₂_one] at h
    exact eq_neg_of_add_eq_zero_left h
  have hprod :
      (2 + chapter11GaussianRoot) * (2 - chapter11GaussianRoot) =
        (5 : chapter11GaussianOrder) := by
    calc
      (2 + chapter11GaussianRoot) * (2 - chapter11GaussianRoot) =
          4 - chapter11GaussianRoot ^ 2 := by ring
      _ = 5 := by rw [hroot]; norm_num
  have hplus :
      Nonempty (chapter11GaussianOrder ⧸ chapter11GaussianIdealFivePlus ≃+* ZMod 5) := by
    have hroot5 : f.eval₂ (algebraMap ℤ (ZMod 5)) (3 : ZMod 5) = 0 := by
      norm_num [f, chapter11GaussianPolynomial] <;> decide
    let ePlus : chapter11GaussianOrder →+* ZMod 5 :=
      AdjoinRoot.lift (f := f) (algebraMap ℤ (ZMod 5)) (3 : ZMod 5) hroot5
    have hkerPlus : RingHom.ker ePlus = chapter11GaussianIdealFivePlus := by
      apply le_antisymm
      · intro x hx
        induction x using AdjoinRoot.induction_on with
        | ih p =>
          let r := p %ₘ f
          have hmk : AdjoinRoot.mk f r = AdjoinRoot.mk f p := by
            rw [AdjoinRoot.mk_eq_mk]
            change f ∣ (p %ₘ f) - p
            rw [modByMonic_eq_sub_mul_div]
            have hd : f ∣ -(f * (p /ₘ f)) :=
              dvd_neg.mpr (dvd_mul_right _ _)
            convert hd using 1 <;> ring
          have hrdeg : r.natDegree ≤ 1 := by
            have hlt := Polynomial.natDegree_modByMonic_lt p hf hf_ne_one
            have hfdeg : f.natDegree = 2 := by
              simpa [f, chapter11GaussianPolynomial] using
                (natDegree_X_pow_add_C (R := ℤ) (n := 2) (r := (1 : ℤ)))
            have hlt' : (p %ₘ f).natDegree < 2 := by
              rw [← hfdeg]
              exact hlt
            dsimp [r]
            omega
          obtain ⟨a, b, hr⟩ :=
            exists_eq_X_add_C_of_natDegree_le_one hrdeg
          have hrker : ePlus (AdjoinRoot.mk f r) = 0 := by
            change ePlus (AdjoinRoot.mk f p) = 0 at hx
            rw [hmk]
            exact hx
          have hrker' : ((3 * a + b : ℤ) : ZMod 5) = 0 := by
            rw [AdjoinRoot.lift_mk, hr] at hrker
            simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
              mul_assoc] using hrker
          have hab : (5 : ℤ) ∣ 3 * a + b :=
            (ZMod.intCast_zmod_eq_zero_iff_dvd (3 * a + b) 5).mp hrker'
          obtain ⟨c, hc⟩ := hab
          have hcA : 3 * (AdjoinRoot.of f) a + (AdjoinRoot.of f) b =
              5 * (AdjoinRoot.of f) c := by
            have hcA' := congrArg (AdjoinRoot.of f) hc
            simpa [map_add, map_mul] using hcA'
          have hEq :
              AdjoinRoot.mk f r =
                a * (2 + chapter11GaussianRoot) + (c - a) * (5 : chapter11GaussianOrder) := by
            rw [hr]
            simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
            change (AdjoinRoot.of f) a * AdjoinRoot.root f + (AdjoinRoot.of f) b =
              (AdjoinRoot.of f) a * (2 + AdjoinRoot.root f) +
                ((AdjoinRoot.of f) c - (AdjoinRoot.of f) a) * 5
            linear_combination hcA
          change AdjoinRoot.mk f p ∈ chapter11GaussianIdealFivePlus
          rw [← hmk, hEq]
          exact (chapter11GaussianIdealFivePlus).add_mem
            ((chapter11GaussianIdealFivePlus).mul_mem_left _
              (Ideal.mem_span_singleton_self _))
            ((chapter11GaussianIdealFivePlus).mul_mem_left _ <| by
              rw [← hprod]
              exact (chapter11GaussianIdealFivePlus).mul_mem_right _
                (Ideal.mem_span_singleton_self _))
      · rw [chapter11GaussianIdealFivePlus]
        refine Ideal.span_le.2 ?_
        rintro x (rfl : x ∈ ({2 + chapter11GaussianRoot} : Set chapter11GaussianOrder))
        change ePlus (2 + AdjoinRoot.root f) = 0
        have hrootmap : ePlus (AdjoinRoot.root f) = (3 : ZMod 5) := by
          dsimp [ePlus]
          exact AdjoinRoot.lift_root hroot5
        calc
          ePlus (2 + AdjoinRoot.root f) = ePlus 2 + ePlus (AdjoinRoot.root f) :=
            map_add ePlus 2 (AdjoinRoot.root f)
          _ = (2 : ZMod 5) + 3 := by
            rw [map_ofNat, hrootmap]
          _ = 0 := by decide
    refine ⟨(Ideal.quotEquivOfEq hkerPlus.symm).trans
      (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective ePlus))⟩
  have hminus :
      Nonempty (chapter11GaussianOrder ⧸ chapter11GaussianIdealFiveMinus ≃+* ZMod 5) := by
    have hroot5 : f.eval₂ (algebraMap ℤ (ZMod 5)) (2 : ZMod 5) = 0 := by
      norm_num [f, chapter11GaussianPolynomial] <;> decide
    let eMinus : chapter11GaussianOrder →+* ZMod 5 :=
      AdjoinRoot.lift (f := f) (algebraMap ℤ (ZMod 5)) (2 : ZMod 5) hroot5
    have hkerMinus : RingHom.ker eMinus = chapter11GaussianIdealFiveMinus := by
      apply le_antisymm
      · intro x hx
        induction x using AdjoinRoot.induction_on with
        | ih p =>
          let r := p %ₘ f
          have hmk : AdjoinRoot.mk f r = AdjoinRoot.mk f p := by
            rw [AdjoinRoot.mk_eq_mk]
            change f ∣ (p %ₘ f) - p
            rw [modByMonic_eq_sub_mul_div]
            have hd : f ∣ -(f * (p /ₘ f)) :=
              dvd_neg.mpr (dvd_mul_right _ _)
            convert hd using 1 <;> ring
          have hrdeg : r.natDegree ≤ 1 := by
            have hlt := Polynomial.natDegree_modByMonic_lt p hf hf_ne_one
            have hfdeg : f.natDegree = 2 := by
              simpa [f, chapter11GaussianPolynomial] using
                (natDegree_X_pow_add_C (R := ℤ) (n := 2) (r := (1 : ℤ)))
            have hlt' : (p %ₘ f).natDegree < 2 := by
              rw [← hfdeg]
              exact hlt
            dsimp [r]
            omega
          obtain ⟨a, b, hr⟩ :=
            exists_eq_X_add_C_of_natDegree_le_one hrdeg
          have hrker : eMinus (AdjoinRoot.mk f r) = 0 := by
            change eMinus (AdjoinRoot.mk f p) = 0 at hx
            rw [hmk]
            exact hx
          have hrker' : ((2 * a + b : ℤ) : ZMod 5) = 0 := by
            rw [AdjoinRoot.lift_mk, hr] at hrker
            simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
              mul_assoc] using hrker
          have hab : (5 : ℤ) ∣ 2 * a + b :=
            (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * a + b) 5).mp hrker'
          obtain ⟨c, hc⟩ := hab
          have hcA : 2 * (AdjoinRoot.of f) a + (AdjoinRoot.of f) b =
              5 * (AdjoinRoot.of f) c := by
            have hcA' := congrArg (AdjoinRoot.of f) hc
            simpa [map_add, map_mul] using hcA'
          have hEq :
              AdjoinRoot.mk f r =
                (-a) * (2 - chapter11GaussianRoot) + c * (5 : chapter11GaussianOrder) := by
            rw [hr]
            simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
            change (AdjoinRoot.of f) a * AdjoinRoot.root f + (AdjoinRoot.of f) b =
              (-(AdjoinRoot.of f) a) * (2 - AdjoinRoot.root f) +
                (AdjoinRoot.of f) c * 5
            linear_combination hcA
          change AdjoinRoot.mk f p ∈ chapter11GaussianIdealFiveMinus
          rw [← hmk, hEq]
          exact (chapter11GaussianIdealFiveMinus).add_mem
            ((chapter11GaussianIdealFiveMinus).mul_mem_left _
              (Ideal.mem_span_singleton_self _))
            ((chapter11GaussianIdealFiveMinus).mul_mem_left _ <| by
              rw [← hprod]
              exact (chapter11GaussianIdealFiveMinus).mul_mem_left _
                (Ideal.mem_span_singleton_self _))
      · rw [chapter11GaussianIdealFiveMinus]
        refine Ideal.span_le.2 ?_
        rintro x (rfl : x ∈ ({2 - chapter11GaussianRoot} : Set chapter11GaussianOrder))
        change eMinus (2 - AdjoinRoot.root f) = 0
        have hrootmap : eMinus (AdjoinRoot.root f) = (2 : ZMod 5) := by
          dsimp [eMinus]
          exact AdjoinRoot.lift_root hroot5
        calc
          eMinus (2 - AdjoinRoot.root f) = eMinus 2 - eMinus (AdjoinRoot.root f) :=
            map_sub eMinus 2 (AdjoinRoot.root f)
          _ = (2 : ZMod 5) - 2 := by
            rw [map_ofNat, hrootmap]
          _ = 0 := by decide
    refine ⟨(Ideal.quotEquivOfEq hkerMinus.symm).trans
      (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective eMinus))⟩
  exact ⟨hplus, hminus⟩

/-- The quotient above `3` is presented by the irreducible quadratic residue
polynomial; field and degree data are stated immediately below. -/
theorem chapter11_gaussian_three_inert_residue_degree
    :
    Nonempty
      (chapter11GaussianOrder ⧸ chapter11GaussianIdealThree ≃+*
        AdjoinRoot (X ^ 2 + 1 : Polynomial (ZMod 3))) := by
  let f : Polynomial ℤ := chapter11GaussianPolynomial ℤ
  let p : Ideal ℤ := Ideal.span {(3 : ℤ)}
  let eZ : ℤ ⧸ p ≃+* ZMod 3 := Int.quotientSpanNatEquivZMod 3
  have hmap : Ideal.map (AdjoinRoot.of f) p =
      chapter11GaussianIdealThree := by
    rw [chapter11GaussianIdealThree, Ideal.map_span]
    simp [f, p]
  have hpoly :
      (f.map (Ideal.Quotient.mk p)).map eZ.toRingHom =
        (X ^ 2 + 1 : Polynomial (ZMod 3)) := by
    ext n
    simp [f, chapter11GaussianPolynomial, eZ]
  have hassoc : Associated
      ((f.map (Ideal.Quotient.mk p)).map eZ.toRingHom)
      (X ^ 2 + 1 : Polynomial (ZMod 3)) := by
    rw [hpoly]
  let eMap : AdjoinRoot (f.map (Ideal.Quotient.mk p)) ≃+*
      AdjoinRoot (X ^ 2 + 1 : Polynomial (ZMod 3)) :=
    AdjoinRoot.mapRingEquiv eZ (f.map (Ideal.Quotient.mk p))
      (X ^ 2 + 1 : Polynomial (ZMod 3)) hassoc
  refine ⟨(Ideal.quotEquivOfEq hmap.symm).trans ?_⟩
  exact (AdjoinRoot.quotEquivQuotMap f p).toRingEquiv.trans eMap

/-- The inert quotient at `3` is a field of residue degree two. -/
theorem chapter11_gaussian_three_is_inert_field :
    IsField (AdjoinRoot (X ^ 2 + 1 : Polynomial (ZMod 3))) ∧
      Module.finrank (ZMod 3)
          (AdjoinRoot (X ^ 2 + 1 : Polynomial (ZMod 3))) = 2 ∧
    Nonempty
          (chapter11GaussianOrder ⧸ chapter11GaussianIdealThree ≃+*
          AdjoinRoot (X ^ 2 + 1 : Polynomial (ZMod 3))) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hres := chapter11_gaussian_odd_prime_three_mod_four_is_inert 3
    (by norm_num) (by norm_num)
  have hfield : IsField (AdjoinRoot (X ^ 2 + 1 : Polynomial (ZMod 3))) := by
    letI : Fact (Irreducible (X ^ 2 + 1 : Polynomial (ZMod 3))) :=
      ⟨hres.2.2⟩
    exact Field.toIsField _
  refine ⟨hfield, ?_, chapter11_gaussian_three_inert_residue_degree⟩
  calc
    Module.finrank (ZMod 3) (AdjoinRoot (X ^ 2 + 1 : Polynomial (ZMod 3))) =
        (AdjoinRoot.powerBasis hres.2.2.ne_zero).dim :=
      (AdjoinRoot.powerBasis hres.2.2.ne_zero).finrank
    _ = (X ^ 2 + 1 : Polynomial (ZMod 3)).natDegree :=
      AdjoinRoot.powerBasis_dim hres.2.2.ne_zero
    _ = 2 := hres.2.1

/-- The ideal above `2` is generated by `1+i`; its square factorization and
residue quotient are the displayed ramification data. -/
theorem chapter11_gaussian_two_ramification_data
    :
    Ideal.span {(2 : chapter11GaussianOrder)} =
        chapter11GaussianIdealTwo ^ 2 ∧
      Nonempty (chapter11GaussianOrder ⧸ chapter11GaussianIdealTwo ≃+* ZMod 2) := by
  let f : Polynomial ℤ := chapter11GaussianPolynomial ℤ
  have hf : f.Monic := by
    simpa [f, chapter11GaussianPolynomial] using
      (monic_X_pow_add_C (R := ℤ) (1 : ℤ) (n := 2) (by norm_num))
  have hf_ne_one : f ≠ 1 := by
    intro h
    have hdeg := congrArg Polynomial.natDegree h
    have hdeg' : f.natDegree = 2 := by
      simpa [f, chapter11GaussianPolynomial] using
        (natDegree_X_pow_add_C (R := ℤ) (n := 2) (r := (1 : ℤ)))
    have hzero : (2 : ℕ) = 0 := by simpa [hdeg'] using hdeg
    omega
  have hroot : (chapter11GaussianRoot : chapter11GaussianOrder) ^ 2 = -1 := by
    change (AdjoinRoot.root (chapter11GaussianPolynomial ℤ)) ^ 2 = -1
    have h := AdjoinRoot.eval₂_root (chapter11GaussianPolynomial ℤ)
    rw [chapter11GaussianPolynomial, eval₂_add, eval₂_X_pow, eval₂_one] at h
    exact eq_neg_of_add_eq_zero_left h
  have hprod2 :
      (1 + chapter11GaussianRoot) * (1 - chapter11GaussianRoot) =
        (2 : chapter11GaussianOrder) := by
    calc
      (1 + chapter11GaussianRoot) * (1 - chapter11GaussianRoot) =
          1 - chapter11GaussianRoot ^ 2 := by ring
      _ = 2 := by rw [hroot]; norm_num
  have hsqgen :
      (1 + chapter11GaussianRoot) ^ 2 =
        (2 : chapter11GaussianOrder) * chapter11GaussianRoot := by
    calc
      (1 + chapter11GaussianRoot) ^ 2 =
          1 + 2 * chapter11GaussianRoot + chapter11GaussianRoot ^ 2 := by ring
      _ = (2 : chapter11GaussianOrder) * chapter11GaussianRoot := by
        rw [hroot]
        ring
  have hback :
      (1 + chapter11GaussianRoot) ^ 2 * (-chapter11GaussianRoot) =
        (2 : chapter11GaussianOrder) := by
    calc
      (1 + chapter11GaussianRoot) ^ 2 * (-chapter11GaussianRoot) =
          (2 * chapter11GaussianRoot) * (-chapter11GaussianRoot) := by rw [hsqgen]
      _ = 2 := by
        calc
          (2 : chapter11GaussianOrder) * chapter11GaussianRoot * (-chapter11GaussianRoot) =
              -2 * chapter11GaussianRoot ^ 2 := by ring
          _ = 2 := by rw [hroot]; norm_num
  have hsq :
      Ideal.span {(2 : chapter11GaussianOrder)} =
        chapter11GaussianIdealTwo ^ 2 := by
    rw [chapter11GaussianIdealTwo, Ideal.span_singleton_pow]
    apply le_antisymm
    · refine Ideal.span_le.2 ?_
      rintro x (rfl : x ∈ ({2} : Set chapter11GaussianOrder))
      rw [← hback]
      exact (Ideal.span {(1 + chapter11GaussianRoot) ^ 2}).mul_mem_right _
        (Ideal.mem_span_singleton_self _)
    · refine Ideal.span_le.2 ?_
      rintro x (rfl : x ∈ ({(1 + chapter11GaussianRoot) ^ 2} : Set chapter11GaussianOrder))
      rw [hsqgen]
      simpa [mul_comm] using
        (Ideal.span {(2 : chapter11GaussianOrder)}).mul_mem_left
          chapter11GaussianRoot (Ideal.mem_span_singleton_self _)
  have hresidue :
      Nonempty (chapter11GaussianOrder ⧸ chapter11GaussianIdealTwo ≃+* ZMod 2) := by
    have hroot2 : f.eval₂ (algebraMap ℤ (ZMod 2)) (1 : ZMod 2) = 0 := by
      norm_num [f, chapter11GaussianPolynomial] <;> decide
    let eTwo : chapter11GaussianOrder →+* ZMod 2 :=
      AdjoinRoot.lift (f := f) (algebraMap ℤ (ZMod 2)) (1 : ZMod 2) hroot2
    have htwo_mem : (2 : chapter11GaussianOrder) ∈ chapter11GaussianIdealTwo := by
      change (2 : chapter11GaussianOrder) ∈ Ideal.span {1 + chapter11GaussianRoot}
      rw [← hprod2]
      exact (Ideal.span {1 + chapter11GaussianRoot}).mul_mem_right _
        (Ideal.mem_span_singleton_self _)
    have hkerTwo : RingHom.ker eTwo = chapter11GaussianIdealTwo := by
      apply le_antisymm
      · intro x hx
        induction x using AdjoinRoot.induction_on with
        | ih p =>
          let r := p %ₘ f
          have hmk : AdjoinRoot.mk f r = AdjoinRoot.mk f p := by
            rw [AdjoinRoot.mk_eq_mk]
            change f ∣ (p %ₘ f) - p
            rw [modByMonic_eq_sub_mul_div]
            have hd : f ∣ -(f * (p /ₘ f)) :=
              dvd_neg.mpr (dvd_mul_right _ _)
            convert hd using 1 <;> ring
          have hrdeg : r.natDegree ≤ 1 := by
            have hlt := Polynomial.natDegree_modByMonic_lt p hf hf_ne_one
            have hfdeg : f.natDegree = 2 := by
              simpa [f, chapter11GaussianPolynomial] using
                (natDegree_X_pow_add_C (R := ℤ) (n := 2) (r := (1 : ℤ)))
            have hlt' : (p %ₘ f).natDegree < 2 := by
              rw [← hfdeg]
              exact hlt
            dsimp [r]
            omega
          obtain ⟨a, b, hr⟩ :=
            exists_eq_X_add_C_of_natDegree_le_one hrdeg
          have hrker : eTwo (AdjoinRoot.mk f r) = 0 := by
            change eTwo (AdjoinRoot.mk f p) = 0 at hx
            rw [hmk]
            exact hx
          have hrker' : ((a + b : ℤ) : ZMod 2) = 0 := by
            rw [AdjoinRoot.lift_mk, hr] at hrker
            simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
              mul_assoc] using hrker
          have hab : (2 : ℤ) ∣ a + b :=
            (ZMod.intCast_zmod_eq_zero_iff_dvd (a + b) 2).mp hrker'
          obtain ⟨c, hc⟩ := hab
          have hcA : (AdjoinRoot.of f) a + (AdjoinRoot.of f) b =
              2 * (AdjoinRoot.of f) c := by
            have hcA' := congrArg (AdjoinRoot.of f) hc
            simpa [map_add, map_mul] using hcA'
          have hEq :
              AdjoinRoot.mk f r =
                a * (1 + chapter11GaussianRoot) + (c - a) * (2 : chapter11GaussianOrder) := by
            rw [hr]
            simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
            change (AdjoinRoot.of f) a * AdjoinRoot.root f + (AdjoinRoot.of f) b =
              (AdjoinRoot.of f) a * (1 + AdjoinRoot.root f) +
                ((AdjoinRoot.of f) c - (AdjoinRoot.of f) a) * 2
            linear_combination hcA
          change AdjoinRoot.mk f p ∈ chapter11GaussianIdealTwo
          rw [← hmk, hEq]
          exact (chapter11GaussianIdealTwo).add_mem
            ((chapter11GaussianIdealTwo).mul_mem_left _
              (Ideal.mem_span_singleton_self _))
            ((chapter11GaussianIdealTwo).mul_mem_left _ htwo_mem)
      · rw [chapter11GaussianIdealTwo]
        refine Ideal.span_le.2 ?_
        rintro x (rfl : x ∈ ({1 + chapter11GaussianRoot} : Set chapter11GaussianOrder))
        change eTwo (1 + AdjoinRoot.root f) = 0
        have hrootmap : eTwo (AdjoinRoot.root f) = (1 : ZMod 2) := by
          dsimp [eTwo]
          exact AdjoinRoot.lift_root hroot2
        calc
          eTwo (1 + AdjoinRoot.root f) = eTwo 1 + eTwo (AdjoinRoot.root f) :=
            map_add eTwo 1 (AdjoinRoot.root f)
          _ = (1 : ZMod 2) + 1 := by
            rw [map_one, hrootmap]
          _ = 0 := by decide
    refine ⟨(Ideal.quotEquivOfEq hkerTwo.symm).trans
      (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective eTwo))⟩
  exact ⟨hsq, hresidue⟩

/-- The prime generated by `1+i` is the unique prime over `2`, with
ramification index two. -/
theorem chapter11_gaussian_two_is_unique_totally_ramified :
    chapter11GaussianIdealTwo.IsPrime ∧
      chapter11GaussianIdealTwo.IsMaximal ∧
      chapter11GaussianIdealTwo.LiesOver
        (Ideal.span ({(2 : ℤ)} : Set ℤ)) ∧
      chapter11GaussianIdealTwo.ramificationIdx ℤ = 2 ∧
      ∀ Q : Ideal chapter11GaussianOrder,
        Q.IsPrime ∧ Q.LiesOver (Ideal.span ({(2 : ℤ)} : Set ℤ)) →
          Q = chapter11GaussianIdealTwo := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  let p : Ideal ℤ := Ideal.span ({(2 : ℤ)} : Set ℤ)
  have hdata := chapter11_gaussian_two_ramification_data
  rcases hdata with ⟨hsq, hres⟩
  obtain ⟨e⟩ := hres
  let hfield : IsField (chapter11GaussianOrder ⧸ chapter11GaussianIdealTwo) :=
    e.toMulEquiv.isField (Field.toIsField (ZMod 2))
  have hmax : chapter11GaussianIdealTwo.IsMaximal :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient
      chapter11GaussianIdealTwo).mpr hfield
  have hprime : chapter11GaussianIdealTwo.IsPrime := hmax.isPrime
  have hroot : (chapter11GaussianRoot : chapter11GaussianOrder) ^ 2 = -1 := by
    change (AdjoinRoot.root (chapter11GaussianPolynomial ℤ)) ^ 2 = -1
    have h := AdjoinRoot.eval₂_root (chapter11GaussianPolynomial ℤ)
    rw [chapter11GaussianPolynomial, eval₂_add, eval₂_X_pow, eval₂_one] at h
    exact eq_neg_of_add_eq_zero_left h
  have hprod2 :
      (1 + chapter11GaussianRoot) * (1 - chapter11GaussianRoot) =
        (2 : chapter11GaussianOrder) := by
    calc
      (1 + chapter11GaussianRoot) * (1 - chapter11GaussianRoot) =
          1 - chapter11GaussianRoot ^ 2 := by ring
      _ = 2 := by rw [hroot]; norm_num
  have htwo_mem : (2 : chapter11GaussianOrder) ∈ chapter11GaussianIdealTwo := by
    rw [chapter11GaussianIdealTwo, ← hprod2]
    exact (Ideal.span {1 + chapter11GaussianRoot}).mul_mem_right _
      (Ideal.mem_span_singleton_self _)
  have hfwd_root :
      (chapter11GaussianPolynomial ℤ).eval₂ (algebraMap ℤ GaussianInt)
          Zsqrtd.sqrtd = 0 := by
    simp [chapter11GaussianPolynomial, pow_two, Zsqrtd.dmuld]
  let fwd : chapter11GaussianOrder →+* GaussianInt :=
    AdjoinRoot.lift (f := chapter11GaussianPolynomial ℤ)
      (algebraMap ℤ GaussianInt) Zsqrtd.sqrtd hfwd_root
  let rev : GaussianInt →+* chapter11GaussianOrder :=
    Zsqrtd.lift ⟨chapter11GaussianRoot, by simpa [pow_two] using hroot⟩
  have hcomp₁ : rev.comp fwd = RingHom.id _ := by
    apply AdjoinRoot.ringHom_ext
    · ext z
      simp [fwd, rev, chapter11GaussianRoot]
    · simp [fwd, rev]
      rfl
  have hcomp₂ : fwd.comp rev = RingHom.id _ := by
    apply Zsqrtd.hom_ext
    simp [fwd, rev, chapter11GaussianRoot]
  have hfwd_bij : Function.Bijective fwd := by
    constructor
    · intro x y hxy
      have hxy' := congrArg (fun z => rev z) hxy
      simpa [← RingHom.comp_apply, hcomp₁] using hxy'
    · intro y
      refine ⟨rev y, ?_⟩
      have h := congrArg (fun φ : GaussianInt →+* GaussianInt => φ y) hcomp₂
      simpa using h
  let eGauss : chapter11GaussianOrder ≃+* GaussianInt :=
    RingEquiv.ofBijective fwd hfwd_bij
  letI : IsDomain chapter11GaussianOrder :=
    eGauss.toMulEquiv.isDomain GaussianInt
  have hrev_surj : Function.Surjective rev := by
    intro x
    refine ⟨fwd x, ?_⟩
    have h := congrArg (fun φ : chapter11GaussianOrder →+* chapter11GaussianOrder => φ x)
      hcomp₁
    simpa using h
  letI : IsPrincipalIdealRing chapter11GaussianOrder :=
    IsPrincipalIdealRing.of_surjective rev hrev_surj
  letI : IsDedekindDomain chapter11GaussianOrder := by
    infer_instance
  have hfmonic : (chapter11GaussianPolynomial ℤ).Monic := by
    simpa [chapter11GaussianPolynomial] using
      (monic_X_pow_add_C (R := ℤ) (1 : ℤ) (n := 2) (by norm_num))
  letI : Module.Finite ℤ chapter11GaussianOrder :=
    hfmonic.finite_adjoinRoot
  letI : Algebra.IsIntegral ℤ chapter11GaussianOrder := by
    infer_instance
  have hover : chapter11GaussianIdealTwo.LiesOver p := by
    constructor
    rw [Ideal.under_def]
    ext z
    constructor
    · intro hz
      rcases (Ideal.mem_span_singleton.mp hz) with ⟨c, hc⟩
      rw [hc]
      simpa [map_mul, mul_comm] using
        (chapter11GaussianIdealTwo).mul_mem_left
          (c : chapter11GaussianOrder) htwo_mem
    · intro hz
      have hq : Ideal.Quotient.mk chapter11GaussianIdealTwo
          (algebraMap ℤ chapter11GaussianOrder z) = 0 :=
        (Ideal.Quotient.eq_zero_iff_mem).2 hz
      have hq' : e (Ideal.Quotient.mk chapter11GaussianIdealTwo
          (algebraMap ℤ chapter11GaussianOrder z)) = e 0 :=
        congrArg (fun y : chapter11GaussianOrder ⧸ chapter11GaussianIdealTwo => e y) hq
      have hzmod : (z : ZMod 2) = 0 := by simpa using hq'
      rw [Ideal.mem_span_singleton]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd z 2).mp hzmod
  have hram : chapter11GaussianIdealTwo.ramificationIdx ℤ = 2 := by
    letI : chapter11GaussianIdealTwo.IsPrime := hprime
    letI : chapter11GaussianIdealTwo.LiesOver p := hover
    have hp0 : p ≠ (⊥ : Ideal ℤ) := by
      dsimp [p]
      rw [Ideal.span_singleton_eq_bot]
      norm_num
    have hof : Function.Injective (algebraMap ℤ chapter11GaussianOrder) := by
      rw [AdjoinRoot.algebraMap_eq]
      exact AdjoinRoot.of.injective_of_degree_ne_zero
        (by
          intro hzero
          have hdeg : (chapter11GaussianPolynomial ℤ).degree = (2 : WithBot ℕ) := by
            simpa [chapter11GaussianPolynomial] using
              (degree_X_pow_add_C (R := ℤ) (n := 2) (by norm_num) (1 : ℤ))
          rw [hdeg] at hzero
          norm_num at hzero)
    have hmap : p.map (algebraMap ℤ chapter11GaussianOrder) =
        chapter11GaussianIdealTwo ^ 2 := by
      dsimp [p]
      rw [Ideal.map_span]
      simpa using hsq
    have hpmap : p.map (algebraMap ℤ chapter11GaussianOrder) ≠ (⊥ : Ideal chapter11GaussianOrder) := by
      intro hbot
      apply hp0
      exact (Ideal.map_eq_bot_iff_of_injective hof).mp hbot
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity p
      chapter11GaussianIdealTwo hpmap, hmap]
    letI : FaithfulSMul ℤ chapter11GaussianOrder :=
      (faithfulSMul_iff_algebraMap_injective ℤ chapter11GaussianOrder).2 hof
    have hP0 : chapter11GaussianIdealTwo ≠ (⊥ : Ideal chapter11GaussianOrder) :=
      Ideal.ne_bot_of_liesOver_of_ne_bot hp0 chapter11GaussianIdealTwo
    exact multiplicity_pow_self_of_prime
      (Ideal.prime_of_isPrime hP0 hprime) 2
  refine ⟨hprime, hmax, hover, hram, ?_⟩
  intro Q hQ
  letI : Q.IsPrime := hQ.1
  letI : Q.LiesOver p := hQ.2
  have h2Q : (2 : chapter11GaussianOrder) ∈ Q := by
    exact (Ideal.mem_of_liesOver Q p 2).mp (Ideal.mem_span_singleton_self _)
  have hprodQ :
      (1 + chapter11GaussianRoot) * (1 - chapter11GaussianRoot) ∈ Q := by
    rw [hprod2]
    exact h2Q
  rcases hQ.1.mem_or_mem hprodQ with hgen | hone
  · have hle : chapter11GaussianIdealTwo ≤ Q := by
      rw [chapter11GaussianIdealTwo]
      exact Ideal.span_le.2 (by
        rintro x (rfl : x ∈ ({1 + chapter11GaussianRoot} :
          Set chapter11GaussianOrder))
        exact hgen)
    have hQmax : Q.IsMaximal := by
      letI : Algebra.IsIntegral ℤ chapter11GaussianOrder := by infer_instance
      apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ℤ)
        (S := chapter11GaussianOrder) Q
      change (Q.under ℤ).IsMaximal
      rw [← Q.over_def p]
      exact Int.ideal_span_isMaximal_of_prime 2
    exact (hmax.eq_of_le hQmax.ne_top hle).symm
  · have hgen : (1 + chapter11GaussianRoot : chapter11GaussianOrder) ∈ Q := by
      have heq : (1 + chapter11GaussianRoot : chapter11GaussianOrder) =
          2 - (1 - chapter11GaussianRoot) := by ring
      rw [heq]
      exact Q.sub_mem h2Q hone
    have hle : chapter11GaussianIdealTwo ≤ Q := by
      rw [chapter11GaussianIdealTwo]
      exact Ideal.span_le.2 (by
        rintro x (rfl : x ∈ ({1 + chapter11GaussianRoot} :
          Set chapter11GaussianOrder))
        exact hgen)
    have hQmax : Q.IsMaximal := by
      letI : Algebra.IsIntegral ℤ chapter11GaussianOrder := by infer_instance
      apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ℤ)
        (S := chapter11GaussianOrder) Q
      change (Q.under ℤ).IsMaximal
      rw [← Q.over_def p]
      exact Int.ideal_span_isMaximal_of_prime 2
    exact (hmax.eq_of_le hQmax.ne_top hle).symm

/-- The Gaussian examples satisfy `∑ e_i f_i = 2`. -/
theorem chapter11_gaussian_sum_e_f_is_two :
    chapter11SplitPattern 2 (fun _ : Fin 2 => 1) (fun _ : Fin 2 => 1) ∧
      chapter11InertPattern 1 (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 2) ∧
      chapter11TotallyRamifiedPattern 1 (fun _ : Fin 1 => 2) (fun _ : Fin 1 => 1) ∧
      ((1 : ℕ) * 1 + 1 * 1 = 2 ∧ 1 * 2 = 2 ∧ 2 * 1 = 2) := by
  simp [chapter11SplitPattern, chapter11InertPattern,
    chapter11TotallyRamifiedPattern]

/-- Tensoring with a split completion produces a product of two copies. -/
def chapter11TensorSplit (K L C : Type*) [CommRing K] [CommRing L] [CommRing C]
    [Algebra K L] [Algebra K C] : Prop :=
  Nonempty (L ⊗[K] C ≃+* C × C)

/-- Tensoring with a one-factor completion remains one quadratic factor. -/
def chapter11TensorOneFactor (K L C E : Type*) [CommRing K] [CommRing L] [CommRing C]
    [CommRing E] [Algebra K L] [Algebra K C] : Prop :=
  Nonempty (L ⊗[K] C ≃+* E)

/-- A one-factor tensor product whose displayed factor is a field. -/
def chapter11TensorSingleFieldFactor (K L C E : Type*) [CommRing K] [CommRing L]
    [CommRing C] [CommRing E] [Algebra K L] [Algebra K C] : Prop :=
  Nonempty (L ⊗[K] C ≃+* E) ∧ IsField E

/-- The Gaussian tensor product at `5` is split. -/
theorem chapter11_gaussian_completed_tensor_at_five [Fact (Nat.Prime 5)]
    :
    chapter11TensorSplit ℚ chapter11GaussianField ℚ_[5] := by
  have hderiv :
      (chapter11GaussianPolynomial ℤ).derivative.aeval (2 : ℤ_[5]) = (4 : ℤ_[5]) := by
    simp [chapter11GaussianPolynomial, Polynomial.aeval_def]
  have hval :
      (chapter11GaussianPolynomial ℤ).aeval (2 : ℤ_[5]) = (5 : ℤ_[5]) := by
    norm_num [chapter11GaussianPolynomial, Polynomial.aeval_def]
  have hnorm :
      ‖(chapter11GaussianPolynomial ℤ).aeval (2 : ℤ_[5])‖ <
        ‖(chapter11GaussianPolynomial ℤ).derivative.aeval (2 : ℤ_[5])‖ ^ 2 := by
    rw [hval, hderiv]
    have hfour : ‖(4 : ℤ_[5])‖ = 1 := by
      exact (PadicInt.norm_intCast_eq_one_iff).2 (by norm_num)
    change ‖(5 : ℤ_[5])‖ < ‖(4 : ℤ_[5])‖ ^ 2
    rw [hfour]
    simpa using
      (PadicInt.norm_intCast_lt_one_iff (p := 5) (z := (5 : ℤ))).2 (by norm_num)
  obtain ⟨z, hz, _, _, _⟩ :=
    hensels_lemma (p := 5) (F := chapter11GaussianPolynomial ℤ)
      (a := (2 : ℤ_[5])) hnorm
  let u : ℚ_[5] := z
  have hu : u ^ 2 = -1 := by
    have hz' := congrArg (fun x : ℤ_[5] => (x : ℚ_[5])) hz
    have hz'' : u ^ 2 + 1 = 0 := by
      simpa [u, chapter11GaussianPolynomial, Polynomial.aeval_def] using hz'
    exact eq_neg_of_add_eq_zero_left hz''
  have hu0 : u ≠ 0 := by
    intro hu0
    rw [hu0] at hu
    norm_num at hu
  let g : ℚ_[5][X] := X - C u
  let h : ℚ_[5][X] := X - C (-u)
  have hfactor : chapter11GaussianPolynomial ℚ_[5] = g * h := by
    have hcalc : (X : ℚ_[5][X]) ^ 2 + 1 = (X - C u) * (X + C u) := by
      have hcu : (C u : ℚ_[5][X]) ^ 2 = -(1 : ℚ_[5][X]) := by
        rw [← C_pow, hu]
        simp
      calc
        X ^ 2 + 1 = X ^ 2 - (C u) ^ 2 := by rw [hcu]; ring
        _ = (X - C u) * (X + C u) := by rw [sq_sub_sq]; ring
    simpa [chapter11GaussianPolynomial, g, h] using hcalc
  have hcop_elem : IsCoprime g h := by
    have h2u0 : (2 : ℚ_[5]) * u ≠ 0 := mul_ne_zero (by norm_num) hu0
    have hC2 : (C (2 : ℚ_[5]) : ℚ_[5][X]) = 2 := by
      change C ((2 : ℕ) : ℚ_[5]) = ((2 : ℕ) : ℚ_[5][X])
      exact C_eq_natCast 2
    refine ⟨-C ((2 * u)⁻¹), C ((2 * u)⁻¹), ?_⟩
    calc
      -C ((2 * u)⁻¹) * g + C ((2 * u)⁻¹) * h =
          C ((2 * u)⁻¹) * C (2 * u) := by
            simp [g, h, sub_eq_add_neg, map_neg]
            ring_nf
            rw [hC2]
      _ = 1 := by
        rw [← map_mul, inv_mul_cancel₀ h2u0]
        simp
  let I : Ideal ℚ_[5][X] := Ideal.span {g}
  let J : Ideal ℚ_[5][X] := Ideal.span {h}
  have hcop : IsCoprime I J := by
    exact Ideal.isCoprime_span_singleton_iff g h |>.2 hcop_elem
  have hprod : I * J = Ideal.span {chapter11GaussianPolynomial ℚ_[5]} := by
    dsimp [I, J]
    rw [Ideal.span_singleton_mul_span_singleton, ← hfactor]
  let ePlus : (ℚ_[5][X] ⧸ I) ≃+* ℚ_[5] := by
    simpa [I, g] using (Polynomial.quotientSpanXSubCAlgEquiv u).toRingEquiv
  let eMinus : (ℚ_[5][X] ⧸ J) ≃+* ℚ_[5] := by
    simpa [J, h] using (Polynomial.quotientSpanXSubCAlgEquiv (-u)).toRingEquiv
  let eSplit : AdjoinRoot (chapter11GaussianPolynomial ℚ_[5]) ≃+*
      ℚ_[5] × ℚ_[5] :=
    (Ideal.quotEquivOfEq hprod.symm).trans <|
      (Ideal.quotientMulEquivQuotientProd I J hcop).trans (ePlus.prodCongr eMinus)
  let q : Polynomial (ℚ_[5] ⊗[ℚ] ℚ) :=
    (chapter11GaussianPolynomial ℚ).map Algebra.TensorProduct.includeRight.toRingHom
  let eRid : ℚ_[5] ⊗[ℚ] ℚ ≃ₐ[ℚ_[5]] ℚ_[5] :=
    Algebra.TensorProduct.rid ℚ ℚ_[5] ℚ_[5]
  have hpoly :
      q.map eRid.toRingHom = chapter11GaussianPolynomial ℚ_[5] := by
    ext n
    simp [q, eRid, chapter11GaussianPolynomial]
  have hassoc : Associated (q.map eRid.toRingHom)
      (chapter11GaussianPolynomial ℚ_[5]) := by
    rw [hpoly]
  let eMap : AdjoinRoot q ≃+*
      AdjoinRoot (chapter11GaussianPolynomial ℚ_[5]) :=
    AdjoinRoot.mapRingEquiv eRid.toRingEquiv q
      (chapter11GaussianPolynomial ℚ_[5]) hassoc
  refine ⟨(Algebra.TensorProduct.comm ℚ chapter11GaussianField ℚ_[5]).toRingEquiv.trans
    ((AdjoinRoot.tensorAlgEquiv (chapter11GaussianPolynomial ℚ)
      q rfl).toRingEquiv.trans (eMap.trans eSplit))⟩

/-- The Gaussian tensor product at `3` has one quadratic algebra factor; the
field and residue-degree properties are stated immediately below. -/
theorem chapter11_gaussian_completed_tensor_at_three [Fact (Nat.Prime 3)]
    :
    chapter11TensorOneFactor ℚ chapter11GaussianField ℚ_[3]
      (AdjoinRoot (chapter11GaussianPolynomial ℚ_[3])) := by
  let q : Polynomial (ℚ_[3] ⊗[ℚ] ℚ) :=
    (chapter11GaussianPolynomial ℚ).map Algebra.TensorProduct.includeRight.toRingHom
  let eRid : ℚ_[3] ⊗[ℚ] ℚ ≃ₐ[ℚ_[3]] ℚ_[3] :=
    Algebra.TensorProduct.rid ℚ ℚ_[3] ℚ_[3]
  have hpoly :
      q.map eRid.toRingHom = chapter11GaussianPolynomial ℚ_[3] := by
    ext n
    simp [q, eRid, chapter11GaussianPolynomial]
  have hassoc : Associated (q.map eRid.toRingHom)
      (chapter11GaussianPolynomial ℚ_[3]) := by
    rw [hpoly]
  let eMap : AdjoinRoot q ≃+*
      AdjoinRoot (chapter11GaussianPolynomial ℚ_[3]) :=
    AdjoinRoot.mapRingEquiv eRid.toRingEquiv q
      (chapter11GaussianPolynomial ℚ_[3]) hassoc
  refine ⟨(Algebra.TensorProduct.comm ℚ chapter11GaussianField ℚ_[3]).toRingEquiv.trans
    ((AdjoinRoot.tensorAlgEquiv (chapter11GaussianPolynomial ℚ)
      q rfl).toRingEquiv.trans eMap)⟩

/-- The single factor at `3` is the unramified quadratic field factor. -/
theorem chapter11_gaussian_completed_tensor_at_three_is_a_field
    [Fact (Nat.Prime 3)] :
      chapter11TensorSingleFieldFactor ℚ chapter11GaussianField ℚ_[3]
      (AdjoinRoot (chapter11GaussianPolynomial ℚ_[3])) := by
  refine ⟨chapter11_gaussian_completed_tensor_at_three, ?_⟩
  let f : ℚ_[3][X] := chapter11GaussianPolynomial ℚ_[3]
  have hf : f.Monic := by
    simpa [f, chapter11GaussianPolynomial] using
      (monic_X_pow_add_C (R := ℚ_[3]) (1 : ℚ_[3]) (n := 2) (by norm_num))
  have hirr : Irreducible f := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · have hnat : f.natDegree = 2 := by
        simpa [f, chapter11GaussianPolynomial] using
          (natDegree_X_pow_add_C (R := ℚ_[3]) (n := 2) (r := (1 : ℚ_[3])))
      rw [hnat]
      norm_num
    · intro x hx
      have hx0 : x ≠ 0 := by
        intro hx0
        subst x
        norm_num [f, chapter11GaussianPolynomial] at hx
      have hx' : x ^ 2 = (-1 : ℚ_[3]) := by
        have hxsum : x ^ 2 + 1 = 0 := by
          simpa [f, chapter11GaussianPolynomial] using hx
        exact eq_neg_of_add_eq_zero_left hxsum
      have hv := congrArg (Padic.addValuation (p := 3)) hx'
      have hneg : Padic.addValuation (p := 3) (-1 : ℚ_[3]) = 0 := by
        rw [← (Padic.addValuation (p := 3)).map_neg]
        simp
      rw [AddValuation.map_pow, hneg, Padic.addValuation.apply hx0] at hv
      have hv' : 2 • x.valuation = 0 := by
        exact_mod_cast hv
      simp [two_nsmul] at hv'
      have hxval : x.valuation = 0 := by omega
      have hxnorm : ‖x‖ = 1 := by
        rw [Padic.norm_eq_zpow_neg_valuation hx0, hxval]
        norm_num
      let y : ℤ_[3] := ⟨x, by rw [hxnorm]⟩
      have hy : y ^ 2 = -1 := by
        apply Subtype.ext
        change x ^ 2 = (-1 : ℚ_[3])
        exact hx'
      have hmod := congrArg (PadicInt.toZMod (p := 3)) hy
      have hno : ¬ ∃ z : ZMod 3, z ^ 2 = -1 := by
        rintro ⟨z, hz⟩
        exact (ZMod.mod_four_ne_three_of_sq_eq_neg_one (p := 3) hz) (by norm_num)
      exact hno ⟨PadicInt.toZMod y, by simpa using hmod⟩
  letI : Fact (Irreducible f) := ⟨hirr⟩
  change IsField (AdjoinRoot f)
  exact Field.toIsField _

/-- The Gaussian tensor product at `2` has one quadratic algebra factor; the
field and ramification properties are stated immediately below. -/
theorem chapter11_gaussian_completed_tensor_at_two [Fact (Nat.Prime 2)]
    :
    chapter11TensorOneFactor ℚ chapter11GaussianField ℚ_[2]
      (AdjoinRoot (chapter11GaussianPolynomial ℚ_[2])) := by
  let q : Polynomial (ℚ_[2] ⊗[ℚ] ℚ) :=
    (chapter11GaussianPolynomial ℚ).map Algebra.TensorProduct.includeRight.toRingHom
  let eRid : ℚ_[2] ⊗[ℚ] ℚ ≃ₐ[ℚ_[2]] ℚ_[2] :=
    Algebra.TensorProduct.rid ℚ ℚ_[2] ℚ_[2]
  have hpoly :
      q.map eRid.toRingHom = chapter11GaussianPolynomial ℚ_[2] := by
    ext n
    simp [q, eRid, chapter11GaussianPolynomial]
  have hassoc : Associated (q.map eRid.toRingHom)
      (chapter11GaussianPolynomial ℚ_[2]) := by
    rw [hpoly]
  let eMap : AdjoinRoot q ≃+*
      AdjoinRoot (chapter11GaussianPolynomial ℚ_[2]) :=
    AdjoinRoot.mapRingEquiv eRid.toRingEquiv q
      (chapter11GaussianPolynomial ℚ_[2]) hassoc
  refine ⟨(Algebra.TensorProduct.comm ℚ chapter11GaussianField ℚ_[2]).toRingEquiv.trans
    ((AdjoinRoot.tensorAlgEquiv (chapter11GaussianPolynomial ℚ)
      q rfl).toRingEquiv.trans eMap)⟩

/-- The single factor at `2` is a field, but it is ramified rather than
unramified. -/
theorem chapter11_gaussian_completed_tensor_at_two_is_a_field
    [Fact (Nat.Prime 2)] :
      chapter11TensorSingleFieldFactor ℚ chapter11GaussianField ℚ_[2]
      (AdjoinRoot (chapter11GaussianPolynomial ℚ_[2])) := by
  refine ⟨chapter11_gaussian_completed_tensor_at_two, ?_⟩
  let f : ℚ_[2][X] := chapter11GaussianPolynomial ℚ_[2]
  have hf : f.Monic := by
    simpa [f, chapter11GaussianPolynomial] using
      (monic_X_pow_add_C (R := ℚ_[2]) (1 : ℚ_[2]) (n := 2) (by norm_num))
  have hirr : Irreducible f := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · have hnat : f.natDegree = 2 := by
        simpa [f, chapter11GaussianPolynomial] using
          (natDegree_X_pow_add_C (R := ℚ_[2]) (n := 2) (r := (1 : ℚ_[2])))
      rw [hnat]
      norm_num
    · intro x hx
      have hx0 : x ≠ 0 := by
        intro hx0
        subst x
        norm_num [f, chapter11GaussianPolynomial] at hx
      have hx' : x ^ 2 = (-1 : ℚ_[2]) := by
        have hxsum : x ^ 2 + 1 = 0 := by
          simpa [f, chapter11GaussianPolynomial] using hx
        exact eq_neg_of_add_eq_zero_left hxsum
      have hv := congrArg (Padic.addValuation (p := 2)) hx'
      have hneg : Padic.addValuation (p := 2) (-1 : ℚ_[2]) = 0 := by
        rw [← (Padic.addValuation (p := 2)).map_neg]
        simp
      rw [AddValuation.map_pow, hneg, Padic.addValuation.apply hx0] at hv
      have hv' : 2 • x.valuation = 0 := by
        exact_mod_cast hv
      simp [two_nsmul] at hv'
      have hxval : x.valuation = 0 := by omega
      have hxnorm : ‖x‖ = 1 := by
        rw [Padic.norm_eq_zpow_neg_valuation hx0, hxval]
        norm_num
      let y : ℤ_[2] := ⟨x, by rw [hxnorm]⟩
      have hy : y ^ 2 = -1 := by
        apply Subtype.ext
        change x ^ 2 = (-1 : ℚ_[2])
        exact hx'
      have hmod := congrArg (PadicInt.toZModPow (p := 2) 3) hy
      have hno : ¬ ∃ z : ZMod 8, z ^ 2 = -1 := by
        rintro ⟨z, hz⟩
        have hzval := congrArg ZMod.val hz
        rw [pow_two, ZMod.val_mul] at hzval
        have hzneg : (-1 : ZMod 8).val = 7 := by
          have hone : (1 : ZMod 8) ≠ 0 := one_ne_zero
          simp [ZMod.neg_val, ZMod.val_one_eq_one_mod, hone]
        rw [hzneg] at hzval
        have hzlt : z.val < 8 := z.val_lt
        interval_cases h : z.val <;> norm_num [h] at hzval
      exact hno ⟨PadicInt.toZModPow 3 y, by simpa using hmod⟩
  letI : Fact (Irreducible f) := ⟨hirr⟩
  change IsField (AdjoinRoot f)
  exact Field.toIsField _

/-! ### Equal-characteristic square covers -/

/-- The polynomial for the square cover u² = c. -/
def chapter11SquareCoverPolynomial (k : Type*) [CommRing k] (c : k) : k[X] :=
  X ^ 2 - Polynomial.C c

/-- A simple-root condition used for the Hensel splitting assertion. -/
def chapter11SimpleRootPair (C : Type*) [CommRing C] (f : C[X]) : Prop :=
  ∃ a b : C, a ≠ b ∧ f.eval a = 0 ∧ f.eval b = 0

/-- At the branch t = 0, u²=t is totally ramified. -/
theorem chapter11_square_cover_at_zero_is_totally_ramified
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (t : K) (u : L) (hrel : algebraMap K L t = u ^ 2)
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    (hext : chapter11ValuationExtensionAt K L vK vL) (ht : vK t < 1) :
    chapter11TotallyRamifiedPattern 1 (fun _ : Fin 1 => 2) (fun _ : Fin 1 => 1) ∧
      algebraMap K L t = u ^ 2 ∧ vK t < 1 := by
  exact ⟨by simp [chapter11TotallyRamifiedPattern], hrel, ht⟩

/-- At t = 1, the two simple roots u = ±1 split after Hensel lifting. -/
theorem chapter11_square_cover_at_one_hensel_splits
    (K L C : Type*) [Field K] [Field L] [Field C] [Algebra K L] [Algebra K C]
    (f : K[X]) (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hpresentation : Nonempty (L ≃ₐ[K] AdjoinRoot f))
    (hroots : chapter11SimpleRootPair C (Polynomial.map (algebraMap K C) f)) :
    chapter11TensorSplit K L C := by
  rcases hpresentation with ⟨eL⟩
  rcases hroots with ⟨a, b, hab, ha, hb⟩
  let F : C[X] := Polynomial.map (algebraMap K C) f
  have hFmonic : F.Monic := by
    exact hf.map (algebraMap K C)
  have hFdeg : F.natDegree = 2 := by
    rw [show F = Polynomial.map (algebraMap K C) f by rfl]
    rw [natDegree_map (algebraMap K C)]
    exact hdeg
  have hdiva : (X - Polynomial.C a : C[X]) ∣ F :=
    (dvd_iff_isRoot.2 ha)
  have hdivb : (X - Polynomial.C b : C[X]) ∣ F :=
    (dvd_iff_isRoot.2 hb)
  have hcop : IsCoprime (X - Polynomial.C a : C[X])
      (X - Polynomial.C b : C[X]) := by
    exact isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero.mpr hab).isUnit
  have hprod_dvd : (X - Polynomial.C a) * (X - Polynomial.C b) ∣ F :=
    hcop.mul_dvd hdiva hdivb
  have hfactor : F = (X - Polynomial.C a) * (X - Polynomial.C b) := by
    symm
    have hmonicprod :
        ((X - Polynomial.C a) * (X - Polynomial.C b) : C[X]).Monic :=
      (monic_X_sub_C a).mul (monic_X_sub_C b)
    have hdegle : F.natDegree ≤
        ((X - Polynomial.C a) * (X - Polynomial.C b) : C[X]).natDegree := by
      rw [Monic.natDegree_mul (monic_X_sub_C a) (monic_X_sub_C b)]
      simp [hFdeg]
    exact (eq_of_monic_of_dvd_of_natDegree_le hmonicprod hFmonic
      hprod_dvd hdegle).symm
  let I : Ideal C[X] := Ideal.span {X - Polynomial.C a}
  let J : Ideal C[X] := Ideal.span {X - Polynomial.C b}
  have hcopI : IsCoprime I J := by
    exact Ideal.isCoprime_span_singleton_iff _ _ |>.2 hcop
  have hprodI : I * J = Ideal.span {F} := by
    dsimp [I, J]
    rw [Ideal.span_singleton_mul_span_singleton, ← hfactor]
  let eA : (C[X] ⧸ I) ≃+* C := by
    simpa [I] using (Polynomial.quotientSpanXSubCAlgEquiv a).toRingEquiv
  let eB : (C[X] ⧸ J) ≃+* C := by
    simpa [J] using (Polynomial.quotientSpanXSubCAlgEquiv b).toRingEquiv
  let eSplit : AdjoinRoot F ≃+* C × C :=
    (Ideal.quotEquivOfEq hprodI.symm).trans <|
      (Ideal.quotientMulEquivQuotientProd I J hcopI).trans (eA.prodCongr eB)
  let q : Polynomial (C ⊗[K] K) :=
    f.map Algebra.TensorProduct.includeRight.toRingHom
  let eRid : C ⊗[K] K ≃ₐ[C] C :=
    Algebra.TensorProduct.rid K C C
  have hq : q.map eRid.toRingHom = F := by
    ext n
    simp [q, eRid, F, Algebra.smul_def]
  have hqassoc : Associated (q.map eRid.toRingHom) F := by
    rw [hq]
  let eMap : AdjoinRoot q ≃+* AdjoinRoot F :=
    AdjoinRoot.mapRingEquiv eRid.toRingEquiv q F hqassoc
  change Nonempty (L ⊗[K] C ≃+* C × C)
  let e₁ : L ⊗[K] C ≃+* C ⊗[K] AdjoinRoot f :=
    (Algebra.TensorProduct.comm K L C).toRingEquiv.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : C ≃ₐ[K] C) eL).toRingEquiv
  let e₂ : C ⊗[K] AdjoinRoot f ≃+* C × C :=
    (AdjoinRoot.tensorAlgEquiv f q rfl).toRingEquiv.trans
      (eMap.trans eSplit)
  exact ⟨e₁.trans e₂⟩

/-- At a nonsquare residue c, the square cover is one unramified quadratic branch. -/
theorem chapter11_square_cover_at_nonsquare_is_unramified_quadratic
    (k : Type*) [Field k] (c : k) (hnonsquare : ¬∃ x : k, x ^ 2 = c) :
    chapter11InertPattern 1 (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 2) ∧
      chapter11IrreducibleResiduePolynomial k
        (chapter11SquareCoverPolynomial k c) := by
  let f := chapter11SquareCoverPolynomial k c
  have hf : f.Monic := by
    simpa [f, chapter11SquareCoverPolynomial] using
      (monic_X_pow_sub_C (R := k) c (n := 2) (by norm_num))
  have hdeg : f.natDegree = 2 := by
    simpa [f, chapter11SquareCoverPolynomial] using
      (natDegree_X_pow_sub_C (R := k) (n := 2) (r := c))
  have hirr : Irreducible f := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · simpa [hdeg]
    · intro x hx
      apply hnonsquare
      refine ⟨x, ?_⟩
      have hx' : x ^ 2 - c = 0 := by
        simpa [f, chapter11SquareCoverPolynomial] using hx
      exact sub_eq_zero.mp hx'
  exact ⟨by simp [chapter11InertPattern], ⟨hf, hdeg, hirr⟩⟩

/-! ### Mixed-characteristic quadratic examples -/

/-- The separable quadratic polynomial used for the unramified 2-adic example. -/
def chapter11MixedCharacteristicUnramifiedPolynomial : ℚ[X] :=
  X ^ 2 + X + 1

/-- The Eisenstein polynomial used for the totally ramified 2-adic example. -/
def chapter11MixedCharacteristicEisensteinPolynomial : ℚ[X] :=
  X ^ 2 - 2

/-- X²+X+1 is irreducible and separable modulo 2, hence unramified quadratic. -/
theorem chapter11_mixed_characteristic_unramified_quadratic_at_two :
    chapter11InertPattern 1 (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 2) ∧
      chapter11IrreducibleResiduePolynomial (ZMod 2)
        (X ^ 2 + X + 1 : (ZMod 2)[X]) ∧
      (X ^ 2 + X + 1 : (ZMod 2)[X]).Separable := by
  have hdata : IsMonicOfDegree (X ^ 2 + X + 1 : (ZMod 2)[X]) 2 := by
    simpa using
      (isMonicOfDegree_add_add_two (R := ZMod 2) (1 : ZMod 2) (1 : ZMod 2))
  have hirr : Irreducible (X ^ 2 + X + 1 : (ZMod 2)[X]) := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · rw [hdata.natDegree_eq]
      norm_num
    · intro x hx
      have hx' : x ^ 2 + x + 1 = 0 := by
        simpa [IsRoot, eval_add, eval_X_pow, eval_one] using hx
      have hxval := congrArg ZMod.val hx'
      rw [pow_two, ZMod.val_add, ZMod.val_add, ZMod.val_mul] at hxval
      have hxlt : x.val < 2 := x.val_lt
      interval_cases h : x.val <;>
        norm_num [h, ZMod.val_one_eq_one_mod] at hxval
  refine ⟨by simp [chapter11InertPattern], ?_, ?_⟩
  · exact ⟨hdata.monic, hdata.natDegree_eq, hirr⟩
  · letI : PerfectField (ZMod 2) := PerfectField.ofFinite
    exact PerfectField.separable_of_irreducible hirr

/-- X²-2 is Eisenstein at 2, hence totally ramified quadratic. -/
theorem chapter11_mixed_characteristic_eisenstein_quadratic_at_two :
    chapter11TotallyRamifiedPattern 1 (fun _ : Fin 1 => 2) (fun _ : Fin 1 => 1) ∧
      chapter11IsEisensteinAt ℤ 2 (X ^ 2 - 2 : ℤ[X]) := by
  refine ⟨by simp [chapter11TotallyRamifiedPattern], ?_⟩
  refine ⟨by
    simpa using (monic_X_pow_sub_C (R := ℤ) (2 : ℤ) (n := 2) (by norm_num)), ?_, ?_, ?_⟩
  · norm_num [show ((X : ℤ[X]) ^ 2 - (2 : ℤ[X])).natDegree = 2 by
      simpa using (natDegree_X_pow_sub_C (R := ℤ) (n := 2) (r := (2 : ℤ)))]
  · intro i hi
    have hdeg : ((X : ℤ[X]) ^ 2 - (2 : ℤ[X])).natDegree = 2 := by
      simpa using (natDegree_X_pow_sub_C (R := ℤ) (n := 2) (r := (2 : ℤ)))
    have hi' : i = 0 ∨ i = 1 := by omega
    rcases hi' with rfl | rfl <;> norm_num [Ideal.mem_span_singleton]
  · intro h
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
    rcases h with ⟨z, hz⟩
    norm_num at hz
    omega

/-- The residue polynomial and the discriminant/constant-term test distinguish the two cases. -/
theorem chapter11_mixed_characteristic_inspect_residue_and_discriminant :
    chapter11IsEisensteinAt ℤ 2 (X ^ 2 - 2 : ℤ[X]) := by
  refine ⟨by
    simpa using (monic_X_pow_sub_C (R := ℤ) (2 : ℤ) (n := 2) (by norm_num)), ?_, ?_, ?_⟩
  · norm_num [show ((X : ℤ[X]) ^ 2 - (2 : ℤ[X])).natDegree = 2 by
      simpa using (natDegree_X_pow_sub_C (R := ℤ) (n := 2) (r := (2 : ℤ)))]
  · intro i hi
    have hdeg : ((X : ℤ[X]) ^ 2 - (2 : ℤ[X])).natDegree = 2 := by
      simpa using
        (natDegree_X_pow_sub_C (R := ℤ) (n := 2) (r := (2 : ℤ)))
    have hi'' : i < 2 := by simpa only [hdeg] using hi
    have hi' : i = 0 ∨ i = 1 := by omega
    rcases hi' with rfl | rfl <;> norm_num [Ideal.mem_span_singleton]
  · intro h
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
    rcases h with ⟨z, hz⟩
    norm_num at hz
    omega

/-! ### The repeated-factor trap -/

/-- The order generated by one chosen root. -/
def chapter11RootOrder (R L : Type*) [CommRing R] [CommRing L] [Algebra R L]
    (α : L) : Subalgebra R L :=
  Algebra.adjoin R ({α} : Set L)

/-- Whether the chosen root order already is the full integral closure. -/
def chapter11RootOrderIsIntegralClosure
    (R L : Type*) [CommRing R] [CommRing L] [Algebra R L] (α : L) : Prop :=
  chapter11RootOrder R L α = integralClosure R L

/-- A defining polynomial that has a root in the displayed algebra.  The
primitive-generation condition for an actual field presentation is kept
explicit in the theorem that uses this predicate. -/
def chapter11RootPresentsExtension
    (R L : Type*) [CommRing R] [CommRing L] [Algebra R L]
    (f : R[X]) : Prop :=
  ∃ α : L, Polynomial.eval α (Polynomial.map (algebraMap R L) f) = 0

/-- A repeated factor can reflect genuine ramification or a nonmaximal root order.

The Dedekind and finite-normalization hypotheses make the ramification index in
the first alternative an invariant of the normalized integral closure.
-/
theorem chapter11_repeated_factor_is_not_by_itself_a_ramification_proof
    (R K L : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hfinite : Module.Finite R (integralClosure R L))
    (p : Ideal R) [p.IsPrime] [p.IsMaximal]
    (hp0 : p ≠ ⊥) (f : R[X]) (hf : f.Monic)
    (hirreducible : Irreducible (Polynomial.map (algebraMap R K) f))
    (hprimitive : ∃ α : L,
      Polynomial.eval α (Polynomial.map (algebraMap R L) f) = 0 ∧
        Algebra.adjoin K ({α} : Set L) = ⊤)
    (hrep : chapter11RepeatedResidueFactor (R ⧸ p)
      (chapter11Reduction R p f)) (hdef : chapter11RootPresentsExtension R L f) :
    (∃ P : Ideal (integralClosure R L), P.IsPrime ∧ P.LiesOver p ∧
        1 < P.ramificationIdx R) ∨
      (∃ α : L,
        Polynomial.eval α (Polynomial.map (algebraMap R L) f) = 0 ∧
          Algebra.adjoin K ({α} : Set L) = ⊤ ∧
          ¬chapter11RootOrderIsIntegralClosure R L α) := by
  rcases hprimitive with ⟨α, hα, hgen⟩
  by_cases horder : chapter11RootOrderIsIntegralClosure R L α
  · left
    have hαint : IsIntegral R α := by
      refine ⟨f, hf, ?_⟩
      simpa [aeval_def] using hα
    let B := integralClosure R L
    let αB : B := ⟨α, hαint⟩
    have horder' : Algebra.adjoin R ({α} : Set L) = integralClosure R L := by
      simpa [chapter11RootOrderIsIntegralClosure, chapter11RootOrder] using horder
    have hadjoinB : Algebra.adjoin R ({αB} : Set B) = ⊤ := by
      apply Subalgebra.map_injective (f := (integralClosure R L).val)
        Subtype.val_injective
      rw [AlgHom.map_adjoin, Set.image_singleton]
      change Algebra.adjoin R ({α} : Set L) =
        Subalgebra.map (integralClosure R L).val ⊤
      rw [horder']
      rfl
    have hcon : conductor R αB = ⊤ :=
      conductor_eq_top_of_adjoin_eq_top hadjoinB
    have hcon' :
        (conductor R αB).comap (algebraMap R B) ⊔ p = ⊤ := by
      simpa [hcon]
    have hirrR : Irreducible f :=
      hf.irreducible_iff_irreducible_map_fraction_map.mpr hirreducible
    have hrootB : Polynomial.aeval αB f = 0 := by
      apply (FaithfulSMul.algebraMap_injective B L)
      simpa [aeval_def, eval₂_at_apply,
        ← IsScalarTower.algebraMap_apply R B L] using hα
    have hmin : f = minpoly R αB := by
      apply Polynomial.eq_of_monic_of_associated hf (minpoly.monic hαint)
      exact
        (Irreducible.associated_of_dvd
          (minpoly.prime_of_isIntegrallyClosed hαint).irreducible hirrR
          (minpoly.isIntegrallyClosed_dvd hαint hrootB)).symm
    letI : Module.Finite R B := hfinite
    letI : IsDedekindDomain B := integralClosure.isDedekindDomain R K L
    have hbar0 : chapter11Reduction R p f ≠ 0 := hrep.1.ne_zero
    rcases hrep with ⟨hbarMonic, _, g, hg, hgdiv⟩
    obtain ⟨q, hqmem, hgq⟩ :=
      exists_mem_normalizedFactors_of_dvd hbar0 hg.irreducible
        (dvd_trans (dvd_pow_self g (by norm_num)) hgdiv)
    have hqmem' :
        q ∈ normalizedFactors (Polynomial.map (Ideal.Quotient.mk p) (minpoly R αB)) := by
      simpa [chapter11Reduction, hmin] using hqmem
    let eKD :=
      KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
        (R := R) (S := B) (x := αB) (I := p)
        (inferInstance : p.IsMaximal) hp0 hcon' hαint
    let qsub : {d : (R ⧸ p)[X] |
        d ∈ normalizedFactors (Polynomial.map (Ideal.Quotient.mk p) (minpoly R αB))} :=
      ⟨q, hqmem'⟩
    let J : Ideal B := (eKD.symm qsub : Ideal B)
    have hJmem : J ∈ normalizedFactors (p.map (algebraMap R B)) := by
      exact (eKD.symm qsub).property
    have heq : eKD ⟨J, hJmem⟩ = qsub := by
      change eKD (eKD.symm qsub) = qsub
      exact eKD.apply_symm_apply qsub
    have hK :=
      KummerDedekind.emultiplicity_factors_map_eq_emultiplicity
        (R := R) (S := B) (I := p) (x := αB)
        (inferInstance : p.IsMaximal) hp0 hcon' hαint hJmem
    change emultiplicity J (p.map (algebraMap R B)) =
      emultiplicity (↑(eKD ⟨J, hJmem⟩))
        (Polynomial.map (Ideal.Quotient.mk p) (minpoly R αB)) at hK
    rw [heq] at hK
    have hK' :
        emultiplicity J (p.map (algebraMap R B)) =
          emultiplicity q (chapter11Reduction R p f) := by
      simpa [qsub, chapter11Reduction, hmin] using hK
    have hqprime : Prime q := prime_of_normalized_factor q hqmem
    have hqfinite : FiniteMultiplicity q (chapter11Reduction R p f) :=
      FiniteMultiplicity.of_prime_left hqprime hbar0
    have hqpow : q ^ 2 ∣ chapter11Reduction R p f := by
      exact (pow_dvd_pow_of_dvd hgq.symm.dvd 2).trans hgdiv
    have hqmult : 2 ≤ multiplicity q (chapter11Reduction R p f) :=
      hqfinite.le_multiplicity_of_pow_dvd hqpow
    have hJprime : Prime J := prime_of_normalized_factor J hJmem
    have hJfinite : FiniteMultiplicity J (p.map (algebraMap R B)) :=
      FiniteMultiplicity.of_prime_left hJprime (by
        rw [← bot_eq_zero, Ne, map_eq_bot_iff_of_injective
          (FaithfulSMul.algebraMap_injective R B)]
        exact hp0)
    have hmap0 : p.map (algebraMap R B) ≠ ⊥ := by
      rw [← bot_eq_zero, Ne, map_eq_bot_iff_of_injective
        (FaithfulSMul.algebraMap_injective R B)]
      exact hp0
    have hJIsPrime : J.IsPrime := Ideal.isPrime_of_prime hJprime
    letI : J.IsPrime := hJIsPrime
    have hJdiv : J ∣ p.map (algebraMap R B) :=
      dvd_of_mem_normalizedFactors hJmem
    letI : J.LiesOver p :=
      (Ideal.liesOver_iff_dvd_map hJIsPrime.ne_top).2 hJdiv
    have hram : J.ramificationIdx R = multiplicity q (chapter11Reduction R p f) := by
      rw [IsDedekindDomain.ramificationIdx_eq_multiplicity p J hmap0]
      calc
        multiplicity J (p.map (algebraMap R B)) =
            emultiplicity J (p.map (algebraMap R B)) :=
          hJfinite.emultiplicity_eq_multiplicity.symm
        _ = emultiplicity q (chapter11Reduction R p f) := hK'
        _ = multiplicity q (chapter11Reduction R p f) :=
          hqfinite.emultiplicity_eq_multiplicity
    have hgt : 1 < J.ramificationIdx R := by
      rw [hram]
      exact lt_of_lt_of_le (by norm_num) hqmult
    exact ⟨J, hJIsPrime, (inferInstance : J.LiesOver p), hgt⟩
  · right
    exact ⟨α, hα, hgen, horder⟩

/-- The intrinsic replacement for the polynomial test is the integral closure and its local DVRs. -/
theorem chapter11_intrinsic_integral_closure_controls_repeated_factors
    (R L : Type*) [CommRing R] [IsDomain R] [Field L] [Algebra R L]
    (p : Ideal R) (f : R[X]) (hf : f.Monic)
    (hdef : chapter11RootPresentsExtension R L f) :
    ∃ α : L,
      Polynomial.eval α (Polynomial.map (algebraMap R L) f) = 0 ∧
      IsIntegral R α ∧
      chapter11RootOrder R L α ≤ integralClosure R L := by
  rcases hdef with ⟨α, hα⟩
  refine ⟨α, hα, ?_, ?_⟩
  · exact ⟨f, hf, by simpa [aeval_def] using hα⟩
  · apply Algebra.adjoin_le
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact ⟨f, hf, by simpa [aeval_def] using hα⟩

/-! ## 11.6. Localization, residue fields, and lengths -/

/-- The localized residue ring B_P / P B_P. -/
abbrev chapter11LocalizedResidueRing (B : Type*) [CommRing B] (P : Ideal B) [P.IsPrime] : Type _ :=
  Localization.AtPrime P ⧸
    Ideal.map (algebraMap B (Localization.AtPrime P)) P

/-- The quotient B_P / P B_P identifies with the fraction field of B/P. -/
theorem chapter11_localized_residue_is_fraction_field
    (B : Type*) [CommRing B] (P : Ideal B) [P.IsPrime] :
    Nonempty
        (chapter11LocalizedResidueRing B P ≃+* FractionRing (B ⧸ P)) := by
  let hmap : Ideal.map (algebraMap B (Localization.AtPrime P)) P =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) :=
    Localization.AtPrime.map_eq_maximalIdeal
  let e₀ :
      (Localization.AtPrime P ⧸
        Ideal.map (algebraMap B (Localization.AtPrime P)) P) ≃+*
        IsLocalRing.ResidueField (Localization.AtPrime P) :=
    Ideal.quotEquivOfEq hmap
  let e : FractionRing (B ⧸ P) ≃ₐ[B ⧸ P]
      IsLocalRing.ResidueField (Localization.AtPrime P) :=
    IsFractionRing.algEquivOfAlgEquiv
      (R := B ⧸ P) (A := B ⧸ P) (K := FractionRing (B ⧸ P))
      (B := B ⧸ P)
      (L := IsLocalRing.ResidueField (Localization.AtPrime P))
      (AlgEquiv.refl : (B ⧸ P) ≃ₐ[B ⧸ P] (B ⧸ P))
  exact ⟨e₀.trans e.symm.toRingEquiv⟩

/-- Since P is maximal in the Dedekind situation, that fraction field is already B/P. -/
theorem chapter11_localized_residue_is_the_residue_field
    (B : Type*) [CommRing B] (P : Ideal B) [P.IsPrime] [P.IsMaximal] :
    IsField (B ⧸ P) ∧
      Nonempty (chapter11LocalizedResidueRing B P ≃+* (B ⧸ P)) := by
  constructor
  · exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient P).mp inferInstance
  · let hmap : Ideal.map (algebraMap B (Localization.AtPrime P)) P =
        IsLocalRing.maximalIdeal (Localization.AtPrime P) :=
      Localization.AtPrime.map_eq_maximalIdeal
    exact ⟨(Ideal.quotEquivOfEq hmap).trans
      (IsLocalization.AtPrime.equivQuotMaximalIdeal P
        (Localization.AtPrime P)).symm⟩

/-- The length valuation w_P(x) = length(B_P/xB_P). -/
def chapter11LocalLengthValue (B : Type*) [CommRing B] (P : Ideal B) [P.IsPrime] (x : B) : ℕ :=
  (Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸
        Ideal.span {algebraMap B (Localization.AtPrime P) x})).toNat

/-- The length value of a base element is its ramification index. -/
theorem chapter11_length_value_of_base_uniformizer
    (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B]
    (m : Ideal A) (π : A) (hπ : chapter11IsUniformizer A m π)
    (hm : m = IsLocalRing.maximalIdeal A) (hm0 : m ≠ ⊥)
    (P : Ideal B) [P.IsPrime] [P.IsMaximal] [P.LiesOver m] :
    chapter11LocalLengthValue B P (algebraMap A B π) = P.ramificationIdx A := by
  rw [chapter11LocalLengthValue]
  change (Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸
        Ideal.span {algebraMap B (Localization.AtPrime P) (algebraMap A B π)})).toNat = _
  rw [← IsScalarTower.algebraMap_apply A B (Localization.AtPrime P)]
  have hspan :
      Ideal.map (algebraMap A (Localization.AtPrime P)) (Ideal.span ({π} : Set A)) =
        Ideal.span ({algebraMap A (Localization.AtPrime P) π} : Set _) := by
    simpa using (Ideal.map_span (algebraMap A (Localization.AtPrime P)) ({π} : Set A))
  rw [← hspan, ← hπ]
  exact (Ideal.ramificationIdx_eq m P).symm

/-- Computing the same length over A multiplies by the residue degree. -/
theorem chapter11_length_as_base_module_is_e_f
    (A B : Type*) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B] [Algebra.IsIntegral A B] [Module.Finite A B]
    [Module.IsTorsionFree A B]
    (m : Ideal A) (π : A) (hπ : chapter11IsUniformizer A m π)
    (hm : m = IsLocalRing.maximalIdeal A) (hm0 : m ≠ ⊥)
    (P : Ideal B) [P.IsPrime] [P.IsMaximal] [P.LiesOver m] :
    (Module.length A
        (Localization.AtPrime P ⧸
          Ideal.span {algebraMap A (Localization.AtPrime P) π})).toNat =
      P.ramificationIdx A * P.inertiaDeg A := by
  let S := Localization.AtPrime P
  let M := S ⧸ Ideal.span {algebraMap A S π}
  letI : m.IsPrime := by
    rw [hm]
    exact (IsLocalRing.maximalIdeal.isMaximal A).isPrime
  letI : m.IsMaximal := by
    rw [hm]
    exact IsLocalRing.maximalIdeal.isMaximal A
  letI : P.LiesOver (IsLocalRing.maximalIdeal A) := by
    rw [← hm]
    infer_instance
  letI := Localization.AtPrime.algebraOfLiesOver m P
  letI : IsLocalHom (algebraMap A S) := by
    apply ((IsLocalRing.local_hom_TFAE (algebraMap A S)).out 4 0).mp
    change (IsLocalRing.maximalIdeal S).under A = IsLocalRing.maximalIdeal A
    rw [← Ideal.under_under (B := B), Localization.AtPrime.under_maximalIdeal]
    exact (P.over_def (IsLocalRing.maximalIdeal A)).symm
  have hspan : Ideal.span {algebraMap A S π} = m.map (algebraMap A S) := by
    change m = Ideal.span ({π} : Set A) at hπ
    rw [hπ, Ideal.map_span]
    simp
  have hres : Module.length (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField S) = P.inertiaDeg A := by
    let e : (B ⧸ P) ≃+* (IsLocalRing.ResidueField S) :=
      IsLocalization.AtPrime.equivQuotMaximalIdeal P S
    let eA : (A ⧸ IsLocalRing.maximalIdeal A) ≃+*
        (IsLocalRing.ResidueField A) := RingEquiv.refl _
    letI : Module.Finite (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ P) := inferInstance
    letI : Module.Finite (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField S) := by
      apply Module.Finite.of_equiv_equiv eA e
      apply RingHom.ext
      intro a
      exact Quotient.inductionOn' a (fun a => rfl)
    have hfin : Module.finrank (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ P) =
        Module.finrank (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField S) := by
      apply Algebra.finrank_eq_of_equiv_equiv eA e
      apply RingHom.ext
      intro a
      exact Quotient.inductionOn' a (fun a => rfl)
    rw [Module.length_eq_finrank, hfin.symm,
      (Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal A) P).symm]
  have hlength : Module.length A M =
      Module.length S M * Module.length (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField S) :=
    IsLocalRing.length_restrictScalars A S M
  have hS : (Module.length S M).toNat = P.ramificationIdx A := by
    dsimp [M]
    rw [hspan]
    exact (Ideal.ramificationIdx_eq m P).symm
  calc
    (Module.length A M).toNat =
        (Module.length S M * Module.length (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField S)).toNat := by rw [hlength]
    _ = (Module.length S M).toNat *
        (Module.length (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField S)).toNat := by simp
    _ = P.ramificationIdx A * P.inertiaDeg A := by
      rw [hS, hres]
      simp

/-- The localized length is additive on nonzero integral elements, as a
normalized discrete valuation must be. -/
theorem chapter11_length_value_is_a_discrete_valuation
    (B : Type*) [CommRing B] [IsDomain B] [IsDedekindDomain B]
    (P : Ideal B) [P.IsPrime] [P.IsMaximal]
    (x y : B) (hx : x ≠ 0) (hy : y ≠ 0) :
    chapter11LocalLengthValue B P (x * y) =
      chapter11LocalLengthValue B P x + chapter11LocalLengthValue B P y := by
  let S := Localization.AtPrime P
  have hS : Function.Injective (algebraMap B S) :=
    IsLocalization.injective S P.primeCompl_le_nonZeroDivisors
  have hyS : algebraMap B S y ≠ 0 := by
    intro hyS
    exact hy (hS (by simpa using hyS))
  have hxS : algebraMap B S x ≠ 0 := by
    intro hxS
    exact hx (hS (by simpa using hxS))
  have hxNzd : algebraMap B S x ∈ nonZeroDivisors S :=
    mem_nonZeroDivisors_of_ne_zero hxS
  have hyNzd : algebraMap B S y ∈ nonZeroDivisors S :=
    mem_nonZeroDivisors_of_ne_zero hyS
  have hxo : Ring.ord S (algebraMap B S x) ≠ ⊤ :=
    Ring.ord_ne_top hxNzd
  have hyo : Ring.ord S (algebraMap B S y) ≠ ⊤ :=
    Ring.ord_ne_top hyNzd
  have hmul := Ring.ord_mul (R := S) (a := algebraMap B S x)
    (b := algebraMap B S y) hyNzd
  change (Ring.ord S (algebraMap B S (x * y))).toNat =
    (Ring.ord S (algebraMap B S x)).toNat +
      (Ring.ord S (algebraMap B S y)).toNat
  rw [map_mul]
  have hmulNat := congrArg ENat.toNat hmul
  rw [ENat.toNat_add hxo hyo] at hmulNat
  simpa [chapter11LocalLengthValue, Ring.ord] using hmulNat

/-! ## 11.7. Norms and the sum over branches -/

/-- The field norm, defined by the determinant of multiplication. -/
def chapter11FieldNorm (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (x : L) : K :=
  Algebra.norm K x

/-- The field trace, defined by the trace of multiplication. -/
def chapter11FieldTrace (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (x : L) : K :=
  Algebra.trace K L x

/-- The residue field attached to an additive valuation. -/
abbrev chapter11AdditiveResidueField {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) :=
  IsLocalRing.ResidueField v.toValuation.valuationSubring

/-- The actual residue degree of an additive valuation extension. -/
noncomputable def chapter11AdditiveResidueDegree
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AddValuation K (WithTop ℤ)) (w : AddValuation L (WithTop ℤ))
    (h : v.IsEquiv (AddValuation.comap (algebraMap K L) w)) : ℕ := by
  letI : Valuation.HasExtension v.toValuation w.toValuation := ⟨h⟩
  exact Module.finrank (chapter11AdditiveResidueField v)
    (chapter11AdditiveResidueField w)

/-- A valuation with value group `ℤ` is normalized when it attains value one. -/
def chapter11AdditiveValuationNormalized
    {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ)) : Prop :=
  ∃ x : K, v x = (1 : WithTop ℤ)

/-- Finiteness of the residue-field extension attached to an equivalent branch. -/
def chapter11ResidueExtensionFinite
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : AddValuation K (WithTop ℤ)) (w : AddValuation L (WithTop ℤ))
    (h : v.IsEquiv (AddValuation.comap (algebraMap K L) w)) : Prop := by
  letI : Valuation.HasExtension v.toValuation w.toValuation := ⟨h⟩
  exact FiniteDimensional (chapter11AdditiveResidueField v)
    (chapter11AdditiveResidueField w)

/-- A finite indexed family containing every normalized extension of `v`
exactly once, up to equivalence. -/
def chapter11CompleteNormalizedBranchFamily
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    {ι : Type*} [Fintype ι]
  (v : AddValuation K (WithTop ℤ))
  (w : ι → AddValuation L (WithTop ℤ)) : Prop :=
  (∀ i, v.IsEquiv (AddValuation.comap (algebraMap K L) (w i))) ∧
    (∀ i, ∃ e : ℕ, 0 < e ∧
      (∀ z : K, w i (algebraMap K L z) = (e : WithTop ℤ) * v z) ∧
      chapter11AdditiveValuationNormalized (w i)) ∧
    (∀ i, ∃ h : v.IsEquiv (AddValuation.comap (algebraMap K L) (w i)),
      chapter11ResidueExtensionFinite v (w i) h) ∧
    (∀ ⦃i j⦄, (w i).IsEquiv (w j) → i = j) ∧
    ∀ w' : AddValuation L (WithTop ℤ),
      v.IsEquiv (AddValuation.comap (algebraMap K L) w') →
        ∃ i, (w i).IsEquiv w'

/-- The displayed natural numbers are the ramification scalings of the
chosen normalized branch valuations. -/
def chapter11RamificationScaling
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {ι : Type*}
    (v : AddValuation K (WithTop ℤ))
    (w : ι → AddValuation L (WithTop ℤ)) (e : ι → ℕ) : Prop :=
  ∀ i, 0 < e i ∧
    ∀ z : K, w i (algebraMap K L z) = (e i : WithTop ℤ) * v z

/-- Defectless normalized branch data for the norm formula.

The degree equality is the explicit defectless hypothesis.  The existential
scaling law records the ramification data; theorems displaying a separately
named `e` also take `chapter11RamificationScaling` so that their `e` cannot be
an unrelated numerical decomposition.
The source formula is a statement about the finite normalization of a DVR:
the finiteness hypothesis and the correspondence of the displayed branches
with the primes/localizations of that normalization are therefore part of the
interface, rather than being left implicit in the valuation family.
-/
def chapter11DefectlessNormBranchData
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {ι : Type*} [Fintype ι]
    (v : AddValuation K (WithTop ℤ))
    (w : ι → AddValuation L (WithTop ℤ)) (f : ι → ℕ) : Prop :=
  chapter11AdditiveValuationNormalized v ∧
    IsDiscreteValuationRing v.valuationSubring ∧
    chapter11NormalizationFinite v.valuationSubring L ∧
    (∀ i, ∃ P : Ideal (chapter11IntegralClosure v.valuationSubring L),
      chapter11Branch v.valuationSubring (chapter11IntegralClosure v.valuationSubring L)
        (IsLocalRing.maximalIdeal v.valuationSubring) P ∧
        Nonempty (Chapter11ValuationBranchCorrespondence
          (chapter11IntegralClosure v.valuationSubring L) L P (w i).toValuation)) ∧
    (∀ P : Ideal (chapter11IntegralClosure v.valuationSubring L),
      chapter11Branch v.valuationSubring (chapter11IntegralClosure v.valuationSubring L)
        (IsLocalRing.maximalIdeal v.valuationSubring) P →
        ∃ i, Nonempty (Chapter11ValuationBranchCorrespondence
          (chapter11IntegralClosure v.valuationSubring L) L P (w i).toValuation)) ∧
    ∃ e : ι → ℕ,
      (∀ i, 0 < e i ∧
        ∀ z : K, w i (algebraMap K L z) = (e i : WithTop ℤ) * v z) ∧
        Module.finrank K L = ∑ i, e i * f i

/-! The next two lemmas make the normalization step in the norm proof explicit.
The first identifies an exactly normalized additive valuation with the DVR
order on nonzero elements.  The second transports that order through a branch
correspondence and its localization equivalence. -/

theorem chapter11_normalized_dvr_ord
    (A K : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (v : AddValuation K (WithTop ℤ))
    (hsub : v.toValuation.valuationSubring.toSubring =
      Subring.map (algebraMap A K) (⊤ : Subring A))
    (hnorm : ∃ z : K, v z = (1 : WithTop ℤ))
    (a : A) (ha0 : a ≠ 0) :
    v (algebraMap A K a) = (Ring.ord A a).toNat := by
  classical
  have hmem (b : A) : algebraMap A K b ∈ v.toValuation.valuationSubring := by
    change algebraMap A K b ∈ v.toValuation.valuationSubring.toSubring
    rw [hsub, Subring.mem_map]
    exact ⟨b, Subring.mem_top _, rfl⟩
  have hzero_of_unit {y : K} (hy : y ≠ 0) (hy0 : 0 ≤ v y)
      (hyi : 0 ≤ v y⁻¹) : v y = 0 := by
    have hytop : v y ≠ ⊤ := (v.ne_top_iff).2 hy
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hytop
    rw [← hn] at hy0
    rw [AddValuation.map_inv, ← hn] at hyi
    have hyn : 0 ≤ n := by exact_mod_cast hy0
    have hyin : 0 ≤ -n := by exact_mod_cast hyi
    have hn0 : n = 0 := by linarith
    rw [hn0] at hn
    simpa using hn.symm
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hunit (u : Aˣ) : v (algebraMap A K (u : A)) = 0 := by
    apply hzero_of_unit (by
      exact (map_ne_zero_iff (algebraMap A K)
        (FaithfulSMul.algebraMap_injective A K)).2 u.ne_zero)
    · exact hmem (u : A)
    · have huinv := hmem ((u⁻¹ : Aˣ) : A)
      change 0 ≤ v (algebraMap A K ((u⁻¹ : Aˣ) : A)) at huinv
      rw [show algebraMap A K ((u⁻¹ : Aˣ) : A) =
        (algebraMap A K (u : A))⁻¹ by simp] at huinv
      exact huinv
  have hpi_pos : 0 < v (algebraMap A K π) := by
    by_contra hnot
    have hpi0 : v (algebraMap A K π) = 0 :=
      le_antisymm (not_lt.mp hnot) (hmem π)
    have hinv : (algebraMap A K π)⁻¹ ∈ v.toValuation.valuationSubring := by
      change 0 ≤ v ((algebraMap A K π)⁻¹)
      rw [AddValuation.map_inv, hpi0]
      exact le_rfl
    change (algebraMap A K π)⁻¹ ∈ v.toValuation.valuationSubring.toSubring at hinv
    rw [hsub, Subring.mem_map] at hinv
    obtain ⟨b, -, hb⟩ := hinv
    have hprod : π * b = 1 := by
      apply (FaithfulSMul.algebraMap_injective A K)
      rw [map_mul, map_one, hb]
      exact mul_inv_cancel₀ (by
        exact (map_ne_zero_iff (algebraMap A K)
          (FaithfulSMul.algebraMap_injective A K)).2 hπ.ne_zero)
    exact hπ.not_isUnit (by
      rw [isUnit_iff_exists_inv]
      exact ⟨b, hprod⟩)
  obtain ⟨z, hz⟩ := hnorm
  have hzmem : z ∈ v.toValuation.valuationSubring := by
    change 0 ≤ v z
    rw [hz]
    exact zero_le_one
  change z ∈ v.toValuation.valuationSubring.toSubring at hzmem
  rw [hsub, Subring.mem_map] at hzmem
  obtain ⟨b, -, hb⟩ := hzmem
  have hb0 : b ≠ 0 := by
    intro hb0
    have hz0 : z = 0 := by simpa [hb0] using hb.symm
    have hzero : v 0 = 1 := hz0 ▸ hz
    simpa using hzero
  obtain ⟨n, u, ha⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hπ
  have hpi_top : v (algebraMap A K π) ≠ ⊤ :=
    (v.ne_top_iff).2 (by
      exact (map_ne_zero_iff (algebraMap A K)
        (FaithfulSMul.algebraMap_injective A K)).2 hπ.ne_zero)
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hpi_top
  have hmpos : 0 < m := by
    have hpi_pos' : (0 : WithTop ℤ) < (m : WithTop ℤ) := by simpa [hm] using hpi_pos
    exact_mod_cast hpi_pos'
  have hnm : n * m = 1 := by
    have hv := hz
    rw [← hb, ha] at hv
    rw [map_mul, AddValuation.map_mul, map_pow, AddValuation.map_pow] at hv
    rw [hunit, ← hm] at hv
    simp only [zero_add, nsmul_eq_mul, Nat.cast_one, mul_one] at hv
    exact_mod_cast hv
  have hn1z : (n : ℤ) = 1 :=
    Int.eq_one_of_mul_eq_one_right (by exact_mod_cast (Nat.zero_le n)) hnm
  have hm1 : m = 1 :=
    Int.eq_one_of_mul_eq_one_left (by linarith [hmpos]) hnm
  have hn1 : n = 1 := by exact_mod_cast hn1z
  have hpi1 : v (algebraMap A K π) = 1 := by
    rw [← hm, hm1]
    norm_num
  obtain ⟨n, u, ha⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hπ
  calc
    v (algebraMap A K a) =
        v (algebraMap A K ((u : A) * π ^ n)) := by rw [ha]
    _ = (n : WithTop ℤ) := by
      simp only [map_mul, AddValuation.map_mul, map_pow, AddValuation.map_pow]
      rw [hunit, hpi1]
      simp [nsmul_eq_mul]
    _ = (Ring.ord A a).toNat := by
      have hord : Ring.ord A a = n := by
        rw [Ring.ord_eq_addVal]
        exact IsDiscreteValuationRing.addVal_def a u hπ n ha
      rw [hord]
      norm_num

theorem chapter11_correspondence_valuationSubring
    (B L : Type*) [CommRing B] [Field L] [Algebra B L]
    (P : Ideal B) [P.IsPrime]
    {vL : Valuation L (Multiplicative (WithTop ℤ)ᵒᵈ)}
    (c : Chapter11ValuationBranchCorrespondence B L P vL) :
    vL.valuationSubring.toSubring =
      Subring.map (vL.valuationSubring.subtype.comp c.localizationEquiv.toRingHom)
        (⊤ : Subring (Localization.AtPrime P)) := by
  apply Subring.ext
  intro z
  constructor
  · intro hz
    rcases c.localizationEquiv.surjective ⟨z, hz⟩ with ⟨s, hs⟩
    refine ⟨s, Subring.mem_top _, ?_⟩
    simpa using congrArg (fun t : vL.valuationSubring => (t : L)) hs
  · intro hz
    rcases hz with ⟨s, -, hs⟩
    change ((c.localizationEquiv s : vL.valuationSubring) : L) = z at hs
    change z ∈ vL.valuationSubring
    rw [← hs]
    exact (c.localizationEquiv s).property

theorem chapter11_local_length_eq_emultiplicity
    (B : Type*) [CommRing B] [IsDomain B] [IsDedekindDomain B]
    (P : Ideal B) [P.IsPrime] [P.IsMaximal] (hP0 : P ≠ (⊥ : Ideal B))
    (b : B) (hb0 : b ≠ 0) :
    chapter11LocalLengthValue B P b =
      (emultiplicity P (Ideal.span ({b} : Set B))).toNat := by
  let S := Localization.AtPrime P
  letI : IsDiscreteValuationRing S :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hP0 S
  have hbS : algebraMap B S b ≠ 0 := by
    exact (map_ne_zero_iff (algebraMap B S)
      (IsLocalization.injective S P.primeCompl_le_nonZeroDivisors)).2 hb0
  have hmax0 : IsLocalRing.maximalIdeal S ≠ (⊥ : Ideal S) := by
    rw [← (Localization.AtPrime.map_eq_maximalIdeal (I := P))]
    exact (Ideal.map_eq_bot_iff_of_injective
      (IsLocalization.injective S P.primeCompl_le_nonZeroDivisors)).not.mpr hP0
  have hlen : (Module.length S
      (S ⧸ Ideal.span {algebraMap B S b})).toNat =
      (Ring.ord S (algebraMap B S b)).toNat := by
    rfl
  have hadd : Ring.ord S (algebraMap B S b) =
      emultiplicity (IsLocalRing.maximalIdeal S)
        (Ideal.span ({algebraMap B S b} : Set S)) := by
    rw [Ring.ord_eq_addVal]
    have hp : Prime (Classical.choose (IsDiscreteValuationRing.exists_prime S)) :=
      Classical.choose_spec (IsDiscreteValuationRing.exists_prime S)
    rw [IsDiscreteValuationRing.addVal, multiplicity_addValuation_apply]
    rw [← Ideal.emultiplicity_eq_emultiplicity_span]
    simpa only [hp.irreducible.maximalIdeal_eq]
  have hram : Ideal.ramificationIdx' P (IsLocalRing.maximalIdeal S) = 1 := by
    apply Ideal.ramificationIdx'_eq_one_of_map_localization
      (p := P) (P := IsLocalRing.maximalIdeal S)
    · rw [← (Localization.AtPrime.map_eq_maximalIdeal (I := P))]
    · exact hmax0
    · exact (IsLocalRing.maximalIdeal S).primeCompl_le_nonZeroDivisors
    · rw [IsScalarTower.algebraMap_eq B S
          (Localization.AtPrime (IsLocalRing.maximalIdeal S)),
        ← Ideal.map_map, ← (Localization.AtPrime.map_eq_maximalIdeal
          (I := IsLocalRing.maximalIdeal S)), Localization.AtPrime.map_eq_maximalIdeal]
  have hmult := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul
    (I := Ideal.span ({b} : Set B)) (h := by simp [hb0])
    (Ideal.prime_of_isPrime hP0 (inferInstance : P.IsPrime)).irreducible
    (Ideal.prime_of_isPrime hmax0 (IsLocalRing.maximalIdeal.isMaximal S).isPrime).irreducible
    hmax0
  rw [Ideal.map_span] at hmult
  have hmult' : emultiplicity (IsLocalRing.maximalIdeal S)
      (Ideal.span ({algebraMap B S b} : Set S)) =
      (emultiplicity P (Ideal.span ({b} : Set B))) := by
    simpa [hram] using hmult
  have hmultord : Ring.ord S (algebraMap B S b) =
      emultiplicity P (Ideal.span ({b} : Set B)) := hadd.trans hmult'
  change (Module.length S
      (S ⧸ Ideal.span {algebraMap B S b})).toNat = _
  rw [hlen]
  exact congrArg ENat.toNat hmultord

/-! The relative norm order is obtained by factoring a principal ideal and
grouping its normalized factors by the prime below them. -/
open UniqueFactorizationMonoid

theorem chapter11_norm_integral_emultiplicity
    (A B K : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Field K] [Algebra A K] [IsFractionRing A K] [PerfectField K]
    [Algebra A B] [Module.Finite A B] [Module.Free A B]
    [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (m : Ideal A) [m.IsMaximal] (hm0 : m ≠ (⊥ : Ideal A))
    (y : B) (hy : y ≠ 0) :
    emultiplicity m
        (Ideal.span ({Algebra.intNorm A B y} : Set A)) =
      ∑ q : m.primesOver B,
        (q.1.inertiaDeg A : ℕ∞) *
          emultiplicity q.1 (Ideal.span ({y} : Set B)) := by
  classical
  letI : PerfectField (FractionRing A) :=
    PerfectField.of_ringEquiv (FractionRing.algEquiv A K).symm.toRingEquiv
  let F := normalizedFactors (Ideal.span ({y} : Set B))
  have hI0 : Ideal.span ({y} : Set B) ≠ (⊥ : Ideal B) := by
    simp [hy]
  have hrel : Ideal.relNorm A (Ideal.span ({y} : Set B)) =
      Ideal.span ({Algebra.intNorm A B y} : Set A) := by
    exact Ideal.relNorm_singleton A y
  have hmprime : Prime m := Ideal.prime_of_isPrime hm0
    (inferInstance : m.IsMaximal).isPrime
  have hsum_map : ∀ (s : Multiset (Ideal B)),
        emultiplicity m (Multiset.map (Ideal.relNorm A) s).prod =
          (Multiset.map (fun Q => emultiplicity m (Ideal.relNorm A Q)) s).sum := by
    intro s
    induction s using Multiset.induction_on with
    | empty =>
      change emultiplicity m (1 : Ideal A) = 0
      apply emultiplicity_eq_zero.mpr
      intro hdiv
      apply (inferInstance : m.IsMaximal).ne_top
      exact top_unique (by simpa [Ideal.one_eq_top] using (Ideal.dvd_iff_le).mp hdiv)
    | @cons Q s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
      rw [emultiplicity_mul hmprime, ih]
  have hsum_rel :
      emultiplicity m (Ideal.relNorm A (Ideal.span ({y} : Set B))) =
        ∑ Q ∈ F.toFinset,
          F.count Q • emultiplicity m (Ideal.relNorm A Q) := by
    rw [← Ideal.prod_normalizedFactors_eq_self hI0, map_multiset_prod]
    rw [hsum_map F, Finset.sum_multiset_map_count]
  have hfactor : ∀ Q : Ideal B, Q ∈ F →
      emultiplicity m (Ideal.relNorm A Q) =
        if hQ : Q.LiesOver m then (Q.inertiaDeg A : ℕ∞) else 0 := by
    intro Q hQ
    have hQ0 : Q ≠ (⊥ : Ideal B) := ne_zero_of_mem_normalizedFactors hQ
    have hQprime : Q.IsPrime :=
      Ideal.isPrime_of_prime (prime_of_normalized_factor Q hQ)
    have hQmax : Q.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hQ0 hQprime
    by_cases hQo : Q.LiesOver m
    · letI : Q.LiesOver m := hQo
      simp only [dif_pos hQo]
      rw [Ideal.relNorm_eq_pow_of_isMaximal Q m]
      have hmp : Prime m := Ideal.prime_of_isPrime hm0
        (inferInstance : m.IsMaximal).isPrime
      exact emultiplicity_pow_self_of_prime hmp (Q.inertiaDeg A)
    · simp only [dif_neg hQo]
      have hundermax : (Ideal.comap (algebraMap A B) Q).IsMaximal :=
        Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q
      letI : (Ideal.comap (algebraMap A B) Q).IsMaximal := hundermax
      letI : Q.LiesOver (Ideal.comap (algebraMap A B) Q) :=
        Ideal.over_under (A := A) (P := Q)
      rw [Ideal.relNorm_eq_pow_of_isMaximal Q (Ideal.comap (algebraMap A B) Q)]
      apply emultiplicity_eq_zero.mpr
      intro hdiv
      have hne : (Ideal.comap (algebraMap A B) Q) ≠ m := by
        intro heq
        exact hQo ⟨heq.symm⟩
      have htop : m ⊔ (Ideal.comap (algebraMap A B) Q) = ⊤ :=
        (inferInstance : m.IsMaximal).coprime_of_ne
          (inferInstance : (Ideal.comap (algebraMap A B) Q).IsMaximal) hne.symm
      have htop_pow := Ideal.sup_pow_eq_top' (n := Q.inertiaDeg A) htop
      apply (inferInstance : m.IsMaximal).ne_top
      rw [← htop_pow]
      exact (sup_eq_left.mpr ((Ideal.dvd_iff_le).mp hdiv)).symm
  rw [hrel] at hsum_rel
  let T : Finset (Ideal B) := F.toFinset.filter (fun Q => Q.LiesOver m)
  have hsum_factor :
      emultiplicity m (Ideal.span ({Algebra.intNorm A B y} : Set A)) =
        ∑ Q ∈ T, F.count Q • (Q.inertiaDeg A : ℕ∞) := by
    calc
      emultiplicity m (Ideal.span ({Algebra.intNorm A B y} : Set A)) =
          ∑ Q ∈ F.toFinset,
            F.count Q • emultiplicity m (Ideal.relNorm A Q) := hsum_rel
      _ = ∑ Q ∈ F.toFinset,
            F.count Q • (if hQ : Q.LiesOver m then
              (Q.inertiaDeg A : ℕ∞) else 0) := by
        apply Finset.sum_congr rfl
        intro Q hQ
        rw [hfactor Q (Multiset.mem_toFinset.mp hQ)]
      _ = ∑ Q ∈ T, F.count Q • (Q.inertiaDeg A : ℕ∞) := by
        rw [show T = F.toFinset.filter (fun Q => Q.LiesOver m) by rfl,
          Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro Q hQ
        by_cases hQo : Q.LiesOver m <;> simp [hQo]
  letI : Fintype (m.primesOver B) :=
    Set.Finite.fintype (Algebra.QuasiFinite.finite_primesOver m)
  have hcount_q (q : m.primesOver B) :
      emultiplicity q.1 (Ideal.span ({y} : Set B)) =
        (F.count q.1 : ℕ∞) := by
    have hq0 : q.1 ≠ (⊥ : Ideal B) :=
      Ideal.ne_bot_of_mem_primesOver hm0 q.2
    have hqprime : Prime q.1 :=
      Ideal.prime_of_isPrime hq0 (Ideal.primesOver.isPrime m q)
    rw [UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors
      hqprime.irreducible hI0]
    simp [F, normalize_eq]
  let U : Finset (m.primesOver B) :=
    Finset.univ.filter (fun q => q.1 ∈ F.toFinset)
  have hsum_q_filter :
      (∑ q : m.primesOver B,
        (q.1.inertiaDeg A : ℕ∞) *
          emultiplicity q.1 (Ideal.span ({y} : Set B))) =
        ∑ q ∈ U,
          (q.1.inertiaDeg A : ℕ∞) *
            emultiplicity q.1 (Ideal.span ({y} : Set B)) := by
    rw [show U = Finset.univ.filter (fun q : m.primesOver B =>
      q.1 ∈ F.toFinset) by rfl, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hqF : q.1 ∈ F.toFinset
    · simp [hqF]
    · have hcount0 : F.count q.1 = 0 :=
        Multiset.count_eq_zero.mpr (by
          exact fun hmem => hqF (Multiset.mem_toFinset.mpr hmem))
      rw [hcount_q q, hcount0]
      simp
  have hsum_bij :
      (∑ q ∈ U,
        (q.1.inertiaDeg A : ℕ∞) *
          emultiplicity q.1 (Ideal.span ({y} : Set B))) =
        ∑ Q ∈ T, F.count Q • (Q.inertiaDeg A : ℕ∞) := by
    apply Finset.sum_bij (s := U) (t := T)
      (fun q _ => q.1)
    · intro q hq
      exact Finset.mem_filter.mpr ⟨
        (Finset.mem_filter.mp hq).2,
        Ideal.primesOver.liesOver m q⟩
    · intro q₁ hq₁ q₂ hq₂ heq
      exact Subtype.ext heq
    · intro Q hQ
      have hQF : Q ∈ F :=
        Multiset.mem_toFinset.mp (Finset.mem_filter.mp hQ).1
      have hQo : Q.LiesOver m := Finset.mem_filter.mp hQ |>.2
      letI : Q.IsPrime := Ideal.isPrime_of_prime
        (prime_of_normalized_factor Q hQF)
      letI : Q.LiesOver m := hQo
      refine ⟨⟨Q, inferInstance, inferInstance⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Multiset.mem_toFinset.mpr hQF⟩
    · intro q hq
      rw [hcount_q q]
      simp [nsmul_eq_mul, mul_comm]
  exact hsum_factor.trans (hsum_q_filter.trans hsum_bij).symm

set_option maxHeartbeats 1000000 in
theorem chapter11_branch_value_eq_local_length
    (B L : Type*) [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Field L] [Algebra B L] [IsFractionRing B L]
    (P : Ideal B) [P.IsPrime] [P.IsMaximal] (hP0 : P ≠ (⊥ : Ideal B))
    (vL : AddValuation L (WithTop ℤ))
    (c : Chapter11ValuationBranchCorrespondence B L P vL.toValuation)
    (hnorm : ∃ z : L, vL z = (1 : WithTop ℤ))
    (b : B) (hb0 : b ≠ 0) :
    vL (algebraMap B L b) =
      (chapter11LocalLengthValue B P b : WithTop ℤ) := by
  let S := Localization.AtPrime P
  let φ : S →+* L :=
    vL.toValuation.valuationSubring.subtype.comp c.localizationEquiv.toRingHom
  letI : Algebra S L := φ.toAlgebra
  letI : IsScalarTower B S L := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro b
    change algebraMap B L b = φ (algebraMap B S b)
    dsimp [φ]
    rw [show algebraMap B S b =
      Localization.mk b ⟨1, P.primeCompl.one_mem⟩ by rfl,
      c.localizationEquiv_on_B b]
    exact (c.embedding_compatible b).symm
  letI : IsFractionRing S L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl S L
  letI : IsDiscreteValuationRing S :=
    chapter11_branch_localization_is_dvr B P hP0
  have hφ : algebraMap S L = φ := RingHom.algebraMap_toAlgebra φ
  have hsub : vL.toValuation.valuationSubring.toSubring =
      Subring.map (algebraMap S L) (⊤ : Subring S) := by
    rw [hφ]
    exact chapter11_correspondence_valuationSubring B L P c
  have hbS : algebraMap B S b ≠ 0 := by
    exact (map_ne_zero_iff (algebraMap B S)
      (IsLocalization.injective S P.primeCompl_le_nonZeroDivisors)).2 hb0
  have hv := chapter11_normalized_dvr_ord S L vL hsub hnorm
    (algebraMap B S b) hbS
  change vL (algebraMap B L b) =
      (Ring.ord S (algebraMap B S b)).toNat
  simpa only [IsScalarTower.algebraMap_apply B S L] using hv

set_option maxHeartbeats 5000000 in
/-- The norm valuation formula v(N(x)) = Σ f_i w_i(x).

The accompanying branch data include the explicit degree equality, excluding
defect and tying the ramification indices to the displayed normalized values.
-/
-- The canonical relative-ideal-norm API currently requires
-- `PerfectField (FractionRing R)` for the base Dedekind domain `R`; here the
-- normalized valuation ring has fraction field identified with `K`, so the
-- formal interface includes `[PerfectField K]`. Separability of `K → L` is
-- retained as the finite-extension hypothesis used by the field-norm step.
-- The finite-normalization and defectless-degree data above remain part of
-- the statement and are not replaced by the conclusion.
theorem chapter11_norm_valuation_formula
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [PerfectField K] [Algebra.IsSeparable K L]
    {ι : Type*} [Fintype ι] (v : AddValuation K (WithTop ℤ))
    (w : ι → AddValuation L (WithTop ℤ)) (f : ι → ℕ)
    (hbranches : chapter11CompleteNormalizedBranchFamily v w)
    (hf : ∀ i, f i = chapter11AdditiveResidueDegree v (w i) (hbranches.1 i))
    (hdefectless : chapter11DefectlessNormBranchData v w f)
    (x : L) (hx : x ≠ 0) :
    v (Algebra.norm K x) =
      ∑ i, (f i : WithTop ℤ) * w i x := by
  classical
  let A := v.valuationSubring
  let B := chapter11IntegralClosure A L
  letI : Algebra A K := by
    dsimp [A]
    infer_instance
  letI : IsFractionRing A K := inferInstance
  letI : IsDomain A := inferInstance
  letI : IsDiscreteValuationRing A := hdefectless.2.1
  letI : IsDedekindDomain A :=
    ((IsDiscreteValuationRing.TFAE A (IsDiscreteValuationRing.not_isField A)).out 0 2).mp
      hdefectless.2.1
  letI : IsIntegralClosure B A L := by
    change IsIntegralClosure (integralClosure A L) A L
    infer_instance
  letI : IsDomain B := (IsIntegralClosure.algebraMap_injective B A L).isDomain
  letI : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L
  letI : Module.IsTorsionFree A B := IsIntegralClosure.isTorsionFree A L
  letI : IsScalarTower A B L := inferInstance
  letI : Module.Finite A B := hdefectless.2.2.1
  letI : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  letI : IsDedekindDomain B := integralClosure.isDedekindDomain A K L
  letI : Module.Free A B :=
    chapter11_finite_torsion_free_over_pid_is_free A B
  have corr_subring_of {P : Ideal B} [P.IsPrime]
      {vL : Valuation L (Multiplicative (WithTop ℤ)ᵒᵈ)}
      (c : Chapter11ValuationBranchCorrespondence B L P vL) :
      vL.valuationSubring.toSubring =
        Subring.map (vL.valuationSubring.subtype.comp c.localizationEquiv.toRingHom)
          (⊤ : Subring (Localization.AtPrime P)) := by
    apply Subring.ext
    intro z
    constructor
    · intro hz
      rcases c.localizationEquiv.surjective ⟨z, hz⟩ with ⟨s, hs⟩
      refine ⟨s, Subring.mem_top _, ?_⟩
      simpa using congrArg (fun t : vL.valuationSubring => (t : L)) hs
    · intro hz
      rcases hz with ⟨s, -, hs⟩
      change ((c.localizationEquiv s : vL.valuationSubring) : L) = z at hs
      change z ∈ vL.valuationSubring
      rw [← hs]
      exact (c.localizationEquiv s).property
  let m : Ideal A := IsLocalRing.maximalIdeal A
  letI : m.IsMaximal := by
    dsimp [m]
    exact IsLocalRing.maximalIdeal.isMaximal A
  letI : m.IsPrime := (inferInstance : m.IsMaximal).isPrime
  have hm0 : m ≠ (⊥ : Ideal A) := by
    dsimp [m]
    exact IsDiscreteValuationRing.not_a_field A
  have hiP : ∀ i, ∃ P : Ideal B,
      chapter11Branch A B m P ∧
        Nonempty (Chapter11ValuationBranchCorrespondence
          B L P (w i).toValuation) := by
    simpa [m] using hdefectless.2.2.2.1
  have hPall : ∀ P : Ideal B,
      chapter11Branch A B m P →
        ∃ i, Nonempty (Chapter11ValuationBranchCorrespondence
          B L P (w i).toValuation) := by
    simpa [m] using hdefectless.2.2.2.2.1
  let P : ι → Ideal B := fun i => Classical.choose (hiP i)
  have hPbranch (i : ι) : chapter11Branch A B m (P i) := by
    exact (Classical.choose_spec (hiP i)).1
  letI (i : ι) : (P i).IsPrime := (hPbranch i).1
  letI (i : ι) : (P i).IsMaximal := (hPbranch i).2.1
  letI (i : ι) : (P i).LiesOver m := (hPbranch i).2.2
  let c : ∀ i : ι,
      Chapter11ValuationBranchCorrespondence B L (P i) (w i).toValuation :=
    fun i => Classical.choice (Classical.choose_spec (hiP i)).2
  let g : ι → m.primesOver B := fun i =>
    ⟨P i, (hPbranch i).1, (hPbranch i).2.2⟩
  have hlocal_on_base (i : ι) (b : B) :
      (c i).localizationEquiv (algebraMap B (Localization.AtPrime (P i)) b) =
        (c i).embedding b := by
    letI : (P i).IsPrime := (hPbranch i).1
    rw [show algebraMap B (Localization.AtPrime (P i)) b =
      Localization.mk b ⟨1, (P i).primeCompl.one_mem⟩ by rfl,
      (c i).localizationEquiv_on_B]
  have hval_eq_of_same_branch
      {Q : Ideal B} [Q.IsPrime]
      {v₁ v₂ : Valuation L (Multiplicative (WithTop ℤ)ᵒᵈ)}
      (c₁ : Chapter11ValuationBranchCorrespondence B L Q v₁)
      (c₂ : Chapter11ValuationBranchCorrespondence B L Q v₂) :
      v₁.IsEquiv v₂ := by
    have hφ :
        v₁.valuationSubring.subtype.comp c₁.localizationEquiv.toRingHom =
          v₂.valuationSubring.subtype.comp c₂.localizationEquiv.toRingHom := by
      apply IsLocalization.ringHom_ext Q.primeCompl
      apply RingHom.ext
      intro b
      change ((c₁.localizationEquiv
          (algebraMap B (Localization.AtPrime Q) b) : v₁.valuationSubring) : L) =
        ((c₂.localizationEquiv
          (algebraMap B (Localization.AtPrime Q) b) : v₂.valuationSubring) : L)
      rw [show algebraMap B (Localization.AtPrime Q) b =
          Localization.mk b ⟨1, Q.primeCompl.one_mem⟩ by rfl,
        c₁.localizationEquiv_on_B, c₂.localizationEquiv_on_B]
      exact (c₁.embedding_compatible b).trans (c₂.embedding_compatible b).symm
    apply (Valuation.isEquiv_iff_valuationSubring v₁ v₂).2
    apply ValuationSubring.ext
    intro z
    change z ∈ v₁.valuationSubring.toSubring ↔
      z ∈ v₂.valuationSubring.toSubring
    rw [chapter11_correspondence_valuationSubring B L Q c₁,
      chapter11_correspondence_valuationSubring B L Q c₂, hφ]
  have hg : Function.Injective g := by
    intro i j hij
    have hPij : P i = P j := congrArg Subtype.val hij
    have hval : (w i).IsEquiv (w j) := by
      let cj : Chapter11ValuationBranchCorrespondence B L (P i) (w j).toValuation :=
        cast (by rw [hPij]) (c j)
      exact hval_eq_of_same_branch (c i) cj
    exact hbranches.2.2.2.1 hval
  letI : Fintype (m.primesOver B) :=
    Set.Finite.fintype (Algebra.QuasiFinite.finite_primesOver m)
  have hg_surj : Function.Surjective g := by
    intro q
    have hqbranch : chapter11Branch A B m q.1 := by
      exact ⟨inferInstance, inferInstance, inferInstance⟩
    obtain ⟨i, hi⟩ := hPall q.1 hqbranch
    rcases hi with ⟨cq⟩
    have hemb : (c i).embedding = cq.embedding := by
      apply RingHom.ext
      intro b
      apply Subtype.ext
      exact (c i).embedding_compatible b |>.trans (cq.embedding_compatible b).symm
    have hPiq : P i = q.1 := by
      calc
        P i = (IsLocalRing.maximalIdeal (w i).toValuation.valuationSubring).comap
            (c i).embedding := (c i).center
        _ = (IsLocalRing.maximalIdeal (w i).toValuation.valuationSubring).comap
            cq.embedding := by rw [hemb]
        _ = q.1 := cq.center.symm
    refine ⟨i, ?_⟩
    apply Subtype.ext
    exact hPiq
  have hinertia (i : ι) :
      (g i).1.inertiaDeg A =
        chapter11AdditiveResidueDegree v (w i) (hbranches.1 i) := by
    letI : (P i).IsPrime := (hPbranch i).1
    letI : (P i).IsMaximal := (hPbranch i).2.1
    letI : (P i).LiesOver m := (hPbranch i).2.2
    change (P i).inertiaDeg A =
      chapter11AdditiveResidueDegree v (w i) (hbranches.1 i)
    rw [Ideal.inertiaDeg_eq_of_isMaximal m (P i)]
    letI : Valuation.HasExtension v.toValuation (w i).toValuation :=
      ⟨hbranches.1 i⟩
    letI : Algebra A (w i).toValuation.valuationSubring :=
      Valuation.HasExtension.instAlgebra_valuationSubring
        v.toValuation (w i).toValuation
    let S := Localization.AtPrime (P i)
    let eQ : B ⧸ P i ≃+* IsLocalRing.ResidueField S :=
      IsLocalization.AtPrime.equivQuotMaximalIdeal (P i) S
    let eRes : IsLocalRing.ResidueField S ≃+*
        chapter11AdditiveResidueField (w i) :=
      IsLocalRing.ResidueField.mapEquiv (c i).localizationEquiv
    let eTarget : B ⧸ P i ≃+* chapter11AdditiveResidueField (w i) :=
      eQ.trans eRes
    letI : m.IsTwoSided := by
      dsimp [m]
      infer_instance
    let eBase : A ⧸ m ≃+* chapter11AdditiveResidueField v := by
      change A ⧸ m ≃+* A ⧸ IsLocalRing.maximalIdeal A
      rfl
    change Module.finrank (A ⧸ m) (B ⧸ P i) =
      Module.finrank (chapter11AdditiveResidueField v)
        (chapter11AdditiveResidueField (w i))
    apply Algebra.finrank_eq_of_equiv_equiv eBase eTarget
    apply RingHom.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hemb :
        (c i).embedding (algebraMap A B a) =
          algebraMap A (w i).toValuation.valuationSubring a := by
      apply Subtype.ext
      calc
        ((c i).embedding (algebraMap A B a) : L) =
            algebraMap B L (algebraMap A B a) :=
          (c i).embedding_compatible _
        _ = algebraMap A L a := by
          rw [← IsScalarTower.algebraMap_apply A B L]
        _ = algebraMap K L (a : K) := by
          rw [IsScalarTower.algebraMap_apply A K L]
          rfl
        _ = (algebraMap A (w i).toValuation.valuationSubring a : L) := by
          symm
          exact Valuation.HasExtension.coe_algebraMap_valuationSubring_eq
            v.toValuation (w i).toValuation a
    calc
      algebraMap (chapter11AdditiveResidueField v)
          (chapter11AdditiveResidueField (w i))
          (eBase (Ideal.Quotient.mk m a)) =
      algebraMap (chapter11AdditiveResidueField v)
            (chapter11AdditiveResidueField (w i))
            (IsLocalRing.residue A a) := by
        rfl
      _ = IsLocalRing.residue (w i).toValuation.valuationSubring
          (algebraMap A (w i).toValuation.valuationSubring a) := by
        exact Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap
          v.toValuation (w i).toValuation a
      _ = IsLocalRing.residue (w i).toValuation.valuationSubring
          ((c i).embedding (algebraMap A B a)) := by rw [hemb]
      _ = eTarget (Ideal.Quotient.mk (P i) (algebraMap A B a)) := by
        change IsLocalRing.residue (w i).toValuation.valuationSubring
            ((c i).embedding (algebraMap A B a)) =
          IsLocalRing.residue (w i).toValuation.valuationSubring
            ((c i).localizationEquiv
              (algebraMap B (Localization.AtPrime (P i))
                (algebraMap A B a)))
        rw [hlocal_on_base]
  have hvalue (i : ι) (b : B) (hb : b ≠ 0) :
      w i (algebraMap B L b) =
        ((emultiplicity (g i).1 (Ideal.span ({b} : Set B))).toNat :
          WithTop ℤ) := by
    letI : (P i).IsPrime := (hPbranch i).1
    letI : (P i).IsMaximal := (hPbranch i).2.1
    letI : (P i).LiesOver m := (hPbranch i).2.2
    have hP0 : P i ≠ (⊥ : Ideal B) :=
      Ideal.ne_bot_of_liesOver_of_ne_bot hm0 (P i)
    have hnorm : ∃ z : L, w i z = (1 : WithTop ℤ) := by
      rcases hbranches.2.1 i with ⟨e, he, hscale, hnorm⟩
      exact hnorm
    have hv := chapter11_branch_value_eq_local_length B L (P i) hP0
      (w i) (c i) hnorm b hb
    have he := chapter11_local_length_eq_emultiplicity B (P i) hP0 b hb
    rw [he] at hv
    simpa [g] using hv
  have hbase_subring :
      v.toValuation.valuationSubring.toSubring =
        Subring.map (algebraMap A K) (⊤ : Subring A) := by
    change A.toSubring = Subring.map (algebraMap A K) (⊤ : Subring A)
    apply Subring.ext
    intro z
    constructor
    · intro hz
      rw [Subring.mem_map]
      exact ⟨⟨z, hz⟩, Subring.mem_top _, rfl⟩
    · intro hz
      rcases Subring.mem_map.mp hz with ⟨a, -, ha⟩
      change z ∈ A.toSubring
      rw [← ha]
      exact a.property
  have hintegral (b : B) (hb : b ≠ 0) :
      v (Algebra.norm K (algebraMap B L b)) =
        ∑ i, (f i : WithTop ℤ) * w i (algebraMap B L b) := by
    have hbL : algebraMap B L b ≠ 0 :=
      (map_ne_zero_iff (algebraMap B L)
        (IsIntegralClosure.algebraMap_injective B A L)).2 hb
    have hI0 : Ideal.span ({b} : Set B) ≠ (⊥ : Ideal B) := by
      simp [hb]
    let F := normalizedFactors (Ideal.span ({b} : Set B))
    have hqem (q : m.primesOver B) :
        emultiplicity q.1 (Ideal.span ({b} : Set B)) =
          (F.count q.1 : ℕ∞) := by
      have hq0 : q.1 ≠ (⊥ : Ideal B) :=
        Ideal.ne_bot_of_mem_primesOver hm0 q.2
      have hqprime : Prime q.1 :=
        Ideal.prime_of_isPrime hq0 (Ideal.primesOver.isPrime m q)
      rw [UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors
        hqprime.irreducible hI0]
      simp [F, normalize_eq]
    have hqtop (q : m.primesOver B) :
        emultiplicity q.1 (Ideal.span ({b} : Set B)) ≠ (⊤ : ℕ∞) := by
      rw [hqem q]
      simp
    have hsum_top : ∀ q : m.primesOver B,
        (q.1.inertiaDeg A : ℕ∞) *
            emultiplicity q.1 (Ideal.span ({b} : Set B)) ≠ (⊤ : ℕ∞) := by
      intro q
      apply WithTop.mul_ne_top
      · exact ENat.natCast_ne_top _
      · exact hqtop q
    have htoNat :
        (∑ q : m.primesOver B,
          (q.1.inertiaDeg A : ℕ∞) *
            emultiplicity q.1 (Ideal.span ({b} : Set B))).toNat =
          ∑ q : m.primesOver B,
            ((q.1.inertiaDeg A : ℕ∞) *
              emultiplicity q.1 (Ideal.span ({b} : Set B))).toNat := by
      simpa using (ENat.toNat_sum (s := (Finset.univ : Finset (m.primesOver B)))
        (fun q hq => hsum_top q))
    have hcast :
        ((∑ q : m.primesOver B,
          (q.1.inertiaDeg A : ℕ∞) *
            emultiplicity q.1 (Ideal.span ({b} : Set B))).toNat : WithTop ℤ) =
          ∑ q : m.primesOver B,
            (q.1.inertiaDeg A : WithTop ℤ) *
              ((emultiplicity q.1 (Ideal.span ({b} : Set B))).toNat :
                WithTop ℤ) := by
      rw [htoNat]
      simp only [ENat.toNat_mul, ENat.toNat_natCast]
      rw [Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro q hq
      norm_cast
    have hbase_em (a : A) (ha : a ≠ 0) :
        v (algebraMap A K a) =
          ((emultiplicity m (Ideal.span ({a} : Set A))).toNat : WithTop ℤ) := by
      have hord := chapter11_normalized_dvr_ord A K v hbase_subring
        hdefectless.1 a ha
      have hordem : Ring.ord A a =
          emultiplicity m (Ideal.span ({a} : Set A)) := by
        rw [Ring.ord_eq_addVal]
        have hp : Prime (Classical.choose (IsDiscreteValuationRing.exists_prime A)) :=
          Classical.choose_spec (IsDiscreteValuationRing.exists_prime A)
        rw [IsDiscreteValuationRing.addVal, multiplicity_addValuation_apply]
        rw [← Ideal.emultiplicity_eq_emultiplicity_span]
        simpa [m, hp.irreducible.maximalIdeal_eq]
      calc
        v (algebraMap A K a) = ((Ring.ord A a).toNat : WithTop ℤ) := hord
        _ = ((emultiplicity m (Ideal.span ({a} : Set A))).toNat : WithTop ℤ) := by
          rw [hordem]
    have hnormEm :
        emultiplicity m (Ideal.span ({Algebra.intNorm A B b} : Set A)) =
          ∑ q : m.primesOver B,
            (q.1.inertiaDeg A : ℕ∞) *
              emultiplicity q.1 (Ideal.span ({b} : Set B)) := by
      exact chapter11_norm_integral_emultiplicity A B K m hm0 b
        hb
    have hintnorm : Algebra.intNorm A B b ≠ 0 := by
      intro hzero
      have hnzero : Algebra.norm K (algebraMap B L b) ≠ 0 :=
        Algebra.norm_ne_zero_iff.mpr hbL
      apply hnzero
      rw [← Algebra.algebraMap_intNorm (A := A) (B := B) (K := K) (L := L) b,
        hzero, map_zero]
    have hnorm_value :
        v (Algebra.norm K (algebraMap B L b)) =
          ((∑ q : m.primesOver B,
            (q.1.inertiaDeg A : ℕ∞) *
              emultiplicity q.1 (Ideal.span ({b} : Set B))).toNat :
            WithTop ℤ) := by
      calc
        v (Algebra.norm K (algebraMap B L b)) =
            v (algebraMap A K (Algebra.intNorm A B b)) := by
              rw [Algebra.algebraMap_intNorm (L := L) b]
        _ = ((emultiplicity m
            (Ideal.span ({Algebra.intNorm A B b} : Set A))).toNat :
              WithTop ℤ) := hbase_em (Algebra.intNorm A B b) hintnorm
        _ = ((∑ q : m.primesOver B,
            (q.1.inertiaDeg A : ℕ∞) *
              emultiplicity q.1 (Ideal.span ({b} : Set B))).toNat :
            WithTop ℤ) := by rw [hnormEm]
    have hsum_branch :
        (∑ i, (f i : WithTop ℤ) * w i (algebraMap B L b)) =
          ∑ q : m.primesOver B,
            (q.1.inertiaDeg A : WithTop ℤ) *
              ((emultiplicity q.1 (Ideal.span ({b} : Set B))).toNat :
                WithTop ℤ) := by
      let e : ι ≃ m.primesOver B := Equiv.ofBijective g ⟨hg, hg_surj⟩
      calc
        (∑ i, (f i : WithTop ℤ) * w i (algebraMap B L b)) =
            ∑ i, (g i).1.inertiaDeg A *
              ((emultiplicity (g i).1 (Ideal.span ({b} : Set B))).toNat :
                WithTop ℤ) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hfi : f i = (g i).1.inertiaDeg A := by
            exact (hf i).trans (hinertia i).symm
          rw [hfi, hvalue i b hb]
        _ = ∑ q : m.primesOver B,
            (q.1.inertiaDeg A : WithTop ℤ) *
              ((emultiplicity q.1 (Ideal.span ({b} : Set B))).toNat :
                WithTop ℤ) := by
          exact Fintype.sum_equiv e _ _ (fun i => rfl)
    calc
      v (Algebra.norm K (algebraMap B L b)) =
          ((∑ q : m.primesOver B,
            (q.1.inertiaDeg A : ℕ∞) *
              emultiplicity q.1 (Ideal.span ({b} : Set B))).toNat :
            WithTop ℤ) := hnorm_value
      _ = ∑ q : m.primesOver B,
          (q.1.inertiaDeg A : WithTop ℤ) *
            ((emultiplicity q.1 (Ideal.span ({b} : Set B))).toNat :
              WithTop ℤ) := hcast
      _ = ∑ i, (f i : WithTop ℤ) * w i (algebraMap B L b) := hsum_branch.symm
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective B x
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have ha0 : a ≠ 0 := by
    intro ha
    apply hx
    simp [ha]
  have haL : algebraMap B L a ≠ 0 :=
    (map_ne_zero_iff (algebraMap B L)
      (IsIntegralClosure.algebraMap_injective B A L)).2 ha0
  have hbL : algebraMap B L b ≠ 0 :=
    (map_ne_zero_iff (algebraMap B L)
      (IsIntegralClosure.algebraMap_injective B A L)).2 hb0
  have hnorm_div :
      v (Algebra.norm K (algebraMap B L a / algebraMap B L b)) =
        v (Algebra.norm K (algebraMap B L a)) -
          v (Algebra.norm K (algebraMap B L b)) := by
    rw [div_eq_mul_inv, map_mul, Algebra.norm_inv,
      AddValuation.map_mul, AddValuation.map_inv]
    simp only [sub_eq_add_neg]
  have hbranch_div :
      (∑ i, (f i : WithTop ℤ) *
          w i (algebraMap B L a / algebraMap B L b)) =
        (∑ i, (f i : WithTop ℤ) * w i (algebraMap B L a)) -
          ∑ i, (f i : WithTop ℤ) * w i (algebraMap B L b) := by
    calc
      (∑ i, (f i : WithTop ℤ) *
          w i (algebraMap B L a / algebraMap B L b)) =
          ∑ i, (f i : WithTop ℤ) *
            (w i (algebraMap B L a) - w i (algebraMap B L b)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [AddValuation.map_div]
      _ = (∑ i, (f i : WithTop ℤ) * w i (algebraMap B L a)) -
          ∑ i, (f i : WithTop ℤ) * w i (algebraMap B L b) := by
        let aa : ι → ℤ := fun i =>
          Classical.choose
            (WithTop.ne_top_iff_exists.mp ((w i).ne_top_iff.mpr haL))
        let bb : ι → ℤ := fun i =>
          Classical.choose
            (WithTop.ne_top_iff_exists.mp ((w i).ne_top_iff.mpr hbL))
        have haa (i : ι) :
            (aa i : WithTop ℤ) = w i (algebraMap B L a) := by
          dsimp [aa]
          exact Classical.choose_spec
            (WithTop.ne_top_iff_exists.mp ((w i).ne_top_iff.mpr haL))
        have hbb (i : ι) :
            (bb i : WithTop ℤ) = w i (algebraMap B L b) := by
          dsimp [bb]
          exact Classical.choose_spec
            (WithTop.ne_top_iff_exists.mp ((w i).ne_top_iff.mpr hbL))
        calc
          (∑ i, (f i : WithTop ℤ) *
              (w i (algebraMap B L a) - w i (algebraMap B L b))) =
              ∑ i, ((f i : WithTop ℤ) *
                ((aa i : WithTop ℤ) - (bb i : WithTop ℤ))) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [haa i, hbb i]
          _ = (∑ i, (f i : WithTop ℤ) * (aa i : WithTop ℤ)) -
              ∑ i, (f i : WithTop ℤ) * (bb i : WithTop ℤ) := by
            have hsum_coe (u : ι → ℤ) :
                (↑(∑ i, (f i : ℤ) * u i) : WithTop ℤ) =
                  ∑ i, (f i : WithTop ℤ) * (u i : WithTop ℤ) := by
              calc
                (↑(∑ i, (f i : ℤ) * u i) : WithTop ℤ) =
                    ∑ i, (↑((f i : ℤ) * u i) : WithTop ℤ) := by
                  rw [WithTop.coe_sum]
                _ = ∑ i, (f i : WithTop ℤ) * (u i : WithTop ℤ) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  change (↑((f i : ℤ) * u i) : WithTop ℤ) =
                    (↑(f i : ℤ) : WithTop ℤ) * (u i : WithTop ℤ)
                  norm_cast
            have hsubterm (i : ι) :
                (f i : WithTop ℤ) *
                    ((aa i : WithTop ℤ) - (bb i : WithTop ℤ)) =
                  (↑((f i : ℤ) * (aa i - bb i)) : WithTop ℤ) := by
              change (↑(f i : ℤ) : WithTop ℤ) *
                    ((aa i : WithTop ℤ) - (bb i : WithTop ℤ)) =
                  (↑((f i : ℤ) * (aa i - bb i)) : WithTop ℤ)
              norm_cast
            have hcast :
                (∑ i, (f i : WithTop ℤ) *
                    ((aa i : WithTop ℤ) - (bb i : WithTop ℤ))) =
                  (↑(∑ i, (f i : ℤ) * (aa i - bb i)) : WithTop ℤ) := by
              calc
                (∑ i, (f i : WithTop ℤ) *
                    ((aa i : WithTop ℤ) - (bb i : WithTop ℤ))) =
                    ∑ i, (↑((f i : ℤ) * (aa i - bb i)) : WithTop ℤ) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  exact hsubterm i
                _ = (↑(∑ i, (f i : ℤ) * (aa i - bb i)) : WithTop ℤ) := by
                  rw [WithTop.coe_sum]
            calc
              (∑ i, (f i : WithTop ℤ) *
                  ((aa i : WithTop ℤ) - (bb i : WithTop ℤ))) =
                  (↑(∑ i, (f i : ℤ) * (aa i - bb i)) : WithTop ℤ) := hcast
              _ = (↑((∑ i, (f i : ℤ) * aa i) -
                  ∑ i, (f i : ℤ) * bb i) : WithTop ℤ) := by
                congr 1
                rw [← Finset.sum_sub_distrib]
                apply Finset.sum_congr rfl
                intro i hi
                rw [mul_sub]
              _ = (∑ i, (f i : WithTop ℤ) * (aa i : WithTop ℤ)) -
                  ∑ i, (f i : WithTop ℤ) * (bb i : WithTop ℤ) := by
                calc
                  (↑((∑ i, (f i : ℤ) * aa i) -
                    ∑ i, (f i : ℤ) * bb i) : WithTop ℤ) =
                      (↑(∑ i, (f i : ℤ) * aa i) : WithTop ℤ) -
                        (↑(∑ i, (f i : ℤ) * bb i) : WithTop ℤ) :=
                    rfl
                  _ = (∑ i, (f i : WithTop ℤ) * (aa i : WithTop ℤ)) -
                      ∑ i, (f i : WithTop ℤ) * (bb i : WithTop ℤ) := by
                    rw [hsum_coe, hsum_coe]
          _ = (∑ i, (f i : WithTop ℤ) * w i (algebraMap B L a)) -
              ∑ i, (f i : WithTop ℤ) * w i (algebraMap B L b) := by
            simp_rw [haa, hbb]
  calc
    v (Algebra.norm K (algebraMap B L a / algebraMap B L b)) =
        v (Algebra.norm K (algebraMap B L a)) -
          v (Algebra.norm K (algebraMap B L b)) := hnorm_div
    _ = (∑ i, (f i : WithTop ℤ) * w i (algebraMap B L a)) -
          ∑ i, (f i : WithTop ℤ) * w i (algebraMap B L b) := by
      rw [hintegral a ha0, hintegral b hb0]
    _ = ∑ i, (f i : WithTop ℤ) *
          w i (algebraMap B L a / algebraMap B L b) := hbranch_div.symm
 

/-- For a base uniformizer, the branch values are e_i, so the norm sees Σ e_i f_i. -/
theorem chapter11_norm_of_uniformizer
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [PerfectField K] [Algebra.IsSeparable K L]
    {ι : Type*} [Fintype ι] (v : AddValuation K (WithTop ℤ))
    (w : ι → AddValuation L (WithTop ℤ)) (e f : ι → ℕ) (π : K)
    (hbranches : chapter11CompleteNormalizedBranchFamily v w)
    (hf : ∀ i, f i = chapter11AdditiveResidueDegree v (w i) (hbranches.1 i))
    (hdefectless : chapter11DefectlessNormBranchData v w f)
    (hscaling : chapter11RamificationScaling v w e)
    (hπ : ∀ i, w i (algebraMap K L π) = (e i : WithTop ℤ))
    (hπ_ne : π ≠ 0) :
    v (Algebra.norm K (algebraMap K L π)) =
      ∑ i, (f i : WithTop ℤ) * (e i : WithTop ℤ) := by
  have hnorm := chapter11_norm_valuation_formula K L v w f hbranches hf hdefectless
    (algebraMap K L π)
      ((map_ne_zero_iff (algebraMap K L)
        (FaithfulSMul.algebraMap_injective K L)).2 hπ_ne)
  simpa [hπ] using hnorm

/-- The same formula extends from integral elements to fractions by division. -/
theorem chapter11_norm_valuation_on_fractions
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (v : AddValuation K (WithTop ℤ)) (x y : L) (hx : x ≠ 0) (hy : y ≠ 0) :
    v (Algebra.norm K (x / y)) =
      v (Algebra.norm K x) - v (Algebra.norm K y) := by
  rw [div_eq_mul_inv, map_mul, Algebra.norm_inv,
    AddValuation.map_mul, AddValuation.map_inv]
  simp only [sub_eq_add_neg]

/-- The uniformizer computation agrees with the degree formula. -/
theorem chapter11_norm_uniformizer_consistency
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [PerfectField K] [Algebra.IsSeparable K L]
    {ι : Type*} [Fintype ι] (v : AddValuation K (WithTop ℤ))
    (w : ι → AddValuation L (WithTop ℤ)) (e f : ι → ℕ) (π : K)
    (hbranches : chapter11CompleteNormalizedBranchFamily v w)
    (hf : ∀ i, f i = chapter11AdditiveResidueDegree v (w i) (hbranches.1 i))
    (hdefectless : chapter11DefectlessNormBranchData v w f)
    (hscaling : chapter11RamificationScaling v w e)
    (hπ : ∀ i, w i (algebraMap K L π) = (e i : WithTop ℤ))
    (hdegree : Module.finrank K L = ∑ i, e i * f i) :
    v (Algebra.norm K (algebraMap K L π)) =
      (Module.finrank K L : WithTop ℤ) := by
  have hι : Nonempty ι := by
    by_contra hι
    letI : IsEmpty ι := ⟨fun i => hι ⟨i⟩⟩
    have hzero : Module.finrank K L = 0 := by simpa using hdegree
    exact (Nat.ne_of_gt Module.finrank_pos) hzero
  let i : ι := Classical.choice hι
  have hπ_ne : π ≠ 0 := by
    intro hzero
    have hi := hπ i
    rw [hzero, map_zero] at hi
    simpa using hi
  calc
    v (Algebra.norm K (algebraMap K L π)) =
        ∑ i, (f i : WithTop ℤ) * (e i : WithTop ℤ) :=
      chapter11_norm_of_uniformizer K L v w e f π hbranches hf hdefectless hscaling hπ
        hπ_ne
    _ = ((∑ i, e i * f i : ℕ) : WithTop ℤ) := by
      rw [Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro i hi
      norm_cast
      exact mul_comm _ _
    _ = (Module.finrank K L : WithTop ℤ) := by
      rw [← hdegree]

/-! ## 11.8. Trace, norm, and boundedness -/

/-- The characteristic polynomial of multiplication by an element of a finite module. -/
def chapter11CharacteristicPolynomial
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Free A B] [Module.Finite A B] (x : B) : A[X] :=
  LinearMap.charpoly (Algebra.lmul A B x)

/-- The characteristic polynomial annihilates the multiplication operator. -/
def chapter11RootOfPolynomial
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (f : A[X]) (x : B) : Prop :=
  Polynomial.eval x (Polynomial.map (algebraMap A B) f) = 0

/-- Cayley--Hamilton gives an integral equation for every element of a finite module. -/
theorem chapter11_characteristic_polynomial_annihilates
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Free A B] [Module.Finite A B] (x : B) :
    chapter11RootOfPolynomial A B (chapter11CharacteristicPolynomial A B x) x := by
  change Polynomial.eval x
    (Polynomial.map (algebraMap A B)
      (LinearMap.charpoly (Algebra.lmul A B x))) = 0
  simpa [aeval_def] using (Algebra.aeval_self_charpoly_lmul (R := A) (M := B) x)

/-- Trace and norm of an integral element remain in the base ring. -/
theorem chapter11_integral_trace_and_norm_stay_integral
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [IsIntegrallyClosed A] [IsDedekindDomain B] [Module.Finite A B]
    [Module.Free A B] [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (x : B) :
    Algebra.trace K L (algebraMap B L x) ∈ Set.range (algebraMap A K) ∧
      Algebra.norm K (algebraMap B L x) ∈ Set.range (algebraMap A K) := by
  refine ⟨?_, ?_⟩
  · refine ⟨Algebra.intTrace A B x, ?_⟩
    exact Algebra.algebraMap_intTrace (L := L) x
  · refine ⟨Algebra.intNorm A B x, ?_⟩
    exact Algebra.algebraMap_intNorm (L := L) x

/-- The trace pairing on the field extension. -/
def chapter11TracePairing (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (x y : L) : K :=
  Algebra.trace K L (x * y)

/-- Separability makes the trace pairing nondegenerate. -/
theorem chapter11_separable_trace_pairing_nondegenerate
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] :
    Function.Injective (fun x : L => fun y : L => chapter11TracePairing K L x y) := by
  intro x₁ x₂ h
  have hz : ∀ y : L, Algebra.trace K L ((x₁ - x₂) * y) = 0 := by
    intro y
    have hy : Algebra.trace K L (x₁ * y) = Algebra.trace K L (x₂ * y) := by
      simpa [chapter11TracePairing] using congrFun h y
    rw [sub_mul, map_sub]
    exact sub_eq_zero.mpr hy
  have hzero : x₁ - x₂ = 0 := by
    exact (traceForm_nondegenerate K L).1 (x₁ - x₂) (by
      intro y
      simpa only [Algebra.traceForm_apply] using hz y)
  exact sub_eq_zero.mp hzero

/-- A common denominator embeds the integral trace pairing into the A-dual. -/
theorem chapter11_trace_pairing_has_common_denominator
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing A K]
    [IsFractionRing B L] [IsIntegralClosure B A L]
    [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [Module.Finite A B] (x : B) :
    ∃ d : A, d ≠ 0 ∧
      ∃ φ : B →ₗ[A] A, ∀ y : B,
        algebraMap A K (φ y) =
        algebraMap A K d *
            Algebra.trace K L (algebraMap B L x * algebraMap B L y) := by
  let hB : B →ₗ[A] L :=
    (IsScalarTower.toAlgHom A B L).toLinearMap.comp (LinearMap.mulLeft A x)
  let h : B →ₗ[A] K :=
    (Algebra.trace K L).restrictScalars A |>.comp hB
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := B)
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (M := A⁰)
    (fun i : Fin n => h (s i))
  have hgen : ∀ i : Fin n, h (s i) * algebraMap A K (d : A) ∈
      LinearMap.range (Algebra.linearMap A K) := by
    intro i
    rcases hd i with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    simpa [Algebra.smul_def, mul_comm] using ha
  let hscl : B →ₗ[A] K := (d : A) • h
  have hscl_gen : ∀ i : Fin n, hscl (s i) ∈ LinearMap.range (Algebra.linearMap A K) := by
    intro i
    simpa [hscl, LinearMap.smul_apply, Algebra.smul_def, mul_comm] using hgen i
  let q : Submodule A B :=
    (LinearMap.range (Algebra.linearMap A K)).comap hscl
  have hqgen : ∀ i : Fin n, s i ∈ q := by
    intro i
    exact hscl_gen i
  have hqtop : q = ⊤ := by
    apply top_unique
    rw [← hs]
    exact Submodule.span_le.2 (fun z hz => by
      rcases hz with ⟨i, rfl⟩
      exact hqgen i)
  have hmem : ∀ y : B, hscl y ∈ LinearMap.range (Algebra.linearMap A K) := by
    intro y
    have : y ∈ q := by rw [hqtop]; exact Submodule.mem_top
    exact this
  let e : A ≃ₗ[A] LinearMap.range (Algebra.linearMap A K) :=
    LinearEquiv.ofBijective (Algebra.linearMap A K).rangeRestrict
      ⟨(Algebra.linearMap A K).injective_rangeRestrict_iff.mpr
          (IsFractionRing.injective A K),
        (Algebra.linearMap A K).surjective_rangeRestrict⟩
  let φ : B →ₗ[A] A :=
    e.symm.toLinearMap.comp (hscl.codRestrict _ hmem)
  have hφ (y : B) : algebraMap A K (φ y) = hscl y := by
    change algebraMap A K (φ y) = (hscl y : K)
    rw [show algebraMap A K (φ y) = (e (φ y) : K) by rfl]
    simp [φ, e]
  have hdne : (d : A) ≠ 0 := by
    exact mem_nonZeroDivisors_iff_ne_zero.mp d.prop
  refine ⟨d, hdne, φ, ?_⟩
  intro y
  rw [hφ]
  change (d : A) • h y = _
  simp only [Algebra.smul_def]
  change algebraMap A K (d : A) *
      Algebra.trace K L (algebraMap B L (x * y)) = _
  rw [map_mul]

/-- Mathlib's different ideal is the inverse of the trace dual. -/
def chapter11DifferentIdeal
    (A B : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [IsIntegrallyClosed A] [IsDedekindDomain B]
    [Module.IsTorsionFree A B] : Ideal B :=
  differentIdeal A B

/-- The quadratic equation T² - Tr(x) T + N(x) proves integrality from trace and norm. -/
def chapter11QuadraticTraceNormRelation
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (x : B) (tr n : A) : Prop :=
  x ^ 2 - algebraMap A B tr * x + algebraMap A B n = 0

/-- A displayed monic quadratic relation is sufficient for integrality. -/
theorem chapter11_quadratic_trace_norm_implies_integral
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (x : B) (tr n : A)
    (h : chapter11QuadraticTraceNormRelation A B x tr n) :
    IsIntegral A x := by
  have hdeg : (C (-tr) * X + C n : A[X]).degree < (2 : ℕ) := by
    exact (degree_add_le _ _).trans_lt (max_lt
      ((degree_C_mul_X_le _).trans_lt (by norm_num))
      (degree_C_le.trans_lt (by norm_num)))
  have hmonic : (X ^ 2 + (C (-tr) * X + C n) : A[X]).Monic :=
    monic_X_pow_add hdeg
  refine ⟨X ^ 2 - C tr * X + C n, ?_, ?_⟩
  · simpa only [map_neg, sub_eq_add_neg, neg_mul, add_assoc] using hmonic
  · simpa only [chapter11QuadraticTraceNormRelation, eval₂_sub, eval₂_add,
      eval₂_mul, eval₂_X, eval₂_X_pow, eval₂_C] using h

/-- For a genuine quadratic field extension, integral trace and norm values
give the monic characteristic equation and hence integrality. -/
theorem chapter11_quadratic_field_trace_norm_implies_integral
    (A K L : Type*) [CommRing A] [IsDomain A] [Field K] [Field L]
    [Algebra A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsFractionRing A K] [FiniteDimensional K L]
    (hdegree : Module.finrank K L = 2) (x : L)
    (htrace : ∃ tr : A, algebraMap A K tr = Algebra.trace K L x)
    (hnorm : ∃ n : A, algebraMap A K n = Algebra.norm K x) :
    IsIntegral A x := by
  classical
  rcases htrace with ⟨tr, htr⟩
  rcases hnorm with ⟨n, hn⟩
  let b := Module.Free.chooseBasis K L
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex K L) = 2 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex]
    exact hdegree
  let m := LinearMap.toMatrix b b (Algebra.lmul K L x)
  have hchar : LinearMap.charpoly (Algebra.lmul K L x) =
      X ^ 2 - C (Algebra.trace K L x) * X + C (Algebra.norm K x) := by
    rw [← LinearMap.charpoly_toMatrix (Algebra.lmul K L x) b]
    change m.charpoly = _
    rw [Matrix.charpoly_of_card_eq_two (M := m) hcard]
    have htr' : m.trace = Algebra.trace K L x := by
      simpa [m, Algebra.trace_apply] using
        (LinearMap.trace_eq_matrix_trace K b (Algebra.lmul K L x)).symm
    have hdet' : m.det = Algebra.norm K x := by
      simpa [m, Algebra.norm_apply] using
        (LinearMap.det_toMatrix b (Algebra.lmul K L x))
    rw [htr', hdet']
  have hroot := Algebra.aeval_self_charpoly_lmul (R := K) (M := L) x
  rw [hchar] at hroot
  have hrel : chapter11QuadraticTraceNormRelation A L x tr n := by
    rw [chapter11QuadraticTraceNormRelation]
    rw [← htr, ← hn] at hroot
    simpa [aeval_def, IsScalarTower.algebraMap_apply A K L] using hroot
  exact chapter11_quadratic_trace_norm_implies_integral A L x tr n hrel

/-- Higher-degree characteristic polynomials have intermediate coefficients. -/
def chapter11MonicCoefficientProfile (A : Type*) [CommRing A] (n : ℕ) :=
  Fin (n + 1) → A

/-- The endpoint coefficient data do not determine a monic coefficient profile. -/
theorem chapter11_higher_degree_trace_norm_omit_intermediate_coefficients
    (A : Type*) [CommRing A] [Nontrivial A] (n : ℕ) (hn : 3 ≤ n) :
    ∃ c d : chapter11MonicCoefficientProfile A n,
      c 0 = d 0 ∧ c ⟨n, Nat.lt_succ_self n⟩ =
        d ⟨n, Nat.lt_succ_self n⟩ ∧ c ≠ d := by
  classical
  let j : Fin (n + 1) := ⟨1, by omega⟩
  let c : chapter11MonicCoefficientProfile A n := fun _ => 0
  let d : chapter11MonicCoefficientProfile A n := fun i => if i = j then 1 else 0
  have hj0 : j ≠ (0 : Fin (n + 1)) := by
    intro h
    have := congrArg Fin.val h
    simp [j] at this
  have hjn : j ≠ (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) := by
    intro h
    have := congrArg Fin.val h
    simp [j] at this
    omega
  have hj0' : (0 : Fin (n + 1)) ≠ j := Ne.symm hj0
  have hjn' : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) ≠ j := Ne.symm hjn
  refine ⟨c, d, ?_, ?_, ?_⟩
  · simp [c, d, hj0']
  · simp [c, d, hjn']
  · intro hcd
    have hcdj := congrFun hcd j
    have h01 : (0 : A) = 1 := by simpa [c, d] using hcdj
    exact zero_ne_one h01

/-- In degree at least three, distinct monic polynomials can have the same
constant and leading coefficients.  These are the intermediate coefficients
which trace and norm do not record. -/
theorem chapter11_monic_polynomials_with_same_endpoint_coefficients
    (A : Type*) [CommRing A] [Nontrivial A] (n : ℕ) (hn : 3 ≤ n) :
    ∃ f g : A[X], f.Monic ∧ g.Monic ∧ f.natDegree = n ∧ g.natDegree = n ∧
      f.coeff 0 = g.coeff 0 ∧ f.coeff n = g.coeff n ∧ f ≠ g := by
  let f : A[X] := X ^ n
  let g : A[X] := X ^ n + X
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hng : g.Monic := by
    apply monic_X_pow_add
    have hlt : (1 : WithBot ℕ) < n := by
      exact_mod_cast (show 1 < n by omega)
    simpa using hlt
  have hfn : f.natDegree = n := by simp [f]
  have hgn : g.natDegree = n := by
    change (X ^ n + X : A[X]).natDegree = n
    have hdeg : (X : A[X]).natDegree < (X ^ n : A[X]).natDegree := by
      simpa using (show 1 < n by omega)
    rw [natDegree_add_eq_left_of_natDegree_lt hdeg]
    simp
  have hneq : f ≠ g := by
    intro hfg
    have hc := congrArg (fun q : A[X] => q.coeff 1) hfg
    simp [f, g, show n ≠ 1 by omega] at hc
  refine ⟨f, g, by simp [f], hng, hfn, hgn, ?_, ?_, hneq⟩
  · simp [f, g, hnpos]
  · rw [coeff_add, coeff_X_pow, coeff_X]
    simp [show 1 ≠ n by omega]

/-- Thus endpoint trace/norm data alone do not determine the intermediate
coefficients in higher degree. -/
theorem chapter11_trace_norm_are_insufficient_in_higher_degree
    (A : Type*) [CommRing A] [Nontrivial A] (n : ℕ) (hn : 3 ≤ n) :
    ∃ c d : chapter11MonicCoefficientProfile A n, c ≠ d ∧ c 0 = d 0 := by
  rcases chapter11_higher_degree_trace_norm_omit_intermediate_coefficients A n hn with
    ⟨c, d, h0, _, hcd⟩
  exact ⟨c, d, hcd, h0⟩

/-! ## 11.9. Towers of extensions -/

/-- Ramification indices multiply in a tower, using Mathlib's intrinsic definition. -/
theorem chapter11_ramification_indices_multiply_in_towers
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (p : Ideal R) (q : Ideal S) (r : Ideal T)
    [p.IsPrime] [q.IsPrime] [r.IsPrime]
    [q.LiesOver p] [r.LiesOver q] [Module.Flat S T] :
    r.ramificationIdx R = q.ramificationIdx R * r.ramificationIdx S := by
  exact Ideal.ramificationIdx_tower q r

/-- Inertia degrees multiply in a tower. -/
theorem chapter11_inertia_degrees_multiply_in_towers
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (p : Ideal R) (q : Ideal S) (r : Ideal T)
    [p.IsPrime] [q.IsPrime] [r.IsPrime]
    [q.LiesOver p] [r.LiesOver q] :
    r.inertiaDeg R = q.inertiaDeg R * r.inertiaDeg S := by
  exact Ideal.inertiaDeg_tower q r

/-- The degree of a field tower is multiplicative. -/
theorem chapter11_field_degrees_multiply_in_towers
    (K L M : Type*) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] :
    Module.finrank K M = Module.finrank K L * Module.finrank L M := by
  exact (Module.finrank_mul_finrank K L M).symm

/-- Combining a first-stage local degree formula with field-tower
multiplicativity. -/
theorem chapter11_branch_tree_recovers_tower_degree
    (K L M : Type*) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M]
    {ι : Type*} [Fintype ι] (e₁ f₁ : ι → ℕ)
    (hL : Module.finrank K L = ∑ i, e₁ i * f₁ i) :
    Module.finrank K M =
      (∑ i, e₁ i * f₁ i) * Module.finrank L M := by
  calc
    Module.finrank K M = Module.finrank K L * Module.finrank L M :=
      (Module.finrank_mul_finrank K L M).symm
    _ = (∑ i, e₁ i * f₁ i) * Module.finrank L M := by rw [hL]

/-- A two-level branch-tree degree computation is the product of the two
stage sums. -/
theorem chapter11_two_stage_branch_tree_recovers_tower_degree
    (K L M : Type*) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e₁ f₁ : ι → ℕ) (e₂ f₂ : κ → ℕ)
    (hL : Module.finrank K L = ∑ i, e₁ i * f₁ i)
    (hM : Module.finrank L M = ∑ j, e₂ j * f₂ j) :
    Module.finrank K M =
      (∑ i, e₁ i * f₁ i) * (∑ j, e₂ j * f₂ j) := by
  calc
    Module.finrank K M = Module.finrank K L * Module.finrank L M :=
      (Module.finrank_mul_finrank K L M).symm
    _ = (∑ i, e₁ i * f₁ i) * (∑ j, e₂ j * f₂ j) := by rw [hL, hM]

/-- A specified chain of primes composes to a prime above the bottom prime.
The Henselian/non-Henselian distinction concerns whether such a chain is
canonical; the transitivity assertion itself does not require a Henselian
hypothesis. -/
theorem chapter11_extensions_transmit_liesOver_along_branch_chain
    (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (p : Ideal R) (q : Ideal S) (r : Ideal T) :
    q.LiesOver p ∧ r.LiesOver q → r.LiesOver p := by
  rintro ⟨hqp, hrq⟩
  letI : q.LiesOver p := hqp
  letI : r.LiesOver q := hrq
  exact Ideal.LiesOver.trans r q p

/-- The tame/wild distinction is the later refinement of the e-data. -/
def chapter11TameAtResidueCharacteristic (e p : ℕ) : Prop :=
  p = 0 ∨ Nat.Coprime e p

/-- Ramification is wild when the residue characteristic divides the ramification index. -/
def chapter11WildAtResidueCharacteristic (e p : ℕ) : Prop :=
  p ≠ 0 ∧ p ∣ e

/-- The branch data g, e, and f are the reusable local input for later tame/wild analysis. -/
theorem chapter11_branch_data_supports_later_tame_wild_analysis
    (e p : ℕ) (hp : p = 0 ∨ Nat.Prime p) :
    chapter11TameAtResidueCharacteristic e p ∨
      chapter11WildAtResidueCharacteristic e p := by
  rcases hp with rfl | hp
  · exact Or.inl (Or.inl rfl)
  by_cases hdiv : p ∣ e
  · exact Or.inr ⟨hp.ne_zero, hdiv⟩
  · exact Or.inl (Or.inr (hp.coprime_iff_not_dvd.mpr hdiv).symm)

end
end LastLib.Book01ValuationsDVRsAndCompletions.Chapter11
