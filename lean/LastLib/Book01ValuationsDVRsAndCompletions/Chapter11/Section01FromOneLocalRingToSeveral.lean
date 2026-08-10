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

/-! # Book 1, Chapter 11, Section 11.1: From One Local Ring to Several
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
    (_hfinite : Module.Finite A B)
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
  let : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L
  let : Module.IsTorsionFree A L :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (by
      intro x y hxy
      apply hAinj
      apply hKinj
      simpa only [IsScalarTower.algebraMap_apply A K L] using hxy)
  let : Module.IsTorsionFree A B := IsIntegralClosure.isTorsionFree A L
  let : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  have hPcomp : P.primeCompl ≤ (nonZeroDivisors B).comap (RingHom.id B) := by
    intro x hx
    change x ∈ nonZeroDivisors B
    exact P.primeCompl_le_nonZeroDivisors hx
  let alg : S →+* L :=
    IsLocalization.map L (RingHom.id B) hPcomp
  let : Algebra S L := alg.toAlgebra
  let : IsScalarTower B S L := by
    apply IsScalarTower.of_algebraMap_eq'
    change algebraMap B L = alg.comp (algebraMap B S)
    simp [alg]
  let : IsFractionRing S L :=
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
            let : P.LiesOver m := hP.2.2
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
    (_hAinj : Function.Injective (algebraMap A K))
    (_hKinj : Function.Injective (algebraMap K L))
    (m : Ideal A) (hm : m = IsLocalRing.maximalIdeal A)
    (W : ValuationSubring L) (vK : Valuation K W.ValueGroup)
    (_hext : vK.IsEquiv (W.valuation.comap (algebraMap K L)))
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
  let : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L
  let : P.IsPrime := hPprime
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
    (B : Type*) [CommRing B] [IsDedekindDomain B]
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
    (_hAinj : Function.Injective (algebraMap A K))
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
  let : IsDedekindDomain A :=
    ((IsDiscreteValuationRing.TFAE A (IsDiscreteValuationRing.not_isField A)).out 0 2).mp
      (inferInstance : IsDiscreteValuationRing A)
  let : IsDedekindDomain B :=
    IsIntegralClosure.isDedekindDomain A K L B
  let : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  have hmax0 : IsLocalRing.maximalIdeal A ≠ (⊥ : Ideal A) :=
    IsDiscreteValuationRing.not_a_field A
  have hmax_over : ∀ P : Ideal B, P.IsMaximal →
      P.LiesOver (IsLocalRing.maximalIdeal A) := by
    intro P hP
    let : P.IsMaximal := hP
    have hunder : (P.under A).IsMaximal := Ideal.IsMaximal.under A P
    exact ⟨(IsLocalRing.eq_maximalIdeal hunder).symm⟩
  have hbranch_max : ∀ P : Ideal B,
      P.IsPrime ∧ P.LiesOver (IsLocalRing.maximalIdeal A) → P.IsMaximal := by
    intro P hP
    let : P.IsPrime := hP.1
    let : P.LiesOver (IsLocalRing.maximalIdeal A) := hP.2
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
        rw [← hι b]
        exact (ι b).property
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
    let : Algebra B S := inferInstance
    let : IsLocalization P.primeCompl W₀ :=
      Localization.subalgebra.isLocalization_ofField L P.primeCompl
        P.primeCompl_le_nonZeroDivisors
    let : IsLocalization P.primeCompl S :=
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
    let : Algebra A vL.valuationSubring := hA.toAlgebra
    let : IsScalarTower A vL.valuationSubring L := by
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
    let : P.IsPrime := cP.prime
    let : P.IsMaximal := hPmax
    let : P.LiesOver (IsLocalRing.maximalIdeal A) := hPover
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
  let : IsDedekindDomain A :=
    ((IsDiscreteValuationRing.TFAE A (IsDiscreteValuationRing.not_isField A)).out 0 2).mp
      (inferInstance : IsDiscreteValuationRing A)
  let : IsIntegralClosure (chapter11IntegralClosure A L) A L := by
    change IsIntegralClosure (integralClosure A L) A L
    infer_instance
  let : IsDedekindDomain (chapter11IntegralClosure A L) :=
    integralClosure.isDedekindDomain A K L
  let : FaithfulSMul A (chapter11IntegralClosure A L) :=
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
    let : P.IsMaximal := hP
    have hcomp : P.comap (algebraMap A (chapter11IntegralClosure A L)) =
        IsLocalRing.maximalIdeal A :=
      IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P)
    exact ⟨hP.isPrime, ⟨hcomp.symm⟩⟩
  · rintro ⟨hPprime, hPover⟩
    let : P.IsPrime := hPprime
    let : P.LiesOver (IsLocalRing.maximalIdeal A) := hPover
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

end
end LastLib.Book01ValuationsDVRsAndCompletions.Chapter11
