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
  Q.IsPrime ∧ ¬Q.LiesOver p

/-! The following interfaces state the localization identities used in the
Dedekind-domain description.  The finite normalization and the two integral
closure structures are explicit so that these results do not reduce to the
predicate wrappers above. -/

/-- The normalization after localizing a Dedekind domain is its base change. -/
theorem chapter11_base_change_model_of_integral_closure
    (R S A B K L : Type*) [CommRing R] [IsDedekindDomain R]
    [CommRing S] [IsDomain S] [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [Field K] [Field L]
    [Algebra R S] [Algebra R A] [Algebra R B]
    [Algebra R K] [IsFractionRing R K] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L]
    [Algebra A B] [Algebra A L] [Algebra B L]
    [IsScalarTower R A B]
    [IsScalarTower A B L] [IsScalarTower R A L]
    [IsScalarTower R B L] [Algebra S L] [IsScalarTower R S L]
    [IsIntegralClosure S R L] [IsIntegralClosure B A L]
    [FiniteDimensional K L]
    (p : Ideal R) [p.IsPrime] [p.IsMaximal]
    [IsLocalization p.primeCompl A] (hp0 : p ≠ (⊥ : Ideal R))
    (hfinite : Module.Finite R S) :
    chapter11BaseChangeModel R S A B := by
  sorry

/-- The same finite normalization is the normalization of `S` away from `p`. -/
theorem chapter11_away_model_of_integral_closure
    (R S A B K L : Type*) [CommRing R] [IsDedekindDomain R]
    [CommRing S] [IsDomain S] [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [Field K] [Field L]
    [Algebra R S] [Algebra R A] [Algebra R B]
    [Algebra R K] [IsFractionRing R K] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L]
    [Algebra A B] [Algebra A L] [Algebra B L]
    [IsScalarTower R A B]
    [IsScalarTower A B L] [IsScalarTower R A L]
    [IsScalarTower R B L] [Algebra S L] [IsScalarTower R S L]
    [IsIntegralClosure S R L] [IsIntegralClosure B A L]
    [FiniteDimensional K L]
    (p : Ideal R) [p.IsPrime] [p.IsMaximal]
    [IsLocalization p.primeCompl A] (hp0 : p ≠ (⊥ : Ideal R))
    (hfinite : Module.Finite R S) :
    chapter11AwayModel R S A B p := by
  sorry

/-- A nonzero prime of the normalization away from `p` maps to the unit ideal. -/
theorem chapter11_prime_disappears_away_from
    (R S K L : Type*) [CommRing R] [IsDedekindDomain R]
    [CommRing S] [IsDomain S] [Field K] [Field L]
    [Algebra R S] [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [Algebra S L] [IsScalarTower R S L]
    [IsIntegralClosure S R L] [FiniteDimensional K L]
    (p : Ideal R) [p.IsPrime] [p.IsMaximal]
    (hp0 : p ≠ (⊥ : Ideal R)) (hfinite : Module.Finite R S)
    (Q : Ideal S) (hQ : chapter11PrimeDisappearsAwayFrom R S p Q)
    (hQ0 : Q ≠ (⊥ : Ideal S)) :
    Ideal.map (algebraMap S (chapter11AwayLocalization R S p)) Q = ⊤ := by
  sorry

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
    [FiniteDimensional K L]
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
  classical
  let _ : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  let S := Localization.AtPrime P
  have hSreg : ∀ y : P.primeCompl, (y : B) ∈ B⁰ :=
    fun y => (Ideal.primeCompl_le_nonZeroDivisors P) y.2
  let φ : S →+* L :=
    IsLocalization.lift (M := P.primeCompl) (S := S) (g := algebraMap B L) (by
      intro y
      apply isUnit_iff_ne_zero.mpr
      exact map_ne_zero_of_mem_nonZeroDivisors (algebraMap B L)
        (IsIntegralClosure.algebraMap_injective B A L) (hSreg y))
  let _ : Algebra S L := φ.toAlgebra
  let _ : IsScalarTower B S L := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro b
    change algebraMap B L b = φ (algebraMap B S b)
    symm
    exact IsLocalization.lift_eq (M := P.primeCompl) (S := S) (g := algebraMap B L) _ b
  let _ : IsScalarTower A S L := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro a
    rw [IsScalarTower.algebraMap_apply A B L]
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [IsScalarTower.algebraMap_apply A B S,
      ← IsScalarTower.algebraMap_apply B S L]
  let _ : IsFractionRing S L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl S L
  let vL : Valuation L ℤᵐ⁰ := (IsDiscreteValuationRing.maximalIdeal S).valuation L
  let e : S ≃+* vL.valuationSubring :=
    IsDiscreteValuationRing.equivValuationSubring
  have he : ∀ s : S, (e s : L) = algebraMap S L s := by
    intro s
    rfl
  let vA : Valuation K ℤᵐ⁰ := (IsDiscreteValuationRing.maximalIdeal A).valuation K
  have hvKle : vA.valuationSubring ≤ vK.valuationSubring := by
    change vA.valuationSubring.toSubring ≤ vK.valuationSubring.toSubring
    rw [← IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring]
    intro x hx
    rcases Subring.mem_map.mp hx with ⟨a, -, rfl⟩
    change (algebraMap A K a : K) ∈ vK.valuationSubring
    rw [← hιA a]
    exact (ιA a).property
  have hιAinj : Function.Injective ιA := by
    intro x y hxy
    apply hAinj
    calc
      algebraMap A K x = (ιA x : K) := (hιA x).symm
      _ = (ιA y : K) := congrArg Subtype.val hxy
      _ = algebraMap A K y := hιA y
  have hm0 : m ≠ (⊥ : Ideal A) := by
    rw [hm]
    intro h
    apply IsDiscreteValuationRing.not_isField A
    exact (IsLocalRing.isField_iff_maximalIdeal_eq).2 h
  have hvKtop : vK.valuationSubring ≠ ⊤ := by
    intro htop
    have hmax : IsLocalRing.maximalIdeal vK.valuationSubring =
        (⊥ : Ideal vK.valuationSubring) := by
      rw [htop]
      exact IsLocalRing.maximalIdeal_eq_bot
    apply hm0
    calc
      m = (IsLocalRing.maximalIdeal vK.valuationSubring).comap ιA := hcenter
      _ = (⊥ : Ideal A) := by
        rw [hmax]
        exact Ideal.comap_bot_of_injective ιA hιAinj
  have hvKeq : vA.valuationSubring = vK.valuationSubring :=
    ValuationSubring.eq_of_le_of_ne_top vA.valuationSubring hvKle hvKtop
  have hvLtop : (vL.comap (algebraMap K L)).valuationSubring ≠ ⊤ := by
    intro htop
    let : P.LiesOver m := hP.2.2
    obtain ⟨a, ha0⟩ :=
      Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hm0)
    have haP : algebraMap A B (a : A) ∈ P :=
      (Ideal.mem_of_liesOver P m (a : A)).mp a.property
    have haSmax : algebraMap B S (algebraMap A B (a : A)) ∈
        IsLocalRing.maximalIdeal S :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff S P _).2 haP
    have haVLmax : e (algebraMap B S (algebraMap A B (a : A))) ∈
        IsLocalRing.maximalIdeal vL.valuationSubring := by
      rw [IsLocalRing.mem_maximalIdeal, map_mem_nonunits_iff e,
        ← IsLocalRing.mem_maximalIdeal]
      exact haSmax
    have haLlt : vL (algebraMap A L (a : A)) < 1 := by
      have hlt := (Valuation.mem_maximalIdeal_iff L vL).mp haVLmax
      rw [he] at hlt
      simpa [IsScalarTower.algebraMap_apply A B L,
        IsScalarTower.algebraMap_apply B S L] using hlt
    have haL0 : algebraMap A L (a : A) ≠ 0 := by
      intro hzero
      apply ha0
      apply Subtype.ext
      apply hAinj
      apply hKinj
      simpa [IsScalarTower.algebraMap_apply A K L] using hzero
    have hinv_mem :
        (algebraMap K L ((algebraMap A K (a : A))⁻¹)) ∈ vL.valuationSubring := by
      have hmem :
          (algebraMap A K (a : A))⁻¹ ∈
            (vL.comap (algebraMap K L)).valuationSubring := by
        rw [htop]
        simp
      exact hmem
    have hinv_le : vL (algebraMap K L ((algebraMap A K (a : A))⁻¹)) ≤ 1 :=
      (Valuation.mem_valuationSubring_iff _ _).mp hinv_mem
    have hinv_le' : vL (algebraMap A L (a : A))⁻¹ ≤ 1 := by
      simpa [map_inv₀, IsScalarTower.algebraMap_apply A K L] using hinv_le
    exact (not_lt_of_ge hinv_le') ((vL.val_lt_one_iff haL0).mp haLlt)
  have hvLle : vA.valuationSubring ≤ (vL.comap (algebraMap K L)).valuationSubring := by
    change vA.valuationSubring.toSubring ≤ (vL.comap (algebraMap K L)).valuationSubring.toSubring
    rw [← IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring]
    intro x hx
    rcases Subring.mem_map.mp hx with ⟨a, -, rfl⟩
    change vL (algebraMap K L (algebraMap A K a)) ≤ 1
    rw [← IsScalarTower.algebraMap_apply A K L,
      IsScalarTower.algebraMap_apply A S L]
    apply (Valuation.mem_valuationSubring_iff _ _).mp
    rw [← he]
    exact (e (algebraMap A S a)).property
  have hvLeq : vA.valuationSubring = (vL.comap (algebraMap K L)).valuationSubring :=
    ValuationSubring.eq_of_le_of_ne_top vA.valuationSubring hvLle hvLtop
  let ι : B →+* vL.valuationSubring :=
    e.toRingHom.comp (algebraMap B S)
  refine ⟨vL, ι, ?_, ?_, ?_⟩
  · change vK.IsEquiv (vL.comap (algebraMap K L))
    apply (Valuation.isEquiv_iff_valuationSubring vK (vL.comap (algebraMap K L))).2
    calc
      vK.valuationSubring = vA.valuationSubring := hvKeq.symm
      _ = (vL.comap (algebraMap K L)).valuationSubring := hvLeq
  · ext b
    change b ∈ P ↔ e (algebraMap B S b) ∈ IsLocalRing.maximalIdeal vL.valuationSubring
    rw [IsLocalRing.mem_maximalIdeal, map_mem_nonunits_iff e,
      ← IsLocalRing.mem_maximalIdeal]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff S P _).symm
  · intro b
    calc
      (ι b : L) = (e (algebraMap B S b) : L) := rfl
      _ = algebraMap S L (algebraMap B S b) := he _
      _ = algebraMap B L b := by
        exact IsLocalization.lift_eq (M := P.primeCompl) (S := S)
          (g := algebraMap B L) _ b

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
    (W : ValuationSubring L)
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

set_option maxHeartbeats 5000000 in
/-- A valuation center on a Dedekind branch identifies the branch localization
with the displayed valuation ring. -/
theorem chapter11_branch_center_gives_localization_equiv
    (B L : Type*) [CommRing B] [Field L] [Algebra B L]
    [IsFractionRing B L] [IsDedekindDomain B]
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (P : Ideal B) [P.IsPrime] [P.IsMaximal] (hP0 : P ≠ (⊥ : Ideal B))
    (vL : Valuation L Γ) (ι : B →+* vL.valuationSubring)
    (hι : ∀ b : B, (ι b : L) = algebraMap B L b)
    (hcenter : chapter11ValuationCenter B L P vL ι) :
    ∃ e : Localization P.primeCompl ≃+* vL.valuationSubring,
      ∀ b : B,
        e (Localization.mk b ⟨1, P.primeCompl.one_mem⟩) = ι b := by
  classical
  let S := Localization.AtPrime P
  let : IsDiscreteValuationRing S :=
    chapter11_branch_localization_is_dvr B P hP0
  let φ : S →+* L :=
    IsLocalization.lift (M := P.primeCompl) (S := S) (g := algebraMap B L) (by
      intro y
      apply isUnit_iff_ne_zero.mpr
      exact map_ne_zero_of_mem_nonZeroDivisors (algebraMap B L)
        (IsFractionRing.injective B L) (Ideal.primeCompl_le_nonZeroDivisors P y.2))
  let _ : Algebra S L := φ.toAlgebra
  let _ : IsScalarTower B S L := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro b
    change algebraMap B L b = φ (algebraMap B S b)
    symm
    exact IsLocalization.lift_eq (M := P.primeCompl) (S := S)
      (g := algebraMap B L) _ b
  let : IsFractionRing S L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl S L
  let v₀ : Valuation L ℤᵐ⁰ := (IsDiscreteValuationRing.maximalIdeal S).valuation L
  let e₀ : S ≃+* v₀.valuationSubring :=
    by simpa [v₀] using (IsDiscreteValuationRing.equivValuationSubring :
      S ≃+* ((IsDiscreteValuationRing.maximalIdeal S).valuation L).valuationSubring)
  have he₀ : ∀ s : S, (e₀ s : L) = φ s := by
    intro s
    rfl
  let ψ : S →+* vL.valuationSubring :=
    IsLocalization.lift (M := P.primeCompl) (S := S) (g := ι) (by
      intro y
      have hymax : ι (y : B) ∉ IsLocalRing.maximalIdeal vL.valuationSubring := by
        intro hymax
        have hyP : (y : B) ∈ P := by
          have hycomap : (y : B) ∈
              (IsLocalRing.maximalIdeal vL.valuationSubring).comap ι := hymax
          rwa [← hcenter] at hycomap
        exact y.2 hyP
      exact IsLocalRing.notMem_maximalIdeal.mp hymax)
  have hψφ : vL.valuationSubring.subtype.comp ψ = φ := by
    apply IsLocalization.ringHom_ext P.primeCompl
    apply RingHom.ext
    intro b
    simp only [RingHom.comp_apply]
    rw [ValuationSubring.subtype_apply]
    rw [IsLocalization.lift_eq (M := P.primeCompl) (S := S) (g := ι),
      IsLocalization.lift_eq (M := P.primeCompl) (S := S) (g := algebraMap B L)]
    exact hι b
  have hψφ_apply (s : S) :
      (ψ s : L) = φ s := by
    exact RingHom.congr_fun hψφ s
  have he₀_apply (s : S) :
      (e₀ s : L) = φ s := he₀ s
  have hle : v₀.valuationSubring ≤ vL.valuationSubring := by
    intro z hz
    rcases e₀.surjective ⟨z, hz⟩ with ⟨s, hs⟩
    have hz' : z = (ψ s : L) := by
      calc
        z = (e₀ s : L) := by simpa using congrArg Subtype.val hs.symm
        _ = (ψ s : L) := by rw [he₀_apply, hψφ_apply]
    rw [hz']
    exact (ψ s).property
  have hιinj : Function.Injective ι := by
    intro x y hxy
    apply IsFractionRing.injective B L
    calc
      algebraMap B L x = (ι x : L) := (hι x).symm
      _ = (ι y : L) := congrArg Subtype.val hxy
      _ = algebraMap B L y := hι y
  have hWtop : vL.valuationSubring ≠ ⊤ := by
    intro htop
    have hmax : IsLocalRing.maximalIdeal vL.valuationSubring =
        (⊥ : Ideal vL.valuationSubring) := by
      rw [htop]
      exact IsLocalRing.maximalIdeal_eq_bot
    apply hP0
    calc
      P = (IsLocalRing.maximalIdeal vL.valuationSubring).comap ι := hcenter
      _ = (⊥ : Ideal B) := by
        rw [hmax]
        exact Ideal.comap_bot_of_injective ι hιinj
  have hvaluationSubring : v₀.valuationSubring = vL.valuationSubring := by
    exact ValuationSubring.eq_of_le_of_ne_top v₀.valuationSubring hle hWtop
  have hφinj : Function.Injective φ := by
    change Function.Injective (algebraMap S L)
    exact IsFractionRing.injective S L
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    apply hφinj
    calc
      φ x = (ψ x : L) := (hψφ_apply x).symm
      _ = (ψ y : L) := congrArg Subtype.val hxy
      _ = φ y := hψφ_apply y
  have hψsurj : Function.Surjective ψ := by
    intro z
    have hz₀ : (z : L) ∈ v₀.valuationSubring := by
      rw [hvaluationSubring]
      exact z.property
    let z₀ : v₀.valuationSubring := ⟨z, hz₀⟩
    rcases e₀.surjective z₀ with ⟨s, hs⟩
    refine ⟨s, ?_⟩
    apply Subtype.ext
    calc
      (ψ s : L) = φ s := hψφ_apply s
      _ = (e₀ s : L) := (he₀_apply s).symm
      _ = (z₀ : L) := congrArg Subtype.val hs
      _ = (z : L) := rfl
  let e : S ≃+* vL.valuationSubring :=
    RingEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  have he (s : S) : (e s : L) = φ s := by
    change (ψ s : L) = φ s
    exact hψφ_apply s
  refine ⟨e, ?_⟩
  intro b
  apply Subtype.ext
  calc
    (e (Localization.mk b ⟨1, P.primeCompl.one_mem⟩) : L) =
        (e (algebraMap B S b) : L) := by
          have hmk : Localization.mk b ⟨1, P.primeCompl.one_mem⟩ =
              algebraMap B S b := Localization.mk_one_eq_algebraMap b
          rw [hmk]
    _ = φ (algebraMap B S b) := he _
    _ = algebraMap B L b := by
      rw [IsLocalization.lift_eq (M := P.primeCompl) (S := S) (g := algebraMap B L)]
    _ = (ι b : L) := (hι b).symm

/-! A finite integral normalization of a DVR is Dedekind without a
separability assumption.  The standard trace-dual theorem supplies the
finite case separately; this interface records the normalization argument
needed when finiteness is already available. -/
theorem chapter11_finite_normalization_is_dedekind
    (A K L B : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Field L] [CommRing B]
    [Algebra A K] [IsFractionRing A K] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] (hfinite : Module.Finite A B) :
    IsDedekindDomain B := by
  let : IsDedekindDomain A :=
    ((IsDiscreteValuationRing.TFAE A (IsDiscreteValuationRing.not_isField A)).out 0 2).mp
      (inferInstance : IsDiscreteValuationRing A)
  let : IsDomain B := (IsIntegralClosure.algebraMap_injective B A L).isDomain
  let : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  let : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  let : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L
  refine (isDedekindDomain_iff (A := B) L).2
    ⟨inferInstance, inferInstance, Ring.DimensionLEOne.of_isIntegral A B, ?_⟩
  intro x hx
  refine ⟨IsIntegralClosure.mk' B x (isIntegral_trans (R := A) _ hx), ?_⟩
  exact IsIntegralClosure.algebraMap_mk' _ _ _

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
    [IsScalarTower A K L] [FiniteDimensional K L]
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
  let : IsDedekindDomain B :=
    chapter11_finite_normalization_is_dedekind A K L B hfinite
  let : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  let m : Ideal A := IsLocalRing.maximalIdeal A
  let : m.IsMaximal := by
    dsimp [m]
    exact IsLocalRing.maximalIdeal.isMaximal A
  let : m.IsPrime := inferInstance
  let : Fintype (m.primesOver B) :=
    Set.Finite.fintype (Algebra.QuasiFinite.finite_primesOver m)
  have hm0 : m ≠ (⊥ : Ideal A) := by
    dsimp [m]
    exact IsDiscreteValuationRing.not_a_field A
  have hmaxiff : ∀ P : Ideal B,
      P.IsMaximal ↔ P.IsPrime ∧ P.LiesOver m := by
    intro P
    constructor
    · intro hP
      let : P.IsMaximal := hP
      have hcomp : P.comap (algebraMap A B) = IsLocalRing.maximalIdeal A :=
        IsLocalRing.eq_maximalIdeal
          (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P)
      exact ⟨hP.isPrime, ⟨by simpa [m] using hcomp.symm⟩⟩
    · rintro ⟨hPprime, hPover⟩
      let : P.IsPrime := hPprime
      let : P.LiesOver m := hPover
      exact hPprime.isMaximal
        (Ideal.ne_bot_of_liesOver_of_ne_bot hm0 P)
  let s : Finset (Ideal B) :=
    Finset.univ.image (fun q : m.primesOver B => (q : Ideal B))
  have hsemilocal : chapter11IsSemilocal B := by
    refine ⟨s, ?_⟩
    intro P
    constructor
    · intro hP
      refine Finset.mem_image.mpr
        ⟨⟨P, ⟨hP.isPrime, (hmaxiff P).mp hP |>.2⟩⟩,
          Finset.mem_univ _, rfl⟩
    · intro hP
      rcases Finset.mem_image.mp hP with ⟨q, -, rfl⟩
      exact (hmaxiff q.1).mpr ⟨q.2.1, q.2.2⟩
  have hlocal : ∀ (P : Ideal B) [P.IsPrime],
      P.IsMaximal → IsDiscreteValuationRing (chapter11BranchLocalization B P) := by
    intro P _ hPmax
    let : P.IsMaximal := hPmax
    have hPover : P.LiesOver m := (hmaxiff P).mp hPmax |>.2
    let : P.LiesOver m := hPover
    exact chapter11_branch_localization_is_dvr B P
      (Ideal.ne_bot_of_liesOver_of_ne_bot hm0 P)
  refine ⟨inferInstance, hsemilocal, ?_, hlocal, ?_⟩
  · intro P
    simpa [m] using hmaxiff P
  · intro ΓL _ vL
    constructor
    · intro hext
      have hcenter_exists :
          ∃ P : Ideal B, chapter11Branch A B m P ∧
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
              vL (algebraMap K L (algebraMap A K a)) ≤ vL (algebraMap K L 1) := by
            simpa [W, Valuation.comap_apply] using hWext (algebraMap A K a) 1
          have hv' := hv.mp ha'
          simpa [IsScalarTower.algebraMap_apply A K L] using hv'
        let ιA' : A →+* W.valuation.valuationSubring :=
          (RingHom.codRestrict (algebraMap A L) W.valuation.valuationSubring
            (by simpa [W] using hmemA))
        have hιA' : ∀ a : A, (ιA' a : L) = algebraMap A L a := by
          intro a
          rfl
        have hcenter' : chapter11ValuationCenter A L m W.valuation ιA' := by
          change m = (IsLocalRing.maximalIdeal W.valuation.valuationSubring).comap ιA'
          change m = (IsLocalRing.maximalIdeal vK.valuationSubring).comap ιA at hcenter
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
            have hltK : vK (algebraMap A K a) < vK 1 := by
              rw [← hιA a]
              simpa using (Valuation.mem_maximalIdeal_iff (K := K) vK).mp haK
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
          RingHom.codRestrict (algebraMap A L) W hmemA
        have hιA_W : ∀ a : A, (ιA_W a : L) = algebraMap A L a := by
          intro a
          rfl
        let _ : Algebra A W := ιA_W.toAlgebra
        let _ : IsScalarTower A W L := by
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
            refine { hom_inj := Subtype.val_injective, map_le_one := ?_, exists_of_le_one := ?_ }
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
          RingHom.codRestrict (algebraMap B L) W.valuation.valuationSubring
            (by simpa only [ValuationSubring.valuationSubring_valuation] using hmemB)
        have hιB : ∀ b : B, (ιB b : L) = algebraMap B L b := by
          intro b
          rfl
        have hconv := chapter11_valuation_ring_converse
          A B K L _hAinj hKinj m rfl W ιB hιB ιA' hιA' hcenter'
        rcases hconv with ⟨P, hP, hPcenter⟩
        let ιB' : B →+* vL.valuationSubring :=
          RingHom.codRestrict (algebraMap B L) vL.valuationSubring
            (by simpa [W] using hmemB)
        have hιB' : ∀ b : B, (ιB' b : L) = algebraMap B L b := by
          intro b
          rfl
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
            apply (Valuation.mem_maximalIdeal_iff (K := L) vL).mpr
            simpa [hιB' b] using hltV
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
        · simpa [m] using hP
        · exact ⟨ιB', hPcenter', hιB'⟩
      rcases hcenter_exists with ⟨P, hP, ι, hιcenter, hι⟩
      let : P.IsPrime := hP.1
      let : P.IsMaximal := hP.2.1
      let : P.LiesOver m := hP.2.2
      have hP0 : P ≠ (⊥ : Ideal B) :=
        Ideal.ne_bot_of_liesOver_of_ne_bot hm0 P
      obtain ⟨e, he⟩ := chapter11_branch_center_gives_localization_equiv
        B L P hP0 vL ι hι hιcenter
      let c : Chapter11ValuationBranchCorrespondence B L P vL :=
        { prime := hP.1
          embedding := ι
          embedding_compatible := hι
          center := hιcenter
          localizationEquiv := e
          localizationEquiv_on_B := he }
      refine ⟨P, ⟨hP.2.1, hP.2.2, ⟨c⟩⟩, ?_⟩
      intro Q hQ
      rcases hQ.2.2 with ⟨cQ⟩
      have hιEq : cQ.embedding = c.embedding := by
        apply RingHom.ext
        intro b
        apply Subtype.ext
        calc
          (cQ.embedding b : L) = algebraMap B L b := cQ.embedding_compatible b
          _ = (c.embedding b : L) := (c.embedding_compatible b).symm
      calc
        Q = (IsLocalRing.maximalIdeal vL.valuationSubring).comap cQ.embedding := cQ.center
        _ = (IsLocalRing.maximalIdeal vL.valuationSubring).comap c.embedding := by rw [hιEq]
        _ = P := c.center.symm
    · intro hdata
      rcases hdata with ⟨P, ⟨hPmax, hPover, ⟨c⟩⟩, _⟩
      let : P.IsPrime := c.prime
      let : P.IsMaximal := hPmax
      have hP0 : P ≠ (⊥ : Ideal B) :=
        Ideal.ne_bot_of_liesOver_of_ne_bot hm0 P
      let vA : Valuation K ℤᵐ⁰ := (IsDiscreteValuationRing.maximalIdeal A).valuation K
      have hvAle : vA.valuationSubring ≤ vK.valuationSubring := by
        change vA.valuationSubring.toSubring ≤ vK.valuationSubring.toSubring
        rw [← IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring]
        intro x hx
        rcases Subring.mem_map.mp hx with ⟨a, -, rfl⟩
        change (algebraMap A K a : K) ∈ vK.valuationSubring
        rw [← hιA a]
        exact (ιA a).property
      have hιAinj : Function.Injective ιA := by
        intro x y hxy
        apply _hAinj
        calc
          algebraMap A K x = (ιA x : K) := (hιA x).symm
          _ = (ιA y : K) := congrArg Subtype.val hxy
          _ = algebraMap A K y := hιA y
      have hvKtop : vK.valuationSubring ≠ ⊤ := by
        intro htop
        have hmax : IsLocalRing.maximalIdeal vK.valuationSubring =
            (⊥ : Ideal vK.valuationSubring) := by
          rw [htop]
          exact IsLocalRing.maximalIdeal_eq_bot
        apply hm0
        have hcenter_eq : IsLocalRing.maximalIdeal A =
            (IsLocalRing.maximalIdeal vK.valuationSubring).comap ιA := by
          exact hcenter
        calc
          m = (IsLocalRing.maximalIdeal vK.valuationSubring).comap ιA := by
            simpa [m] using hcenter_eq
          _ = (⊥ : Ideal A) := by
            rw [hmax]
            exact Ideal.comap_bot_of_injective ιA hιAinj
      have hvKeq : vA.valuationSubring = vK.valuationSubring :=
        ValuationSubring.eq_of_le_of_ne_top vA.valuationSubring hvAle hvKtop
      have hvLle : vA.valuationSubring ≤
          (vL.comap (algebraMap K L)).valuationSubring := by
        change vA.valuationSubring.toSubring ≤
          (vL.comap (algebraMap K L)).valuationSubring.toSubring
        rw [← IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring]
        intro x hx
        rcases Subring.mem_map.mp hx with ⟨a, -, rfl⟩
        change vL (algebraMap K L (algebraMap A K a)) ≤ 1
        rw [← IsScalarTower.algebraMap_apply A K L]
        have haW : (c.embedding (algebraMap A B a) : L) ∈ vL.valuationSubring :=
          (c.embedding (algebraMap A B a)).property
        have haVal : vL (c.embedding (algebraMap A B a) : L) ≤ 1 :=
          (Valuation.mem_valuationSubring_iff vL _).mp haW
        simpa [c.embedding_compatible (algebraMap A B a),
          IsScalarTower.algebraMap_apply A B L] using haVal
      let : P.LiesOver m := hPover
      let ιA0 : A →+* (vL.comap (algebraMap K L)).valuationSubring :=
        RingHom.codRestrict (algebraMap A K)
          (vL.comap (algebraMap K L)).valuationSubring (by
            intro a
            have haA : algebraMap A K a ∈ vA.valuationSubring := by
              change algebraMap A K a ∈ vA.valuationSubring.toSubring
              rw [← IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring]
              exact ⟨a, Subring.mem_top _, rfl⟩
            exact hvLle haA)
      have hιA0 : ∀ a : A, (ιA0 a : K) = algebraMap A K a := by
        intro a
        rfl
      have hιA0inj : Function.Injective ιA0 := by
        intro x y hxy
        apply _hAinj
        exact congrArg Subtype.val hxy
      have hbasecenter :
          (IsLocalRing.maximalIdeal (vL.comap (algebraMap K L)).valuationSubring).comap
              ιA0 = m := by
        apply Ideal.ext
        intro a
        constructor
        · intro ha
          change ιA0 a ∈
            IsLocalRing.maximalIdeal (vL.comap (algebraMap K L)).valuationSubring at ha
          have hltL : vL (algebraMap A L a) < 1 := by
            have hlt :=
              (Valuation.mem_maximalIdeal_iff (K := K)
                (vL.comap (algebraMap K L)) (a := ιA0 a)).mp ha
            rw [hιA0 a] at hlt
            simpa [Valuation.comap_apply, IsScalarTower.algebraMap_apply A K L] using hlt
          have hmaxL : c.embedding (algebraMap A B a) ∈
              IsLocalRing.maximalIdeal vL.valuationSubring := by
            apply (Valuation.mem_maximalIdeal_iff (K := L) vL).mpr
            simpa [c.embedding_compatible (algebraMap A B a),
              IsScalarTower.algebraMap_apply A B L] using hltL
          have haP : algebraMap A B a ∈ P := by
            have haComap : algebraMap A B a ∈
                (IsLocalRing.maximalIdeal vL.valuationSubring).comap c.embedding := hmaxL
            exact Eq.mpr (congrArg (fun I : Ideal B => algebraMap A B a ∈ I) c.center)
              haComap
          exact (Ideal.mem_of_liesOver P m a).mpr haP
        · intro ha
          have haP : algebraMap A B a ∈ P :=
            (Ideal.mem_of_liesOver P m a).mp ha
          have hmaxL : c.embedding (algebraMap A B a) ∈
              IsLocalRing.maximalIdeal vL.valuationSubring := by
            have haComap : algebraMap A B a ∈
                (IsLocalRing.maximalIdeal vL.valuationSubring).comap c.embedding :=
              Eq.mp (congrArg (fun I : Ideal B => algebraMap A B a ∈ I) c.center) haP
            exact haComap
          have hltL : vL (algebraMap A L a) < 1 := by
            have hlt := (Valuation.mem_maximalIdeal_iff (K := L) vL).mp hmaxL
            simpa [c.embedding_compatible (algebraMap A B a),
              IsScalarTower.algebraMap_apply A B L] using hlt
          have hltK : (vL.comap (algebraMap K L)) (algebraMap A K a) < 1 := by
            simpa [Valuation.comap_apply, IsScalarTower.algebraMap_apply A K L] using hltL
          have haK : ιA0 a ∈
              IsLocalRing.maximalIdeal (vL.comap (algebraMap K L)).valuationSubring :=
            (Valuation.mem_maximalIdeal_iff (K := K)
              (vL.comap (algebraMap K L)) (a := ιA0 a)).mpr hltK
          change ιA0 a ∈
            IsLocalRing.maximalIdeal (vL.comap (algebraMap K L)).valuationSubring
          exact haK
      have hvLtop : (vL.comap (algebraMap K L)).valuationSubring ≠ ⊤ := by
        intro htop
        have hmaxW : IsLocalRing.maximalIdeal
            (vL.comap (algebraMap K L)).valuationSubring =
              (⊥ : Ideal (vL.comap (algebraMap K L)).valuationSubring) := by
          rw [htop]
          exact IsLocalRing.maximalIdeal_eq_bot
        have hmax : (IsLocalRing.maximalIdeal
            (vL.comap (algebraMap K L)).valuationSubring).comap
              ιA0 = (⊥ : Ideal A) := by
          rw [hmaxW]
          exact Ideal.comap_bot_of_injective ιA0 hιA0inj
        apply hm0
        exact hbasecenter.symm.trans hmax
      have hvLeq : vA.valuationSubring =
          (vL.comap (algebraMap K L)).valuationSubring :=
        ValuationSubring.eq_of_le_of_ne_top vA.valuationSubring hvLle hvLtop
      apply (Valuation.isEquiv_iff_valuationSubring vK
        (vL.comap (algebraMap K L))).mpr
      calc
        vK.valuationSubring = vA.valuationSubring := hvKeq.symm
        _ = (vL.comap (algebraMap K L)).valuationSubring := hvLeq


/-- In the finite normalization, maximal ideals are exactly the primes above the base maximal ideal. -/
theorem chapter11_maximal_ideals_are_precisely_branches
    (A K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L]
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
    chapter11_finite_normalization_is_dedekind A K L
      (chapter11IntegralClosure A L) hfinite
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
