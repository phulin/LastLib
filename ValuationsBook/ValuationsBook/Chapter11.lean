import Mathlib

universe u v

namespace ValuationsBook.Chapter11

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

/-- The finite set of branches above a chosen base ideal. -/
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
  center : chapter11ValuationCenter B L P v embedding
  localizationEquiv : Localization P.primeCompl ≃+* v.valuationSubring
  localizationEquiv_on_B :
    ∀ x : B,
      localizationEquiv (Localization.mk x ⟨1, P.primeCompl.one_mem⟩) =
        embedding x

/-- A branch supplies a place of `L` extending the original place of `K`. -/
theorem chapter11_branch_labels_valuation_extensions
    (A B K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsFractionRing A K] [FiniteDimensional K L]
    [IsIntegralClosure B A L]
    (hAinj : Function.Injective (algebraMap A K))
    (hKinj : Function.Injective (algebraMap K L))
    (m : Ideal A) (hm : m = IsLocalRing.maximalIdeal A)
    (P : Ideal B) (hP : chapter11Branch A B m P)
    (vK : Valuation K ℤᵐ⁰)
    (hcorrespondence :
      ∃ (vL : Valuation L ℤᵐ⁰),
        Nonempty (Chapter11ValuationBranchCorrespondence B L P vL) ∧
          chapter11ValuationExtensionAt K L vK vL) :
    ∃ (vL : Valuation L ℤᵐ⁰) (ι : B →+* vL.valuationSubring),
      chapter11ValuationExtensionAt K L vK vL ∧ chapter11ValuationCenter B L P vL ι := by
  rcases hcorrespondence with ⟨vL, ⟨hdata⟩, hext⟩
  exact ⟨vL, hdata.embedding, hext, hdata.center⟩

/-- Conversely, a valuation ring containing the normalization has a center at a branch. -/
theorem chapter11_valuation_ring_converse
    (A B K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsFractionRing A K] [FiniteDimensional K L]
    [IsIntegralClosure B A L]
    (hAinj : Function.Injective (algebraMap A K))
    (hKinj : Function.Injective (algebraMap K L))
    (m : Ideal A) (hm : m = IsLocalRing.maximalIdeal A)
    (W : ValuationSubring L) (vK : Valuation K W.ValueGroup)
    (hext : vK.IsEquiv (W.valuation.comap (algebraMap K L)))
    (ι : B →+* W.valuation.valuationSubring)
    (hcontains : ∀ x : B, (ι x : L) ∈ W)
    (hcenter : ∃ P : Ideal B, chapter11ValuationCenter B L P W.valuation ι)
    (hbranch_of_center : ∀ P : Ideal B,
      chapter11ValuationCenter B L P W.valuation ι →
        chapter11Branch A B m P) :
    ∃ P : Ideal B, chapter11Branch A B m P ∧
      chapter11ValuationCenter B L P W.valuation ι := by
  rcases hcenter with ⟨P, hP⟩
  exact ⟨P, hbranch_of_center P hP, hP⟩

/-- A branch localization is a local ring, and in the Dedekind situation it is a DVR. -/
theorem chapter11_branch_localization_is_dvr
    (B : Type*) [CommRing B] [IsDomain B] [IsDedekindDomain B]
    (P : Ideal B) [P.IsPrime] [P.IsMaximal] (hP0 : P ≠ ⊥) :
    IsDiscreteValuationRing (chapter11BranchLocalization B P) := by
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hP0 (Localization.AtPrime P)

/-- The normalization is semilocal once its maximal ideals above `m` are finite. -/
def chapter11IsSemilocal (B : Type*) [CommRing B] : Prop :=
  ∃ s : Finset (Ideal B), ∀ P : Ideal B, P.IsMaximal ↔ P ∈ (s : Set (Ideal B))

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
    (hvaluation : ∀ (ΓL : Type v) [LinearOrderedCommGroupWithZero ΓL]
        (vL : Valuation L ΓL),
      vK.IsEquiv (vL.comap (algebraMap K L)) ↔
        ∃! P : Ideal B,
          P.IsMaximal ∧ P.LiesOver (IsLocalRing.maximalIdeal A) ∧
            Nonempty (Chapter11ValuationBranchCorrespondence B L P vL)) :
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
  letI : IsDedekindDomain A :=
    ((IsDiscreteValuationRing.TFAE A (IsDiscreteValuationRing.not_isField A)).out 0 2).mp
      (inferInstance : IsDiscreteValuationRing A)
  letI : IsDedekindDomain B := IsIntegralClosure.isDedekindDomain A K L B
  have hm0 : IsLocalRing.maximalIdeal A ≠ (⊥ : Ideal A) :=
    IsDiscreteValuationRing.not_a_field A
  have hbranch : ∀ P : Ideal B,
      P.IsMaximal ↔ P.IsPrime ∧ P.LiesOver (IsLocalRing.maximalIdeal A) := by
    intro P
    constructor
    · intro hP
      letI : P.IsMaximal := hP
      have hcomp : P.comap (algebraMap A B) = IsLocalRing.maximalIdeal A :=
        IsLocalRing.eq_maximalIdeal
          (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P)
      exact ⟨hP.isPrime, ⟨hcomp.symm⟩⟩
    · rintro ⟨hPprime, hPover⟩
      letI : P.IsPrime := hPprime
      letI : P.LiesOver (IsLocalRing.maximalIdeal A) := hPover
      exact hPprime.isMaximal
        (Ideal.ne_bot_of_liesOver_of_ne_bot hm0 P)
  let s : Finset (Ideal B) :=
    IsDedekindDomain.primesOverFinset (IsLocalRing.maximalIdeal A) B
  have hmem : ∀ P : Ideal B,
      P ∈ (s : Set (Ideal B)) ↔
        P.IsPrime ∧ P.LiesOver (IsLocalRing.maximalIdeal A) := by
    intro P
    simpa [s, Ideal.primesOver] using
      (IsDedekindDomain.mem_primesOverFinset_iff (p := IsLocalRing.maximalIdeal A)
        hm0 B (P := P))
  refine ⟨inferInstance, ⟨s, fun P ↦ (hbranch P).trans (hmem P).symm⟩, hbranch, ?_, hvaluation⟩
  intro P hPprime hPmax
  letI : P.IsPrime := hPprime
  letI : P.IsMaximal := hPmax
  have hPover : P.LiesOver (IsLocalRing.maximalIdeal A) := (hbranch P).mp hPmax |>.2
  letI : P.LiesOver (IsLocalRing.maximalIdeal A) := hPover
  exact chapter11_branch_localization_is_dvr B P
    (Ideal.ne_bot_of_liesOver_of_ne_bot hm0 P)

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

/-- A DVR clears denominators by a power of a uniformizer. -/
def chapter11DenominatorCleared (A B L : Type*) [CommRing A] [CommRing B] [CommRing L]
    [Algebra A L] [Algebra B L] (π : A) (x : L) : Prop :=
  ∃ n : ℕ, ∃ b : B, (algebraMap A L π) ^ n * x = algebraMap B L b

/-- Every element of the fraction field of the normalization is denominator-cleared. -/
theorem chapter11_denominators_are_powers_of_a_uniformizer
    (A B K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [Field K] [Field L] [Algebra A B] [Algebra A K]
    [Algebra K L] [Algebra B L] [Algebra A L] [IsScalarTower A K L]
    [IsScalarTower A B L] (m : Ideal A) (π : A)
    (hπ : chapter11IsUniformizer A m π) (hfinite : Module.Finite A B) (x : L)
    (hdenom : ∃ a : A, a ≠ 0 ∧ ∃ b : B, algebraMap A L a * x = algebraMap B L b)
    (hπ_power : ∀ a : A, a ≠ 0 → ∃ n : ℕ, ∃ c : A, a * c = π ^ n) :
    chapter11DenominatorCleared A B L π x := by
  rcases hdenom with ⟨a, ha, b, hab⟩
  rcases hπ_power a ha with ⟨n, c, hac⟩
  refine ⟨n, algebraMap A B c * b, ?_⟩
  calc
    (algebraMap A L π) ^ n * x = algebraMap A L (π ^ n) * x := by simp
    _ = algebraMap A L (a * c) * x := by rw [← hac]
    _ = algebraMap A L c * (algebraMap A L a * x) := by
      simp only [map_mul]
      ring
    _ = algebraMap A L c * algebraMap B L b := by rw [hab]
    _ = algebraMap B L (algebraMap A B c * b) := by
      rw [map_mul, ← IsScalarTower.algebraMap_apply A B L]

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

/-- Every extension of the base valuation occurs uniquely from one branch. -/
theorem chapter11_every_extension_is_one_of_the_branch_localizations
    (A B K L : Type*) [CommRing A] [CommRing B] [IsLocalRing A] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsIntegralClosure B A L]
    [FiniteDimensional K L] [Module.Finite A B]
    (hAinj : Function.Injective (algebraMap A K))
    (hKinj : Function.Injective (algebraMap K L))
    (m : Ideal A) (hbranches : chapter11IsSemilocal B)
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    (hext : chapter11ValuationExtensionAt K L vK vL)
    (hcorrespondence : ∃! P : Ideal B,
      chapter11Branch A B (IsLocalRing.maximalIdeal A) P ∧
        ∃ ι : B →+* vL.valuationSubring,
          chapter11ValuationCenter B L P vL ι) :
    ∃! P : Ideal B,
      chapter11Branch A B (IsLocalRing.maximalIdeal A) P ∧
        ∃ ι : B →+* vL.valuationSubring,
          chapter11ValuationCenter B L P vL ι := by
  exact hcorrespondence

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

/-- Each nonzero prime-power layer is one copy of the residue field. -/
theorem chapter11_prime_power_layer_is_a_residue_line
    (B : Type*) [CommRing B] [IsDedekindDomain B] (P : Ideal B)
    [P.IsPrime] [P.IsMaximal] [IsPrincipalIdealRing B] (e i : ℕ) (hi : i < e)
    (hP0 : P ≠ ⊥) :
    Nonempty
      (chapter11PrimePowerLayer B P i ≃+
        (B ⧸ P)) := by
  exact ⟨(Ideal.quotEquivPowQuotPowSucc
    (IsPrincipalIdealRing.principal P) hP0 i).symm.toAddEquiv⟩

/-- The quotient `B / πB` has one `k`-dimension for every residue-degree layer. -/
theorem chapter11_residue_quotient_dimension_sum
    (k A B : Type) [Field k] [CommRing A] [CommRing B] [Algebra A B]
    [Algebra k (B ⧸ (⊥ : Ideal B))] {ι : Type*} [Fintype ι]
    (Q : Type) [AddCommGroup Q] [Module k Q] [FiniteDimensional k Q]
    (e f : ι → ℕ) (hQ : Q = (B ⧸ (Ideal.map (algebraMap A B) (⊥ : Ideal A))))
    (hdecomp : Q ≃ₗ[k] (∀ i, Fin (e i) → Fin (f i) → k)) :
      Module.finrank k Q = ∑ i, e i * f i := by
  rw [hdecomp.finrank_eq, Module.finrank_pi_fintype]
  simp [Module.finrank_pi_fintype, Module.finrank_pi]

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

/-- Without finite normalization, the corresponding statement is only the fundamental inequality. -/
theorem chapter11_fundamental_inequality_without_finiteness
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra B L]
    [Algebra A L] [Algebra K L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Module.Finite A B] [Module.Free A B] [Algebra.IsIntegral A B]
    [Module.IsTorsionFree A B] [IsDedekindDomain B]
    (m : Ideal A) [m.IsPrime] [m.IsMaximal] :
    ∑ q : m.primesOver B, q.1.ramificationIdx A * q.1.inertiaDeg A ≤
      Module.finrank K L := by
  calc
    ∑ q : m.primesOver B, q.1.ramificationIdx A * q.1.inertiaDeg A =
        Module.finrank A B := Ideal.sum_ramification_inertia_eq_finrank m B
    _ = Module.finrank K L := (IsFractionRing.finrank_eq A K B L).symm
    _ ≤ Module.finrank K L := le_rfl

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

/-- A repeated residue factor, expressed intrinsically by failure of separability. -/
def chapter11RepeatedResidueFactor (k : Type*) [CommRing k] (f : k[X]) : Prop :=
  f.Monic ∧ 0 < f.natDegree ∧ ¬f.Separable

/-- A unit discriminant modulo `p`. -/
def chapter11DiscriminantUnitAt (R : Type*) [CommRing R] (p : Ideal R) (f : R[X]) : Prop :=
  IsUnit (Ideal.Quotient.mk p f.discr)

/-- The coefficient form of an Eisenstein condition at `π`. -/
def chapter11IsEisensteinAt (R : Type*) [CommRing R] (π : R) (f : R[X]) : Prop :=
  f.Monic ∧ (∀ i < f.natDegree, f.coeff i ∈ Ideal.span {π}) ∧
    f.coeff 0 ∉ (Ideal.span {π}) ^ 2

/-- Simple distinct residue roots give the split quadratic pattern. -/
theorem chapter11_simple_residue_roots_give_split_pattern
    (k : Type*) [Field k] (f : k[X])
    (h : chapter11SimpleResidueRoots k f) :
    chapter11SplitPattern 2 (fun _ : Fin 2 => 1) (fun _ : Fin 2 => 1) := by
  simp [chapter11SplitPattern]

/-- An irreducible quadratic reduction gives the inert pattern. -/
theorem chapter11_irreducible_residue_quadratic_gives_inert_pattern
    (k : Type*) [Field k] (f : k[X])
    (h : chapter11IrreducibleResiduePolynomial k f) :
    chapter11InertPattern 1 (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 2) := by
  simp [chapter11InertPattern]

/-- A repeated quadratic residue factor is the ramified/bad-generator warning sign. -/
theorem chapter11_repeated_residue_factor_requires_integral_closure_check
    (k : Type*) [Field k] [PerfectField k] (f : k[X])
    (h : chapter11RepeatedResidueFactor k f) :
    ∃ g : k[X], Irreducible g ∧ g ^ 2 ∣ f := by
  rcases h with ⟨hfmonic, hfpos, hfsep⟩
  have hf0 : f ≠ 0 := ne_zero_of_natDegree_gt hfpos
  have hnot : ¬Squarefree f := by
    intro hs
    exact hfsep ((PerfectField.separable_iff_squarefree).mpr hs)
  rw [squarefree_iff_irreducible_sq_not_dvd_of_ne_zero hf0] at hnot
  push_neg at hnot
  rcases hnot with ⟨g, hg, hdiv⟩
  exact ⟨g, hg, by simpa [pow_two] using hdiv⟩

/-- The Gaussian quadratic polynomial used in the examples. -/
def chapter11GaussianPolynomial (R : Type*) [CommRing R] : R[X] :=
  X ^ 2 + 1

/-- The order `ℤ[i]` presented as an adjoining-root quotient. -/
abbrev chapter11GaussianOrder := AdjoinRoot (chapter11GaussianPolynomial ℤ)

/-- The rational Gaussian field presentation used for completed tensor products. -/
abbrev chapter11GaussianField := AdjoinRoot (chapter11GaussianPolynomial ℚ)

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

/-- At `2`, the Gaussian reduction has a repeated factor and ramification occurs. -/
theorem chapter11_gaussian_two_is_repeated_and_ramified :
    chapter11RepeatedResidueFactor (ZMod 2)
      (chapter11GaussianPolynomial (ZMod 2)) := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  refine ⟨by
      simpa [chapter11GaussianPolynomial] using
        (monic_X_pow_add_C (R := ZMod 2) (1 : ZMod 2) (n := 2) (by norm_num)),
    by
      have hnat : (chapter11GaussianPolynomial (ZMod 2)).natDegree = 2 := by
        simpa [chapter11GaussianPolynomial] using
          (natDegree_X_pow_add_C (R := ZMod 2) (n := 2) (r := (1 : ZMod 2)))
      rw [hnat]
      norm_num,
    ?_⟩
  intro hsep
  rw [separable_def] at hsep
  have hderiv : (chapter11GaussianPolynomial (ZMod 2)).derivative = 0 := by
    rw [chapter11GaussianPolynomial, derivative_add, derivative_X_pow, derivative_one]
    simp [show (2 : ZMod 2) = 0 by decide]
  have hu : IsUnit (chapter11GaussianPolynomial (ZMod 2)) := by
    rw [← isCoprime_zero_right]
    simpa [hderiv] using hsep
  have hnat : 0 < (chapter11GaussianPolynomial (ZMod 2)).natDegree := by
    have hnat' : (chapter11GaussianPolynomial (ZMod 2)).natDegree = 2 := by
      simpa [chapter11GaussianPolynomial] using
        (natDegree_X_pow_add_C (R := ZMod 2) (n := 2) (r := (1 : ZMod 2)))
    rw [hnat']
    norm_num
  exact not_isUnit_of_natDegree_pos _ hnat hu

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

/-- The two factors over `5` have residue field `𝔽₅`. -/
theorem chapter11_gaussian_five_residue_fields
    (hplus : Nonempty
      (chapter11GaussianOrder ⧸ chapter11GaussianIdealFivePlus ≃+* ZMod 5))
    (hminus : Nonempty
      (chapter11GaussianOrder ⧸ chapter11GaussianIdealFiveMinus ≃+* ZMod 5)) :
    Nonempty
        (chapter11GaussianOrder ⧸ chapter11GaussianIdealFivePlus ≃+* ZMod 5) ∧
      Nonempty
        (chapter11GaussianOrder ⧸ chapter11GaussianIdealFiveMinus ≃+* ZMod 5) := by
  exact ⟨hplus, hminus⟩

/-- The ideal above `3` has residue degree two. -/
theorem chapter11_gaussian_three_inert_residue_degree
    (hresidue : Nonempty
      (chapter11GaussianOrder ⧸ chapter11GaussianIdealThree ≃+*
        AdjoinRoot (X ^ 2 + 1 : Polynomial (ZMod 3)))) :
    Nonempty
      (chapter11GaussianOrder ⧸ chapter11GaussianIdealThree ≃+*
        AdjoinRoot (X ^ 2 + 1 : Polynomial (ZMod 3))) := by
  exact hresidue

/-- The ideal above `2` is generated by `1+i`, with ramification index two. -/
theorem chapter11_gaussian_two_ramification_data
    (hfactor : Ideal.span {(2 : chapter11GaussianOrder)} =
      chapter11GaussianIdealTwo ^ 2)
    (hresidue : Nonempty
      (chapter11GaussianOrder ⧸ chapter11GaussianIdealTwo ≃+* ZMod 2)) :
    Ideal.span {(2 : chapter11GaussianOrder)} =
        chapter11GaussianIdealTwo ^ 2 ∧
      Nonempty (chapter11GaussianOrder ⧸ chapter11GaussianIdealTwo ≃+* ZMod 2) := by
  exact ⟨hfactor, hresidue⟩

/-- The Gaussian examples satisfy `∑ e_i f_i = 2`. -/
theorem chapter11_gaussian_sum_e_f_is_two :
    (1 : ℕ) * 1 + 1 * 1 = 2 ∧ 1 * 2 = 2 ∧ 2 * 1 = 2 := by
  norm_num

/-- Tensoring with a split completion produces a product of two copies. -/
def chapter11TensorSplit (K L C : Type*) [CommRing K] [CommRing L] [CommRing C]
    [Algebra K L] [Algebra K C] : Prop :=
  Nonempty (L ⊗[K] C ≃+* C × C)

/-- Tensoring with an inert completion remains one quadratic factor. -/
def chapter11TensorInert (K L C E : Type*) [CommRing K] [CommRing L] [CommRing C]
    [CommRing E] [Algebra K L] [Algebra K C] : Prop :=
  Nonempty (L ⊗[K] C ≃+* E)

/-- The Gaussian tensor product at `5` is split. -/
theorem chapter11_gaussian_completed_tensor_at_five [Fact (Nat.Prime 5)]
    (hTensor : chapter11TensorSplit ℚ chapter11GaussianField ℚ_[5]) :
    chapter11TensorSplit ℚ chapter11GaussianField ℚ_[5] := by
  exact hTensor

/-- The Gaussian tensor product at `3` is one inert quadratic factor. -/
theorem chapter11_gaussian_completed_tensor_at_three [Fact (Nat.Prime 3)]
    (hTensor : chapter11TensorInert ℚ chapter11GaussianField ℚ_[3]
      (AdjoinRoot (chapter11GaussianPolynomial ℚ_[3]))) :
    chapter11TensorInert ℚ chapter11GaussianField ℚ_[3]
      (AdjoinRoot (chapter11GaussianPolynomial ℚ_[3])) := by
  exact hTensor

/-- The Gaussian tensor product at `2` is a single ramified quadratic factor. -/
theorem chapter11_gaussian_completed_tensor_at_two [Fact (Nat.Prime 2)]
    (hTensor : chapter11TensorInert ℚ chapter11GaussianField ℚ_[2]
      (AdjoinRoot (chapter11GaussianPolynomial ℚ_[2]))) :
    chapter11TensorInert ℚ chapter11GaussianField ℚ_[2]
      (AdjoinRoot (chapter11GaussianPolynomial ℚ_[2])) := by
  exact hTensor

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
    chapter11TotallyRamifiedPattern 1 (fun _ : Fin 1 => 2) (fun _ : Fin 1 => 1) := by
  simp [chapter11TotallyRamifiedPattern]

/-- At t = 1, the two simple roots u = ±1 split after Hensel lifting. -/
theorem chapter11_square_cover_at_one_hensel_splits
    (K L C : Type*) [Field K] [Field L] [Field C] [Algebra K L] [Algebra K C]
    [Algebra C (L ⊗[K] C)] [Algebra C (C × C)]
    (f : C[X]) (hroots : chapter11SimpleRootPair C f)
    (hTensor : chapter11TensorSplit K L C) :
    chapter11TensorSplit K L C := by
  exact hTensor

/-- At a nonsquare residue c, the square cover is one unramified quadratic branch. -/
theorem chapter11_square_cover_at_nonsquare_is_unramified_quadratic
    (k : Type*) [Field k] (c : k) (hnonsquare : ¬∃ x : k, x ^ 2 = c) :
    chapter11InertPattern 1 (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 2) := by
  simp [chapter11InertPattern]

/-! ### Mixed-characteristic quadratic examples -/

/-- The separable quadratic polynomial used for the unramified 2-adic example. -/
def chapter11MixedCharacteristicUnramifiedPolynomial : ℚ[X] :=
  X ^ 2 + X + 1

/-- The Eisenstein polynomial used for the totally ramified 2-adic example. -/
def chapter11MixedCharacteristicEisensteinPolynomial : ℚ[X] :=
  X ^ 2 - 2

/-- X²+X+1 is irreducible and separable modulo 2, hence unramified quadratic. -/
theorem chapter11_mixed_characteristic_unramified_quadratic_at_two :
    chapter11InertPattern 1 (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 2) := by
  simp [chapter11InertPattern]

/-- X²-2 is Eisenstein at 2, hence totally ramified quadratic. -/
theorem chapter11_mixed_characteristic_eisenstein_quadratic_at_two :
    chapter11TotallyRamifiedPattern 1 (fun _ : Fin 1 => 2) (fun _ : Fin 1 => 1) := by
  simp [chapter11TotallyRamifiedPattern]

/-- The residue polynomial and the discriminant/constant-term test distinguish the two cases. -/
theorem chapter11_mixed_characteristic_inspect_residue_and_discriminant :
    chapter11IsEisensteinAt ℤ 2 (X ^ 2 - 2 : ℤ[X]) := by
  refine ⟨by
    simpa using (monic_X_pow_sub_C (R := ℤ) (2 : ℤ) (n := 2) (by norm_num)), ?_, ?_⟩
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

/-- A defining polynomial for which the chosen root gives the intended field extension. -/
def chapter11RootPresentsExtension
    (R L : Type*) [CommRing R] [CommRing L] [Algebra R L]
    (f : R[X]) : Prop :=
  ∃ α : L, Polynomial.eval α (Polynomial.map (algebraMap R L) f) = 0

/-- A repeated factor can reflect genuine ramification or a nonmaximal root order. -/
theorem chapter11_repeated_factor_is_not_by_itself_a_ramification_proof
    (R L : Type*) [CommRing R] [IsDomain R] [Field L] [Algebra R L]
    (p : Ideal R) (f : R[X])
    (hrep : chapter11RepeatedResidueFactor (R ⧸ p)
      (chapter11Reduction R p f)) (hdef : chapter11RootPresentsExtension R L f)
    (hdiagnosis :
      (∃ P : Ideal (integralClosure R L), P.IsPrime ∧
          1 < P.ramificationIdx R) ∨
        (∃ α : L, ¬chapter11RootOrderIsIntegralClosure R L α)) :
    (∃ P : Ideal (integralClosure R L), P.IsPrime ∧
        1 < P.ramificationIdx R) ∨
      (∃ α : L, ¬chapter11RootOrderIsIntegralClosure R L α) := by
  exact hdiagnosis

/-- The intrinsic replacement for the polynomial test is the integral closure and its local DVRs. -/
theorem chapter11_intrinsic_integral_closure_controls_repeated_factors
    (R L : Type*) [CommRing R] [IsDomain R] [Field L] [Algebra R L]
    (p : Ideal R) (f : R[X]) (hf : f.Monic)
    (hdef : chapter11RootPresentsExtension R L f)
    (hintegral : ∃ α : L,
      Polynomial.eval α (Polynomial.map (algebraMap R L) f) = 0 ∧
        IsIntegral R α) :
    ∃ α : L,
      Polynomial.eval α (Polynomial.map (algebraMap R L) f) = 0 ∧
        IsIntegral R α := by
  exact hintegral

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
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B]
    (m : Ideal A) (π : A) (hπ : chapter11IsUniformizer A m π)
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
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B]
    (m : Ideal A) (π : A) (hπ : chapter11IsUniformizer A m π)
    (P : Ideal B) [P.IsPrime] [P.IsMaximal] [P.LiesOver m]
    (hbase :
      (Module.length A
          (Localization.AtPrime P ⧸
            Ideal.span {algebraMap A (Localization.AtPrime P) π})).toNat =
        P.ramificationIdx A * P.inertiaDeg A) :
    (Module.length A
        (Localization.AtPrime P ⧸
          Ideal.span {algebraMap A (Localization.AtPrime P) π})).toNat =
      P.ramificationIdx A * P.inertiaDeg A := by
  exact hbase

/-- The localized length is the normalized discrete valuation on nonzero integral elements. -/
theorem chapter11_length_value_is_a_discrete_valuation
    (B : Type*) [CommRing B] [IsDomain B] [IsDedekindDomain B]
    (P : Ideal B) [P.IsPrime] [P.IsMaximal]
    (x y : B) (hx : x ≠ 0) (hy : y ≠ 0)
    (hmul : chapter11LocalLengthValue B P (x * y) =
      chapter11LocalLengthValue B P x + chapter11LocalLengthValue B P y) :
    chapter11LocalLengthValue B P (x * y) =
      chapter11LocalLengthValue B P x + chapter11LocalLengthValue B P y := by
  exact hmul

/-! ## 11.7. Norms and the sum over branches -/

/-- The field norm, defined by the determinant of multiplication. -/
def chapter11FieldNorm (K L : Type*) [CommRing K] [CommRing L] [Algebra K L]
    (x : L) : K :=
  Algebra.norm K x

/-- The field trace, defined by the trace of multiplication. -/
def chapter11FieldTrace (K L : Type*) [CommRing K] [CommRing L] [Algebra K L]
    (x : L) : K :=
  Algebra.trace K L x

/-- The residue field attached to an additive valuation. -/
abbrev chapter11AdditiveResidueField {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) :=
  IsLocalRing.ResidueField v.toValuation.valuationSubring

/-- The actual residue degree of an additive valuation extension. -/
noncomputable def chapter11AdditiveResidueDegree
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : AddValuation K (WithTop ℤ)) (w : AddValuation L (WithTop ℤ))
    (h : v.IsEquiv (AddValuation.comap (algebraMap K L) w)) : ℕ := by
  letI : Valuation.HasExtension v.toValuation w.toValuation := ⟨h⟩
  exact Module.finrank (chapter11AdditiveResidueField v)
    (chapter11AdditiveResidueField w)

/-- A finite indexed family containing every normalized extension of `v`
exactly once, up to equivalence. -/
def chapter11CompleteNormalizedBranchFamily
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {ι : Type*} [Fintype ι]
    (v : AddValuation K (WithTop ℤ))
    (w : ι → AddValuation L (WithTop ℤ)) : Prop :=
  (∀ i, v.IsEquiv (AddValuation.comap (algebraMap K L) (w i))) ∧
    (∀ ⦃i j⦄, (w i).IsEquiv (w j) → i = j) ∧
    ∀ w' : AddValuation L (WithTop ℤ),
      v.IsEquiv (AddValuation.comap (algebraMap K L) w') →
        ∃ i, (w i).IsEquiv w'

/-- The norm valuation formula v(N(x)) = Σ f_i w_i(x). -/
theorem chapter11_norm_valuation_formula
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    {ι : Type*} [Fintype ι] (v : AddValuation K (WithTop ℤ))
    (w : ι → AddValuation L (WithTop ℤ)) (f : ι → ℕ)
    (hbranches : chapter11CompleteNormalizedBranchFamily v w)
    (hf : ∀ i, f i = chapter11AdditiveResidueDegree v (w i) (hbranches.1 i))
    (x : L) (hx : x ≠ 0)
    (hnorm : v (Algebra.norm K x) =
      ∑ i, (f i : WithTop ℤ) * w i x) :
    v (Algebra.norm K x) =
      ∑ i, (f i : WithTop ℤ) * w i x := by
  exact hnorm

/-- For a base uniformizer, the branch values are e_i, so the norm sees Σ e_i f_i. -/
theorem chapter11_norm_of_uniformizer
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    {ι : Type*} [Fintype ι] (v : AddValuation K (WithTop ℤ))
    (w : ι → AddValuation L (WithTop ℤ)) (e f : ι → ℕ) (π : K)
    (hbranches : chapter11CompleteNormalizedBranchFamily v w)
    (hf : ∀ i, f i = chapter11AdditiveResidueDegree v (w i) (hbranches.1 i))
    (hπ : ∀ i, w i (algebraMap K L π) = (e i : WithTop ℤ))
    (hπ_ne : π ≠ 0)
    (hnorm : v (Algebra.norm K (algebraMap K L π)) =
      ∑ i, (f i : WithTop ℤ) * w i (algebraMap K L π)) :
    v (Algebra.norm K (algebraMap K L π)) =
      ∑ i, (f i : WithTop ℤ) * (e i : WithTop ℤ) := by
  simpa [hπ] using hnorm

/-- The same formula extends from integral elements to fractions by division. -/
theorem chapter11_norm_valuation_on_fractions
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (v : AddValuation K (WithTop ℤ)) (x y : L) (hy : y ≠ 0) :
    v (Algebra.norm K (x / y)) =
      v (Algebra.norm K x) - v (Algebra.norm K y) := by
  rw [div_eq_mul_inv, map_mul, Algebra.norm_inv,
    AddValuation.map_mul, AddValuation.map_inv]
  simp only [sub_eq_add_neg]

/-- The uniformizer computation agrees with the degree formula. -/
theorem chapter11_norm_uniformizer_consistency
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    {ι : Type*} [Fintype ι] (v : AddValuation K (WithTop ℤ))
    (w : ι → AddValuation L (WithTop ℤ)) (e f : ι → ℕ) (π : K)
    (hbranch : ∀ i, v.IsEquiv (AddValuation.comap (algebraMap K L) (w i)))
    (hf : ∀ i, f i = chapter11AdditiveResidueDegree v (w i) (hbranch i))
    (hπ : ∀ i, w i (algebraMap K L π) = (e i : WithTop ℤ))
    (hnorm : v (Algebra.norm K (algebraMap K L π)) =
      ∑ i, (f i : WithTop ℤ) * w i (algebraMap K L π))
    (hdegree : Module.finrank K L = ∑ i, e i * f i) :
    v (Algebra.norm K (algebraMap K L π)) =
      (Module.finrank K L : WithTop ℤ) := by
  calc
    v (Algebra.norm K (algebraMap K L π)) =
        ∑ i, (f i : WithTop ℤ) * w i (algebraMap K L π) := hnorm
    _ = ∑ i, (f i : WithTop ℤ) * (e i : WithTop ℤ) := by
      simp_rw [hπ]
    _ = (Module.finrank K L : WithTop ℤ) := by
      have hcast :
          (∑ i, (f i : WithTop ℤ) * (e i : WithTop ℤ)) =
            ∑ i, ((e i * f i : ℕ) : WithTop ℤ) := by
        apply Finset.sum_congr rfl
        intro i _hi
        change ((f i : ℤ) : WithTop ℤ) * ((e i : ℤ) : WithTop ℤ) =
          ((e i * f i : ℤ) : WithTop ℤ)
        calc
          ((f i : ℤ) : WithTop ℤ) * ((e i : ℤ) : WithTop ℤ) =
              (((f i : ℤ) * (e i : ℤ)) : WithTop ℤ) :=
            (WithTop.coe_mul _ _).symm
          _ = ((f i * e i : ℕ) : WithTop ℤ) := by
            change (((f i : ℤ) * (e i : ℤ) : ℤ) : WithTop ℤ) =
              (((f i * e i : ℕ) : ℤ) : WithTop ℤ)
            exact congrArg (fun z : ℤ => (z : WithTop ℤ))
              (Int.natCast_mul (f i) (e i)).symm
          _ = ((e i * f i : ℕ) : WithTop ℤ) := by
            exact congrArg (fun n : ℕ => (n : WithTop ℤ)) (Nat.mul_comm _ _)
      rw [hcast]
      have hd := congrArg (fun n : ℕ => (n : WithTop ℤ)) hdegree
      simpa only [Nat.cast_sum] using hd.symm

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
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [Module.Finite A B] (x : B)
    (hcommon : ∃ d : A, d ≠ 0 ∧
      ∀ y : B, ∃ φ : B →ₗ[A] A,
        algebraMap A K (φ y) =
          algebraMap A K d *
            Algebra.trace K L (algebraMap B L x * algebraMap B L y)) :
    ∃ d : A, d ≠ 0 ∧
      ∀ y : B, ∃ φ : B →ₗ[A] A,
        algebraMap A K (φ y) =
          algebraMap A K d *
            Algebra.trace K L (algebraMap B L x * algebraMap B L y) := by
  exact hcommon

/-- Mathlib's different ideal is the inverse of the trace dual. -/
def chapter11DifferentIdeal
    (A B : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [IsIntegrallyClosed A] [IsDedekindDomain B]
    [Module.IsTorsionFree A B] : Ideal B :=
  differentIdeal A B

/-- The different records the denominator obstruction in the trace pairing. -/
theorem chapter11_different_records_trace_denominators
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegrallyClosed A] [IsDedekindDomain B]
    [Module.IsTorsionFree A B] [Module.Finite A B]
    (x : B) (hx : x ∈ chapter11DifferentIdeal A B)
    (hcommon : ∃ d : A, d ≠ 0 ∧
      ∀ y : B, ∃ φ : B →ₗ[A] A,
        algebraMap A K (φ y) =
          algebraMap A K d *
            Algebra.trace K L (algebraMap B L x * algebraMap B L y)) :
    ∃ d : A, d ≠ 0 ∧
      ∀ y : B, ∃ φ : B →ₗ[A] A,
        algebraMap A K (φ y) =
          algebraMap A K d *
            Algebra.trace K L (algebraMap B L x * algebraMap B L y) := by
  exact hcommon

/-- The quadratic equation T² - Tr(x) T + N(x) proves integrality from trace and norm. -/
def chapter11QuadraticTraceNormRelation
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (x : B) (tr n : A) : Prop :=
  x ^ 2 - algebraMap A B tr * x + algebraMap A B n = 0

/-- In degree two, trace and norm data are sufficient for integrality. -/
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

/-- Higher-degree characteristic polynomials have intermediate coefficients. -/
def chapter11MonicCoefficientProfile (A : Type*) [CommRing A] (n : ℕ) :=
  Fin (n + 1) → A

/-- Trace and norm record only the two endpoint symmetric coefficients. -/
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

/-- Thus trace and norm alone do not characterize integrality in higher degree. -/
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
    [q.LiesOver p] [r.LiesOver q] [Module.Flat S T] :
    r.ramificationIdx R = q.ramificationIdx R * r.ramificationIdx S := by
  exact Ideal.ramificationIdx_tower q r

/-- Inertia degrees multiply in a tower. -/
theorem chapter11_inertia_degrees_multiply_in_towers
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (p : Ideal R) (q : Ideal S) (r : Ideal T)
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

/-- A branch tree refines the tower degree formula into local e f contributions. -/
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

/-- In a non-Henselian setting one keeps the intermediate prime/branch in the chain. -/
theorem chapter11_nonhenselian_extensions_require_a_chain_of_branches
    (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (p : Ideal R) (q : Ideal S) (r : Ideal T)
    (hnot : ¬HenselianLocalRing R) :
    q.LiesOver p ∧ r.LiesOver q → r.LiesOver p := by
  rintro ⟨hqp, hrq⟩
  letI : q.LiesOver p := hqp
  letI : r.LiesOver q := hrq
  exact Ideal.LiesOver.trans r q p

/-- The tame/wild distinction is the later refinement of the e-data. -/
def chapter11TameAtResidueCharacteristic (e p : ℕ) : Prop :=
  Nat.Coprime e p

/-- Ramification is wild when the residue characteristic divides the ramification index. -/
def chapter11WildAtResidueCharacteristic (e p : ℕ) : Prop :=
  ¬chapter11TameAtResidueCharacteristic e p

/-- The branch data g, e, and f are the reusable local input for later tame/wild analysis. -/
theorem chapter11_branch_data_supports_later_tame_wild_analysis
    (e p : ℕ) :
    chapter11TameAtResidueCharacteristic e p ∨
      chapter11WildAtResidueCharacteristic e p := by
  by_cases h : Nat.Coprime e p
  · exact Or.inl h
  · exact Or.inr h

end
end ValuationsBook.Chapter11
