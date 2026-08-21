import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section04RamificationIndexAndResidueDegree
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section01TheExtensionProblem
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Finite

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter10

universe u10K u10L u10Γ u10Kh u10ΓL

open scoped BigOperators TensorProduct WithZero
open Polynomial

noncomputable section

/-!
# Chapter 10: Extensions of valuations

This file is a statement-generation formalization of Sections 10.1--10.7 of
Book 1.  The declarations deliberately keep the valuation-theoretic data
explicit: this makes the extension, residue, and ramification assertions
usable independently of the other generated chapters.
-/

/-! # Book 1, Chapter 10, Section 10.5: Several Extensions and the Fundamental Equality
-/

/-! ## 10.5. Several extensions and the fundamental equality -/

/-- The numerical data attached to one branch.  `degree` is the local `e f`
contribution, not the degree of the whole extension. -/
structure Chapter10BranchInvariant where
  degree : ℕ
  e : ℕ
  f : ℕ

/-- The contribution ef of one branch. -/
def Chapter10BranchContribution (p : Chapter10BranchInvariant) : ℕ :=
  p.e * p.f

/-- A valuation branch together with its numerical profile. -/
structure Chapter10ValuationBranch {K L ΓK : Type*} [Field K] [Field L]
    [Algebra K L] [LinearOrderedCommGroupWithZero ΓK] [FiniteDimensional K L]
    (v : Valuation K ΓK) where
  extension : Chapter10HeterogeneousValuationExtension L v
  extensionData : Chapter10HeterogeneousExtensionData
    v extension.valuation extension.isExtension
  profile : Chapter10BranchInvariant
  profile_e : profile.e = extensionData.ramificationIndex
  profile_f : profile.f = extensionData.residueDegree

namespace Chapter10ValuationBranch

abbrev valueGroup
    {K L ΓK : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK] [FiniteDimensional K L]
    {v : Valuation K ΓK}
    (b : Chapter10ValuationBranch (K := K) (L := L) v) :=
  b.extension.valueGroup

abbrev w
    {K L ΓK : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK] [FiniteDimensional K L]
    {v : Valuation K ΓK}
    (b : Chapter10ValuationBranch (K := K) (L := L) v) :=
  b.extension.valuation

instance
    {K L ΓK : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK] [FiniteDimensional K L]
    {v : Valuation K ΓK}
    (b : Chapter10ValuationBranch (K := K) (L := L) v) :
    LinearOrderedCommGroupWithZero b.valueGroup :=
  b.extension.orderedValueGroup

end Chapter10ValuationBranch

/-! A family must contain one representative of each equivalence class, not
merely at least one representative.  The latter condition alone would allow
the same branch to be counted repeatedly in the fundamental sum. -/
/-- Equivalence of two explicitly chosen valuation branches. -/
def Chapter10BranchesEquivalent
    {K L ΓK : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK] [FiniteDimensional K L]
    {v : Valuation K ΓK}
    (b₁ b₂ : Chapter10ValuationBranch (K := K) (L := L) v) : Prop :=
  b₁.w.IsEquiv b₂.w

/-- A finite list of branches containing every inequivalent extension. -/
def Chapter10CompleteBranchFamily
    {K L ΓK : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK] [FiniteDimensional K L]
    (v : Valuation K ΓK)
    (S : Finset (Chapter10ValuationBranch (K := K) (L := L) v)) : Prop :=
  (∀ (ΓL : Type*) [LinearOrderedCommGroupWithZero ΓL]
      (w : Valuation L ΓL),
    v.IsEquiv (w.comap (algebraMap K L)) ↔
    ∃ b, b ∈ S ∧
        b.w.IsEquiv w) ∧
    (∀ b₁ ∈ S, ∀ b₂ ∈ S,
      b₁ ≠ b₂ → ¬ Chapter10BranchesEquivalent b₁ b₂)

/-- A branch profile records the local contribution `e f`, together with the
ramification and residue data supplied by its extension branch. -/
def Chapter10BranchProfileCorrect
    {K L ΓK : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK] [FiniteDimensional K L]
    (v : Valuation K ΓK)
    (b : Chapter10ValuationBranch (K := K) (L := L) v) : Prop :=
  b.profile.degree = Chapter10BranchContribution b.profile ∧
    b.profile.e = b.extensionData.ramificationIndex ∧
    b.profile.f = b.extensionData.residueDegree

/-- Residue degree as a function of the explicit extension equivalence. -/
noncomputable def Chapter10ResidueDegreeOfExtension
    {K L ΓK ΓL : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓL]
    [FiniteDimensional K L]
    (v : Valuation K ΓK) (w : Valuation L ΓL)
    (h : v.IsEquiv (w.comap (algebraMap K L))) : ℕ := by
  let : Valuation.HasExtension v w := ⟨h⟩
  exact Chapter10ResidueDegree v w

/-- An immediate valuation extension has surjective induced value-group map and
bijective residue-field map.  The maps, rather than literal equality of value
group subtypes, are used because equivalent valuations may have different
ordered codomains or different normalizations. -/
def Chapter10ImmediateValuationExtension
    {K L ΓK ΓL : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓL]
    [FiniteDimensional K L]
    (v : Valuation K ΓK) (w : Valuation L ΓL)
    (h : v.IsEquiv (w.comap (algebraMap K L)))
    (d : Chapter10HeterogeneousExtensionData v w h) : Prop := by
  letI : Valuation.HasExtension v w := ⟨h⟩
  exact Function.Surjective d.valueGroupMap ∧
    Function.Bijective (Chapter10ResidueFieldMap v w)

/-- Tensoring a finite extension with a field extension preserves its dimension. -/
theorem chapter10_henselized_tensor_dimension
    {K L Kh : Type*} [Field K] [Field L] [Field Kh]
    [Algebra K L] [Algebra K Kh]
    [FiniteDimensional K L] :
    Module.finrank Kh (Kh ⊗[K] L) = Module.finrank K L := by
  exact Module.finrank_baseChange (R := Kh) (S := K) (M' := L)

/-- The base-change tensor product used to separate the branches. -/
abbrev Chapter10HenselizedTensor (K L Kh : Type*) [CommRing K] [CommRing L]
    [CommRing Kh] [Algebra K L] [Algebra K Kh] : Type _ := L ⊗[K] Kh

/-- Maximal ideals of an algebra are the local-factor indices. -/
def Chapter10TensorMaximalIdeals {C : Type*} [CommRing C] : Set (Ideal C) :=
  {P | P.IsMaximal}

/-- A local factor contribution is represented by linearly independent vectors
in the corresponding residue factor.  This is the structural input used to
derive the numerical local bound; the bound itself is not stored as data. -/
def Chapter10FactorContributionIndependent
    {K L Kh : Type*} [Field K] [Field L] [Field Kh]
    [Algebra K L] [Algebra K Kh]
    (P : Ideal (L ⊗[K] Kh)) (n : ℕ) : Prop := by
  letI : Algebra Kh (L ⊗[K] Kh) := Algebra.TensorProduct.rightAlgebra
  exact ∃ f : Fin n → (L ⊗[K] Kh) ⧸ P, LinearIndependent Kh f

/-- The dimension of a maximal tensor factor, using its canonical right-field
algebra structure. -/
def Chapter10TensorFactorDimension
    {K L Kh : Type*} [Field K] [Field L] [Field Kh]
    [Algebra K L] [Algebra K Kh]
    (P : Ideal (L ⊗[K] Kh)) : ℕ := by
  letI : Algebra Kh (L ⊗[K] Kh) := Algebra.TensorProduct.rightAlgebra
  exact Module.finrank Kh ((L ⊗[K] Kh) ⧸ P)

/-- Independent vectors in a finite tensor factor give the corresponding
dimension bound. -/
theorem chapter10_factor_contribution_le_factor_dimension
    {K L Kh : Type*} [Field K] [Field L] [Field Kh]
    [Algebra K L] [Algebra K Kh] [FiniteDimensional K L]
    (P : Ideal (L ⊗[K] Kh)) (n : ℕ)
    (h : Chapter10FactorContributionIndependent P n) :
    n ≤ Chapter10TensorFactorDimension P := by
  let : Algebra Kh (L ⊗[K] Kh) := Algebra.TensorProduct.rightAlgebra
  let : Module.Finite Kh (L ⊗[K] Kh) :=
    Module.Finite.equiv (Algebra.TensorProduct.commRight K Kh L).toLinearEquiv
  simpa [Chapter10FactorContributionIndependent, Chapter10TensorFactorDimension] using
    (show ∃ f : Fin n → (L ⊗[K] Kh) ⧸ P, LinearIndependent Kh f from h).choose_spec.fintype_card_le_finrank

/-! A finite henselized tensor separates the inequivalent heterogeneous
valuation branches.  The package below keeps the branch-to-factor
correspondence and the value/residue contributions explicit. -/

/-- A finite maximal-factor index for the henselized tensor, together with the
branch data and the local contribution carried by each factor. -/
structure Chapter10HenselizedTensorBranchCorrespondence
    {K : Type u10K} {L : Type u10L} {Kh : Type u10Kh} {ΓK : Type u10Γ}
    [Field K] [Field L] [Field Kh]
    [Algebra K L] [Algebra K Kh] [FiniteDimensional K L]
    [LinearOrderedCommGroupWithZero ΓK]
    [Algebra Kh (L ⊗[K] Kh)] [Module.Finite Kh (L ⊗[K] Kh)]
    (v : Valuation K ΓK)
    (S : Finset (Chapter10ValuationBranch (K := K) (L := L) v)) where
  complete : Chapter10CompleteBranchFamily.{u10K, u10L, u10Γ, u10ΓL} v S
  factors : Finset (Ideal (L ⊗[K] Kh))
  factors_maximal : ∀ P ∈ factors, P.IsMaximal
  factors_exhaustive : ∀ P, P.IsMaximal ↔ P ∈ factors
  branchFactor : {b // b ∈ S} ≃ {P // P ∈ factors}
  factorRamification : {P // P ∈ factors} → ℕ
  factorResidueDegree : {P // P ∈ factors} → ℕ
  branch_ramification :
    ∀ b, factorRamification (branchFactor b) =
      Nat.card (Chapter10ValueGroup b.1.w ⧸
        b.1.extensionData.valueGroupMap.range)
  branch_residue :
    ∀ b, factorResidueDegree (branchFactor b) =
      Chapter10HeterogeneousResidueDegree v b.1.w b.1.extension.isExtension
  branch_profile :
    ∀ b, b.1.profile.e = factorRamification (branchFactor b) ∧
      b.1.profile.f = factorResidueDegree (branchFactor b)
  factorContributionIndependent :
    ∀ b : {b // b ∈ S},
      Chapter10FactorContributionIndependent (branchFactor b).1
        (Chapter10BranchContribution b.1.profile)

private theorem chapter10_henselized_tensor_factor_dimensions_bound
    {K L Kh : Type*} [Field K] [Field L] [Field Kh]
    [Algebra K L] [Algebra K Kh]
    [FiniteDimensional K L]
    (factors : Finset (Ideal (L ⊗[K] Kh)))
    (hmax : ∀ P ∈ factors, P.IsMaximal)
    (hexhaustive : ∀ P, P.IsMaximal ↔ P ∈ factors) :
    (letI : Algebra Kh (L ⊗[K] Kh) := Algebra.TensorProduct.rightAlgebra
     Finset.sum factors
         (fun P => Module.finrank Kh ((L ⊗[K] Kh) ⧸ P)) ≤
       Module.finrank K L) := by
  let : Algebra Kh (Kh ⊗[K] L) := Algebra.TensorProduct.leftAlgebra
  let : Algebra Kh (L ⊗[K] Kh) := Algebra.TensorProduct.rightAlgebra
  let : Module.Finite Kh (Kh ⊗[K] L) :=
    Module.Finite.base_change (R := K) (A := Kh) (M := L)
  let : Module.Finite Kh (L ⊗[K] Kh) :=
    Module.Finite.equiv (Algebra.TensorProduct.commRight K Kh L).toLinearEquiv
  let : IsArtinianRing (L ⊗[K] Kh) :=
    IsArtinianRing.of_finite Kh (L ⊗[K] Kh)
  let : Finite (PrimeSpectrum (L ⊗[K] Kh)) := inferInstance
  let : Fintype (PrimeSpectrum (L ⊗[K] Kh)) := Fintype.ofFinite _
  have hdim := IsArtinianRing.finrank_eq_sum_primeSpectrum
    (L ⊗[K] Kh) Kh
  have hquot (p : PrimeSpectrum (L ⊗[K] Kh)) :
      Module.finrank Kh ((L ⊗[K] Kh) ⧸ p.asIdeal) ≤
        Module.finrank Kh (Localization.AtPrime p.asIdeal) := by
    let : p.asIdeal.IsMaximal := by
      rw [← IsArtinianRing.isPrime_iff_isMaximal]
      exact p.isPrime
    let f : (L ⊗[K] Kh) →ₐ[Kh] ((L ⊗[K] Kh) ⧸ p.asIdeal) :=
      Ideal.Quotient.mkₐ Kh p.asIdeal
    have hf : ∀ y : p.asIdeal.primeCompl, IsUnit (f y) := by
      intro y
      let : Field ((L ⊗[K] Kh) ⧸ p.asIdeal) := Ideal.Quotient.field p.asIdeal
      change IsUnit (Ideal.Quotient.mk p.asIdeal y)
      rw [isUnit_iff_ne_zero, ne_eq, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_primeCompl_iff.mp y.property
    let g : Localization.AtPrime p.asIdeal →ₐ[Kh]
        ((L ⊗[K] Kh) ⧸ p.asIdeal) :=
      IsLocalization.liftAlgHom hf
    have hg : Function.Surjective g := by
      intro z
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective Kh p.asIdeal z
      refine ⟨algebraMap (L ⊗[K] Kh) (Localization.AtPrime p.asIdeal) x, ?_⟩
      rw [IsLocalization.liftAlgHom_apply]
      simp [f]
    let : Module.Finite Kh (Localization.AtPrime p.asIdeal) :=
      Module.Finite.of_surjective
        (IsScalarTower.toAlgHom Kh (L ⊗[K] Kh)
          (Localization.AtPrime p.asIdeal)).toLinearMap
        (IsArtinianRing.localization_surjective p.asIdeal.primeCompl
          (Localization.AtPrime p.asIdeal))
    exact LinearMap.finrank_le_finrank_of_surjective (f := g.toLinearMap) hg
  let e : {P // P ∈ factors} ≃ PrimeSpectrum (L ⊗[K] Kh) :=
    { toFun := fun P =>
        ⟨P.1, (IsArtinianRing.isPrime_iff_isMaximal P.1).mpr
          (hmax P.1 P.2)⟩
      invFun := fun p =>
        ⟨p.asIdeal, (hexhaustive p.asIdeal).mp
          ((IsArtinianRing.isPrime_iff_isMaximal p.asIdeal).mp p.isPrime)⟩
      left_inv := by
        intro P
        rfl
      right_inv := by
        intro p
        change (⟨p.asIdeal, _⟩ : PrimeSpectrum (L ⊗[K] Kh)) = p
        rfl }
  have hsum0 : Finset.sum factors (fun P =>
      Module.finrank Kh ((L ⊗[K] Kh) ⧸ P)) =
      ∑ P : {P // P ∈ factors},
        Module.finrank Kh ((L ⊗[K] Kh) ⧸ P.1) := by
    rw [Finset.sum_subtype factors (p := fun P => P ∈ factors)
      (fun P => Iff.rfl)]
  have hsum1 : (∑ P : {P // P ∈ factors},
      Module.finrank Kh ((L ⊗[K] Kh) ⧸ P.1)) =
      ∑ p : PrimeSpectrum (L ⊗[K] Kh),
        Module.finrank Kh ((L ⊗[K] Kh) ⧸ p.asIdeal) := by
    apply Fintype.sum_equiv e
    intro P
    rfl
  rw [hsum0, hsum1]
  calc
    (∑ p : PrimeSpectrum (L ⊗[K] Kh),
        Module.finrank Kh ((L ⊗[K] Kh) ⧸ p.asIdeal)) ≤
        ∑ p : PrimeSpectrum (L ⊗[K] Kh),
          Module.finrank Kh (Localization.AtPrime p.asIdeal) :=
      Finset.sum_le_sum (fun p _ => hquot p)
    _ = Module.finrank Kh (L ⊗[K] Kh) := hdim.symm
    _ = Module.finrank K L := by
      rw [← Module.finrank_baseChange (R := Kh) (S := K) (M' := L)]
      exact (Algebra.TensorProduct.commRight K Kh L).toLinearEquiv.finrank_eq.symm


/-- The branch contributions in a finite henselized tensor are bounded by the
total extension degree. -/
theorem chapter10_henselized_tensor_branch_sum_bound
    {K : Type u10K} {L : Type u10L} {Kh : Type u10Kh} {ΓK : Type u10Γ}
    [Field K] [Field L] [Field Kh]
    [Algebra K L] [Algebra K Kh] [FiniteDimensional K L]
    [LinearOrderedCommGroupWithZero ΓK]
    [Algebra Kh (L ⊗[K] Kh)] [Module.Finite Kh (L ⊗[K] Kh)]
    (v : Valuation K ΓK)
    (S : Finset (Chapter10ValuationBranch (K := K) (L := L) v))
      (D : Chapter10HenselizedTensorBranchCorrespondence.{u10K, u10L, u10Γ,
      u10Kh, u10ΓL} (K := K) (L := L) (Kh := Kh) (ΓK := ΓK) v S) :
    Finset.sum S (fun b => Chapter10BranchContribution b.profile) ≤
      Module.finrank K L := by
  classical
  have hsum0 :
      Finset.sum S (fun b => Chapter10BranchContribution b.profile) =
        ∑ b : {b // b ∈ S}, Chapter10BranchContribution b.1.profile := by
    rw [Finset.sum_subtype S (p := fun b => b ∈ S) (fun b => Iff.rfl)]
  have hle :
      (∑ b : {b // b ∈ S}, Chapter10BranchContribution b.1.profile) ≤
        ∑ b : {b // b ∈ S},
          Chapter10TensorFactorDimension (D.branchFactor b).1 := by
    exact Finset.sum_le_sum (fun b _ =>
      chapter10_factor_contribution_le_factor_dimension
        (P := (D.branchFactor b).1)
        (n := Chapter10BranchContribution b.1.profile)
        (D.factorContributionIndependent b))
  let : Fintype {P // P ∈ D.factors} := Finset.fintypeCoeSort D.factors
  have hsum1 :
      (∑ b : {b // b ∈ S},
        Chapter10TensorFactorDimension (D.branchFactor b).1) =
        ∑ P : {P // P ∈ D.factors}, Chapter10TensorFactorDimension P.1 := by
    apply Fintype.sum_equiv D.branchFactor
    intro b
    rfl
  have hsum2 :
      (∑ P : {P // P ∈ D.factors}, Chapter10TensorFactorDimension P.1) =
        Finset.sum D.factors (fun P =>
          (letI : Algebra Kh (L ⊗[K] Kh) := Algebra.TensorProduct.rightAlgebra
           Module.finrank Kh ((L ⊗[K] Kh) ⧸ P))) := by
    rw [Finset.sum_subtype D.factors (p := fun P => P ∈ D.factors)
      (fun P => Iff.rfl) (F := Finset.fintypeCoeSort D.factors)]
    rfl
  have hdim := chapter10_henselized_tensor_factor_dimensions_bound
    (K := K) (L := L) (Kh := Kh) D.factors D.factors_maximal D.factors_exhaustive
  calc
    Finset.sum S (fun b => Chapter10BranchContribution b.profile) =
        ∑ b : {b // b ∈ S}, Chapter10BranchContribution b.1.profile := hsum0
    _ ≤ ∑ b : {b // b ∈ S},
          Chapter10TensorFactorDimension (D.branchFactor b).1 := hle
    _ = ∑ P : {P // P ∈ D.factors}, Chapter10TensorFactorDimension P.1 := hsum1
    _ = Finset.sum D.factors (fun P =>
          (letI : Algebra Kh (L ⊗[K] Kh) := Algebra.TensorProduct.rightAlgebra
           Module.finrank Kh ((L ⊗[K] Kh) ⧸ P))) := hsum2
    _ ≤ Module.finrank K L := hdim

/-- The finite base-change tensor product has finitely many maximal local factors. -/
theorem chapter10_henselized_tensor_has_finitely_many_factors
    {K L Kh : Type*} [Field K] [Field L] [Field Kh]
    [Algebra K L] [Algebra K Kh] [FiniteDimensional K L]
    [Algebra Kh (L ⊗[K] Kh)] [Module.Finite Kh (L ⊗[K] Kh)]
    : Set.Finite (Chapter10TensorMaximalIdeals (C := L ⊗[K] Kh)) := by
  let : IsArtinianRing (L ⊗[K] Kh) :=
    IsArtinianRing.of_finite Kh (L ⊗[K] Kh)
  exact IsArtinianRing.setOfPred_isMaximal_finite (L ⊗[K] Kh)

/-- Residue-field dimensions of the local base-change tensor factors are bounded by the total
dimension; nilpotent Artinian multiplicities account for the possible gap. -/
theorem chapter10_henselized_tensor_factor_dimensions
    {K L Kh : Type*} [Field K] [Field L] [Field Kh]
    [Algebra K L] [Algebra K Kh]
    [FiniteDimensional K L]
    (factors : Finset (Ideal (L ⊗[K] Kh)))
    (hmax : ∀ P ∈ factors, P.IsMaximal)
    (hexhaustive : ∀ P, P.IsMaximal ↔ P ∈ factors) :
    (letI : Algebra Kh (L ⊗[K] Kh) := Algebra.TensorProduct.rightAlgebra
     Finset.sum factors
         (fun P => Module.finrank Kh ((L ⊗[K] Kh) ⧸ P)) ≤
       Module.finrank K L) := by
  let : Algebra Kh (Kh ⊗[K] L) := Algebra.TensorProduct.leftAlgebra
  let : Algebra Kh (L ⊗[K] Kh) := Algebra.TensorProduct.rightAlgebra
  let : Module.Finite Kh (Kh ⊗[K] L) :=
    Module.Finite.base_change (R := K) (A := Kh) (M := L)
  let : Module.Finite Kh (L ⊗[K] Kh) :=
    Module.Finite.equiv (Algebra.TensorProduct.commRight K Kh L).toLinearEquiv
  let : IsArtinianRing (L ⊗[K] Kh) :=
    IsArtinianRing.of_finite Kh (L ⊗[K] Kh)
  let : Finite (PrimeSpectrum (L ⊗[K] Kh)) := inferInstance
  let : Fintype (PrimeSpectrum (L ⊗[K] Kh)) := Fintype.ofFinite _
  have hdim := IsArtinianRing.finrank_eq_sum_primeSpectrum
    (L ⊗[K] Kh) Kh
  have hquot (p : PrimeSpectrum (L ⊗[K] Kh)) :
      Module.finrank Kh ((L ⊗[K] Kh) ⧸ p.asIdeal) ≤
        Module.finrank Kh (Localization.AtPrime p.asIdeal) := by
    let : p.asIdeal.IsMaximal := by
      rw [← IsArtinianRing.isPrime_iff_isMaximal]
      exact p.isPrime
    let f : (L ⊗[K] Kh) →ₐ[Kh] ((L ⊗[K] Kh) ⧸ p.asIdeal) :=
      Ideal.Quotient.mkₐ Kh p.asIdeal
    have hf : ∀ y : p.asIdeal.primeCompl, IsUnit (f y) := by
      intro y
      let : Field ((L ⊗[K] Kh) ⧸ p.asIdeal) := Ideal.Quotient.field p.asIdeal
      change IsUnit (Ideal.Quotient.mk p.asIdeal y)
      rw [isUnit_iff_ne_zero, ne_eq, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_primeCompl_iff.mp y.property
    let g : Localization.AtPrime p.asIdeal →ₐ[Kh]
        ((L ⊗[K] Kh) ⧸ p.asIdeal) :=
      IsLocalization.liftAlgHom hf
    have hg : Function.Surjective g := by
      intro z
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective Kh p.asIdeal z
      refine ⟨algebraMap (L ⊗[K] Kh) (Localization.AtPrime p.asIdeal) x, ?_⟩
      rw [IsLocalization.liftAlgHom_apply]
      simp [f]
    let : Module.Finite Kh (Localization.AtPrime p.asIdeal) :=
      Module.Finite.of_surjective
        (IsScalarTower.toAlgHom Kh (L ⊗[K] Kh)
          (Localization.AtPrime p.asIdeal)).toLinearMap
        (IsArtinianRing.localization_surjective p.asIdeal.primeCompl
          (Localization.AtPrime p.asIdeal))
    exact LinearMap.finrank_le_finrank_of_surjective (f := g.toLinearMap) hg
  let e : {P // P ∈ factors} ≃ PrimeSpectrum (L ⊗[K] Kh) :=
    { toFun := fun P =>
        ⟨P.1, (IsArtinianRing.isPrime_iff_isMaximal P.1).mpr
          (hmax P.1 P.2)⟩
      invFun := fun p =>
        ⟨p.asIdeal, (hexhaustive p.asIdeal).mp
          ((IsArtinianRing.isPrime_iff_isMaximal p.asIdeal).mp p.isPrime)⟩
      left_inv := by
        intro P
        rfl
      right_inv := by
        intro p
        change (⟨p.asIdeal, _⟩ : PrimeSpectrum (L ⊗[K] Kh)) = p
        rfl }
  have hsum0 : Finset.sum factors (fun P =>
      Module.finrank Kh ((L ⊗[K] Kh) ⧸ P)) =
      ∑ P : {P // P ∈ factors},
        Module.finrank Kh ((L ⊗[K] Kh) ⧸ P.1) := by
    rw [Finset.sum_subtype factors (p := fun P => P ∈ factors)
      (fun P => Iff.rfl)]
  have hsum1 : (∑ P : {P // P ∈ factors},
      Module.finrank Kh ((L ⊗[K] Kh) ⧸ P.1)) =
      ∑ p : PrimeSpectrum (L ⊗[K] Kh),
        Module.finrank Kh ((L ⊗[K] Kh) ⧸ p.asIdeal) := by
    apply Fintype.sum_equiv e
    intro P
    rfl
  rw [hsum0, hsum1]
  calc
    (∑ p : PrimeSpectrum (L ⊗[K] Kh),
        Module.finrank Kh ((L ⊗[K] Kh) ⧸ p.asIdeal)) ≤
        ∑ p : PrimeSpectrum (L ⊗[K] Kh),
          Module.finrank Kh (Localization.AtPrime p.asIdeal) :=
      Finset.sum_le_sum (fun p _ => hquot p)
    _ = Module.finrank Kh (L ⊗[K] Kh) := hdim.symm
    _ = Module.finrank K L := by
      rw [← Module.finrank_baseChange (R := Kh) (S := K) (M' := L)]
      exact (Algebra.TensorProduct.commRight K Kh L).toLinearEquiv.finrank_eq.symm

/-- There are only finitely many inequivalent extensions of a finite
extension.  It is placed after the henselized-tensor finiteness package that
will supply its proof. -/
/- Proof roadmap.

The missing result is not another finiteness lemma: it is the branch/factor
bridge which constructs `S` and
`Chapter10HenselizedTensorBranchCorrespondence v S`.  In particular,
`chapter10_henselized_tensor_has_finitely_many_factors` only enumerates the
maximal ideals after a field `Kh` has been chosen, and the correspondence
structure above *takes* completeness as a field; neither result constructs a
valuation branch from a factor.

First add a helper immediately before this theorem which packages the standard
henselization argument.  Choose a henselization `(Kh, vh)` of `(K, v)` in a
universe at least
`max (max u10K u10L) u10Γ`, install
`Algebra.TensorProduct.rightAlgebra : Algebra Kh (L ⊗[K] Kh)`, and obtain its
module-finiteness by transporting
`Module.Finite.base_change (R := K) (A := Kh) (M := L)` across
`Algebra.TensorProduct.commRight K Kh L`.  Use
`chapter10_henselized_tensor_has_finitely_many_factors` to turn
`Chapter10TensorMaximalIdeals` into a `Finset`.  The helper must then prove the
standard equivalence

`{extensions of v to L}/IsEquiv ≃ {P // P.IsMaximal in L ⊗[K] Kh}`,

constructing the extension attached to a factor by pulling back the unique
extension over the henselian factor field.  Package each representative using
`chapter10_valuation_extension_exists_as_heterogeneous` from
`Section02ExistenceByMaximalDomination.lean`, and build its
`Chapter10HeterogeneousExtensionData` with
`chapter10_heterogeneous_extension_data_exists` from
`Section04RamificationIndexAndResidueDegree.lean`; set the profile to
`{ degree := d.ramificationIndex * d.residueDegree,
   e := d.ramificationIndex, f := d.residueDegree }`.
Surjectivity of the displayed equivalence gives the first conjunct of
`Chapter10CompleteBranchFamily`; injectivity gives its no-duplicates conjunct.
The same construction must also prove `factorContributionIndependent` (using
the value/residue independent family constructed in the proof of
`chapter10_heterogeneous_single_extension_fundamental_inequality` in Section04),
so that the resulting object can be reused by the next theorem.

Once the helper returns `⟨Kh, instances, S, D⟩`, this theorem is just
`⟨S, D.complete⟩`.  There is currently no henselization object or theorem in
this Mathlib snapshot, so do not try to manufacture `D` merely from
`chapter10_henselized_tensor_has_finitely_many_factors`; the field and the
branch/factor equivalence are the substantive missing formalization. -/
theorem chapter10_finitely_many_valuation_extensions
    {K L ΓK : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK] [FiniteDimensional K L]
    (v : Valuation K ΓK) :
    ∃ S : Finset (Chapter10ValuationBranch (K := K) (L := L) v),
      Chapter10CompleteBranchFamily v S := by
  sorry

/-- The sum of `e f` over all branches is bounded by the extension degree. -/
/- Proof roadmap.

Reuse the *strong* helper described above, retaining its `Kh` and
`D : Chapter10HenselizedTensorBranchCorrespondence v S`.  Return

`⟨S, D.complete,
  chapter10_henselized_tensor_branch_sum_bound (K := K) (L := L)
    (Kh := Kh) v S D⟩`.

Universe parameters on `D` must be supplied as in the declaration of
`chapter10_henselized_tensor_branch_sum_bound`: the fifth parameter is the
universe of the factor/branch value groups, while `Kh` is the fourth.  Install
the helper's `Field Kh`, `Algebra K Kh`,
`Algebra Kh (L ⊗[K] Kh)`, and `Module.Finite Kh (L ⊗[K] Kh)` fields as local
instances before applying the bound.

Do not first call `chapter10_finitely_many_valuation_extensions`: that theorem
forgets both `Kh` and `D`, and completeness alone cannot reconstruct
`factorContributionIndependent` or `branchFactor`.  This loss of the tensor
witness was the dead end in the previous proof attempt. -/
theorem chapter10_fundamental_inequality
    {K L ΓK : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK] [FiniteDimensional K L]
    (v : Valuation K ΓK) :
    ∃ S : Finset (Chapter10ValuationBranch (K := K) (L := L) v),
      Chapter10CompleteBranchFamily v S ∧
        Finset.sum S (fun b => Chapter10BranchContribution b.profile) ≤
          Module.finrank K L := by
  sorry

/-- The defect records the possible loss in a local tensor factor. -/
def Chapter10Defect (degree e f : ℕ) : ℚ :=
  (degree : ℚ) / ((e * f : ℕ) : ℚ)

/-- Defect one is exactly equality in the fundamental inequality. -/
theorem chapter10_defect_eq_one_iff
    (degree e f : ℕ) (hpos : 0 < e * f) :
    Chapter10Defect degree e f = 1 ↔ degree = e * f := by
  constructor
  · intro h
    unfold Chapter10Defect at h
    have hne : (e * f : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hpos)
    field_simp [hne] at h
    exact_mod_cast h
  · intro h
    subst degree
    unfold Chapter10Defect
    field_simp [show (e * f : ℚ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hpos)]

/-- A numerical profile is defectless when its degree is ef. -/
def Chapter10DefectlessProfile (p : Chapter10BranchInvariant) : Prop :=
  p.degree = p.e * p.f

/-- The finite normalization hypothesis in the DVR equality theorem, tied to
the actual integral closure rather than an arbitrary module. -/
def Chapter10FiniteNormalization
    (A L : Type*) [CommRing A] [CommRing L] [Algebra A L] : Prop :=
  Module.Finite A (integralClosure A L)

/-- Finite normalization of a DVR gives equality in the sum formula. -/
/- Proof roadmap.

Put `B := integralClosure A L`, `m := IsLocalRing.maximalIdeal A`, and install
`hfinite` as `Module.Finite A B`.  A DVR is a valuation ring, integrally
closed, and a PID; `B` is torsion-free over `A` by
`IsIntegralClosure.isTorsionFree`, hence free/flat over the PID (the relevant
Mathlib infrastructure is in
`Mathlib/LinearAlgebra/FreeModule/PID.lean`).  Give `m.primesOver B` its finite
type with `Set.Finite.fintype (Algebra.QuasiFinite.finite_primesOver m)`.  Then
`Ideal.sum_ramification_inertia_eq_finrank` from
`Mathlib/RingTheory/RamificationInertia/Basic.lean` yields

`∑ q : m.primesOver B, q.1.ramificationIdx A * q.1.inertiaDeg A
    = Module.finrank A B`.

Use `chapter10_finite_extension_prime_valuation_correspondence` from
`Section03IntegralElementsAreBounded.lean`, instantiated with
`(A := A) (B := B) (K := K) (L := L)`, to identify valuation-extension
classes with primes above `m`.  Map `b : {b // b ∈ S}` first to the quotient
class `Quotient.mk'' b.1.extension`, then through that equivalence.  The
coverage and no-duplicates halves of `hcomplete` prove that this map is
bijective (for coverage, eliminate a quotient representative and apply the
forward implication in `hcomplete.1`; for injectivity use `hcomplete.2` and
`Valuation.isEquiv_iff_valuationSubring`).  Turn it into an `Equiv` with
`Equiv.ofBijective`, identifying the prime-above subtype with
`m.primesOver B` by `Subtype.ext` and the definition of
`Chapter10PrimeAboveMaximal`.

Before reindexing the sum, prove the two local comparison lemmas which are
still absent from the file.  For a branch `b` with center `P` they must state

* `b.extensionData.ramificationIndex = P.ramificationIdx A`, and
* `b.extensionData.residueDegree = P.inertiaDeg A`.

For the first, identify the localization `Localization.AtPrime P` with
`b.w.valuationSubring` using the center-localization argument already spelled
out beside `chapter10_algebraic_extension_prime_valuation_correspondence` in
`Section03IntegralElementsAreBounded.lean`; compare a DVR uniformizer and use
`chapter10_normalized_ramification_index_eq_scale` from Section04.  For the
second, the same local-ring equivalence induces an equivalence of residue
fields; rewrite `Chapter10HeterogeneousResidueDegree` and use
`Ideal.inertiaDeg_eq` from
`Mathlib/RingTheory/RamificationInertia/Inertia.lean`.  Merely knowing equality of centers is
insufficient for either numerical rewrite.

Now rewrite `b.profile.e` and `b.profile.f` with `b.profile_e`, `b.profile_f`
and the two comparison lemmas, and use `Fintype.sum_equiv` for the branch/prime
equivalence.  Finish with the displayed ramification-inertia sum and
`IsIntegralClosure.rank A K L B` (or directly its localization-basis proof) to
replace `Module.finrank A B` by `Module.finrank K L`.  The direct named
`IsIntegralClosure.rank` theorem in this Mathlib version carries a separability
assumption from its section; because the present statement assumes only
`hfinite`, do not add separability.  Instead use finite freeness plus
`IsIntegralClosure.isLocalization A K L B` and
`Basis.localizationLocalization`, exactly the rank-comparison argument in that
Mathlib file. -/
theorem chapter10_finite_dvr_normalization_fundamental_equality
    {A K L ΓK : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra A L] [IsScalarTower A K L]
    [LinearOrderedCommGroupWithZero ΓK]
    (v : Valuation K ΓK) (hA : v.Integers A)
    (hfinite : Module.Finite A (integralClosure A L))
    (S : Finset (Chapter10ValuationBranch (K := K) (L := L) v))
    (hcomplete : Chapter10CompleteBranchFamily v S) :
    Finset.sum S (fun b => Chapter10BranchContribution b.profile) = Module.finrank K L := by
  sorry

/-- The normalization of a ring in an algebra, named for the Dedekind case. -/
noncomputable def Chapter10Normalization (A L : Type*) [CommRing A] [CommRing L]
    [Algebra A L] : Subalgebra A L :=
  integralClosure A L

/-- Finite separable extensions of Dedekind domains have finite normalization. -/
theorem chapter10_dedekind_separable_normalization_finite
    {A K L : Type*} [CommRing A] [IsDedekindDomain A]
    [Field K] [Field L] [Algebra A K] [Algebra A L] [Algebra K L]
    [IsFractionRing A K] [IsScalarTower A K L]
    [FiniteDimensional K L]
    (hseparable : Algebra.IsSeparable K L) :
    Module.Finite A (Chapter10Normalization A L) := by
  let : Algebra.IsSeparable K L := hseparable
  exact IsIntegralClosure.finite A K L (integralClosure A L)

/-- In the discrete setting, finite normalization gives the same equality;
the hypotheses do not require completeness. -/
theorem chapter10_finite_normalization_defectless
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀)
    [IsDiscreteValuationRing v.valuationSubring]
    (hfinite : Module.Finite v.valuationSubring
      (integralClosure v.valuationSubring L))
    (S : Finset (Chapter10ValuationBranch (K := K) (L := L) v))
    (hcomplete : Chapter10CompleteBranchFamily v S) :
    Finset.sum S (fun b => Chapter10BranchContribution b.profile) = Module.finrank K L := by
  let : IsFractionRing v.valuationSubring K :=
    (Valuation.valuationSubring.integers v).isFractionRing
  exact chapter10_finite_dvr_normalization_fundamental_equality
    (A := v.valuationSubring) (K := K) (L := L) v
    (Valuation.valuationSubring.integers v) hfinite S hcomplete

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter10
