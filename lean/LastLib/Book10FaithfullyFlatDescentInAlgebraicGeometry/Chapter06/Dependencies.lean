import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter06

noncomputable section

open TensorProduct

universe u v

/-! Shared book-facing vocabulary for Chapter 6. -/

/-- A finite spanning witness for a module. -/
abbrev FiniteGeneratorWitness (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] : Prop :=
  (⊤ : Submodule R M).FG

theorem finiteGeneratorWitness_iff_moduleFinite
    {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] :
    FiniteGeneratorWitness R M ↔ Module.Finite R M :=
  Module.finite_def.symm

/-- The finite-projective condition used throughout the chapter. -/
def FiniteProjective (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  Module.Finite R M ∧ Module.Projective R M

theorem finiteProjective_iff_moduleFinite_and_projective
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    FiniteProjective R M ↔ Module.Finite R M ∧ Module.Projective R M :=
  Iff.rfl

/-- A finite free presentation split witnessing finite projectivity. -/
structure FiniteProjectiveWitness
    (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] where
  index : ℕ
  cover : (Fin index → R) →ₗ[R] M
  sectionMap : M →ₗ[R] (Fin index → R)
  cover_surjective : Function.Surjective cover
  cover_section : cover ∘ₗ sectionMap = LinearMap.id

/-- The finite-locally-free condition expressed using the canonical free locus. -/
def FiniteLocallyFree (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  Module.Finite R M ∧
    ∀ p : PrimeSpectrum R,
      Module.Free (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M)

theorem finiteLocallyFree_iff_freeLocus_eq_univ
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] :
    FiniteLocallyFree R M ↔ Module.freeLocus R M = Set.univ := by
  simp [FiniteLocallyFree, Module.freeLocus]

/-- The fiber rank of a finitely presented module at a prime. -/
noncomputable def fiberRank
    {R : Type*} (M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (p : PrimeSpectrum R) : ℕ :=
  Module.rankAtStalk M p

theorem fiberRank_eq_stalkRank
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (p : PrimeSpectrum R) :
    fiberRank M p = Module.rankAtStalk M p :=
  rfl

theorem fiberRank_eq_residueField_finrank
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (p : PrimeSpectrum R) :
    fiberRank M p = Module.finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M) := by
  exact Module.rankAtStalk_eq M p

/-- A module has constant fiber rank `r`. -/
def HasConstantRank
    {R : Type*} (M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (r : ℕ) : Prop :=
  ∀ p : PrimeSpectrum R, fiberRank M p = r

/-- The fiber rank of a module lies in a prescribed set of natural numbers. -/
def HasRankIn
    {R : Type*} (M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (ranks : Set ℕ) : Prop :=
  ∀ p : PrimeSpectrum R, fiberRank M p ∈ ranks

/-- The `r`th exterior power, used as the determinant module in the constant-rank case. -/
abbrev determinantModule
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] (r : ℕ) : Type* :=
  ⋀[R]^r M

/-- The map induced on determinant modules by a linear map. -/
noncomputable def determinantMap
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (r : ℕ) (f : M →ₗ[R] N) :
    determinantModule R M r →ₗ[R] determinantModule R N r :=
  exteriorPower.map r f

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter06
