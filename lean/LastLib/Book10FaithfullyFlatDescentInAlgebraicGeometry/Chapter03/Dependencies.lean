import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Ring.Opposite
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Chapter 3 shared interfaces

This file contains the small amount of notation and shared tensor-product data used by the
source-ordered sections of Chapter 3.  The statements in the section files are the book-facing
API; these definitions only package canonical Mathlib constructions.
-/

open scoped BigOperators TensorProduct

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter03

universe u v

abbrev Chapter03FaithfullyFlat (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] : Prop :=
  Module.FaithfullyFlat A B

instance chapter03ZModTwoOppositeModule : Module ℤᵐᵒᵖ (ZMod 2) :=
  Module.compHom (ZMod 2)
    ((RingHom.id ℤ).fromOpposite (fun _ _ => mul_comm _ _))

theorem chapter03_faithfullyFlat_iff_ringHom
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] :
    Chapter03FaithfullyFlat A B ↔ (algebraMap A B).FaithfullyFlat := by
  exact (RingHom.faithfullyFlat_algebraMap_iff (R := A) (S := B)).symm

/-- The unit map `M → B ⊗[A] M` used throughout the chapter. -/
def chapter03TensorUnitMap (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] (M : Type*) [AddCommGroup M] [Module A M] :
    M →ₗ[A] B ⊗[A] M :=
  TensorProduct.mk A B M 1

@[simp]
theorem chapter03TensorUnitMap_apply (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] (M : Type*) [AddCommGroup M] [Module A M] (m : M) :
    chapter03TensorUnitMap A B M m = (1 : B) ⊗ₜ[A] m :=
  rfl

/-- The iterated tensor product with `n + 1` copies of `B`, right-associated. -/
structure Chapter03AmitsurTensorStage (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] where
  carrier : Type v
  [addCommGroup : AddCommGroup carrier]
  [module : Module A carrier]

def chapter03AmitsurTensorStage (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] : ℕ → Chapter03AmitsurTensorStage A B
  | 0 =>
      { carrier := B
        addCommGroup := inferInstance
        module := inferInstance }
  | n + 1 =>
      let stage := chapter03AmitsurTensorStage A B n
      letI := stage.addCommGroup
      letI := stage.module
      { carrier := B ⊗[A] stage.carrier
        addCommGroup := inferInstance
        module := inferInstance }

def Chapter03AmitsurTensor (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] : ℕ → Type v :=
  fun n => (chapter03AmitsurTensorStage A B n).carrier

instance chapter03AmitsurTensorAddCommGroup (A : Type u) (B : Type v) [CommRing A]
    [CommRing B] [Algebra A B] (n : ℕ) :
    AddCommGroup (Chapter03AmitsurTensor A B n) :=
  (chapter03AmitsurTensorStage A B n).addCommGroup

instance chapter03AmitsurTensorModule (A : Type u) (B : Type v) [CommRing A]
    [CommRing B] [Algebra A B] (n : ℕ) :
    Module A (Chapter03AmitsurTensor A B n) :=
  (chapter03AmitsurTensorStage A B n).module

@[simp]
theorem chapter03AmitsurTensor_zero (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] :
    Chapter03AmitsurTensor A B 0 = B :=
  rfl

@[simp]
theorem chapter03AmitsurTensor_succ (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] (n : ℕ) :
    Chapter03AmitsurTensor A B (n + 1) = B ⊗[A] Chapter03AmitsurTensor A B n :=
  rfl

/-- A family of coface maps for the higher Amitsur construction. -/
abbrev Chapter03AmitsurFaceFamily (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] :=
  ∀ n : ℕ, Fin (n + 2) →
    Chapter03AmitsurTensor A B n →ₗ[A] Chapter03AmitsurTensor A B (n + 1)

def chapter03AmitsurD0 (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] : B →ₗ[A] Chapter03AmitsurTensor A B 1 :=
  TensorProduct.mk A B B 1

def chapter03AmitsurD1 (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] : B →ₗ[A] Chapter03AmitsurTensor A B 1 :=
  (TensorProduct.mk A B B).flip 1

/-- The recursion follows the right-associated tensor convention above: position zero inserts
`1` on the left, and every later position recursively inserts `1` in the tail. -/
def chapter03AmitsurFace (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] : Chapter03AmitsurFaceFamily A B
  | 0, i =>
      Fin.cases (chapter03AmitsurD0 A B)
        (fun _ => chapter03AmitsurD1 A B) i
  | n + 1, i =>
      Fin.cases
        (TensorProduct.mk A B (Chapter03AmitsurTensor A B (n + 1)) 1)
        (fun j => (chapter03AmitsurFace A B n j).lTensor B) i

@[simp]
theorem chapter03AmitsurD0_apply (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] (b : B) :
    chapter03AmitsurD0 A B b = (1 : B) ⊗ₜ[A] b :=
  rfl

@[simp]
theorem chapter03AmitsurD1_apply (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] (b : B) :
    chapter03AmitsurD1 A B b = b ⊗ₜ[A] (1 : B) :=
  rfl

def chapter03AmitsurDifference (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] : B →ₗ[A] Chapter03AmitsurTensor A B 1 :=
  chapter03AmitsurD0 A B - chapter03AmitsurD1 A B

def chapter03AmitsurEqualizer (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] : Set B :=
  {b | chapter03AmitsurD0 A B b = chapter03AmitsurD1 A B b}

def chapter03ModuleAmitsurAugmentation (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] (M : Type*) [AddCommGroup M] [Module A M] :
    M →ₗ[A] B ⊗[A] M :=
  chapter03TensorUnitMap A B M

def chapter03ModuleAmitsurD0 (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] (M : Type*) [AddCommGroup M] [Module A M] :
    B ⊗[A] M →ₗ[A] Chapter03AmitsurTensor A B 1 ⊗[A] M :=
  (chapter03AmitsurD0 A B).rTensor M

def chapter03ModuleAmitsurD1 (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] (M : Type*) [AddCommGroup M] [Module A M] :
    B ⊗[A] M →ₗ[A] Chapter03AmitsurTensor A B 1 ⊗[A] M :=
  (chapter03AmitsurD1 A B).rTensor M

def chapter03ModuleAmitsurDifference (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] (M : Type*) [AddCommGroup M] [Module A M] :
    B ⊗[A] M →ₗ[A] Chapter03AmitsurTensor A B 1 ⊗[A] M :=
  chapter03ModuleAmitsurD0 A B M - chapter03ModuleAmitsurD1 A B M

def chapter03AmitsurInvariant (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] (M : Type*) [AddCommGroup M] [Module A M] (x : B ⊗[A] M) : Prop :=
  chapter03ModuleAmitsurD0 A B M x = chapter03ModuleAmitsurD1 A B M x

def chapter03ModuleAmitsurEqualizer (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] (M : Type*) [AddCommGroup M] [Module A M] :
    Submodule A (B ⊗[A] M) :=
  LinearMap.ker (chapter03ModuleAmitsurDifference A B M)

theorem chapter03AmitsurInvariant_iff_mem (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] (M : Type*) [AddCommGroup M] [Module A M] (x : B ⊗[A] M) :
    chapter03AmitsurInvariant A B M x ↔ x ∈ chapter03ModuleAmitsurEqualizer A B M := by
  change chapter03ModuleAmitsurD0 A B M x = chapter03ModuleAmitsurD1 A B M x ↔
    x ∈ (chapter03ModuleAmitsurD0 A B M - chapter03ModuleAmitsurD1 A B M).ker
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    change chapter03ModuleAmitsurD0 A B M x - chapter03ModuleAmitsurD1 A B M x = 0
    exact sub_eq_zero.mpr h
  · intro h
    apply sub_eq_zero.mp
    simpa only [LinearMap.sub_apply] using h

/-- The alternating differential `∂ₙ = ∑ i (-1)^i dⁱ` for a coface family. -/
def chapter03AmitsurBoundary (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] (face : Chapter03AmitsurFaceFamily A B) (n : ℕ) :
    Chapter03AmitsurTensor A B n →ₗ[A] Chapter03AmitsurTensor A B (n + 1) :=
  ∑ i : Fin (n + 2), (-1 : A) ^ (i : ℕ) • face n i

def Chapter03AmitsurDifferentialSquaresToZero (A : Type u) (B : Type v) [CommRing A]
    [CommRing B] [Algebra A B] (face : Chapter03AmitsurFaceFamily A B) : Prop :=
  ∀ n : ℕ,
    (chapter03AmitsurBoundary A B face (n + 1)).comp
        (chapter03AmitsurBoundary A B face n) = 0

def Chapter03AmitsurPositiveExact (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] (face : Chapter03AmitsurFaceFamily A B) : Prop :=
  ∀ n : ℕ,
    Function.Exact (chapter03AmitsurBoundary A B face n)
      (chapter03AmitsurBoundary A B face (n + 1))

abbrev Chapter03ModuleAmitsurFaceFamily (A : Type u) (B : Type v) (M : Type*)
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M] [Module A M] :=
  ∀ n : ℕ, Fin (n + 2) →
    (Chapter03AmitsurTensor A B n ⊗[A] M) →ₗ[A]
      (Chapter03AmitsurTensor A B (n + 1) ⊗[A] M)

def chapter03ModuleAmitsurFace (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] (M : Type*) [AddCommGroup M] [Module A M] :
    Chapter03ModuleAmitsurFaceFamily A B M :=
  fun n i => (chapter03AmitsurFace A B n i).rTensor M

def chapter03ModuleAmitsurBoundary (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] (M : Type*) [AddCommGroup M] [Module A M]
    (face : Chapter03ModuleAmitsurFaceFamily A B M) (n : ℕ) :
    (Chapter03AmitsurTensor A B n ⊗[A] M) →ₗ[A]
      (Chapter03AmitsurTensor A B (n + 1) ⊗[A] M) :=
  ∑ i : Fin (n + 2), (-1 : A) ^ (i : ℕ) • face n i

def Chapter03ModuleAmitsurDifferentialSquaresToZero (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] (M : Type*) [AddCommGroup M] [Module A M]
    (face : Chapter03ModuleAmitsurFaceFamily A B M) : Prop :=
  ∀ n : ℕ,
    (chapter03ModuleAmitsurBoundary A B M face (n + 1)).comp
        (chapter03ModuleAmitsurBoundary A B M face n) = 0

def Chapter03ModuleAmitsurPositiveExact (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] (M : Type*) [AddCommGroup M] [Module A M]
    (face : Chapter03ModuleAmitsurFaceFamily A B M) : Prop :=
  ∀ n : ℕ,
    Function.Exact (chapter03ModuleAmitsurBoundary A B M face n)
      (chapter03ModuleAmitsurBoundary A B M face (n + 1))

def Chapter03AmitsurFaceFamilyMatchesLowDegree (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] (face : Chapter03AmitsurFaceFamily A B) : Prop :=
  face 0 ⟨0, by decide⟩ = chapter03AmitsurD0 A B ∧
    face 0 ⟨1, by decide⟩ = chapter03AmitsurD1 A B

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter03
