import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Data.ZMod.Basic
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter03.Dependencies

/-!
# 3.3 Purity and descent tests
-/

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter03

open scoped TensorProduct

def Chapter03PureAlgebraMap (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] : Prop :=
  ∀ (M : Type*) [AddCommGroup M] [Module A M],
    Function.Injective (chapter03TensorUnitMap A B M)

theorem chapter03_faithfullyFlat_pure
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] :
    Chapter03PureAlgebraMap A B := by
  intro M _ _
  exact Module.FaithfullyFlat.tensorProduct_mk_injective M

theorem chapter03_pure_does_not_imply_flat :
    Chapter03PureAlgebraMap ℤ (TrivSqZeroExt ℤ (ZMod 2)) ∧
      ¬ Module.Flat ℤ (TrivSqZeroExt ℤ (ZMod 2)) := by
  sorry

theorem chapter03_finite_generation_descends
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module.FaithfullyFlat A B]
    [Module.Finite B (B ⊗[A] M)] :
    Module.Finite A M :=
  Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B

def Chapter03FiniteGeneratorFamily (R M : Type*) [CommSemiring R] [AddCommMonoid M]
    [Module R M] (n : ℕ) (m : Fin n → M) : Prop :=
  Submodule.span R (Set.range m) = ⊤

def chapter03TensorGeneratorFamily
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] {n : ℕ} (m : Fin n → M) :
    Fin n → B ⊗[A] M :=
  fun i => (1 : B) ⊗ₜ[A] m i

theorem chapter03_tensor_generator_family_descends
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module.FaithfullyFlat A B] {n : ℕ}
    (m : Fin n → M)
    (hm : Chapter03FiniteGeneratorFamily B (B ⊗[A] M) n
      (chapter03TensorGeneratorFamily (A := A) (B := B) (M := M) m)) :
    Chapter03FiniteGeneratorFamily A M n m := by
  sorry

/-- Provisional Chapter 6-facing interface for descent of finite presentations of modules. -/
theorem chapter03_finite_presentation_descends
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module.FaithfullyFlat A B]
    [Module.FinitePresentation B (B ⊗[A] M)] :
    Module.FinitePresentation A M := by
  sorry

def Chapter03ProjectivityDescentHypotheses (A M : Type*) [CommRing A] [AddCommGroup M]
    [Module A M] : Prop :=
  Module.FinitePresentation A M ∧ Module.Flat A M

theorem chapter03_projective_of_finite_presentation_and_flat
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [Module.FinitePresentation A M] [Module.Flat A M] :
    Module.Projective A M :=
  Module.Flat.projective_of_finitePresentation

def Chapter03LinearEquationSolution
    {A M N : Type*} [CommRing A] [AddCommGroup M] [AddCommGroup N]
    [Module A M] [Module A N] (f : M →ₗ[A] N) (b : N) (x : M) : Prop :=
  f x = b

theorem chapter03_finite_linear_system_solution_descends
    {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    [Module.Finite A N] [Module.FaithfullyFlat A B]
    (f : M →ₗ[A] N) (b : N) (x : B ⊗[A] M)
    (hsolve : (f.lTensor B) x = chapter03TensorUnitMap A B N b)
    (hinvariant : chapter03AmitsurInvariant A B M x) :
    ∃ y : M, Chapter03LinearEquationSolution f b y := by
  sorry

theorem chapter03_zero_test
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module.FaithfullyFlat A B] :
    Subsingleton (B ⊗[A] M) ↔ Subsingleton M :=
  chapter03_tensor_vanishes_iff

theorem chapter03_injective_test
    {A B M M' : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [AddCommGroup M'] [Module A M] [Module A M']
    [Module.FaithfullyFlat A B] (u : M →ₗ[A] M') :
    Function.Injective (u.lTensor B) ↔ Function.Injective u := by
  exact (chapter03_tensor_injective_iff u).symm

theorem chapter03_surjective_test
    {A B M M' : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [AddCommGroup M'] [Module A M] [Module A M']
    [Module.FaithfullyFlat A B] (u : M →ₗ[A] M') :
    Function.Surjective (u.lTensor B) ↔ Function.Surjective u := by
  exact (chapter03_tensor_surjective_iff u).symm

theorem chapter03_zero_map_test
    {A B M M' : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [AddCommGroup M'] [Module A M] [Module A M']
    [Module.FaithfullyFlat A B] (u : M →ₗ[A] M') :
    u.lTensor B = 0 ↔ u = 0 := by
  exact (chapter03_tensor_zero_iff u).symm

theorem chapter03_exactness_test
    {A B M' M M'' : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M'] [AddCommGroup M] [AddCommGroup M'']
    [Module A M'] [Module A M] [Module A M''] [Module.FaithfullyFlat A B]
    (u : M' →ₗ[A] M) (v : M →ₗ[A] M'') :
    Function.Exact (u.lTensor B) (v.lTensor B) ↔ Function.Exact u v :=
  (chapter03_tensor_exact_iff u v).symm

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter03
