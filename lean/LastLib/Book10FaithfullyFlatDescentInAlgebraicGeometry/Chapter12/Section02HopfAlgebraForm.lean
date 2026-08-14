import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter12.Dependencies

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter12

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Bialgebra Coalgebra HopfAlgebra TensorProduct

universe u v

/-!
### 12.2 Hopf-algebra form

The book-facing names below are thin wrappers around the pinned Mathlib Hopf-algebra API.  In
particular, the tensor products and algebra maps are not replaced by an unstructured collection of
equations.
-/

abbrev Chapter12HopfAlgebra (A H : Type*) [CommSemiring A] [Semiring H] := HopfAlgebra A H

abbrev Chapter12CommutativeHopfAlgebra (A : Type u) [CommRing A] := CommHopfAlgCat A

def chapter12Comultiplication (A H : Type*) [CommSemiring A] [Semiring H]
    [Bialgebra A H] : H →ₐ[A] H ⊗[A] H :=
  Bialgebra.comulAlgHom A H

def chapter12Counit (A H : Type*) [CommSemiring A] [Semiring H]
    [Bialgebra A H] : H →ₐ[A] A :=
  Bialgebra.counitAlgHom A H

def chapter12Antipode (A H : Type*) [CommSemiring A] [CommRing H]
    [HopfAlgebra A H] : H →ₐ[A] H :=
  HopfAlgebra.antipodeAlgHom A H

@[simp]
theorem chapter12Comultiplication_apply (A H : Type*) [CommSemiring A] [Semiring H]
    [Bialgebra A H] (h : H) :
    chapter12Comultiplication A H h = Coalgebra.comul h := rfl

@[simp]
theorem chapter12Counit_apply (A H : Type*) [CommSemiring A] [Semiring H]
    [Bialgebra A H] (h : H) :
    chapter12Counit A H h = Coalgebra.counit h := rfl

@[simp]
theorem chapter12Antipode_apply (A H : Type*) [CommSemiring A] [CommRing H]
    [HopfAlgebra A H] (h : H) :
    chapter12Antipode A H h = HopfAlgebra.antipode A h := rfl

theorem chapter12_hopf_coassociative (A H : Type*) [CommSemiring A] [Semiring H]
    [HopfAlgebra A H] :
    Coalgebra.coassoc (R := A) (A := H) :=
  Coalgebra.coassoc

theorem chapter12_hopf_left_counit (A H : Type*) [CommSemiring A] [Semiring H]
    [HopfAlgebra A H] :
    Coalgebra.rTensor_counit_comp_comul (R := A) (A := H) :=
  Coalgebra.rTensor_counit_comp_comul

theorem chapter12_hopf_right_counit (A H : Type*) [CommSemiring A] [Semiring H]
    [HopfAlgebra A H] :
    Coalgebra.lTensor_counit_comp_comul (R := A) (A := H) :=
  Coalgebra.lTensor_counit_comp_comul

theorem chapter12_hopf_antipode_left (A H : Type*) [CommSemiring A] [Semiring H]
    [HopfAlgebra A H] :
    HopfAlgebra.mul_antipode_rTensor_comul (R := A) (A := H) :=
  HopfAlgebra.mul_antipode_rTensor_comul

theorem chapter12_hopf_antipode_right (A H : Type*) [CommSemiring A] [Semiring H]
    [HopfAlgebra A H] :
    HopfAlgebra.mul_antipode_lTensor_comul (R := A) (A := H) :=
  HopfAlgebra.mul_antipode_lTensor_comul

/-! The affine dictionary. -/

theorem chapter12_hopfSpec_fullyFaithful (A : CommRingCat.{u}) :
    (AlgebraicGeometry.hopfSpec A).FullyFaithful :=
  AlgebraicGeometry.hopfSpec.fullyFaithful A

theorem chapter12_affine_hopf_essential_image (A : CommRingCat.{u})
    (G : Chapter12GroupScheme (Spec A)) :
    (AlgebraicGeometry.hopfSpec A).essImage G ↔ IsAffine G.X.left := by
  simpa using (AlgebraicGeometry.essImage_hopfSpec (R := A) (G := G))

theorem chapter12_affine_coordinate_hopf_algebra
    (A : Type u) [CommRing A] (G : Scheme.{u})
    [G.Over (Spec A)] [GrpObj (G.asOver (Spec A))] [IsAffine G] :
    HopfAlgebra A Γ(G, ⊤) := by
  infer_instance

/-! ### Finite projective descent and duality -/

/-- The finite-projective hypothesis decisive for the duality statements in this section. -/
def Chapter12FiniteProjectiveModule (A M : Type*) [CommRing A]
    [AddCommGroup M] [Module A M] : Prop :=
  Module.Finite A M ∧ Module.Projective A M

/-!
For an affine group scheme, the geometric finite-locally-free condition is the coordinate
finite-projective condition.  The equivalence is kept as a bridge so later action statements can
switch between the two canonical presentations.
-/

theorem chapter12_affine_finiteLocallyFree_iff_coordinate_finiteProjective
    (A H : Type u) [CommRing A] [CommRing H] [Algebra A H] [HopfAlgebra A H] :
    Chapter12FiniteLocallyFree
        (Spec.map (CommRingCat.ofHom (algebraMap A H))) ↔
      Chapter12FiniteProjectiveModule A H := by
  sorry

/-- A module together with its chosen faithfully-flat base-change presentation. -/
structure Chapter12ModuleBaseChangeData
    (A B M N : Type*) [CommRing A] [CommRing B]
    [AddCommGroup M] [AddCommGroup N] [Algebra A B]
    [Module A M] [Module B N] where
  equivalence : B ⊗[A] M ≃ₗ[B] N

theorem chapter12_finite_projective_descends
    (A B M N : Type*) [CommRing A] [CommRing B]
    [AddCommGroup M] [AddCommGroup N] [Algebra A B]
    [Module A M] [Module B N] [Module.FaithfullyFlat A B]
    (D : Chapter12ModuleBaseChangeData A B M N)
    (hN : Chapter12FiniteProjectiveModule B N) :
    Chapter12FiniteProjectiveModule A M := by
  sorry

theorem chapter12_dual_of_finite_projective
    (A M : Type*) [CommRing A] [AddCommGroup M] [Module A M]
    (hM : Chapter12FiniteProjectiveModule A M) :
    Chapter12FiniteProjectiveModule A (Module.Dual A M) := by
  rcases hM with ⟨hfinite, hprojective⟩
  letI : Module.Finite A M := hfinite
  letI : Module.Projective A M := hprojective
  constructor <;> infer_instance

/-- The base-change map on duals, with the source convention `Dual A M = M →ₗ[A] A`. -/
def chapter12DualBaseChange (A B M : Type*) [CommSemiring A] [CommSemiring B]
    [Algebra A B] [AddCommMonoid M] [Module A M] :
    Module.Dual A M →ₗ[A] Module.Dual B (B ⊗[A] M) :=
  Module.Dual.baseChange B

@[simp]
theorem chapter12DualBaseChange_apply_tmul
    (A B M : Type*) [CommSemiring A] [CommSemiring B]
    [Algebra A B] [AddCommMonoid M] [Module A M]
    (f : Module.Dual A M) (b : B) (m : M) :
    chapter12DualBaseChange A B M f (b ⊗ₜ[A] m) = (f m) • b := by
  exact Module.Dual.baseChange_apply_tmul B f b m

theorem chapter12_dual_base_change_is_base_change
    (R A V W : Type*) [CommSemiring R] [CommSemiring A]
    [AddCommMonoid V] [AddCommMonoid W] [Module R V] [Module R W]
    [Algebra R A] [Module A W] [IsScalarTower R A W]
    (j : V →ₗ[R] W) (h : IsBaseChange A j)
    [Free R V] [Module.Finite R V] :
    IsBaseChange A (h.toDual) := by
  exact h.dual

theorem chapter12_finite_projective_dual_base_change
    (R A V W : Type*) [CommRing R] [CommRing A]
    [AddCommGroup V] [AddCommGroup W] [Module R V] [Module R W]
    [Algebra R A] [Module A W] [IsScalarTower R A W]
    (j : V →ₗ[R] W) (h : IsBaseChange A j)
    (hV : Chapter12FiniteProjectiveModule R V) :
    IsBaseChange A (h.toDual) := by
  sorry

/-- The transpose of an algebra map, with the contravariant direction made explicit. -/
def chapter12TransposeAlgHom
    (A H K : Type*) [CommSemiring A] [Semiring H] [Semiring K]
    [Algebra A H] [Algebra A K] (f : H →ₐ[A] K) :
    Module.Dual A K →ₗ[A] Module.Dual A H :=
  f.toLinearMap.dualMap

@[simp]
theorem chapter12TransposeAlgHom_apply
    (A H K : Type*) [CommSemiring A] [Semiring H] [Semiring K]
    [Algebra A H] [Algebra A K] (f : H →ₐ[A] K)
    (φ : Module.Dual A K) (h : H) :
    chapter12TransposeAlgHom A H K f φ h = φ (f h) := by
  exact LinearMap.dualMap_apply f.toLinearMap φ h

theorem chapter12TransposeAlgHom_comp
    (A H K L : Type*) [CommSemiring A] [Semiring H] [Semiring K] [Semiring L]
    [Algebra A H] [Algebra A K] [Algebra A L]
    (f : H →ₐ[A] K) (g : K →ₐ[A] L) :
    chapter12TransposeAlgHom A H L (g.comp f) =
      (chapter12TransposeAlgHom A H K f).comp
        (chapter12TransposeAlgHom A K L g) := by
  exact (LinearMap.dualMap_comp_dualMap f.toLinearMap g.toLinearMap).symm

/-!
The preceding declarations deliberately require finite projectivity before using dual base change.
No assertion about arbitrary duals is made: without this hypothesis the dual need not be finite
projective and the tensor/base-change comparison is not a representability interface.
-/

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter12
