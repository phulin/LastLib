import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter12.Dependencies
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter06.Section03FiniteProjectiveModules
import Mathlib.LinearAlgebra.Contraction

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

def chapter12Antipode (A H : Type*) [CommSemiring A] [CommSemiring H]
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
theorem chapter12Antipode_apply (A H : Type*) [CommSemiring A] [CommSemiring H]
    [HopfAlgebra A H] (h : H) :
    chapter12Antipode A H h = HopfAlgebra.antipode A h := rfl

theorem chapter12_hopf_coassociative (A H : Type*) [CommSemiring A] [Semiring H]
    [Bialgebra A H] :
    ((TensorProduct.assoc A H H H).toLinearMap ∘ₗ LinearMap.rTensor H comul ∘ₗ comul =
      LinearMap.lTensor H comul ∘ₗ comul) := by
  exact Coalgebra.coassoc

theorem chapter12_hopf_left_counit (A H : Type*) [CommSemiring A] [Semiring H]
    [Bialgebra A H] :
    (LinearMap.rTensor H counit ∘ₗ comul = (TensorProduct.mk A A H) 1) := by
  exact Coalgebra.rTensor_counit_comp_comul

theorem chapter12_hopf_right_counit (A H : Type*) [CommSemiring A] [Semiring H]
    [Bialgebra A H] :
    (LinearMap.lTensor H counit ∘ₗ comul = (TensorProduct.mk A H A).flip 1) := by
  exact Coalgebra.lTensor_counit_comp_comul

theorem chapter12_hopf_antipode_left (A H : Type*) [CommSemiring A] [Semiring H]
    [HopfAlgebra A H] :
    (LinearMap.mul' A H ∘ₗ LinearMap.rTensor H (HopfAlgebra.antipode A) ∘ₗ comul =
      Algebra.linearMap A H ∘ₗ counit) := by
  exact HopfAlgebra.mul_antipode_rTensor_comul

theorem chapter12_hopf_antipode_right (A H : Type*) [CommSemiring A] [Semiring H]
    [HopfAlgebra A H] :
    (LinearMap.mul' A H ∘ₗ LinearMap.lTensor H (HopfAlgebra.antipode A) ∘ₗ comul =
      Algebra.linearMap A H ∘ₗ counit) := by
  exact HopfAlgebra.mul_antipode_lTensor_comul

/-! The affine dictionary. -/

def chapter12_hopfSpec_fullyFaithful (A : CommRingCat.{u}) :
    (AlgebraicGeometry.hopfSpec A).FullyFaithful :=
  AlgebraicGeometry.hopfSpec.fullyFaithful

theorem chapter12_affine_hopf_essential_image (A : CommRingCat.{u})
    (G : Chapter12GroupScheme (Spec A)) :
    (AlgebraicGeometry.hopfSpec A).essImage G ↔ IsAffine G.X.left := by
  exact AlgebraicGeometry.essImage_hopfSpec

instance chapter12_affine_coordinate_hopf_algebra
    (A : Type u) [CommRing A] (G : Scheme.{u})
    [G.Over (Spec (CommRingCat.of A))]
    [GrpObj (G.asOver (Spec (CommRingCat.of A)))] [IsAffine G] :
    HopfAlgebra A Γ(G, ⊤) := by
  letI : Algebra (CommRingCat.of A) Γ(G, ⊤) :=
    ((commAlgCatEquivUnder (CommRingCat.of A)).inverse.obj <|
      .mk (AlgebraicGeometry.Spec.fullyFaithful.preimage <|
        G.isoSpec.inv ≫ G ↘ AlgebraicGeometry.Spec (CommRingCat.of A)).unop).algebra
  have h₁ : GrpObj ((AlgebraicGeometry.algSpec (CommRingCat.of A)).obj <|
      .op <| CommAlgCat.of (CommRingCat.of A) Γ(G, ⊤)) :=
    .ofIso <| G.isoSpec.asOver (Spec (CommRingCat.of A))
  have h₂ : GrpObj (Opposite.op <| CommAlgCat.of (CommRingCat.of A) Γ(G, ⊤)) :=
    AlgebraicGeometry.algSpec.fullyFaithful.grpObj _
  exact ((commHopfAlgCatEquivCogrpCommAlgCat (CommRingCat.of A)).inverse.obj <|
    .op <| .mk <| .op <| .of (CommRingCat.of A) Γ(G, ⊤)).hopfAlgebra

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
    (A H : Type u) [CommRing A] [CommRing H] [HopfAlgebra A H] :
    Chapter12FiniteLocallyFree
        (Spec.map (CommRingCat.ofHom (algebraMap A H))) ↔
      Chapter12FiniteProjectiveModule A H := by
  simp only [Chapter12FiniteLocallyFree, Chapter12FiniteProjectiveModule,
    IsFinite.SpecMap_iff, Flat.SpecMap_iff,
    LocallyOfFinitePresentation.SpecMap_iff]
  change RingHom.Finite (algebraMap A H) ∧ RingHom.Flat (algebraMap A H) ∧
      RingHom.FinitePresentation (algebraMap A H) ↔
    Module.Finite A H ∧ Module.Projective A H
  constructor
  · rintro ⟨hfinite, hflat, hfp⟩
    have : Module.Finite A H := (RingHom.finite_algebraMap).mp hfinite
    have : Module.Flat A H := (RingHom.flat_algebraMap_iff).mp hflat
    have : Algebra.FinitePresentation A H :=
      (RingHom.finitePresentation_algebraMap).mp hfp
    have : Module.FinitePresentation A H :=
      Module.FinitePresentation.of_finite_of_finitePresentation A H
    exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩
  · rintro ⟨hfinite, hprojective⟩
    let : Module.Finite A H := hfinite
    let : Module.Projective A H := hprojective
    let : Module.Flat A H := Module.Flat.of_projective
    let : Module.FinitePresentation A H := Module.finitePresentation_of_projective A H
    exact ⟨(RingHom.finite_algebraMap).mpr hfinite,
      (RingHom.flat_algebraMap_iff).mpr inferInstance,
      (RingHom.finitePresentation_algebraMap).mpr inferInstance⟩

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
  let hbase :
      LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter06.FiniteProjective
        B (B ⊗[A] M) := by
    let : Module.Finite B N := hN.1
    let : Module.Projective B N := hN.2
    exact ⟨Module.Finite.equiv D.equivalence.symm,
      Module.Projective.of_equiv' D.equivalence.symm⟩
  exact LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter06.finiteProjective_of_faithfullyFlat_baseChange_of_hypothesis
    hbase

theorem chapter12_dual_of_finite_projective
    (A M : Type*) [CommRing A] [AddCommGroup M] [Module A M]
    (hM : Chapter12FiniteProjectiveModule A M) :
    Chapter12FiniteProjectiveModule A (Module.Dual A M) := by
  let : Module.Finite A M := hM.1
  let : Module.Projective A M := hM.2
  exact ⟨inferInstance, inferInstance⟩

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
    [Module.Free R V] [Module.Finite R V] :
    IsBaseChange A (h.toDual) := by
  exact h.dual

theorem chapter12_finite_projective_dual_base_change
    (R A V W : Type*) [CommRing R] [CommRing A]
    [AddCommGroup V] [AddCommGroup W] [Module R V] [Module R W]
    [Algebra R A] [Module A W] [IsScalarTower R A W]
    (j : V →ₗ[R] W) (h : IsBaseChange A j)
    (hV : Chapter12FiniteProjectiveModule R V) :
    IsBaseChange A (h.toDual) := by
  letI : Module.Finite R V := hV.1
  letI : Module.Projective R V := hV.2
  let c₀ : Module.Dual R V →ₗ[R] (V →ₗ[R] A) :=
    (Algebra.linearMap R A).compRight R
  let c : A ⊗[R] Module.Dual R V →ₗ[A] (V →ₗ[R] A) :=
    LinearMap.liftBaseChange A c₀
  have hc_comm :
      (c.restrictScalars R).comp (TensorProduct.comm R (Module.Dual R V) A).toLinearMap =
        dualTensorHom R V A := by
    apply TensorProduct.ext
    intro φ a
    apply LinearMap.ext
    intro v
    simp [c, c₀, TensorProduct.comm_tmul, Algebra.smul_def, mul_comm]
  have hc : Function.Bijective c := by
    apply (Function.Bijective.of_comp_iff
      (c.restrictScalars R) (TensorProduct.comm R (Module.Dual R V) A).bijective).mp
    change Function.Bijective ((c.restrictScalars R).comp
      (TensorProduct.comm R (Module.Dual R V) A).toLinearMap)
    rw [hc_comm]
    exact dualTensorHom_bijective
  let e₀ : A ⊗[R] Module.Dual R V →ₗ[A] Module.Dual A (A ⊗[R] V) :=
    (LinearMap.liftBaseChangeEquiv A).toLinearMap.comp c
  have he₀ : Function.Bijective e₀ :=
    by
      change Function.Bijective ((LinearMap.liftBaseChangeEquiv A).toLinearMap.comp c)
      exact (LinearEquiv.bijective (LinearMap.liftBaseChangeEquiv A)).comp hc
  let e₀' : A ⊗[R] Module.Dual R V ≃ₗ[A] Module.Dual A (A ⊗[R] V) :=
    LinearEquiv.ofBijective e₀ he₀
  have he₀_base (φ : Module.Dual R V) :
      e₀' (1 ⊗ₜ[R] φ) = φ.baseChange A := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | tmul a v =>
        simp [e₀', e₀, c, c₀, LinearMap.liftBaseChange_tmul,
          Module.Dual.baseChange_apply_tmul, Algebra.smul_def, mul_comm]
  refine IsBaseChange.of_equiv
    (e₀'.trans (Module.Dual.congr h.equiv)) ?_
  intro φ
  change (Module.Dual.congr h.equiv) (e₀' (1 ⊗ₜ[R] φ)) = h.toDual φ
  rw [he₀_base]
  exact (IsBaseChange.toDual_apply h φ).symm

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
