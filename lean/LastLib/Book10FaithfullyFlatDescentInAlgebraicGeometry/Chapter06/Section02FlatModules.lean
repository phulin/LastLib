import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter06.Dependencies

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter06

noncomputable section

open TensorProduct

universe u v w

/-! ## 6.2 Flat modules -/

/-- The tensor criterion for flatness, in the left-tensor formulation. -/
theorem flat_iff_lTensor_preserves_injective
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    [Small.{max u v} R] :
    Module.Flat R M ↔
      ∀ ⦃N N' : Type (max u v)⦄ [AddCommGroup N] [AddCommGroup N']
        [Module R N] [Module R N'] (f : N →ₗ[R] N'),
        Function.Injective f → Function.Injective (f.lTensor M) := by
  exact Module.Flat.iff_lTensor_preserves_injective_linearMap

/-- Flat modules preserve exact sequences after tensoring. -/
theorem flat_lTensor_exact
    {R M N N' N'' : Type*} [CommRing R] [AddCommGroup M]
    [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N''] [Module R M]
    [Module R N] [Module R N'] [Module R N''] [Module.Flat R M]
    {f : N →ₗ[R] N'} {g : N' →ₗ[R] N''} (h : Function.Exact f g) :
    Function.Exact (f.lTensor M) (g.lTensor M) := by
  exact Module.Flat.lTensor_exact M h

/-- Faithfully flat tensoring reflects injectivity. -/
theorem faithfullyFlat_lTensor_injective_iff
    {R B N N' : Type*} [CommRing R] [CommRing B] [AddCommGroup N]
    [AddCommGroup N'] [Algebra R B] [Module R N] [Module R N']
    [Module.FaithfullyFlat R B] (f : N →ₗ[R] N') :
    Function.Injective (f.lTensor B) ↔ Function.Injective f := by
  sorry

/-- Faithfully flat tensoring reflects surjectivity. -/
theorem faithfullyFlat_lTensor_surjective_iff
    {R B N N' : Type*} [CommRing R] [CommRing B] [AddCommGroup N]
    [AddCommGroup N'] [Algebra R B] [Module R N] [Module R N']
    [Module.FaithfullyFlat R B] (f : N →ₗ[R] N') :
    Function.Surjective (f.lTensor B) ↔ Function.Surjective f := by
  sorry

/-- Faithfully flat tensoring reflects exactness. -/
theorem faithfullyFlat_lTensor_exact_iff
    {R B N N' N'' : Type*} [CommRing R] [CommRing B]
    [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
    [Algebra R B] [Module R N] [Module R N'] [Module R N'']
    [Module.FaithfullyFlat R B] {f : N →ₗ[R] N'} {g : N' →ₗ[R] N''} :
    Function.Exact (f.lTensor B) (g.lTensor B) ↔ Function.Exact f g := by
  sorry

/-- Flatness descends along a faithfully flat tensor-product base change. -/
theorem flat_of_faithfullyFlat_tensorProduct
    {A B M : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.FaithfullyFlat A B]
    [Module.Flat B (B ⊗[A] M)] :
    Module.Flat A M := by
  exact Module.Flat.of_flat_tensorProduct A M B

/-- The relative base-changed ring and module used for the fpqc-local statement. -/
abbrev relativeBaseChangedRing
    (A R B : Type*) [CommRing A] [CommRing R] [CommRing B]
    [Algebra A R] [Algebra A B] : Type* :=
  B ⊗[A] R

abbrev relativeBaseChangedModule
    (A R B M : Type*) [CommRing A] [CommRing R] [CommRing B]
    [AddCommGroup M] [Algebra A R] [Algebra A B] [Module R M]
    [Module A M] [IsScalarTower A R M] : Type* :=
  B ⊗[A] M

/-- Flatness after relative base change is the source-level hypothesis on `R_B` and `M_B`. -/
def FlatAfterFaithfullyFlatBaseChange
    (A R B M : Type*) [CommRing A] [CommRing R] [CommRing B]
    [AddCommGroup M] [Algebra A R] [Algebra A B] [Module R M]
    [Module A M] [IsScalarTower A R M] : Prop :=
  Module.Flat (relativeBaseChangedRing A R B) (relativeBaseChangedModule A R B M)

/-- The relative flatness statement is fpqc local on the base. -/
theorem flat_of_flatAfterFaithfullyFlatBaseChange
    {A R B M : Type*} [CommRing A] [CommRing R] [CommRing B]
    [AddCommGroup M] [Algebra A R] [Algebra A B] [Module R M]
    [Module A M] [IsScalarTower A R M] [Module.FaithfullyFlat A B]
    (hM : FlatAfterFaithfullyFlatBaseChange A R B M) :
    Module.Flat R M := by
  sorry

/-- The ring-hom formulation of fpqc-local flatness. -/
theorem ringHom_flat_of_faithfullyFlat_relative_baseChange
    {A R B : Type*} [CommRing A] [CommRing R] [CommRing B]
    (f : A →+* R) (g : A →+* B) (hg : g.FaithfullyFlat)
    (hbase :
      letI : Algebra A R := f.toAlgebra
      letI : Algebra A B := g.toAlgebra
      Module.Flat B (B ⊗[A] R)) :
    RingHom.Flat f := by
  sorry

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter06
