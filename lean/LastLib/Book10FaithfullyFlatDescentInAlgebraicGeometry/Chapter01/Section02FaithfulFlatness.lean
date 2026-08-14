import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter01.Dependencies

/-!
# 1.2 Faithful flatness

This section presents the ring, module, ideal-theoretic, spectral, and fiber formulations in the
same order as the chapter.  The module predicates are the pinned Mathlib predicates; the
chapter-facing names make the direction of tensoring explicit.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry TensorProduct

universe u

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter01

noncomputable section

/-- Flatness of an algebra, expressed through its underlying module. -/
abbrev Chapter01FlatAlgebra (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] : Prop :=
  Module.Flat A B

/-- Faithful flatness of an algebra, expressed through its underlying module. -/
abbrev Chapter01FaithfullyFlatAlgebra
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] : Prop :=
  Module.FaithfullyFlat A B

/-- Flatness of a ring homomorphism. -/
abbrev Chapter01FlatRingHom {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) : Prop :=
  f.Flat

/-- Faithful flatness of a ring homomorphism. -/
abbrev Chapter01FaithfullyFlatRingHom {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) : Prop :=
  f.FaithfullyFlat

/-- Tensoring with `B` preserves exact sequences of `A`-modules. -/
def Chapter01TensoringPreservesExactness
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] : Prop :=
  ∀ {M₁ M₂ M₃ : Type u} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [Module A M₁] [Module A M₂] [Module A M₃]
    (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃),
    Function.Exact f g → Function.Exact (f.lTensor B) (g.lTensor B)

/-- Tensoring with `B` preserves and reflects exact sequences of `A`-modules. -/
def Chapter01TensoringPreservesAndReflectsExactness
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] : Prop :=
  ∀ {M₁ M₂ M₃ : Type u} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [Module A M₁] [Module A M₂] [Module A M₃]
    (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃),
    Function.Exact f g ↔ Function.Exact (f.lTensor B) (g.lTensor B)

theorem chapter01_faithfullyFlat_iff_tensoring_preserves_and_reflects_exactness
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    Chapter01FaithfullyFlatAlgebra A B ↔
      Chapter01TensoringPreservesAndReflectsExactness A B := by
  unfold Chapter01FaithfullyFlatAlgebra Chapter01TensoringPreservesAndReflectsExactness
  constructor
  · intro h M₁ M₂ M₃ _ _ _ _ _ _ f g
    let _ : Module.FaithfullyFlat A B := h
    exact (Module.FaithfullyFlat.lTensor_exact_iff_exact A B f g).symm
  · intro h
    exact (Module.FaithfullyFlat.iff_exact_iff_lTensor_exact A B).mpr (fun f g => h f g)

theorem chapter01_flat_iff_tensoring_preserves_exactness
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    Chapter01FlatAlgebra A B ↔ Chapter01TensoringPreservesExactness A B := by
  simpa [Chapter01FlatAlgebra, Chapter01TensoringPreservesExactness] using
    (Module.Flat.iff_lTensor_exact (R := A) (M := B))

/-- Faithfulness of tensoring, written as reflection of trivial modules. -/
def Chapter01TensorReflectsTriviality
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module A M],
    Subsingleton (B ⊗[A] M) → Subsingleton M

theorem chapter01_faithfullyFlat_iff_flat_and_tensor_reflects_triviality
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
      Chapter01FaithfullyFlatAlgebra A B ↔
      Chapter01FlatAlgebra A B ∧ Chapter01TensorReflectsTriviality A B := by
  simpa [Chapter01FaithfullyFlatAlgebra, Chapter01FlatAlgebra, Chapter01TensorReflectsTriviality] using
    (Module.FaithfullyFlat.iff_flat_and_lTensor_reflects_triviality (R := A) (M := B))

theorem chapter01_faithfullyFlat_iff_flat_and_tensor_nontrivial
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    Chapter01FaithfullyFlatAlgebra A B ↔
      Chapter01FlatAlgebra A B ∧
        ∀ (M : Type u) [AddCommGroup M] [Module A M],
          Nontrivial M → Nontrivial (B ⊗[A] M) := by
  simpa [Chapter01FaithfullyFlatAlgebra, Chapter01FlatAlgebra] using
    (Module.FaithfullyFlat.iff_flat_and_lTensor_faithful A B)

/-- Extension of an ideal along an algebra map; this is the book's notation `IB`. -/
abbrev chapter01IdealExtension
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A) : Ideal B :=
  I.map (algebraMap A B)

/-- The quotient-tensor identity used in the proper-ideal criterion. -/
noncomputable def chapter01QuotientTensorEquiv
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A) :
    (A ⧸ I) ⊗[A] B ≃ₐ[A ⧸ I] B ⧸ chapter01IdealExtension A B I :=
  (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).symm

theorem chapter01_faithfullyFlat_iff_flat_and_proper_ideal
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    Chapter01FaithfullyFlatAlgebra A B ↔
      Chapter01FlatAlgebra A B ∧
        ∀ I : Ideal A, I ≠ ⊤ → chapter01IdealExtension A B I ≠ ⊤ := by
  simpa [Chapter01FaithfullyFlatAlgebra, Chapter01FlatAlgebra, chapter01IdealExtension] using
    (Module.FaithfullyFlat.iff_flat_and_proper_ideal (R := A) (M := B))

theorem chapter01_faithfullyFlat_iff_flat_and_ideal_extension_eq_top
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    Chapter01FaithfullyFlatAlgebra A B ↔
      Chapter01FlatAlgebra A B ∧
        ∀ I : Ideal A, chapter01IdealExtension A B I = ⊤ → I = ⊤ := by
  simpa [Chapter01FaithfullyFlatAlgebra, Chapter01FlatAlgebra, chapter01IdealExtension] using
    (Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top (R := A) (M := B))

theorem chapter01_ringHom_faithfullyFlat_iff_flat_and_spec_surjective
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    Chapter01FaithfullyFlatRingHom f ↔
      Chapter01FlatRingHom f ∧ Function.Surjective (PrimeSpectrum.comap f) :=
  RingHom.FaithfullyFlat.iff_flat_and_comap_surjective

theorem chapter01_ringHom_faithfullyFlat_flat
    {A B : Type u} [CommRing A] [CommRing B] {f : A →+* B}
    (hf : Chapter01FaithfullyFlatRingHom f) : Chapter01FlatRingHom f :=
  RingHom.FaithfullyFlat.flat hf

theorem chapter01_algebraMap_faithfullyFlat_iff
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    (algebraMap A B).FaithfullyFlat ↔ Chapter01FaithfullyFlatAlgebra A B := by
  exact RingHom.faithfullyFlat_algebraMap_iff

/-- The fiber over a prime of `A`, in the order used in the chapter. -/
abbrev Chapter01PrimeFiber
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (p : PrimeSpectrum A) :=
  B ⊗[A] p.asIdeal.ResidueField

theorem chapter01_primeFiber_nontrivial_of_faithfullyFlat
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] (p : PrimeSpectrum A) :
    Nontrivial (Chapter01PrimeFiber A B p) := by
  infer_instance

theorem chapter01_faithfullyFlat_of_flat_of_primeFiber_nontrivial
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    (h : ∀ p : PrimeSpectrum A, Nontrivial (Chapter01PrimeFiber A B p)) :
    Module.FaithfullyFlat A B := by
  exact Module.FaithfullyFlat.of_comap_surjective (fun p => by
    let _ : Nontrivial (B ⊗[A] p.asIdeal.ResidueField) := h p
    exact (PrimeSpectrum.nontrivial_iff_mem_rangeComap p).mp
      ((TensorProduct.comm A B p.asIdeal.ResidueField).symm.toEquiv.nontrivial))

theorem chapter01_faithfullyFlat_iff_flat_and_primeFiber_nontrivial
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    Module.FaithfullyFlat A B ↔
      Module.Flat A B ∧
        ∀ p : PrimeSpectrum A, Nontrivial (Chapter01PrimeFiber A B p) := by
  constructor
  · intro h
    let _ : Module.FaithfullyFlat A B := h
    exact ⟨inferInstance, fun p => chapter01_primeFiber_nontrivial_of_faithfullyFlat A B p⟩
  · rintro ⟨hf, h⟩
    let _ : Module.Flat A B := hf
    exact chapter01_faithfullyFlat_of_flat_of_primeFiber_nontrivial A B h

theorem chapter01_tensorProduct_mk_injective
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] (M : Type u) [AddCommGroup M] [Module A M] :
    Function.Injective (TensorProduct.mk A B M 1) := by
  exact Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := B) M

/-- The tensor-unit criterion is stated with the flatness conjunct made explicit. -/
theorem chapter01_faithfullyFlat_iff_flat_and_tensorProduct_mk_injective
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    Module.FaithfullyFlat A B ↔
      Module.Flat A B ∧
        ∀ (M : Type u) [AddCommGroup M] [Module A M],
          Function.Injective (TensorProduct.mk A B M 1) := by
  constructor
  · intro h
    let _ : Module.FaithfullyFlat A B := h
    exact ⟨inferInstance, fun M _ _ => chapter01_tensorProduct_mk_injective A B M⟩
  · rintro ⟨hf, hm⟩
    let _ : Module.Flat A B := hf
    exact (Module.FaithfullyFlat.iff_flat_and_lTensor_reflects_triviality (R := A) (M := B)).2
      ⟨hf, fun M _ _ hM => by
        let _ : Subsingleton (B ⊗[A] M) := hM
        exact (hm M).subsingleton⟩

theorem chapter01_lTensor_injective_iff_injective
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B]
    {M N : Type u} [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    (f : M →ₗ[A] N) :
    Function.Injective (f.lTensor B) ↔ Function.Injective f :=
  Module.FaithfullyFlat.lTensor_injective_iff_injective A B f

theorem chapter01_lTensor_surjective_iff_surjective
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B]
    {M N : Type u} [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    (f : M →ₗ[A] N) :
    Function.Surjective (f.lTensor B) ↔ Function.Surjective f :=
  Module.FaithfullyFlat.lTensor_surjective_iff_surjective A B f

theorem chapter01_lTensor_bijective_iff_bijective
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B]
    {M N : Type u} [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    (f : M →ₗ[A] N) :
    Function.Bijective (f.lTensor B) ↔ Function.Bijective f :=
  Module.FaithfullyFlat.lTensor_bijective_iff_bijective A B f

theorem chapter01_faithfullyFlat_trans
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Module.FaithfullyFlat A B] [Module.FaithfullyFlat B C] :
    Module.FaithfullyFlat A C :=
  Module.FaithfullyFlat.trans A B C

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter01
