import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter06.Dependencies

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter06

noncomputable section

open TensorProduct

universe u v

/-! ## 6.1 Finite generation and finite presentation -/

/-- A finite list of tensors which generates a base-changed module. -/
structure TensorGeneratorWitness
    (A B M : Type*) [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] where
  index : ℕ
  generators : Fin index → B ⊗[A] M
  span_eq_top : Submodule.span B (Set.range generators) = ⊤

theorem tensorGeneratorWitness_of_finite
    {A B M : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.Finite B (B ⊗[A] M)] :
    Nonempty (TensorGeneratorWitness A B M) := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := B) (M := B ⊗[A] M)
  exact ⟨⟨n, s, hs⟩⟩

/-- Finite generation descends along a faithfully flat base change. -/
theorem module_finite_of_faithfullyFlat_baseChange
    {A B M : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.FaithfullyFlat A B]
    [Module.Finite B (B ⊗[A] M)] :
    Module.Finite A M := by
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B

/-- A surjective base-changed inclusion forces the original submodule to be all of the module. -/
theorem submodule_eq_top_of_faithfullyFlat_lTensor_surjective
    {A B M : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.FaithfullyFlat A B]
    (N : Submodule A M)
    (hN : Function.Surjective (N.subtype.lTensor B)) :
    N = ⊤ := by
  sorry

/-- The tensor product of a quotient by a submodule is zero when its base-changed quotient map is.
-/
theorem tensor_quotient_subsingleton_of_faithfullyFlat_lTensor_surjective
    {A B M : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.FaithfullyFlat A B]
    (N : Submodule A M)
    (hN : Function.Surjective (N.subtype.lTensor B)) :
    Subsingleton (B ⊗[A] (M ⧸ N)) := by
  sorry

/-- This packages the vanishing step used to recover the original finite span. -/
theorem tensor_quotient_subsingleton_iff_submodule_eq_top
    {A B M : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.FaithfullyFlat A B]
    (N : Submodule A M) :
    Subsingleton (B ⊗[A] (M ⧸ N)) ↔ N = ⊤ := by
  sorry

/-- For a surjection onto a finitely presented module, the kernel is finitely generated. -/
theorem finitePresentation_kernel_fg_of_surjective
    {A P M : Type*} [CommRing A] [AddCommGroup P] [AddCommGroup M]
    [Module A P] [Module A M] [Module.Finite A P]
    [Module.FinitePresentation A M]
    (f : P →ₗ[A] M) (hf : Function.Surjective f) :
    (LinearMap.ker f).FG := by
  exact Module.FinitePresentation.fg_ker f hf

/-- A finite presentation descends from a finite presentation of the source and a finite kernel. -/
theorem finitePresentation_of_surjective_of_kernel_fg
    {A P M : Type*} [CommRing A] [AddCommGroup P] [AddCommGroup M]
    [Module A P] [Module A M] [Module.FinitePresentation A P]
    (f : P →ₗ[A] M) (hf : Function.Surjective f)
    (hker : (LinearMap.ker f).FG) :
    Module.FinitePresentation A M := by
  exact Module.finitePresentation_of_surjective f hf hker

/-- Finite presentation is equivalent to a finite-free right exact presentation. -/
theorem finitePresentation_iff_finite_free_exact
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M] :
    Module.FinitePresentation A M ↔
      ∃ (n m : ℕ) (f : (Fin n → A) →ₗ[A] M)
        (g : (Fin m → A) →ₗ[A] (Fin n → A)),
        Function.Surjective f ∧ Function.Exact g f := by
  sorry

/-- Finite presentation descends along faithfully flat base change.  This is the affine statement
with a uniform finite presentation; no merely pointwise-family variant is asserted. -/
theorem module_finitePresentation_of_faithfullyFlat_baseChange
    {A B M : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.FaithfullyFlat A B]
    [Module.FinitePresentation B (B ⊗[A] M)] :
    Module.FinitePresentation A M := by
  sorry

/-- Finite type descends for algebras along a faithfully flat base change. -/
theorem algebra_finiteType_of_faithfullyFlat_baseChange
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Module.FaithfullyFlat A B]
    [Algebra.FiniteType B (B ⊗[A] C)] :
    Algebra.FiniteType A C := by
  exact Algebra.FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat B

/-- Finite presentation descends for algebras along a faithfully flat base change.  The finite
affine presentation supplies the uniform relation list used here. -/
theorem algebra_finitePresentation_of_faithfullyFlat_baseChange
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Module.FaithfullyFlat A B]
    [Algebra.FinitePresentation B (B ⊗[A] C)] :
    Algebra.FinitePresentation A C := by
  exact Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat B

/-- A finitely presented module algebra is finitely presented as an algebra. -/
theorem algebra_finitePresentation_of_module_finitePresentation
    {A C : Type*} [CommRing A] [CommRing C] [Algebra A C]
    [Module.FinitePresentation A C] :
    Algebra.FinitePresentation A C := by
  infer_instance

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter06
