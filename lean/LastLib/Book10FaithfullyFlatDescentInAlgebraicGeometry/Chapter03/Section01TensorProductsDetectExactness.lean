import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter03.Dependencies

/-!
# 3.1 Tensor products detect exactness
-/

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter03

open scoped TensorProduct

theorem chapter03_flat_tensor_preserves_exact
    {A B M' M M'' : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M'] [AddCommGroup M] [AddCommGroup M'']
    [Module A M'] [Module A M] [Module A M''] [Module.Flat A B]
    (u : M' →ₗ[A] M) (v : M →ₗ[A] M'') (h : Function.Exact u v) :
    Function.Exact (u.lTensor B) (v.lTensor B) := by
  sorry

theorem chapter03_tensor_exact_iff
    {A B M' M M'' : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M'] [AddCommGroup M] [AddCommGroup M'']
    [Module A M'] [Module A M] [Module A M''] [Module.FaithfullyFlat A B]
    (u : M' →ₗ[A] M) (v : M →ₗ[A] M'') :
    Function.Exact u v ↔
      Function.Exact (u.lTensor B) (v.lTensor B) :=
  (Module.FaithfullyFlat.lTensor_exact_iff_exact A B u v).symm

theorem chapter03_tensor_preserves_exact
    {A B M' M M'' : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M'] [AddCommGroup M] [AddCommGroup M'']
    [Module A M'] [Module A M] [Module A M''] [Module.FaithfullyFlat A B]
    (u : M' →ₗ[A] M) (v : M →ₗ[A] M'') (h : Function.Exact u v) :
    Function.Exact (u.lTensor B) (v.lTensor B) :=
  (chapter03_tensor_exact_iff u v).1 h

theorem chapter03_tensor_reflects_exact
    {A B M' M M'' : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M'] [AddCommGroup M] [AddCommGroup M'']
    [Module A M'] [Module A M] [Module A M''] [Module.FaithfullyFlat A B]
    (u : M' →ₗ[A] M) (v : M →ₗ[A] M'')
    (h : Function.Exact (u.lTensor B) (v.lTensor B)) :
    Function.Exact u v :=
  (chapter03_tensor_exact_iff u v).2 h

theorem chapter03_tensor_injective_iff
    {A B M M' : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [AddCommGroup M'] [Module A M] [Module A M']
    [Module.FaithfullyFlat A B] (u : M →ₗ[A] M') :
    Function.Injective u ↔ Function.Injective (u.lTensor B) :=
  (Module.FaithfullyFlat.lTensor_injective_iff_injective A B u).symm

theorem chapter03_tensor_surjective_iff
    {A B M M' : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [AddCommGroup M'] [Module A M] [Module A M']
    [Module.FaithfullyFlat A B] (u : M →ₗ[A] M') :
    Function.Surjective u ↔ Function.Surjective (u.lTensor B) :=
  (Module.FaithfullyFlat.lTensor_surjective_iff_surjective A B u).symm

theorem chapter03_tensor_bijective_iff
    {A B M M' : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [AddCommGroup M'] [Module A M] [Module A M']
    [Module.FaithfullyFlat A B] (u : M →ₗ[A] M') :
    Function.Bijective u ↔ Function.Bijective (u.lTensor B) :=
  (Module.FaithfullyFlat.lTensor_bijective_iff_bijective A B u).symm

theorem chapter03_tensor_zero_iff
    {A B M M' : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [AddCommGroup M'] [Module A M] [Module A M']
    [Module.FaithfullyFlat A B] (u : M →ₗ[A] M') :
    u = 0 ↔ u.lTensor B = 0 :=
  Module.FaithfullyFlat.zero_iff_lTensor_zero A B u

theorem chapter03_tensor_map_eq_iff
    {A B M M' : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [AddCommGroup M'] [Module A M] [Module A M']
    [Module.FaithfullyFlat A B] (u v : M →ₗ[A] M') :
    u = v ↔ u.lTensor B = v.lTensor B := by
  sorry

theorem chapter03_tensor_vanishes_iff
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module.FaithfullyFlat A B] :
    Subsingleton (B ⊗[A] M) ↔ Subsingleton M :=
  Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right A B

theorem chapter03_ideal_contraction
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] (I : Ideal A) :
    Ideal.comap (algebraMap A B) (Ideal.map (algebraMap A B) I) = I := by
  exact Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) I

theorem chapter03_ideal_extension_injective
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] :
    Function.Injective (Ideal.map (algebraMap A B)) := by
  exact Ideal.map_injective_of_faithfullyFlat (B := B)

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter03
