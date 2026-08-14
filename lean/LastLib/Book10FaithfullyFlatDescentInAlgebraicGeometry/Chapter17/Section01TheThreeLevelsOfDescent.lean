import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter17.Dependencies

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter17

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11
open scoped AlgebraicGeometry TensorProduct

universe u v

/-! ### 17.1 The three levels of descent -/

/- The faithfully flat tensor theorem is the algebraic preservation-and-reflection bridge used
   throughout the synthesis.  The orientation below keeps the un-tensored sequence on the left. -/
theorem faithfullyFlat_lTensor_exact_iff_exact
    {A M N P : Type u} [CommRing A] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module A M] [Module A N] [Module A P]
    (B : Type u) [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    (f : M →ₗ[A] N) (g : N →ₗ[A] P) :
    Function.Exact f g ↔ Function.Exact (f.lTensor B) (g.lTensor B) := by
  exact (Module.FaithfullyFlat.lTensor_exact_iff_exact A B f g).symm

theorem faithfullyFlat_lTensor_injective_iff_injective
    {A M N : Type u} [CommRing A] [AddCommGroup M] [AddCommGroup N]
    [Module A M] [Module A N]
    (B : Type u) [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    (f : M →ₗ[A] N) :
    Function.Injective f ↔ Function.Injective (f.lTensor B) := by
  exact (Module.FaithfullyFlat.lTensor_injective_iff_injective (R := A) (M := B) f).symm

theorem faithfullyFlat_lTensor_surjective_iff_surjective
    {A M N : Type u} [CommRing A] [AddCommGroup M] [AddCommGroup N]
    [Module A M] [Module A N]
    (B : Type u) [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    (f : M →ₗ[A] N) :
    Function.Surjective f ↔ Function.Surjective (f.lTensor B) := by
  exact (Module.FaithfullyFlat.lTensor_surjective_iff_surjective (R := A) (M := B) f).symm

theorem faithfullyFlat_lTensor_bijective_iff_bijective
    {A M N : Type u} [CommRing A] [AddCommGroup M] [AddCommGroup N]
    [Module A M] [Module A N]
    (B : Type u) [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    (f : M →ₗ[A] N) :
    Function.Bijective f ↔ Function.Bijective (f.lTensor B) := by
  exact (Module.FaithfullyFlat.lTensor_bijective_iff_bijective (R := A) (M := B) f).symm

theorem faithfullyFlat_baseChange_unit_injective
    {A B M : Type u} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.FaithfullyFlat A B] :
    Function.Injective (amitsurUnit A B M) := by
  exact Module.FaithfullyFlat.tensorProduct_mk_injective M

/- LOCAL_DEPENDENCY_GUESS: the pinned tensor API supplies exactness preservation and reflection,
   but not the full Amitsur equalizer statement for arbitrary modules. -/
theorem amitsur_module_exact
    {A B M : Type u} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.FaithfullyFlat A B] :
    Function.Exact (amitsurUnit A B M) (amitsurDifference A B M) := by
  sorry

theorem amitsur_module_equalizer_range
    {A B M : Type u} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.FaithfullyFlat A B] :
    LinearMap.range (amitsurUnit A B M) = LinearMap.ker (amitsurDifference A B M) := by
  sorry

theorem amitsur_algebra_exact_of_faithfullyFlat
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] :
    Function.Exact (Algebra.linearMap A B)
      (Algebra.TensorProduct.includeLeftSubRight A B) := by
  exact Chapter11.SchemeDescent.amitsur_exact A B
    (Chapter11.SchemeDescent.AmitsurEqualizerCondition.of_faithfullyFlat A B)

theorem amitsur_algebra_equalizer_range_of_faithfullyFlat
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] :
    Algebra.TensorProduct.includeLeftRingHom.eqLocus
        Algebra.TensorProduct.includeRight.toRingHom (S := B ⊗[A] B) =
      Set.range (algebraMap A B) := by
  exact Chapter11.SchemeDescent.amitsur_equalizer_eq_range A B
    (Chapter11.SchemeDescent.AmitsurEqualizerCondition.of_faithfullyFlat A B)

/- The module-category formulation packages effective descent through the canonical comonadic
   extension-of-scalars adjunction. -/
theorem module_extension_is_comonadic_of_faithfullyFlat
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : f.FaithfullyFlat) :
    ComonadicLeftAdjoint (ModuleCat.extendScalars f) := by
  exact ModuleCat.comonadicExtendScalars hf

theorem module_flatness_iff_after_faithfullyFlat_baseChange
    {A B M : Type u} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.FaithfullyFlat A B] :
    Module.Flat A M ↔ Module.Flat B (B ⊗[A] M) := by
  exact (Module.Flat.iff_flat_tensorProduct B).symm

/- Affine spectra reverse the arrows in the algebraic diagram. -/
theorem affineSpecOfRingHom_comp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) :
    affineSpecOfRingHom (g.comp f) =
      affineSpecOfRingHom g ≫ affineSpecOfRingHom f := by
  simp [affineSpecOfRingHom]

theorem affineSpecOfRingHom_id
    {A : Type u} [CommRing A] :
    affineSpecOfRingHom (RingHom.id A) = 𝟙 (AlgebraicGeometry.Spec (.of A)) := by
  simp [affineSpecOfRingHom]

theorem every_scheme_has_affine_neighborhoods (X : Scheme.{u}) :
    Chapter11.SchemeDescent.HasAffineNeighbourhoods X := by
  exact Chapter11.SchemeDescent.scheme_has_affine_neighbourhoods X

theorem stable_affine_open_cover_exists
    {S T : Scheme.{u}} {p : T ⟶ S}
    (D : Chapter11.SchemeDescent.Datum p) (hp : FpqcMorphism p) :
    Nonempty (Chapter11.SchemeDescent.StableAffineOpenCover D) := by
  exact Chapter11.SchemeDescent.stableAffineOpenCover D hp

theorem relation_first_is_faithfullyFlat
    {S T : Scheme.{u}} {p : T ⟶ S} (D : Chapter11.SchemeDescent.Datum p)
    (hp : FpqcMorphism p) :
    Chapter11.Scheme.IsFaithfullyFlat (Chapter11.SchemeDescent.relationFirst D) := by
  exact Chapter11.SchemeDescent.relationFirst_isFaithfullyFlat D hp

theorem relation_second_is_faithfullyFlat
    {S T : Scheme.{u}} {p : T ⟶ S} (D : Chapter11.SchemeDescent.Datum p)
    (hp : FpqcMorphism p) :
    Chapter11.Scheme.IsFaithfullyFlat (Chapter11.SchemeDescent.relationSecond D) := by
  exact Chapter11.SchemeDescent.relationSecond_isFaithfullyFlat D hp

/- The triple tensor/transitivity clause is the same cocycle identity used by geometric descent. -/
theorem scheme_datum_triple_cocycle
    {ι : Type v} {S : Scheme.{u}} {X : ι → Scheme.{u}}
    {f : ∀ i, X i ⟶ S} (D : Chapter11.SchemeDescent.Data f) {Y : Scheme}
    (q : Y ⟶ S) {i₁ i₂ i₃ : ι} (g₁ : Y ⟶ X i₁) (g₂ : Y ⟶ X i₂)
    (g₃ : Y ⟶ X i₃) (hg₁ : g₁ ≫ f i₁ = q) (hg₂ : g₂ ≫ f i₂ = q)
    (hg₃ : g₃ ≫ f i₃ = q) :
    D.hom q g₁ g₂ hg₁ hg₂ ≫ D.hom q g₂ g₃ hg₂ hg₃ =
      D.hom q g₁ g₃ hg₁ hg₃ := by
  exact Chapter11.SchemeDescent.datum_cocycle D q g₁ g₂ g₃ hg₁ hg₂ hg₃

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter17
