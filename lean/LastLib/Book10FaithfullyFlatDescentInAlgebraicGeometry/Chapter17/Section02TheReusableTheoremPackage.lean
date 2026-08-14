import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter17.Dependencies

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter17

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02
open LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10
open scoped AlgebraicGeometry TensorProduct

universe u v

/-! ### 17.2 Reusable theorem package -/

/- The first reduction is finite and affine on every affine part of the base. -/
theorem fpqc_family_has_finite_affine_refinement
    {S : Scheme.{u}} {I : Type v} {F : SchemeFamily S I}
    (hF : FpqcCoveringFamily F) {U : S.Opens} (hU : IsAffineOpen U) :
    Nonempty (AffineFiniteFamilyReduction F U) := by
  exact finiteFamilyReduction_affine_refinement hU.isCompact hF

theorem fpqc_family_has_finite_reduction
    {S : Scheme.{u}} {I : Type v} {F : SchemeFamily S I}
    (hF : FpqcCoveringFamily F) {U : S.Opens} (hU : IsAffineOpen U) :
    Nonempty (FiniteFamilyReduction F U) := by
  exact (fpqcCoveringFamily_iff_affine_reductions F).mp hF |>.2 U hU

/- The finite reduction API is the formal reason that no infinite coproduct or product is needed
   in the fpqc construction. -/
theorem finite_affine_reduction_avoids_infinite_products
    {S : Scheme.{u}} {I : Type v} {F : SchemeFamily S I}
    (hF : FpqcCoveringFamily F) :
    ∀ U : S.Opens, IsAffineOpen U →
      Nonempty (AffineFiniteFamilyReduction F U) := by
  intro U hU
  exact fpqc_family_has_finite_affine_refinement hF hU

/- Schemes and their morphisms are effective and fully faithful for singleton fpqc covers. -/
theorem schemes_effective_fpqc_descent
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : FpqcMorphism p) :
    Chapter11.SchemeDescent.IsEffective (fun _ : PUnit => p) := by
  exact Chapter11.SchemeDescent.singleton_effective_of_fpqc p hp

theorem scheme_morphisms_descend_fully_faithfully
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : FpqcMorphism p) :
    (Chapter11.SchemeDescent.overPseudofunctor.toDescentData
      (fun _ : PUnit => p)).FullyFaithful := by
  exact Chapter11.SchemeDescent.singleton_morphisms_descend_uniquely p hp

theorem schemes_effective_for_fpqc_family
    {S : Scheme.{u}} (𝒰 : Chapter11.FpqcFamily S) :
    Chapter11.SchemeDescent.IsEffective (fun i => 𝒰.cover.f i) := by
  exact Chapter11.SchemeDescent.family_effective_of_fpqc 𝒰

theorem scheme_morphisms_descend_for_fpqc_family
    {S : Scheme.{u}} (𝒰 : Chapter11.FpqcFamily S) :
    (Chapter11.SchemeDescent.overPseudofunctor.toDescentData
      (fun i => 𝒰.cover.f i)).FullyFaithful := by
  exact Chapter11.SchemeDescent.family_morphisms_descend_uniquely 𝒰

theorem schemes_and_morphisms_effective_fpqc_descent
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : FpqcMorphism p) :
    Chapter11.SchemeDescent.IsEffective (fun _ : PUnit => p) ∧
      (Chapter11.SchemeDescent.overPseudofunctor.toDescentData
        (fun _ : PUnit => p)).FullyFaithful :=
  ⟨schemes_effective_fpqc_descent p hp, scheme_morphisms_descend_fully_faithfully p hp⟩

theorem descended_scheme_unique_up_to_unique_iso
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : FpqcMorphism p)
    {D : Chapter11.SchemeDescent.Datum p}
    (A B : Chapter11.SchemeDescent.Effective (fun _ : PUnit => p) D) :
    Nonempty (Chapter11.SchemeDescent.CompatibleIso A B) ∧
      ∀ e₁ e₂ : Chapter11.SchemeDescent.CompatibleIso A B, e₁ = e₂ := by
  exact Chapter11.SchemeDescent.effective_unique_up_to_unique_iso A B
    (scheme_morphisms_descend_fully_faithfully p hp)

/- Modules use Mathlib's comonadic extension-of-scalars theorem; the algebra statement is the
   corresponding Amitsur equalizer. -/
theorem modules_have_effective_faithfullyFlat_descent
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : f.FaithfullyFlat) :
    ComonadicLeftAdjoint (ModuleCat.extendScalars f) := by
  exact module_extension_is_comonadic_of_faithfullyFlat f hf

theorem algebras_have_amitsur_effective_descent
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] :
    Chapter11.SchemeDescent.AmitsurEqualizerCondition A B := by
  exact Chapter11.SchemeDescent.AmitsurEqualizerCondition.of_faithfullyFlat A B

theorem quasiCoherent_sheaves_effective_fpqc_descent
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : FpqcMorphism p) :
    IsEffectiveDescent quasiCoherentModuleSheafPseudofunctor (fun _ : PUnit => p) := by
  sorry

theorem quasiCoherent_sheaf_morphisms_descend_fully_faithfully
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : FpqcMorphism p) :
    IsFullyFaithfulDescent quasiCoherentModuleSheafPseudofunctor (fun _ : PUnit => p) := by
  sorry

/- Finiteness and local freeness are stated on the actual base-changed module or morphism. -/

theorem module_finite_generation_descends
    {A B M : Type u} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.FaithfullyFlat A B]
    (hM : Module.Finite B (B ⊗[A] M)) : Module.Finite A M := by
  letI : Module.Finite B (B ⊗[A] M) := hM
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B

/- LOCAL_DEPENDENCY_GUESS: finite presentation and finite projectivity use the same Amitsur
   descent construction, but are not packaged together in the pinned module API. -/
theorem module_finite_presentation_descends
    {A B M : Type u} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.FaithfullyFlat A B]
    (hM : Module.FinitePresentation B (B ⊗[A] M)) :
    Module.FinitePresentation A M := by
  sorry

def IsFiniteProjectiveModule (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  Module.Finite R M ∧ Module.Projective R M

theorem module_finite_projectivity_descends
    {A B M : Type u} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.FaithfullyFlat A B]
    (hM : IsFiniteProjectiveModule B (B ⊗[A] M)) :
    IsFiniteProjectiveModule A M := by
  sorry

theorem finite_flatness_descends
    {A B M : Type u} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.FaithfullyFlat A B]
    [Module.Flat B (B ⊗[A] M)] : Module.Flat A M := by
  exact Module.Flat.of_flat_tensorProduct A M B

/- LOCAL_DEPENDENCY_GUESS: the scheme-level rank profile packages finite, flat, finite
   presentation, and constant fiber rank; its faithful-flat reflection is a Chapter 10 bridge. -/
theorem finite_locally_free_rank_descends
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (d : ℕ)
    (hg : FpqcMorphism g)
    (hup : FiniteLocallyFreeProfile (baseChangeToBase f g) d) :
    FiniteLocallyFreeProfile f d := by
  sorry

/- The property package is deliberately a morphism-property API: the local theorem is applied
   only after the descended object has been constructed. -/
structure FpqcMorphismDescentPackage : Prop where
  affine : IsFpqcLocalMorphismProperty (@IsAffineHom)
  finite : IsFpqcLocalMorphismProperty (@IsFinite)
  finiteLocallyFree : IsFpqcLocalMorphismProperty FiniteLocallyFreeMorphismProperty
  quasiCompact : IsFpqcLocalMorphismProperty (@QuasiCompact)
  quasiSeparated : IsFpqcLocalMorphismProperty (@QuasiSeparated)
  separated : IsFpqcLocalMorphismProperty (@IsSeparated)
  finiteType : IsFpqcLocalMorphismProperty (@LocallyOfFiniteType)
  finitePresentation : IsFpqcLocalMorphismProperty (@LocallyOfFinitePresentation)
  flat : IsFpqcLocalMorphismProperty (@Flat)
  proper : IsFpqcLocalMorphismProperty (@IsProper)
  smooth : IsFpqcLocalMorphismProperty (@Smooth)
  etale : IsFpqcLocalMorphismProperty (@Etale)
  unramified : IsFpqcLocalMorphismProperty (@FormallyUnramified)

/- LOCAL_DEPENDENCY_GUESS: the pinned Mathlib files provide many of these descent instances, but
   the complete book-facing package (especially affine, finite, and finite-locally-free) is not
   exposed by one earlier declaration. -/
theorem fpqc_morphism_descent_package : FpqcMorphismDescentPackage := by
  sorry

/- A structured fiber is any category whose pseudofunctor remembers the structure maps and the
   triple cocycle.  This is the common interface for line bundles, vector bundles, tensors,
   pairings, sections, Cartier divisors, finite-flat group schemes, actions, and torsors. -/
structure StructuredFpqcDescentPackage
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v, u})
    {ι : Type v} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S) : Prop where
  effective : IsEffectiveDescent F f
  fullyFaithful : IsFullyFaithfulDescent F f

theorem structured_objects_and_structure_maps_descend
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v, u})
    {ι : Type v} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
    (hF : StructuredFpqcDescentPackage F f) :
    IsEffectiveDescent F f ∧ IsFullyFaithfulDescent F f :=
  ⟨hF.effective, hF.fullyFaithful⟩

/- The intrinsic affine envelope is the canonical test for quasi-affineness. -/
theorem intrinsic_affine_envelope_is_affine (X : Scheme.{u}) :
    IsAffine (intrinsicAffineEnvelope X) := by
  infer_instance

theorem quasiAffine_iff_intrinsic_affine_envelope
    (X : Scheme.{u}) :
    Scheme.IsQuasiAffine X ↔ IsQuasiAffineViaIntrinsicAffineEnvelope X := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the local-on-the-base theorem for quasi-affineness is routed through
   `toSpecΓ`; the pinned snapshot does not expose the full relative envelope statement. -/
theorem quasiAffine_descends_through_intrinsic_affine_envelope
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (hfqc : QuasiCompact f) (hfqs : QuasiSeparated f) (hg : FpqcMorphism g)
    (hup : Scheme.IsQuasiAffine (baseChange f g)) :
    Scheme.IsQuasiAffine X := by
  sorry

/- Positive geometry: a finite immersion system is the global form of the local embeddings. -/
structure FiniteEmbeddingSystem {X S : Scheme.{u}} (f : X ⟶ S) where
  witness : Book8RelativeImmersionWitness f
  finite : Book8IsFiniteDimensionalLocallyOnBase witness.projectiveBundle

structure FiniteProjectiveEmbeddingSystem {X S : Scheme.{u}} (f : X ⟶ S) where
  witness : Book8RelativeClosedImmersionWitness f
  finite : Book8IsFiniteDimensionalLocallyOnBase witness.projectiveBundle

theorem quasiProjective_of_finite_embedding_system
    {X S : Scheme.{u}} {f : X ⟶ S} (D : FiniteEmbeddingSystem f) :
    Book8IsQuasiProjectiveMorphism f :=
  ⟨D.witness⟩

theorem projective_of_finite_projective_embedding_system
    {X S : Scheme.{u}} {f : X ⟶ S} (D : FiniteProjectiveEmbeddingSystem f) :
    Book8IsProjectiveMorphism f :=
  ⟨D.witness⟩

/- LOCAL_DEPENDENCY_GUESS: finite presentation makes the local ample embeddings finite and allows
   their finite affine systems to be assembled into a global quasi-projective model. -/
theorem finitePresentation_ample_gives_quasiProjective
    {X S : Scheme.{u}} (f : X ⟶ S) (L : Book8LineBundle X)
    (hfqc : QuasiCompact f) (hfqs : QuasiSeparated f)
    (hfp : LocallyOfFinitePresentation f) (hL : Book8IsAmple f L) :
    Book8IsQuasiProjectiveMorphism f := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: properness upgrades the same finite positive embedding system to a
   finite closed embedding, hence to a projective morphism. -/
theorem finitePresentation_ample_proper_gives_projective
    {X S : Scheme.{u}} (f : X ⟶ S) (L : Book8LineBundle X)
    (hfqc : QuasiCompact f) (hfqs : QuasiSeparated f) (hproper : IsProper f)
    (hfp : LocallyOfFinitePresentation f) (hL : Book8IsAmple f L) :
    Book8IsProjectiveMorphism f := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: quasi-projectivity is local on the base for quasi-compact,
   quasi-separated morphisms after a faithfully flat quasi-compact cover. -/
theorem quasiProjective_descends_local_on_base
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (hfqc : QuasiCompact f) (hfqs : QuasiSeparated f)
    (hg : FpqcMorphism g)
    (hup : Book8IsQuasiProjectiveMorphism (baseChangeToBase f g)) :
    Book8IsQuasiProjectiveMorphism f := by
  sorry

theorem projective_descends_with_compatible_ample_data
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (L : Book8LineBundle X)
    (M : Book8LineBundle (baseChange f g)) (hM : IsBaseChangeOf f g L M)
    (hfqc : QuasiCompact f) (hfqs : QuasiSeparated f) (hproper : IsProper f)
    (hfp : LocallyOfFinitePresentation f) (hg : FpqcMorphism g)
    (hMample : Book8IsAmple (baseChangeToBase f g) M) :
    Book8IsAmple f L ∧ Book8IsProjectiveMorphism f := by
  exact projectivity_descent_from_upstairs_polarized_data f g L M hM hfqc hfqs hproper hfp
      ⟨hg.1, hg.2.1⟩ hg.2.2 hMample

/- A finite locally free cover is the unpolarized norm input. -/
structure FiniteLocallyFreeCoverData {T S : Scheme.{u}} (q : T ⟶ S) where
  rank : ℕ
  profile : FiniteLocallyFreeProfile q rank
  surjective : Surjective q

noncomputable def normLineBundle
    {Z T : Scheme.{u}} (q : Z ⟶ T)
    [Chapter10PicardOperations T] [Chapter10DeterminantLineAPI q]
    (M : Chapter10LineBundle Z) : Chapter10LineBundle T :=
  chapter10Norm q M

theorem normLineBundle_determinant_formula
    {Z T : Scheme.{u}} (q : Z ⟶ T)
    [Chapter10PicardOperations T] [Chapter10DeterminantLineAPI q]
    (M : Chapter10LineBundle Z) :
    normLineBundle q M =
      chapter10PicardTensor (chapter10DeterminantLine q M)
        (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Chapter10PicardOperations.dual
          (chapter10DeterminantLine q (chapter10StructureSheafLineBundle Z))) := by
  exact chapter10_norm_determinant_formula q M

/- LOCAL_DEPENDENCY_GUESS: this is the norm-ampleness bridge used when a finite locally free
   cover supplies a polarization upstairs but no line bundle has yet been descended. -/
theorem normLineBundle_is_ample_of_finiteLocallyFree_cover
    {Z T : Scheme.{u}} (q : Z ⟶ T) (d : ℕ)
    (hq : FiniteLocallyFreeProfile q d)
    (hsurj : Surjective q)
    [Chapter10PicardOperations T] [Chapter10DeterminantLineAPI q]
    (M : Chapter10LineBundle Z)
    (hM : Book8IsAmple (𝟙 Z) (Chapter09AsBook8LineBundle M)) :
    Book8IsAmple (𝟙 T)
      (Chapter09AsBook8LineBundle (normLineBundle q M)) := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: norms turn an unpolarized finite locally free cover with an upstairs
   projective model into a downstairs projective model. -/
theorem projective_descends_from_unpolarized_finiteLocallyFree_cover
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (cover : FiniteLocallyFreeCoverData g)
    (hup : Book8IsProjectiveMorphism (baseChangeToBase f g))
    [Chapter10PicardOperations X]
    [Chapter10DeterminantLineAPI (baseChangeToSource f g)] :
    Book8IsProjectiveMorphism f := by
  sorry

/- Effective Cartier divisors provide the positive line-bundle input in generalized elliptic and
   related moduli situations. -/
noncomputable def cartierLineBundle {X : Scheme.{u}}
    (D : EffectiveCartierDivisor X)
    [Chapter10IdealDualAPI X] : Book8LineBundle X :=
  Chapter09AsBook8LineBundle (chapter10OofD D)

structure CompatiblePositiveDivisorData
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) where
  downstairs : EffectiveCartierDivisor X
  upstairs : EffectiveCartierDivisor (baseChange f g)
  lineBundle_isBaseChangeOf :
    IsBaseChangeOf f g (cartierLineBundle downstairs) (cartierLineBundle upstairs)
  upstairs_ample : Book8IsAmple (baseChangeToBase f g) (cartierLineBundle upstairs)

theorem projectivity_descends_from_compatible_positive_divisor
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [Chapter10IdealDualAPI X] [Chapter10IdealDualAPI (baseChange f g)]
    (D : CompatiblePositiveDivisorData f g)
    (hfqc : QuasiCompact f) (hfqs : QuasiSeparated f) (hproper : IsProper f)
    (hfp : LocallyOfFinitePresentation f) (hg : FpqcMorphism g) :
    Book8IsProjectiveMorphism f := by
  exact (projective_descends_with_compatible_ample_data f g
    (cartierLineBundle D.downstairs) (cartierLineBundle D.upstairs)
    D.lineBundle_isBaseChangeOf hfqc hfqs hproper hfp hg D.upstairs_ample).2

structure RigidifiedAmpleLineBundleData {X S : Scheme.{u}} (f : X ⟶ S) where
  lineBundle : Book8LineBundle X
  section : S ⟶ X
  section_over : section ≫ f = 𝟙 S
  rigidification :
    (lineBundle.pullback section).Isomorphic
      (LineBundle.trivial S)
  ample : Book8IsAmple f lineBundle

structure CompatibleRigidifiedAmpleLineBundleData
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) where
  downstairs : RigidifiedAmpleLineBundleData f
  upstairs : Book8LineBundle (baseChange f g)
  lineBundle_isBaseChangeOf : IsBaseChangeOf f g downstairs.lineBundle upstairs
  upstairs_ample : Book8IsAmple (baseChangeToBase f g) upstairs

/- LOCAL_DEPENDENCY_GUESS: the rigidification is part of the structured descent datum in the
   generalized elliptic and PEL applications; the positivity conclusion is the same polarized
   projectivity bridge as above. -/
theorem projectivity_descends_from_compatible_rigidified_ample_line_bundle
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (D : CompatibleRigidifiedAmpleLineBundleData f g)
    (hfqc : QuasiCompact f) (hfqs : QuasiSeparated f) (hproper : IsProper f)
    (hfp : LocallyOfFinitePresentation f) (hg : FpqcMorphism g) :
    Book8IsProjectiveMorphism f := by
  exact (projective_descends_with_compatible_ample_data f g D.downstairs.lineBundle
    D.upstairs D.lineBundle_isBaseChangeOf hfqc hfqs hproper hfp hg D.upstairs_ample).2

/- The structure-package interface is the single place where the group law, action, torsor
   equations, determinant condition, or polarization cocycle is supplied to descent. -/
theorem finiteFlatGroupSchemes_actions_and_torsors_descend
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v, u})
    {ι : Type v} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
    (hF : StructuredFpqcDescentPackage F f) :
    IsEffectiveDescent F f ∧ IsFullyFaithfulDescent F f := by
  exact structured_objects_and_structure_maps_descend F hF

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter17
