import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter01.Dependencies

/-!
# 1.3 The geometric meaning

The scheme-level predicates below keep flatness, surjectivity, quasi-compactness, and local finite
presentation separate.  The final family-refinement interface is intentionally small: the detailed
covering theory is developed in the next chapter, but the finite-control hypothesis is already
needed to state the warning in this chapter.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter01

noncomputable section

/-- A faithfully flat morphism of schemes. -/
def Chapter01FaithfullyFlatMorphism {T S : Scheme.{u}} (p : T ⟶ S) : Prop :=
  Flat p ∧ Surjective p

/-- An fpqc morphism, i.e. a faithfully flat quasi-compact morphism. -/
def Chapter01FpqcMorphism {T S : Scheme.{u}} (p : T ⟶ S) : Prop :=
  Chapter01FaithfullyFlatMorphism p ∧ QuasiCompact p

/-- An fppf morphism, i.e. a flat morphism locally of finite presentation. -/
def Chapter01FppfMorphism {T S : Scheme.{u}} (p : T ⟶ S) : Prop :=
  Flat p ∧ LocallyOfFinitePresentation p

/-- A surjective fppf morphism. -/
def Chapter01FppfCover {T S : Scheme.{u}} (p : T ⟶ S) : Prop :=
  Chapter01FppfMorphism p ∧ Surjective p

theorem chapter01_flat_morphism_iff_stalk_maps {T S : Scheme.{u}} (p : T ⟶ S) :
    Flat p ↔ ∀ x, (p.stalkMap x).hom.Flat :=
  Flat.iff_flat_stalkMap p

theorem chapter01_fpqcMorphism_of_fppfCover_of_quasiCompact
    {T S : Scheme.{u}} {p : T ⟶ S} (hp : Chapter01FppfCover p)
    (hpqc : QuasiCompact p) : Chapter01FpqcMorphism p := by
  exact ⟨⟨hp.1.1, hp.2⟩, hpqc⟩

theorem chapter01_specMap_faithfullyFlat_iff
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Chapter01FaithfullyFlatMorphism (Spec.map f) ↔ f.hom.FaithfullyFlat := by
  simpa [Chapter01FaithfullyFlatMorphism] using
    (flat_and_surjective_SpecMap_iff f)

theorem chapter01_specMap_ringHom_faithfullyFlat_iff
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    Chapter01FaithfullyFlatMorphism (chapter01SpecMap f) ↔ f.FaithfullyFlat := by
  simpa [chapter01SpecMap, Chapter01FaithfullyFlatMorphism] using
    (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom f))

/- LOCAL_DEPENDENCY_GUESS: the detailed fpqc/fppf family refinement construction is supplied by
Chapter 2.  This chapter records the weakest witness needed for its forward reference. -/
theorem chapter01_surjective_fppf_morphism_has_fpqc_family_refinement
    {T S : Scheme.{u}} (p : T ⟶ S) (hp : Chapter01FppfMorphism p) (hs : Surjective p) :
    Nonempty (Chapter01FpqcFamilyRefinement p) := by
  sorry

/-- A finite flat surjective morphism is the finite locally free cover used in the examples. -/
def Chapter01FiniteLocallyFreeCover {T S : Scheme.{u}} (p : T ⟶ S) : Prop :=
  Nonempty T ∧ IsFinite p ∧ Flat p ∧ Surjective p

theorem chapter01_finiteLocallyFreeCover_isFaithfullyFlat
    {T S : Scheme.{u}} {p : T ⟶ S} (hp : Chapter01FiniteLocallyFreeCover p) :
    Chapter01FaithfullyFlatMorphism p := by
  exact ⟨hp.2.2.1, hp.2.2.2⟩

theorem chapter01_fieldExtension_faithfullyFlat
    (K L : Type u) [Field K] [Field L] [Algebra K L] :
    (algebraMap K L).FaithfullyFlat := by
  sorry

theorem chapter01_fieldExtension_spec_cover
    (K L : Type u) [Field K] [Field L] [Algebra K L] :
    Chapter01FaithfullyFlatMorphism
      (chapter01SpecMap (algebraMap K L)) := by
  apply (chapter01_specMap_ringHom_faithfullyFlat_iff (algebraMap K L)).2
  exact chapter01_fieldExtension_faithfullyFlat K L

/-- The coproduct of the members of an open cover is the corresponding single algebraic map. -/
noncomputable def chapter01OpenCoverSigmaMap {S : Scheme.{u}} (𝒰 : S.OpenCover) :
    (∐ 𝒰.X) ⟶ S :=
  Sigma.desc 𝒰.f

theorem chapter01_openCover_component_flat {S : Scheme.{u}} (𝒰 : S.OpenCover)
    (i : 𝒰.I₀) : Flat (𝒰.f i) := by
  infer_instance

theorem chapter01_openCover_sigma_isFaithfullyFlat {S : Scheme.{u}} (𝒰 : S.OpenCover) :
    Chapter01FaithfullyFlatMorphism (chapter01OpenCoverSigmaMap 𝒰) := by
  constructor
  · infer_instance
  · exact Surjective.sigmaDesc_of_union_range_eq_univ 𝒰.iUnion_range

/-- The localization map is flat even before one asks whether it covers the target. -/
theorem chapter01_localization_flat
    (A : Type u) [CommRing A] (f : A) :
    RingHom.Flat (algebraMap A (Localization.Away f)) := by
  exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers f))

/-- The product of two localizations packages the cover `D(f) ∪ D(g)` into one ring map. -/
def chapter01LocalizationProductMap
    (A : Type u) [CommRing A] (f g : A) :
    A →+* Localization.Away f × Localization.Away g :=
  (algebraMap A (Localization.Away f)).prod (algebraMap A (Localization.Away g))

def Chapter01LocalizationProductCoverCondition
    (A : Type u) [CommRing A] (f g : A) : Prop :=
  Ideal.span ({f, g} : Set A) = ⊤

theorem chapter01_localization_product_faithfullyFlat
    (A : Type u) [CommRing A] (f g : A)
    (hfg : Chapter01LocalizationProductCoverCondition A f g) :
    RingHom.FaithfullyFlat (chapter01LocalizationProductMap A f g) := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: pinned Mathlib supplies adic-completion flatness but not the
faithfulness theorem in this generality; the displayed statement is the standard noetherian
Jacobson-radical bridge required by the source. -/
theorem chapter01_adicCompletion_faithfullyFlat_of_noetherian_of_le_jacobson
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal A)) :
    RingHom.FaithfullyFlat (algebraMap A (AdicCompletion I A)) := by
  sorry

theorem chapter01_adicCompletion_flat_of_noetherian
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    Module.Flat A (AdicCompletion I A) := by
  infer_instance

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter01
