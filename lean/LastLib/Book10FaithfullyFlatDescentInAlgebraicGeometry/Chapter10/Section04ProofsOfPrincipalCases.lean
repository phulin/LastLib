import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.Section03TableOfDescendingProperties

/-!
## 10.4 Proofs of the principal cases

This file records the affine, topological, finiteness, properness, smoothness, étale, and
unramified proof interfaces used to justify the table.
-/

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

noncomputable section

universe u

/-! ### Quasi-compactness and affine-local finite conditions -/

/-- A quasi-compact morphism descends along an fpqc family; finite affine reductions are essential.
-/
theorem chapter10_quasiCompact_descends_from_family {S : Scheme.{u}} {I : Type*}
    (𝒞 : Chapter10FpqcCoverFamily S I) {X : Scheme.{u}}
    (f : X ⟶ S)
    (hf : ∀ i, QuasiCompact (chapter10BaseChangeMorphism f (𝒞.map i))) :
    QuasiCompact f := by
  exact chapter10_quasiCompact_descends_from_family_aux 𝒞 f hf

/-- Quasi-compactness is local for an fpqc covering family, with the finite-control hypothesis
made explicit in `Chapter10FpqcCoverFamily`. -/
theorem chapter10_quasiCompact_family_iff {S : Scheme.{u}} {I : Type*}
    (𝒞 : Chapter10FpqcCoverFamily S I) {X : Scheme.{u}} (f : X ⟶ S) :
    QuasiCompact f ↔
      ∀ i, QuasiCompact (chapter10BaseChangeMorphism f (𝒞.map i)) := by
  constructor
  · intro hf i
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @QuasiCompact) (IsPullback.of_hasPullback f (𝒞.map i)) hf
  · intro hf
    exact chapter10_quasiCompact_descends_from_family 𝒞 f hf

/-- On affine schemes, locally finite type is finite generation of the coordinate algebra. -/
theorem chapter10_affine_locallyOfFiniteType_iff
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    LocallyOfFiniteType (Spec.map φ) ↔ φ.hom.FiniteType := by
  exact HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)

/-- On affine schemes, locally finite presentation is finite presentation of the coordinate
algebra. -/
theorem chapter10_affine_locallyOfFinitePresentation_iff
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    LocallyOfFinitePresentation (Spec.map φ) ↔ φ.hom.FinitePresentation := by
  exact LocallyOfFinitePresentation.SpecMap_iff φ

/-- Locally finite type descends from an fpqc base change. -/
theorem chapter10_locallyOfFiniteType_descends {X S T : Scheme.{u}}
    (f : X ⟶ S) (p : T ⟶ S) (hp : Chapter10FpqcCover p)
    (hf : LocallyOfFiniteType (chapter10BaseChangeMorphism f p)) :
    LocallyOfFiniteType f := by
  have hdesc : MorphismProperty.DescendsAlong
      (@LocallyOfFiniteType : MorphismProperty Scheme.{u})
        chapter10FpqcMorphismProperty := inferInstance
  exact hdesc.of_isPullback (IsPullback.of_hasPullback f p).flip
    ⟨⟨hp.surjective, hp.flat⟩, hp.quasiCompact⟩ hf

/-- Locally finite presentation descends from an fpqc base change. -/
theorem chapter10_locallyOfFinitePresentation_descends {X S T : Scheme.{u}}
    (f : X ⟶ S) (p : T ⟶ S) (hp : Chapter10FpqcCover p)
    (hf : LocallyOfFinitePresentation (chapter10BaseChangeMorphism f p)) :
    LocallyOfFinitePresentation f := by
  have hdesc : MorphismProperty.DescendsAlong
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
        chapter10FpqcMorphismProperty := inferInstance
  exact hdesc.of_isPullback (IsPullback.of_hasPullback f p).flip
    ⟨⟨hp.surjective, hp.flat⟩, hp.quasiCompact⟩ hf

private theorem chapter10_ringHomFlat_codescendsAlong_faithfullyFlat :
    RingHom.CodescendsAlong RingHom.Flat RingHom.FaithfullyFlat := by
  apply RingHom.CodescendsAlong.mk RingHom.FaithfullyFlat RingHom.Flat.respectsIso
  introv h H
  rw [RingHom.faithfullyFlat_algebraMap_iff] at h
  rw [RingHom.flat_algebraMap_iff] at H ⊢
  exact Module.Flat.of_flat_tensorProduct (R := R) (M := T) S

/-- Flatness descends from an fpqc base change. -/
theorem chapter10_flat_descends {X S T : Scheme.{u}}
    (f : X ⟶ S) (p : T ⟶ S) (hp : Chapter10FpqcCover p)
    (hf : Flat (chapter10BaseChangeMorphism f p)) :
    Flat f := by
  have hdesc : MorphismProperty.DescendsAlong
      (@Flat : MorphismProperty Scheme.{u})
        chapter10FpqcMorphismProperty :=
    HasRingHomProperty.descendsAlong_flat
      chapter10_ringHomFlat_codescendsAlong_faithfullyFlat
  exact hdesc.of_isPullback (IsPullback.of_hasPullback f p).flip
    ⟨⟨hp.surjective, hp.flat⟩, hp.quasiCompact⟩ hf

/-- Finite type is locally finite type plus quasi-compactness. -/
theorem chapter10_finiteType_iff {X S : Scheme.{u}} (f : X ⟶ S) :
    chapter10FiniteType f ↔ LocallyOfFiniteType f ∧ QuasiCompact f := by
  rfl

/-- Finite presentation is locally finite presentation plus quasi-compactness. -/
theorem chapter10_finitePresentation_iff {X S : Scheme.{u}} (f : X ⟶ S) :
    chapter10FinitePresentation f ↔ LocallyOfFinitePresentation f ∧ QuasiCompact f := by
  rfl

/-- The finite part of finite locally free descent is obtained from finite module and flat descent.
-/
theorem chapter10_finiteLocallyFreeOfRank_descends {X S T : Scheme.{u}}
    (f : X ⟶ S) (p : T ⟶ S) (hp : Chapter10FpqcCover p) (r : ℕ)
    (hf : chapter10FiniteLocallyFreeOfRank (chapter10BaseChangeMorphism f p) r) :
    chapter10FiniteLocallyFreeOfRank f r := by
  exact (chapter10_finiteLocallyFreeOfRank_fpqc_local_on_base r f p hp).2 hf

/-! ### Properness -/

/-- The source-facing properness conjunction. -/
def chapter10ProperByDefinition {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  IsSeparated f ∧ UniversallyClosed f ∧ chapter10FiniteType f

/-- The source-facing conjunction agrees with Mathlib's proper-morphism predicate. -/
theorem chapter10_properByDefinition_iff_isProper {X S : Scheme.{u}} (f : X ⟶ S) :
    chapter10ProperByDefinition f ↔ IsProper f := by
  constructor
  · rintro ⟨hsep, hclosed, ⟨hfinite, hqc⟩⟩
    exact (isProper_iff f).2 ⟨hsep, hclosed, hfinite⟩
  · intro hf
    rcases (isProper_iff f).1 hf with ⟨hsep, hclosed, hfinite⟩
    have hqc : QuasiCompact f := by
      constructor
      intro U hU hUc
      exact (@Scheme.Hom.isProperMap _ _ f hclosed).isCompact_preimage hUc
    exact ⟨hsep, hclosed, ⟨hfinite, hqc⟩⟩

/-- Universal closedness descends by testing closed images after an fpqc base change. -/
theorem chapter10_universallyClosed_descends {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (hp : Chapter10FpqcCover p)
    (hf : UniversallyClosed (chapter10BaseChangeMorphism f p)) :
    UniversallyClosed f := by
  have hdesc : MorphismProperty.DescendsAlong
      (@UniversallyClosed : MorphismProperty Scheme.{u})
        chapter10FpqcMorphismProperty := inferInstance
  exact hdesc.of_isPullback (IsPullback.of_hasPullback f p).flip
    ⟨⟨hp.surjective, hp.flat⟩, hp.quasiCompact⟩ hf

/-- Properness descends after its finite-type and separated pieces have descended. -/
theorem chapter10_proper_descends {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (hp : Chapter10FpqcCover p)
    (hfinite : chapter10FiniteType (chapter10BaseChangeMorphism f p))
    (hsep : IsSeparated (chapter10BaseChangeMorphism f p))
    (hclosed : UniversallyClosed (chapter10BaseChangeMorphism f p)) :
    chapter10ProperByDefinition f := by
  apply (chapter10_properByDefinition_iff_isProper f).2
  apply (chapter10_proper_fpqc_local_on_base f p hp).2
  exact (isProper_iff (chapter10BaseChangeMorphism f p)).2
    ⟨hsep, hclosed, hfinite.1⟩

/-! ### Smoothness, étaleness, and unramifiedness -/

/-- The smooth-fiber criterion in the book-facing geometric-regularity vocabulary. -/
theorem chapter10_smooth_iff_lfp_flat_geometricallyRegularFibers {X S : Scheme.{u}} (f : X ⟶ S) :
    Smooth f ↔ LocallyOfFinitePresentation f ∧ Flat f ∧
      chapter10GeometricallyRegularFibers f := by
  constructor
  · intro hf
    have : Smooth f := hf
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro s
    change Smooth (pullback.snd f (S.fromSpecResidueField s))
    infer_instance
  · rintro ⟨hfp, hflat, hfibers⟩
    have : LocallyOfFinitePresentation f := hfp
    have : Flat f := hflat
    exact Smooth.of_smooth_fiberToSpecResidueField f hfibers

/-- A point of the base lifts to a point of a surjective cover. -/
theorem chapter10_fpqc_cover_lifts_point {S T : Scheme.{u}} (p : T ⟶ S)
    (hp : Chapter10FpqcCover p) (s : S) : ∃ t : T, p t = s := by
  exact hp.surjective.surj s

/-- Geometric regularity is unchanged by a faithfully flat extension of the residue field. -/
theorem chapter10_geometricallyRegular_iff_after_faithfullyFlat_field_extension
    {K L A : Type u} [Field K] [Field L] [CommRing A] [Algebra K L] [Algebra K A]
    (hL : (algebraMap K L).FaithfullyFlat) :
    chapter10GeometricallyRegularAlgebra K A ↔
      chapter10GeometricallyRegularAlgebra L (L ⊗[K] A) := by
  have : Module.FaithfullyFlat K L :=
    (RingHom.faithfullyFlat_algebraMap_iff).mp hL
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap K A))) ↔
    Smooth (Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[K] A))))
  constructor
  · intro h
    apply (HasRingHomProperty.Spec_iff (P := @Smooth)).2
    have h' : (CommRingCat.ofHom (algebraMap K A)).hom.Smooth :=
      (HasRingHomProperty.Spec_iff (P := @Smooth)).1 h
    have h'' : (algebraMap K A).Smooth := by
      simpa only [CommRingCat.hom_ofHom] using h'
    have h''' : Algebra.Smooth K A := (RingHom.smooth_algebraMap).1 h''
    have : Algebra.Smooth K A := h'''
    have h'''' : (algebraMap L (L ⊗[K] A)).Smooth :=
      (RingHom.smooth_algebraMap).2 inferInstance
    simpa only [CommRingCat.hom_ofHom] using h''''
  · intro h
    have h' : (CommRingCat.ofHom (algebraMap L (L ⊗[K] A))).hom.Smooth :=
      (HasRingHomProperty.Spec_iff (P := @Smooth)).1 h
    have h'' : (algebraMap L (L ⊗[K] A)).Smooth := by
      simpa only [CommRingCat.hom_ofHom] using h'
    have h''' : Algebra.Smooth L (L ⊗[K] A) :=
      (RingHom.smooth_algebraMap).1 h''
    have : Algebra.Smooth L (L ⊗[K] A) := h'''
    have h'''' : Algebra.Smooth K A :=
      Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat L
    apply (HasRingHomProperty.Spec_iff (P := @Smooth)).2
    have h''''' : (algebraMap K A).Smooth :=
      (RingHom.smooth_algebraMap).2 h''''
    simpa only [CommRingCat.hom_ofHom] using h'''''

/-- Smoothness descends from an fpqc base change; the proof uses the fiber criterion, point lifting,
and faithful-flat invariance of geometric regularity. -/
theorem chapter10_smooth_descends {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (hp : Chapter10FpqcCover p)
    (hf : Smooth (chapter10BaseChangeMorphism f p)) : Smooth f := by
  have hdesc : MorphismProperty.DescendsAlong
      (@Smooth : MorphismProperty Scheme.{u})
        chapter10FpqcMorphismProperty := inferInstance
  exact hdesc.of_isPullback (IsPullback.of_hasPullback f p).flip
    ⟨⟨hp.surjective, hp.flat⟩, hp.quasiCompact⟩ hf

/-- Étale morphisms are smooth of relative dimension zero. -/
theorem chapter10_etale_iff_smooth_relativeDimension_zero {X S : Scheme.{u}} (f : X ⟶ S) :
    Etale f ↔ SmoothOfRelativeDimension 0 f := by
  exact Etale.iff_smoothOfRelativeDimension_zero f

/-- The equivalent flat/unramified form of étaleness. -/
theorem chapter10_etale_iff_flat_and_unramified {X S : Scheme.{u}} (f : X ⟶ S) :
    Etale f ↔ Flat f ∧ chapter10Unramified f ∧ LocallyOfFinitePresentation f := by
  sorry

/-- Étaleness descends from an fpqc base change. -/
theorem chapter10_etale_descends {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (hp : Chapter10FpqcCover p)
    (hf : Etale (chapter10BaseChangeMorphism f p)) : Etale f := by
  have hdesc : MorphismProperty.DescendsAlong
      (@Etale : MorphismProperty Scheme.{u})
        chapter10FpqcMorphismProperty := inferInstance
  exact hdesc.of_isPullback (IsPullback.of_hasPullback f p).flip
    ⟨⟨hp.surjective, hp.flat⟩, hp.quasiCompact⟩ hf

/-- Unramifiedness descends by combining locally finite type descent with open-diagonal descent. -/
theorem chapter10_unramified_descends {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (hp : Chapter10FpqcCover p)
    (hf : chapter10Unramified (chapter10BaseChangeMorphism f p)) :
    chapter10Unramified f := by
  have hfin := chapter10_locallyOfFiniteType_descends f p hp hf.1
  have : LocallyOfFiniteType (chapter10BaseChangeMorphism f p) := hf.1
  have : IsOpenImmersion
      (pullback.diagonal (chapter10BaseChangeMorphism f p)) := hf.2
  have hformalBase : FormallyUnramified (chapter10BaseChangeMorphism f p) := inferInstance
  have hdesc : MorphismProperty.DescendsAlong
      (@FormallyUnramified : MorphismProperty Scheme.{u})
        chapter10FpqcMorphismProperty := inferInstance
  have hformal : FormallyUnramified f :=
    hdesc.of_isPullback (IsPullback.of_hasPullback f p).flip
      ⟨⟨hp.surjective, hp.flat⟩, hp.quasiCompact⟩ hformalBase
  have : LocallyOfFiniteType f := hfin
  have : FormallyUnramified f := hformal
  exact ⟨hfin, inferInstance⟩

/-- The table's ascent direction is supplied by base-change stability; descent is the only
direction requiring the fpqc arguments. -/
theorem chapter10_fpqc_local_iff {X S T : Scheme.{u}} (P : MorphismProperty Scheme.{u})
    (f : X ⟶ S) (p : T ⟶ S) (_hp : Chapter10FpqcCover p)
    (hdown : P f → P (chapter10BaseChangeMorphism f p))
    (hup : P (chapter10BaseChangeMorphism f p) → P f) :
    P f ↔ P (chapter10BaseChangeMorphism f p) := by
  exact ⟨hdown, hup⟩

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10
