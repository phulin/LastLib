import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter14.Section02DescendingQuasiAffineSchemes

/-!
# Book 10, Chapter 14, §14.3: finite presentation and openness

This leaf records the finite-presentation refinement of the envelope theorem,
the finite-principal-open consequence on affine charts, and the reusable
nonvanishing-locus interface for finite determinant families.
-/

noncomputable section

universe u

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter14

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

/-! ## Finite presentation -/

/-- Mathlib's finite-presentation convention for a scheme morphism: locally
of finite presentation together with quasi-compactness. -/
def chapter14FinitelyPresented {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  QuasiCompact f ∧ LocallyOfFinitePresentation f

theorem chapter14_finitelyPresented_iff {X S : Scheme.{u}} (f : X ⟶ S) :
    chapter14FinitelyPresented f ↔
      QuasiCompact f ∧ LocallyOfFinitePresentation f :=
  Iff.rfl

theorem chapter14_finitelyPresented_of_fpqc_base_change
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (hg : chapter14Fpqc g)
    (hXT : chapter14FinitelyPresented (chapter14BaseChangeToBase f g)) :
    chapter14FinitelyPresented f := by
  rcases hXT with ⟨hqc, hfp⟩
  refine ⟨?_, ?_⟩
  · rw [quasiCompact_iff_forall_isAffineOpen]
    intro U hU
    have hTU : IsCompact (g ⁻¹ᵁ U : Set T) :=
      hg.quasiCompact.isCompact_preimage (U : Set S) U.isOpen hU.isCompact
    have hpullback : IsCompact
        ((chapter14BaseChangeToBase f g) ⁻¹ᵁ (g ⁻¹ᵁ U) :
          Set (chapter14BaseChange f g)) :=
      hqc.isCompact_preimage (g ⁻¹ᵁ U : Set T) (g ⁻¹ᵁ U).isOpen hTU
    have hpreimage :
        (chapter14BaseChangeToSource f g).base ⁻¹'
            (f.base ⁻¹' (U : Set S)) =
          (chapter14BaseChangeToBase f g).base ⁻¹'
            (g.base ⁻¹' (U : Set S)) := by
      ext x
      change f (chapter14BaseChangeToSource f g x) ∈ U ↔
        g (chapter14BaseChangeToBase f g x) ∈ U
      change (pullback.fst f g ≫ f) x ∈ U ↔
        (pullback.snd f g ≫ g) x ∈ U
      rw [pullback.condition]
    have hcompactPreimage : IsCompact
        ((chapter14BaseChangeToSource f g).base ⁻¹'
          (f.base ⁻¹' (U : Set S))) := by
      rw [hpreimage]
      exact hpullback
    have hstable : MorphismProperty.IsStableUnderBaseChange
        (@Surjective : MorphismProperty Scheme.{u}) := inferInstance
    have halong : MorphismProperty.IsStableUnderBaseChangeAlong
        (@Surjective : MorphismProperty Scheme.{u}) f :=
      { of_isPullback := fun pb h => hstable.of_isPullback pb h }
    have hsurjective : Surjective (chapter14BaseChangeToSource f g) :=
      halong.of_isPullback (IsPullback.of_hasPullback f g).flip hg.surjective
    have hsurjectiveBase : Function.Surjective
        (chapter14BaseChangeToSource f g).base := hsurjective.surj
    have hcompactImage := hcompactPreimage.image
      (chapter14BaseChangeToSource f g).continuous
    have himage :
        (chapter14BaseChangeToSource f g).base ''
            ((chapter14BaseChangeToSource f g).base ⁻¹'
              (f.base ⁻¹' (U : Set S))) =
          f.base ⁻¹' (U : Set S) :=
      Set.image_preimage_eq _ hsurjectiveBase
    change IsCompact (f.base ⁻¹' (U : Set S))
    rw [← himage]
    exact hcompactImage
  · have hdesc : MorphismProperty.DescendsAlong
        (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
        (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := inferInstance
    exact hdesc.of_isPullback (IsPullback.of_hasPullback f g).flip
      ⟨⟨hg.surjective, hg.flat⟩, hg.quasiCompact⟩ hfp

theorem chapter14_locallyOfFinitePresentation_of_fpqc_base_change
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (hg : chapter14Fpqc g)
    (hXT : chapter14FinitelyPresented (chapter14BaseChangeToBase f g)) :
    LocallyOfFinitePresentation f := by
  exact (chapter14_finitelyPresented_of_fpqc_base_change f g hg hXT).2

structure Chapter14FinitePresentationEnvelopeStatement
    {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] where
  evaluationOpen : IsOpenImmersion (chapter14AffineEnvelopeEvaluation f)
  evaluationQuasiCompact : QuasiCompact (chapter14AffineEnvelopeEvaluation f)
  evaluationLocallyOfFinitePresentation :
    LocallyOfFinitePresentation (chapter14AffineEnvelopeEvaluation f)

theorem chapter14_affine_envelope_finite_presentation
    {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (hX : chapter14QuasiAffine f) :
    Chapter14FinitePresentationEnvelopeStatement f := by
  let hOpen : IsOpenImmersion (chapter14AffineEnvelopeEvaluation f) :=
    chapter14_affine_envelope_evaluation_is_open_of_quasiAffine f hX
  exact {
    evaluationOpen := hOpen
    evaluationQuasiCompact :=
      chapter14_affine_envelope_evaluation_is_quasiCompact_of_quasiAffine f hX
    evaluationLocallyOfFinitePresentation :=
      @locallyOfFinitePresentation_of_isOpenImmersion _ _ _ hOpen }

theorem chapter14_finite_presentation_and_envelope_statement
    {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [LocallyOfFinitePresentation f]
    (hX : chapter14QuasiAffine f) :
    chapter14FinitelyPresented f ∧
      Chapter14FinitePresentationEnvelopeStatement f := by
  exact ⟨⟨inferInstance, inferInstance⟩,
    chapter14_affine_envelope_finite_presentation f hX⟩

theorem chapter14_finite_presentation_and_envelope_after_fpqc_base_change
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (hg : chapter14Fpqc g)
    (hXT : chapter14QuasiAffine (chapter14BaseChangeToBase f g))
    (hfpXT : chapter14FinitelyPresented (chapter14BaseChangeToBase f g)) :
    chapter14QuasiAffine f ∧
      chapter14FinitelyPresented f ∧
        Chapter14FinitePresentationEnvelopeStatement f := by
  have hqa := chapter14_quasiAffine_of_fpqc_base_change f g hg hXT
  have hfp := chapter14_finitelyPresented_of_fpqc_base_change f g hg hfpXT
  refine ⟨hqa, hfp, ?_⟩
  exact @chapter14_affine_envelope_finite_presentation _ _ f inferInstance
    inferInstance hqa

/-! ## Finite principal-open presentations of envelope images -/

theorem chapter14_open_immersion_qc_image_over_affine_open_has_finite_principals
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
    (U : Y.Opens) (hU : IsAffineOpen U) :
    ∃ s : Finset Γ(Y, U),
      (∀ g ∈ s, Y.basicOpen g ≤ j.opensRange ⊓ U) ∧
        ∀ x : X, x ∈ j ⁻¹ᵁ U ↔
          ∃ g ∈ s, x ∈ j ⁻¹ᵁ Y.basicOpen g := by
  classical
  have hK : IsCompact ((j.opensRange ⊓ U : Y.Opens) : Set Y) := by
    rw [← j.image_preimage_eq_opensRange_inf U]
    exact (j.isCompact_preimage hU.isCompact).image j.continuous
  let I := {g : Γ(Y, U) // Y.basicOpen g ≤ j.opensRange ⊓ U}
  let V : I → Set Y := fun g => Y.basicOpen g.1
  have hVopen (g : I) : IsOpen (V g) := by
    exact (Y.basicOpen g.1).isOpen
  have hVcover :
      ((j.opensRange ⊓ U : Y.Opens) : Set Y) ⊆ ⋃ g : I, V g := by
    intro y hy
    have hyU : y ∈ U := hy.2
    obtain ⟨g, hgRange, hyg⟩ :=
      hU.exists_basicOpen_le (V := j.opensRange)
        ⟨y, hy.1⟩ hyU
    refine Set.mem_iUnion.mpr ⟨⟨g, ?_⟩, hyg⟩
    exact le_inf hgRange (Y.basicOpen_le g)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover V hVopen hVcover
  let s : Finset Γ(Y, U) := t.image Subtype.val
  refine ⟨s, ?_, ?_⟩
  · intro g hg
    obtain ⟨g', hg't, rfl⟩ := Finset.mem_image.mp hg
    exact g'.property
  · intro x
    constructor
    · intro hx
      have hxK : j x ∈ (j.opensRange ⊓ U : Y.Opens) :=
        ⟨⟨x, rfl⟩, hx⟩
      have hxcover : j x ∈ ⋃ g ∈ t, V g := ht hxK
      obtain ⟨g, hg⟩ := Set.mem_iUnion.mp hxcover
      obtain ⟨hg't, hxg⟩ := Set.mem_iUnion.mp hg
      refine ⟨g.1, Finset.mem_image.mpr ⟨g, hg't, rfl⟩, ?_⟩
      change j x ∈ Y.basicOpen g.1
      exact hxg
    · rintro ⟨g, hg, hxg⟩
      obtain ⟨g', hg't, rfl⟩ := Finset.mem_image.mp hg
      change j x ∈ U
      change j x ∈ Y.basicOpen g'.1 at hxg
      exact (Y.basicOpen_le g'.1) hxg

theorem chapter14_open_immersion_qc_image_intersection_is_compact
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
    (U : Y.Opens) (hU : IsAffineOpen U) :
    IsCompact ((j.opensRange ⊓ U : Y.Opens) : Set Y) := by
  rw [← j.image_preimage_eq_opensRange_inf U]
  exact (j.isCompact_preimage hU.isCompact).image j.continuous

theorem chapter14_open_immersion_qc_image_intersection_is_open
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (U : Y.Opens) :
    IsOpen ((j.opensRange ⊓ U : Y.Opens) : Set Y) := by
  exact (j.opensRange ⊓ U).isOpen

def chapter14OpenImmersionRange
    {X Y : Scheme.{u}} (j : X ⟶ Y) (hOpen : IsOpenImmersion j) : Y.Opens := by
  letI := hOpen
  exact j.opensRange

theorem chapter14_affine_envelope_image_has_finite_principal_presentation
    {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (hX : chapter14QuasiAffine f)
    (U : (chapter14AffineEnvelopeScheme f).Opens)
    (hU : IsAffineOpen U) :
    ∃ s : Finset Γ(chapter14AffineEnvelopeScheme f, U),
      (∀ g ∈ s,
          (chapter14AffineEnvelopeScheme f).basicOpen g ≤
            chapter14OpenImmersionRange (chapter14AffineEnvelopeEvaluation f)
              (chapter14_affine_envelope_evaluation_is_open_of_quasiAffine f hX) ⊓ U) ∧
        ∀ x : X, x ∈ chapter14AffineEnvelopeEvaluation f ⁻¹ᵁ U ↔
          ∃ g ∈ s,
            x ∈ chapter14AffineEnvelopeEvaluation f ⁻¹ᵁ
              (chapter14AffineEnvelopeScheme f).basicOpen g := by
  let hOpen : IsOpenImmersion (chapter14AffineEnvelopeEvaluation f) :=
    chapter14_affine_envelope_evaluation_is_open_of_quasiAffine f hX
  let hQuasiCompact : QuasiCompact (chapter14AffineEnvelopeEvaluation f) :=
    chapter14_affine_envelope_evaluation_is_quasiCompact_of_quasiAffine f hX
  simpa [chapter14OpenImmersionRange] using
    (@chapter14_open_immersion_qc_image_over_affine_open_has_finite_principals
      _ _ (chapter14AffineEnvelopeEvaluation f) hOpen hQuasiCompact U hU)

/-! ## Common nonvanishing loci -/

/-- The common nonvanishing locus of a finite family of global sections. -/
def chapter14CommonDeterminantLocus {X : Scheme.{u}} {n : ℕ}
    (determinant : Fin n → Γ(X, ⊤)) : X.Opens :=
  ⨅ i, X.basicOpen (determinant i)

theorem chapter14_mem_commonDeterminantLocus_iff
    {X : Scheme.{u}} {n : ℕ} (determinant : Fin n → Γ(X, ⊤)) (x : X) :
    x ∈ chapter14CommonDeterminantLocus determinant ↔
      ∀ i, x ∈ X.basicOpen (determinant i) := by
  change x ∈ (((⨅ i, X.basicOpen (determinant i)) : X.Opens) : Set X) ↔ _
  rw [TopologicalSpace.Opens.coe_iInf]
  simp

theorem chapter14_commonDeterminantLocus_is_open
    {X : Scheme.{u}} {n : ℕ} (determinant : Fin n → Γ(X, ⊤)) :
    IsOpen (chapter14CommonDeterminantLocus determinant : Set X) := by
  exact (chapter14CommonDeterminantLocus determinant).isOpen

theorem chapter14_commonDeterminantLocus_is_quasiAffine
    {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f]
    {n : ℕ} (determinant : Fin n → Γ(X, ⊤)) :
    chapter14QuasiAffine
      ((chapter14CommonDeterminantLocus determinant).ι ≫ f) := by
  exact chapter14_quasiAffine_mk
    ((chapter14CommonDeterminantLocus determinant).ι ≫ f) f
    (by infer_instance) (chapter14CommonDeterminantLocus determinant).ι
    (by infer_instance) rfl

theorem chapter14_commonDeterminantLocus_preimage
    {X Y : Scheme.{u}} (h : Y ⟶ X) {n : ℕ}
    (determinant : Fin n → Γ(X, ⊤)) :
    h ⁻¹ᵁ chapter14CommonDeterminantLocus determinant =
      chapter14CommonDeterminantLocus (fun i ↦ h.appTop (determinant i)) := by
  ext y
  change h y ∈ (((⨅ i, X.basicOpen (determinant i)) : X.Opens) : Set X) ↔
    y ∈ (((⨅ i, Y.basicOpen (h.appTop (determinant i))) : Y.Opens) : Set Y)
  rw [TopologicalSpace.Opens.coe_iInf, TopologicalSpace.Opens.coe_iInf]
  simp only [Set.mem_iInter]
  constructor
  · intro hy i
    rw [← Scheme.preimage_basicOpen_top h (determinant i)]
    exact hy i
  · intro hy i
    change y ∈ h ⁻¹ᵁ X.basicOpen (determinant i)
    rw [Scheme.preimage_basicOpen_top h (determinant i)]
    exact hy i

theorem chapter14_commonDeterminantLocus_base_change_membership
    {X Y : Scheme.{u}} (h : Y ⟶ X) {n : ℕ}
    (determinant : Fin n → Γ(X, ⊤)) (y : Y) :
    y ∈ h ⁻¹ᵁ chapter14CommonDeterminantLocus determinant ↔
      ∀ i, y ∈ Y.basicOpen (h.appTop (determinant i)) := by
  rw [chapter14_commonDeterminantLocus_preimage]
  exact chapter14_mem_commonDeterminantLocus_iff _ _

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter14
