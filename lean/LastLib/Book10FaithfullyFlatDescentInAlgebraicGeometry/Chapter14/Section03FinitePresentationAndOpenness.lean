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
  sorry

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
  exact
    { evaluationOpen :=
        chapter14_affine_envelope_evaluation_is_open_of_quasiAffine f hX
      evaluationQuasiCompact :=
        chapter14_affine_envelope_evaluation_is_quasiCompact_of_quasiAffine f hX
      evaluationLocallyOfFinitePresentation := by infer_instance }

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
  sorry

/-! ## Finite principal-open presentations of envelope images -/

theorem chapter14_open_immersion_qc_image_over_affine_open_has_finite_principals
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
    (U : Y.Opens) (hU : IsAffineOpen U) :
    ∃ s : Finset Γ(Y, U),
      ∀ x : X, x ∈ j ⁻¹ᵁ U ↔
        ∃ g ∈ s, x ∈ j ⁻¹ᵁ Y.basicOpen g := by
  sorry

theorem chapter14_open_immersion_qc_image_intersection_is_compact
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
    (U : Y.Opens) (hU : IsAffineOpen U) :
    IsCompact ((j.opensRange ⊓ U : Y.Opens) : Set Y) := by
  sorry

theorem chapter14_open_immersion_qc_image_intersection_is_open
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (U : Y.Opens) :
    IsOpen ((j.opensRange ⊓ U : Y.Opens) : Set Y) := by
  exact (j.opensRange ⊓ U).isOpen

theorem chapter14_affine_envelope_image_has_finite_principal_presentation
    {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (hX : chapter14QuasiAffine f)
    (U : chapter14AffineEnvelopeScheme f).Opens
    (hU : IsAffineOpen U) :
    ∃ s : Finset Γ(chapter14AffineEnvelopeScheme f, U),
      ∀ x : X, x ∈ chapter14AffineEnvelopeEvaluation f ⁻¹ᵁ U ↔
        ∃ g ∈ s,
          x ∈ chapter14AffineEnvelopeEvaluation f ⁻¹ᵁ
            (chapter14AffineEnvelopeScheme f).basicOpen g := by
  letI : IsOpenImmersion (chapter14AffineEnvelopeEvaluation f) :=
    chapter14_affine_envelope_evaluation_is_open_of_quasiAffine f hX
  letI : QuasiCompact (chapter14AffineEnvelopeEvaluation f) :=
    chapter14_affine_envelope_evaluation_is_quasiCompact_of_quasiAffine f hX
  exact chapter14_open_immersion_qc_image_over_affine_open_has_finite_principals
    (chapter14AffineEnvelopeEvaluation f) U hU

/-! ## Common nonvanishing loci -/

/-- The common nonvanishing locus of a finite family of global sections. -/
def chapter14CommonDeterminantLocus {X : Scheme.{u}} {n : ℕ}
    (determinant : Fin n → Γ(X, ⊤)) : X.Opens :=
  ⨅ i, X.basicOpen (determinant i)

theorem chapter14_mem_commonDeterminantLocus_iff
    {X : Scheme.{u}} {n : ℕ} (determinant : Fin n → Γ(X, ⊤)) (x : X) :
    x ∈ chapter14CommonDeterminantLocus determinant ↔
      ∀ i, x ∈ X.basicOpen (determinant i) := by
  sorry

theorem chapter14_commonDeterminantLocus_is_open
    {X : Scheme.{u}} {n : ℕ} (determinant : Fin n → Γ(X, ⊤)) :
    IsOpen (chapter14CommonDeterminantLocus determinant : Set X) := by
  exact (chapter14CommonDeterminantLocus determinant).isOpen

theorem chapter14_commonDeterminantLocus_is_quasiAffine
    {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f]
    {n : ℕ} (determinant : Fin n → Γ(X, ⊤)) :
    chapter14QuasiAffine
      ((chapter14CommonDeterminantLocus determinant).ι ≫ f) := by
  apply chapter14_quasiAffine_mk
    ((chapter14CommonDeterminantLocus determinant).ι ≫ f) f
  · infer_instance
  · exact (chapter14CommonDeterminantLocus determinant).ι
  · infer_instance
  · simp

theorem chapter14_commonDeterminantLocus_preimage
    {X Y : Scheme.{u}} (h : Y ⟶ X) {n : ℕ}
    (determinant : Fin n → Γ(X, ⊤)) :
    h ⁻¹ᵁ chapter14CommonDeterminantLocus determinant =
      chapter14CommonDeterminantLocus (fun i ↦ h.appTop (determinant i)) := by
  sorry

theorem chapter14_commonDeterminantLocus_base_change_membership
    {X Y : Scheme.{u}} (h : Y ⟶ X) {n : ℕ}
    (determinant : Fin n → Γ(X, ⊤)) (y : Y) :
    y ∈ h ⁻¹ᵁ chapter14CommonDeterminantLocus determinant ↔
      ∀ i, y ∈ Y.basicOpen (h.appTop (determinant i)) := by
  rw [chapter14_commonDeterminantLocus_preimage]
  exact chapter14_mem_commonDeterminantLocus_iff _ _

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter14
