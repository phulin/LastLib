import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter14.Dependencies

/-!
# Book 10, Chapter 14, §14.1: intrinsic affine envelopes

The declarations below separate the canonical envelope map from the
quasi-affineness assertion.  The latter is the theorem that makes the
envelope useful for descent.
-/

noncomputable section

universe u

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter14

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

/-! ## Finite principal opens on affine schemes -/

structure Chapter14FinitePrincipalOpenCover (Y : Scheme.{u}) where
  affine : IsAffine Y
  carrierOpen : Y.Opens
  sections : Finset Γ(Y, ⊤)
  covers : ∀ x : Y, x ∈ open → ∃ g ∈ sections, x ∈ Y.basicOpen g

theorem chapter14_finite_principal_open_cover_of_compact_open
    (Y : Scheme.{u}) [IsAffine Y] (V : Y.Opens)
    (hV : IsCompact (V : Set Y)) :
    ∃ s : Finset Γ(Y, ⊤), ∀ x : Y, x ∈ V ↔ ∃ g ∈ s, x ∈ Y.basicOpen g := by
  sorry

theorem chapter14_principal_open_is_affine_of_affine
    (Y : Scheme.{u}) (U : Y.Opens) (hU : IsAffineOpen U)
    (g : Γ(Y, U)) :
    IsAffineOpen (Y.basicOpen g) := by
  exact hU.basicOpen g

theorem chapter14_finite_principal_open_cover_is_affine
    (Y : Scheme.{u}) [IsAffine Y] (V : Y.Opens)
    (hV : IsCompact (V : Set Y)) :
    ∃ C : Chapter14FinitePrincipalOpenCover Y,
      C.carrierOpen = V ∧
        ∀ x : Y, x ∈ V → ∃ g ∈ C.sections, x ∈ Y.basicOpen g := by
  sorry

/-! ## The envelope map -/

theorem chapter14_affine_envelope_evaluation_is_open_of_quasiAffine
    {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (hX : chapter14QuasiAffine f) :
    IsOpenImmersion (chapter14AffineEnvelopeEvaluation f) := by
  sorry

theorem chapter14_affine_envelope_evaluation_is_quasiCompact_of_quasiAffine
    {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (hX : chapter14QuasiAffine f) :
    QuasiCompact (chapter14AffineEnvelopeEvaluation f) := by
  sorry

theorem chapter14_quasiAffine_of_affine_envelope_evaluation_is_open
    {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (hOpen : IsOpenImmersion (chapter14AffineEnvelopeEvaluation f)) :
    chapter14QuasiAffine f := by
  exact chapter14_quasiAffine_mk f (chapter14AffineEnvelopeMap f)
    (chapter14_affine_envelope_is_affine f)
    (chapter14AffineEnvelopeEvaluation f) hOpen
    (chapter14_affine_envelope_evaluation_over_base f)

theorem chapter14_quasiAffine_iff_affine_envelope_evaluation_is_open
    {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] :
    chapter14QuasiAffine f ↔
      IsOpenImmersion (chapter14AffineEnvelopeEvaluation f) := by
  constructor
  · exact chapter14_affine_envelope_evaluation_is_open_of_quasiAffine f
  · exact chapter14_quasiAffine_of_affine_envelope_evaluation_is_open f

theorem chapter14_affine_envelope_evaluation_is_quasiCompact_open_of_quasiAffine
    {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (hX : chapter14QuasiAffine f) :
    IsOpenImmersion (chapter14AffineEnvelopeEvaluation f) ∧
      QuasiCompact (chapter14AffineEnvelopeEvaluation f) := by
  exact ⟨chapter14_affine_envelope_evaluation_is_open_of_quasiAffine f hX,
    chapter14_affine_envelope_evaluation_is_quasiCompact_of_quasiAffine f hX⟩

theorem chapter14_quasiAffine_iff_quasiCompact_open_affine_envelope_evaluation
    {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] :
    chapter14QuasiAffine f ↔
      IsOpenImmersion (chapter14AffineEnvelopeEvaluation f) ∧
        QuasiCompact (chapter14AffineEnvelopeEvaluation f) := by
  constructor
  · exact chapter14_affine_envelope_evaluation_is_quasiCompact_open_of_quasiAffine f
  · intro h
    exact chapter14_quasiAffine_of_affine_envelope_evaluation_is_open f h.1

/-! ## Restriction, membership, and normalization bridges -/

theorem chapter14_affine_envelope_preimage_basicOpen
    {X Y : Scheme.{u}} (j : X ⟶ Y) (g : Γ(Y, ⊤)) :
    j ⁻¹ᵁ Y.basicOpen g = X.basicOpen (j.appTop g) := by
  exact Scheme.preimage_basicOpen_top j g

theorem chapter14_affine_envelope_preimage_basicOpen_mem_iff
    {X Y : Scheme.{u}} (j : X ⟶ Y) (g : Γ(Y, ⊤)) (x : X) :
    x ∈ j ⁻¹ᵁ Y.basicOpen g ↔ x ∈ X.basicOpen (j.appTop g) := by
  rw [chapter14_affine_envelope_preimage_basicOpen]

theorem chapter14_affine_envelope_basicOpen_restriction
    {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (g : Γ(X, U)) :
    X.basicOpen g ≤ U ∧ IsAffineOpen (X.basicOpen g) := by
  exact ⟨Scheme.basicOpen_le _ _, hU.basicOpen g⟩

theorem chapter14_affine_envelope_evaluation_over_base_appTop
    {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] :
    (chapter14AffineEnvelopeMap f).appTop ≫
        (chapter14AffineEnvelopeEvaluation f).appTop = f.appTop := by
  rw [← Scheme.Hom.comp_appTop, chapter14_affine_envelope_evaluation_over_base]

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter14
