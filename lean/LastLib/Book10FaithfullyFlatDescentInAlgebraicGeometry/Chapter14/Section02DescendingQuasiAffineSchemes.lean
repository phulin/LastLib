import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter14.Section01IntrinsicAffineEnvelopes

/-!
# Book 10, Chapter 14, §14.2: descending quasi-affine schemes

The base-change comparison is recorded at both the sheaf-of-functions level
and the affine-envelope level.  The fpqc descent statement then applies the
Mathlib descent interface for open immersions.
-/

noncomputable section

universe u

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter14

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

/-! ## Base change of the canonical map -/

theorem chapter14_relative_global_functions_base_change
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [Flat g] :
    Nonempty ((Scheme.Modules.pullback g).obj (chapter14RelativeGlobalFunctions f) ≅
      chapter14RelativeGlobalFunctions (chapter14BaseChangeToBase f g)) := by
  sorry

noncomputable def chapter14RelativeGlobalFunctionsBaseChangeIso
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [Flat g] :
    (Scheme.Modules.pullback g).obj (chapter14RelativeGlobalFunctions f) ≅
      chapter14RelativeGlobalFunctions (chapter14BaseChangeToBase f g) :=
  Classical.choice (chapter14_relative_global_functions_base_change f g)

theorem chapter14_relative_global_functions_base_change_is_quasicoherent
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [Flat g] :
    (chapter14RelativeGlobalFunctions (chapter14BaseChangeToBase f g)).IsQuasicoherent := by
  sorry

def chapter14AffineEnvelopeEvaluationBaseChange
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] :
    chapter14BaseChange f g ⟶
      pullback (chapter14AffineEnvelopeMap f) g := by
  apply pullback.lift
  · exact chapter14BaseChangeToSource f g ≫ chapter14AffineEnvelopeEvaluation f
  · exact chapter14BaseChangeToBase f g
  · rw [Category.assoc, chapter14_affine_envelope_evaluation_over_base]
    exact pullback.condition

@[simp]
theorem chapter14AffineEnvelopeEvaluationBaseChange_fst
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] :
    chapter14AffineEnvelopeEvaluationBaseChange f g ≫
        pullback.fst (chapter14AffineEnvelopeMap f) g =
      chapter14BaseChangeToSource f g ≫ chapter14AffineEnvelopeEvaluation f := by
  exact pullback.lift_fst _ _ _

@[simp]
theorem chapter14AffineEnvelopeEvaluationBaseChange_snd
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] :
    chapter14AffineEnvelopeEvaluationBaseChange f g ≫
        pullback.snd (chapter14AffineEnvelopeMap f) g =
      chapter14BaseChangeToBase f g := by
  exact pullback.lift_snd _ _ _

/-! ## The affine-envelope base-change comparison -/

structure Chapter14AffineEnvelopeBaseChangeData
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact (chapter14BaseChangeToBase f g)]
    [QuasiSeparated (chapter14BaseChangeToBase f g)] where
  comparison :
    pullback (chapter14AffineEnvelopeMap f) g ≅
      (chapter14AffineEnvelope (chapter14BaseChangeToBase f g)).envelope
  comparison_over_base :
    comparison.hom ≫ chapter14AffineEnvelopeMap (chapter14BaseChangeToBase f g) =
      pullback.snd (chapter14AffineEnvelopeMap f) g
  comparison_evaluation :
    chapter14AffineEnvelopeEvaluationBaseChange f g ≫ comparison.hom =
      chapter14AffineEnvelopeEvaluation (chapter14BaseChangeToBase f g)

theorem chapter14_affine_envelope_base_change_exists
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [Flat g]
    [QuasiCompact (chapter14BaseChangeToBase f g)]
    [QuasiSeparated (chapter14BaseChangeToBase f g)] :
    Nonempty (Chapter14AffineEnvelopeBaseChangeData f g) := by
  sorry

noncomputable def chapter14AffineEnvelopeBaseChange
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [Flat g]
    [QuasiCompact (chapter14BaseChangeToBase f g)]
    [QuasiSeparated (chapter14BaseChangeToBase f g)] :
    Chapter14AffineEnvelopeBaseChangeData f g :=
  Classical.choice (chapter14_affine_envelope_base_change_exists f g)

def chapter14AffineEnvelopeBaseChangeIso
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [Flat g]
    [QuasiCompact (chapter14BaseChangeToBase f g)]
    [QuasiSeparated (chapter14BaseChangeToBase f g)] :
    pullback (chapter14AffineEnvelopeMap f) g ≅
      (chapter14AffineEnvelope (chapter14BaseChangeToBase f g)).envelope :=
  (chapter14AffineEnvelopeBaseChange f g).comparison

theorem chapter14_affine_envelope_base_change_over_base
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [Flat g]
    [QuasiCompact (chapter14BaseChangeToBase f g)]
    [QuasiSeparated (chapter14BaseChangeToBase f g)] :
    (chapter14AffineEnvelopeBaseChangeIso f g).hom ≫
        chapter14AffineEnvelopeMap (chapter14BaseChangeToBase f g) =
      pullback.snd (chapter14AffineEnvelopeMap f) g := by
  exact (chapter14AffineEnvelopeBaseChange f g).comparison_over_base

theorem chapter14_affine_envelope_base_change_evaluation
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [Flat g]
    [QuasiCompact (chapter14BaseChangeToBase f g)]
    [QuasiSeparated (chapter14BaseChangeToBase f g)] :
    chapter14AffineEnvelopeEvaluationBaseChange f g ≫
        (chapter14AffineEnvelopeBaseChangeIso f g).hom =
      chapter14AffineEnvelopeEvaluation (chapter14BaseChangeToBase f g) := by
  exact (chapter14AffineEnvelopeBaseChange f g).comparison_evaluation

/-! ## Stability and fpqc descent -/

theorem chapter14_quasiAffine_base_change
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (hX : chapter14QuasiAffine f) :
    chapter14QuasiAffine (chapter14BaseChangeToBase f g) := by
  sorry

theorem chapter14_quasiAffine_of_fpqc_base_change
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (hg : chapter14Fpqc g)
    (hXT : chapter14QuasiAffine (chapter14BaseChangeToBase f g)) :
    chapter14QuasiAffine f := by
  sorry

theorem chapter14_quasiAffine_iff_fpqc_base_change
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (hg : chapter14Fpqc g) :
    chapter14QuasiAffine f ↔
      chapter14QuasiAffine (chapter14BaseChangeToBase f g) := by
  constructor
  · exact chapter14_quasiAffine_base_change f g
  · exact chapter14_quasiAffine_of_fpqc_base_change f g hg

theorem chapter14_quasi_affine_descent_theorem
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (hg : chapter14Fpqc g)
    (hXT : chapter14QuasiAffine (chapter14BaseChangeToBase f g)) :
    chapter14QuasiAffine f := by
  exact chapter14_quasiAffine_of_fpqc_base_change f g hg hXT

theorem chapter14_quasi_affineness_is_fpqc_local
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (hg : chapter14Fpqc g) :
    chapter14QuasiAffine f ↔
      chapter14QuasiAffine (chapter14BaseChangeToBase f g) := by
  exact chapter14_quasiAffine_iff_fpqc_base_change f g hg

/-! ## The locally quasi-affine boundary variant -/

def chapter14LocallyQuasiAffine {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsCompact (U : Set X) ∧
    chapter14QuasiAffine (U.ι ≫ f)

theorem chapter14_quasiAffine_implies_locallyQuasiAffine
    {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (hX : chapter14QuasiAffine f) :
    chapter14LocallyQuasiAffine f := by
  sorry

theorem chapter14_locallyQuasiAffine_restrict
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hX : chapter14LocallyQuasiAffine f) (U : S.Opens) :
    chapter14LocallyQuasiAffine (chapter14RestrictionToOpenMap f U) := by
  sorry

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter14
