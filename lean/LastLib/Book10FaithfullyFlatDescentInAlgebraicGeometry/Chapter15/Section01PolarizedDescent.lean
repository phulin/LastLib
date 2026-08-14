import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter15.Dependencies

/-!
# 15.1 Polarized descent

The line bundle and its Čech datum are inputs.  The output records both the
descended line bundle and the positivity conclusion; a bare existence claim for
some ample bundle upstairs is intentionally not accepted as descent data.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter15

noncomputable section

structure PolarizedObject {X S : Scheme.{u}} (f : X ⟶ S) where
  lineBundle : LineBundle X
  ample : IsAmple f lineBundle

structure PolarizedBaseChangeData
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) where
  cover : FpqcCoverData g
  lineBundle : LineBundle (baseChange f g)
  descent : FpqcLineBundleDescentDatum f g
  descent_carrier : descent.lineBundle = lineBundle
  ample : IsAmple (baseChangeToBase f g) lineBundle

noncomputable def baseChangeLineBundle {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (L : LineBundle X) : LineBundle (baseChange f g) :=
  pullbackLineBundle (baseChangeToSource f g) L

theorem baseChangeLineBundle_is_pullback {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (L : LineBundle X) :
    lineBundleIsomorphic (baseChangeLineBundle f g L)
      (pullbackLineBundle (baseChangeToSource f g) L) := by
  exact lineBundleIsomorphic_refl _

/- LOCAL_DEPENDENCY_GUESS: Chapter 9's effective descent theorem is consumed
  through this explicit
  realization record.  Its comparison isomorphism is part of the conclusion,
  not a hidden equality between an arbitrary upstairs bundle and a pullback. -/
theorem lineBundle_fpqc_effective_descent
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (hf : IsFinitePresentation f) (hg : FpqcCoverData g)
    (D : FpqcLineBundleDescentDatum f g) :
    ∃ L : LineBundle X,
      Nonempty (LineBundleDescentRealization D.descent L) := by
  sorry

theorem relative_ampleness_baseChange
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (L : LineBundle X)
    (hf : IsFinitePresentation f) (hg : FpqcCoverData g) :
    IsAmple f L ↔
      IsAmple (baseChangeToBase f g) (baseChangeLineBundle f g L) := by
  sorry

theorem relative_ampleness_faithfullyFlat_descent
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (L : LineBundle X)
    (hf : IsFinitePresentation f) (hg : FpqcCoverData g)
    (hL : IsAmple (baseChangeToBase f g) (baseChangeLineBundle f g L)) :
    IsAmple f L := by
  exact (relative_ampleness_baseChange f g L hf hg).mpr hL

theorem relative_ampleness_of_descended_lineBundle
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (L : LineBundle X) (M : LineBundle (baseChange f g))
    (D : FpqcLineBundleDescentDatum f g)
    (hD : Nonempty (LineBundleDescentRealization D.descent L))
    (hf : IsFinitePresentation f) (hg : FpqcCoverData g)
    (hM : IsAmple (baseChangeToBase f g) M) :
    IsAmple f L := by
  sorry

/- The finite presentation assumptions are exactly the hypotheses under which
  the preceding affine-local criterion supplies a positive power and an
  embedding.  Quasi-compactness of the base is kept separate because it is the
  uniformity hypothesis, not part of the local descent statement. -/
theorem polarized_quasiProjective_effective_descent
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (hf : IsFinitePresentation f) (hg : FpqcCoverData g)
    (D : PolarizedBaseChangeData f g) :
    ∃ L : LineBundle X,
      Nonempty (LineBundleDescentRealization D.descent.descent L) ∧
        IsAmple f L ∧ HasLocalFiniteRankEmbedding f := by
  sorry

theorem polarized_quasiProjective_global_embedding
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (hf : IsFinitePresentation f) (hg : FpqcCoverData g)
    (hS : QuasiCompact (𝟙 S)) (D : PolarizedBaseChangeData f g) :
    ∃ L : LineBundle X,
      Nonempty (LineBundleDescentRealization D.descent.descent L) ∧
        IsAmple f L ∧ HasGlobalFiniteRankEmbedding f := by
  sorry

theorem polarized_quasiProjective_local_embedding
    {X S : Scheme.{u}} (f : X ⟶ S) (L : LineBundle X)
    (hf : IsFinitePresentation f) (hL : IsAmple f L) :
    HasLocalFiniteRankEmbedding f := by
  sorry

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter15
