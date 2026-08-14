import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter15.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.Section01PullbackOfPositivity
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.Section03DescentOfAmplenessAndProjectivity

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
    (hg : FpqcCoverData g)
    (D : FpqcLineBundleDescentDatum f g) :
    ∃ L : LineBundle X,
      Nonempty (LineBundleDescentRealization D.descent L) := by
  exact lineBundleDescentDatum_effective_via_chapter09
    (baseChangeToSource f g) D.descent
    (baseChangeToSource_fpqcCoverData f g hg)

theorem relative_ampleness_baseChange
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (L : LineBundle X)
    (hf : IsFinitePresentation f) (hg : FpqcCoverData g) :
    IsAmple f L ↔
      IsAmple (baseChangeToBase f g) (baseChangeLineBundle f g L) := by
  change
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.IsAmple f L ↔
      LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.IsAmple
        (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.baseChangeToBase f g)
        (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.baseChangeLineBundle f g L)
  exact
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.ample_iff_faithfullyFlat_baseChange
      f g L hf.1 hf.2.1 hg.isFaithfullyFlat hg.quasiCompact

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
    (hMD : lineBundleIsomorphic M D.lineBundle)
    (hf : IsFinitePresentation f) (hg : FpqcCoverData g)
    (hM : IsAmple (baseChangeToBase f g) M) :
    IsAmple f L := by
  apply (relative_ampleness_baseChange f g L hf hg).mpr
  have hBM : lineBundleIsomorphic (baseChangeLineBundle f g L) M := by
    rcases hD with ⟨R⟩
    exact lineBundleIsomorphic_trans
      ⟨(fpqcLineBundleRealizationComparison f g D L R).hom⟩
      (lineBundleIsomorphic_symm hMD)
  exact
    (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.isAmple_congr
      (baseChangeToBase f g) hBM).mpr hM

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
        IsAmple f L ∧ HasLocalFiniteRankEmbeddingFor f L := by
  obtain ⟨L, hL⟩ := lineBundle_fpqc_effective_descent f g hg D.descent
  have hample : IsAmple f L :=
    relative_ampleness_of_descended_lineBundle f g L D.lineBundle D.descent
      hL (by
        rw [← D.descent_carrier, ← D.descent.carrier_eq]
        exact lineBundleIsomorphic_refl _) hf hg D.ample
  refine ⟨L, hL, hample, ?_⟩
  · classical
    let : QuasiCompact f := hf.1
    let : QuasiSeparated f := hf.2.1
    let : LocallyOfFinitePresentation f := hf.2.2
    rcases hample with ⟨W⟩
    intro s
    obtain ⟨i, hs⟩ := W.base_open_cover s
    let U : S.Opens := W.base_open i
    have hU : IsAffineOpen U := W.base_open_affine i
    let : IsAffine U := hU
    refine ⟨U, hs, ?_⟩
    have hAmp : IsAmple (f ∣_ U) (L.pullback (f ⁻¹ᵁ U).ι) :=
      LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.ample_restrict
        f U L ⟨W⟩
    obtain ⟨n, hn, hV⟩ :=
      LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04_ample_has_veryAmple_power
        (f ∣_ U) (L.pullback (f ⁻¹ᵁ U).ι) hAmp
    refine ⟨n, hn, ?_⟩
    rcases hV with ⟨w⟩
    exact ⟨⟨w, w.projectiveBundle.E, rfl⟩, ⟨w⟩, w.immersion⟩

theorem polarized_quasiProjective_global_embedding
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (hf : IsFinitePresentation f) (hg : FpqcCoverData g)
    (hS : QuasiCompact (𝟙 S)) (D : PolarizedBaseChangeData f g) :
    ∃ L : LineBundle X,
      Nonempty (LineBundleDescentRealization D.descent.descent L) ∧
        IsAmple f L ∧
          ∃ n : ℕ, 0 < n ∧ HasGlobalFiniteRankEmbeddingFor f (L.tensorPower n) := by
  sorry

theorem polarized_quasiProjective_local_embedding
    {X S : Scheme.{u}} (f : X ⟶ S) (L : LineBundle X)
    (hf : IsFinitePresentation f) (hL : IsAmple f L) :
    HasLocalFiniteRankEmbeddingFor f L := by
  classical
  let : QuasiCompact f := hf.1
  let : QuasiSeparated f := hf.2.1
  let : LocallyOfFinitePresentation f := hf.2.2
  rcases hL with ⟨W⟩
  intro s
  obtain ⟨i, hs⟩ := W.base_open_cover s
  let U : S.Opens := W.base_open i
  have hU : IsAffineOpen U := W.base_open_affine i
  let : IsAffine U := hU
  refine ⟨U, hs, ?_⟩
  have hAmp : IsAmple (f ∣_ U) (L.pullback (f ⁻¹ᵁ U).ι) :=
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.ample_restrict
      f U L ⟨W⟩
  obtain ⟨n, hn, hV⟩ :=
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04_ample_has_veryAmple_power
      (f ∣_ U) (L.pullback (f ⁻¹ᵁ U).ι) hAmp
  refine ⟨n, hn, ?_⟩
  rcases hV with ⟨w⟩
  refine ⟨⟨w, w.projectiveBundle.E, rfl⟩, ⟨w⟩, w.immersion⟩

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter15
