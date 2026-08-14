import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter15.Section01PolarizedDescent
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.Section02FaithfullyFlatDescentOfVeryAmpleness
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.Section04ProofsOfPrincipalCases

/-!
# 15.2 Very ampleness and closed immersions

The coefficient sheaf, its quotient onto the polarized line bundle, and the
induced map to the relative projective bundle are kept together.  This is the
finite system of sections whose descent is asserted in the source.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04

universe u

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter15

noncomputable section

structure DescendedProjectiveEmbedding {X S : Scheme.{u}} (f : X ⟶ S) where
  projectiveBundle :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Chapter04ProjectiveBundle S
  universalQuotientCompatible :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04ProjectiveBundleUniversalQuotientCompatible
      projectiveBundle
  map : X ⟶ projectiveBundle.space
  over : map ≫ projectiveBundle.projection = f
  immersion : IsImmersion map

structure DescendedFiniteLinearSystem
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (D : FpqcLineBundleDescentDatum f g)
    (V : CompatibleFiniteLinearSystem f g D) where
  lineBundle : LineBundle X
  lineBundleRealization :
    LineBundleDescentRealization D.descent lineBundle
  coefficient : S.Modules
  coefficientRealization :
    ModuleDescentRealization V.coefficients.descent coefficient
  finiteLocallyFree :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04FiniteLocallyFree coefficient
  quotient : (Scheme.Modules.pullback f).obj coefficient ⟶ lineBundle.sheaf
  quotient_epi : Epi quotient
  embedding : DescendedProjectiveEmbedding f
  coefficient_comparison :
    (Scheme.Modules.pullback (baseChangeToSource f g)).obj
        ((Scheme.Modules.pullback f).obj coefficient) ≅
      (Scheme.Modules.pullback (baseChangeToBase f g)).obj V.coefficients.coefficient
  coefficient_comparison_is_realization :
    coefficient_comparison =
      coefficientRealizationComparison f g V.coefficients coefficient
        coefficientRealization
  lineBundle_comparison :
    (Scheme.Modules.pullback (baseChangeToSource f g)).obj lineBundle.sheaf ≅
      D.lineBundle.sheaf
  lineBundle_comparison_is_realization :
    lineBundle_comparison =
      (fpqcLineBundleRealizationComparison f g D lineBundle
        lineBundleRealization).hom
  quotient_compatibility :
    coefficient_comparison.hom ≫ V.system.quotient =
      (Scheme.Modules.pullback (baseChangeToSource f g)).map quotient ≫
        lineBundle_comparison.hom
  embedding_coefficient_eq : embedding.projectiveBundle.E = coefficient
  lineBundle_pullback_iso : lineBundle.sheaf ≅
    (Scheme.Modules.pullback embedding.map).obj embedding.projectiveBundle.tautological
  quotient_associated :
    quotient ≫ lineBundle_pullback_iso.hom =
      (eqToIso (congrArg (fun h : X ⟶ S =>
        (Scheme.Modules.pullback h).obj coefficient) embedding.over.symm)).hom ≫
        (chapter04PullbackCompositionIso embedding.map embedding.projectiveBundle.projection
          coefficient).hom ≫
          (Scheme.Modules.pullback embedding.map).map
            ((eqToIso (congrArg (fun E' : S.Modules =>
              (Scheme.Modules.pullback embedding.projectiveBundle.projection).obj E')
                embedding_coefficient_eq.symm)).hom ≫
              embedding.projectiveBundle.universalQuotient)
  baseChange_embedding_map :
    baseChange f g ⟶ baseChange embedding.projectiveBundle.projection g
  baseChange_embedding_map_source :
    baseChange_embedding_map ≫
        baseChangeToSource embedding.projectiveBundle.projection g =
      baseChangeToSource f g ≫ embedding.map
  baseChange_embedding_map_base :
    baseChange_embedding_map ≫
        baseChangeToBase embedding.projectiveBundle.projection g =
      baseChangeToBase f g
  projectiveSpace_comparison :
    baseChange embedding.projectiveBundle.projection g ≅ V.system.projectiveBundle.space
  projectiveSpace_comparison_over :
    projectiveSpace_comparison.hom ≫ V.system.projectiveBundle.projection =
      baseChangeToBase embedding.projectiveBundle.projection g
  associatedMap_compatibility :
    baseChange_embedding_map ≫ projectiveSpace_comparison.hom = V.system.associatedMap

theorem DescendedFiniteLinearSystem.isVeryAmple
    {X S T : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S}
    {D : FpqcLineBundleDescentDatum f g}
    {V : CompatibleFiniteLinearSystem f g D}
    (Z : DescendedFiniteLinearSystem f g D V) : IsVeryAmple f Z.lineBundle := by
  let W :
      LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.RelativeVeryAmpleWitness
        f Z.lineBundle :=
    { projectiveBundle := Z.embedding.projectiveBundle
      universalQuotientCompatible := Z.embedding.universalQuotientCompatible
      map := Z.embedding.map
      immersion := Z.embedding.immersion
      over := Z.embedding.over
      pullback_iso := Z.lineBundle_pullback_iso }
  exact ⟨W⟩

theorem DescendedFiniteLinearSystem.hasGlobalFiniteRankEmbeddingFor
    {X S T : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S}
    {D : FpqcLineBundleDescentDatum f g}
    {V : CompatibleFiniteLinearSystem f g D}
    (Z : DescendedFiniteLinearSystem f g D V) :
    HasGlobalFiniteRankEmbeddingFor f Z.lineBundle := by
  refine ⟨{
    witness := {
      projectiveBundle := Z.embedding.projectiveBundle
      universalQuotientCompatible := Z.embedding.universalQuotientCompatible
      map := Z.embedding.map
      immersion := Z.embedding.immersion
      over := Z.embedding.over
      pullback_iso := Z.lineBundle_pullback_iso }
    coefficient := Z.coefficient
    coefficient_is_witness := Z.embedding_coefficient_eq.symm },
    Z.isVeryAmple, Z.embedding.immersion⟩

/- The preceding result is the effective descent theorem for a finite system
  of sections.  Its conclusion has actual descended coefficient and quotient
  objects, rather than only a proposition that some embedding exists. -/
theorem compatible_finite_linear_system_effective_descent
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (hf : IsFinitePresentation f) (hg : FpqcCoverData g)
    (D : FpqcLineBundleDescentDatum f g)
    (V : CompatibleFiniteLinearSystem f g D) :
    ∃ Z : DescendedFiniteLinearSystem f g D V,
      IsVeryAmple f Z.lineBundle := by
  sorry

theorem veryAmple_faithfullyFlat_descent_of_compatible_sections
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (hf : IsFinitePresentation f) (hg : FpqcCoverData g)
    (D : FpqcLineBundleDescentDatum f g)
    (V : CompatibleFiniteLinearSystem f g D) :
    ∃ L : LineBundle X,
      IsVeryAmple f L ∧
        Nonempty (LineBundleDescentRealization D.descent L) := by
  obtain ⟨Z, hZ⟩ := compatible_finite_linear_system_effective_descent f g hf hg D V
  exact ⟨Z.lineBundle, hZ, ⟨Z.lineBundleRealization⟩⟩

theorem ample_finitePresentation_has_veryAmple_power
    {X S : Scheme.{u}} (f : X ⟶ S) (L : LineBundle X)
    (hf : IsFinitePresentation f) (hquasi : IsQuasiProjectiveMorphism f)
    (hS : QuasiCompact (𝟙 S)) (hL : IsAmple f L) :
    ∃ n : ℕ, 0 < n ∧ IsVeryAmple f (L.tensorPower n) := by
  sorry

theorem ample_global_embedding_after_a_positive_power
    {X S : Scheme.{u}} (f : X ⟶ S) (L : LineBundle X)
    (hf : IsFinitePresentation f) (hquasi : IsQuasiProjectiveMorphism f)
    (hS : QuasiCompact (𝟙 S)) (hL : IsAmple f L) :
    ∃ n : ℕ, 0 < n ∧ IsVeryAmple f (L.tensorPower n) ∧
      HasGlobalFiniteRankEmbeddingFor f (L.tensorPower n) := by
  sorry

/- Closed immersion is a separate property from immersion.  It is tested on
  the upstairs map and then reflected through the fpqc cover. -/
theorem closedImmersion_faithfullyFlat_descent_of_compatible_sections
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (hf : IsFinitePresentation f) (hg : FpqcCoverData g)
    (D : FpqcLineBundleDescentDatum f g)
    (V : CompatibleFiniteLinearSystem f g D)
    (hclosed : IsClosedImmersion V.system.associatedMap) :
    ∃ Z : DescendedFiniteLinearSystem f g D V,
      IsClosedImmersion Z.embedding.map := by
  sorry

theorem immersion_iff_faithfullyFlat_baseChange
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (hf : IsFinitePresentation f) (hg : FpqcCoverData g) :
    IsImmersion f ↔ IsImmersion (baseChangeToBase f g) := by
  change IsImmersion f ↔
    IsImmersion
      (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.baseChangeToBase
        f g)
  exact
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.immersion_iff_faithfullyFlat_baseChange
      f g hf.1 hf.2.1 hf.2.2 hg.isFaithfullyFlat hg.quasiCompact

theorem closedImmersion_iff_faithfullyFlat_baseChange
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (_hf : IsFinitePresentation f) (hg : FpqcCoverData g) :
    IsClosedImmersion f ↔ IsClosedImmersion (baseChangeToBase f g) := by
  change IsClosedImmersion f ↔ IsClosedImmersion (pullback.snd f g)
  constructor
  · intro h
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @IsClosedImmersion) (IsPullback.of_hasPullback f g) h
  · intro h
    exact
      LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10_closedImmersion_descends
        f g ⟨hg.surjective, hg.flat, hg.quasiCompact⟩ h

theorem openImmersion_iff_faithfullyFlat_baseChange
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (_hf : IsFinitePresentation f) (hg : FpqcCoverData g) :
    IsOpenImmersion f ↔ IsOpenImmersion (baseChangeToBase f g) := by
  change IsOpenImmersion f ↔ IsOpenImmersion (pullback.snd f g)
  constructor
  · intro h
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @IsOpenImmersion) (IsPullback.of_hasPullback f g) h
  · intro h
    exact
      MorphismProperty.of_pullback_snd_of_descendsAlong
        (P := @IsOpenImmersion)
        (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
        (f := f) (g := g)
        ⟨⟨hg.surjective, hg.flat⟩, hg.quasiCompact⟩ h

theorem immersion_upstairs_is_closed_of_proper
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (D : FpqcLineBundleDescentDatum f g)
    (V : CompatibleFiniteLinearSystem f g D)
    (hproper : IsProper (baseChangeToBase f g)) :
    IsClosedImmersion V.system.associatedMap := by
  have hcomp : IsProper
      (V.system.associatedMap ≫ V.system.projectiveBundle.projection) := by
    rw [V.system.associated_over]
    exact hproper
  have hmap : IsProper V.system.associatedMap :=
    (AlgebraicGeometry.IsProper.comp_iff
      (f := V.system.associatedMap)
      (g := V.system.projectiveBundle.projection)).mp hcomp
  exact
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.closedImmersion_of_proper_immersion
      V.system.associatedMap hmap V.system.associated_immersion

/- LOCAL_DEPENDENCY_GUESS: the properness reflection used here is the
  independent scheme-morphism descent result from the preceding book chapter. -/
theorem proper_faithfullyFlat_descent
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (hg : FpqcCoverData g)
    (hproper : IsProper (baseChangeToBase f g)) : IsProper f := by
  apply (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10_properByDefinition_iff_isProper f).mp
  have hproper' :=
    (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10_properByDefinition_iff_isProper
      (baseChangeToBase f g)).mpr hproper
  exact
    LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10_proper_descends
      f g ⟨hg.surjective, hg.flat, hg.quasiCompact⟩ hproper'.2.2 hproper'.1 hproper'.2.1

theorem veryAmple_and_closedImmersion_descent_for_proper_upstairs
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (hf : IsFinitePresentation f) (hg : FpqcCoverData g)
    (D : FpqcLineBundleDescentDatum f g)
    (V : CompatibleFiniteLinearSystem f g D)
    (hproper : IsProper (baseChangeToBase f g)) :
    ∃ Z : DescendedFiniteLinearSystem f g D V,
      IsClosedImmersion Z.embedding.map := by
  apply closedImmersion_faithfullyFlat_descent_of_compatible_sections f g hf hg D V
  exact immersion_upstairs_is_closed_of_proper f g D V hproper

theorem finite_system_global_on_quasiCompact_base
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (hf : IsFinitePresentation f) (hg : FpqcCoverData g)
    (D : FpqcLineBundleDescentDatum f g)
    (V : CompatibleFiniteLinearSystem f g D) :
    ∃ Z : DescendedFiniteLinearSystem f g D V,
      HasGlobalFiniteRankEmbeddingFor f Z.lineBundle := by
  obtain ⟨Z, hZ⟩ := compatible_finite_linear_system_effective_descent f g hf hg D V
  exact ⟨Z, Z.hasGlobalFiniteRankEmbeddingFor⟩

theorem finite_system_local_on_arbitrary_base
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (hf : IsFinitePresentation f) (hg : FpqcCoverData g)
    (D : FpqcLineBundleDescentDatum f g)
    (V : CompatibleFiniteLinearSystem f g D) :
    HasLocalFiniteRankEmbedding f := by
  obtain ⟨Z, hZ⟩ := compatible_finite_linear_system_effective_descent f g hf hg D V
  have hglobal : HasGlobalFiniteRankEmbedding f :=
    ⟨Z.lineBundle, Z.hasGlobalFiniteRankEmbeddingFor⟩
  intro s
  refine ⟨⊤, Set.mem_univ s, ?_⟩
  exact hasGlobalFiniteRankEmbedding_restrict f ⊤ hglobal

structure LocallyClosedProjectivePresentation {X S : Scheme.{u}} (f : X ⟶ S) where
  projectiveBundle :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Chapter04ProjectiveBundle S
  embedding : X ⟶ projectiveBundle.space
  overBase : embedding ≫ projectiveBundle.projection = f
  locallyClosed : IsImmersion embedding

theorem locallyClosed_projective_presentation_descends
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (hf : IsFinitePresentation f) (hg : FpqcCoverData g)
    (D : FpqcLineBundleDescentDatum f g)
    (V : CompatibleFiniteLinearSystem f g D) :
    ∃ _Z : DescendedFiniteLinearSystem f g D V,
      IsQuasiProjectiveMorphism f := by
  obtain ⟨Z, hZ⟩ := compatible_finite_linear_system_effective_descent f g hf hg D V
  exact ⟨Z, hasGlobalFiniteRankEmbeddingFor_isQuasiProjectiveMorphism
    Z.hasGlobalFiniteRankEmbeddingFor⟩

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter15
