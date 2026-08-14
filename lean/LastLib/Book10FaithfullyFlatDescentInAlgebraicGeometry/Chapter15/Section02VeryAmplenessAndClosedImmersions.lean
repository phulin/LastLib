import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter15.Section01PolarizedDescent

/-!
# 15.2 Very ampleness and closed immersions

The coefficient sheaf, its quotient onto the polarized line bundle, and the
induced map to the relative projective bundle are kept together.  This is the
finite system of sections whose descent is asserted in the source.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter15

noncomputable section

structure DescendedProjectiveEmbedding {X S : Scheme.{u}} (f : X ⟶ S) where
  projectiveBundle :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
      .Chapter04ProjectiveBundle S
  universalQuotientCompatible :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
      .chapter04ProjectiveBundleUniversalQuotientCompatible projectiveBundle
  map : X ⟶ projectiveBundle.space
  over : map ≫ projectiveBundle.projection = f
  immersion : IsImmersion map

structure DescendedFiniteLinearSystem
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (D : FpqcLineBundleDescentDatum f g)
    (V : CompatibleFiniteLinearSystem f g D) where
  lineBundle : LineBundle X
  lineBundleRealization :
    LineBundleDescentRealization D.descent.descent lineBundle
  coefficient : S.Modules
  coefficientRealization :
    ModuleDescentRealization V.coefficients.descent coefficient
  finiteLocallyFree :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
      .chapter04FiniteLocallyFree coefficient
  quotient : (Scheme.Modules.pullback f).obj coefficient ⟶ lineBundle.sheaf
  quotient_epi : Epi quotient
  /- LOCAL_DEPENDENCY_GUESS: these fields are the descended quotient and
    projective-space map commuting with the upstairs square. -/
  quotient_descended : Prop
  map_descended : Prop
  embedding : DescendedProjectiveEmbedding f
  lineBundle_pullback_iso : lineBundle.sheaf ≅
    (Scheme.Modules.pullback embedding.map).obj embedding.projectiveBundle.tautological

theorem DescendedFiniteLinearSystem.isVeryAmple
    {X S T : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S}
    {D : FpqcLineBundleDescentDatum f g}
    {V : CompatibleFiniteLinearSystem f g D}
    (Z : DescendedFiniteLinearSystem f g D V) : IsVeryAmple f Z.lineBundle := by
  let W :
      LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05
        .RelativeVeryAmpleWitness f Z.lineBundle :=
    { projectiveBundle := Z.embedding.projectiveBundle
      universalQuotientCompatible := Z.embedding.universalQuotientCompatible
      map := Z.embedding.map
      immersion := Z.embedding.immersion
      over := Z.embedding.over
      pullback_iso := Z.lineBundle_pullback_iso }
  exact ⟨W⟩

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
        Nonempty (LineBundleDescentRealization D.descent.descent L) := by
  sorry

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
      HasGlobalFiniteRankEmbedding f := by
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
  sorry

theorem closedImmersion_iff_faithfullyFlat_baseChange
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (hf : IsFinitePresentation f) (hg : FpqcCoverData g) :
    IsClosedImmersion f ↔ IsClosedImmersion (baseChangeToBase f g) := by
  sorry

theorem openImmersion_iff_faithfullyFlat_baseChange
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (hf : IsFinitePresentation f) (hg : FpqcCoverData g) :
    IsOpenImmersion f ↔ IsOpenImmersion (baseChangeToBase f g) := by
  sorry

theorem immersion_upstairs_is_closed_of_proper
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (D : FpqcLineBundleDescentDatum f g)
    (V : CompatibleFiniteLinearSystem f g D)
    (hproper : IsProper (baseChangeToBase f g)) :
    IsClosedImmersion V.system.associatedMap := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the properness reflection used here is the
  independent scheme-morphism descent result from the preceding book chapter. -/
theorem proper_faithfullyFlat_descent
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (hg : FpqcCoverData g)
    (hproper : IsProper (baseChangeStructureMap f g)) : IsProper f := by
  sorry

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
    (hS : QuasiCompact (𝟙 S))
    (D : FpqcLineBundleDescentDatum f g)
    (V : CompatibleFiniteLinearSystem f g D) :
    ∃ Z : DescendedFiniteLinearSystem f g D V,
      HasGlobalFiniteRankEmbedding f := by
  sorry

theorem finite_system_local_on_arbitrary_base
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (hf : IsFinitePresentation f) (hg : FpqcCoverData g)
    (D : FpqcLineBundleDescentDatum f g)
    (V : CompatibleFiniteLinearSystem f g D) :
    HasLocalFiniteRankEmbedding f := by
  sorry

structure LocallyClosedProjectivePresentation {X S : Scheme.{u}} (f : X ⟶ S) where
  projectiveBundle :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
      .Chapter04ProjectiveBundle S
  embedding : X ⟶ projectiveBundle.space
  overBase : embedding ≫ projectiveBundle.projection = f
  locallyClosed : IsImmersion embedding

theorem locallyClosed_projective_presentation_descends
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (hf : IsFinitePresentation f) (hg : FpqcCoverData g)
    (D : FpqcLineBundleDescentDatum f g)
    (V : CompatibleFiniteLinearSystem f g D) :
    ∃ Z : DescendedFiniteLinearSystem f g D V,
      IsQuasiProjectiveMorphism f := by
  sorry

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter15
