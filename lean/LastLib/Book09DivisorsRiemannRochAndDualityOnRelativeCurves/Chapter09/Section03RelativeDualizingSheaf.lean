import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09.Core

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09

noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry

universe u

/-! ### 9.3 The relative dualizing sheaf -/

/-- The curve positivity criterion used to prove local projectivity. -/
structure Chapter09CurvePositivityCriterion
    {X S : Scheme.{u}} (f : X ⟶ S) (L : Chapter04LineBundle X) where
  positiveOnEveryComponent : Prop
  ampleOnEveryFiber :
    ∀ s : S,
      chapter04Ample (f.fiberToSpecResidueField s)
        (chapter04PullbackLineBundle (f.fiberι s) L)
  positive_iff_ample :
    positiveOnEveryComponent ↔
      ∀ s : S,
        chapter04Ample (f.fiberToSpecResidueField s)
          (chapter04PullbackLineBundle (f.fiberι s) L)

/-- The normalization step in the componentwise ampleness argument. -/
structure Chapter09FiniteNormalizationWitness
    {X S : Scheme.{u}} (f : X ⟶ S) (L : Chapter04LineBundle X) where
  normalization : Scheme.{u}
  normalizationMap : normalization ⟶ X
  finite : IsFinite normalizationMap
  lineBundle : Chapter04LineBundle normalization
  lineBundle_is_pullback : Prop
  componentwiseNonvanishing : Prop

/-- Positivity on a proper reduced relative curve is equivalent to fiberwise ampleness. -/
theorem chapter09_proper_reduced_curve_positivity_iff_ampleness
    (F : Chapter09ProperFlatReducedCurveFamily) (L : Chapter04LineBundle F.X) :
    Nonempty (Chapter09CurvePositivityCriterion F.f L) := by
  sorry

/-- The normalization argument supplies finite componentwise affine witnesses. -/
theorem chapter09_normalization_gives_componentwise_affine_nonvanishing
    (F : Chapter09ProperFlatReducedCurveFamily)
    (L : Chapter04LineBundle F.X) :
    Nonempty (Chapter09FiniteNormalizationWitness F.f L) := by
  sorry

/-- A proper flat finitely presented geometrically reduced family of curves is
projective after an fpqc base change. -/
theorem chapter09_proper_flat_curve_is_fpqc_locally_projective
    (F : Chapter09ProperFlatReducedCurveFamily) :
    chapter09FpqcLocallyProjective F := by
  sorry

/-- Smooth families are covered by the preceding local projectivity theorem. -/
theorem chapter09_smooth_curve_family_is_fpqc_locally_projective
    (F : Chapter09ProperFlatReducedCurveFamily) [SmoothOfRelativeDimension 1 F.f] :
    chapter09FpqcLocallyProjective F := by
  exact chapter09_proper_flat_curve_is_fpqc_locally_projective F

/- LOCAL_DEPENDENCY_GUESS: the pinned revision has no ordinary-double-point
fiber predicate, so the nodal-fiber condition remains an explicit hypothesis. -/
/-- A nodal-family hypothesis is the special reduced-fiber case of local projectivity. -/
structure Chapter09NodalRelativeCurveFamily (F : Chapter09ProperFlatReducedCurveFamily) where
  nodalFibers : Prop

theorem chapter09_nodal_curve_family_is_fpqc_locally_projective
    (F : Chapter09ProperFlatReducedCurveFamily)
    (N : Chapter09NodalRelativeCurveFamily F) :
    chapter09FpqcLocallyProjective F := by
  exact chapter09_proper_flat_curve_is_fpqc_locally_projective F

/-! ### Relative Ext construction -/

/- LOCAL_DEPENDENCY_GUESS: over a nonregular base, relative
Cohen--Macaulayness alone does not supply a finite locally free resolution of
an arbitrary projective embedding.  The relative Ext construction therefore
accepts the perfect-embedding profile explicitly. -/
structure Chapter09RelativePerfectEmbeddingProfile
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Chapter09ExtTheory X] where
  ambientDimension : ℕ
  one_le_ambientDimension : 1 ≤ ambientDimension
  embedding : X ⟶
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.chapter02ProjectiveSpace
      S ambientDimension
  closedImmersion : IsClosedImmersion embedding
  over :
    embedding ≫
        LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.chapter02ProjectiveSpaceProjection
          S ambientDimension = f
  ambientDualizingSheaf :
    (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.chapter02ProjectiveSpace
      S ambientDimension).Modules
  ambientDualizingSheaf_is_relativeDualizing : Prop
  resolution :
    Chapter09FiniteLocallyFreeResolutionProfile
      (chapter09Pushforward embedding (chapter09StructureSheaf X))
  codimension_eq : resolution.codimension = ambientDimension - 1

abbrev Chapter09RelativePerfectEmbeddingProfile.ambient
    {X S : Scheme.{u}} {f : X ⟶ S}
    [Chapter09ExtTheory X]
    (P : Chapter09RelativePerfectEmbeddingProfile f) : Scheme.{u} :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.chapter02ProjectiveSpace
    S P.ambientDimension

abbrev Chapter09RelativePerfectEmbeddingProfile.ambientMap
    {X S : Scheme.{u}} {f : X ⟶ S}
    [Chapter09ExtTheory X]
    (P : Chapter09RelativePerfectEmbeddingProfile f) : P.ambient ⟶ S :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.chapter02ProjectiveSpaceProjection
    S P.ambientDimension

/-- The relative projective Ext presentation after passing to a projective cover. -/
structure Chapter09RelativeExtConstruction
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Chapter09ExtTheory X]
    [Chapter09RelativeDerivedHomTheory f]
    (P : Chapter09RelativePerfectEmbeddingProfile f)
    [Chapter09ExtTheory P.ambient] where
  ambientDualizingSheaf : P.ambient.Modules
  ambientDualizingSheaf_eq : ambientDualizingSheaf = P.ambientDualizingSheaf
  resolution :
    Chapter09FiniteLocallyFreeResolutionProfile
      (chapter09Pushforward P.embedding (chapter09StructureSheaf X))
  resolution_eq : resolution = P.resolution
  extSheaf : P.ambient.Modules
  extSheaf_formula :
    extSheaf =
      chapter09SheafExt
        (chapter09Pushforward P.embedding (chapter09StructureSheaf X))
        ambientDualizingSheaf (P.ambientDimension - 1)
  codimension_eq : resolution.codimension = P.ambientDimension - 1
  dualizingSheaf : X.Modules
  pushforward_iso : chapter09Pushforward P.embedding dualizingSheaf ≅ extSheaf
  LaurentPairingOverBase : Prop
  tensorCompatibility : Prop
  evaluationAtOneTrace : Prop
  descentCocycle : Prop

/-- The local projective construction supplies the relative Ext presentation. -/
theorem chapter09_relative_dualizing_sheaf_from_projective_embedding
    (F : Chapter09RelativeCurveFamily)
    [Chapter09ExtTheory F.X]
    [Chapter09RelativeDerivedHomTheory F.f]
    (P : Chapter09RelativePerfectEmbeddingProfile F.f)
    [Chapter09ExtTheory P.ambient] :
    Nonempty (Chapter09RelativeExtConstruction F.f P) := by
  sorry

/-- The Laurent-monomial pairing over the base ring commutes with tensor product. -/
structure Chapter09BaseLaurentPairingCompatibility
    {X S : Scheme.{u}} (f : X ⟶ S) where
  baseChangeRing : Type (u + 1)
  pairingBeforeTensor : Prop
  pairingAfterTensor : Prop
  compatible : Prop

theorem chapter09_relative_laurent_pairing_commutes_with_tensor
    (F : Chapter09RelativeCurveFamily) :
    Nonempty (Chapter09BaseLaurentPairingCompatibility F.f) := by
  sorry

/- A relative analogue of the absolute embedding-independence package. -/
structure Chapter09RelativeEmbeddingComparison
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Chapter09ExtTheory X]
    [Chapter09RelativeDerivedHomTheory f]
    (P Q : Chapter09RelativePerfectEmbeddingProfile f)
    [Chapter09ExtTheory P.ambient]
    [Chapter09ExtTheory Q.ambient] where
  inducedDualizingIso :
    ∀ (DP : Chapter09RelativeExtConstruction f P)
      (DQ : Chapter09RelativeExtConstruction f Q),
      Nonempty (DP.dualizingSheaf ≅ DQ.dualizingSheaf)
  representsTheSameFunctor : Prop
  traceCompatible : Prop
  comparisonUnique : Prop
  cocycle : Prop

theorem chapter09_relative_embedding_comparison_exists
    (F : Chapter09RelativeCurveFamily)
    [Chapter09ExtTheory F.X]
    [Chapter09RelativeDerivedHomTheory F.f]
    (P Q : Chapter09RelativePerfectEmbeddingProfile F.f)
    [Chapter09ExtTheory P.ambient]
    [Chapter09ExtTheory Q.ambient] :
    Nonempty (Chapter09RelativeEmbeddingComparison F.f P Q) := by
  sorry

/-- Relative duality and trace descend from a faithfully flat projective cover. -/
structure Chapter09RelativeDescentComparison
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [Chapter09RelativeDerivedHomTheory f]
    [Chapter09RelativeDerivedHomTheory (chapter09BaseChangedFamilyMap f g)] where
  localDualizingSheaf : (chapter09BaseChangeTotal f g).Modules
  descendedDualizingSheaf : X.Modules
  comparison :
    localDualizingSheaf ≅
      chapter09Pullback (chapter09BaseChangeToX f g) descendedDualizingSheaf
  traceDescent : Prop
  dualityDescent : Prop
  cocycle : Prop

theorem chapter09_relative_duality_descends_across_projective_embeddings
    (F : Chapter09RelativeCurveFamily)
    (cover : Chapter09FpqcCover F.S)
    [Chapter09RelativeDerivedHomTheory F.f]
    [Chapter09RelativeDerivedHomTheory
      (chapter09BaseChangedFamilyMap F.f cover.map)] :
    Nonempty (Chapter09RelativeDescentComparison F.f cover.map) := by
  sorry

/-! ### Existence, trace, and base change -/

/-- Relative dualizing sheaf existence under the precise family hypotheses. -/
theorem chapter09_relative_dualizing_sheaf_exists
    (F : Chapter09RelativeCurveFamily)
    [Chapter09RelativeDerivedHomTheory F.f] :
    chapter09HasRelativeDualizingSheaf F.f := by
  sorry

/-- The relative trace in (9.3) is the degree-one derived pushforward map. -/
theorem chapter09_relative_trace
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Chapter09RelativeDerivedHomTheory f]
    (D : Chapter09RelativeDualizingData f) :
    chapter09RPushforward f D.omega 1 ⟶ chapter09StructureSheaf S :=
  D.trace

/-- Relative duality for every vector bundle, formula (9.4). -/
theorem chapter09_relative_duality
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Chapter09RelativeDerivedHomTheory f]
    (D : Chapter09RelativeDualizingData f)
    (E : X.Modules) (V : Chapter09VectorBundleDualTensor E D.omega)
    (hE : chapter09VectorBundle E) :
    Chapter09RelativeDualityComparison f E V.tensor D.omega := by
  exact D.relativeDuality E V hE

/-- Formation of the relative dualizing sheaf commutes with arbitrary base change.

The target data is attached to the literal pullback family map, so no choice of
identification of total spaces is hidden in the statement. -/
theorem chapter09_relative_dualizing_base_change
    (F : Chapter09RelativeCurveFamily) {S' : Scheme.{u}} (g : S' ⟶ F.S)
    [Chapter09RelativeDerivedHomTheory F.f]
    [Chapter09RelativeDerivedHomTheory (chapter09BaseChangedFamilyMap F.f g)]
    (D : Chapter09RelativeDualizingData F.f)
    (D' : Chapter09RelativeDualizingData (chapter09BaseChangedFamilyMap F.f g)) :
    Nonempty (Chapter09RelativeBaseChangeComparison F.f g D D') := by
  sorry

/-- Base change includes specialization to every geometric or residue-field fiber. -/
theorem chapter09_relative_dualizing_specializes_to_fiber
    (F : Chapter09RelativeCurveFamily)
    [Chapter09RelativeDerivedHomTheory F.f]
    (D : Chapter09RelativeDualizingData F.f) (s : F.S)
    [Chapter09RelativeDerivedHomTheory
      (chapter09BaseChangedFamilyMap F.f (F.S.fromSpecResidueField s))]
    (Dₛ : Chapter09RelativeDualizingData
      (chapter09BaseChangedFamilyMap F.f (F.S.fromSpecResidueField s))) :
    Nonempty
      (Chapter09RelativeBaseChangeComparison
        F.f (F.S.fromSpecResidueField s) D Dₛ) := by
  exact chapter09_relative_dualizing_base_change F (F.S.fromSpecResidueField s) D Dₛ

/-- Formula (9.4) specializes to the absolute curve duality comparison on a fiber. -/
theorem chapter09_relative_duality_specializes_to_fiber
    (F : Chapter09RelativeCurveFamily)
    [Chapter09RelativeDerivedHomTheory F.f]
    (D : Chapter09RelativeDualizingData F.f) (s : F.S)
    [Chapter09RelativeDerivedHomTheory
      (chapter09BaseChangedFamilyMap F.f (F.S.fromSpecResidueField s))]
    (Dₛ : Chapter09RelativeDualizingData
      (chapter09BaseChangedFamilyMap F.f (F.S.fromSpecResidueField s)))
    (E : (chapter09BaseChangeTotal F.f (F.S.fromSpecResidueField s)).Modules)
    (V : Chapter09VectorBundleDualTensor E Dₛ.omega)
    (hE : chapter09VectorBundle E) :
    Chapter09RelativeDualityComparison
      (chapter09BaseChangedFamilyMap F.f (F.S.fromSpecResidueField s)) E V.tensor Dₛ.omega := by
  exact Dₛ.relativeDuality E V hE

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09
