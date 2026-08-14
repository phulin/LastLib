import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09.Core

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09

noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04

universe u

/-! ### 9.3 The relative dualizing sheaf -/

/-- The curve positivity criterion used to prove local projectivity. -/
structure Chapter09CurvePositivityCriterion
    {X S : Scheme.{u}} (f : X ⟶ S) (L : Chapter04LineBundle X) where
  positiveOnEveryComponent : Prop
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
  lineBundle_is_pullback :
    lineBundle = chapter04PullbackLineBundle normalizationMap L
  componentwiseNonvanishing : Prop
  componentwiseNonvanishing_holds : componentwiseNonvanishing

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
  nodalFibers_holds : nodalFibers

theorem chapter09_nodal_curve_family_is_fpqc_locally_projective
    (F : Chapter09ProperFlatReducedCurveFamily)
    (_N : Chapter09NodalRelativeCurveFamily F) :
    chapter09FpqcLocallyProjective F := by
  exact chapter09_proper_flat_curve_is_fpqc_locally_projective F

/-! ### Relative Ext construction -/

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
  LaurentPairingOverBase_holds : LaurentPairingOverBase
  tensorCompatibility : Prop
  tensorCompatibility_holds : tensorCompatibility
  evaluationAtOneTrace : Prop
  evaluationAtOneTrace_holds : evaluationAtOneTrace
  descentCocycle : Prop
  descentCocycle_holds : descentCocycle

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
  pairingBeforeTensor_holds : pairingBeforeTensor
  pairingAfterTensor : Prop
  pairingAfterTensor_holds : pairingAfterTensor
  compatible : Prop
  compatible_holds : compatible

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
  representsTheSameFunctor_holds : representsTheSameFunctor
  traceCompatible : Prop
  traceCompatible_holds : traceCompatible
  comparisonUnique : Prop
  comparisonUnique_holds : comparisonUnique
  cocycle : Prop
  cocycle_holds : cocycle

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
    [Chapter09RelativeDerivedHomTheory (chapter09BaseChangedFamilyMap f g)]
    (P : Chapter09RelativePerfectEmbeddingProfile
      (chapter09BaseChangedFamilyMap f g))
    [Chapter09ExtTheory (chapter09BaseChangeTotal f g)]
    [Chapter09ExtTheory P.ambient] where
  localExtConstruction :
    Chapter09RelativeExtConstruction (chapter09BaseChangedFamilyMap f g) P
  localDualizingSheaf : (chapter09BaseChangeTotal f g).Modules
  localExtToLocalDualizing :
    chapter09Pushforward P.embedding localDualizingSheaf ≅
      localExtConstruction.extSheaf
  localDualizingSheaf_eq :
    localDualizingSheaf = localExtConstruction.dualizingSheaf
  descendedDualizingSheaf : X.Modules
  comparison :
    localDualizingSheaf ≅
      chapter09Pullback (chapter09BaseChangeToX f g) descendedDualizingSheaf
  traceDescent : Prop
  traceDescent_holds : traceDescent
  dualityDescent : Prop
  dualityDescent_holds : dualityDescent
  cocycle : Prop
  cocycle_holds : cocycle

theorem chapter09_relative_duality_descends_across_projective_embeddings
    (F : Chapter09RelativeCurveFamily)
    (cover : Chapter09FpqcCover F.S)
    (P : Chapter09RelativePerfectEmbeddingProfile
      (chapter09BaseChangedFamilyMap F.f cover.map))
    [Chapter09RelativeDerivedHomTheory F.f]
    [Chapter09RelativeDerivedHomTheory
      (chapter09BaseChangedFamilyMap F.f cover.map)]
    [Chapter09ExtTheory (chapter09BaseChangeTotal F.f cover.map)]
    [Chapter09ExtTheory P.ambient] :
    Nonempty (Chapter09RelativeDescentComparison F.f cover.map P) := by
  sorry

/-! ### Existence, trace, and base change -/

/- The relative Ext profile supplies the perfect-embedding calculation, but
the pinned projective and derived APIs do not identify its Ext sheaf with the
full trace/duality package.  Keep that genuinely missing comparison as a
separate theorem instead of assuming relative Cohen--Macaulayness alone gives
a finite resolution over an arbitrary base. -/
theorem chapter09_relative_ext_construction_yields_dualizing_data
    (F : Chapter09RelativeCurveFamily)
    [Chapter09ExtTheory F.X]
    [Chapter09RelativeDerivedHomTheory F.f]
    (P : Chapter09RelativePerfectEmbeddingProfile F.f)
    [Chapter09ExtTheory P.ambient]
    (E : Chapter09RelativeExtConstruction F.f P) :
    Nonempty (Chapter09RelativeDualizingData F.f) := by
  sorry

/-- Relative dualizing data existence after choosing a perfect projective
embedding. -/
theorem chapter09_relative_dualizing_sheaf_exists_from_perfect_embedding
    (F : Chapter09RelativeCurveFamily)
    [Chapter09ExtTheory F.X]
    [Chapter09RelativeDerivedHomTheory F.f]
    (P : Chapter09RelativePerfectEmbeddingProfile F.f)
    [Chapter09ExtTheory P.ambient] :
    chapter09HasRelativeDualizingSheaf F.f := by
  rcases chapter09_relative_dualizing_sheaf_from_projective_embedding F P with ⟨E⟩
  exact chapter09_relative_ext_construction_yields_dualizing_data F P E

/-- Proper flat Cohen--Macaulay relative curves have relative dualizing data.

The proof uses the missing general relative-duality construction rather than
silently claiming that relative Cohen--Macaulayness supplies a perfect
projective resolution over an arbitrary base. -/
theorem chapter09_relative_dualizing_sheaf_exists
    (F : Chapter09RelativeCurveFamily)
    [Chapter09RelativeDerivedHomTheory F.f] :
    chapter09HasRelativeDualizingSheaf F.f := by
  sorry

/-- The relative trace in (9.3) is the degree-one derived pushforward map. -/
def chapter09_relative_trace
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Chapter09RelativeDerivedHomTheory f]
    (D : Chapter09RelativeDualizingData f) :
    chapter09RPushforward f D.omega 1 ⟶ chapter09StructureSheaf S :=
  D.trace

/-- Relative duality for every vector bundle, formula (9.4). -/
def chapter09_relative_duality
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Chapter09RelativeDerivedHomTheory f]
    (D : Chapter09RelativeDualizingData f)
    (E : X.Modules) (V : Chapter09VectorBundleDualTensor E D.omega)
    (hE : chapter09VectorBundle E) :
    Chapter09RelativeDualityComparison f E D.omega V := by
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

/- A fiber specialization records both the base-change comparison and the
   resulting fiberwise duality comparison. -/
structure Chapter09RelativeDualityFiberSpecialization
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [Chapter09RelativeDerivedHomTheory f]
    [Chapter09RelativeDerivedHomTheory (chapter09BaseChangedFamilyMap f g)]
    (D : Chapter09RelativeDualizingData f)
    (D' : Chapter09RelativeDualizingData (chapter09BaseChangedFamilyMap f g))
    (E : (chapter09BaseChangeTotal f g).Modules)
    (V : Chapter09VectorBundleDualTensor E D'.omega)
    (hE : chapter09VectorBundle E) where
  baseChange : Chapter09RelativeBaseChangeComparison f g D D'
  comparison :
    Chapter09RelativeDualityComparison
      (chapter09BaseChangedFamilyMap f g) E D'.omega V

/-- Formula (9.4) specializes to the absolute curve duality comparison on a fiber. -/
def chapter09_relative_duality_specializes_to_fiber
    (F : Chapter09RelativeCurveFamily)
    [Chapter09RelativeDerivedHomTheory F.f]
    (D : Chapter09RelativeDualizingData F.f) (s : F.S)
    [Chapter09RelativeDerivedHomTheory
      (chapter09BaseChangedFamilyMap F.f (F.S.fromSpecResidueField s))]
    (Dₛ : Chapter09RelativeDualizingData
      (chapter09BaseChangedFamilyMap F.f (F.S.fromSpecResidueField s)))
    (B : Chapter09RelativeBaseChangeComparison
      F.f (F.S.fromSpecResidueField s) D Dₛ)
    (E : (chapter09BaseChangeTotal F.f (F.S.fromSpecResidueField s)).Modules)
    (V : Chapter09VectorBundleDualTensor E Dₛ.omega)
    (hE : chapter09VectorBundle E) :
    Chapter09RelativeDualityFiberSpecialization
      F.f (F.S.fromSpecResidueField s) D Dₛ E V hE := by
  exact
    { baseChange := B
      comparison := Dₛ.relativeDuality E V hE }

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09
