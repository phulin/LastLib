import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter16.Dependencies

/-!
## 16.4 Practical descent protocol

The protocol is represented as data-bearing steps rather than as proof narration.  The final
separation record keeps size, quasi-compactness, effectivity, and property descent independent.
-/

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter16

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology
open scoped AlgebraicGeometry

universe u v

inductive Chapter16PositivitySource
  | compatibleAmpleLineBundle
  | finiteFlatNorm
  | canonicalPositiveDivisor

inductive Chapter16DescentProtocolStep
  | specifyCover
  | inventoryObjectsAndMorphisms
  | checkTripleCocycle
  | descendFiniteLocallyFreeModules
  | descendAlgebrasAndAffinePieces
  | descendSchemesAndLoci
  | descendFinitenessProperties
  | supplyPositiveLineBundle
  | verifyUniversalProperty

def chapter16PracticalDescentProtocol :
    List Chapter16DescentProtocolStep :=
  [.specifyCover,
   .inventoryObjectsAndMorphisms,
   .checkTripleCocycle,
   .descendFiniteLocallyFreeModules,
   .descendAlgebrasAndAffinePieces,
   .descendSchemesAndLoci,
   .descendFinitenessProperties,
   .supplyPositiveLineBundle,
   .verifyUniversalProperty]

inductive Chapter16DescentComponent
  | carrierScheme
  | structureMap
  | identitySection
  | smoothOpen
  | multiplication
  | action
  | incidenceMorphism
  | finiteLocallyFreeModule
  | algebraAction
   | polarization
   | determinantCondition
   | levelStructure
   | alternatingPairing
   | isotropicSubgroup
   | similitudeFactor
   | fiberCondition
   | closedLocus
  | openLocus
  | universalFamily

def chapter16GeneralizedEllipticDescentInventory :
    List Chapter16DescentComponent :=
  [.carrierScheme, .structureMap, .identitySection, .smoothOpen, .multiplication,
   .action, .incidenceMorphism, .finiteLocallyFreeModule, .fiberCondition]

def chapter16PELDescentInventory : List Chapter16DescentComponent :=
  [.carrierScheme, .structureMap, .finiteLocallyFreeModule, .algebraAction,
   .polarization, .determinantCondition, .levelStructure, .alternatingPairing,
   .isotropicSubgroup, .similitudeFactor, .closedLocus, .openLocus]

inductive Chapter16ProtocolInventoryKind
  | generalizedElliptic
  | pel

def chapter16RequiredProtocolInventory : Chapter16ProtocolInventoryKind →
    List Chapter16DescentComponent
  | .generalizedElliptic => chapter16GeneralizedEllipticDescentInventory
  | .pel => chapter16PELDescentInventory

structure Chapter16ProtocolTransitionData
    {S : Scheme.{u}} {I : Type v}
    (F : LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.SchemeFamily S I)
    where
  /- The canonical descent-data object contains the maps on the pairwise
     fiber products and its triple-overlap cocycle.  Direct maps between the
     cover members would be the wrong domains for descent. -/
  descentData :
    LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11.SchemeDescent.Data
      F.map

structure Chapter16ProtocolIndexingData (I : Type v) where
  indexingType : Type v
  indexingEquivalence : indexingType ≃ I

structure Chapter16ProtocolLocalStepData where
  cardinality : ℕ
  steps : Fin cardinality → Chapter16DescentProtocolStep

structure Chapter16ProtocolModuleData (S : Scheme.{u}) where
  module : S.Modules
  finiteLocallyFree :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04FiniteLocallyFree
      module

structure Chapter16ProtocolAffinePieceData (S : Scheme.{u}) where
  piece : Scheme.{u}
  map : piece ⟶ S
  affine : IsAffine piece
  closedLocus : Set piece
  closedLocus_isClosed : IsClosed closedLocus
  openLocus : Set piece
  openLocus_isOpen : IsOpen openLocus

structure Chapter16ProtocolSchemeEffectivityData
    {S : Scheme.{u}} {I : Type v}
    (F : LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.SchemeFamily S I)
    (D : LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11.SchemeDescent.Data F.map)
    where
  descended : Scheme.{u}
  descendedMap : descended ⟶ S
  comparison : D ≅
    (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11.SchemeDescent.overPseudofunctor.toDescentData
      F.map).obj (Over.mk descendedMap)
  comparison_over : ∀ i,
    (comparison.hom.hom i).left ≫
        ((Over.pullback (F.map i)).obj (Over.mk descendedMap)).hom =
      (D.obj i).hom

structure Chapter16ProtocolMorphismEffectivityData
    {S : Scheme.{u}} {I : Type v}
    (F : LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.SchemeFamily S I)
    (D : LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11.SchemeDescent.Data F.map)
    where
  source : Scheme.{u}
  target : Scheme.{u}
  sourceMap : source ⟶ S
  targetMap : target ⟶ S
  map : source ⟶ target
  map_over : map ≫ targetMap = sourceMap
  descentData : LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11.SchemeDescent.Data F.map
  descentData_matches : descentData = D
  baseMap : Over.mk sourceMap ⟶ Over.mk targetMap
  baseMap_eq : baseMap = Over.homMk map map_over
  baseChangeMap : ∀ i,
    (Over.pullback (F.map i)).obj (Over.mk sourceMap) ⟶
      (Over.pullback (F.map i)).obj (Over.mk targetMap)
  baseChangeMap_is_canonical : ∀ i,
    baseChangeMap i = (Over.pullback (F.map i)).map (Over.homMk map map_over)

structure Chapter16ProtocolMorphismProperties {X S : Scheme.{u}} (f : X ⟶ S) where
  finitePresentation : LocallyOfFinitePresentation f
  flat : Flat f
  smooth : Smooth f
  proper : IsProper f

structure Chapter16ProtocolPositiveLineBundleData
    {S : Scheme.{u}} {I : Type v}
    (F : LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.SchemeFamily S I)
    (D : LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11.SchemeDescent.Data F.map)
    where
  carrier : Scheme.{u}
  map : carrier ⟶ S
  lineBundle : Chapter16LineBundle carrier
  ample : Chapter16IsAmple map lineBundle
  descentData : LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11.SchemeDescent.Data F.map
  descentData_matches : descentData = D
  upstairsLineBundle : ∀ i, Chapter16LineBundle (pullback map (F.map i))
  lineBundle_baseChange : ∀ i,
    Chapter16LineBundle.Isomorphic (upstairsLineBundle i)
      (chapter16BaseChangeLineBundle map (F.map i) lineBundle)

structure Chapter16ProtocolUniversalPropertyData
    (S : Scheme.{u})
    (M : LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter14.Chapter14RelativeFunctor S)
    where
  representingObject : Over S
  fullFaithfulness : M ≅ yoneda.obj representingObject

structure Chapter16ProtocolGlueUniquenessData (S : Scheme.{u}) where
  left : Scheme.{u}
  right : Scheme.{u}
  comparison : left ≅ right
  compatible : (left ≅ right) → Prop
  comparison_compatible : compatible comparison
  uniqueness : ∀ e₁ e₂ : left ≅ right,
    compatible e₁ → compatible e₂ → e₁ = e₂

structure Chapter16ProtocolPropertyDescentData
    {S : Scheme.{u}} {I : Type v}
    (F : LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.SchemeFamily S I)
    (D : LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11.SchemeDescent.Data F.map)
    where
  descentData : LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11.SchemeDescent.Data F.map
  descentData_matches : descentData = D
  properties : ∀ i, Chapter16ProtocolMorphismProperties (F.map i)
  properties_on_descent_data : ∀ i,
    Chapter16ProtocolMorphismProperties (D.obj i).hom

structure Chapter16ProtocolSizeControlData
    {S : Scheme.{u}} {I : Type v}
    (F : LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.SchemeFamily S I)
    where
  indexing : Chapter16ProtocolIndexingData I
  localSteps : Chapter16ProtocolLocalStepData

structure Chapter16ProtocolSeparation
    {S : Scheme.{u}} {I : Type v}
    (F : LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.SchemeFamily S I)
    (M : LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter14.Chapter14RelativeFunctor S)
    where
  sizeControl : Chapter16ProtocolSizeControlData F
  quasiCompactness : Chapter16FpqcCoveringFamily F
  overlapObjectsAndMorphisms : Chapter16ProtocolTransitionData F
  schemeEffectivity : Chapter16ProtocolSchemeEffectivityData F overlapObjectsAndMorphisms.descentData
  propertyDescent : Chapter16ProtocolPropertyDescentData F overlapObjectsAndMorphisms.descentData

inductive Chapter16OptionalFppfCoverCertificate
    {S : Scheme.{u}} {I : Type v}
    (F : LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.SchemeFamily S I)
    : Type (max u v)
  | none
  | some (proof : Chapter16FppfCoveringFamily F)

structure Chapter16DescentProtocolCertificate
    {S : Scheme.{u}} {I : Type v}
    (F : LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.SchemeFamily S I)
    (M : LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter14.Chapter14RelativeFunctor S)
  where
  fpqcCover : Chapter16FpqcCoveringFamily F
  /- An fppf certificate is optional: every fppf cover is used through its fpqc
     consequence, while the protocol also applies to genuinely fpqc covers. -/
  fppfCover : Chapter16OptionalFppfCoverCertificate F
  finite_affine_reduction : ∀ (U : S.Opens), IsAffineOpen U →
    IsCompact (U : Set S) →
      Nonempty
        (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.AffineFiniteFamilyReduction
          F U)
  inventoryKind : Chapter16ProtocolInventoryKind
  inventory : List Chapter16DescentComponent
  inventory_matches_required :
    inventory = chapter16RequiredProtocolInventory inventoryKind
  overlapObjectsAndMorphisms : Chapter16ProtocolTransitionData F
  finiteLocallyFreeModulesFirst : Chapter16ProtocolModuleData S
  affineAlgebrasAndPieces : Chapter16ProtocolAffinePieceData S
  schemeEffectivity :
    Chapter16ProtocolSchemeEffectivityData F overlapObjectsAndMorphisms.descentData
  morphismEffectivity :
    Chapter16ProtocolMorphismEffectivityData F overlapObjectsAndMorphisms.descentData
  finitenessFlatnessSmoothnessProperness : ∀ i,
    Chapter16ProtocolMorphismProperties (F.map i)
  propertyDescent :
    Chapter16ProtocolPropertyDescentData F overlapObjectsAndMorphisms.descentData
  positivitySource : Chapter16PositivitySource
  compatiblePositiveLineBundle :
    Chapter16ProtocolPositiveLineBundleData F overlapObjectsAndMorphisms.descentData
  positiveLineBundle_carrier :
    compatiblePositiveLineBundle.carrier = schemeEffectivity.descended
  universalPropertyByFullFaithfulness : Chapter16ProtocolUniversalPropertyData S M

structure Chapter16ProtocolEffectivityData
    {S : Scheme.{u}} {I : Type v}
    {F : LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.SchemeFamily S I}
    {M : LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter14.Chapter14RelativeFunctor S}
(C : Chapter16DescentProtocolCertificate F M) where
  scheme : Chapter16ProtocolSchemeEffectivityData F C.overlapObjectsAndMorphisms.descentData
  scheme_matches : scheme = C.schemeEffectivity
  morphism : Chapter16ProtocolMorphismEffectivityData F C.overlapObjectsAndMorphisms.descentData
  morphism_matches : morphism = C.morphismEffectivity
  universal : Chapter16ProtocolUniversalPropertyData S M
  universal_matches : universal = C.universalPropertyByFullFaithfulness

theorem chapter16_protocol_certificate_has_all_effectivity_steps
    {S : Scheme.{u}} {I : Type v}
    {F : LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.SchemeFamily S I}
    {M : LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter14.Chapter14RelativeFunctor S}
    (C : Chapter16DescentProtocolCertificate F M) :
    Nonempty (Chapter16ProtocolEffectivityData C) := by
  sorry

structure Chapter16InfiniteFamilyProtocolData
    {S : Scheme.{u}} {I : Type v}
    (F : LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.SchemeFamily S I)
    (M : LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter14.Chapter14RelativeFunctor S)
  where
  setIndexed : Chapter16ProtocolIndexingData I
  fpqcCover : Chapter16FpqcCoveringFamily F
  affineFinitePart : ∀ (U : S.Opens), IsAffineOpen U →
    IsCompact (U : Set S) →
      Nonempty
        (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.AffineFiniteFamilyReduction
          F U)
  localStepsFinite : Chapter16ProtocolLocalStepData
  glueByUniqueness : Chapter16ProtocolGlueUniquenessData S
  overlapObjectsAndMorphisms : Chapter16ProtocolTransitionData F
  schemeEffectivity : Chapter16ProtocolSchemeEffectivityData F overlapObjectsAndMorphisms.descentData
  propertyDescent : Chapter16ProtocolPropertyDescentData F overlapObjectsAndMorphisms.descentData

def chapter16_infinite_family_protocol_separates_size_and_properties
    {S : Scheme.{u}} {I : Type v}
    {F : LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.SchemeFamily S I}
    {M : LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter14.Chapter14RelativeFunctor S}
    (D : Chapter16InfiniteFamilyProtocolData F M) :
    Chapter16ProtocolSeparation F M :=
  { sizeControl :=
      { indexing := D.setIndexed
        localSteps := D.localStepsFinite }
    quasiCompactness := D.fpqcCover
    schemeEffectivity := D.schemeEffectivity
    propertyDescent := D.propertyDescent
    overlapObjectsAndMorphisms := D.overlapObjectsAndMorphisms }

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter16
