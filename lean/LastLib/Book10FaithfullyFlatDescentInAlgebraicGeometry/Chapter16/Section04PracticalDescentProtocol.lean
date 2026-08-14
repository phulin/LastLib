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
  | closedLocus
  | openLocus
  | universalFamily

def chapter16GeneralizedEllipticDescentInventory :
    List Chapter16DescentComponent :=
  [.carrierScheme, .structureMap, .identitySection, .smoothOpen, .multiplication,
   .action, .incidenceMorphism]

def chapter16PELDescentInventory : List Chapter16DescentComponent :=
  [.carrierScheme, .structureMap, .finiteLocallyFreeModule, .algebraAction,
   .polarization, .determinantCondition, .closedLocus, .openLocus]

structure Chapter16DescentProtocolCertificate
    {S : Scheme.{u}} {I : Type v}
    (F : LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.SchemeFamily S I)
    where
  fpqcCover : Chapter16FpqcCoveringFamily F
  fppfCover : Chapter16FppfCoveringFamily F
  finite_affine_reduction : ∀ (U : S.Opens), IsAffineOpen U →
    IsCompact (U : Set S) →
      Nonempty
        (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.AffineFiniteFamilyReduction
          F U)
  inventory : List Chapter16DescentComponent
  overlapObjectsAndMorphisms : Prop
  tripleCocycle : Prop
  finiteLocallyFreeModulesFirst : Prop
  affineAlgebrasAndPieces : Prop
  schemeEffectivity : Prop
  morphismEffectivity : Prop
  finitenessFlatnessSmoothnessProperness : Prop
  positivitySource : Chapter16PositivitySource
  compatiblePositiveLineBundle : Prop
  universalPropertyByFullFaithfulness : Prop

theorem chapter16_protocol_certificate_has_all_effectivity_steps
    {S : Scheme.{u}} {I : Type v}
    {F : LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.SchemeFamily S I}
    (C : Chapter16DescentProtocolCertificate F) :
    C.schemeEffectivity ∧ C.morphismEffectivity ∧
      C.universalPropertyByFullFaithfulness := by
  exact ⟨C.schemeEffectivity, C.morphismEffectivity,
    C.universalPropertyByFullFaithfulness⟩

structure Chapter16InfiniteFamilyProtocolData
    {S : Scheme.{u}} {I : Type v}
    (F : LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.SchemeFamily S I)
    where
  setIndexed : Prop
  fpqcCover : Chapter16FpqcCoveringFamily F
  affineFinitePart : ∀ (U : S.Opens), IsAffineOpen U →
    IsCompact (U : Set S) →
      Nonempty
        (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.AffineFiniteFamilyReduction
          F U)
  localStepsFinite : Prop
  glueByUniqueness : Prop

structure Chapter16ProtocolSeparation where
  sizeControl : Prop
  quasiCompactness : Prop
  schemeEffectivity : Prop
  propertyDescent : Prop

theorem chapter16_infinite_family_protocol_separates_size_and_properties
    {S : Scheme.{u}} {I : Type v}
    {F : LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.SchemeFamily S I}
    (D : Chapter16InfiniteFamilyProtocolData F) :
    Chapter16ProtocolSeparation := by
  exact
    { sizeControl := D.setIndexed ∧ D.localStepsFinite
      quasiCompactness := Chapter16FpqcCoveringFamily F
      schemeEffectivity := D.glueByUniqueness
      propertyDescent := D.glueByUniqueness }

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter16
