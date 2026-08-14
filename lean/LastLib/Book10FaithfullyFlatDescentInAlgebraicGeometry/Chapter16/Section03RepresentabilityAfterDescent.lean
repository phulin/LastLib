import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter16.Dependencies

/-!
## 16.3 Representability after descent

This section records the distinction between effectivity of the objects and representability of a
functor.  The parameter-space records expose the closed equations and open conditions used in the
local construction, while the transition records carry the overlap and triple-overlap data.
-/

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter16

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology
open scoped AlgebraicGeometry

universe u v

abbrev Chapter16RelativeFunctor (S : Scheme.{u}) :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter14.Chapter14RelativeFunctor S

def chapter16RestrictedRelativeFunctor
    {S T : Scheme.{u}} (F : Chapter16RelativeFunctor S) (g : T ⟶ S) :
    Chapter16RelativeFunctor T :=
  (Over.map g).op.comp F

def chapter16RepresentedBy {S : Scheme.{u}} (F : Chapter16RelativeFunctor S)
    (Y : Over S) : Prop :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter14.chapter14RepresentedBy F Y

structure Chapter16ModuleTrivializationCertificate (T : Scheme.{u}) where
  bundle : T.Modules
  finiteLocallyFree :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04FiniteLocallyFree
      bundle
  trivialModule : T.Modules
  trivialization : bundle ≅ trivialModule

structure Chapter16LocalUniversalFamilyData
    {T S P : Scheme.{u}} (g : T ⟶ S) (parameterMap : P ⟶ T) where
  carrier : Scheme.{u}
  familyToParameter : carrier ⟶ P
  familyToBase : carrier ⟶ T
  family_over_parameter : familyToParameter ≫ parameterMap = familyToBase
  family_over_base : familyToBase ≫ g = familyToParameter ≫ parameterMap ≫ g

structure Chapter16ParameterFamilyCompatibility
    {P Q : Scheme.{u}} (iso : P ≅ Q) where
  overlap : Scheme.{u}
  toP : overlap ⟶ P
  toQ : overlap ⟶ Q
  compatibility : toP ≫ iso.hom = toQ

/-! ### Local parameter spaces -/

/- LOCAL_DEPENDENCY_GUESS: the pinned Book 8 interfaces expose representability and projective
families, but not a single Hilbert-parameter object carrying all six closed/open loci.  The local
presentation record keeps those equations and open conditions explicit for the later bridge. -/

structure Chapter16ClosedParameterCondition (P : Scheme.{u}) where
  locus : Set P
  closed : IsClosed locus

structure Chapter16OpenParameterCondition (P : Scheme.{u}) where
  locus : Set P
  isOpen : IsOpen locus

structure Chapter16ParameterLoci (P : Scheme.{u}) where
  groupLaws : Chapter16ClosedParameterCondition P
  endomorphisms : Chapter16ClosedParameterCondition P
  polarizations : Chapter16ClosedParameterCondition P
  determinant : Chapter16ClosedParameterCondition P
  nondegeneracy : Chapter16OpenParameterCondition P
  smoothness : Chapter16OpenParameterCondition P

structure Chapter16LocalParameterPresentation
    {T S : Scheme.{u}} (F : Chapter16RelativeFunctor S) (g : T ⟶ S) where
  parameter : Scheme.{u}
  parameterMap : parameter ⟶ T
  projectiveEmbedding : Chapter16IsProjectiveMorphism parameterMap
  noetherian_base : IsLocallyNoetherian T
  finitePresentation : LocallyOfFinitePresentation parameterMap
  fixed_polynomial :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter14.Chapter14NumericalPolynomial
  vectorBundles_trivialized : Chapter16ModuleTrivializationCertificate T
  canonicalLineBundle : Chapter16LineBundle parameter
  ample_canonical_lineBundle : Chapter16IsAmple parameterMap canonicalLineBundle
  hilbertScheme_parameter :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter14.Chapter14ProjectiveMorphismData
      parameterMap
  locallyClosed_parameter : IsLocallyClosed (Set.range parameterMap)
  parameterLoci : Chapter16ParameterLoci parameter
  localFunctor : Chapter16RelativeFunctor T
  localFunctor_is_restriction : localFunctor = chapter16RestrictedRelativeFunctor F g
  localUniversalFamily :
    Chapter16LocalUniversalFamilyData (𝟙 T) parameterMap
  localRepresentability : chapter16RepresentedBy localFunctor (Over.mk parameterMap)

structure Chapter16ParameterSpaceData {S : Scheme.{u}} where
  parameter : Scheme.{u}
  parameterMap : parameter ⟶ S
  projective : Chapter16IsProjectiveMorphism parameterMap
  loci : Chapter16ParameterLoci parameter
  universalFamily :
    Chapter16LocalUniversalFamilyData (𝟙 S) parameterMap

/-! ### Change of trivialization -/

structure Chapter16ParameterTransition {P Q : Scheme.{u}} where
  iso : P ≅ Q
  overlap_compatibility : Chapter16ParameterFamilyCompatibility iso
  universalFamilyCompatibility : Chapter16ParameterFamilyCompatibility iso
  objectCompatibility : Chapter16ParameterFamilyCompatibility iso

/- A local parameter scheme is only compared with another one after both are pulled back to
the pairwise overlap of their bases.  The generic transition above remains useful for absolute
scheme changes; this record carries the missing over-the-overlap equation for the moduli package. -/
structure Chapter16ParameterOverlapTransition
    {P Q U : Scheme.{u}} (p : P ⟶ U) (q : Q ⟶ U) where
  iso : P ≅ Q
  iso_over : iso.hom ≫ q = p
  iso_inv_over : iso.inv ≫ p = q
  universalFamilyCompatibility : Chapter16ParameterFamilyCompatibility iso
  objectCompatibility : Chapter16ParameterFamilyCompatibility iso

structure Chapter16TripleParameterTransition
    {P Q R : Scheme.{u}}
    (ePQ : Chapter16ParameterTransition (P := P) (Q := Q))
    (eQR : Chapter16ParameterTransition (P := Q) (Q := R))
    (ePR : Chapter16ParameterTransition (P := P) (Q := R)) where
  triple_identity : ePQ.iso ≪≫ eQR.iso = ePR.iso

structure Chapter16CanonicalOverlapDescentData
    {S : Scheme.{u}} {I : Type v}
    (family : LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.SchemeFamily S I)
    (D : LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11.SchemeDescent.Data
      family.map) where
  compare : ∀ (i j : I) (U : Scheme.{u})
    (u : U ⟶ family.obj i) (v : U ⟶ family.obj j)
    (_h : u ≫ family.map i = v ≫ family.map j),
    (Over.pullback u).obj (D.obj i) ≅ (Over.pullback v).obj (D.obj j)
  compare_comp : ∀ (i j k : I) (U : Scheme.{u})
    (u : U ⟶ family.obj i) (v : U ⟶ family.obj j) (w : U ⟶ family.obj k)
    (hij : u ≫ family.map i = v ≫ family.map j)
    (hjk : v ≫ family.map j = w ≫ family.map k)
    (hik : u ≫ family.map i = w ≫ family.map k),
    (compare i j U u v hij).hom ≫ (compare j k U v w hjk).hom =
      (compare i k U u w hik).hom

theorem chapter16_parameter_transition_has_isomorphism
    {P Q : Scheme.{u}} (e : Chapter16ParameterTransition (P := P) (Q := Q)) :
    Nonempty (P ≅ Q) := ⟨e.iso⟩

/-! ### Gluing local parameter schemes and universal objects -/

structure Chapter16ModuliDescentPackage {S : Scheme.{u}} (F : Chapter16RelativeFunctor S)
    (I : Type v) where
  family : LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.SchemeFamily S I
  cover : Chapter16FpqcCoveringFamily family
  fppfCover : Chapter16FppfCoveringFamily family
  localParameter : ∀ i,
    Chapter16LocalParameterPresentation F (family.map i)
  /- The canonical Chapter 11 descent datum already contains the actual pairwise
     and triple-overlap comparisons.  Keeping a second family of unrelated
     transition isomorphisms would not express the cocycle. -/
  parameterSchemeDescent :
    LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11.SchemeDescent.Data
      family.map
  parameterSchemeDescent_comparison : ∀ i,
    parameterSchemeDescent.obj i ≅
      Over.mk ((localParameter i).parameterMap)
  parameterOverlap :
    Chapter16CanonicalOverlapDescentData family parameterSchemeDescent
  localRepresentability : ∀ i,
    chapter16RepresentedBy (localParameter i).localFunctor
      (Over.mk (localParameter i).parameterMap)
  /- Universal families need their own descent datum.  The parameter-space
     cocycle does not, by itself, glue the carriers of the universal family. -/
  universalFamilyDescent :
    LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11.SchemeDescent.Data
      (ι := I) (S := S)
      (X := fun i => family.obj i) family.map
  universalFamilyDescent_comparison : ∀ i,
    universalFamilyDescent.obj i ≅
      Over.mk ((localParameter i).localUniversalFamily.familyToBase)
  universalFamilyOverlap :
    Chapter16CanonicalOverlapDescentData family universalFamilyDescent
  universalFamily_parameter_map : ∀ i,
    universalFamilyDescent.obj i ⟶ parameterSchemeDescent.obj i
  universalFamily_parameter_map_matches : ∀ i,
    (universalFamilyDescent_comparison i).hom ≫
        Over.homMk
          (U := Over.mk ((localParameter i).localUniversalFamily.familyToBase))
          (V := Over.mk ((localParameter i).parameterMap))
          (localParameter i).localUniversalFamily.familyToParameter
          (localParameter i).localUniversalFamily.family_over_parameter =
      universalFamily_parameter_map i ≫
        (parameterSchemeDescent_comparison i).hom
  parameter_transition_natural :
    ∀ (i j : I) (U : Scheme.{u})
      (u : U ⟶ family.obj i) (v : U ⟶ family.obj j)
      (_h : u ≫ family.map i = v ≫ family.map j),
      (Over.pullback u).obj (Over.mk ((localParameter i).parameterMap)) ≅
        (Over.pullback v).obj (Over.mk ((localParameter j).parameterMap))
  parameter_transition_is_canonical :
    ∀ (i j : I) (U : Scheme.{u})
      (u : U ⟶ family.obj i) (v : U ⟶ family.obj j)
      (h : u ≫ family.map i = v ≫ family.map j),
      parameter_transition_natural i j U u v h =
        (Over.pullback u).mapIso (parameterSchemeDescent_comparison i).symm ≪≫
          parameterOverlap.compare i j U u v h ≪≫
          (Over.pullback v).mapIso (parameterSchemeDescent_comparison j)
  universalFamily_transition_natural :
    ∀ (i j : I) (U : Scheme.{u})
      (u : U ⟶ family.obj i) (v : U ⟶ family.obj j)
      (_h : u ≫ family.map i = v ≫ family.map j),
      (Over.pullback u).obj
          (Over.mk ((localParameter i).localUniversalFamily.familyToBase)) ≅
        (Over.pullback v).obj
          (Over.mk ((localParameter j).localUniversalFamily.familyToBase))
  universalFamily_transition_is_canonical :
    ∀ (i j : I) (U : Scheme.{u})
      (u : U ⟶ family.obj i) (v : U ⟶ family.obj j)
      (h : u ≫ family.map i = v ≫ family.map j),
      universalFamily_transition_natural i j U u v h =
        (Over.pullback u).mapIso (universalFamilyDescent_comparison i).symm ≪≫
          universalFamilyOverlap.compare i j U u v h ≪≫
          (Over.pullback v).mapIso (universalFamilyDescent_comparison j)

structure Chapter16GluedUniversalFamilyData {S : Scheme.{u}} (Y : Over S) where
  index : Type v
  localCarrier : index → Scheme.{u}
  localMap : ∀ i, localCarrier i ⟶ S
  localToGlobal : ∀ i, localCarrier i ⟶ Y.left
  localToGlobal_over : ∀ i, localToGlobal i ≫ Y.hom = localMap i
  transition : ∀ i j, localCarrier i ≅ localCarrier j
  transition_over : ∀ i j,
    (transition i j).hom ≫ localMap j = localMap i
  transition_compatible_with_global : ∀ i j,
    (transition i j).hom ≫ localToGlobal j = localToGlobal i
  triple_cocycle : ∀ i j k,
    transition i j ≪≫ transition j k = transition i k

structure Chapter16GluedUniversalFamily {S : Scheme.{u}}
    (F : Chapter16RelativeFunctor S) where
  representingObject : Over S
  representingEquivalence : chapter16RepresentedBy F representingObject
  universalFamily : Chapter16GluedUniversalFamilyData representingObject
  overlap_isomorphisms : ∀ i j,
    universalFamily.localCarrier i ≅ universalFamily.localCarrier j
  overlap_isomorphisms_match : ∀ i j,
    overlap_isomorphisms i j = universalFamily.transition i j
  triple_cocycle : ∀ i j k,
    universalFamily.transition i j ≪≫ universalFamily.transition j k =
      universalFamily.transition i k

theorem chapter16_parameter_spaces_glue
    {S : Scheme.{u}} {F : Chapter16RelativeFunctor S} {I : Type v}
    (D : Chapter16ModuliDescentPackage F I) :
    Nonempty (Chapter16GluedUniversalFamily F) := by
  sorry

theorem chapter16_representability_after_descent
    {S : Scheme.{u}} {F : Chapter16RelativeFunctor S} {I : Type v}
    (D : Chapter16ModuliDescentPackage F I) :
    ∃ Y : Over S, chapter16RepresentedBy F Y := by
  rcases chapter16_parameter_spaces_glue D with ⟨G⟩
  exact ⟨G.representingObject, G.representingEquivalence⟩

theorem chapter16_full_faithfulness_recovers_the_moduli_functor
    {S : Scheme.{u}} {F : Chapter16RelativeFunctor S} {Y : Over S}
    (h : chapter16RepresentedBy F Y) : Nonempty (F ≅ yoneda.obj Y) := h

/-! ### Groupoids, automorphisms, and the Book 13 boundary -/

structure Chapter16NontrivialAutomorphismWitness (C : Type u) [Category C] where
  object : C
  automorphism : object ≅ object
  nontrivial : automorphism.hom ≠ 𝟙 object

structure Chapter16GroupoidValuedModuli (S : Scheme.{u}) where
  functor : (Over S)ᵒᵖ ⥤ Cat.{u, u}
  all_morphisms_invertible :
    ∀ X : (Over S)ᵒᵖ, ∀ {A B : functor.obj X} (f : A ⟶ B), IsIso f

structure Chapter16SetValuedModuli (S : Scheme.{u}) where
  functor : Chapter16RelativeFunctor S

structure Chapter16ModuliWithAutomorphisms (S : Scheme.{u}) where
  groupoidValued : Chapter16GroupoidValuedModuli S
  witnessBase : Over S
  witness :
    Chapter16NontrivialAutomorphismWitness
      (groupoidValued.functor.obj (Opposite.op witnessBase))

inductive Chapter16ModuliValueKind
  | setValued
  | groupoidValued

def chapter16_moduli_with_automorphisms_kind : Chapter16ModuliValueKind :=
  .groupoidValued

/- The later stack language is named explicitly so that a set-valued representability theorem is not
 read as a coarse moduli-space theorem. -/
inductive Chapter16Book13Continuation
  | stacks
  | inertia
  | rigidification
  | coarseSpaces

def chapter16_topics_reserved_for_book13 :
    List Chapter16Book13Continuation :=
  [.stacks, .inertia, .rigidification, .coarseSpaces]

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter16
