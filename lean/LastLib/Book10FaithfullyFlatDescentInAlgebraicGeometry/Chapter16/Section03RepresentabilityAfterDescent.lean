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

def chapter16RepresentedBy {S : Scheme.{u}} (F : Chapter16RelativeFunctor S)
    (Y : Over S) : Prop :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter14.chapter14RepresentedBy F Y

/-! ### Local parameter spaces -/

/- LOCAL_DEPENDENCY_GUESS: the pinned Book 8 interfaces expose representability and projective
families, but not a single Hilbert-parameter object carrying all six closed/open loci.  The local
presentation record keeps those equations and open conditions explicit for the later bridge. -/

structure Chapter16ClosedParameterCondition (P : Scheme.{u}) where
  locus : Set P
  closed : IsClosed locus

structure Chapter16OpenParameterCondition (P : Scheme.{u}) where
  locus : Set P
  open : IsOpen locus

structure Chapter16ParameterLoci (P : Scheme.{u}) where
  groupLaws : Chapter16ClosedParameterCondition P
  endomorphisms : Chapter16ClosedParameterCondition P
  polarizations : Chapter16ClosedParameterCondition P
  determinant : Chapter16ClosedParameterCondition P
  nondegeneracy : Chapter16OpenParameterCondition P
  smoothness : Chapter16OpenParameterCondition P

structure Chapter16LocalParameterPresentation {T S : Scheme.{u}} (g : T ⟶ S) where
  parameter : Scheme.{u}
  parameterMap : parameter ⟶ T
  projectiveEmbedding : Chapter16IsProjectiveMorphism parameterMap
  noetherian_base : Prop
  finitePresentation : Prop
  fixed_polynomial : Prop
  vectorBundles_trivialized : Prop
  ample_canonical_lineBundle : Prop
  hilbertScheme_parameter : Prop
  locallyClosed_parameter : Prop
  parameterLoci : Chapter16ParameterLoci parameter
  localUniversalFamily : Prop
  localRepresentability : Prop

structure Chapter16ParameterSpaceData {S : Scheme.{u}} where
  parameter : Scheme.{u}
  parameterMap : parameter ⟶ S
  projective : Chapter16IsProjectiveMorphism parameterMap
  loci : Chapter16ParameterLoci parameter
  universalFamily : Prop

/-! ### Change of trivialization -/

structure Chapter16ParameterTransition {P Q : Scheme.{u}} where
  iso : P ≅ Q
  universalFamilyCompatibility : Prop
  objectCompatibility : Prop

structure Chapter16TripleParameterTransition
    {P Q R : Scheme.{u}}
    (ePQ : Chapter16ParameterTransition (P := P) (Q := Q))
    (eQR : Chapter16ParameterTransition (P := Q) (Q := R))
    (ePR : Chapter16ParameterTransition (P := P) (Q := R)) where
  triple_identity : ePQ.iso ≪≫ eQR.iso = ePR.iso

theorem chapter16_parameter_transition_is_canonical
    {P Q : Scheme.{u}} (e : Chapter16ParameterTransition (P := P) (Q := Q)) :
    Nonempty (P ≅ Q) := ⟨e.iso⟩

/-! ### Gluing local parameter schemes and universal objects -/

structure Chapter16ModuliDescentPackage {S : Scheme.{u}} (F : Chapter16RelativeFunctor S)
    (I : Type v) where
  family : LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.SchemeFamily S I
  cover : Chapter16FpqcCoveringFamily family
  fppfCover : Chapter16FppfCoveringFamily family
  localParameter : ∀ i,
    Chapter16LocalParameterPresentation (family.map i)
  overlapTransitions : ∀ i j,
    Chapter16ParameterTransition
      (P := (localParameter i).parameter) (Q := (localParameter j).parameter)
  tripleTransitions : ∀ i j k,
    Chapter16TripleParameterTransition
      (overlapTransitions i j) (overlapTransitions j k) (overlapTransitions i k)
  local_universal_cocycle : Prop
  transition_composition_on_objects : Prop

structure Chapter16GluedUniversalFamily {S : Scheme.{u}}
    (F : Chapter16RelativeFunctor S) where
  representingObject : Over S
  representingEquivalence : chapter16RepresentedBy F representingObject
  universalFamily : Prop
  overlap_isomorphisms : Prop
  triple_cocycle : Prop

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
  all_morphisms_invertible : Prop

structure Chapter16SetValuedModuli (S : Scheme.{u}) where
  functor : Chapter16RelativeFunctor S

structure Chapter16ModuliWithAutomorphisms (S : Scheme.{u}) where
  groupoidValued : Chapter16GroupoidValuedModuli S
  automorphismCategory : Type u
  automorphismCategory_structure : Category automorphismCategory
  witness : Chapter16NontrivialAutomorphismWitness automorphismCategory

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
