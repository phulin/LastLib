import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09

noncomputable section

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open scoped AlgebraicGeometry

universe u v

/-!
This file contains the shared book-facing interfaces for Chapter 9.  In
particular, the pinned Mathlib checkout has module sheaves and their ordinary
cohomology, but it does not yet expose the sheaf-Ext and derived-duality
objects used by the textbook.  Those two missing interfaces are kept explicit
below, so the statements do not silently replace a derived assertion by a
cohomological one.
-/

/-! ### Basic sheaf operations and cohomology -/

/-- The structure sheaf, in the module-sheaf category used by the preceding book. -/
abbrev chapter09StructureSheaf (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- A coherent module sheaf, using the canonical quasi-coherence and finite-type predicates. -/
def chapter09Coherent {X : Scheme.{u}} (F : X.Modules) : Prop :=
  F.IsQuasicoherent ∧ F.IsFiniteType

/-- The canonical cohomology object supplied by Book 8, viewed as its carrier type. -/
abbrev chapter09H {X : Scheme.{u}} (F : X.Modules) (i : ℕ) : Type (u + 1) :=
  chapter04Cohomology F i

/-- The bundled cohomology object underlying `chapter09H`. -/
abbrev chapter09HObject {X : Scheme.{u}} (F : X.Modules) (i : ℕ) : AddCommGrpCat.{u + 1} :=
  chapter04Cohomology F i

/-- Functoriality of the canonical cohomology construction on module sheaves. -/
abbrev chapter09CohomologyMap
    {X : Scheme.{u}} {F G : X.Modules} (φ : F ⟶ G) (i : ℕ) :
    chapter09HObject F i ⟶ chapter09HObject G i :=
  (chapter04CanonicalCohomologyContext X).map φ i

theorem chapter09CohomologyMap_id
    {X : Scheme.{u}} (F : X.Modules) (i : ℕ) :
    chapter09CohomologyMap (𝟙 F) i = 𝟙 _ := by
  exact (chapter04CanonicalCohomologyContext X).map_id F i

theorem chapter09CohomologyMap_comp
    {X : Scheme.{u}} {F G H : X.Modules}
    (φ : F ⟶ G) (ψ : G ⟶ H) (i : ℕ) :
    chapter09CohomologyMap (φ ≫ ψ) i =
      chapter09CohomologyMap φ i ≫ chapter09CohomologyMap ψ i := by
  exact (chapter04CanonicalCohomologyContext X).map_comp φ ψ i

/-- The underlying (not yet scalar-enhanced) dual of a cohomology type. -/
abbrev chapter09Dual (k V : Type*) := V → k

/-- The linear dual used when the cohomology scalar action is available. -/
abbrev chapter09LinearDual (k V : Type*) [Semiring k] [AddCommGroup V] [Module k V] :=
  V →ₗ[k] k

/-- Pushforward of a module sheaf along a scheme morphism. -/
abbrev chapter09Pushforward {X Y : Scheme.{u}} (i : X ⟶ Y) (F : X.Modules) : Y.Modules :=
  (Scheme.Modules.pushforward i).obj F

/-- Pullback of a module sheaf along a scheme morphism. -/
abbrev chapter09Pullback {X Y : Scheme.{u}} (i : Y ⟶ X) (F : X.Modules) : Y.Modules :=
  (Scheme.Modules.pullback i).obj F

/-- An invertible module sheaf, bridged to Book 8's canonical local criterion. -/
def chapter09IsInvertible {X : Scheme.{u}} (F : X.Modules) : Prop :=
  chapter04IsInvertible F

/-- A finite locally free module sheaf, i.e. a vector bundle for this chapter. -/
def chapter09VectorBundle {X : Scheme.{u}} (E : X.Modules) : Prop :=
  SheafOfModules.IsLocallyFree E ∧ SheafOfModules.IsFiniteType E

/-- A vector-bundle dual tensored with a proposed dualizing sheaf.

The equality field records the canonical tensor construction while leaving the
dual bundle itself as the input supplied by the vector-bundle API. -/
structure Chapter09VectorBundleDualTensor
    {X : Scheme.{u}} (E ω : X.Modules) where
  dual : X.Modules
  dual_is_the_dual : Prop
  dual_is_vectorBundle : chapter09VectorBundle dual
  tensor : X.Modules
  tensor_eq : tensor = chapter04Tensor dual ω

/-- A two-sided perfect pairing, before scalar-linearity is added by the field API. -/
structure Chapter09PerfectPairing (k A B : Type*) where
  pairing : A → B → k
  perfect_left : Function.Bijective (fun a => fun b => pairing a b)
  perfect_right : Function.Bijective (fun b => fun a => pairing a b)

/-- The scalar-linear form of a perfect pairing over the field of definition. -/
structure Chapter09LinearPerfectPairing
    (k A B : Type*) [Semiring k]
    [AddCommGroup A] [Module k A]
    [AddCommGroup B] [Module k B] where
  leftPairing : A →ₗ[k] (B →ₗ[k] k)
  leftPerfect : Function.Bijective leftPairing
  rightPairing : B →ₗ[k] (A →ₗ[k] k)
  rightPerfect : Function.Bijective rightPairing
  compatibility : ∀ a b, leftPairing a b = rightPairing b a

/-! ### The missing Ext interface -/

/- LOCAL_DEPENDENCY_GUESS: Mathlib's `CategoryTheory.Abelian.Ext` is an Ext
functor for an abelian category with enough projectives, but the pinned
module-sheaf category does not expose the sheaf-Ext operation used in the
chapter.  This class is the smallest book-facing interface for both the
sheaf-valued and global Ext terms; it does not assert any duality theorem. -/
class Chapter09ExtTheory (X : Scheme.{u}) where
  groupExt : X.Modules → X.Modules → ℕ → Type (u + 1)
  sheafExt : X.Modules → X.Modules → ℕ → X.Modules
  groupExtAddCommGroup : ∀ F G n, AddCommGroup (groupExt F G n)

attribute [instance] Chapter09ExtTheory.groupExtAddCommGroup

/-- The global Ext type used in the proper-curve duality statements. -/
abbrev chapter09Ext {X : Scheme.{u}} [Chapter09ExtTheory X]
    (F G : X.Modules) (n : ℕ) : Type (u + 1) :=
  Chapter09ExtTheory.groupExt F G n

/-- The sheaf-valued Ext object used by the projective construction. -/
abbrev chapter09SheafExt {X : Scheme.{u}} [Chapter09ExtTheory X]
    (F G : X.Modules) (n : ℕ) : X.Modules :=
  Chapter09ExtTheory.sheafExt F G n

/-! ### Curves over a field and zero-dimensional sheaves -/

/-- The zero-dimensional coherent-sheaf hypothesis used in (9.1). -/
structure Chapter09ZeroDimensionalCoherentSheaf (X : Scheme.{u}) where
  carrier : X.Modules
  coherent : chapter09Coherent carrier
  zeroDimensionalSupport : Prop

/-- Predicate form of `Chapter09ZeroDimensionalCoherentSheaf`. -/
def chapter09ZeroDimensional {X : Scheme.{u}} (T : X.Modules) : Prop :=
  ∃ hT : Chapter09ZeroDimensionalCoherentSheaf X, hT.carrier = T

/-- A proper curve over a field, with the dimension-one assertion kept explicit. -/
structure Chapter09ProperCurveOverField (k : Type u) [Field k] where
  scheme : Scheme.{u}
  structureMap : scheme ⟶ AlgebraicGeometry.Spec (.of k)
  proper : IsProper structureMap
  quasiCompact : QuasiCompact structureMap
  locallyOfFinitePresentation : LocallyOfFinitePresentation structureMap
  pureDimensionOne : Prop

/-- A proper Cohen--Macaulay curve over a field. -/
structure Chapter09CohenMacaulayCurveOverField
    (k : Type u) [Field k] extends Chapter09ProperCurveOverField k where
  relativeCohenMacaulay : Prop

/- LOCAL_DEPENDENCY_GUESS: local Cohen--Macaulayness is a property of all
stalks; it is not identified with a tautological proposition. -/
structure Chapter09CohenMacaulayProfile (X : Scheme.{u}) : Type (u + 1) where
  stalkwise : ∀ x : X, Prop

/- LOCAL_DEPENDENCY_GUESS: the pinned Mathlib API has no local
Cohen--Macaulay predicate for scheme stalks.  This named proposition is kept
as a hypothesis field until the corresponding local commutative-algebra API is
available. -/
def chapter09CohenMacaulay (X : Scheme.{u}) : Prop :=
  ∃ h : Chapter09CohenMacaulayProfile X, ∀ x, h.stalkwise x

/-! ### Absolute duality package -/

/-- The absolute derived-duality comparison represented by (9.2).

The two type families are the book-facing derived `RHom` objects.  A later
derived-category implementation can replace this interface without changing
the chapter statements. -/
class Chapter09AbsoluteDerivedHomTheory (k : Type u) [Field k] (X : Scheme.{u}) where
  globalSections : X.Modules → Type (u + 1)
  baseRHom : Type (u + 1) → ℤ → Type (u + 1)
  schemeRHom : X.Modules → X.Modules → ℤ → Type (u + 1)

/-- A comparison object for the shifted form of absolute duality. -/
structure Chapter09AbsoluteDerivedDualityComparison
    (k : Type u) [Field k] {X : Scheme.{u}}
    [Chapter09AbsoluteDerivedHomTheory k X]
  (F ω : X.Modules) where
  comparison :
    Chapter09AbsoluteDerivedHomTheory.baseRHom
        (Chapter09AbsoluteDerivedHomTheory.globalSections F) 0 ≃
      Chapter09AbsoluteDerivedHomTheory.schemeRHom F ω 1
  quasi_isomorphism : Prop

/-- A trace-compatible isomorphism between two proposed absolute dualizing sheaves. -/
structure Chapter09TraceCompatibleIso
    (k : Type u) [Field k] {X : Scheme.{u}}
    (D E : X.Modules)
    (trD : chapter09H D 1 → k) (trE : chapter09H E 1 → k) where
  iso : D ≅ E
  trace_compatibility :
    ∀ x, trD x =
      trE ((chapter04CanonicalCohomologyContext X).map iso.hom 1 x)

/-- The full absolute dualizing-sheaf package for a proper Cohen--Macaulay curve. -/
structure Chapter09AbsoluteDualizingData
    (k : Type u) [Field k]
    (C : Chapter09CohenMacaulayCurveOverField k)
    [Chapter09ExtTheory C.scheme]
    [Chapter09AbsoluteDerivedHomTheory k C.scheme] where
  sheaf : C.scheme.Modules
  coherent : chapter09Coherent sheaf
  maximalCohenMacaulay : Prop
  trace : chapter09H sheaf 1 → k
  trace_is_image_of_one : Prop
  pairing_is_multiplication_then_trace : Prop
  zeroDimensionalExt :
    ∀ (T : C.scheme.Modules),
      chapter09ZeroDimensional T →
        Nonempty (chapter09Ext T sheaf 1 ≃ chapter09Dual k (chapter09H T 0))
  zeroDimensionalLinearExt :
    ∀ (T : C.scheme.Modules), chapter09ZeroDimensional T →
      ∃ hT : Module k (chapter09H T 0),
        ∃ hExt : Module k (chapter09Ext T sheaf 1),
          @Nonempty
            (letI : Module k (chapter09H T 0) := hT
             letI : Module k (chapter09Ext T sheaf 1) := hExt
             chapter09Ext T sheaf 1 ≃ₗ[k] chapter09LinearDual k (chapter09H T 0))
  perfectPairing :
    ∀ (F : C.scheme.Modules) (i : ℕ),
      chapter09Coherent F → i ≤ 1 →
        Chapter09PerfectPairing k (chapter09H F i) (chapter09Ext F sheaf (1 - i))
  linearPerfectPairing :
    ∀ (F : C.scheme.Modules) (i : ℕ), chapter09Coherent F → i ≤ 1 →
      ∃ hF : Module k (chapter09H F i),
        ∃ hExt : Module k (chapter09Ext F sheaf (1 - i)),
          @Nonempty
            (letI : Module k (chapter09H F i) := hF
             letI : Module k (chapter09Ext F sheaf (1 - i)) := hExt
             Chapter09LinearPerfectPairing k (chapter09H F i)
               (chapter09Ext F sheaf (1 - i)))
  vectorBundlePairing :
    ∀ (E : C.scheme.Modules)
      (V : Chapter09VectorBundleDualTensor E sheaf),
      chapter09VectorBundle E →
        ∀ (i : ℕ), i ≤ 1 →
          Chapter09PerfectPairing k (chapter09H E i)
            (chapter09H V.tensor (1 - i))
  derivedDuality :
    ∀ (F : C.scheme.Modules),
      chapter09Coherent F →
        Chapter09AbsoluteDerivedDualityComparison k F sheaf

/-! ### Projective embeddings and the projective-space calculation -/

/-- A closed immersion of the curve into a chosen projective space over the field. -/
structure Chapter09ProjectiveEmbedding
    (k : Type u) [Field k]
    (C : Chapter09CohenMacaulayCurveOverField k) where
  N : ℕ
  one_le_N : 1 ≤ N
  embedding : C.scheme ⟶
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.chapter02ProjectiveSpace
      (AlgebraicGeometry.Spec (.of k)) N
  closedImmersion : IsClosedImmersion embedding
  over :
    embedding ≫
        LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.chapter02ProjectiveSpaceProjection
          (AlgebraicGeometry.Spec (.of k)) N =
      C.structureMap

abbrev Chapter09ProjectiveEmbedding.ambient
    {k : Type u} [Field k]
    {C : Chapter09CohenMacaulayCurveOverField k}
    (I : Chapter09ProjectiveEmbedding k C) : Scheme.{u} :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.chapter02ProjectiveSpace
    (AlgebraicGeometry.Spec (.of k)) I.N

abbrev Chapter09ProjectiveEmbedding.ambientStructureMap
    {k : Type u} [Field k]
    {C : Chapter09CohenMacaulayCurveOverField k}
    (I : Chapter09ProjectiveEmbedding k C) : I.ambient ⟶ AlgebraicGeometry.Spec (.of k) :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.chapter02ProjectiveSpaceProjection
    (AlgebraicGeometry.Spec (.of k)) I.N

/- LOCAL_DEPENDENCY_GUESS: the pinned revision has no finite-resolution
object for coherent module sheaves on a projective scheme.  The profile keeps
the exactness and pure-codimension obligations explicit for the later proof
pass. -/
structure Chapter09FiniteLocallyFreeResolutionProfile
    {P : Scheme.{u}} (M : P.Modules) where
  length : ℕ
  codimension : ℕ
  finiteLocallyFreeResolution : Prop
  exact : Prop
  pureCodimension : Prop

/-- The sheaf Ext presentation of a dualizing sheaf from a projective embedding. -/
structure Chapter09AbsoluteExtConstruction
    (k : Type u) [Field k]
    (C : Chapter09CohenMacaulayCurveOverField k)
    (I : Chapter09ProjectiveEmbedding k C)
    [Chapter09ExtTheory I.ambient] where
  ambientDualizingSheaf : I.ambient.Modules
  ambientDualizingSheaf_is_dualizing : Prop
  resolution :
    Chapter09FiniteLocallyFreeResolutionProfile
      (chapter09Pushforward I.embedding (chapter09StructureSheaf C.scheme))
  codimension_eq : resolution.codimension = I.N - 1
  extSheaf : I.ambient.Modules
  extSheaf_formula :
    extSheaf =
      chapter09SheafExt
        (chapter09Pushforward I.embedding (chapter09StructureSheaf C.scheme))
        ambientDualizingSheaf (I.N - 1)
  changeOfRingsIdentification : Prop
  dualizingSheaf : C.scheme.Modules
  pushforward_iso : chapter09Pushforward I.embedding dualizingSheaf ≅ extSheaf

/-- The inverse product Laurent monomial appearing in the projective-space Cech pairing. -/
def chapter09InverseProductExponent (N : ℕ) : Fin (N + 1) → ℤ :=
  fun _ => -1

/-- The complementary twist `-m-N-1` in the projective-space pairing. -/
def chapter09ComplementaryTwist (N : ℕ) (m : ℤ) : ℤ :=
  -m - (N : ℤ) - 1

/- LOCAL_DEPENDENCY_GUESS: the pinned revision has no projective-space Cech
complex API over an arbitrary base ring.  The package records its two precise
twists, degrees, coefficient convention, and perfectness interface. -/
structure Chapter09ProjectiveCechPairing
    (k : Type u) [Field k] (N : ℕ) (m : ℤ) (q : ℕ) where
  degree_bound : q ≤ N
  degree_q_term : Type (u + 1)
  complementary_degree_term : Type (u + 1)
  leftTwist : ℤ
  leftTwist_eq : leftTwist = m
  rightTwist : ℤ
  rightTwist_eq : rightTwist = chapter09ComplementaryTwist N m
  leftDegree : ℕ
  leftDegree_eq : leftDegree = q
  rightDegree : ℕ
  rightDegree_eq : rightDegree = N - q
  degree_q_description : Prop
  complementary_degree_description : Prop
  pairing : degree_q_term → complementary_degree_term → k
  coefficient_of_inverse_product : Prop
  perfect :
    Chapter09PerfectPairing k degree_q_term complementary_degree_term

/-! ### Relative curves, base change, and relative duality -/

/-- The proper flat geometrically reduced curve family used for local projectivity. -/
structure Chapter09ProperFlatReducedCurveFamily where
  X : Scheme.{u}
  S : Scheme.{u}
  f : X ⟶ S
  proper : IsProper f
  flat : Flat f
  quasiCompact : QuasiCompact f
  locallyOfFinitePresentation : LocallyOfFinitePresentation f
  relativeCurve :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Chapter09RelativeCurve f
  geometricallyReducedFibers : GeometricallyReduced f

/-- The additional Cohen--Macaulay family hypotheses used by relative duality. -/
structure Chapter09RelativeCurveFamily where
  X : Scheme.{u}
  S : Scheme.{u}
  f : X ⟶ S
  proper : IsProper f
  flat : Flat f
  quasiCompact : QuasiCompact f
  locallyOfFinitePresentation : LocallyOfFinitePresentation f
  relativeCurve :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Chapter09RelativeCurve f
  geometricallyReducedFibers : GeometricallyReduced f
  relativeCohenMacaulay : Prop
  baseLocallyNoetherian : IsLocallyNoetherian S

/-- An fpqc cover used in the local projectivity argument. -/
abbrev Chapter09FpqcCover (S : Scheme.{u}) :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Chapter09FaithfullyFlatCover S

/-- The total space and structure map after a base change `S' → S`. -/
abbrev chapter09BaseChangeTotal {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) : Scheme.{u} :=
  Limits.pullback f g

abbrev chapter09BaseChangeToX {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) : chapter09BaseChangeTotal f g ⟶ X :=
  Limits.pullback.fst f g

abbrev chapter09BaseChangeToBase {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) : chapter09BaseChangeTotal f g ⟶ S' :=
  Limits.pullback.snd f g

/-- The base-changed family map used in the arbitrary-base-change theorem. -/
abbrev chapter09BaseChangedFamilyMap {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) :
    chapter09BaseChangeTotal f g ⟶ S' :=
  chapter09BaseChangeToBase f g

/- LOCAL_DEPENDENCY_GUESS: the preceding book supplies the effective-Cartier
ideal and finite-flat-rank records, but not the associated divisor line bundle
`𝒪(D)`.  The relation to the line bundle is therefore retained explicitly. -/
/-- A relative effective Cartier divisor together with the positivity data used in §9.3. -/
structure Chapter09RelativeEffectiveCartierDivisor
    {X S : Scheme.{u}} (f : X ⟶ S) where
  canonical :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Chapter09EffectiveCartierDivisor X
  degree : ℕ
  finiteFlatRank :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Chapter09FiniteLocallyFreeProfile
      (canonical.ideal.subschemeι ≫ f) degree
  lineBundle : Chapter04LineBundle X
  lineBundle_is_divisor_bundle : Prop
  positiveDegreeOnEveryFiberComponent : Prop
  relativeAmple : chapter04Ample f lineBundle

abbrev Chapter09RelativeEffectiveCartierDivisor.support
    {X S : Scheme.{u}} {f : X ⟶ S}
    (D : Chapter09RelativeEffectiveCartierDivisor f) : Scheme.{u} :=
  D.canonical.ideal.subscheme

abbrev Chapter09RelativeEffectiveCartierDivisor.inclusion
    {X S : Scheme.{u}} {f : X ⟶ S}
    (D : Chapter09RelativeEffectiveCartierDivisor f) : D.support ⟶ X :=
  D.canonical.ideal.subschemeι

abbrev Chapter09RelativeEffectiveCartierDivisor.closedImmersion
    {X S : Scheme.{u}} {f : X ⟶ S}
    (D : Chapter09RelativeEffectiveCartierDivisor f) : IsClosedImmersion D.inclusion :=
  D.canonical.closed

abbrev Chapter09RelativeEffectiveCartierDivisor.finiteOverBase
    {X S : Scheme.{u}} {f : X ⟶ S}
    (D : Chapter09RelativeEffectiveCartierDivisor f) :
    IsFinite (D.inclusion ≫ f) :=
  D.finiteFlatRank.finite

abbrev Chapter09RelativeEffectiveCartierDivisor.flatOverBase
    {X S : Scheme.{u}} {f : X ⟶ S}
    (D : Chapter09RelativeEffectiveCartierDivisor f) :
    Flat (D.inclusion ≫ f) :=
  D.finiteFlatRank.flat

abbrev Chapter09RelativeEffectiveCartierDivisor.constantRank
    {X S : Scheme.{u}} {f : X ⟶ S}
    (D : Chapter09RelativeEffectiveCartierDivisor f) : Prop :=
  ∀ y, Scheme.Hom.finrank (D.inclusion ≫ f) y = D.degree

abbrev Chapter09RelativeEffectiveCartierDivisor.cartier
    {X S : Scheme.{u}} {f : X ⟶ S}
    (D : Chapter09RelativeEffectiveCartierDivisor f) : Prop :=
  D.canonical.locallyRegularPrincipal

abbrev Chapter09RelativeEffectiveCartierDivisor.effective
    {X S : Scheme.{u}} {f : X ⟶ S}
    (D : Chapter09RelativeEffectiveCartierDivisor f) : Prop :=
  D.canonical.locallyRegularPrincipal

/-- Local projectivity data obtained from sections through smooth points. -/
structure Chapter09FpqcLocalProjectivityWitness
    (F : Chapter09ProperFlatReducedCurveFamily) where
  cover : Chapter09FpqcCover F.S
  etaleNeighborhoodAroundGeometricFiber : Prop
  sectionsThroughSmoothPoints : Prop
  divisor :
    Chapter09RelativeEffectiveCartierDivisor
      (chapter09BaseChangedFamilyMap F.f cover.map)
  curvePositivityCriterion : Prop
  affineNonvanishingAfterShrinking : Prop
  relativelyAmple : chapter04Ample
    (chapter09BaseChangedFamilyMap F.f cover.map) divisor.lineBundle
  noRiemannRochUsed : Prop
  projectiveAfterBaseChange :
    chapter04Projective (chapter09BaseChangedFamilyMap F.f cover.map)

/-- A projective morphism after an fpqc base change. -/
def chapter09FpqcLocallyProjective (F : Chapter09ProperFlatReducedCurveFamily) : Prop :=
  Nonempty (Chapter09FpqcLocalProjectivityWitness F)

/- LOCAL_DEPENDENCY_GUESS: the pinned Mathlib API has no relative derived
pushforward/RHom package for module sheaves.  These type families record the
two derived objects occurring in (9.4), while the trace remains an actual
morphism in the module-sheaf category. -/
class Chapter09RelativeDerivedHomTheory {X S : Scheme.{u}} (f : X ⟶ S) where
  directImage : X.Modules → ℕ → S.Modules
  derivedPushforward : X.Modules → ℤ → Type (u + 1)
  baseRHom : Type (u + 1) → S.Modules → ℤ → Type (u + 1)
  relativePushforward : X.Modules → ℤ → Type (u + 1)

abbrev chapter09RPushforward {X S : Scheme.{u}} (f : X ⟶ S)
    [Chapter09RelativeDerivedHomTheory f] (F : X.Modules) (i : ℕ) : S.Modules :=
  Chapter09RelativeDerivedHomTheory.directImage F i

/-- The shifted comparison in relative duality (9.4). -/
structure Chapter09RelativeDualityComparison
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Chapter09RelativeDerivedHomTheory f]
  (E EdualOmega ω : X.Modules) where
  comparison :
    Chapter09RelativeDerivedHomTheory.relativePushforward EdualOmega 1 ≃
      Chapter09RelativeDerivedHomTheory.baseRHom
        (Chapter09RelativeDerivedHomTheory.derivedPushforward E 0)
        (chapter09StructureSheaf S) 0
  quasi_isomorphism : Prop

/-- A vector bundle on `X` together with its `E^∨ ⊗ ω` realization. -/
structure Chapter09RelativeDualizingData
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Chapter09RelativeDerivedHomTheory f] where
  omega : X.Modules
  coherent : chapter09Coherent omega
  relativeMaximalCohenMacaulay : Prop
  trace : chapter09RPushforward f omega 1 ⟶ chapter09StructureSheaf S
  cupProductTraceRealization : Prop
  relativeDuality :
    ∀ (E : X.Modules) (V : Chapter09VectorBundleDualTensor E omega),
      chapter09VectorBundle E →
        Chapter09RelativeDualityComparison f E V.tensor omega

/-- The base-change comparison package for the relative dualizing sheaf, trace, and duality. -/
structure Chapter09RelativeBaseChangeComparison
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [Chapter09RelativeDerivedHomTheory f]
    [Chapter09RelativeDerivedHomTheory (Limits.pullback.snd f g)]
    (D : Chapter09RelativeDualizingData f)
    (D' : Chapter09RelativeDualizingData (Limits.pullback.snd f g)) where
  iso :
    chapter09Pullback (Limits.pullback.fst f g) D.omega ≅ D'.omega
  trace_compatibility : Prop
  duality_compatibility : Prop

/-- Relative dualizing sheaf existence, separated from the family hypotheses. -/
def chapter09HasRelativeDualizingSheaf
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Chapter09RelativeDerivedHomTheory f] : Prop :=
  Nonempty (Chapter09RelativeDualizingData f)

/-! ### Differentials, Gorenstein data, and adjunction -/

/- LOCAL_DEPENDENCY_GUESS: Mathlib's scheme-level Kähler differential module
sheaf is not yet available at the pinned revision. -/
class Chapter09DifferentialSheafTheory {X S : Scheme.{u}} (f : X ⟶ S) where
  omegaOne : X.Modules

abbrev chapter09RelativeDifferentials {X S : Scheme.{u}} (f : X ⟶ S)
    [Chapter09DifferentialSheafTheory f] : X.Modules :=
  Chapter09DifferentialSheafTheory.omegaOne

/-- Gorensteinness of a relative dualizing package in the curve case. -/
def chapter09RelativeGorenstein
    {X S : Scheme.{u}} {f : X ⟶ S}
    [Chapter09RelativeDerivedHomTheory f]
    (D : Chapter09RelativeDualizingData f) : Prop :=
  chapter09IsInvertible D.omega

/-- Gorensteinness of an absolute dualizing package. -/
def chapter09AbsoluteGorenstein
    (k : Type u) [Field k]
    (C : Chapter09CohenMacaulayCurveOverField k)
    [Chapter09ExtTheory C.scheme]
    [Chapter09AbsoluteDerivedHomTheory k C.scheme]
    (D : Chapter09AbsoluteDualizingData k C) : Prop :=
  chapter09IsInvertible D.sheaf

/-- Local complete-intersection data for a relative curve. -/
structure Chapter09RelativeLocalCompleteIntersection
    {X S : Scheme.{u}} (f : X ⟶ S) where
  ambient : Scheme.{u}
  ambientMap : ambient ⟶ S
  ambientSmooth : Smooth ambientMap
  immersion : X ⟶ ambient
  closedImmersion : IsClosedImmersion immersion
  over : immersion ≫ ambientMap = f
  regularSequence : Prop
  pureRelativeDimensionOne : Prop

/-- A relative hypersurface in a smooth relative surface, with its divisor line bundle. -/
structure Chapter09RelativeHypersurface
    {X S : Scheme.{u}} (f : X ⟶ S) where
  ambient : Scheme.{u}
  ambientMap : ambient ⟶ S
  ambientSmoothSurface : SmoothOfRelativeDimension 2 ambientMap
  inclusion : X ⟶ ambient
  closedImmersion : IsClosedImmersion inclusion
  over : inclusion ≫ ambientMap = f
  regularEquation : Prop
  nodalFiber : Prop
  divisorLineBundle : Chapter04LineBundle ambient
  divisorLineBundle_is_OX : Prop

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09
