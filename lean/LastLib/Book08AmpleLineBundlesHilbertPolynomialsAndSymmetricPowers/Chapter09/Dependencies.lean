import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.AlgebraicGeometry.Group.Smooth
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.RingTheory.PicardGroup
import Mathlib.Topology.Separation.Connected

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

/-!
Shared interfaces for Chapter 9.

The preceding chapters of Book 08 are drafted independently.  The pinned
Mathlib tree supplies schemes, sheaves of modules, group objects, and the
standard morphism properties, but it does not yet expose a global invertible-
sheaf, relative Proj-bundle, cohomology, or relative Hilbert-polynomial API.
The interfaces below keep those missing pieces explicit and use canonical
Mathlib objects wherever they are already available.
-/

/- LOCAL_DEPENDENCY_GUESS: Mathlib's `SheafOfModules.IsLocallyFree` has no
global rank-one/invertible-sheaf wrapper yet.  A local generator by one
element on every member of a locally free cover is the book-facing rank-one
formulation used here. -/
def chapter09IsInvertibleSheaf {X : Scheme.{u}} (M : X.Modules) : Prop :=
  ∃ q : M.LocalGeneratorsData.{u}, q.IsLocallyFreeData ∧
    ∀ i : q.I, Nonempty ((q.generators i).I ≃ Unit)

structure Chapter09LineBundle (X : Scheme.{u}) where
  module : X.Modules
  isInvertible : chapter09IsInvertibleSheaf module

structure Chapter09LineBundleIso {X : Scheme.{u}}
    (L M : Chapter09LineBundle X) where
  hom : L.module ≅ M.module

def chapter09LineBundleIsomorphic {X : Scheme}
    (L M : Chapter09LineBundle X) : Prop :=
  Nonempty (Chapter09LineBundleIso L M)

/- LOCAL_DEPENDENCY_GUESS: tensor products of sheaves of modules and their
invertibility closure are not packaged in the pinned AlgebraicGeometry API.
This is the minimal monoidal interface needed for tensor powers and the cube
identities; its laws are stated as isomorphism-valued bridges rather than as
definitional equalities. -/
class Chapter09LineBundleTensorTheory (X : Scheme) where
  tensor : Chapter09LineBundle X → Chapter09LineBundle X → Chapter09LineBundle X
  unit : Chapter09LineBundle X
  dual : Chapter09LineBundle X → Chapter09LineBundle X
  unit_is_structure_sheaf :
    chapter09LineBundleIsomorphic unit
      (by
        exact {
          module := SheafOfModules.unit X.ringCatSheaf
          isInvertible := by sorry })
  tensor_assoc : ∀ L M N,
    chapter09LineBundleIsomorphic (tensor (tensor L M) N) (tensor L (tensor M N))
  tensor_unit_left : ∀ L, chapter09LineBundleIsomorphic (tensor unit L) L
  tensor_unit_right : ∀ L, chapter09LineBundleIsomorphic (tensor L unit) L
  tensor_comm : ∀ L M, chapter09LineBundleIsomorphic (tensor L M) (tensor M L)

def chapter09StructureSheafLineBundle (X : Scheme) : Chapter09LineBundle X :=
  { module := SheafOfModules.unit X.ringCatSheaf
    isInvertible := by sorry }

def chapter09Tensor {X : Scheme} [Chapter09LineBundleTensorTheory X]
    (L M : Chapter09LineBundle X) : Chapter09LineBundle X :=
  Chapter09LineBundleTensorTheory.tensor L M

def chapter09Dual {X : Scheme} [Chapter09LineBundleTensorTheory X]
    (L : Chapter09LineBundle X) : Chapter09LineBundle X :=
  Chapter09LineBundleTensorTheory.dual L

def chapter09LineBundlePower {X : Scheme} [Chapter09LineBundleTensorTheory X]
    (L : Chapter09LineBundle X) : ℕ → Chapter09LineBundle X
  | 0 => Chapter09LineBundleTensorTheory.unit (X := X)
  | n + 1 => chapter09Tensor (chapter09LineBundlePower L n) L

@[simp]
theorem chapter09LineBundlePower_zero {X : Scheme}
    [Chapter09LineBundleTensorTheory X] (L : Chapter09LineBundle X) :
    chapter09LineBundlePower L 0 = Chapter09LineBundleTensorTheory.unit (X := X) :=
  rfl

@[simp]
theorem chapter09LineBundlePower_succ {X : Scheme}
    [Chapter09LineBundleTensorTheory X] (L : Chapter09LineBundle X) (n : ℕ) :
    chapter09LineBundlePower L (n + 1) = chapter09Tensor (chapter09LineBundlePower L n) L :=
  rfl

/- Integer powers are needed for the multiplication-by-`m` formula.  Negative
  powers use the dual supplied by the tensor interface. -/
def chapter09LineBundleIntPower {X : Scheme}
    [Chapter09LineBundleTensorTheory X] (L : Chapter09LineBundle X) : ℤ → Chapter09LineBundle X
  | Int.ofNat n => chapter09LineBundlePower L n
  | Int.negSucc n => chapter09LineBundlePower (chapter09Dual L) (n + 1)

@[simp]
theorem chapter09LineBundleIntPower_ofNat {X : Scheme}
    [Chapter09LineBundleTensorTheory X] (L : Chapter09LineBundle X) (n : ℕ) :
    chapter09LineBundleIntPower L (Int.ofNat n) = chapter09LineBundlePower L n :=
  rfl

@[simp]
theorem chapter09LineBundleIntPower_negSucc {X : Scheme}
    [Chapter09LineBundleTensorTheory X] (L : Chapter09LineBundle X) (n : ℕ) :
    chapter09LineBundleIntPower L (Int.negSucc n) =
      chapter09LineBundlePower (chapter09Dual L) (n + 1) :=
  rfl

def chapter09PullbackLineBundle {X Y : Scheme}
    [Chapter09LineBundleTensorTheory X] [Chapter09LineBundleTensorTheory Y]
    (f : X ⟶ Y) (L : Chapter09LineBundle Y) : Chapter09LineBundle X :=
  { module := (Scheme.Modules.pullback f).obj L.module
    isInvertible := by sorry }

abbrev chapter09GlobalSection {X : Scheme}
    [Chapter09LineBundleTensorTheory X]
    (L : Chapter09LineBundle X) (n : ℕ) :=
  (Scheme.Modules.presheaf (chapter09LineBundlePower L n).module).obj
    (Opposite.op (⊤ : X.Opens))

/- LOCAL_DEPENDENCY_GUESS: the affine-open definition, evaluation maps, and
relative very-ampleness equivalence from Sections 1--5 of the book are not
available in the current tree.  These predicates are deliberately kept as a
book-facing interface and do not contain any later Chapter 9 conclusion. -/
class Chapter09RelativePositivityTheory {X S : Scheme} (f : X ⟶ S) where
  ample : Chapter09LineBundle X → Prop
  veryAmple : Chapter09LineBundle X → Prop
  generated : Chapter09LineBundle X → Prop

def chapter09RelativelyAmple {X S : Scheme} (f : X ⟶ S)
    [Chapter09RelativePositivityTheory f] (L : Chapter09LineBundle X) : Prop :=
  Chapter09RelativePositivityTheory.ample (f := f) L

def chapter09RelativelyVeryAmple {X S : Scheme} (f : X ⟶ S)
    [Chapter09RelativePositivityTheory f] (L : Chapter09LineBundle X) : Prop :=
  Chapter09RelativePositivityTheory.veryAmple (f := f) L

def chapter09RelativelyGenerated {X S : Scheme} (f : X ⟶ S)
    [Chapter09RelativePositivityTheory f] (L : Chapter09LineBundle X) : Prop :=
  Chapter09RelativePositivityTheory.generated (f := f) L

/- LOCAL_DEPENDENCY_GUESS: a relative curve predicate is not yet present in
pinned Mathlib.  It is kept separate from smoothness, flatness, and properness
so those hypotheses remain visible in every theorem that uses them. -/
structure Chapter09RelativeCurveData {X S : Scheme} (f : X ⟶ S) where
  fibers_are_curves : Prop

def Chapter09RelativeCurve {X S : Scheme} (f : X ⟶ S) : Prop :=
  Nonempty (Chapter09RelativeCurveData f)

def Chapter09RelativeCurve.fibers_are_curves {X S : Scheme} {f : X ⟶ S}
    (h : Chapter09RelativeCurve f) : Prop :=
  (Classical.choice h).fibers_are_curves

/- LOCAL_DEPENDENCY_GUESS: relative projectivity is represented here by the
factorization property supplied by the earlier Projective-morphism chapter. -/
structure Chapter09ProjectiveMorphismWitness {X S : Scheme} (f : X ⟶ S) where
  ambient : Scheme
  ambientToBase : ambient ⟶ S
  embedding : X ⟶ ambient
  embedding_closed : IsClosedImmersion embedding
  overBase : embedding ≫ ambientToBase = f
  projective_factorization : Prop

def Chapter09ProjectiveMorphism {X S : Scheme} (f : X ⟶ S) : Prop :=
  Nonempty (Chapter09ProjectiveMorphismWitness f)

def Chapter09ProjectiveMorphism.projective_factorization
    {X S : Scheme} {f : X ⟶ S} (h : Chapter09ProjectiveMorphism f) : Prop :=
  (Classical.choice h).projective_factorization

/- LOCAL_DEPENDENCY_GUESS: the pinned sheaf API exposes local freeness but not
the rank function and its compatibility with connected components.  The
compatibility field is the reusable bridge used by the family dimension result. -/
class Chapter09ModuleRankTheory (S : Scheme) where
  rank : S.Modules → S → ℕ
  locallyFree_rank_constant :
    ∀ (E : S.Modules), E.IsLocallyFree →
      ∀ x y, y ∈ connectedComponent x → rank E y = rank E x

def chapter09ModuleRank {S : Scheme} [Chapter09ModuleRankTheory S]
    (E : S.Modules) : S → ℕ :=
  Chapter09ModuleRankTheory.rank E

/- LOCAL_DEPENDENCY_GUESS: this is the missing coherent-cohomology interface;
the field is a vanishing predicate, not an assumed vanishing theorem. -/
class Chapter09CohomologyTheory (X : Scheme) where
  hOneVanishes : X.Modules → Prop

def chapter09HOneVanishes {X : Scheme} [Chapter09CohomologyTheory X]
    (M : X.Modules) : Prop :=
  Chapter09CohomologyTheory.hOneVanishes M

/- The base-change predicate is written directly with the canonical pullback
and pushforward functors.  It is intentionally a property of a module rather
than a typeclass carrying the desired family conclusion. -/
def chapter09PushforwardCommutesWithBaseChange {X S : Scheme}
    (f : X ⟶ S) (M : X.Modules) : Prop :=
  ∀ (T : Scheme) (g : T ⟶ S),
    Nonempty
      (((Scheme.Modules.pushforward (pullback.snd f g)).obj
          ((Scheme.Modules.pullback (pullback.fst f g)).obj M)) ≅
        ((Scheme.Modules.pullback g).obj
          ((Scheme.Modules.pushforward f).obj M)))

/- LOCAL_DEPENDENCY_GUESS: this class records the missing theorem identifying
fiber Hilbert-polynomial values with ranks of pushforwards of twists. -/
class Chapter09FiberHilbertPolynomialTheory {X S : Scheme} (f : X ⟶ S)
    (L : Chapter09LineBundle X) [Chapter09ModuleRankTheory S]
    [Chapter09LineBundleTensorTheory X] where
  polynomial : S → ℕ → ℕ
  rank_eq_pushforward :
    ∀ (s : S) (n : ℕ),
      chapter09ModuleRank
          ((Scheme.Modules.pushforward f).obj (chapter09LineBundlePower L n).module) s =
        polynomial s n

def chapter09FiberHilbertPolynomial {X S : Scheme} (f : X ⟶ S)
    (L : Chapter09LineBundle X)
    [Chapter09LineBundleTensorTheory X]
    [Chapter09ModuleRankTheory S]
    [Chapter09FiberHilbertPolynomialTheory f L] : S → ℕ → ℕ :=
  Chapter09FiberHilbertPolynomialTheory.polynomial (f := f) (L := L)

structure Chapter09RelativeProjectiveSpace (S : Scheme) (E : S.Modules) where
  carrier : Scheme
  projection : carrier ⟶ S
  projective : Chapter09ProjectiveMorphism projection

structure Chapter09EvaluationWitness {X S : Scheme} (f : X ⟶ S)
    (E : S.Modules) where
  ambient : Chapter09RelativeProjectiveSpace S E
  map : X ⟶ ambient.carrier
  isEvaluationMap : Prop

def chapter09ConstantOnConnectedComponents {S : Scheme} (r : S → ℕ) : Prop :=
  ∀ x y, y ∈ connectedComponent x → r y = r x

structure Chapter09FaithfullyFlatCover (S : Scheme) where
  total : Scheme
  map : total ⟶ S
  flat : Flat map
  surjective : Surjective map

/- LOCAL_DEPENDENCY_GUESS: Mathlib has group objects and relative morphism
properties, but not the book-level dual abelian scheme, scalar maps, or
geometric-connected-fiber package. -/
structure Chapter09AbelianScheme (S : Scheme) where
  carrier : Scheme
  structureMap : carrier ⟶ S
  [group : GrpObj (Over.mk structureMap)]
  [commutative : IsCommMonObj (Over.mk structureMap)]
  smooth : Smooth structureMap
  proper : IsProper structureMap
  geometricallyConnected : GeometricallyConnected structureMap
  dual : Scheme
  dualStructureMap : dual ⟶ S
  [dualGroup : GrpObj (Over.mk dualStructureMap)]
  [dualCommutative : IsCommMonObj (Over.mk dualStructureMap)]
  dual_represents_dual : Prop
  zero : S ⟶ carrier
  zero_fac : zero ≫ structureMap = 𝟙 S
  scalar : ℤ → (Over.mk structureMap ⟶ Over.mk structureMap)
  scalar_is_group_hom : ∀ m, IsMonHom (scalar m)

def chapter09ScalarMap {S : Scheme} (A : Chapter09AbelianScheme S) (m : ℤ) :
    A.carrier ⟶ A.carrier :=
  (A.scalar m).left

def chapter09NegationMap {S : Scheme} (A : Chapter09AbelianScheme S) :
    A.carrier ⟶ A.carrier :=
  chapter09ScalarMap A (-1)

def chapter09Rigidified {S : Scheme} (A : Chapter09AbelianScheme S)
    [Chapter09LineBundleTensorTheory A.carrier]
    [Chapter09LineBundleTensorTheory S]
    (L : Chapter09LineBundle A.carrier) : Prop :=
  chapter09LineBundleIsomorphic
    (chapter09PullbackLineBundle A.zero L)
    (chapter09StructureSheafLineBundle S)

def chapter09Symmetric {S : Scheme} (A : Chapter09AbelianScheme S)
    [Chapter09LineBundleTensorTheory A.carrier]
    [Chapter09LineBundleTensorTheory S]
    (L : Chapter09LineBundle A.carrier) : Prop :=
  chapter09LineBundleIsomorphic
    (chapter09PullbackLineBundle (chapter09NegationMap A) L) L

structure Chapter09AbelianMorphism {S : Scheme}
    (A : Chapter09AbelianScheme S) where
  hom : Over.mk A.structureMap ⟶ Over.mk A.dualStructureMap
  isGroupHom : letI := A.group; letI := A.dualGroup; IsMonHom hom

def chapter09AbelianMorphismMap {S : Scheme}
    {A : Chapter09AbelianScheme S} (φ : Chapter09AbelianMorphism A) :
    A.carrier ⟶ A.dual :=
  φ.hom.left

/- LOCAL_DEPENDENCY_GUESS: the translation/pullback/tensor construction of
the Picard-difference map `λ_L` is not exposed by the pinned Picard API. -/
class Chapter09PolarizationMapTheory {S : Scheme} (A : Chapter09AbelianScheme S) where
  lambda : Chapter09LineBundle A.carrier → Chapter09AbelianMorphism A

def chapter09Lambda {S : Scheme} (A : Chapter09AbelianScheme S)
    [Chapter09PolarizationMapTheory A]
    (L : Chapter09LineBundle A.carrier) : Chapter09AbelianMorphism A :=
  Chapter09PolarizationMapTheory.lambda (A := A) L

def chapter09FiniteSurjective {X Y : Scheme} (f : X ⟶ Y) : Prop :=
  IsFinite f ∧ Surjective f

theorem chapter09FiniteSurjective_iff {X Y : Scheme} (f : X ⟶ Y) :
    chapter09FiniteSurjective f ↔ IsFinite f ∧ Surjective f :=
  Iff.rfl

def chapter09AbelianMorphismIsGroupHom {S : Scheme}
    {A : Chapter09AbelianScheme S} (φ : Chapter09AbelianMorphism A) : Prop :=
  letI := A.group
  letI := A.dualGroup
  IsMonHom φ.hom

def chapter09PolarizationMapProperty {S : Scheme} (A : Chapter09AbelianScheme S)
    (φ : Chapter09AbelianMorphism A) : Prop :=
  chapter09AbelianMorphismIsGroupHom φ ∧
    chapter09FiniteSurjective (chapter09AbelianMorphismMap φ)

def chapter09Polarization {S : Scheme} (A : Chapter09AbelianScheme S)
    [Chapter09LineBundleTensorTheory A.carrier]
    [Chapter09LineBundleTensorTheory S]
    [Chapter09RelativePositivityTheory A.structureMap]
    [Chapter09PolarizationMapTheory A]
    (L : Chapter09LineBundle A.carrier) : Prop :=
  chapter09RelativelyAmple A.structureMap L ∧
    chapter09PolarizationMapProperty A (chapter09Lambda A L)

structure Chapter09PolarizationLocalWitness {S : Scheme}
    (A : Chapter09AbelianScheme S) (φ : Chapter09AbelianMorphism A) where
  cover : Chapter09FaithfullyFlatCover S
  baseChangedAbelianScheme : Chapter09AbelianScheme cover.total
  isBaseChange : Prop
  bundle : Chapter09LineBundle baseChangedAbelianScheme.carrier
  rigidified : Prop
  relativelyAmple : Prop
  realizes : Prop

def chapter09PolarizationLocallyInduced {S : Scheme}
    (A : Chapter09AbelianScheme S) (φ : Chapter09AbelianMorphism A) : Prop :=
  Nonempty (Chapter09PolarizationLocalWitness A φ)

/- LOCAL_DEPENDENCY_GUESS: the pinned scheme API has products and pullbacks but
does not yet package the relative triple product, its seven partial-sum maps,
or the associated tensor product of pullbacks as a cubical line bundle. -/
structure Chapter09CubeTrivialization {S : Scheme}
    (A : Chapter09AbelianScheme S)
    [Chapter09LineBundleTensorTheory A.carrier]
    (L : Chapter09LineBundle A.carrier) where
  cube : Scheme
  cubeIsTripleProduct : Prop
  coordinateProjection : Fin 3 → cube ⟶ A.carrier
  partialSumMap : Fin 7 → cube ⟶ A.carrier
  alternatingProduct : Chapter09LineBundle cube
  alternatingProductIsPartialSumProduct : Prop
  canonicalTrivialization :
    Chapter09LineBundleIso alternatingProduct (chapter09StructureSheafLineBundle cube)
  rigidifiedOnCoordinateHyperplanes : Prop

def chapter09TheoremOfCubeStatement {S : Scheme}
    (A : Chapter09AbelianScheme S)
    [Chapter09LineBundleTensorTheory A.carrier]
    (L : Chapter09LineBundle A.carrier) : Prop :=
  Nonempty (Chapter09CubeTrivialization A L)

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09
