import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Group.Smooth
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.Topology.Separation.Connected
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08.Dependencies

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry MonObj
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08

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

/- Chapter 9 owns the finite-length and effective-Cartier interfaces used by
Section 9.1. Keeping these records here avoids a dependency on the later
Chapter 10 while retaining the canonical ideal-sheaf and fiber-rank data. -/
abbrev Chapter09ClosedSubscheme (X : Scheme) := X.IdealSheafData

structure Chapter09FiniteLocallyFreeProfile {X Y : Scheme} (q : X ⟶ Y) (d : ℕ) : Prop where
  finite : IsFinite q
  flat : Flat q
  locallyOfFinitePresentation : LocallyOfFinitePresentation q
  rank : ∀ y : Y, Scheme.Hom.finrank q y = d

def Chapter09LocallyRegularPrincipal {X : Scheme}
    (D : Chapter09ClosedSubscheme X) : Prop :=
  ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ a : Γ(X, U),
    D.ideal U = Ideal.span {a} ∧ IsRegular a

structure Chapter09EffectiveCartierDivisor (X : Scheme) where
  ideal : Chapter09ClosedSubscheme X
  locallyRegularPrincipal : Chapter09LocallyRegularPrincipal ideal
  closed : IsClosedImmersion ideal.subschemeι

/- The preceding Chapter 4 interface supplies the canonical pinned-Mathlib
formulation of an invertible module sheaf.  Keep this chapter-facing name as
a thin bridge rather than introducing a second rank-one predicate. -/
def chapter09IsInvertibleSheaf {X : Scheme.{u}} (M : X.Modules) : Prop :=
  chapter04IsInvertible M

structure Chapter09LineBundle (X : Scheme.{u}) where
  module : X.Modules
  isInvertible : chapter09IsInvertibleSheaf module

structure Chapter09LineBundleIso {X : Scheme.{u}}
    (L M : Chapter09LineBundle X) where
  hom : L.module ≅ M.module

def chapter09LineBundleIsomorphic {X : Scheme}
    (L M : Chapter09LineBundle X) : Prop :=
  Nonempty (Chapter09LineBundleIso L M)

def chapter09StructureSheafLineBundle (X : Scheme) : Chapter09LineBundle X :=
  { module := SheafOfModules.unit X.ringCatSheaf
    isInvertible := (chapter04TrivialLineBundle X).isInvertible }

def chapter09AsChapter04LineBundle {X : Scheme} (L : Chapter09LineBundle X) :
    Chapter04LineBundle X :=
  { sheaf := L.module
    isInvertible := L.isInvertible }

/- LOCAL_DEPENDENCY_GUESS: tensor products of sheaves of modules and their
invertibility closure are not packaged in the pinned AlgebraicGeometry API.
The module isomorphism below is essential: the book-facing tensor operation
must be the canonical sheaf tensor, rather than an unrelated operation with
the same notation. -/
class Chapter09LineBundleTensorTheory (X : Scheme) where
  tensor : Chapter09LineBundle X → Chapter09LineBundle X → Chapter09LineBundle X
  unit : Chapter09LineBundle X
  tensor_module_iso : ∀ L M,
    (tensor L M).module ≅ chapter04Tensor L.module M.module
  unit_module_iso : unit.module ≅ SheafOfModules.unit X.ringCatSheaf
  tensor_assoc : ∀ L M N,
    chapter09LineBundleIsomorphic (tensor (tensor L M) N) (tensor L (tensor M N))
  tensor_unit_left : ∀ L, chapter09LineBundleIsomorphic (tensor unit L) L
  tensor_unit_right : ∀ L, chapter09LineBundleIsomorphic (tensor L unit) L
  tensor_comm : ∀ L M, chapter09LineBundleIsomorphic (tensor L M) (tensor M L)

def chapter09Tensor {X : Scheme} [Chapter09LineBundleTensorTheory X]
    (L M : Chapter09LineBundle X) : Chapter09LineBundle X :=
  Chapter09LineBundleTensorTheory.tensor L M

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

def chapter09PullbackLineBundle {X Y : Scheme}
    (f : X ⟶ Y) (L : Chapter09LineBundle Y) : Chapter09LineBundle X :=
  { module := (Scheme.Modules.pullback f).obj L.module
    isInvertible := (chapter04PullbackLineBundle f (chapter09AsChapter04LineBundle L)).isInvertible }

abbrev chapter09GlobalSection {X : Scheme}
    [Chapter09LineBundleTensorTheory X]
    (L : Chapter09LineBundle X) (n : ℕ) :=
  (Scheme.Modules.presheaf (chapter09LineBundlePower L n).module).obj
    (Opposite.op (⊤ : X.Opens))

def chapter09RelativelyAmple {X S : Scheme} (f : X ⟶ S)
    (L : Chapter09LineBundle X) : Prop :=
  chapter04Ample f (chapter09AsChapter04LineBundle L)

def chapter09RelativelyVeryAmple {X S : Scheme} (f : X ⟶ S)
    (L : Chapter09LineBundle X) : Prop :=
  chapter04VeryAmple f (chapter09AsChapter04LineBundle L)

def chapter09RelativelyGenerated {X S : Scheme} (f : X ⟶ S)
    (L : Chapter09LineBundle X) : Prop :=
  chapter04SheafSurjective
    (chapter04EvaluationMap f (chapter09AsChapter04LineBundle L).sheaf)

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

/- The preceding Chapter 4 interface packages the closed immersion.  Its
projective-bundle record does not itself record quasi-compactness, so retain
that finiteness datum in the Chapter 9 projective-morphism witness. -/
structure Chapter09ProjectiveMorphismWitness {X S : Scheme} (f : X ⟶ S) where
  witness : Chapter04ProjectiveWitness f
  quasiCompact : QuasiCompact f

def Chapter09ProjectiveMorphism {X S : Scheme} (f : X ⟶ S) : Prop :=
  Nonempty (Chapter09ProjectiveMorphismWitness f)

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

/- LOCAL_DEPENDENCY_GUESS: Chapter 4 supplies the book-facing cohomology
context; this class only chooses the context for the current scheme. -/
class Chapter09CohomologyTheory (X : Scheme) where
  context : Chapter04CohomologyContext X

def chapter09HOneVanishes {X : Scheme} [Chapter09CohomologyTheory X]
    (M : X.Modules) : Prop :=
  (Chapter09CohomologyTheory.context (X := X)).Vanishes M 1

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

/- LOCAL_DEPENDENCY_GUESS: the rank/base-change theorem identifying the
pushforward with the fiber Hilbert polynomial is not yet canonical here.  Use
the preceding numerical-polynomial object and state only the eventual range in
which H⁰ equals χ. -/
class Chapter09FiberHilbertPolynomialTheory {X S : Scheme} (f : X ⟶ S)
    (L : Chapter09LineBundle X) [Chapter09ModuleRankTheory S]
    [Chapter09LineBundleTensorTheory X] where
  polynomial : S → Chapter08NumericalPolynomial
  rank_eq_pushforward :
    ∀ (s : S), ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (chapter09ModuleRank
          ((Scheme.Modules.pushforward f).obj (chapter09LineBundlePower L n).module) s : ℤ) =
        (polynomial s).value n

def chapter09FiberHilbertPolynomial {X S : Scheme} (f : X ⟶ S)
    (L : Chapter09LineBundle X)
    [Chapter09LineBundleTensorTheory X]
    [Chapter09ModuleRankTheory S]
    [Chapter09FiberHilbertPolynomialTheory f L] : S → Chapter08NumericalPolynomial :=
  Chapter09FiberHilbertPolynomialTheory.polynomial (f := f) (L := L)

structure Chapter09RelativeProjectiveSpace (S : Scheme) (E : S.Modules) where
  bundle : Chapter04ProjectiveBundle S
  coefficientIso : E ≅ bundle.E

abbrev Chapter09RelativeProjectiveSpace.carrier
    {S : Scheme} {E : S.Modules} (P : Chapter09RelativeProjectiveSpace S E) : Scheme :=
  P.bundle.space

abbrev Chapter09RelativeProjectiveSpace.projection
    {S : Scheme} {E : S.Modules} (P : Chapter09RelativeProjectiveSpace S E) :
    P.carrier ⟶ S :=
  P.bundle.projection

structure Chapter09EvaluationWitness {X S : Scheme} (f : X ⟶ S)
    (L : Chapter09LineBundle X) (E : S.Modules) where
  veryAmple : Chapter04VeryAmpleWitness f (chapter09AsChapter04LineBundle L)
  coefficientIso : E ≅ veryAmple.projectiveBundle.E

def Chapter09EvaluationWitness.ambient
    {X S : Scheme} {f : X ⟶ S} {L : Chapter09LineBundle X} {E : S.Modules}
    (W : Chapter09EvaluationWitness f L E) : Chapter09RelativeProjectiveSpace S E :=
  { bundle := W.veryAmple.projectiveBundle
    coefficientIso := W.coefficientIso }

abbrev Chapter09EvaluationWitness.map
    {X S : Scheme} {f : X ⟶ S} {L : Chapter09LineBundle X} {E : S.Modules}
    (W : Chapter09EvaluationWitness f L E) : X ⟶ W.ambient.carrier :=
  W.veryAmple.map

theorem Chapter09EvaluationWitness.over
    {X S : Scheme} {f : X ⟶ S} {L : Chapter09LineBundle X} {E : S.Modules}
    (W : Chapter09EvaluationWitness f L E) : W.map ≫ W.ambient.projection = f :=
  W.veryAmple.over

def chapter09ConstantOnConnectedComponents {S : Scheme} (r : S → ℕ) : Prop :=
  ∀ x y, y ∈ connectedComponent x → r y = r x

structure Chapter09FaithfullyFlatCover (S : Scheme) where
  total : Scheme
  map : total ⟶ S
  flat : Flat map
  quasiCompact : QuasiCompact map
  surjective : Surjective map

/- LOCAL_DEPENDENCY_GUESS: Mathlib has group objects and relative morphism
properties, but not the book-level abelian-scheme package.  The fields below
are the properties used by the chapter: smooth proper geometrically connected
fibres, the identity section, and inversion.  The dual abelian scheme and the
Picard construction are deliberately not made inputs here; the source says
that they belong to later theory. -/
structure Chapter09AbelianScheme (S : Scheme) where
  carrier : Scheme
  structureMap : carrier ⟶ S
  [group : GrpObj (Over.mk structureMap)]
  [commutative : IsCommMonObj (Over.mk structureMap)]
  smooth : Smooth structureMap
  proper : IsProper structureMap
  quasiCompact : QuasiCompact structureMap
  geometricallyConnected : GeometricallyConnected structureMap
  zero : S ⟶ carrier
  zero_fac : zero ≫ structureMap = 𝟙 S
  zero_is_group_unit :
    letI := group
    (Over.homMk zero zero_fac :
      MonoidalCategoryStruct.tensorUnit (Over S) ⟶ Over.mk structureMap) =
      η[Over.mk structureMap]
  negation : Over.mk structureMap ⟶ Over.mk structureMap
  negation_is_inversion :
    letI := group
    negation = (𝟙 (Over.mk structureMap))⁻¹
  negation_is_group_hom : letI := group; letI := commutative; IsMonHom negation

def chapter09AbelianPowerPushforward {S : Scheme}
    (A : Chapter09AbelianScheme S)
    [Chapter09LineBundleTensorTheory A.carrier]
    (L : Chapter09LineBundle A.carrier) (n : ℕ) : S.Modules :=
  (Scheme.Modules.pushforward A.structureMap).obj
    (chapter09LineBundlePower L n).module

def chapter09NegationMap {S : Scheme} (A : Chapter09AbelianScheme S) :
    A.carrier ⟶ A.carrier :=
  A.negation.left

def chapter09Rigidified {S : Scheme} (A : Chapter09AbelianScheme S)
    [Chapter09LineBundleTensorTheory A.carrier]
    (L : Chapter09LineBundle A.carrier) : Prop :=
  chapter09LineBundleIsomorphic
    (chapter09PullbackLineBundle A.zero L)
    (chapter09StructureSheafLineBundle S)

def chapter09Symmetric {S : Scheme} (A : Chapter09AbelianScheme S)
    [Chapter09LineBundleTensorTheory A.carrier]
    (L : Chapter09LineBundle A.carrier) : Prop :=
  chapter09LineBundleIsomorphic
    (chapter09PullbackLineBundle (chapter09NegationMap A) L) L

def chapter09Polarization {S : Scheme} (A : Chapter09AbelianScheme S)
    (L : Chapter09LineBundle A.carrier) : Prop :=
  chapter09RelativelyAmple A.structureMap L

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09
