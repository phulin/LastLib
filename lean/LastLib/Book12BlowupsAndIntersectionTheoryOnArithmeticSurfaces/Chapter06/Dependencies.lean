import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
Shared interfaces for Chapter 6.

The pinned Mathlib snapshot supplies schemes, scheme-theoretic fibers, the standard
morphism properties, DVRs, and regular-local-ring predicates.  It does not yet
package the book's regular arithmetic surfaces, surface regularity, Cartier
divisors, blowups, or intersection numbers.  The records below keep those
interfaces explicit and use the canonical Mathlib objects whenever there is a
canonical object to attach them to.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter06

/-! The local thickness equation is shared by the resolution and base-change
interfaces in this chapter. -/

def chapter06ThicknessEquation {R : Type u} [CommRing R]
    (x y π : R) (n : ℕ) : Prop :=
  x * y = π ^ n

/-! ### Bases, models, and regularity profiles -/

/- LOCAL_DEPENDENCY_GUESS: excellence and the scheme-level Dedekind predicate
are not packaged together in the pinned scheme API.  They are kept as
book-facing propositions, while the carrier remains a canonical scheme. -/
structure Chapter06ExcellentDedekindBase (S : Scheme.{u}) where
  excellent : Prop
  excellentEvidence : excellent
  connected : Prop
  connectedEvidence : connected
  dedekind : Prop
  dedekindEvidence : dedekind

/- LOCAL_DEPENDENCY_GUESS: the pinned snapshot has `IsIntegral` and
`IsLocallyNoetherian`, but not the regularity predicate for an arbitrary
scheme in the form used by the resolution theorem. -/
structure Chapter06NormalExcellentSurface (X : Scheme.{u}) where
  integral : IsIntegral X
  locallyNoetherian : IsLocallyNoetherian X
  normalAt : X → Prop
  normalAt_iff : ∀ x, normalAt x ↔ IsIntegrallyClosed (X.presheaf.stalk x)
  everywhereNormal : ∀ x, normalAt x
  excellent : Prop
  excellentEvidence : excellent
  dimensionTwo : Prop
  dimensionTwoEvidence : dimensionTwo
  regularAt : X → Prop
  regularAt_iff : ∀ x, regularAt x ↔ IsRegularLocalRing (X.presheaf.stalk x)

structure Chapter06RegularSurface (X : Scheme.{u}) where
  integral : IsIntegral X
  locallyNoetherian : IsLocallyNoetherian X
  dimensionTwo : Prop
  dimensionTwoEvidence : dimensionTwo
  regularAt : X → Prop
  regularAt_iff : ∀ x, regularAt x ↔ IsRegularLocalRing (X.presheaf.stalk x)
  everywhereRegular : ∀ x, regularAt x

def chapter06SingularLocus {X : Scheme.{u}}
    (hX : Chapter06NormalExcellentSurface X) : Set X :=
  {x | ¬ hX.regularAt x}

theorem chapter06_mem_singularLocus_iff {X : Scheme.{u}}
    (hX : Chapter06NormalExcellentSurface X) (x : X) :
    x ∈ chapter06SingularLocus hX ↔ ¬ hX.regularAt x := by
  rfl

structure Chapter06ArithmeticSurface {S X : Scheme.{u}} (f : X ⟶ S) where
  base : Chapter06ExcellentDedekindBase S
  integral : IsIntegral X
  locallyNoetherian : IsLocallyNoetherian X
  proper : IsProper f
  flat : Flat f
  relativeDimensionOne : Prop
  relativeDimensionOneEvidence : relativeDimensionOne
  regular : Chapter06RegularSurface X
  genericFiberSmooth : Prop
  genericFiberSmoothEvidence : genericFiberSmooth
  genericFiberGeometricallyConnected : Prop
  genericFiberGeometricallyConnectedEvidence : genericFiberGeometricallyConnected

/-! A model retains an explicit generic fiber so that generic-curve comparison
does not silently identify a surface with its generic fiber. -/
structure Chapter06RelativeSurfaceModel (S : Scheme.{u}) where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ S
  genericFiber : Scheme.{u}
  genericFiberToCarrier : genericFiber ⟶ carrier
  genericFiberIdentification : Prop
  genericFiberIdentificationEvidence : genericFiberIdentification
  genericFiberSmooth : Prop
  genericFiberSmoothEvidence : genericFiberSmooth
  genericFiberGeometricallyConnected : Prop
  genericFiberGeometricallyConnectedEvidence : genericFiberGeometricallyConnected

def Chapter06SameGenericCurve {S : Scheme.{u}}
    (X Y : Chapter06RelativeSurfaceModel S) : Prop :=
  Nonempty (Y.genericFiber ≅ X.genericFiber)

/-! ### Modifications and resolution -/

/- LOCAL_DEPENDENCY_GUESS: relative projectivity, birationality, and support of
a blowup are not bundled by the pinned Mathlib scheme API.  This record keeps
the geometric meaning of a supported projective modification visible. -/
structure Chapter06ProjectiveModification {X Y : Scheme.{u}} where
  map : Y ⟶ X
  projective : Prop
  projectiveEvidence : projective
  birational : Prop
  birationalEvidence : birational
  center : Set X
  isomorphismAwayFromCenter : Prop
  isomorphismAwayFromCenterEvidence : isomorphismAwayFromCenter

structure Chapter06VerticalModification
    {S : Scheme.{u}} (X Y : Chapter06RelativeSurfaceModel S) where
  map : Y.carrier ⟶ X.carrier
  overBase : map ≫ X.structureMap = Y.structureMap
  projective : Prop
  projectiveEvidence : projective
  birational : Prop
  birationalEvidence : birational
  center : Set X.carrier
  centerVertical : Prop
  centerVerticalEvidence : centerVertical
  isomorphismAwayFromCenter : Prop
  isomorphismAwayFromCenterEvidence : isomorphismAwayFromCenter
  genericFiberPreserved : Chapter06SameGenericCurve X Y

structure Chapter06SurfaceResolution {X : Scheme.{u}}
    (hX : Chapter06NormalExcellentSurface X) where
  resolved : Scheme.{u}
  map : resolved ⟶ X
  modification : Chapter06ProjectiveModification (X := X) (Y := resolved)
  modificationMap : modification.map = map
  projective : Prop
  projectiveEvidence : projective
  birational : Prop
  birationalEvidence : birational
  center : Set X
  centerSubsetSingular : center ⊆ chapter06SingularLocus hX
  isomorphismAwayFromCenter : Prop
  isomorphismAwayFromCenterEvidence : isomorphismAwayFromCenter
  targetIntegral : IsIntegral resolved
  targetLocallyNoetherian : IsLocallyNoetherian resolved
  targetDimensionTwo : Prop
  targetDimensionTwoEvidence : targetDimensionTwo
  targetRegular : Chapter06RegularSurface resolved

inductive Chapter06ResolutionPurpose : Type
  | surfaceSingularities
  | embeddedBoundary

def Chapter06SurfaceResolutionTask {X : Scheme.{u}}
    (hX : Chapter06NormalExcellentSurface X) : Prop :=
  Nonempty (Chapter06SurfaceResolution hX)

/-! ### The numerical local data which a resolution step transports -/

structure Chapter06LocalStepInvariants where
  equationMultiplicity : ℕ
  branchCount : ℕ
  tangentDirectionCount : ℕ
  fiberComponentMultiplicity : ℕ

def Chapter06LocalStepNeedsNewCenter (d : Chapter06LocalStepInvariants) : Prop :=
  d.equationMultiplicity > 1 ∨ d.branchCount > 2 ∨
    (d.branchCount = 2 ∧ d.tangentDirectionCount = 1)

structure Chapter06FiberComponent where
  multiplicity : ℕ
  multiplicityPositive : 0 < multiplicity
  integral : Prop
  integralEvidence : integral

structure Chapter06CenterFiberData where
  components : List Chapter06FiberComponent
  throughCenter : Chapter06FiberComponent → Bool
  localOrder : Chapter06FiberComponent → ℕ
  localOrderPositiveOnThroughCenter :
    ∀ C, C ∈ components → throughCenter C = true → 0 < localOrder C

def chapter06FiberMultiplicitySum (d : Chapter06CenterFiberData) : ℕ :=
  (d.components.filter d.throughCenter).foldl
    (fun acc C => acc + C.multiplicity * d.localOrder C) 0

def chapter06ExceptionalFiberMultiplicity (d : Chapter06CenterFiberData) : ℕ :=
  chapter06FiberMultiplicitySum d

theorem chapter06_exceptional_fiber_multiplicity_eq_sum
    (d : Chapter06CenterFiberData) :
    chapter06ExceptionalFiberMultiplicity d = chapter06FiberMultiplicitySum d := by
  rfl

/-! ### Formal divisors and the total-transform interface -/

/- LOCAL_DEPENDENCY_GUESS: a Cartier-divisor group and its scheme-level
pullback are supplied by the surrounding Book 12 chapters, but are not yet
available in this isolated snapshot.  The support/coefficient record is the
smallest interface needed by the total-fiber identity in this chapter. -/
structure Chapter06FormalDivisor (X : Scheme.{u}) where
  terms : Type u
  support : terms → Set X
  coefficient : terms → ℤ

def chapter06PullbackFormalDivisor {X Y : Scheme.{u}}
    (b : Y ⟶ X) (D : Chapter06FormalDivisor X) : Chapter06FormalDivisor Y :=
  { terms := D.terms
    support := fun i => b ⁻¹' D.support i
    coefficient := D.coefficient }

structure Chapter06UniformizerFiberTransform {X Y : Scheme.{u}} (b : Y ⟶ X) where
  uniformizer : Type u
  fiberOnX : Chapter06FormalDivisor X
  fiberOnY : Chapter06FormalDivisor Y
  fiberIsPrincipalUniformizer : Prop
  fiberIsPrincipalUniformizerEvidence : fiberIsPrincipalUniformizer
  fiberOnYIsTotalPullback :
    fiberOnY = chapter06PullbackFormalDivisor b fiberOnX

/-! ### Curves and numerical intersection data -/

/- LOCAL_DEPENDENCY_GUESS: the global Cartier--Weil dictionary and the
intersection pairing are deliberately deferred to later Book 12 chapters.
This record is a neutral carrier for the numerical facts already used in
Chapter 6, without pretending that an arbitrary integer is a canonical degree. -/
structure Chapter06CurveNumericalData where
  smooth : Prop
  smoothEvidence : smooth
  rational : Prop
  rationalEvidence : rational
  vertical : Prop
  verticalEvidence : vertical
  selfIntersection : ℤ
  normalDegree : ℤ

structure Chapter06CurveOnSurface (X : Scheme.{u}) where
  carrier : Scheme.{u}
  inclusion : carrier ⟶ X
  integral : Prop
  integralEvidence : integral
  codimensionOne : Prop
  codimensionOneEvidence : codimensionOne
  numerical : Chapter06CurveNumericalData

def Chapter06IntersectionMatrix (ι : Type u) := Matrix ι ι ℤ

def chapter06NegativeChainMatrix (r : ℕ) :
    Chapter06IntersectionMatrix (Fin r) := fun i j =>
  if i = j then -2
  else if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1
  else 0

theorem chapter06_negativeChainMatrix_diagonal (r : ℕ) (i : Fin r) :
    chapter06NegativeChainMatrix r i i = -2 := by
  simp [chapter06NegativeChainMatrix]

theorem chapter06_negativeChainMatrix_adjacent (r : ℕ)
    (i j : Fin r) (hij : i.val + 1 = j.val) :
    chapter06NegativeChainMatrix r i j = 1 := by sorry

theorem chapter06_negativeChainMatrix_nonadjacent (r : ℕ)
    (i j : Fin r) (hne : i ≠ j)
    (hleft : i.val + 1 ≠ j.val) (hright : j.val + 1 ≠ i.val) :
    chapter06NegativeChainMatrix r i j = 0 := by
  simp [chapter06NegativeChainMatrix, hne, hleft, hright]

structure Chapter06FiberProfile where
  components : List Chapter06FiberComponent
  connected : Prop
  connectedEvidence : connected
  nodal : Prop
  nodalEvidence : nodal

def chapter06FiberReduced (F : Chapter06FiberProfile) : Prop :=
  ∀ C, C ∈ F.components → C.multiplicity = 1

def chapter06SemistableFiber (F : Chapter06FiberProfile) : Prop :=
  chapter06FiberReduced F ∧ F.nodal

structure Chapter06NormalCrossingBoundary (X : Scheme.{u}) where
  support : Set X
  smoothBranches : Prop
  smoothBranchesEvidence : smoothBranches
  atMostTwoBranches : Prop
  atMostTwoBranchesEvidence : atMostTwoBranches
  transverseBranches : Prop
  transverseBranchesEvidence : transverseBranches

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter06

end
