import Mathlib.Algebra.FreeAbelianGroup.Finsupp
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ResidueField

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter11

noncomputable section

classical

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

universe u v

/-!
Shared interfaces for Chapter 11.

The preceding chapters of Book 12 are directory placeholders in this snapshot,
and the pinned Mathlib tree does not contain a surface-intersection or point-
blowup package.  The records below therefore keep the canonical scheme maps,
residue degrees, free abelian divisor group, and morphism directions visible
while marking the genuinely missing geometric packages as local dependency
interfaces.  They are intentionally independent of the later chapters of the
book.
-/

/-! ### Arithmetic surfaces and closed points -/

/-- The excellent connected Dedekind base occurring in the definition of an
arithmetic surface.  The three geometric properties are retained as explicit
fields because the pinned scheme API has no single bundled arithmetic-base
structure. -/
structure Chapter11ArithmeticBase where
  carrier : Scheme.{u}
  excellent : Prop
  connected : Prop
  dedekind : Prop

/-- A regular arithmetic surface over an excellent Dedekind base.

The generic-fiber hypotheses are part of the standing convention for an
arithmetic surface, even though the point-blowup identities below only use
the regular-surface and proper-fiber consequences. -/
structure Chapter11ArithmeticSurface (S : Chapter11ArithmeticBase) where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ S.carrier
  integral : Prop
  regular : Prop
  proper : IsProper structureMap
  flat : Flat structureMap
  relativeDimensionOne : Prop
  genericFiberSmooth : Prop
  genericFiberGeometricallyConnected : Prop

/-- A closed point of a surface together with the closed point of the base
over which it lies.  The equality is the scheme-theoretic meaning of
`x ∈ X_s` used in this chapter. -/
structure Chapter11SurfacePoint {S : Chapter11ArithmeticBase}
    (X : Chapter11ArithmeticSurface S) where
  point : X.carrier
  basePoint : S.carrier
  point_closed : IsClosed ({point} : Set X.carrier)
  basePoint_closed : IsClosed ({basePoint} : Set S.carrier)
  lies_over : X.structureMap point = basePoint

/-- The residue degree of a surface point over its base point.

This is the canonical Mathlib `Scheme.Hom.residueDegree`, which installs the
algebra structure from the residue-field map and computes the finite
dimensional degree, returning zero in the infinite case. -/
noncomputable def chapter11ResidueDegree
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    (p : Chapter11SurfacePoint X) : ℕ :=
  X.structureMap.residueDegree p.point

abbrev chapter11PointDegree
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    (p : Chapter11SurfacePoint X) : ℕ :=
  chapter11ResidueDegree p

/-- The same canonical residue-degree operation for a general morphism of
schemes; it is used for points on an exceptional curve above a center. -/
noncomputable def chapter11ResidueDegreeOfMap
    {Y X : Scheme.{u}} (f : Y ⟶ X) (y : Y) : ℕ :=
  f.residueDegree y

/-! ### Curves and divisors -/

/- LOCAL_DEPENDENCY_GUESS: the preceding surface chapters supply the
codimension-one Cartier/Weil dictionary and the order of a Cartier equation at
a closed point, but those interfaces are not present in this checkout.  The
fields below are the minimal book-facing replacement; the residue-degree and
divisor-group operations remain canonical. -/

/-- An integral codimension-one Cartier curve on a regular arithmetic surface.

`multiplicity` is the order of a local Cartier equation at a closed point.  The
zero-off-the-curve and smooth-point-one laws are recorded here because they are
used by the strict-transform and proximity formulas. -/
structure Chapter11CartierCurve {S : Chapter11ArithmeticBase}
    (X : Chapter11ArithmeticSurface S) where
  carrier : Scheme.{u}
  inclusion : carrier ⟶ X.carrier
  closed : IsClosedImmersion inclusion
  integral : Prop
  codimensionOne : Prop
  cartier : Prop
  vertical : Prop
  horizontal : Prop
  vertical_or_horizontal : vertical ∨ horizontal
  multiplicity : Chapter11SurfacePoint X → ℕ
  smoothAt : Chapter11SurfacePoint X → Prop
  multiplicity_zero_of_not_mem :
    ∀ p, (¬ ∃ z : carrier, inclusion z = p.point) → multiplicity p = 0
  multiplicity_one_of_smoothAt :
    ∀ p, (∃ z : carrier, inclusion z = p.point) → smoothAt p → multiplicity p = 1

/-- Scheme-theoretic membership of a closed surface point in a Cartier curve. -/
def chapter11PointLiesOnCurve
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    (D : Chapter11CartierCurve X) (p : Chapter11SurfacePoint X) : Prop :=
  ∃ z : D.carrier, D.inclusion z = p.point

theorem chapter11_point_lies_on_curve_iff
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    (D : Chapter11CartierCurve X) (p : Chapter11SurfacePoint X) :
    chapter11PointLiesOnCurve D p ↔
      ∃ z : D.carrier, D.inclusion z = p.point :=
  Iff.rfl

/-- Two curves meet when their closed subschemes have a common closed point. -/
def chapter11CurvesMeet
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    (D G : Chapter11CartierCurve X) : Prop :=
  ∃ p : Chapter11SurfacePoint X,
    chapter11PointLiesOnCurve D p ∧ chapter11PointLiesOnCurve G p

/-- Divisors are the free abelian group on integral Cartier curves.

On a regular surface this is the book-facing Cartier--Weil divisor group;
using Mathlib's free abelian group gives addition, integer coefficients,
support, and coefficient extraction without inventing a second cycle type. -/
abbrev Chapter11Divisor {S : Chapter11ArithmeticBase}
    (X : Chapter11ArithmeticSurface S) :=
  FreeAbelianGroup (Chapter11CartierCurve X)

abbrev Chapter11CartierDivisor {S : Chapter11ArithmeticBase}
    (X : Chapter11ArithmeticSurface S) :=
  Chapter11Divisor X

/-- The divisor associated with a prime Cartier curve. -/
def chapter11CurveAsDivisor
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    (D : Chapter11CartierCurve X) : Chapter11Divisor X :=
  FreeAbelianGroup.of D

/-- The multiplicity of a signed Cartier divisor at a closed point, obtained
by summing the curve coefficients against their local multiplicities. -/
noncomputable def chapter11DivisorMultiplicity
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    (D : Chapter11Divisor X) (p : Chapter11SurfacePoint X) : ℤ :=
  ∑ C in D.support,
    FreeAbelianGroup.coeff C D * (C.multiplicity p : ℤ)

theorem chapter11_curveAsDivisor_multiplicity
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    (D : Chapter11CartierCurve X) (p : Chapter11SurfacePoint X) :
    chapter11DivisorMultiplicity (chapter11CurveAsDivisor D) p =
      (D.multiplicity p : ℤ) := by
  sorry

/-- The support predicate used when a local intersection is proper. -/
def chapter11NoCommonComponent
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    (D G : Chapter11Divisor X) : Prop :=
  ∀ C, C ∈ D.support → C ∉ G.support

def chapter11DivisorIsVertical
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    (D : Chapter11Divisor X) : Prop :=
  ∀ C, C ∈ D.support → C.vertical

def chapter11DivisorIsHorizontal
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    (D : Chapter11Divisor X) : Prop :=
  ∀ C, C ∈ D.support → C.horizontal

/-! ### Point blowups and transforms -/

/- LOCAL_DEPENDENCY_GUESS: Mathlib has the Rees algebra and relative Proj
primitives but no bundled point-blowup object with exceptional and strict
transform maps.  This record is the smallest interface needed by the chapter;
the field `isBlowupOfPoint` is deliberately a geometric predicate rather than
an axiom asserting any intersection formula. -/

/-- A point blowup over the fixed arithmetic base. -/
structure Chapter11PointBlowup
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    (p : Chapter11SurfacePoint X) where
  target : Chapter11ArithmeticSurface S
  map : target.carrier ⟶ X.carrier
  map_over_base : map ≫ X.structureMap = target.structureMap
  isBlowupOfPoint : Prop
  target_regular : target.regular
  exceptionalCurve : Chapter11CartierCurve target
  exceptional_vertical : exceptionalCurve.vertical
  exceptional_contracted_to_center : Prop
  strictTransform : Chapter11CartierCurve X → Chapter11CartierCurve target
  totalTransform : Chapter11Divisor X →+ Chapter11Divisor target
  totalTransform_is_pullback : Prop
  isomorphism_off_center : Prop

abbrev Chapter11BlowupSurface
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (b : Chapter11PointBlowup p) : Chapter11ArithmeticSurface S :=
  b.target

def chapter11BlowupMorphism
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (b : Chapter11PointBlowup p) : b.target.carrier ⟶ X.carrier :=
  b.map

def chapter11ExceptionalDivisor
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (b : Chapter11PointBlowup p) : Chapter11Divisor b.target :=
  chapter11CurveAsDivisor b.exceptionalCurve

noncomputable def chapter11StrictTransformMap
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (b : Chapter11PointBlowup p) :
    Chapter11Divisor X →+ Chapter11Divisor b.target :=
  FreeAbelianGroup.lift (fun D => chapter11CurveAsDivisor (b.strictTransform D))

noncomputable def chapter11StrictTransformDivisor
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (b : Chapter11PointBlowup p) (D : Chapter11Divisor X) :
    Chapter11Divisor b.target :=
  chapter11StrictTransformMap b D

theorem chapter11_strictTransformMap_curve
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (b : Chapter11PointBlowup p)
    (D : Chapter11CartierCurve X) :
    chapter11StrictTransformMap b (chapter11CurveAsDivisor D) =
      chapter11CurveAsDivisor (b.strictTransform D) := by
  sorry

def chapter11TotalTransform
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (b : Chapter11PointBlowup p) (D : Chapter11Divisor X) :
    Chapter11Divisor b.target :=
  b.totalTransform D

/-! ### Numerical intersections and the projection bridge -/

/- LOCAL_DEPENDENCY_GUESS: Books 9--10 supply degree, pushforward, pullback,
and the projection formula in the intended development, but those Book 12
interfaces are not available in this checkout.  A numerical context below is
chosen only in a vertical/proper setting where its integer pairing is defined;
it is not a claim that arbitrary horizontal self-intersections have canonical
integer values. -/

/-- An integer-valued numerical intersection pairing in a specified setting.

The `scope` field records the hypotheses under which the pairing is defined;
the pairing itself is deliberately not extended to an arbitrary global
arithmetic-surface intersection theory. -/
structure Chapter11NumericalIntersectionContext
    {S : Chapter11ArithmeticBase}
    (X : Chapter11ArithmeticSurface S) where
  scope : Prop
  pairing : Chapter11Divisor X → Chapter11Divisor X → ℤ
  pairing_add_left :
    ∀ D₁ D₂ G,
      pairing (D₁ + D₂) G = pairing D₁ G + pairing D₂ G
  pairing_add_right :
    ∀ D G₁ G₂,
      pairing D (G₁ + G₂) = pairing D G₁ + pairing D G₂
  pairing_zsmul_left :
    ∀ (n : ℤ) D G, pairing (n • D) G = n * pairing D G
  pairing_zsmul_right :
    ∀ (n : ℤ) D G, pairing D (n • G) = n * pairing D G
  pairing_zero_left : ∀ G, pairing 0 G = 0
  pairing_zero_right : ∀ D, pairing D 0 = 0

def chapter11Intersection
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    (I : Chapter11NumericalIntersectionContext X)
    (D G : Chapter11Divisor X) : ℤ :=
  I.pairing D G

/-- The pushforward/projection data used for a point blowup.  This is the
book-facing form of the earlier proper-map projection formula: strict
transforms push forward to their original curves, and the exceptional curve
pushes forward to zero. -/
structure Chapter11PointBlowupProjectionData
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (b : Chapter11PointBlowup p) where
  source : Chapter11NumericalIntersectionContext X
  target : Chapter11NumericalIntersectionContext b.target
  pushforward : Chapter11Divisor b.target →+ Chapter11Divisor X
  pushforward_totalTransform :
    ∀ D, pushforward (chapter11TotalTransform b D) = D
  pushforward_strictTransform :
    ∀ C, pushforward (chapter11CurveAsDivisor (b.strictTransform C)) =
      chapter11CurveAsDivisor C
  pushforward_exceptional :
    pushforward (chapter11ExceptionalDivisor b) = 0
  projection_formula :
    ∀ D G,
      target.pairing (chapter11TotalTransform b D) G =
        source.pairing D (pushforward G)

/-! ### Local intersections and finite exceptional support -/

/- LOCAL_DEPENDENCY_GUESS: the length/Tor construction of Chapter 7 is not
available as a reusable declaration.  The local theory below leaves that
construction abstract but requires its proper-intersection input explicitly,
so the chapter cannot accidentally assign a finite length to a common
component. -/

/-- Local intersection multiplicities for proper pairs of Cartier divisors. -/
class Chapter11LocalIntersectionTheory
    {S : Chapter11ArithmeticBase}
    (X : Chapter11ArithmeticSurface S) where
  localIntersection :
    ∀ (D G : Chapter11Divisor X),
      chapter11NoCommonComponent D G →
      Chapter11SurfacePoint X → ℤ
  symmetric :
    ∀ (D G : Chapter11Divisor X) (h : chapter11NoCommonComponent D G)
      (h' : chapter11NoCommonComponent G D) (p : Chapter11SurfacePoint X),
      localIntersection D G h p = localIntersection G D h' p

def chapter11LocalIntersection
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    [Chapter11LocalIntersectionTheory X]
    (D G : Chapter11Divisor X)
    (h : chapter11NoCommonComponent D G)
    (p : Chapter11SurfacePoint X) : ℤ :=
  Chapter11LocalIntersectionTheory.localIntersection D G h p

/-- A point on the exceptional curve of a point blowup, hence infinitely near
to the center. -/
def chapter11InfinitelyNear
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (b : Chapter11PointBlowup p)
    (q : Chapter11SurfacePoint b.target) : Prop :=
  chapter11PointLiesOnCurve b.exceptionalCurve q ∧
    b.map q.point = p.point

/-- A finite, injectively indexed list of points on the exceptional curve at
which the two strict transforms still meet. -/
structure Chapter11ExceptionalContactData
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (b : Chapter11PointBlowup p)
    [Chapter11LocalIntersectionTheory X]
    [Chapter11LocalIntersectionTheory b.target]
    (D G : Chapter11Divisor X) where
  source_no_common : chapter11NoCommonComponent D G
  strict_no_common :
    chapter11NoCommonComponent
      (chapter11StrictTransformDivisor b D)
      (chapter11StrictTransformDivisor b G)
  index : Type u
  [index_finite : Fintype index]
  point : index → Chapter11SurfacePoint b.target
  point_injective : Function.Injective point
  point_on_exceptional :
    ∀ i, chapter11PointLiesOnCurve b.exceptionalCurve (point i)
  point_over_center : ∀ i, b.map (point i).point = p.point
  captures_all_remaining_contact :
    ∀ q : Chapter11SurfacePoint b.target,
      (∀ i, point i ≠ q) →
        chapter11LocalIntersection
          (chapter11StrictTransformDivisor b D)
          (chapter11StrictTransformDivisor b G)
          strict_no_common q = 0

attribute [instance] Chapter11ExceptionalContactData.index_finite

noncomputable def chapter11ExceptionalContactContribution
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    {b : Chapter11PointBlowup p}
    [Chapter11LocalIntersectionTheory X]
    [Chapter11LocalIntersectionTheory b.target]
    {D G : Chapter11Divisor X}
    (F : Chapter11ExceptionalContactData b D G) : ℤ :=
  ∑ i,
    chapter11LocalIntersection
      (chapter11StrictTransformDivisor b D)
      (chapter11StrictTransformDivisor b G)
      F.strict_no_common (F.point i) *
      (chapter11ResidueDegreeOfMap b.map (F.point i).point : ℤ)

/-! ### Iterated blowup and resolution-graph data -/

/- LOCAL_DEPENDENCY_GUESS: the preceding resolution chapter is not present in
the filesystem.  The following records expose the maps, centers, strict
transforms, and final residual term needed by the source-order formula without
postulating a conclusion about any particular resolution. -/

/-- A finite sequence of point-blowup maps over one arithmetic base.  The
`target_eq_stage` fields identify each abstract blowup target with the next
surface in the displayed chain. -/
structure Chapter11PointBlowupSequence (S : Chapter11ArithmeticBase) where
  length : ℕ
  stage : Fin (length + 1) → Chapter11ArithmeticSurface S
  initialPoint : Chapter11SurfacePoint (stage 0)
  center : ∀ j : Fin length,
    Chapter11SurfacePoint (stage ⟨j.1, Nat.lt_succ_of_lt j.2⟩)
  step : ∀ j : Fin length,
    Chapter11PointBlowup (center j)
  target_eq_stage :
    ∀ j : Fin length,
      (step j).target = stage (Fin.succ j)
  map_to_initial :
    ∀ j : Fin (length + 1),
      (stage j).carrier ⟶ (stage 0).carrier
  map_to_initial_center :
    ∀ j : Fin length,
      map_to_initial ⟨j.1, Nat.lt_succ_of_lt j.2⟩ (center j).point =
        initialPoint.point
  first_center_is_initial_point : Prop

noncomputable def chapter11CenterDegreeOverInitial
    {S : Chapter11ArithmeticBase}
    (Q : Chapter11PointBlowupSequence S) (j : Fin Q.length) : ℕ :=
  chapter11ResidueDegreeOfMap
    (Q.map_to_initial ⟨j.1, Nat.lt_succ_of_lt j.2⟩)
    (Q.center j).point

/-- The intersection data attached to a chosen sequence of point blowups.
`strictD` and `strictG` are the stagewise strict transforms; the residual is
the intersection left after the selected centers. -/
structure Chapter11IteratedIntersectionData
    {S : Chapter11ArithmeticBase}
    (Q : Chapter11PointBlowupSequence S)
    [Chapter11LocalIntersectionTheory (Q.stage 0)] where
  D G : Chapter11Divisor (Q.stage 0)
  source_no_common : chapter11NoCommonComponent D G
  original_point : Chapter11SurfacePoint (Q.stage 0)
  strictD : ∀ j : Fin (Q.length + 1), Chapter11Divisor (Q.stage j)
  strictG : ∀ j : Fin (Q.length + 1), Chapter11Divisor (Q.stage j)
  strict_transform_data : Prop
  multiplicityD : Fin Q.length → ℤ
  multiplicityG : Fin Q.length → ℤ
  center_degree : Fin Q.length → ℕ
  center_degree_eq_residue_degree :
    ∀ j, center_degree j = chapter11CenterDegreeOverInitial Q j
  original_point_eq_sequence_initial : original_point = Q.initialPoint
  residualIntersection : ℤ
  residual_is_remaining_intersection : Prop
  final_strict_transforms_disjoint : Prop

/-! ### Proximity and final resolution graphs -/

/-- Data for a later blowup at a point of the strict transform of an earlier
exceptional component. -/
structure Chapter11ProximityData
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (first : Chapter11PointBlowup p)
    (q : Chapter11SurfacePoint first.target)
    (later : Chapter11PointBlowup q) where
  oldComponent : Chapter11CartierCurve first.target
  oldComponent_is_strict_transform :
    oldComponent = first.exceptionalCurve
  center_on_oldComponent : chapter11PointLiesOnCurve oldComponent q
  old_multiplicity_at_center : oldComponent.multiplicity q = 1
  creationSquare : ℤ
  creationSquare_eq_exceptional_square : Prop
  before : Chapter11NumericalIntersectionContext first.target
  after : Chapter11NumericalIntersectionContext later.target

/-- Data for a later center lying on two components at once. -/
structure Chapter11DoubleProximityData
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (first : Chapter11PointBlowup p)
    (q : Chapter11SurfacePoint first.target)
    (later : Chapter11PointBlowup q) where
  component₁ component₂ : Chapter11CartierCurve first.target
  component₁_ne_component₂ : component₁ ≠ component₂
  center_on_component₁ : chapter11PointLiesOnCurve component₁ q
  center_on_component₂ : chapter11PointLiesOnCurve component₂ q
  component₁_multiplicity : component₁.multiplicity q = 1
  component₂_multiplicity : component₂.multiplicity q = 1
  before : Chapter11NumericalIntersectionContext first.target
  after : Chapter11NumericalIntersectionContext later.target

/-- A resolution graph records final strict transforms and their final squares,
not merely the labels assigned when components were created. -/
structure Chapter11ResolutionGraph
    (S : Chapter11ArithmeticBase) where
  finalSurface : Chapter11ArithmeticSurface S
  component : Type u
  [component_finite : Fintype component]
  finalStrictTransform : component → Chapter11CartierCurve finalSurface
  finalSquare : component → ℤ
  intersectionContext : Chapter11NumericalIntersectionContext finalSurface
  finalSquare_eq_intersection :
    ∀ i, finalSquare i =
      intersectionContext.pairing
        (chapter11CurveAsDivisor (finalStrictTransform i))
        (chapter11CurveAsDivisor (finalStrictTransform i))

attribute [instance] Chapter11ResolutionGraph.component_finite

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter11
