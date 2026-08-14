import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.RegularLocalRing.Defs
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter11.Dependencies

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter10

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Set TopologicalSpace
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter11
open scoped AlgebraicGeometry BigOperators

universe u v

/-!
Shared interfaces for Chapter 10.

The pinned Mathlib snapshot already contains schemes, residue fields, algebraic
cycles, order of vanishing, ideal-sheaf pullback, and the standard proper,
finite, flat, and dominant morphism properties.  The earlier book-facing
intersection package is not a single Mathlib object, so the small records
below keep the cycle, Cartier, degree, and intersection interfaces explicit.
They are data interfaces for the constructions used by the later sections;
the theorems establishing their geometric properties remain in the proof pass.
-/

/-! ### Arithmetic surfaces and curves -/

/-- An integral regular noetherian scheme of dimension two. -/
structure Chapter10IntegralRegularSurface where
  carrier : Scheme.{u}
  integral : IsIntegral carrier
  locallyNoetherian : IsLocallyNoetherian carrier
  regular : ∀ x : carrier, IsRegularLocalRing (carrier.presheaf.stalk x)
  normal : ∀ x : carrier, IsIntegrallyClosed (carrier.presheaf.stalk x)
  dimension_two : Order.krullDim carrier = 2

/-- The arithmetic-surface package used in the standing conventions. -/
structure Chapter10ArithmeticSurface extends Chapter10IntegralRegularSurface where
  base : Scheme.{u}
  structureMap : carrier ⟶ base
  proper : IsProper structureMap
  flat : Flat structureMap
  relativeDimensionOne : Prop
  baseConnected : ConnectedSpace base
  baseExcellent : Prop
  baseDedekind : Prop

structure Chapter10ProperSurfaceMorphismData
    {X Y : Scheme.{u}} (f : Y ⟶ X) where
  sourceSurface : Chapter10IntegralRegularSurface
  targetSurface : Chapter10IntegralRegularSurface
  sourceSurface_carrier : sourceSurface.carrier = Y
  targetSurface_carrier : targetSurface.carrier = X
  proper : IsProper f

structure Chapter10DedekindBase where
  carrier : Scheme.{u}
  integral : IsIntegral carrier
  locallyNoetherian : IsLocallyNoetherian carrier
  regular : ∀ s : carrier, IsRegularLocalRing (carrier.presheaf.stalk s)
  dimension_one : Order.krullDim carrier = 1

/-- A codimension-one point, i.e. the generic point of a prime curve. -/
abbrev Chapter10PrimeCurvePoint (X : Scheme.{u}) :=
  {x : X // Order.coheight x = 1}

/-- A closed point, used as a generator of a zero-cycle. -/
abbrev Chapter10ClosedPoint (X : Scheme.{u}) :=
  {x : X // IsClosed ({x} : Set X)}

/-- An integral curve embedded as a closed codimension-one subscheme. -/
structure Chapter10IntegralCurveOn (X : Scheme.{u}) where
  carrier : Scheme.{u}
  inclusion : carrier ⟶ X
  integral : IsIntegral carrier
  locallyNoetherian : IsLocallyNoetherian carrier
  closed : IsClosedImmersion inclusion
  dimension_one : Order.krullDim carrier = 1
  genericPoint : carrier
  genericPoint_is_generic : IsGenericPoint genericPoint (Set.univ : Set carrier)
  primePoint : Chapter10PrimeCurvePoint X
  genericPoint_maps_to_prime : inclusion genericPoint = primePoint.1

/-!
The image package records the one-dimensional image in the form needed by
the projection formula.  A separate image package is useful because a proper
map may instead contract the curve to a closed point.
-/
/- LOCAL_DEPENDENCY_GUESS: the preceding curve-image package supplies the
generically-finite function-field extension and its finite degree. -/
structure Chapter10CurveImageData
    {X Y : Scheme.{u}} (f : Y ⟶ X) (C : Chapter10IntegralCurveOn Y) where
  image : Chapter10IntegralCurveOn X
  map : C.carrier ⟶ image.carrier
  factorization : map ≫ image.inclusion = C.inclusion ≫ f
  genericPoint_map : map C.genericPoint = image.genericPoint
  proper : IsProper map
  genericallyFinite : Prop
  fieldDegree : ℕ
  fieldDegree_eq_residueDegree : fieldDegree = map.residueDegree C.genericPoint
  fieldDegree_is_finite_extension : Prop

def chapter10CurveImageDegree
    {X Y : Scheme.{u}} {f : Y ⟶ X} {C : Chapter10IntegralCurveOn Y}
    (M : Chapter10CurveImageData f C) : ℕ :=
  M.fieldDegree

/-! ### Cycles and Cartier divisors -/

abbrev Chapter10AlgebraicCycle (X : Scheme.{u}) :=
  AlgebraicCycle X ℤ

/-- A finite Weil divisor, represented by a locally finite integer cycle on
the codimension-one points of a surface. -/
structure Chapter10WeilDivisor (X : Scheme.{u}) where
  cycle : Chapter10AlgebraicCycle X
  support_is_curve : cycle.support ⊆ {x : X | Order.coheight x = 1}
  finite_support : cycle.support.Finite

@[ext]
theorem chapter10_weilDivisor_ext {X : Scheme.{u}}
    {D E : Chapter10WeilDivisor X} (h : D.cycle = E.cycle) : D = E := by
  cases D
  cases E
  cases h
  rfl

/-- A finite zero-cycle, represented by a locally finite cycle on closed
points. -/
structure Chapter10ZeroCycle (X : Scheme.{u}) where
  cycle : Chapter10AlgebraicCycle X
  support_is_closed : cycle.support ⊆ {x : X | IsClosed ({x} : Set X)}
  finite_support : cycle.support.Finite

@[ext]
theorem chapter10_zeroCycle_ext {X : Scheme.{u}}
    {z w : Chapter10ZeroCycle X} (h : z.cycle = w.cycle) : z = w := by
  cases z
  cases w
  cases h
  rfl

noncomputable def chapter10PrimeCurveDivisor {X : Scheme.{u}}
    (C : Chapter10PrimeCurvePoint X) : Chapter10WeilDivisor X := by
  classical
  exact
    { cycle := Function.locallyFinsupp.single C.1 1
      support_is_curve := by
        sorry
      finite_support := by
        sorry }

noncomputable def chapter10PointZeroCycle {X : Scheme.{u}}
    (x : Chapter10ClosedPoint X) : Chapter10ZeroCycle X := by
  classical
  exact
    { cycle := Function.locallyFinsupp.single x.1 1
      support_is_closed := by
        sorry
      finite_support := by
        sorry }

def chapter10WeilDivisorZero {X : Scheme.{u}} : Chapter10WeilDivisor X where
  cycle := 0
  support_is_curve := by
    simp
  finite_support := by
    simp

def chapter10WeilDivisorAdd {X : Scheme.{u}}
    (D E : Chapter10WeilDivisor X) : Chapter10WeilDivisor X where
  cycle := D.cycle + E.cycle
  support_is_curve := by
    sorry
  finite_support := by
    sorry

def chapter10WeilDivisorZsmul {X : Scheme.{u}}
    (n : ℤ) (D : Chapter10WeilDivisor X) : Chapter10WeilDivisor X where
  cycle := n • D.cycle
  support_is_curve := by
    sorry
  finite_support := by
    sorry

def chapter10ZeroCycleZero {X : Scheme.{u}} : Chapter10ZeroCycle X where
  cycle := 0
  support_is_closed := by
    simp
  finite_support := by
    simp

def chapter10ZeroCycleAdd {X : Scheme.{u}}
    (z w : Chapter10ZeroCycle X) : Chapter10ZeroCycle X where
  cycle := z.cycle + w.cycle
  support_is_closed := by
    sorry
  finite_support := by
    sorry

def chapter10ZeroCycleZsmul {X : Scheme.{u}}
    (n : ℤ) (z : Chapter10ZeroCycle X) : Chapter10ZeroCycle X where
  cycle := n • z.cycle
  support_is_closed := by
    sorry
  finite_support := by
    sorry

/-- A Cartier divisor together with its Weil-cycle and associated line bundle.
The `isCartier` field is the book-facing regular-surface dictionary supplied
by the preceding chapters. -/
structure Chapter10CartierDivisor (X : Scheme.{u}) where
  divisor : Chapter10WeilDivisor X
  lineBundle : Chapter10LineBundle X
  isCartier : Prop

def chapter10CartierDivisorEquivalent {X : Scheme.{u}}
    (D E : Chapter10CartierDivisor X) : Prop :=
  D.divisor.cycle = E.divisor.cycle ∧
    chapter11LineBundleIsomorphic D.lineBundle E.lineBundle

theorem chapter10_cartierDivisorEquivalent_refl {X : Scheme.{u}}
    (D : Chapter10CartierDivisor X) :
    chapter10CartierDivisorEquivalent D D := by
  exact ⟨rfl, chapter11_lineBundleIsomorphic_refl D.lineBundle⟩

theorem chapter10_cartierDivisorEquivalent_symm {X : Scheme.{u}}
    {D E : Chapter10CartierDivisor X}
    (h : chapter10CartierDivisorEquivalent D E) :
    chapter10CartierDivisorEquivalent E D := by
  exact ⟨h.1.symm, chapter11_lineBundleIsomorphic_symm h.2⟩

/-!
The effective Cartier divisor below reuses the earlier effective-Cartier
interface.  In particular, its ideal is the canonical `IdealSheafData`, so
scheme-theoretic inverse images can use Mathlib's `IdealSheafData.comap`.
-/
abbrev Chapter10EffectiveCartierDivisor (X : Scheme.{u}) :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Chapter09EffectiveCartierDivisor X

noncomputable def chapter10SchemeTheoreticInverseImageIdeal
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (D : Chapter10EffectiveCartierDivisor X) : Y.IdealSheafData :=
  D.ideal.comap f

def chapter10PulledBackEquationIsRegular
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (D : Chapter10EffectiveCartierDivisor X) : Prop :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Chapter09LocallyRegularPrincipal
    (chapter10SchemeTheoreticInverseImageIdeal f D)

/-! ### Degree and intersection interfaces -/

/- LOCAL_DEPENDENCY_GUESS: the preceding surface chapters supply the
Cartier/Weil dictionary and the controlled intersection constructions. -/
class Chapter10IntersectionTheory (X : Scheme.{u}) where
  withCurve : Chapter10CartierDivisor X → Chapter10IntegralCurveOn X → ℤ
  withWeilDivisor : Chapter10CartierDivisor X → Chapter10WeilDivisor X → ℤ
  withCartierDivisors : ∀ (D G : Chapter10CartierDivisor X),
    Disjoint D.divisor.cycle.support G.divisor.cycle.support → Chapter10ZeroCycle X
  withCartierWeilDivisors : ∀ (D : Chapter10CartierDivisor X)
    (G : Chapter10WeilDivisor X),
    Disjoint D.divisor.cycle.support G.cycle.support → Chapter10ZeroCycle X
  withCurve_eq_withWeilDivisor : ∀ (D : Chapter10CartierDivisor X)
    (C : Chapter10IntegralCurveOn X),
    withCurve D C = withWeilDivisor D (chapter10PrimeCurveDivisor C.primePoint)
  withWeilDivisor_zsmul : ∀ (D : Chapter10CartierDivisor X)
    (n : ℤ) (G : Chapter10WeilDivisor X),
    withWeilDivisor D (chapter10WeilDivisorZsmul n G) =
      n * withWeilDivisor D G

def chapter10IntersectionNumber {X : Scheme.{u}}
    [Chapter10IntersectionTheory X]
    (D : Chapter10CartierDivisor X) (C : Chapter10IntegralCurveOn X) : ℤ :=
  Chapter10IntersectionTheory.withCurve D C

def chapter10IntersectionNumberWithWeilDivisor {X : Scheme.{u}}
    [Chapter10IntersectionTheory X]
    (D : Chapter10CartierDivisor X) (G : Chapter10WeilDivisor X) : ℤ :=
  Chapter10IntersectionTheory.withWeilDivisor D G

def chapter10ProperIntersection {X : Scheme.{u}}
    (D G : Chapter10CartierDivisor X) : Prop :=
  Disjoint D.divisor.cycle.support G.divisor.cycle.support

/- LOCAL_DEPENDENCY_GUESS: restriction of a line bundle to a prime curve has
an integer degree and is invariant under line-bundle isomorphism. -/
class Chapter10CurveDegreeTheory (X : Scheme.{u}) where
  degree : Chapter10IntegralCurveOn X → Chapter10LineBundle X → ℤ
  degree_iso : ∀ (C : Chapter10IntegralCurveOn X) {L M : Chapter10LineBundle X},
    chapter11LineBundleIsomorphic L M → degree C L = degree C M

def chapter10CurveDegree {X : Scheme.{u}}
    [Chapter10CurveDegreeTheory X]
    (C : Chapter10IntegralCurveOn X) (L : Chapter10LineBundle X) : ℤ :=
  Chapter10CurveDegreeTheory.degree C L

/-! ### Function-field and birational adapters -/

def chapter10CurveFieldDegree {X Y : Scheme.{u}}
    (f : Y ⟶ X) (C : Chapter10PrimeCurvePoint Y) : ℕ :=
  f.residueDegree C.1

def chapter10PointFieldDegree {X Y : Scheme.{u}}
    (f : Y ⟶ X) (y : Y) : ℕ :=
  f.residueDegree y

/- LOCAL_DEPENDENCY_GUESS: the canonical map of function fields induced by a
dominant map is not packaged in the pinned scheme API. -/
class Chapter10DominantFunctionFieldTheory
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] where
  map : X.functionField ⟶ Y.functionField
  injective : Function.Injective map

def chapter10FunctionFieldMap {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] [IsDominant f]
    [Chapter10DominantFunctionFieldTheory f] :
    X.functionField ⟶ Y.functionField :=
  Chapter10DominantFunctionFieldTheory.map f

structure Chapter10BirationalMorphismData
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] where
  dominant : IsDominant f
  functionField : Chapter10DominantFunctionFieldTheory f
  isIso : IsIso functionField.map

def chapter10BirationalMorphism {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] : Prop :=
  Nonempty (Chapter10BirationalMorphismData f)

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter10
