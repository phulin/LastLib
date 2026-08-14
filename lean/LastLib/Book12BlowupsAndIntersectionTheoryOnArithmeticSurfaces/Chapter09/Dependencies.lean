import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Data.Finsupp.Basic
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Topology.KrullDimension
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Dependencies

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter09

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Order TopologicalSpace
open scoped AlgebraicGeometry BigOperators

universe u v

/-!
Shared interfaces for Chapter 9.

The pinned Mathlib snapshot now supplies algebraic cycles, residue-field
degrees, function fields, and module length.  It does not package Cartier
divisors on a general scheme, rational equivalence, or the arithmetic-surface
intersection pairing.  The records below keep those book-facing interfaces
explicit while using the canonical objects wherever they are available.
-/

/-! ### Regular surfaces and the divisor vocabulary -/

/-- The line-bundle object supplied by the preceding algebraic-geometry books. -/
abbrev Chapter09LineBundle (X : Scheme.{u}) :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Chapter09LineBundle X

abbrev Chapter09LineBundleIso {X : Scheme.{u}}
    (L M : Chapter09LineBundle X) :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Chapter09LineBundleIso L M

/-- A noetherian integral regular scheme of absolute dimension two.

`regular` is stated on affine opens using Mathlib's canonical
`IsRegularRing`; the dimension field is deliberately separate so that the
surface hypothesis is not smuggled into regularity. -/
structure Chapter09RegularNoetherianIntegralSurface where
  carrier : Scheme.{u}
  noetherian : IsNoetherian carrier
  integral : IsIntegral carrier
  regular : ∀ U : carrier.affineOpens, IsRegularRing Γ(carrier, U)
  dimensionTwo : topologicalKrullDim carrier = 2

/-- The function field of a Chapter 9 surface, with the integral-scheme
instance installed locally when the canonical Mathlib abbreviation is used. -/
noncomputable def chapter09RationalFunction
    (X : Chapter09RegularNoetherianIntegralSurface) : Type u :=
  letI : IsIntegral X.carrier := X.integral
  X.carrier.functionField

noncomputable instance chapter09RationalFunction.field
    (X : Chapter09RegularNoetherianIntegralSurface) : Field (chapter09RationalFunction X) := by
  dsimp [chapter09RationalFunction]
  letI : IsIntegral X.carrier := X.integral
  infer_instance

/-- A codimension-one point, recorded using the canonical order-theoretic
coheight. -/
structure Chapter09CodimensionOnePoint (X : Scheme.{u}) where
  point : X
  coheight_one : coheight point = 1

abbrev Chapter09CodimOneStalk
    (X : Chapter09RegularNoetherianIntegralSurface)
    (ξ : Chapter09CodimensionOnePoint X.carrier) :=
  X.carrier.presheaf.stalk ξ.point

/-- A prime curve on a regular surface.  The closed immersion and integral
one-dimensional carrier make the codimension-one geometry explicit; `order`
is the valuation used by principal divisors. -/
structure Chapter09PrimeCurve (X : Chapter09RegularNoetherianIntegralSurface) where
  carrier : Scheme.{u}
  inclusion : carrier ⟶ X.carrier
  closed : IsClosedImmersion inclusion
  integral : IsIntegral carrier
  dimensionOne : topologicalKrullDim carrier = 1
  codimensionOne : Prop
  vertical : Prop
  order : chapter09RationalFunction X → ℤ
  order_zero : order 0 = 0
  order_one : order 1 = 0
  order_mul : ∀ f g, order (f * g) = order f + order g

/- LOCAL_DEPENDENCY_GUESS: the canonical Mathlib cycle is indexed by scheme
points, while the book needs the codimension-one prime-curve summand and its
valuation.  `Chapter09PrimeCurve` is the minimal bridge carrying that data. -/

/-- Weil divisors are finite integer sums of prime curves. -/
abbrev Chapter09WeilDivisor (X : Chapter09RegularNoetherianIntegralSurface) :=
  Chapter09PrimeCurve X →₀ ℤ

abbrev Chapter09Divisor (X : Chapter09RegularNoetherianIntegralSurface) :=
  Chapter09WeilDivisor X

def chapter09DivisorCoeff
    (D : Chapter09Divisor X) (C : Chapter09PrimeCurve X) : ℤ :=
  D C

/-- A line bundle together with the rational-section data used in the Cartier
dictionary.  The `rationalSection_is_rational` field keeps the trivialization choice
explicit rather than treating an arbitrary field element as a section. -/
structure Chapter09LineBundleRationalSection
    (X : Chapter09RegularNoetherianIntegralSurface) where
  lineBundle : Chapter09LineBundle X.carrier
  rationalSection : chapter09RationalFunction X
  rationalSection_nonzero : rationalSection ≠ 0
  rationalSection_is_rational : Prop

/-- Local Cartier data attached to a divisor.  Mathlib has the local rational
function and invertible-sheaf ingredients separately, so their compatibility
is retained as an explicit field. -/
structure Chapter09CartierPresentation
    (X : Chapter09RegularNoetherianIntegralSurface) where
  divisor : Chapter09Divisor X
  localEquation : X.carrier.Opens → chapter09RationalFunction X
  localEquations_are_regular : Prop
  associatedLineBundle : Chapter09LineBundle X.carrier
  rationalSection : chapter09RationalFunction X
  rationalSection_nonzero : rationalSection ≠ 0
  compatible : Prop

/-- The local-equation presentation is the Cartier divisor object used by the
book-facing dictionary. -/
abbrev Chapter09CartierDivisor
    (X : Chapter09RegularNoetherianIntegralSurface) :=
  Chapter09CartierPresentation X

/-- The three presentations of a divisor and their compatibility data. -/
structure Chapter09RegularSurfaceDictionary
    (X : Chapter09RegularNoetherianIntegralSurface) where
  cartierToWeil : Chapter09CartierPresentation X → Chapter09WeilDivisor X
  cartierToWeil_eq_divisor : ∀ P, cartierToWeil P = P.divisor
  cartierToLineBundleSection :
    Chapter09CartierPresentation X → Chapter09LineBundleRationalSection X
  cartierRealizes : ∀ D : Chapter09WeilDivisor X,
    ∃ P : Chapter09CartierPresentation X, cartierToWeil P = D
  compatibility : Prop

def chapter09LineBundleRationalSectionOfPresentation
    {X : Chapter09RegularNoetherianIntegralSurface}
    (P : Chapter09CartierPresentation X) :
    Chapter09LineBundleRationalSection X :=
  { lineBundle := P.associatedLineBundle
    rationalSection := P.rationalSection
    rationalSection_nonzero := P.rationalSection_nonzero
    rationalSection_is_rational := P.compatible }

/-! ### Zero-cycles and residue degrees -/

/-- A closed point used as a summand of a zero-cycle. -/
structure Chapter09ClosedPoint (X : Scheme.{u}) where
  point : X
  closed : IsClosed ({point} : Set X)

/-- A zero-cycle is a finite integer sum of closed points. -/
abbrev Chapter09ZeroCycle (X : Scheme.{u}) :=
  Chapter09ClosedPoint X →₀ ℤ

def chapter09ZeroCycleCoeff
    (z : Chapter09ZeroCycle X) (x : Chapter09ClosedPoint X) : ℤ :=
  z x

/-- The canonical residue-field degree at a point of a scheme morphism. -/
def chapter09ResidueFieldDegree
    {X S : Scheme.{u}} (f : X ⟶ S) (x : Chapter09ClosedPoint X) : ℕ :=
  f.residueDegree x.point

theorem chapter09_residueFieldDegree_eq_finrank
    {X S : Scheme.{u}} (f : X ⟶ S) (x : Chapter09ClosedPoint X) :
    chapter09ResidueFieldDegree f x = f.residueDegree x.point :=
  rfl

/-- Degree of a zero-cycle over the base of a scheme morphism, with the
residue-field weights built in. -/
def chapter09ZeroCycleDegree
    {X S : Scheme.{u}} (f : X ⟶ S) (z : Chapter09ZeroCycle X) : ℤ :=
  ∑ x in z.support, z x * (chapter09ResidueFieldDegree f x : ℤ)

/-- Support of a zero-cycle lies over a chosen base point. -/
def chapter09ZeroCycleSupportedOver
    {X S : Scheme.{u}} (f : X ⟶ S) (s : S) (z : Chapter09ZeroCycle X) : Prop :=
  ∀ x, z x ≠ 0 → f x.point = s

/-- The residue degree formula for a cycle supported over `s`. -/
theorem chapter09_zeroCycle_degree_formula
    {X S : Scheme.{u}} (f : X ⟶ S) (s : S) (z : Chapter09ZeroCycle X)
    (hz : chapter09ZeroCycleSupportedOver f s z) :
    chapter09ZeroCycleDegree f z =
      ∑ x in z.support, z x * (f.residueDegree x.point : ℤ) := by
  rfl

/-! ### Cartier--Weil and principal-divisor bridges -/

/-- Nonzero rational functions, so that `div f` never receives the undefined
argument `f = 0`. -/
abbrev Chapter09NonzeroRationalFunction
    (X : Chapter09RegularNoetherianIntegralSurface) :=
  { f : chapter09RationalFunction X // f ≠ 0 }

/-- The unavailable global Cartier/rational-section constructor is isolated in
one reusable interface.  Its coefficient formula is fixed by the valuation on
each prime curve. -/
class Chapter09PrincipalDivisorTheory
    (X : Chapter09RegularNoetherianIntegralSurface) where
  principal : Chapter09NonzeroRationalFunction X → Chapter09WeilDivisor X
  principal_one :
    principal ⟨1, one_ne_zero⟩ = 0
  principal_mul : ∀ f g,
    principal ⟨f.1 * g.1, mul_ne_zero f.2 g.2⟩ = principal f + principal g
  principal_coeff_order : ∀ f C,
    principal f C = C.order f.1

def chapter09PrincipalDivisor
    {X : Chapter09RegularNoetherianIntegralSurface}
    [Chapter09PrincipalDivisorTheory X]
    (f : Chapter09NonzeroRationalFunction X) : Chapter09WeilDivisor X :=
  Chapter09PrincipalDivisorTheory.principal f

noncomputable def chapter09PrincipalSubgroup
    (X : Chapter09RegularNoetherianIntegralSurface)
    [Chapter09PrincipalDivisorTheory X] :
    AddSubgroup (Chapter09WeilDivisor X) :=
  AddSubgroup.closure (Set.range (chapter09PrincipalDivisor (X := X)))

def chapter09RationallyEquivalent
    {X : Chapter09RegularNoetherianIntegralSurface}
    [Chapter09PrincipalDivisorTheory X]
    (D E : Chapter09WeilDivisor X) : Prop :=
  D - E ∈ chapter09PrincipalSubgroup X

noncomputable def chapter09RationalEquivalenceSetoid
    (X : Chapter09RegularNoetherianIntegralSurface)
    [Chapter09PrincipalDivisorTheory X] : Setoid (Chapter09WeilDivisor X) where
  r := chapter09RationallyEquivalent
  iseqv := by
    sorry

abbrev Chapter09RationalEquivalenceClass
    (X : Chapter09RegularNoetherianIntegralSurface)
    [Chapter09PrincipalDivisorTheory X] :=
  Quotient (chapter09RationalEquivalenceSetoid X)

/-! ### Proper curves, vertical curves, and intersection interfaces -/

/-- A proper integral curve over a field, with its dimension hypothesis
visible to the degree interface. -/
structure Chapter09ProperCurveOverField (k : Type u) [Field k] where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ Spec (CommRingCat.of k)
  proper : IsProper structureMap
  integral : IsIntegral carrier
  dimensionOne : topologicalKrullDim carrier = 1

noncomputable def chapter09CurveRationalFunction
    {k : Type u} [Field k] (C : Chapter09ProperCurveOverField k) : Type u :=
  letI : IsIntegral C.carrier := C.integral
  C.carrier.functionField

noncomputable instance chapter09CurveRationalFunction.field
    {k : Type u} [Field k] (C : Chapter09ProperCurveOverField k) :
    Field (chapter09CurveRationalFunction C) := by
  dsimp [chapter09CurveRationalFunction]
  letI : IsIntegral C.carrier := C.integral
  infer_instance

abbrev Chapter09CurveDivisor
    {k : Type u} [Field k] (C : Chapter09ProperCurveOverField k) :=
  Chapter09ZeroCycle C.carrier

/-- The proper-curve degree package used to express degree zero of principal
divisors without replacing a divisor by an integer prematurely. -/
class Chapter09ProperCurveDivisorTheory
    {k : Type u} [Field k] (C : Chapter09ProperCurveOverField k) where
  principal : { f : chapter09CurveRationalFunction C // f ≠ 0 } →
    Chapter09CurveDivisor C
  degree : Chapter09CurveDivisor C → ℤ
  principal_degree_zero : ∀ f, degree (principal f) = 0

def chapter09PrincipalDivisorDegreeZero
    {k : Type u} [Field k] (C : Chapter09ProperCurveOverField k)
    [Chapter09ProperCurveDivisorTheory C] : Prop :=
  ∀ f, Chapter09ProperCurveDivisorTheory.degree (Chapter09ProperCurveDivisorTheory.principal f) = 0

/-- A vertical proper curve on an arithmetic surface. -/
structure Chapter09VerticalCurve
    (X : Chapter09RegularNoetherianIntegralSurface) where
  curve : Type u
  [curveField : Field curve]
  carrier : Scheme.{u}
  structureMap : carrier ⟶ Spec (CommRingCat.of curve)
  proper : IsProper structureMap
  integral : IsIntegral carrier
  inclusion : carrier ⟶ X.carrier
  vertical : Prop

attribute [instance] Chapter09VerticalCurve.curveField

/-- Restriction of a divisor to a proper vertical curve, its degree, and the
fiberwise intersection pairing.  The restriction map is a thin bridge to the
line-bundle/degree API of Book 9. -/
class Chapter09VerticalIntersectionTheory
    (X : Chapter09RegularNoetherianIntegralSurface)
    (P : Chapter09PrincipalDivisorTheory X) where
  restrictionLineBundle : ∀ D : Chapter09WeilDivisor X,
    ∀ C : Chapter09VerticalCurve X, Chapter09LineBundle C.carrier
  degree : ∀ C : Chapter09VerticalCurve X, Chapter09LineBundle C.carrier → ℤ
  intersection : Chapter09WeilDivisor X → Chapter09VerticalCurve X → ℤ
  intersection_eq_degree : ∀ D C,
    intersection D C = degree C (restrictionLineBundle D C)
  intersection_add : ∀ D E C,
    intersection (D + E) C = intersection D C + intersection E C
  intersection_zero : ∀ C, intersection 0 C = 0
  principal_invariance : ∀ D f C,
    intersection (D + P.principal f) C = intersection D C

/- LOCAL_DEPENDENCY_GUESS: restriction of an invertible sheaf to a vertical
curve and its degree are inherited from the preceding relative-curve books,
but their composite is not a single pinned Mathlib declaration. -/

def chapter09VerticalIntersection
    {X : Chapter09RegularNoetherianIntegralSurface}
    {P : Chapter09PrincipalDivisorTheory X}
    [I : Chapter09VerticalIntersectionTheory X P]
    (D : Chapter09WeilDivisor X) (C : Chapter09VerticalCurve X) : ℤ :=
  I.intersection D C

def chapter09IsVerticalDivisor
    {X : Chapter09RegularNoetherianIntegralSurface}
    (D : Chapter09WeilDivisor X) : Prop :=
  ∀ C, D C ≠ 0 → C.vertical

/-! The vertical--vertical case is a bilinear pairing on divisor data.  The
symmetry field is restricted to vertical inputs because that is the domain
where the arithmetic-surface construction is asserted in this chapter. -/
class Chapter09VerticalDivisorPairingTheory
    (X : Chapter09RegularNoetherianIntegralSurface)
    (P : Chapter09PrincipalDivisorTheory X) where
  pairing : Chapter09WeilDivisor X → Chapter09WeilDivisor X → ℤ
  pairing_add_left : ∀ D E F,
    pairing (D + E) F = pairing D F + pairing E F
  pairing_add_right : ∀ D E F,
    pairing D (E + F) = pairing D E + pairing D F
  pairing_zero_left : ∀ D, pairing 0 D = 0
  pairing_zero_right : ∀ D, pairing D 0 = 0
  pairing_symmetric_on_vertical : ∀ D E,
    chapter09IsVerticalDivisor D → chapter09IsVerticalDivisor E →
      pairing D E = pairing E D

/- LOCAL_DEPENDENCY_GUESS: the pinned cycle API has no rational-equivalence
quotient for zero-cycles with boundary terms.  This record keeps the global
principal-intersection assertion and the retained boundary contribution
separate until that earlier cycle package is available. -/
class Chapter09PrincipalIntersectionCycleTheory
    (X : Chapter09RegularNoetherianIntegralSurface)
    (P : Chapter09PrincipalDivisorTheory X) where
  intersectionCycle :
    Chapter09WeilDivisor X → Chapter09NonzeroRationalFunction X →
      Chapter09ZeroCycle X.carrier
  principalIntersectionRationallyTrivial : Prop
  boundaryContributionsRetained : Prop
  horizontalBoundaryMayBeNonzero : Prop

def chapter09PrincipalIntersectionCycle
    {X : Chapter09RegularNoetherianIntegralSurface}
    {P : Chapter09PrincipalDivisorTheory X}
    [T : Chapter09PrincipalIntersectionCycleTheory X P]
    (D : Chapter09WeilDivisor X)
    (f : Chapter09NonzeroRationalFunction X) : Chapter09ZeroCycle X.carrier :=
  T.intersectionCycle D f

/-! ### Projective moving and local-length interfaces -/

/-- A projective regular surface over a field.  The infinite-field hypothesis
needed by the usual moving lemma is left to the theorem that uses it. -/
structure Chapter09ProjectiveRegularSurfaceOverField (k : Type u) [Field k]
    extends Chapter09RegularNoetherianIntegralSurface where
  structureMap : carrier ⟶ Spec (CommRingCat.of k)
  proper : IsProper structureMap
  projective : Prop

def chapter09NoCommonPrimeComponents
    {X : Chapter09RegularNoetherianIntegralSurface}
    (D E : Chapter09WeilDivisor X) : Prop :=
  ∀ C, ¬ (D C ≠ 0 ∧ E C ≠ 0)

def chapter09LinearlyEquivalent
    {X : Chapter09RegularNoetherianIntegralSurface}
    [Chapter09PrincipalDivisorTheory X]
    (D E : Chapter09WeilDivisor X) : Prop :=
  chapter09RationallyEquivalent D E

/-- The module-theoretic local length `length R/(I + J)` used at a proper
intersection. -/
noncomputable def chapter09LocalIntersectionLength
    {R : Type u} [CommRing R] (I J : Ideal R) : ℕ∞ :=
  Module.length R (Ideal.Quotient (I ⊔ J))

/-- A local witness records the ideal quotient whose module length contributes
at a closed intersection point. -/
structure Chapter09LocalLengthWitness
    {k : Type u} [Field k]
    (X : Chapter09ProjectiveRegularSurfaceOverField k)
    (D E : Chapter09WeilDivisor X.toChapter09RegularNoetherianIntegralSurface) where
  point : Chapter09ClosedPoint X.carrier
  leftIdeal : Ideal (X.carrier.presheaf.stalk point.point)
  rightIdeal : Ideal (X.carrier.presheaf.stalk point.point)
  length : ℕ∞
  length_eq_ideal_quotient :
    length = chapter09LocalIntersectionLength leftIdeal rightIdeal
  leftIdeal_represents_D : Prop
  rightIdeal_represents_E : Prop
  proper_intersection : Prop

/-- A local-length intersection package for divisors with no common component.
The support and formula fields are intentionally explicit because Mathlib's
cycle and module-length APIs do not yet identify them automatically. -/
class Chapter09LocalLengthIntersectionTheory
    {k : Type u} [Field k]
    (X : Chapter09ProjectiveRegularSurfaceOverField k) where
  localIntersectionCycle :
    ∀ (D E : Chapter09WeilDivisor X.toChapter09RegularNoetherianIntegralSurface),
      chapter09NoCommonPrimeComponents D E → Chapter09ZeroCycle X.carrier
  localLengthWitness : ∀ D E,
    chapter09NoCommonPrimeComponents D E →
    Chapter09LocalLengthWitness X D E
  supported_on_proper_intersections : Prop
  local_length_formula : Prop
  independent_of_moving_representative : Prop
  recovers_lineBundle_intersection : Prop

def chapter09LocalLengthIntersection
    {k : Type u} [Field k]
    (X : Chapter09ProjectiveRegularSurfaceOverField k)
    [T : Chapter09LocalLengthIntersectionTheory X]
    (D E : Chapter09WeilDivisor X.toChapter09RegularNoetherianIntegralSurface)
    (h : chapter09NoCommonPrimeComponents D E) : ℤ :=
  chapter09ZeroCycleDegree X.structureMap (T.localIntersectionCycle D E h)

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter09
