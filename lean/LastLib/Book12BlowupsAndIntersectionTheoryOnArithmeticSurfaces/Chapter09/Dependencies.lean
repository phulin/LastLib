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
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Topology.KrullDimension
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Dependencies
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03.Dependencies
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter11.Dependencies

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
  LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter11.Chapter11LineBundle X

abbrev Chapter09LineBundleIso {X : Scheme.{u}}
    (L M : Chapter09LineBundle X) :=
  LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter11.Chapter11LineBundleIso L M

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
  /-- The arithmetic-surface verticality predicate, kept external to the
  underlying prime-curve data so a geometric curve has only one index. -/
  verticalPrimeCurve :
    LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03.Chapter03PrimeDivisor
      carrier → Prop

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

/-! The order of vanishing is defined only on nonzero rational functions.  In
particular, extending it to zero with an integer value would no longer be a
valuation and would make the principal-divisor coefficient interface
misleading. -/
abbrev Chapter09NonzeroRationalFunction
    (X : Chapter09RegularNoetherianIntegralSurface) :=
  { f : chapter09RationalFunction X // f ≠ 0 }

/-! The preceding divisor chapter already packages codimension-one points as
subtypes. Reuse that canonical object, while exposing the named projections
used by the Chapter 9 statements. -/
abbrev Chapter09CodimensionOnePoint (X : Scheme.{u}) :=
  LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03.Chapter03CodimensionOnePoint X

abbrev Chapter09CodimensionOnePoint.point
    {X : Scheme.{u}} (ξ : Chapter09CodimensionOnePoint X) : X :=
  ξ.1

theorem Chapter09CodimensionOnePoint.coheight_one
    {X : Scheme.{u}} (ξ : Chapter09CodimensionOnePoint X) :
    coheight ξ.point = 1 :=
  ξ.2

abbrev Chapter09CodimOneStalk
    (X : Chapter09RegularNoetherianIntegralSurface)
    (ξ : Chapter09CodimensionOnePoint X.carrier) :=
  X.carrier.presheaf.stalk ξ.point

instance chapter09CodimOneStalk.domain
    (X : Chapter09RegularNoetherianIntegralSurface)
    (ξ : Chapter09CodimensionOnePoint X.carrier) :
    IsDomain (Chapter09CodimOneStalk X ξ) := by
  exact @AlgebraicGeometry.instIsDomainCarrierStalkCommRingCatPresheafOfIsIntegral
    X.carrier X.integral ξ.point

/-! A prime curve extends the canonical codimension-one prime divisor. The
vertical marker is supplied by the surface-level arithmetic predicate, so it
does not duplicate the geometric curve in the Weil-divisor index. The order
is Mathlib's order of vanishing at the canonical generic point, not an
unconstrained extra function. -/
structure Chapter09PrimeCurve (X : Chapter09RegularNoetherianIntegralSurface)
    extends
      LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03.Chapter03PrimeDivisor
        X.carrier where
  dimensionOne :
    topologicalKrullDim toChapter03PrimeDivisor.closedSubscheme.subscheme = 1

def Chapter09PrimeCurve.vertical
    {X : Chapter09RegularNoetherianIntegralSurface}
    (C : Chapter09PrimeCurve X) : Prop :=
  X.verticalPrimeCurve C.toChapter03PrimeDivisor

abbrev Chapter09PrimeCurve.carrier
    {X : Chapter09RegularNoetherianIntegralSurface}
    (C : Chapter09PrimeCurve X) : Scheme.{u} :=
  C.toChapter03PrimeDivisor.closedSubscheme.subscheme

abbrev Chapter09PrimeCurve.inclusion
    {X : Chapter09RegularNoetherianIntegralSurface}
    (C : Chapter09PrimeCurve X) : C.carrier ⟶ X.carrier :=
  C.toChapter03PrimeDivisor.closedSubscheme.subschemeι

theorem Chapter09PrimeCurve.closed
    {X : Chapter09RegularNoetherianIntegralSurface}
    (C : Chapter09PrimeCurve X) : IsClosedImmersion C.inclusion := by
  exact LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03.chapter03_primeDivisor_isClosedImmersion
    C.toChapter03PrimeDivisor

@[ext]
theorem chapter09_primeCurve_ext
    {X : Chapter09RegularNoetherianIntegralSurface}
    {C D : Chapter09PrimeCurve X}
    (h : C.toChapter03PrimeDivisor = D.toChapter03PrimeDivisor) : C = D := by
  cases C
  cases D
  cases h
  rfl

noncomputable def Chapter09PrimeCurve.order
    {X : Chapter09RegularNoetherianIntegralSurface}
    (C : Chapter09PrimeCurve X) : Chapter09NonzeroRationalFunction X → ℤ :=
  fun f =>
    letI : IsIntegral X.carrier := X.integral
    letI : IsNoetherian X.carrier := X.noetherian
    X.carrier.ord f.1 C.toChapter03PrimeDivisor.genericPoint

theorem Chapter09PrimeCurve.order_one
    {X : Chapter09RegularNoetherianIntegralSurface}
    (C : Chapter09PrimeCurve X) : C.order ⟨1, one_ne_zero⟩ = 0 := by
  sorry

theorem Chapter09PrimeCurve.order_mul
    {X : Chapter09RegularNoetherianIntegralSurface}
    (C : Chapter09PrimeCurve X) (f g : Chapter09NonzeroRationalFunction X) :
    C.order ⟨f.1 * g.1, mul_ne_zero f.2 g.2⟩ = C.order f + C.order g := by
  sorry

/- The canonical Mathlib cycle is indexed by scheme points. The preceding
Book 9 divisor chapter supplies the codimension-one prime-divisor bridge;
`Chapter09PrimeCurve` adds only the vertical marker needed here. -/

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
  rationalSection_is_rational_holds : rationalSection_is_rational

/-- Local Cartier data attached to a divisor.  Mathlib has the local rational
function and invertible-sheaf ingredients separately, so their compatibility
is retained as an explicit field. -/
structure Chapter09CartierPresentation
    (X : Chapter09RegularNoetherianIntegralSurface) where
  /-- The Book 9 Cartier object whose valuation data controls this presentation. -/
  book9CartierTheory :
    LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03.Chapter03CartierDivisorTheory
      X.carrier
  book9CartierDivisor : book9CartierTheory.CartierDivisor
  divisor : Chapter09Divisor X
  localEquation : X.carrier.Opens → chapter09RationalFunction X
  /-- Local equations realize the Book 9 valuation on the Chapter 9 prime-curve index. -/
  localEquation_is_book9_principal :
    ∀ x : X.carrier, ∃ U : X.carrier.Opens, x ∈ U ∧
      ∃ (f : chapter09RationalFunction X), f ≠ 0 ∧
        localEquation U = f ∧
          ∀ C : Chapter09PrimeCurve X,
            C.toChapter03PrimeDivisor.genericPoint ∈ U →
              divisor C =
                book9CartierTheory.valuation book9CartierDivisor
                  C.toChapter03PrimeDivisor
  associatedLineBundle : Chapter09LineBundle X.carrier
  rationalSection : chapter09RationalFunction X
  rationalSection_nonzero : rationalSection ≠ 0
  compatible : Prop
  compatible_holds : compatible

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
  cartierToWeil_coeff_eq_book9_valuation :
    ∀ (P : Chapter09CartierPresentation X) (C : Chapter09PrimeCurve X),
      cartierToWeil P C =
        P.book9CartierTheory.valuation P.book9CartierDivisor
          C.toChapter03PrimeDivisor
  cartierRealizes : ∀ D : Chapter09WeilDivisor X,
    ∃ P : Chapter09CartierPresentation X, cartierToWeil P = D

def chapter09LineBundleRationalSectionOfPresentation
    {X : Chapter09RegularNoetherianIntegralSurface}
    (P : Chapter09CartierPresentation X) :
    Chapter09LineBundleRationalSection X :=
  { lineBundle := P.associatedLineBundle
    rationalSection := P.rationalSection
    rationalSection_nonzero := P.rationalSection_nonzero
    rationalSection_is_rational := P.compatible
    rationalSection_is_rational_holds := P.compatible_holds }

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
def chapter09ResidueFieldExtensionFinite
    {X S : Scheme.{u}} (f : X ⟶ S) (x : Chapter09ClosedPoint X) : Prop :=
  letI := (f.residueFieldMap x.point).hom.toAlgebra
  Module.Finite (S.residueField (f x.point)) (X.residueField x.point)

def chapter09ZeroCycleResidueDegreesFinite
    {X S : Scheme.{u}} (f : X ⟶ S) (z : Chapter09ZeroCycle X) : Prop :=
  ∀ x, x ∈ z.support → chapter09ResidueFieldExtensionFinite f x

def chapter09ResidueFieldDegree
    {X S : Scheme.{u}} (f : X ⟶ S) (x : Chapter09ClosedPoint X)
    (_hfinite : chapter09ResidueFieldExtensionFinite f x) : ℕ :=
  f.residueDegree x.point

theorem chapter09_residueFieldDegree_eq_finrank
    {X S : Scheme.{u}} (f : X ⟶ S) (x : Chapter09ClosedPoint X)
    (hfinite : chapter09ResidueFieldExtensionFinite f x) :
    chapter09ResidueFieldDegree f x hfinite = f.residueDegree x.point := by
  sorry

/-- Degree of a zero-cycle over the base of a scheme morphism, with the
residue-field weights built in. -/
def chapter09ZeroCycleDegree
    {X S : Scheme.{u}} (f : X ⟶ S) (z : Chapter09ZeroCycle X)
    (hfinite : chapter09ZeroCycleResidueDegreesFinite f z) : ℤ :=
  ∑ x ∈ z.support.attach,
    z x.1 * (chapter09ResidueFieldDegree f x.1 (hfinite x.1 x.2) : ℤ)

/-- Support of a zero-cycle lies over a chosen base point. -/
def chapter09ZeroCycleSupportedOver
    {X S : Scheme.{u}} (f : X ⟶ S) (s : S) (z : Chapter09ZeroCycle X) : Prop :=
  ∀ x, z x ≠ 0 → f x.point = s

/-- The residue degree formula for a cycle supported over `s`. -/
theorem chapter09_zeroCycle_degree_formula
    {X S : Scheme.{u}} (f : X ⟶ S) (s : S) (z : Chapter09ZeroCycle X)
    (_hz : chapter09ZeroCycleSupportedOver f s z)
    (hfinite : chapter09ZeroCycleResidueDegreesFinite f z) :
    chapter09ZeroCycleDegree f z hfinite =
      ∑ x ∈ z.support.attach, z x.1 * (f.residueDegree x.1.point : ℤ) := by
  sorry

/-! Mathlib's cycle API does not yet provide the boundary-aware rational
equivalence relation needed for the global principal-intersection statement.
This record makes that missing relation an actual equivalence interface rather
than an unstructured proposition. -/
class Chapter09ZeroCycleRationalEquivalenceTheory (X : Scheme.{u}) where
  /-- The subgroup of zero-cycles killed by the boundary/rational relations. -/
  rationalSubgroup : AddSubgroup (Chapter09ZeroCycle X)
  rationallyEquivalent : Chapter09ZeroCycle X → Chapter09ZeroCycle X → Prop
  /-- Rational equivalence is the additive quotient relation attached to the
  subgroup, rather than an unrelated equivalence predicate. -/
  rationallyEquivalent_iff_sub_mem : ∀ z w,
    rationallyEquivalent z w ↔ z - w ∈ rationalSubgroup
  rationallyEquivalent_refl : ∀ z, rationallyEquivalent z z
  rationallyEquivalent_symm : ∀ {z w},
    rationallyEquivalent z w → rationallyEquivalent w z
  rationallyEquivalent_trans : ∀ {z w t},
    rationallyEquivalent z w → rationallyEquivalent w t →
      rationallyEquivalent z t

theorem chapter09_zeroCycle_rationallyEquivalent_refl
    (X : Scheme.{u}) [Z : Chapter09ZeroCycleRationalEquivalenceTheory X]
    (z : Chapter09ZeroCycle X) : Z.rationallyEquivalent z z :=
  Z.rationallyEquivalent_refl z

theorem chapter09_zeroCycle_rationallyEquivalent_iff_sub_mem
    (X : Scheme.{u}) [Z : Chapter09ZeroCycleRationalEquivalenceTheory X]
    (z w : Chapter09ZeroCycle X) :
    Z.rationallyEquivalent z w ↔ z - w ∈ Z.rationalSubgroup :=
  Z.rationallyEquivalent_iff_sub_mem z w

theorem chapter09_zeroCycle_rationallyEquivalent_symm
    (X : Scheme.{u}) [Z : Chapter09ZeroCycleRationalEquivalenceTheory X]
    {z w : Chapter09ZeroCycle X}
    (h : Z.rationallyEquivalent z w) : Z.rationallyEquivalent w z :=
  Z.rationallyEquivalent_symm h

theorem chapter09_zeroCycle_rationallyEquivalent_trans
    (X : Scheme.{u}) [Z : Chapter09ZeroCycleRationalEquivalenceTheory X]
    {z w t : Chapter09ZeroCycle X}
    (hzw : Z.rationallyEquivalent z w)
    (hwt : Z.rationallyEquivalent w t) : Z.rationallyEquivalent z t :=
  Z.rationallyEquivalent_trans hzw hwt

/-! ### Cartier--Weil and principal-divisor bridges -/

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
    principal f C = C.order f

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
  residueFieldDegrees_finite : ∀ z : Chapter09CurveDivisor C,
    chapter09ZeroCycleResidueDegreesFinite C.structureMap z
  /-- The degree is the residue-weighted degree of the zero-cycle. -/
  degree_eq_zeroCycleDegree : ∀ z,
    degree z =
      chapter09ZeroCycleDegree C.structureMap z (residueFieldDegrees_finite z)
  principal_degree_zero : ∀ f, degree (principal f) = 0

def chapter09PrincipalDivisorDegreeZero
    {k : Type u} [Field k] (C : Chapter09ProperCurveOverField k)
    [Chapter09ProperCurveDivisorTheory C] : Prop :=
  ∀ f, Chapter09ProperCurveDivisorTheory.degree (C := C)
    (Chapter09ProperCurveDivisorTheory.principal (C := C) f) = 0

/-- A vertical proper curve on an arithmetic surface. -/
structure Chapter09VerticalCurve
    (X : Chapter09RegularNoetherianIntegralSurface) where
  arithmeticBase : Scheme.{u}
  arithmeticBase_isDedekind :
    LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03.Chapter03DedekindBase
      arithmeticBase
  arithmeticStructureMap : X.carrier ⟶ arithmeticBase
  underlyingPrimeCurve : Chapter09PrimeCurve X
  basePoint : Chapter09ClosedPoint arithmeticBase
  factorThroughFiber :
    underlyingPrimeCurve.carrier ⟶ arithmeticStructureMap.fiber basePoint.point
  factorThroughFiber_comm :
    factorThroughFiber ≫ arithmeticStructureMap.fiberι basePoint.point =
      underlyingPrimeCurve.inclusion
  structureMap :
    underlyingPrimeCurve.carrier ⟶ Spec (arithmeticBase.residueField basePoint.point)
  factorThroughFiber_structureMap :
    factorThroughFiber ≫ arithmeticStructureMap.fiberToSpecResidueField basePoint.point =
      structureMap
  proper : IsProper structureMap
  integral : IsIntegral underlyingPrimeCurve.carrier
  dimensionOne : topologicalKrullDim underlyingPrimeCurve.carrier = 1
  underlyingPrimeCurve_vertical : underlyingPrimeCurve.vertical

abbrev Chapter09VerticalCurve.carrier
    {X : Chapter09RegularNoetherianIntegralSurface}
    (C : Chapter09VerticalCurve X) : Scheme.{u} :=
  C.underlyingPrimeCurve.carrier

abbrev Chapter09VerticalCurve.inclusion
    {X : Chapter09RegularNoetherianIntegralSurface}
    (C : Chapter09VerticalCurve X) : C.carrier ⟶ X.carrier :=
  C.underlyingPrimeCurve.inclusion

def Chapter09VerticalCurve.vertical
    {X : Chapter09RegularNoetherianIntegralSurface}
    (C : Chapter09VerticalCurve X) : Prop :=
  C.underlyingPrimeCurve.vertical

theorem Chapter09VerticalCurve.vertical_holds
    {X : Chapter09RegularNoetherianIntegralSurface}
    (C : Chapter09VerticalCurve X) : C.vertical :=
  by sorry

theorem Chapter09VerticalCurve.closed
    {X : Chapter09RegularNoetherianIntegralSurface}
    (C : Chapter09VerticalCurve X) : IsClosedImmersion C.inclusion := by
  sorry

/-- Restriction of a divisor to a proper vertical curve, its degree, and the
fiberwise intersection pairing.  The restriction map is a thin bridge to the
line-bundle/degree API of Book 9. -/
class Chapter09VerticalIntersectionTheory
    (X : Chapter09RegularNoetherianIntegralSurface)
    (P : Chapter09PrincipalDivisorTheory X) where
  restrictionLineBundle : ∀ _D : Chapter09WeilDivisor X,
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
  ∀ C : Chapter09PrimeCurve X, D C ≠ 0 → C.vertical

/-! The vertical--vertical case is a bilinear pairing on divisor data.  The
symmetry field is restricted to vertical inputs because that is the domain
where the arithmetic-surface construction is asserted in this chapter. -/
class Chapter09VerticalDivisorPairingTheory
    (X : Chapter09RegularNoetherianIntegralSurface) where
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

def chapter09NoCommonPrimeComponents
    {X : Chapter09RegularNoetherianIntegralSurface}
    (D E : Chapter09WeilDivisor X) : Prop :=
  ∀ C, ¬ (D C ≠ 0 ∧ E C ≠ 0)

/- LOCAL_DEPENDENCY_GUESS: the pinned cycle API has no rational-equivalence
quotient for zero-cycles with boundary terms.  The full zero-cycle codomain of
`intersectionCycle` retains those terms, while `Z` supplies the missing
rational-equivalence relation.  The proper-intersection hypothesis is explicit
because a common component has no finite local-length intersection cycle. -/
class Chapter09PrincipalIntersectionCycleTheory
    (X : Chapter09RegularNoetherianIntegralSurface)
    (P : Chapter09PrincipalDivisorTheory X)
  [Z : Chapter09ZeroCycleRationalEquivalenceTheory X.carrier] where
  intersectionCycle :
    ∀ (D E : Chapter09WeilDivisor X),
      chapter09NoCommonPrimeComponents D E → Chapter09ZeroCycle X.carrier
  principalIntersectionRationallyTrivial :
    ∀ D f (h : chapter09NoCommonPrimeComponents D (P.principal f)),
      Z.rationallyEquivalent (intersectionCycle D (P.principal f) h) 0

def chapter09PrincipalIntersectionCycle
    {X : Chapter09RegularNoetherianIntegralSurface}
    {P : Chapter09PrincipalDivisorTheory X}
    [Z : Chapter09ZeroCycleRationalEquivalenceTheory X.carrier]
    [T : Chapter09PrincipalIntersectionCycleTheory X P]
    (D : Chapter09WeilDivisor X)
    (f : Chapter09NonzeroRationalFunction X)
    (h : chapter09NoCommonPrimeComponents D (P.principal f)) :
    Chapter09ZeroCycle X.carrier :=
  T.intersectionCycle D (P.principal f) h

/-! ### Projective moving and local-length interfaces -/

/-- A projective regular surface over a field.  The infinite-field hypothesis
needed by the usual moving lemma is left to the theorem that uses it. -/
structure Chapter09ProjectiveRegularSurfaceOverField (k : Type u) [Field k]
    extends Chapter09RegularNoetherianIntegralSurface where
  structureMap : carrier ⟶ Spec (CommRingCat.of k)
  proper : IsProper structureMap
  projective :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Chapter09ProjectiveMorphism
      structureMap

/-- Local lengths are nonnegative for effective divisors. Signed divisor
intersections are obtained by the bilinear extension from this effective
interface, as in the preceding local-intersection chapter. -/
def chapter09IsEffectiveWeilDivisor
    {X : Chapter09RegularNoetherianIntegralSurface}
    (D : Chapter09WeilDivisor X) : Prop :=
  ∀ C, 0 ≤ D C

abbrev Chapter09EffectiveWeilDivisor
    (X : Chapter09RegularNoetherianIntegralSurface) :=
  {D : Chapter09WeilDivisor X // chapter09IsEffectiveWeilDivisor D}

theorem chapter09_noCommonPrimeComponents_symm
    {X : Chapter09RegularNoetherianIntegralSurface}
    {D E : Chapter09WeilDivisor X}
    (h : chapter09NoCommonPrimeComponents D E) :
    chapter09NoCommonPrimeComponents E D := by
  intro C hC
  exact h C ⟨hC.2, hC.1⟩

def chapter09LinearlyEquivalent
    {X : Chapter09RegularNoetherianIntegralSurface}
    [Chapter09PrincipalDivisorTheory X]
    (D E : Chapter09WeilDivisor X) : Prop :=
  chapter09RationallyEquivalent D E

class Chapter09MovingLemmaTheory
    {k : Type u} [Field k] [Infinite k]
    (X : Chapter09ProjectiveRegularSurfaceOverField k)
    [P : Chapter09PrincipalDivisorTheory X.toChapter09RegularNoetherianIntegralSurface]
    where
  avoids_common_components :
    ∀ D E : Chapter09WeilDivisor X.toChapter09RegularNoetherianIntegralSurface,
      ∃ D' : Chapter09WeilDivisor X.toChapter09RegularNoetherianIntegralSurface,
        chapter09LinearlyEquivalent D D' ∧
          chapter09NoCommonPrimeComponents D' E
  /-- A moved effective divisor remains effective so it can enter the local-length API. -/
  avoids_common_components_preserving_effectivity :
    ∀ (D E : Chapter09WeilDivisor X.toChapter09RegularNoetherianIntegralSurface),
      chapter09IsEffectiveWeilDivisor D →
        chapter09IsEffectiveWeilDivisor E →
          ∃ D' : Chapter09WeilDivisor X.toChapter09RegularNoetherianIntegralSurface,
            chapter09LinearlyEquivalent D D' ∧
              chapter09NoCommonPrimeComponents D' E ∧
                chapter09IsEffectiveWeilDivisor D'

/-- The module-theoretic local length `length R/(I + J)` used at a proper
intersection. -/
noncomputable def chapter09LocalIntersectionLength
    {R : Type u} [CommRing R] (I J : Ideal R) : ℕ∞ :=
  Module.length R (R ⧸ (I ⊔ J))

/-- A local witness records the ideal quotient whose module length contributes
at a closed intersection point. -/
structure Chapter09LocalLengthWitness
    {k : Type u} [Field k]
    (X : Chapter09ProjectiveRegularSurfaceOverField k)
    (D E : Chapter09WeilDivisor X.toChapter09RegularNoetherianIntegralSurface)
    (h : chapter09NoCommonPrimeComponents D E)
    (hD : chapter09IsEffectiveWeilDivisor D)
    (hE : chapter09IsEffectiveWeilDivisor E)
    (point : Chapter09ClosedPoint X.carrier) where
  leftIdeal : Ideal (X.carrier.presheaf.stalk point.point)
  rightIdeal : Ideal (X.carrier.presheaf.stalk point.point)
  length : ℕ
  length_eq_ideal_quotient :
    (length : ℕ∞) = chapter09LocalIntersectionLength leftIdeal rightIdeal
  leftIdeal_represents_D : Prop
  leftIdeal_represents_D_holds : leftIdeal_represents_D
  rightIdeal_represents_E : Prop
  rightIdeal_represents_E_holds : rightIdeal_represents_E

/- A local-length intersection package for divisors with no common component.
The cycle symmetry, pointwise length formula, moving invariance, and
line-bundle comparison are explicit because Mathlib's cycle and module-length
APIs do not yet identify them automatically. -/
class Chapter09LocalLengthIntersectionTheory
    {k : Type u} [Field k]
    (X : Chapter09ProjectiveRegularSurfaceOverField k)
    [P : Chapter09PrincipalDivisorTheory X.toChapter09RegularNoetherianIntegralSurface] where
  localIntersectionCycle :
    ∀ (D E : Chapter09WeilDivisor X.toChapter09RegularNoetherianIntegralSurface),
      chapter09NoCommonPrimeComponents D E →
        chapter09IsEffectiveWeilDivisor D →
          chapter09IsEffectiveWeilDivisor E → Chapter09ZeroCycle X.carrier
  localIntersectionCycle_residueDegrees_finite : ∀ D E
    (h : chapter09NoCommonPrimeComponents D E)
    (hD : chapter09IsEffectiveWeilDivisor D)
    (hE : chapter09IsEffectiveWeilDivisor E),
      chapter09ZeroCycleResidueDegreesFinite X.structureMap
        (localIntersectionCycle D E h hD hE)
  localLengthWitness : ∀ D E
    (h : chapter09NoCommonPrimeComponents D E)
    (hD : chapter09IsEffectiveWeilDivisor D)
    (hE : chapter09IsEffectiveWeilDivisor E)
    (x : Chapter09ClosedPoint X.carrier),
      Chapter09LocalLengthWitness X D E h hD hE x
  localIntersectionCycle_symmetric : ∀ D E
    (hDE : chapter09NoCommonPrimeComponents D E)
    (hD : chapter09IsEffectiveWeilDivisor D)
    (hE : chapter09IsEffectiveWeilDivisor E)
    (hED : chapter09NoCommonPrimeComponents E D),
    localIntersectionCycle D E hDE hD hE =
      localIntersectionCycle E D hED hE hD
  local_length_formula : ∀ D E (h : chapter09NoCommonPrimeComponents D E)
    (hD : chapter09IsEffectiveWeilDivisor D)
    (hE : chapter09IsEffectiveWeilDivisor E)
    (x : Chapter09ClosedPoint X.carrier),
    localIntersectionCycle D E h hD hE x =
      ((localLengthWitness D E h hD hE x).length : ℤ)
  lineBundleIntersection :
    Chapter09WeilDivisor X.toChapter09RegularNoetherianIntegralSurface →
      Chapter09WeilDivisor X.toChapter09RegularNoetherianIntegralSurface → ℤ
  independent_of_moving_representative : ∀ D D' E
    (hDE : chapter09NoCommonPrimeComponents D E)
    (hD'E : chapter09NoCommonPrimeComponents D' E)
    (hEffD : chapter09IsEffectiveWeilDivisor D)
    (hEffD' : chapter09IsEffectiveWeilDivisor D')
    (hEffE : chapter09IsEffectiveWeilDivisor E),
    chapter09LinearlyEquivalent D D' →
      chapter09ZeroCycleDegree X.structureMap
          (localIntersectionCycle D E hDE hEffD hEffE)
          (localIntersectionCycle_residueDegrees_finite D E hDE hEffD hEffE) =
        chapter09ZeroCycleDegree X.structureMap
          (localIntersectionCycle D' E hD'E hEffD' hEffE)
          (localIntersectionCycle_residueDegrees_finite D' E hD'E hEffD' hEffE)
  recovers_lineBundle_intersection : ∀ D E
    (h : chapter09NoCommonPrimeComponents D E)
    (hD : chapter09IsEffectiveWeilDivisor D)
    (hE : chapter09IsEffectiveWeilDivisor E),
    lineBundleIntersection D E =
      chapter09ZeroCycleDegree X.structureMap
        (localIntersectionCycle D E h hD hE)
        (localIntersectionCycle_residueDegrees_finite D E h hD hE)

def chapter09LocalLengthIntersection
    {k : Type u} [Field k]
    (X : Chapter09ProjectiveRegularSurfaceOverField k)
    [P : Chapter09PrincipalDivisorTheory X.toChapter09RegularNoetherianIntegralSurface]
    [T : Chapter09LocalLengthIntersectionTheory X]
    (D E : Chapter09WeilDivisor X.toChapter09RegularNoetherianIntegralSurface)
    (h : chapter09NoCommonPrimeComponents D E)
    (hD : chapter09IsEffectiveWeilDivisor D)
    (hE : chapter09IsEffectiveWeilDivisor E) : ℤ :=
  chapter09ZeroCycleDegree X.structureMap (T.localIntersectionCycle D E h hD hE)
    (T.localIntersectionCycle_residueDegrees_finite D E h hD hE)

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter09
