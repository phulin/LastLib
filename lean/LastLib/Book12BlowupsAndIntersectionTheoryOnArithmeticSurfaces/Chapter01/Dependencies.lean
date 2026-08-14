import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Topology.KrullDimension
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.Section01ProjectiveBundles
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03.Section03NormalCurvesAndRegularModels
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Section04TheDivisorPicardCorrespondence
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter05.Dependencies
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter13.Dependencies

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter01

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter05
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter13
open scoped AlgebraicGeometry BigOperators

universe u v

/-!
Shared interfaces for Book 12, Chapter 1.

The preceding books already provide codimension-one prime divisors, Weil
divisors, line-bundle classes, residue-field degrees, and projective bundles.
This file only packages the arithmetic-surface context and the small
intersection/blowup bridges needed to state the chapter's opening formulas.
-/

/-! ### Arithmetic bases, surfaces, curves, and points -/

/-- An excellent connected Dedekind base, with the connectedness hypothesis visible. -/
structure Chapter01ExcellentConnectedDedekindBase where
  carrier : Scheme.{u}
  dedekind : Chapter13DedekindScheme carrier
  excellent : Chapter13ExcellentScheme carrier
  connected : ConnectedSpace carrier

/-- The generic point and its chosen function-field presentation. -/
structure Chapter01GenericPointData
    (B : Chapter01ExcellentConnectedDedekindBase)
    (K : Type u) [Field K] where
  eta : B.carrier
  eta_is_generic : IsGenericPoint eta Set.univ
  residueFieldIso : CommRingCat.of K ≅ B.carrier.residueField eta
  genericPointMap : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ B.carrier
  genericPointMap_eq :
    genericPointMap (genericPoint
      (AlgebraicGeometry.Spec (CommRingCat.of K))) = eta
  genericPointMap_is_residueFieldMap :
    genericPointMap =
      AlgebraicGeometry.Spec.map residueFieldIso.inv ≫
        B.carrier.fromSpecResidueField eta

/-- The full excellent Dedekind base convention used by the chapter. -/
structure Chapter01ExcellentConnectedDedekindBaseData
    (K : Type u) [Field K] extends
    Chapter01ExcellentConnectedDedekindBase where
  genericPoint : Chapter01GenericPointData toChapter01ExcellentConnectedDedekindBase K

abbrev chapter01GenericPoint
    {K : Type u} [Field K]
    (B : Chapter01ExcellentConnectedDedekindBaseData K) : B.carrier :=
  B.genericPoint.eta

abbrev chapter01GenericPointMap
    {K : Type u} [Field K]
    (B : Chapter01ExcellentConnectedDedekindBaseData K) :
    AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ B.carrier :=
  B.genericPoint.genericPointMap

/-- A regular arithmetic surface has absolute dimension two and relative dimension one. -/
structure Chapter01RegularArithmeticSurface
    {K : Type u} [Field K]
    (B : Chapter01ExcellentConnectedDedekindBaseData K) where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ B.carrier
  integral : IsIntegral carrier
  noetherian : IsNoetherian carrier
  regular : Chapter13RegularScheme carrier
  proper : IsProper structureMap
  flat : Flat structureMap
  relativeDimensionOne : Chapter13RelativeDimensionOne structureMap
  absoluteDimensionTwo : Chapter13AbsoluteDimensionTwo carrier

namespace Chapter01RegularArithmeticSurface

instance {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    (X : Chapter01RegularArithmeticSurface B) : IsIntegral X.carrier :=
  X.integral

instance {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    (X : Chapter01RegularArithmeticSurface B) : IsNoetherian X.carrier :=
  X.noetherian

instance {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    (X : Chapter01RegularArithmeticSurface B) : Chapter13RegularScheme X.carrier :=
  X.regular

end Chapter01RegularArithmeticSurface

/-- The generic fiber of a regular arithmetic surface. -/
abbrev chapter01GenericFiber
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    (X : Chapter01RegularArithmeticSurface B) : Scheme.{u} :=
  pullback X.structureMap (chapter01GenericPointMap B)

/-- The usual smooth and geometrically connected generic-fiber convention. -/
structure Chapter01GenericFiberProperties
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    (X : Chapter01RegularArithmeticSurface B) where
  smooth : Smooth (pullback.snd X.structureMap (chapter01GenericPointMap B))
  geometricallyConnected :
    Chapter13GeometricallyConnected
      (pullback.snd X.structureMap (chapter01GenericPointMap B))

/-- A closed surface point together with the closed point of the base below it. -/
structure Chapter01SurfacePoint
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    (X : Chapter01RegularArithmeticSurface B) where
  point : X.carrier
  basePoint : B.carrier
  point_closed : IsClosed ({point} : Set X.carrier)
  basePoint_closed : IsClosed ({basePoint} : Set B.carrier)
  lies_over : X.structureMap point = basePoint

/-- The residue-field weight appearing in fiberwise intersection formulas. -/
noncomputable def chapter01ResidueDegree
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    (p : Chapter01SurfacePoint X) : ℕ :=
  X.structureMap.residueDegree p.point

theorem chapter01_residueDegree_eq_morphism_residueDegree
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    (p : Chapter01SurfacePoint X) :
    chapter01ResidueDegree p = X.structureMap.residueDegree p.point := by
  rfl

/-- The chapter's curve vocabulary reuses Book 9's integral codimension-one subschemes. -/
abbrev Chapter01Curve (X : Scheme.{u}) := Chapter03PrimeDivisor X

abbrev Chapter01Divisor (X : Scheme.{u}) := Chapter03WeilDivisor X

def chapter01CurveIsHorizontal
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    (C : Chapter01Curve X.carrier) : Prop :=
  X.structureMap.base C.genericPoint = chapter01GenericPoint B

def chapter01CurveIsVertical
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    (C : Chapter01Curve X.carrier) : Prop :=
  ∃ s : B.carrier, IsClosed ({s} : Set B.carrier) ∧
    s ≠ chapter01GenericPoint B ∧
    C.support ⊆ X.structureMap ⁻¹' ({s} : Set B.carrier)

/-- Local multiplicity of a curve at a surface point.

The pinned library has the local regular-ring and initial-form ingredients,
but not their assembled order-of-a-Cartier-equation operation.  This is the
minimal reusable interface for that operation; it does not contain any
intersection conclusion. -/
class Chapter01CurveMultiplicityTheory (X : Scheme.{u}) where
  multiplicity : Chapter01Curve X → X → ℕ
  multiplicity_zero_of_not_mem :
    ∀ (C : Chapter01Curve X) (x : X),
      x ∉ C.support → multiplicity C x = 0

def chapter01CurveMultiplicity
    {X : Scheme.{u}} [Chapter01CurveMultiplicityTheory X]
    (C : Chapter01Curve X) (x : X) : ℕ :=
  Chapter01CurveMultiplicityTheory.multiplicity C x

theorem chapter01_curveMultiplicity_zero_of_not_mem
    {X : Scheme.{u}} [Chapter01CurveMultiplicityTheory X]
    (C : Chapter01Curve X) (x : X) (hx : x ∉ C.support) :
    chapter01CurveMultiplicity C x = 0 := by
  exact Chapter01CurveMultiplicityTheory.multiplicity_zero_of_not_mem C x hx

noncomputable def chapter01DivisorMultiplicity
    {X : Scheme.{u}} [Chapter01CurveMultiplicityTheory X]
    (D : Chapter01Divisor X) (x : X) : ℤ :=
  ∑ C ∈ D.support, D C * (chapter01CurveMultiplicity C x : ℤ)

def chapter01NoCommonComponent
    {X : Scheme.{u}} (D G : Chapter01Divisor X) : Prop :=
  ∀ C, ¬ (D C ≠ 0 ∧ G C ≠ 0)

theorem chapter01_divisorMultiplicity_single
    {X : Scheme.{u}} [Chapter01CurveMultiplicityTheory X]
    (C : Chapter01Curve X) (x : X) :
    chapter01DivisorMultiplicity (Finsupp.single C 1) x =
      chapter01CurveMultiplicity C x := by
  sorry

/-! ### Numerical contexts and point blowups -/

/-- An integer-valued intersection pairing in a stated domain of definition. -/
structure Chapter01NumericalIntersectionContext
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    (X : Chapter01RegularArithmeticSurface B) where
  scope : Set (Chapter01Divisor X.carrier × Chapter01Divisor X.carrier)
  pairing : Chapter01Divisor X.carrier → Chapter01Divisor X.carrier → ℤ
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

def chapter01Intersection
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    (I : Chapter01NumericalIntersectionContext X)
    (D G : Chapter01Divisor X.carrier) : ℤ :=
  I.pairing D G

/-- A point blowup record retaining the maps and generic-fiber identification. -/
structure Chapter01PointBlowup
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    (p : Chapter01SurfacePoint X) where
  target : Chapter01RegularArithmeticSurface B
  map : target.carrier ⟶ X.carrier
  map_over_base : map ≫ X.structureMap = target.structureMap
  isBlowupOfPoint : Prop
  genericFiberIso : chapter01GenericFiber target ≅ chapter01GenericFiber X
  genericFiberIso_over :
    genericFiberIso.hom ≫ pullback.snd X.structureMap
        (chapter01GenericPointMap B) =
      pullback.snd target.structureMap (chapter01GenericPointMap B)
  exceptionalCurve : Chapter01Curve target.carrier
  exceptional_vertical : chapter01CurveIsVertical exceptionalCurve
  exceptional_contracted_to_center :
    ∀ y : target.carrier,
      y ∈ exceptionalCurve.support → map y = p.point
  strictTransform : Chapter01Curve X.carrier → Chapter01Curve target.carrier
  strictTransformDivisor :
    Chapter01Divisor X.carrier →+ Chapter01Divisor target.carrier
  strictTransform_on_curve :
    ∀ C, strictTransformDivisor (Finsupp.single C 1) =
      Finsupp.single (strictTransform C) 1

def chapter01ExceptionalDivisor
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    {p : Chapter01SurfacePoint X}
    (b : Chapter01PointBlowup p) : Chapter01Divisor b.target.carrier :=
  Finsupp.single b.exceptionalCurve 1

def chapter01StrictTransformDivisor
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    {p : Chapter01SurfacePoint X}
    (b : Chapter01PointBlowup p) (D : Chapter01Divisor X.carrier) :
    Chapter01Divisor b.target.carrier :=
  b.strictTransformDivisor D

/-- Pushforward/projection data used to transport the numerical pairing across a blowup. -/
structure Chapter01PointBlowupProjectionData
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    {p : Chapter01SurfacePoint X}
    (b : Chapter01PointBlowup p) where
  source : Chapter01NumericalIntersectionContext X
  target : Chapter01NumericalIntersectionContext b.target
  pushforward : Chapter01Divisor b.target.carrier →+ Chapter01Divisor X.carrier
  pushforward_strictTransform :
    ∀ C, pushforward (Finsupp.single (b.strictTransform C) 1) =
      Finsupp.single C 1
  pushforward_exceptional :
    pushforward (chapter01ExceptionalDivisor b) = 0
  projection_formula :
    ∀ D G,
      target.pairing (b.strictTransformDivisor D) G =
        source.pairing D (pushforward G)

/-! ### Local lengths, line bundles, cycles, and base-valued targets -/

noncomputable def chapter01LocalIntersectionLength
    {X : Scheme.{u}} (x : X)
    (I J : Ideal (X.presheaf.stalk x)) : ℕ∞ :=
  Module.length (X.presheaf.stalk x) ((X.presheaf.stalk x) ⧸ (I ⊔ J))

structure Chapter01LocalIntersectionWitness
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    (D G : Chapter01Divisor X.carrier) where
  point : Chapter01SurfacePoint X
  leftIdeal : Ideal (X.carrier.presheaf.stalk point.point)
  rightIdeal : Ideal (X.carrier.presheaf.stalk point.point)
  length : ℕ∞
  length_eq_ideal_quotient :
    length = chapter01LocalIntersectionLength point.point leftIdeal rightIdeal
  source_no_common : chapter01NoCommonComponent D G
  leftIdeal_represents_D : Prop
  rightIdeal_represents_G : Prop

abbrev Chapter01LineBundle (X : Scheme.{u}) := Chapter04LineBundle X
abbrev Chapter01LineBundleClass (X : Scheme.{u}) := Chapter04PicardGroup X
abbrev Chapter01ZeroCycle (X : Scheme.{u}) := Chapter05Divisor X

/-- A degree map is extra data on a base-valued cycle or divisor class. -/
structure Chapter01SpecifiedDegreeMap (A : Type u) where
  degree : A → ℤ

def chapter01ApplySpecifiedDegree
    {A : Type u} (d : Chapter01SpecifiedDegreeMap A) (a : A) : ℤ :=
  d.degree a

class Chapter01ZeroCycleIntersectionTheory
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    (X : Chapter01RegularArithmeticSurface B) where
  pairing : Chapter01Divisor X.carrier → Chapter01Divisor X.carrier →
    Chapter01ZeroCycle B.carrier

class Chapter01BaseClassIntersectionTheory
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    (X : Chapter01RegularArithmeticSurface B) where
  pairing : Chapter01Divisor X.carrier → Chapter01Divisor X.carrier →
    Chapter01LineBundleClass B.carrier

/- LOCAL_DEPENDENCY_GUESS: the pinned scheme and module APIs do not assemble
the normal bundle of a codimension-one subscheme into a Picard-class-valued
operation.  The class below is the smallest reusable bridge for the statement
that a horizontal normal bundle has a class, without choosing an integer degree. -/
class Chapter01NormalBundleClassTheory
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    (X : Chapter01RegularArithmeticSurface B) where
  normalBundleClass :
    ∀ C : Chapter01Curve X.carrier,
      Chapter01LineBundleClass C.closedSubscheme.subscheme

def chapter01HorizontalNormalBundleClass
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    [Chapter01NormalBundleClassTheory X]
    (C : Chapter01Curve X.carrier) :
    Chapter01LineBundleClass C.closedSubscheme.subscheme :=
  Chapter01NormalBundleClassTheory.normalBundleClass C

/- LOCAL_DEPENDENCY_GUESS: degree of a line bundle on a proper curve is
available in the preceding book through Euler-characteristic interfaces, but
the assembled vertical-component operation is kept explicit here. -/
class Chapter01VerticalLineBundleDegreeTheory
    {k : Type u} [Field k]
    (C : Chapter05ProperRegularIntegralCurve k) where
  degree : Chapter01LineBundle C.carrier → ℤ

def chapter01VerticalLineBundleDegree
    {k : Type u} [Field k]
    {C : Chapter05ProperRegularIntegralCurve k}
    [Chapter01VerticalLineBundleDegreeTheory C]
    (L : Chapter01LineBundle C.carrier) : ℤ :=
  Chapter01VerticalLineBundleDegreeTheory.degree L

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter01
