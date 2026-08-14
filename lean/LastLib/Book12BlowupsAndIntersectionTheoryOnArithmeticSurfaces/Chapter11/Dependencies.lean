import Mathlib.Algebra.FreeAbelianGroup.Finsupp
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ResidueField
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.Section02ChartsAndExceptionalCurves
import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter03.Section01ConstructionAndProjectivity
import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter04.Section02TotalAndStrictTransforms
import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter05.Section02ExceptionalCurveAndItsNormalBundle
import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter06.Section03EmbeddedResolutionOfSpecialFibersAndSections
import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter07.Section01LengthOfAProperIntersection
import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter07.Section02SymmetryPositivityAndTransversality
import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter07.Section04HomologicalIntersectionAndSelfIntersection

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter11

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

open LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter03
open LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter04
open LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter05
open LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter06
open LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter07
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07

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
  residueDegree_positive :
    0 < X.structureMap.residueDegree point

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

/- The preceding transform chapters supply the effective-Cartier ideal and its
scheme-theoretic support.  The curve record retains that ideal as the source
of the divisor, while its inclusion keeps the prime-curve carrier visible. -/

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
  cartierDivisor : Chapter04EffectiveCartierDivisor X.carrier
  cartierDivisor_support :
    (cartierDivisor.ideal.support : Set X.carrier) = Set.range inclusion
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
  ∑ C ∈ D.support,
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

theorem chapter11_noCommonComponent_comm
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    (D G : Chapter11Divisor X) :
    chapter11NoCommonComponent D G ↔ chapter11NoCommonComponent G D := by
  constructor
  · intro h C hC_G hC_D
    exact h C hC_D hC_G
  · intro h C hC_D hC_G
    exact h C hC_G hC_D

def chapter11DivisorsDisjoint
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    (D G : Chapter11Divisor X) : Prop :=
  ∀ C, C ∈ D.support →
    ∀ E, E ∈ G.support → ¬ chapter11CurvesMeet C E

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

def chapter11TransportMorphism
    {X Y : Scheme.{u}} (h : X = Y) {Z : Scheme.{u}}
    (f : X ⟶ Z) : Y ⟶ Z := by
  cases h
  exact f

def chapter11TransportIdealSheaf
    {X Y : Scheme.{u}} (h : X = Y) (I : X.IdealSheafData) : Y.IdealSheafData := by
  cases h
  exact I

/- The center, relative Rees/Proj presentation, and the saturation operation
are all retained in the point-blowup record.  Equalities identify the
book-facing arithmetic-surface carrier with those earlier scheme interfaces. -/

/-- A point blowup over the fixed arithmetic base. -/
structure Chapter11PointBlowup
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    (p : Chapter11SurfacePoint X) where
  target : Chapter11ArithmeticSurface S
  map : target.carrier ⟶ X.carrier
  map_over_base : map ≫ X.structureMap = target.structureMap
  centerIdeal : Chapter03CoherentIdeal X.carrier
  centerIdeal_eq_pointIdeal :
    centerIdeal.ideal = chapter07PointIdeal p.point
  reesBlowup : Chapter03Blowup centerIdeal
  rees_carrier_eq_target : reesBlowup.carrier = target.carrier
  rees_projection_eq_map :
    chapter11TransportMorphism rees_carrier_eq_target reesBlowup.projection = map
  target_regular : target.regular
  cartierBlowup : Chapter04Blowup X.carrier centerIdeal.ideal
  cartier_carrier_eq_rees : cartierBlowup.carrier = reesBlowup.carrier
  cartier_morphism_eq_rees :
    chapter11TransportMorphism cartier_carrier_eq_rees cartierBlowup.morphism =
      reesBlowup.projection
  exceptionalIdeal : target.carrier.IdealSheafData
  exceptionalIdeal_eq_pullback :
    exceptionalIdeal =
      chapter11TransportIdealSheaf
        (cartier_carrier_eq_rees.trans rees_carrier_eq_target)
        cartierBlowup.exceptionalIdeal
  exceptionalIdeal_support_eq_preimage :
    (exceptionalIdeal.support : Set target.carrier) =
      centerIdeal.support.preimage map
  exceptionalCurve : Chapter11CartierCurve target
  exceptionalIdeal_subscheme_eq_curve :
    exceptionalIdeal.subscheme = exceptionalCurve.carrier
  exceptionalCurve_inclusion_eq_subscheme :
    chapter11TransportMorphism exceptionalIdeal_subscheme_eq_curve
        exceptionalIdeal.subschemeι = exceptionalCurve.inclusion
  exceptionalCurve_ideal_eq_exceptionalIdeal :
    exceptionalCurve.cartierDivisor.ideal = exceptionalIdeal
  exceptional_vertical : exceptionalCurve.vertical
  exceptional_contracted_to_center :
    ∀ z : exceptionalCurve.carrier,
      map (exceptionalCurve.inclusion z) = p.point
  strictTransform : Chapter11CartierCurve X → Chapter11CartierCurve target
  strictTransform_ideal_eq_saturation :
    ∀ C, (strictTransform C).cartierDivisor.ideal =
      chapter04IdealSheafSaturation
        (C.cartierDivisor.ideal.comap map) exceptionalIdeal
  strictTransform_meets_exceptional_of_mem :
    ∀ C, chapter11PointLiesOnCurve C p →
      chapter11CurvesMeet (strictTransform C) exceptionalCurve
  totalTransform : Chapter11Divisor X →+ Chapter11Divisor target
  totalTransformIdeal : Chapter11CartierCurve X → target.carrier.IdealSheafData
  totalTransformIdeal_eq_pullback :
    ∀ C, totalTransformIdeal C = C.cartierDivisor.ideal.comap map
  isomorphism_off_center :
    IsIso (chapter03BlowupRestriction reesBlowup centerIdeal.ideal.support.compl)

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

def chapter11TotalTransformIdeal
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (b : Chapter11PointBlowup p) (C : Chapter11CartierCurve X) :
    b.target.carrier.IdealSheafData :=
  C.cartierDivisor.ideal.comap b.map

def chapter11StrictTransformIdeal
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (b : Chapter11PointBlowup p) (C : Chapter11CartierCurve X) :
    b.target.carrier.IdealSheafData :=
  chapter04IdealSheafSaturation (C.cartierDivisor.ideal.comap b.map)
    b.exceptionalIdeal

def chapter11TransportDivisor
    {S : Chapter11ArithmeticBase}
    {X Y : Chapter11ArithmeticSurface S}
    (h : X = Y) (D : Chapter11Divisor X) : Chapter11Divisor Y := by
  cases h
  exact D

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
  pairing_symmetric : ∀ D G, pairing D G = pairing G D

def chapter11Intersection
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    (I : Chapter11NumericalIntersectionContext X)
    (D G : Chapter11Divisor X) : ℤ :=
  I.pairing D G

/-! ### The normal-bundle and vertical-intersection bridge -/

structure Chapter11ExceptionalNormalBundleData
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (b : Chapter11PointBlowup p) where
  exceptionalBaseMap :
    b.exceptionalCurve.carrier ⟶
      AlgebraicGeometry.Spec (.of (S.carrier.residueField p.basePoint))
  normalBundle : Chapter05LineBundle b.exceptionalCurve.carrier
  degreeTheory :
    Chapter05CurveDegreeTheory b.exceptionalCurve.carrier
      (S.carrier.residueField p.basePoint) exceptionalBaseMap

noncomputable def chapter11ExceptionalNormalBundleDegree
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    {b : Chapter11PointBlowup p}
    (N : Chapter11ExceptionalNormalBundleData b) : ℤ :=
  letI : Chapter05CurveDegreeTheory b.exceptionalCurve.carrier
      (S.carrier.residueField p.basePoint) N.exceptionalBaseMap := N.degreeTheory
  chapter05Degree (f := N.exceptionalBaseMap) N.normalBundle

structure Chapter11ExceptionalIntersectionBridge
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (b : Chapter11PointBlowup p)
    (I : Chapter11NumericalIntersectionContext b.target) where
  scope : I.scope
  normalBundle : Chapter11ExceptionalNormalBundleData b
  pairing_eq_normalBundleDegree :
    I.pairing (chapter11ExceptionalDivisor b)
        (chapter11ExceptionalDivisor b) =
      chapter11ExceptionalNormalBundleDegree normalBundle
  normalBundleDegree_eq_neg_residueDegree :
    chapter11ExceptionalNormalBundleDegree normalBundle =
      -(chapter11ResidueDegree p : ℤ)

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
  exceptionalIntersection : Chapter11ExceptionalIntersectionBridge b target
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

/-! The local length/Tor, additivity, and positivity interfaces from Chapter 7
are made explicit before Chapter 11 uses its separation theorem. -/

structure Chapter11Chapter07LocalIntersectionWitness
    {S : Chapter11ArithmeticBase.{u}}
    {X : Chapter11ArithmeticSurface S}
    (D G : Chapter11Divisor X)
    (h : chapter11NoCommonComponent D G)
    (p : Chapter11SurfacePoint X) where
  ring : Type u
  ringComm : CommRing ring
  ringLocal : IsLocalRing ring
  ringNoetherian : IsNoetherianRing ring
  ringRegular : IsRegularLocalRing ring
  hasProjectiveResolutions :
    HasProjectiveResolutions (@Chapter07LocalModuleCategory ring ringComm)
  firstCurve : @Chapter07LocalEffectiveCartierCurve ring ringComm
  secondCurve : @Chapter07LocalEffectiveCartierCurve ring ringComm
  proper :
    @Chapter07ProperIntersectionAt ring ringComm ringLocal firstCurve secondCurve
  firstPassesThrough : @Chapter07PassesThrough ring ringComm ringLocal firstCurve
  secondPassesThrough : @Chapter07PassesThrough ring ringComm ringLocal secondCurve
  firstModule : @Chapter07LocalModuleCategory ring ringComm
  secondModule : @Chapter07LocalModuleCategory ring ringComm
  torProfile : @Chapter07LocalTorLengthProfile ring ringComm
  torProfile_eq_canonical :
    ∀ j, torProfile.torLength j =
      @Chapter07CanonicalTorLength ring ringComm hasProjectiveResolutions j
        firstModule secondModule
  moduleLength : ℕ∞
  moduleLength_eq_tor_zero : moduleLength = torProfile.torLength 0
  moduleLength_finite : moduleLength ≠ ⊤
  localValue : ℤ
  localValue_eq_moduleLength : localValue = Int.ofNat moduleLength.toNat

structure Chapter11Chapter07LocalIntersectionAdapter
    {S : Chapter11ArithmeticBase}
    (X : Chapter11ArithmeticSurface S) where
  localIntersection :
    ∀ (D G : Chapter11Divisor X),
      chapter11NoCommonComponent D G →
      Chapter11SurfacePoint X → ℤ
  moduleLengthWitness :
    ∀ (D G : Chapter11Divisor X) (h : chapter11NoCommonComponent D G)
      (p : Chapter11SurfacePoint X),
      Nonempty (Chapter11Chapter07LocalIntersectionWitness D G h p)
  localIntersection_eq_moduleLength :
    ∀ (D G : Chapter11Divisor X) (h : chapter11NoCommonComponent D G)
      (p : Chapter11SurfacePoint X)
      (W : Chapter11Chapter07LocalIntersectionWitness D G h p),
      localIntersection D G h p = W.localValue
  add_left :
    ∀ (D₁ D₂ G : Chapter11Divisor X)
      (h₁ : chapter11NoCommonComponent D₁ G)
      (h₂ : chapter11NoCommonComponent D₂ G)
      (h₁₂ : chapter11NoCommonComponent (D₁ + D₂) G)
      (p : Chapter11SurfacePoint X),
      localIntersection (D₁ + D₂) G h₁₂ p =
        localIntersection D₁ G h₁ p + localIntersection D₂ G h₂ p
  add_right :
    ∀ (D E₁ E₂ : Chapter11Divisor X)
      (h₁ : chapter11NoCommonComponent D E₁)
      (h₂ : chapter11NoCommonComponent D E₂)
      (h₁₂ : chapter11NoCommonComponent D (E₁ + E₂))
      (p : Chapter11SurfacePoint X),
      localIntersection D (E₁ + E₂) h₁₂ p =
        localIntersection D E₁ h₁ p + localIntersection D E₂ h₂ p
  curve_nonnegative :
    ∀ (C G : Chapter11CartierCurve X)
      (h : chapter11NoCommonComponent
        (chapter11CurveAsDivisor C) (chapter11CurveAsDivisor G))
      (p : Chapter11SurfacePoint X),
      0 ≤ localIntersection (chapter11CurveAsDivisor C)
        (chapter11CurveAsDivisor G) h p
  curve_positive_iff :
    ∀ (C G : Chapter11CartierCurve X)
      (h : chapter11NoCommonComponent
        (chapter11CurveAsDivisor C) (chapter11CurveAsDivisor G))
      (p : Chapter11SurfacePoint X),
      0 < localIntersection (chapter11CurveAsDivisor C)
        (chapter11CurveAsDivisor G) h p ↔
        chapter11PointLiesOnCurve C p ∧ chapter11PointLiesOnCurve G p
  zero_of_disjoint :
    ∀ (D G : Chapter11Divisor X)
      (h : chapter11NoCommonComponent D G)
      (_hdisjoint : chapter11DivisorsDisjoint D G)
      (p : Chapter11SurfacePoint X),
      localIntersection D G h p = 0

class Chapter11LocalIntersectionTheory
    {S : Chapter11ArithmeticBase}
    (X : Chapter11ArithmeticSurface S) where
  adapter : Chapter11Chapter07LocalIntersectionAdapter X
  symmetric :
    ∀ (D G : Chapter11Divisor X) (h : chapter11NoCommonComponent D G)
      (h' : chapter11NoCommonComponent G D) (p : Chapter11SurfacePoint X),
      adapter.localIntersection D G h p = adapter.localIntersection G D h' p

def chapter11LocalIntersection
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    [Chapter11LocalIntersectionTheory X]
    (D G : Chapter11Divisor X)
    (h : chapter11NoCommonComponent D G)
    (p : Chapter11SurfacePoint X) : ℤ :=
  (Chapter11LocalIntersectionTheory.adapter (X := X)).localIntersection D G h p

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
  point_residueDegree_positive :
    ∀ i, 0 < chapter11ResidueDegreeOfMap b.map (point i).point
  point_is_contact :
    ∀ i,
      chapter11LocalIntersection
          (chapter11StrictTransformDivisor b D)
          (chapter11StrictTransformDivisor b G)
          strict_no_common (point i) ≠ 0
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

/- A one-step witness carries the local intersection separation, the finite
contact points above the center, and the projection context for that step.
Unlike a free residual integer, every remaining term is a Chapter 7 local
intersection weighted by its residue degree. -/
structure Chapter11IteratedOneStepWitness
    {S : Chapter11ArithmeticBase.{u}}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (b : Chapter11PointBlowup p)
    (sourceTheory : Chapter11LocalIntersectionTheory X)
    (targetTheory : Chapter11LocalIntersectionTheory b.target)
    (D G : Chapter11Divisor X) where
  source_no_common : chapter11NoCommonComponent D G
  strict_no_common :
    chapter11NoCommonComponent
      (chapter11StrictTransformDivisor b D)
      (chapter11StrictTransformDivisor b G)
  projection : Chapter11PointBlowupProjectionData b
  index : Type u
  [index_finite : Fintype index]
  point : index → Chapter11SurfacePoint b.target
  point_injective : Function.Injective point
  point_on_exceptional :
    ∀ i, chapter11PointLiesOnCurve b.exceptionalCurve (point i)
  point_over_center : ∀ i, b.map (point i).point = p.point
  point_residueDegree_positive :
    ∀ i, 0 < chapter11ResidueDegreeOfMap b.map (point i).point
  point_is_contact :
    ∀ i,
      @chapter11LocalIntersection _ b.target targetTheory
        (chapter11StrictTransformDivisor b D)
        (chapter11StrictTransformDivisor b G)
        strict_no_common (point i) ≠ 0
  captures_all_remaining_contact :
    ∀ q : Chapter11SurfacePoint b.target,
      (∀ i, point i ≠ q) →
        @chapter11LocalIntersection _ b.target targetTheory
          (chapter11StrictTransformDivisor b D)
          (chapter11StrictTransformDivisor b G)
          strict_no_common q = 0
  separation :
    @chapter11LocalIntersection _ X sourceTheory D G source_no_common p =
      chapter11DivisorMultiplicity D p * chapter11DivisorMultiplicity G p +
        (∑ i,
          @chapter11LocalIntersection _ b.target targetTheory
            (chapter11StrictTransformDivisor b D)
            (chapter11StrictTransformDivisor b G)
            strict_no_common (point i) *
            (chapter11ResidueDegreeOfMap b.map (point i).point : ℤ))

attribute [instance] Chapter11IteratedOneStepWitness.index_finite

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
  map_to_initial_over_base :
    ∀ j : Fin (length + 1),
      map_to_initial j ≫ (stage 0).structureMap = (stage j).structureMap
  map_to_initial_step :
    ∀ j : Fin length,
      chapter11TransportMorphism
          (congrArg (fun T : Chapter11ArithmeticSurface S => T.carrier)
            (target_eq_stage j))
          ((step j).map ≫ map_to_initial
            ⟨j.1, Nat.lt_succ_of_lt j.2⟩) =
        map_to_initial (Fin.succ j)
  map_to_initial_center :
    ∀ j : Fin length,
      map_to_initial ⟨j.1, Nat.lt_succ_of_lt j.2⟩ (center j).point =
        initialPoint.point
  first_center_is_initial_point :
    ∀ (j : Fin length), j.1 = 0 → HEq (center j) initialPoint

noncomputable def chapter11CenterDegreeOverInitial
    {S : Chapter11ArithmeticBase}
    (Q : Chapter11PointBlowupSequence S) (j : Fin Q.length) : ℕ :=
  chapter11ResidueDegreeOfMap
    (Q.map_to_initial ⟨j.1, Nat.lt_succ_of_lt j.2⟩)
    (Q.center j).point

/-- The intersection data attached to a chosen sequence of point blowups.
`strictD` and `strictG` are the stagewise strict transforms.  Every step has
an explicit Chapter 7 local-intersection/projection witness, and the final
residual is defined from a finite list of final local intersections. -/
structure Chapter11IteratedIntersectionData
    {S : Chapter11ArithmeticBase.{u}}
    (Q : Chapter11PointBlowupSequence S)
    [Chapter11LocalIntersectionTheory (Q.stage 0)] where
  D : Chapter11Divisor (Q.stage 0)
  G : Chapter11Divisor (Q.stage 0)
  source_no_common : chapter11NoCommonComponent D G
  original_point : Chapter11SurfacePoint (Q.stage 0)
  strictD : ∀ j : Fin (Q.length + 1), Chapter11Divisor (Q.stage j)
  strictG : ∀ j : Fin (Q.length + 1), Chapter11Divisor (Q.stage j)
  strictD_step :
    ∀ j : Fin Q.length,
      chapter11TransportDivisor (Q.target_eq_stage j)
          (chapter11StrictTransformDivisor (Q.step j)
            (strictD ⟨j.1, Nat.lt_succ_of_lt j.2⟩)) =
        strictD (Fin.succ j)
  strictG_step :
    ∀ j : Fin Q.length,
      chapter11TransportDivisor (Q.target_eq_stage j)
          (chapter11StrictTransformDivisor (Q.step j)
            (strictG ⟨j.1, Nat.lt_succ_of_lt j.2⟩)) =
        strictG (Fin.succ j)
  multiplicityD : Fin Q.length → ℤ
  multiplicityG : Fin Q.length → ℤ
  center_degree : Fin Q.length → ℕ
  center_degree_eq_residue_degree :
    ∀ j, center_degree j = chapter11CenterDegreeOverInitial Q j
  center_degree_positive : ∀ j, 0 < center_degree j
  original_point_eq_sequence_initial : original_point = Q.initialPoint
  stage_theory :
    ∀ j : Fin (Q.length + 1),
      Chapter11LocalIntersectionTheory (Q.stage j)
  step_target_theory :
    ∀ j : Fin Q.length,
      Chapter11LocalIntersectionTheory (Q.step j).target
  step_witness :
    ∀ j : Fin Q.length,
      Chapter11IteratedOneStepWitness
        (Q.step j)
        (stage_theory ⟨j.1, Nat.lt_succ_of_lt j.2⟩)
        (step_target_theory j)
        (strictD ⟨j.1, Nat.lt_succ_of_lt j.2⟩)
        (strictG ⟨j.1, Nat.lt_succ_of_lt j.2⟩)
  final_theory :
    Chapter11LocalIntersectionTheory (Q.stage (Fin.last Q.length))
  final_no_common :
    chapter11NoCommonComponent
      (strictD (Fin.last Q.length)) (strictG (Fin.last Q.length))
  residualIndex : Type u
  [residualIndex_finite : Fintype residualIndex]
  residualPoint : residualIndex → Chapter11SurfacePoint (Q.stage (Fin.last Q.length))
  residualPoint_injective : Function.Injective residualPoint
  residualPoint_is_contact :
    ∀ i,
      @chapter11LocalIntersection _ (Q.stage (Fin.last Q.length)) final_theory
        (strictD (Fin.last Q.length)) (strictG (Fin.last Q.length))
        final_no_common (residualPoint i) ≠ 0
  residual_captures_all_contact :
    ∀ q : Chapter11SurfacePoint (Q.stage (Fin.last Q.length)),
      @chapter11LocalIntersection _ (Q.stage (Fin.last Q.length)) final_theory
        (strictD (Fin.last Q.length)) (strictG (Fin.last Q.length))
        final_no_common q ≠ 0 →
        ∃ i, residualPoint i = q
  final_strict_transforms_disjoint :
    chapter11DivisorsDisjoint
      (strictD (Fin.last Q.length)) (strictG (Fin.last Q.length))
  multiplicityD_eq_stage_multiplicity :
    ∀ j,
      multiplicityD j =
        chapter11DivisorMultiplicity
          (strictD ⟨j.1, Nat.lt_succ_of_lt j.2⟩) (Q.center j)
  multiplicityG_eq_stage_multiplicity :
    ∀ j,
      multiplicityG j =
        chapter11DivisorMultiplicity
          (strictG ⟨j.1, Nat.lt_succ_of_lt j.2⟩) (Q.center j)

attribute [instance] Chapter11IteratedIntersectionData.residualIndex_finite

noncomputable def chapter11ResidualIntersection
    {S : Chapter11ArithmeticBase}
    (Q : Chapter11PointBlowupSequence S)
    [Chapter11LocalIntersectionTheory (Q.stage 0)]
    (H : Chapter11IteratedIntersectionData Q) : ℤ :=
  ∑ i,
    @chapter11LocalIntersection _ (Q.stage (Fin.last Q.length)) H.final_theory
      (H.strictD (Fin.last Q.length)) (H.strictG (Fin.last Q.length))
      H.final_no_common (H.residualPoint i) *
      (chapter11ResidueDegreeOfMap
        (Q.map_to_initial (Fin.last Q.length)) (H.residualPoint i).point : ℤ)

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
  center_over_same_base_point : q.basePoint = p.basePoint
  old_multiplicity_at_center : oldComponent.multiplicity q = 1
  creationSquare : ℤ
  before : Chapter11NumericalIntersectionContext first.target
  exceptionalIntersection :
    Chapter11ExceptionalIntersectionBridge first before
  after : Chapter11NumericalIntersectionContext later.target
  creationSquare_eq_exceptional_square :
    creationSquare =
      before.pairing (chapter11CurveAsDivisor oldComponent)
        (chapter11CurveAsDivisor oldComponent)
  projection : Chapter11PointBlowupProjectionData later
  before_eq_projection_source : before = projection.source
  after_eq_projection_target : after = projection.target

/-- Data for a later center lying on two components at once. -/
structure Chapter11DoubleProximityData
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (first : Chapter11PointBlowup p)
    (q : Chapter11SurfacePoint first.target)
    (later : Chapter11PointBlowup q) where
  component₁ : Chapter11CartierCurve first.target
  component₂ : Chapter11CartierCurve first.target
  component₁_ne_component₂ : component₁ ≠ component₂
  center_on_component₁ : chapter11PointLiesOnCurve component₁ q
  center_on_component₂ : chapter11PointLiesOnCurve component₂ q
  center_over_same_base_point : q.basePoint = p.basePoint
  component₁_multiplicity : component₁.multiplicity q = 1
  component₂_multiplicity : component₂.multiplicity q = 1
  before : Chapter11NumericalIntersectionContext first.target
  after : Chapter11NumericalIntersectionContext later.target
  projection : Chapter11PointBlowupProjectionData later
  before_eq_projection_source : before = projection.source
  after_eq_projection_target : after = projection.target

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
