import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Topology.KrullDimension
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.Dependencies
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter03.Core
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04.Dependencies

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter05

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter03
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04
open scoped AlgebraicGeometry BigOperators

noncomputable section

universe u v

/-!
Shared interfaces for Chapter 5.  Scheme fibers, finite morphisms, orders of
vanishing, and flat modules use the pinned Mathlib definitions.  The
book-facing surface, divisor, and component records only package data which
the source uses but which is not bundled by one canonical Mathlib object.
-/

/-! ### Dedekind bases, surfaces, and local dimensions -/

abbrev Chapter05LocalRing (X : Scheme.{u}) (x : X) : Type u :=
  X.presheaf.stalk x

def Chapter05NormalScheme (X : Scheme.{u}) : Prop :=
  ∀ x : X,
    IsDomain (Chapter05LocalRing X x) ∧
      IsIntegrallyClosed (Chapter05LocalRing X x)

def Chapter05IsDVRLocalRing (A : Type u) [CommRing A] : Prop :=
  ∃ hA : IsDomain A, letI := hA; IsDiscreteValuationRing A

structure Chapter05DedekindScheme (S : Scheme.{u}) : Prop where
  connected : _root_.IsConnected (Set.univ : Set S)
  normal : Chapter05NormalScheme S
  noetherian : IsNoetherian S
  dimension_one : topologicalKrullDim S = (1 : WithBot ℕ∞)
  affine_isDedekind : ∀ U : S.affineOpens, IsDedekindDomain Γ(S, U)

structure Chapter05ExcellentDedekindScheme (S : Scheme.{u}) : Prop
    extends Chapter05DedekindScheme S where
  closedPoint_isExcellentDVR :
    ∀ s : S, IsClosed ({s} : Set S) →
      Chapter05IsDVRLocalRing (Chapter05LocalRing S s) ∧
        Chapter03Excellent (Chapter05LocalRing S s)
  affine_isExcellent :
    ∀ U : S.affineOpens, Chapter03Excellent Γ(S, U)

def Chapter05FiniteTypeMorphism {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Chapter03FiniteTypeMorphism f

abbrev Chapter05PureDimensionOne : ObjectProperty Scheme.{u} :=
  Chapter01PureDimensionOne

def Chapter05RelativeDimensionOne {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Chapter01RelativeDimensionOne f

structure Chapter05ArithmeticSurface
    (S X : Scheme.{u}) (f : X ⟶ S) : Prop where
  integral : IsIntegral X
  normal : Chapter05NormalScheme X
  flat : Flat f
  finiteType : Chapter05FiniteTypeMorphism f
  relativeDimensionOne : Chapter05RelativeDimensionOne f

def Chapter05ProperArithmeticSurface
    (S X : Scheme.{u}) (f : X ⟶ S) : Prop :=
  Chapter05ArithmeticSurface S X f ∧ IsProper f

theorem chapter05_properArithmeticSurface_iff
    {S X : Scheme.{u}} {f : X ⟶ S} :
    Chapter05ProperArithmeticSurface S X f ↔
      Chapter05ArithmeticSurface S X f ∧ IsProper f :=
  Iff.rfl

def chapter05LocalDimension (X : Scheme.{u}) (x : X) : WithBot ℕ∞ :=
  ringKrullDim (Chapter05LocalRing X x)

def Chapter05GenericPoint (X : Scheme.{u}) (x : X) : Prop :=
  IsGenericPoint x (Set.univ : Set X)

def Chapter05PrimeDivisorPoint (X : Scheme.{u}) (x : X) : Prop :=
  Order.coheight x = 1

def Chapter05ClosedPoint (X : Scheme.{u}) (x : X) : Prop :=
  IsClosed ({x} : Set X)

def Chapter05ClosedPointOverClosedBasePoint
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  Chapter05ClosedPoint X x ∧ IsClosed ({f x} : Set S)

def Chapter05RegularSystemOfParameters
    (A : Type u) [CommRing A] [IsLocalRing A] (u v : A) : Prop :=
  Ideal.span ({u, v} : Set A) = IsLocalRing.maximalIdeal A ∧
    RingTheory.Sequence.IsRegular A [u, v]

def Chapter05RegularAtClosedPoints
    {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ x : X, Chapter05ClosedPointOverClosedBasePoint f x →
    ∃ u v : Chapter05LocalRing X x,
      Chapter05RegularSystemOfParameters (Chapter05LocalRing X x) u v

/-! The catenary interface is the one introduced in Chapter 3. -/

abbrev Chapter05Catenary (A : Type u) [CommRing A] : Prop :=
  Chapter03Catenary A

abbrev Chapter05UniversallyCatenary (A : Type u) [CommRing A] : Prop :=
  Chapter03UniversallyCatenary A

def Chapter05AffineCatenaryProfile (S : Scheme.{u}) : Prop :=
  ∀ U : S.affineOpens, Chapter05UniversallyCatenary Γ(S, U)

def Chapter05ExpectedDimensionProfile (A : Type u) [CommRing A] : Prop :=
  Chapter05Catenary A

theorem chapter05_catenary_saturated_chain_length_unique
    (A : Type u) [CommRing A] (hA : Chapter05Catenary A)
    (p q : PrimeSpectrum A) (hpq : p ≤ q)
    (c d : Chapter03SaturatedPrimeChain A p q) :
    c.length = d.length := by
  sorry

/-! ### Integral closed subschemes and prime divisors -/

structure Chapter05IntegralClosedSubscheme (X : Scheme.{u}) where
  carrier : Scheme.{u}
  inclusion : carrier ⟶ X
  closedImmersion : IsClosedImmersion inclusion
  integral : IsIntegral carrier

structure Chapter05PrimeDivisor (X : Scheme.{u})
    extends Chapter05IntegralClosedSubscheme X where
  genericPoint : carrier
  genericPoint_is_generic : IsGenericPoint genericPoint (Set.univ : Set carrier)
  point : X
  point_eq : inclusion genericPoint = point
  codimension_one : Order.coheight point = 1

def chapter05PrimeDivisorPoint
    {X : Scheme.{u}} (D : Chapter05PrimeDivisor X) : X :=
  D.point

def chapter05Horizontal
    {X S : Scheme.{u}} (f : X ⟶ S)
    (Z : Chapter05IntegralClosedSubscheme X) : Prop :=
  IsDominant (Z.inclusion ≫ f)

def chapter05Vertical
    {X S : Scheme.{u}} (f : X ⟶ S)
    (Z : Chapter05IntegralClosedSubscheme X) : Prop :=
  ∃ s : S, IsClosed ({s} : Set S) ∧
    Set.range (fun z : Z.carrier => f (Z.inclusion z)) ⊆ ({s} : Set S)

def chapter05PrimeDivisorHorizontal
    {X S : Scheme.{u}} (f : X ⟶ S)
    (D : Chapter05PrimeDivisor X) : Prop :=
  chapter05Horizontal f D.toChapter05IntegralClosedSubscheme

def chapter05PrimeDivisorVertical
    {X S : Scheme.{u}} (f : X ⟶ S)
    (D : Chapter05PrimeDivisor X) : Prop :=
  chapter05Vertical f D.toChapter05IntegralClosedSubscheme

theorem chapter05_primeDivisor_point_eq_inclusion_generic
    {X : Scheme.{u}} (D : Chapter05PrimeDivisor X) :
    D.inclusion D.genericPoint = D.point :=
  D.point_eq

theorem chapter05_primeDivisor_is_codimension_one
    {X : Scheme.{u}} (D : Chapter05PrimeDivisor X) :
    Order.coheight D.point = 1 :=
  D.codimension_one

theorem chapter05_primeDivisor_horizontal_iff
    {X S : Scheme.{u}} (f : X ⟶ S) (D : Chapter05PrimeDivisor X) :
    chapter05PrimeDivisorHorizontal f D ↔
      IsDominant (D.inclusion ≫ f) :=
  Iff.rfl

theorem chapter05_primeDivisor_vertical_iff
    {X S : Scheme.{u}} (f : X ⟶ S) (D : Chapter05PrimeDivisor X) :
    chapter05PrimeDivisorVertical f D ↔
      ∃ s : S, IsClosed ({s} : Set S) ∧
        Set.range (fun z : D.carrier => f (D.inclusion z)) ⊆ ({s} : Set S) :=
  Iff.rfl

def Chapter05VerticalIrreducibleComponent
    {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ C : irreducibleComponents X, ∃ s : S,
    IsClosed ({s} : Set S) ∧
      (C.1 : Set X) ⊆ f ⁻¹' ({s} : Set S)

def Chapter05VerticalFiberComponentPoint
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  ∃ s : S, IsClosed ({s} : Set S) ∧
    ∃ C : irreducibleComponents (f.fiber s),
      ∃ y : f.fiber s,
        IsGenericPoint y C.1 ∧ f.fiberι s y = x

/-! ### Fibers, base change, and divisor coefficients -/

abbrev chapter05Fiber {X S : Scheme.{u}} (f : X ⟶ S) (s : S) : Scheme.{u} :=
  f.fiber s

structure Chapter05BaseClosedPoint (S : Scheme.{u}) where
  point : S
  closed : IsClosed ({point} : Set S)

structure Chapter05FiniteBaseChange (S S' : Scheme.{u}) where
  map : S' ⟶ S
  finite : IsFinite map

abbrev chapter05BaseChangedSurface
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) : Scheme.{u} :=
  pullback f g

abbrev chapter05BaseChangedStructureMap
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) :
    chapter05BaseChangedSurface f g ⟶ S' :=
  pullback.snd f g

def Chapter05FiberGenericallyReduced
    {X S : Scheme.{u}} (f : X ⟶ S) (s : S) : Prop :=
  ∀ C : irreducibleComponents (f.fiber s),
    ∃ y : f.fiber s, IsGenericPoint y C.1 ∧
      IsReduced ((f.fiber s).presheaf.stalk y)

def chapter05FiberGenericResidueExtension
    {X S : Scheme.{u}} (f : X ⟶ S) (s : S) (y : f.fiber s) :=
  Scheme.Spec.map ((f.fiberToSpecResidueField s).residueFieldMap y).op

def Chapter05FiberGenericResidueExtensionsReduced
    {X S : Scheme.{u}} (f : X ⟶ S) (s : S) : Prop :=
  ∀ C : irreducibleComponents (f.fiber s),
    ∀ y : f.fiber s, IsGenericPoint y C.1 →
      GeometricallyReduced (chapter05FiberGenericResidueExtension f s y)

def Chapter05FiberGeometricallyReduced
    {X S : Scheme.{u}} (f : X ⟶ S) (s : S) : Prop :=
  GeometricallyReduced (f.fiberToSpecResidueField s)

/- LOCAL_DEPENDENCY_GUESS: the pinned scheme API provides `Scheme.ord` and
scheme fibers but not a bundled Weil-divisor/principal-divisor construction
indexed by codimension-one integral closed subschemes.  This record keeps the
canonical order formula and the support condition explicit. -/

abbrev Chapter05WeilDivisor (X : Scheme.{u}) :=
  Chapter05PrimeDivisor X →₀ ℤ

structure Chapter05PrincipalDivisorPresentation
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (g : X.functionField) where
  nonzero : g ≠ 0
  divisor : Chapter05WeilDivisor X
  coefficient_eq : ∀ D : Chapter05PrimeDivisor X,
    divisor D = AlgebraicGeometry.Scheme.ord g D.point

structure Chapter05PulledBackUniformizer
    {X S : Scheme.{u}} (f : X ⟶ S)
    (s : Chapter05BaseClosedPoint S)
    [IsIntegral X] [IsLocallyNoetherian X] where
  point_over : X
  point_over_eq : f point_over = s.point
  uniformizer : Chapter05LocalRing S (f point_over)
  uniformizer_irreducible : Irreducible uniformizer
  rationalFunction : X.functionField
  pullback_eq : rationalFunction =
    algebraMap (Chapter05LocalRing X point_over) X.functionField
      ((f.stalkMap point_over).hom uniformizer)

structure Chapter05FiberComponentFamily
    {X S : Scheme.{u}} (f : X ⟶ S) (s : Chapter05BaseClosedPoint S) where
  index : Type u
  finiteIndex : Fintype index
  component : index → irreducibleComponents (f.fiber s.point)
  genericPoint : index → f.fiber s.point
  genericPoint_is_generic : ∀ i, IsGenericPoint (genericPoint i) (component i).1
  primeDivisor : index → Chapter05PrimeDivisor X
  primeDivisor_point : ∀ i,
    (primeDivisor i).point = f.fiberι s.point (genericPoint i)
  component_injective : Function.Injective component
  component_complete : ∀ C : irreducibleComponents (f.fiber s.point),
    ∃ i, component i = C

structure Chapter05FiberDivisorData
    {X S : Scheme.{u}} (f : X ⟶ S) (s : Chapter05BaseClosedPoint S)
    [IsIntegral X] [IsLocallyNoetherian X] where
  family : Chapter05FiberComponentFamily f s
  uniformizer : Chapter05PulledBackUniformizer f s
  multiplicity : family.index → ℕ
  multiplicity_positive : ∀ i, 0 < multiplicity i
  multiplicity_eq_order : ∀ i,
    (multiplicity i : ℤ) =
      AlgebraicGeometry.Scheme.ord uniformizer.rationalFunction
        (family.primeDivisor i).point

noncomputable def chapter05FiberDivisor
    {X S : Scheme.{u}} {f : X ⟶ S} {s : Chapter05BaseClosedPoint S}
    [IsIntegral X] [IsLocallyNoetherian X]
    (D : Chapter05FiberDivisorData f s) : Chapter05WeilDivisor X := by
  classical
  letI := D.family.finiteIndex
  exact ∑ i, Finsupp.single (D.family.primeDivisor i) (D.multiplicity i : ℤ)

theorem chapter05_fiberDivisor_eq_component_sum
    {X S : Scheme.{u}} {f : X ⟶ S} {s : Chapter05BaseClosedPoint S}
    [IsIntegral X] [IsLocallyNoetherian X]
    (D : Chapter05FiberDivisorData f s) :
    letI := D.family.finiteIndex
    chapter05FiberDivisor D =
      ∑ i, Finsupp.single (D.family.primeDivisor i) (D.multiplicity i : ℤ) := by
  rfl

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter05
