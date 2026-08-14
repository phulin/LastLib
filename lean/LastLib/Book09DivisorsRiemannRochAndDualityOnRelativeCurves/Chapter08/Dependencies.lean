import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Trace.Basic
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Section02RelativeEffectiveCartierDivisors

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10

noncomputable section

universe u v

/-!
Shared interfaces for Chapter 8.

The pinned Mathlib tree already supplies the function field of an integral
scheme, residue fields, Kähler differentials, finite morphisms, and linear
duals.  The records below only name the curve and finite-thickening data that
the residue construction uses.  In particular, no later chapter is imported
for a divisor, dualizing-sheaf, or duality interface.
-/

abbrev Chapter08FunctionField (X : Scheme.{u}) [IrreducibleSpace X] :=
  X.functionField

abbrev Chapter08ResidueField (X : Scheme.{u}) (x : X) := X.residueField x

def Chapter08ClosedPoint (X : Scheme.{u}) :=
  {x : X // IsClosed ({x} : Set X)}

/- A one-dimensional curve is used through the local condition needed by
the divisor and residue constructions: every closed-point stalk has
Krull dimension one.  This is a usable replacement for an unconstrained
proposition field and is implied by the usual pure-dimension-one
finite-type hypotheses. -/
def Chapter08PureDimensionOne (X : Scheme.{u}) : Prop :=
  ∀ x : Chapter08ClosedPoint X,
    ringKrullDim (X.presheaf.stalk x.1) = 1

structure Chapter08SmoothIntegralCurve (k : Type u) [Field k] where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ Spec (.of k)
  smooth : Smooth structureMap
  integral : IsIntegral carrier
  noetherian : IsNoetherian carrier
  dimensionOne : Chapter08PureDimensionOne carrier

/- The structure morphism induces the canonical map from the base field to a
closed residue field.  Keeping this map explicit is useful when a coefficient
field is chosen in a completed local ring: an arbitrary ring homomorphism is
not enough to say that the coefficient-field identification is over `k`. -/
noncomputable def chapter08ResidueFieldMap
    {k : Type u} [Field k]
    (C : Chapter08SmoothIntegralCurve k)
    (x : Chapter08ClosedPoint C.carrier) :
    k →+* C.carrier.residueField x.1 :=
  (((Scheme.ΓSpecIso (.of k)).inv ≫ C.structureMap.appTop ≫
    C.carrier.Γevaluation x.1).hom)

noncomputable instance chapter08StalkAlgebra
    {k : Type u} [Field k]
    (C : Chapter08SmoothIntegralCurve k)
    (x : Chapter08ClosedPoint C.carrier) :
    Algebra k (C.carrier.presheaf.stalk x.1) :=
  RingHom.toAlgebra
    (((Scheme.ΓSpecIso (.of k)).inv ≫ C.structureMap.appTop ≫
      C.carrier.presheaf.germ ⊤ x.1 (by simp)).hom)

instance {k : Type u} [Field k] (C : Chapter08SmoothIntegralCurve k) :
    Smooth C.structureMap := C.smooth

instance {k : Type u} [Field k] (C : Chapter08SmoothIntegralCurve k) :
    IsIntegral C.carrier := C.integral

structure Chapter08ProperGeometricallyConnectedCurve (k : Type u) [Field k]
    extends Chapter08SmoothIntegralCurve k where
  proper : IsProper structureMap
  geometricallyConnected : GeometricallyConnected structureMap

instance {k : Type u} [Field k] (C : Chapter08ProperGeometricallyConnectedCurve k) :
    Smooth C.structureMap := C.toChapter08SmoothIntegralCurve.smooth

instance {k : Type u} [Field k] (C : Chapter08ProperGeometricallyConnectedCurve k) :
    IsIntegral C.carrier := C.toChapter08SmoothIntegralCurve.integral

instance {k : Type u} [Field k] (C : Chapter08ProperGeometricallyConnectedCurve k) :
    IsProper C.structureMap := C.proper

instance {k : Type u} [Field k] (C : Chapter08ProperGeometricallyConnectedCurve k) :
    GeometricallyConnected C.structureMap := C.geometricallyConnected

/- A proper smooth integral curve is enough for the finite-map trace theorem.
   Geometric connectedness is needed for the global residue theorem above, but
   not for finite trace or its local residue formula. -/
structure Chapter08ProperSmoothIntegralCurve (k : Type u) [Field k]
    extends Chapter08SmoothIntegralCurve k where
  proper : IsProper structureMap

instance {k : Type u} [Field k] (C : Chapter08ProperSmoothIntegralCurve k) :
    Smooth C.structureMap := C.toChapter08SmoothIntegralCurve.smooth

instance {k : Type u} [Field k] (C : Chapter08ProperSmoothIntegralCurve k) :
    IsIntegral C.carrier := C.toChapter08SmoothIntegralCurve.integral

instance {k : Type u} [Field k] (C : Chapter08ProperSmoothIntegralCurve k) :
    IsProper C.structureMap := C.proper

def Chapter08RegularAt
    {k : Type u} [Field k]
    (C : Chapter08SmoothIntegralCurve k)
    (x : Chapter08ClosedPoint C.carrier)
    (f : C.carrier.functionField) : Prop :=
  f ∈ Set.range
    (algebraMap (C.carrier.presheaf.stalk x.1) C.carrier.functionField)

def Chapter08UnitAt
    {k : Type u} [Field k]
    (C : Chapter08SmoothIntegralCurve k)
    (x : Chapter08ClosedPoint C.carrier)
    (f : C.carrier.functionField) : Prop :=
    ∃ s : C.carrier.presheaf.stalk x.1,
    IsUnit s ∧ algebraMap (C.carrier.presheaf.stalk x.1) C.carrier.functionField s = f

def Chapter08UniformizerAt
    {k : Type u} [Field k]
    (C : Chapter08SmoothIntegralCurve k)
    (x : Chapter08ClosedPoint C.carrier)
    (f : C.carrier.functionField) : Prop :=
  ∃ s : C.carrier.presheaf.stalk x.1,
    algebraMap (C.carrier.presheaf.stalk x.1) C.carrier.functionField s = f ∧
      Ideal.span ({s} : Set (C.carrier.presheaf.stalk x.1)) =
        IsLocalRing.maximalIdeal (C.carrier.presheaf.stalk x.1) ∧
      IsRegular s

structure Chapter08PointIdeal
    {k : Type u} [Field k]
    (C : Chapter08SmoothIntegralCurve k)
    (x : Chapter08ClosedPoint C.carrier) where
  ideal : Chapter09ClosedSubscheme C.carrier
  supportedAt : (ideal.support : Set C.carrier) = {x.1}
  closed : IsClosedImmersion ideal.subschemeι

/- A structure map to `Spec k` canonically induces the displayed algebra on
the generic stalk.  The wrapper keeps the book-facing dependency explicit,
while the instance immediately below uses the pinned scheme maps. -/
class Chapter08FunctionFieldAlgebra (k : Type u) [Field k] (X : Scheme.{v})
    [IsIntegral X] where
  toAlgebra : Algebra k X.functionField

attribute [instance_reducible] Chapter08FunctionFieldAlgebra.toAlgebra
attribute [instance] Chapter08FunctionFieldAlgebra.toAlgebra

noncomputable instance chapter08FunctionFieldAlgebraCanonical
    {k : Type u} [Field k]
    (C : Chapter08SmoothIntegralCurve k) :
    Chapter08FunctionFieldAlgebra k C.carrier where
  toAlgebra := by
    letI : Nonempty (⊤ : C.carrier.Opens) := by
      rcases C.integral.nonempty with ⟨x⟩
      exact ⟨⟨x, by simp⟩⟩
    apply RingHom.toAlgebra
    exact (((Scheme.ΓSpecIso (.of k)).inv ≫ C.structureMap.appTop ≫
      C.carrier.germToFunctionField ⊤).hom)

abbrev Chapter08RationalDifferentials (k : Type u) [Field k] (X : Scheme.{v})
    [IsIntegral X] [Algebra k X.functionField] :=
  Ω[X.functionField⁄k]

/- The generic separability of a finite map is a property of the induced
function-field extension.  Store the extension itself, rather than an
unconstrained proposition flag, so later trace constructions can recover
the finite and separable hypotheses they need. -/
structure Chapter08FiniteSeparableFieldExtension
    (F E : Type v) [Field F] [Field E] where
  [algebra : Algebra F E]
  finite : FiniteDimensional F E
  separable : Algebra.IsSeparable F E

def Chapter08FiniteSeparableFieldExtension.toAlgebraMap
    {F E : Type v} [Field F] [Field E]
    (L : Chapter08FiniteSeparableFieldExtension F E) : F →+* E :=
  @algebraMap F E _ _ L.algebra

noncomputable instance chapter08TopNonemptyOfIntegral
    (X : Scheme.{u}) [IsIntegral X] : Nonempty (⊤ : X.Opens) := by
  rcases (inferInstance : IsIntegral X).nonempty with ⟨x⟩
  exact ⟨⟨x, by simp⟩⟩

/- A scheme morphism between integral schemes induces a map on their generic
stalks.  The global-section compatibility below records that map against the
canonical `germToFunctionField` maps, rather than introducing an unrelated
ring hom with the same source and target. -/
structure Chapter08InducedFunctionFieldMap
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) where
  map : Y.functionField →+* X.functionField
  map_from_generic_stalk :
    Spec.map (CommRingCat.ofHom map) ≫ Y.fromSpecStalk (genericPoint Y) =
      X.fromSpecStalk (genericPoint X) ≫ f
  map_global_sections :
    ∀ s : Γ(Y, ⊤),
      map (Y.germToFunctionField ⊤ s) =
        X.germToFunctionField ⊤ (f.appTop s)

structure Chapter08FiniteMapOfCurves (k : Type u) [Field k] where
  source : Chapter08SmoothIntegralCurve k
  target : Chapter08SmoothIntegralCurve k
  hom : source.carrier ⟶ target.carrier
  finite : IsFinite hom
  dominant : IsDominant hom
  functionFieldExtension :
    Chapter08FiniteSeparableFieldExtension
      target.carrier.functionField source.carrier.functionField
  functionFieldMap : Chapter08InducedFunctionFieldMap hom
  functionFieldMap_eq_extension :
    functionFieldMap.map = functionFieldExtension.toAlgebraMap
  functionFieldExtension_overBase :
    ∀ a : k,
      algebraMap k source.carrier.functionField a =
        functionFieldExtension.toAlgebraMap
          (algebraMap k target.carrier.functionField a)
  overBase : hom ≫ target.structureMap = source.structureMap

noncomputable instance chapter08FiniteMapOfCurvesAlgebra
    {k : Type u} [Field k]
    (π : Chapter08FiniteMapOfCurves k) :
    Algebra π.target.carrier.functionField π.source.carrier.functionField :=
  π.functionFieldExtension.algebra

structure Chapter08FiniteMapOfProperCurves (k : Type u) [Field k] where
  source : Chapter08ProperSmoothIntegralCurve k
  target : Chapter08ProperSmoothIntegralCurve k
  hom : source.carrier ⟶ target.carrier
  finite : IsFinite hom
  dominant : IsDominant hom
  functionFieldExtension :
    Chapter08FiniteSeparableFieldExtension
      target.carrier.functionField source.carrier.functionField
  functionFieldMap : Chapter08InducedFunctionFieldMap hom
  functionFieldMap_eq_extension :
    functionFieldMap.map = functionFieldExtension.toAlgebraMap
  functionFieldExtension_overBase :
    ∀ a : k,
      algebraMap k source.carrier.functionField a =
        functionFieldExtension.toAlgebraMap
          (algebraMap k target.carrier.functionField a)
  overBase : hom ≫ target.structureMap = source.structureMap

noncomputable instance chapter08FiniteMapOfProperCurvesAlgebra
    {k : Type u} [Field k]
    (π : Chapter08FiniteMapOfProperCurves k) :
    Algebra π.target.carrier.functionField π.source.carrier.functionField :=
  π.functionFieldExtension.algebra

structure Chapter08ProjectiveLineFunctionFieldData
    (k : Type u) [Field k]
    (C : Chapter08ProperGeometricallyConnectedCurve k)
    (f : C.carrier ⟶ chapter04ProjectiveLine k) where
  functionField : Type u
  [functionFieldField : Field functionField]
  [functionFieldAlgebra : Algebra k functionField]
  globalSectionsMap : Γ(chapter04ProjectiveLine k, ⊤) →+* functionField
  genericMap : Spec (.of functionField) ⟶ chapter04ProjectiveLine k
  genericMap_overBase :
    genericMap ≫ chapter04ProjectiveLineStructureMap k =
      Spec.map (CommRingCat.ofHom (algebraMap k functionField))
  map : functionField →+* C.carrier.functionField
  dominant : IsDominant f
  map_from_generic_stalk :
    Spec.map (CommRingCat.ofHom map) ≫ genericMap =
      C.carrier.fromSpecStalk (genericPoint C.carrier) ≫ f
  map_global_sections :
    ∀ s : Γ(chapter04ProjectiveLine k, ⊤),
      map (globalSectionsMap s) = C.carrier.germToFunctionField ⊤ (f.appTop s)
  globalSectionsMap_overBase :
    ∀ a : k,
      globalSectionsMap
          ((((Scheme.ΓSpecIso (.of k)).inv ≫
            (chapter04ProjectiveLineStructureMap k).appTop).hom) a) =
        algebraMap k functionField a
  extension :
    Chapter08FiniteSeparableFieldExtension functionField C.carrier.functionField
  map_eq_extension : map = extension.toAlgebraMap
  extension_overBase :
    ∀ a : k,
      extension.toAlgebraMap (algebraMap k functionField a) =
        algebraMap k C.carrier.functionField a

structure Chapter08FiniteMapToProjectiveLine (k : Type u) [Field k]
    (C : Chapter08ProperGeometricallyConnectedCurve k) where
  element : C.carrier.functionField
  hom : C.carrier ⟶ chapter04ProjectiveLine k
  finite : IsFinite hom
  dominant : IsDominant hom
  functionFieldMap : Chapter08ProjectiveLineFunctionFieldData k C hom
  overBase :
    hom ≫ chapter04ProjectiveLineStructureMap k =
      C.structureMap

/-!
Mathlib's pinned algebraic-geometry layer has no single public predicate for
“a Cohen–Macaulay curve”.  This is the minimal chapter-facing package needed
for the final finite-duality warning; its fields are hypotheses, not axioms.
-/
/- In relative dimension one, Cohen--Macaulayness at the closed points is
equivalent to the existence of a regular element in the maximal ideal of
each noetherian one-dimensional local stalk. -/
def Chapter08LocallyCohenMacaulayAtClosedPoints (X : Scheme.{u}) : Prop :=
  ∀ x : Chapter08ClosedPoint X,
    ∃ t : X.presheaf.stalk x.1,
      IsRegular t ∧ t ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x.1)

structure Chapter08CohenMacaulayCurve (k : Type u) [Field k] where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ Spec (.of k)
  proper : IsProper structureMap
  locallyNoetherian : IsNoetherian carrier
  pureDimensionOne : Chapter08PureDimensionOne carrier
  locallyCohenMacaulay : Chapter08LocallyCohenMacaulayAtClosedPoints carrier

/- Local dependency guess: the earlier chapters expose effective Cartier
divisors and ideal powers, but not yet the canonical ideal of a closed point
as a divisor. -/
structure Chapter08PointThickening (k : Type u) [Field k]
    (C : Chapter08SmoothIntegralCurve k)
    (x : Chapter08ClosedPoint C.carrier) (n : ℕ) where
  divisor : Chapter09EffectiveCartierDivisor C.carrier
  supportedAt : (divisor.ideal.support : Set C.carrier) = {x.1}
  pointIdeal : Chapter08PointIdeal C x
  pointIdeal_eq_canonical :
    pointIdeal.ideal =
      Scheme.IdealSheafData.vanishingIdeal
        (⟨{x.1}, x.2⟩ : TopologicalSpace.Closeds C.carrier)
  pointIdealEffective : Chapter09EffectiveCartierDivisor C.carrier
  pointIdealEffective_ideal : pointIdealEffective.ideal = pointIdeal.ideal
  nthIdeal_eq_pow : divisor.ideal = pointIdeal.ideal ^ n
  finiteOverBase : IsFinite (divisor.ideal.subschemeι ≫ C.structureMap)
  nonzeroOrder : 0 < n

abbrev Chapter08ThickeningScheme
    {k : Type u} [Field k]
    {C : Chapter08SmoothIntegralCurve k}
    {x : Chapter08ClosedPoint C.carrier} {n : ℕ}
    (T : Chapter08PointThickening k C x n) := T.divisor.ideal.subscheme

abbrev Chapter08ThickeningSections
    {k : Type u} [Field k]
    {C : Chapter08SmoothIntegralCurve k}
    {x : Chapter08ClosedPoint C.carrier} {n : ℕ}
    (T : Chapter08PointThickening k C x n) := Γ(Chapter08ThickeningScheme T, ⊤)

/- The global-sections algebra comes from the structure map of the finite
thickening.  The class is a stable book-facing name for the canonical map
constructed immediately below. -/
class Chapter08ThickeningSectionsAlgebra
    {k : Type u} [Field k]
    {C : Chapter08SmoothIntegralCurve k}
    {x : Chapter08ClosedPoint C.carrier} {n : ℕ}
    (T : Chapter08PointThickening k C x n) where
  toAlgebra : Algebra k (Chapter08ThickeningSections T)

attribute [instance_reducible] Chapter08ThickeningSectionsAlgebra.toAlgebra
attribute [instance] Chapter08ThickeningSectionsAlgebra.toAlgebra

noncomputable instance chapter08ThickeningSectionsAlgebraCanonical
    {k : Type u} [Field k]
    {C : Chapter08SmoothIntegralCurve k}
    {x : Chapter08ClosedPoint C.carrier} {n : ℕ}
    (T : Chapter08PointThickening k C x n) :
    Chapter08ThickeningSectionsAlgebra T where
  toAlgebra := by
    apply RingHom.toAlgebra
    exact (((Scheme.ΓSpecIso (.of k)).inv ≫
      (T.divisor.ideal.subschemeι ≫ C.structureMap).appTop).hom)

abbrev Chapter08ThickeningDual
    {k : Type u} [Field k]
    {C : Chapter08SmoothIntegralCurve k}
    {x : Chapter08ClosedPoint C.carrier} {n : ℕ}
    (T : Chapter08PointThickening k C x n) [Algebra k (Chapter08ThickeningSections T)] :=
  Chapter08ThickeningSections T →ₗ[k] k

abbrev Chapter08StructureSheaf (X : Scheme.{u}) :=
  SheafOfModules.unit X.ringCatSheaf

abbrev Chapter08CartierOminusNX
    {k : Type u} [Field k]
    {C : Chapter08SmoothIntegralCurve k}
    {x : Chapter08ClosedPoint C.carrier} {n : ℕ}
    (T : Chapter08PointThickening k C x n) : C.carrier.Modules :=
  chapter10CartierOminusD T.divisor

abbrev Chapter08CartierQuotient
    {k : Type u} [Field k]
    {C : Chapter08SmoothIntegralCurve k}
    {x : Chapter08ClosedPoint C.carrier} {n : ℕ}
    (T : Chapter08PointThickening k C x n) : C.carrier.Modules :=
  chapter10CartierQuotientModule T.divisor

abbrev Chapter08CartierInclusion
    {k : Type u} [Field k]
    {C : Chapter08SmoothIntegralCurve k}
    {x : Chapter08ClosedPoint C.carrier} {n : ℕ}
    (T : Chapter08PointThickening k C x n) :
    Chapter08CartierOminusNX T ⟶ Chapter08StructureSheaf C.carrier :=
  chapter10CartierInclusion T.divisor

abbrev Chapter08CartierQuotientMap
    {k : Type u} [Field k]
    {C : Chapter08SmoothIntegralCurve k}
    {x : Chapter08ClosedPoint C.carrier} {n : ℕ}
    (T : Chapter08PointThickening k C x n) :
    Chapter08StructureSheaf C.carrier ⟶ Chapter08CartierQuotient T :=
  chapter10CartierQuotient T.divisor

abbrev Chapter08CartierExactSequence
    {k : Type u} [Field k]
    {C : Chapter08SmoothIntegralCurve k}
    {x : Chapter08ClosedPoint C.carrier} {n : ℕ}
    (T : Chapter08PointThickening k C x n) :=
  Chapter10CartierExactSequence T.divisor

structure Chapter08FiniteDualityData
    (A B ωA ωB : Type u)
    [CommRing A] [CommRing B] [AddCommGroup ωA] [AddCommGroup ωB]
    [Algebra A B] [Module A ωA] [Module B ωB] [Module A ωB]
    [IsScalarTower A B ωB]
    [Module B (B →ₗ[A] ωA)]
    [IsScalarTower A B (B →ₗ[A] ωA)] where
  finite : Module.Finite A B
  identification : ωB ≃ₗ[B] (B →ₗ[A] ωA)

abbrev Chapter08FiniteRelativeDualizingModule
    (A B ωA : Type u) [CommRing A] [CommRing B] [AddCommGroup ωA]
    [Algebra A B] [Module A ωA] := B →ₗ[A] ωA

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08
