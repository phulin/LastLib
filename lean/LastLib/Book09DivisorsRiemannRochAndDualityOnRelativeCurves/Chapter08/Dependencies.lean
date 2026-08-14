import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Trace.Basic
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09

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

structure Chapter08SmoothIntegralCurve (k : Type u) [Field k] where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ Spec (.of k)
  smooth : Smooth structureMap
  integral : IsIntegral carrier
  dimensionOne : Prop

instance (C : Chapter08SmoothIntegralCurve k) : Smooth C.structureMap := C.smooth

instance (C : Chapter08SmoothIntegralCurve k) : IsIntegral C.carrier := C.integral

structure Chapter08ProperGeometricallyConnectedCurve (k : Type u) [Field k]
    extends Chapter08SmoothIntegralCurve k where
  proper : IsProper structureMap
  geometricallyConnected : GeometricallyConnected structureMap

instance (C : Chapter08ProperGeometricallyConnectedCurve k) :
    Smooth C.structureMap := C.toChapter08SmoothIntegralCurve.smooth

instance (C : Chapter08ProperGeometricallyConnectedCurve k) :
    IsIntegral C.carrier := C.toChapter08SmoothIntegralCurve.integral

instance (C : Chapter08ProperGeometricallyConnectedCurve k) :
    IsProper C.structureMap := C.proper

instance (C : Chapter08ProperGeometricallyConnectedCurve k) :
    GeometricallyConnected C.structureMap := C.geometricallyConnected

def Chapter08RegularAt
    (C : Chapter08SmoothIntegralCurve k)
    (x : Chapter08ClosedPoint C.carrier)
    (f : C.carrier.functionField) : Prop :=
  f ∈ Set.range
    (algebraMap (C.carrier.presheaf.stalk x.1) C.carrier.functionField)

def Chapter08UnitAt
    (C : Chapter08SmoothIntegralCurve k)
    (x : Chapter08ClosedPoint C.carrier)
    (f : C.carrier.functionField) : Prop :=
  ∃ s : C.carrier.presheaf.stalk x.1,
    IsUnit s ∧ algebraMap (C.carrier.presheaf.stalk x.1) C.carrier.functionField s = f

/- A structure map to `Spec k` canonically induces the displayed algebra on
the generic stalk.  The wrapper keeps the book-facing dependency explicit,
while the instance immediately below uses the pinned scheme maps. -/
class Chapter08FunctionFieldAlgebra (k : Type u) [Field k] (X : Scheme.{v})
    [IsIntegral X] where
  toAlgebra : Algebra k X.functionField

attribute [instance] Chapter08FunctionFieldAlgebra.toAlgebra

noncomputable instance chapter08FunctionFieldAlgebraCanonical
    (C : Chapter08SmoothIntegralCurve k) :
    Chapter08FunctionFieldAlgebra k C.carrier where
  toAlgebra := by
    apply RingHom.toAlgebra
    exact (((Scheme.ΓSpecIso (.of k)).inv ≫ C.structureMap.appTop ≫
      C.carrier.germToFunctionField ⊤).hom)

abbrev Chapter08RationalDifferentials (k : Type u) (X : Scheme.{v})
    [IsIntegral X] [Algebra k X.functionField] :=
  Ω[X.functionField⁄k]

structure Chapter08FiniteMapOfCurves (k : Type u) [Field k] where
  source : Chapter08SmoothIntegralCurve k
  target : Chapter08SmoothIntegralCurve k
  hom : source.carrier ⟶ target.carrier
  finite : IsFinite hom
  genericallySeparable : Prop
  overBase : hom ≫ target.structureMap = source.structureMap

structure Chapter08FiniteMapOfProperCurves (k : Type u) [Field k] where
  source : Chapter08ProperGeometricallyConnectedCurve k
  target : Chapter08ProperGeometricallyConnectedCurve k
  hom : source.carrier ⟶ target.carrier
  finite : IsFinite hom
  genericallySeparable : Prop
  overBase : hom ≫ target.structureMap = source.structureMap

/-!
Mathlib's pinned algebraic-geometry layer has no single public predicate for
“a Cohen–Macaulay curve”.  This is the minimal chapter-facing package needed
for the final finite-duality warning; its fields are hypotheses, not axioms.
-/
structure Chapter08CohenMacaulayCurve where
  carrier : Scheme.{u}
  locallyNoetherian : Prop
  pureDimensionOne : Prop
  locallyCohenMacaulay : Prop

/- Local dependency guess: the earlier chapters expose effective Cartier
divisors and ideal powers, but not yet the canonical ideal of a closed point
as a divisor. -/
structure Chapter08PointThickening (k : Type u) [Field k]
    (C : Chapter08SmoothIntegralCurve k)
    (x : Chapter08ClosedPoint C.carrier) (n : ℕ) where
  divisor : Chapter09EffectiveCartierDivisor C.carrier
  supportedAt : (divisor.ideal.support : Set C.carrier) = {x.1}
  pointIdeal : Chapter09ClosedSubscheme C.carrier
  pointIdealEffective : Chapter09EffectiveCartierDivisor C.carrier
  pointIdealEffective_ideal : pointIdealEffective.ideal = pointIdeal
  nthIdeal_eq_pow : divisor.ideal = pointIdeal ^ n
  finiteOverBase : IsFinite (divisor.ideal.subschemeι ≫ C.structureMap)
  nonzeroOrder : 0 < n

abbrev Chapter08ThickeningScheme
    (T : Chapter08PointThickening k C x n) := T.divisor.ideal.subscheme

abbrev Chapter08ThickeningSections
    (T : Chapter08PointThickening k C x n) := Γ(Chapter08ThickeningScheme T, ⊤)

/- The global-sections algebra comes from the structure map of the finite
thickening.  The class is a stable book-facing name for the canonical map
constructed immediately below. -/
class Chapter08ThickeningSectionsAlgebra
    (T : Chapter08PointThickening k C x n) where
  toAlgebra : Algebra k (Chapter08ThickeningSections T)

attribute [instance] Chapter08ThickeningSectionsAlgebra.toAlgebra

noncomputable instance chapter08ThickeningSectionsAlgebraCanonical
    (T : Chapter08PointThickening k C x n) :
    Chapter08ThickeningSectionsAlgebra T where
  toAlgebra := by
    apply RingHom.toAlgebra
    exact (((Scheme.ΓSpecIso (.of k)).inv ≫
      (T.divisor.ideal.subschemeι ≫ C.structureMap).appTop).hom)

abbrev Chapter08ThickeningDual
    (T : Chapter08PointThickening k C x n) [Algebra k (Chapter08ThickeningSections T)] :=
  Chapter08ThickeningSections T →ₗ[k] k

abbrev Chapter08StructureSheaf (X : Scheme.{u}) :=
  SheafOfModules.unit X.ringCatSheaf

structure Chapter08CartierExactSequence (T : Chapter08PointThickening k C x n) where
  complex : ShortComplex C.carrier.Modules
  idealTwist : C.carrier.Modules
  thickeningSheaf : C.carrier.Modules
  idealTwistIso : complex.X₁ ≅ idealTwist
  structureSheafIso : complex.X₂ ≅ Chapter08StructureSheaf C.carrier
  thickeningSheafIso : complex.X₃ ≅ thickeningSheaf
  left_mono : Mono complex.f
  right_epi : Epi complex.g
  exact : complex.Exact

structure Chapter08FiniteDualityData
    (A B ωA ωB : Type u)
    [CommRing A] [CommRing B] [AddCommGroup ωA] [AddCommGroup ωB]
    [Algebra A B] [Module A ωA] [Module B ωB] [Module A ωB] where
  finite : Module.Finite A B
  relativeDualizingModule : Type u
  [relativeDualizingAddCommGroup : AddCommGroup relativeDualizingModule]
  [relativeDualizingModuleB : Module B relativeDualizingModule]
  [relativeDualizingModuleA : Module A relativeDualizingModule]
  [homModuleB : Module B (B →ₗ[A] ωA)]
  identification : ωB ≃ₗ[B] relativeDualizingModule
  homDescription : relativeDualizingModule ≃ₗ[B] (B →ₗ[A] ωA)

abbrev Chapter08FiniteRelativeDualizingModule
    (A B ωA : Type u) [CommRing A] [CommRing B] [AddCommGroup ωA]
    [Algebra A B] [Module A ωA] := B →ₗ[A] ωA

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08
