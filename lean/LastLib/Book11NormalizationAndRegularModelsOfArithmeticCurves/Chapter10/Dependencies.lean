import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.MvPolynomial
import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.RingTheory.TensorProduct.Basic
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.Section01PullbackOfPositivity
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.Section03DescentOfAmplenessAndProjectivity
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.Dependencies
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.Section04ProofsOfPrincipalCases
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11.Section01TheoremAndHypotheses
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.Dependencies
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter02.Section04BirationalInvarianceAndComponents
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter03.Core
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04.Dependencies
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.Section04LocalityAndProjectivity
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter08.Dependencies

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter10

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter02
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter03
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter08
open scoped AlgebraicGeometry BigOperators TensorProduct

universe u v

/-! ### Interfaces shared by the five sections -/

abbrev Chapter10FiniteFieldExtension (K K' : Type u) [Field K] [Field K'] [Algebra K K'] : Prop :=
  FiniteDimensional K K'

theorem chapter10_finiteFieldExtension_iff (K K' : Type u) [Field K] [Field K']
    [Algebra K K'] :
    Chapter10FiniteFieldExtension K K' ↔ FiniteDimensional K K' :=
  Iff.rfl

structure Chapter10ExcellentDedekindBase (S : Scheme.{u}) (K : Type u) [Field K]
    extends Chapter01GenericPointData S K where
  excellentDedekind : Chapter03ExcellentDedekindScheme S

noncomputable def chapter10BaseExtensionMap {S : Scheme.{u}} {K K' : Type u}
    [Field K] [Field K'] [Algebra K K']
    (B : Chapter10ExcellentDedekindBase S K) :
    Spec (CommRingCat.of K') ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap K K')) ≫ B.genericPointMap

abbrev chapter10BaseChange {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S) : Scheme.{u} :=
  LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10BaseChange f p

abbrev chapter10BaseChangeToSource {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S) :
    chapter10BaseChange f p ⟶ X :=
  LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10BaseChangeToSource f p

abbrev chapter10BaseChangeToBase {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S) :
    chapter10BaseChange f p ⟶ T :=
  LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10BaseChangeMorphism f p

theorem chapter10_baseChange_condition {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S) :
    chapter10BaseChangeToSource f p ≫ f = chapter10BaseChangeToBase f p ≫ p := by
  exact LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10BaseChange_condition f p

def chapter10FieldBaseChange {X : Scheme.{u}} {k K : Type u} [Field k] [Field K]
    [Algebra k K] (f : X ⟶ Spec (CommRingCat.of k)) : Scheme.{u} :=
  pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))

abbrev Chapter10NormalScheme : ObjectProperty Scheme.{u} := Chapter01NormalScheme

abbrev Chapter10RegularScheme : ObjectProperty Scheme.{u} := Chapter04RegularScheme

def Chapter10ModelMorphismProperties {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Flat f ∧ IsProper f ∧ Chapter07IsProjectiveMorphism f

def Chapter10GeometricallyIntegral {X : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (CommRingCat.of k)) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K],
    IsIntegral (chapter10FieldBaseChange f (K := K))

def Chapter10GeometricallyNormal {X : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (CommRingCat.of k)) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K],
    Chapter10NormalScheme (chapter10FieldBaseChange f (K := K))

def Chapter10BaseChangeFailure (P : ObjectProperty Scheme.{u}) : Prop :=
  ∃ (X S T : Scheme.{u}) (f : X ⟶ S) (p : T ⟶ S),
    P X ∧ ¬ P (chapter10BaseChange f p)

def Chapter10DesiredGenericFiber {X S : Scheme.{u}} (f : X ⟶ S) (η : S) (C : Scheme.{u}) : Prop :=
  Nonempty (f.fiber η ≅ C)

/- LOCAL_DEPENDENCY_GUESS: the pinned Mathlib snapshot has affine reduction rings and scheme
properties, but no scheme-level reduction object with its universal property.  This is the
smallest reusable boundary needed to state the normalize-after-reduction operation below. -/
structure Chapter10ReductionData (Y : Scheme.{u}) where
  carrier : Scheme.{u}
  projection : carrier ⟶ Y
  closed : IsClosedImmersion projection
  reduced : IsReduced carrier
  universal : ∀ {Z : Scheme.{u}} (g : Z ⟶ Y), IsReduced Z →
    ∃ h : Z ⟶ carrier, h ≫ projection = g
  unique : ∀ {Z : Scheme.{u}} (g : Z ⟶ Y) (hZ : IsReduced Z)
    (h₁ h₂ : Z ⟶ carrier), h₁ ≫ projection = g → h₂ ≫ projection = g → h₁ = h₂

theorem chapter10_reduction_is_reduced {Y : Scheme.{u}} (R : Chapter10ReductionData Y) :
    IsReduced R.carrier := by
  exact R.reduced

structure Chapter10ValuationExtensionAt (K K' : Type u) [Field K] [Field K']
    [Algebra K K'] where
  baseValuation : Valuation K ℤᵐ⁰
  extensionValuation : Valuation K' ℤᵐ⁰
  extendsBase : ∀ x : K,
    extensionValuation (algebraMap K K' x) = baseValuation x

structure Chapter10DVRPointCorrespondence {S S' : Scheme.{u}} (ν : S' ⟶ S)
    {K K' : Type u} [Field K] [Field K'] [Algebra K K'] (s : S) where
  extensions : Type u
  extension : extensions → Chapter10ValuationExtensionAt K K'
  point : extensions → {x : S' // ν x = s}
  bijective : Function.Bijective point
  stalk_is_dvr : ∀ e, IsDiscreteValuationRing (S'.presheaf.stalk (point e.1))

structure Chapter10FiniteReducedAlgebra (K A : Type u) [Field K] [CommRing A]
    [Algebra K A] where
  finite : FiniteDimensional K A
  reduced : IsReduced A
  finiteMinimalPrimes : Finite (Chapter02MinimalPrime A)

structure Chapter10FiniteReducedAlgebraNormalizationData
    (A : Type u) [CommRing A] where
  index : Type u
  finite_index : Finite index
  factor : index → Chapter02MinimalPrime A
  factor_bijective : Function.Bijective factor
  factorField : index → CommRingCat
  factorFieldEquiv : ∀ i,
    factorField i ≅ CommRingCat.of (Chapter02ComponentFractionRing A (factor i))
  component : index → Scheme.{u}
  componentMap : ∀ i, component i ⟶ Spec (CommRingCat.of A)
  componentIntegral : ∀ i, IsIntegralHom (componentMap i)
  componentNormal : ∀ i, Chapter10NormalScheme (component i)
  carrier : Scheme.{u}
  decomposition : carrier ≅ ∐ i, component i
  map : carrier ⟶ Spec (CommRingCat.of A)
  decomposition_over_base : ∀ i,
    Sigma.ι (fun j => component j) i ≫ decomposition.inv ≫ map = componentMap i
  finite : IsFinite map

end
end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter10
