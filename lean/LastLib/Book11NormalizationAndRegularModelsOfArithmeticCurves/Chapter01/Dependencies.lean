import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.MvPolynomial
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Topology.KrullDimension
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.Section01FromOneLocalRingToSeveral
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Dependencies
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01.Section01TheAbsoluteAndRelativeSettings
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.Dependencies

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10
open scoped AlgebraicGeometry TensorProduct

universe u v

/-! ### Basic scheme-theoretic interfaces -/

/- Finite type is written out because the source distinguishes it from finite
presentation and because the two factors are useful independently later. -/
def Chapter01FiniteType {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  LocallyOfFiniteType f ∧ QuasiCompact f

abbrev chapter01BaseChange {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) : Scheme.{u} :=
  pullback f g

abbrev chapter01GenericFiber {X S : Scheme.{u}} {K : Type u} [Field K]
    (f : X ⟶ S) (η : Spec (CommRingCat.of K) ⟶ S) : Scheme.{u} :=
  chapter01BaseChange f η

/- The pure-dimension-one convention is reused from the earlier relative-curve chapter. -/
abbrev Chapter01PureDimensionOne : ObjectProperty Scheme.{u} :=
  LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01.Chapter01PureDimensionOne

def Chapter01PureDimensionTwo : ObjectProperty Scheme.{u} :=
  fun X => ∀ Z : irreducibleComponents X,
    topologicalKrullDim Z.1 = (2 : WithBot ℕ∞)

def Chapter01RelativeDimensionOne {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  geometrically Chapter01PureDimensionOne f

/-! ### Normality and regularity -/

def Chapter01NormalRing (R : Type u) [CommRing R] : Prop :=
  IsDomain R ∧ IsIntegrallyClosed R

def Chapter01NormalLocalRing (R : Type u) [CommRing R] : Prop :=
  IsLocalRing R ∧ Chapter01NormalRing R

def Chapter01NormalScheme (X : Scheme.{u}) : Prop :=
  ∀ x : X, Chapter01NormalLocalRing (X.presheaf.stalk x)

def Chapter01ArithmeticSurface {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  IsIntegral X ∧ Chapter01NormalScheme X ∧ Flat f ∧
    Chapter01FiniteType f ∧ Chapter01RelativeDimensionOne f ∧
      Chapter01PureDimensionTwo X

abbrev Chapter01RegularLocalRing (R : Type u) [CommRing R] : Prop :=
  IsRegularLocalRing R

abbrev Chapter01RegularRing (R : Type u) [CommRing R] : Prop :=
  IsRegularRing R

def Chapter01RegularScheme (X : Scheme.{u}) : Prop :=
  ∀ x : X, Chapter01RegularLocalRing (X.presheaf.stalk x)

abbrev Chapter01NoetherianScheme (X : Scheme.{u}) : Prop :=
  IsNoetherian X

def Chapter01DedekindScheme (S : Scheme.{u}) : Prop :=
  IsNoetherian S ∧ ∀ U : S.affineOpens, IsDedekindDomain Γ(S, U)

/-! ### Finiteness hypotheses for normalization -/

abbrev Chapter01IntegralClosure (A L : Type u) [CommRing A] [CommRing L] [Algebra A L] :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11IntegralClosure A L

abbrev Chapter01NormalizationFinite (A L : Type u) [CommRing A] [CommRing L] [Algebra A L] : Prop :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11NormalizationFinite A L

abbrev Chapter01Japanese (R : Type u) [CommRing R] [IsDomain R] : Prop :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.Chapter11Japanese R

/- LOCAL_DEPENDENCY_GUESS: the pinned Mathlib snapshot has no catenary or
excellent-ring API.  These definitions keep the three conditions in the
source's excellence package explicit at the Chapter 1 boundary. -/
structure Chapter01SaturatedPrimeChain (A : Type u) [CommRing A]
    (p q : PrimeSpectrum A) where
  length : ℕ
  chain : Fin (length + 1) → PrimeSpectrum A
  first : chain 0 = p
  last : chain ⟨length, Nat.lt_succ_self length⟩ = q
  strict : ∀ i : Fin length, chain i.castSucc < chain i.succ
  saturated : ∀ i : Fin length,
    ¬ ∃ r : PrimeSpectrum A, chain i.castSucc < r ∧ r < chain i.succ

def Chapter01Catenary (A : Type u) [CommRing A] : Prop :=
  ∀ (p q : PrimeSpectrum A), p ≤ q →
    ∀ (c d : Chapter01SaturatedPrimeChain A p q), c.length = d.length

def Chapter01UniversallyCatenary (A : Type u) [CommRing A] : Prop :=
  ∀ (B : Type u) [CommRing B] [Algebra A B] [Algebra.FiniteType A B],
    Chapter01Catenary B

abbrev chapter01FormalFiber (A : Type u) [CommRing A] (p : PrimeSpectrum A) : Type u :=
  letI : p.asIdeal.IsPrime := p.isPrime
  p.asIdeal.ResidueField ⊗[Localization.AtPrime p.asIdeal]
    AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
      (Localization.AtPrime p.asIdeal)

def Chapter01GeometricallyRegularAlgebra
    (k B : Type u) [Field k] [CommRing B] [Algebra k B] : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K],
    IsRegularRing (B ⊗[k] K)

def Chapter01GeometricallyRegularFormalFibers (A : Type u) [CommRing A] : Prop :=
  ∀ p : PrimeSpectrum A,
    letI : p.asIdeal.IsPrime := p.isPrime
    Chapter01GeometricallyRegularAlgebra p.asIdeal.ResidueField
      (chapter01FormalFiber A p)

def chapter01RegularLocus (B : Type u) [CommRing B] : Set (PrimeSpectrum B) :=
  {p | letI : p.asIdeal.IsPrime := p.isPrime
    IsRegularLocalRing (Localization.AtPrime p.asIdeal)}

def Chapter01RegularLocusOpen (A : Type u) [CommRing A] : Prop :=
  ∀ (B : Type u) [CommRing B] [Algebra A B] [Algebra.FiniteType A B],
    IsOpen (chapter01RegularLocus B)

class Chapter01Nagata (R : Type u) [CommRing R] : Prop where
  noetherian : IsNoetherianRing R
  japanese_quotient : ∀ (p : Ideal R) [p.IsPrime],
    Chapter01Japanese (R ⧸ p)

class Chapter01ExcellentRing (R : Type u) [CommRing R] : Prop where
  noetherian : IsNoetherianRing R
  universallyCatenary : Chapter01UniversallyCatenary R
  geometricallyRegularFormalFibers : Chapter01GeometricallyRegularFormalFibers R
  regularLocusOpen : Chapter01RegularLocusOpen R

def Chapter01ExcellentScheme (X : Scheme.{u}) : Prop :=
  IsNoetherian X ∧ ∀ U : X.affineOpens, Chapter01ExcellentRing Γ(X, U)

/-! ### Morphism properties used by the chapter -/

abbrev Chapter01SmoothMorphism {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Smooth f

abbrev Chapter01ProperMorphism {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  IsProper f

abbrev Chapter01ProjectiveMorphism {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  chapter04Projective f

abbrev Chapter01GeometricallyRegularFiber {X S : Scheme.{u}}
    (f : X ⟶ S) (s : S) : Prop :=
  chapter10GeometricallyRegularFiber f s

abbrev Chapter01GeometricallyRegularFibers {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  chapter10GeometricallyRegularFibers f

structure Chapter01SmoothMorphismData {X S : Scheme.{u}} (f : X ⟶ S) : Prop where
  locallyOfFinitePresentation : LocallyOfFinitePresentation f
  flat : Flat f
  geometricallyRegularFibers : Chapter01GeometricallyRegularFibers f

/-! ### Birational and generic-fiber bookkeeping -/

structure Chapter01BirationalWitness {X Y : Scheme.{u}} (f : X ⟶ Y) where
  sourceIntegral : IsIntegral X
  targetIntegral : IsIntegral Y
  denseOpen : Y.Opens
  dense : Dense (denseOpen : Set Y)
  restrictionIsIso : IsIso (f ∣_ denseOpen)

def Chapter01Birational {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  Nonempty (Chapter01BirationalWitness f)

def Chapter01ProperBirational {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  Chapter01ProperMorphism f ∧ Chapter01Birational f

structure Chapter01GenericPointData (S : Scheme.{u}) (K : Type u) [Field K] where
  noetherian : Chapter01NoetherianScheme S
  integral : IsIntegral S
  η : S
  η_is_generic : IsGenericPoint η Set.univ
  residueFieldIso : CommRingCat.of K ≅ S.residueField η
  genericPointMap : Spec (CommRingCat.of K) ⟶ S
  genericPointMap_eq : genericPointMap (genericPoint (Spec (CommRingCat.of K))) = η
  genericPointMap_is_residueFieldMap :
    genericPointMap = Spec.map residueFieldIso.inv ≫ S.fromSpecResidueField η

abbrev Chapter01IntegralBase := Chapter01GenericPointData

structure Chapter01DedekindBase (S : Scheme.{u}) (K : Type u) [Field K]
    extends Chapter01GenericPointData S K where
  dedekind : Chapter01DedekindScheme S

structure Chapter01Model {S C : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter01IntegralBase S K) (c : C ⟶ Spec (CommRingCat.of K)) where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ S
  flat : Flat structureMap
  finiteType : Chapter01FiniteType structureMap
  genericFiberIso : chapter01GenericFiber structureMap B.genericPointMap ≅ C
  genericFiberIso_over :
    genericFiberIso.hom ≫ c = pullback.snd structureMap B.genericPointMap

def Chapter01ProperModel {S C : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter01IntegralBase S K} {c : C ⟶ Spec (CommRingCat.of K)}
    (M : Chapter01Model B c) : Prop :=
  Chapter01ProperMorphism M.structureMap

def Chapter01ProjectiveModel {S C : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter01IntegralBase S K}
    {c : C ⟶ Spec (CommRingCat.of K)} (M : Chapter01Model B c) : Prop :=
  Chapter01ProjectiveMorphism M.structureMap

def Chapter01NormalModel {S C : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter01IntegralBase S K} {c : C ⟶ Spec (CommRingCat.of K)}
    (M : Chapter01Model B c) : Prop :=
  Chapter01NormalScheme M.carrier

def Chapter01RegularModel {S C : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter01IntegralBase S K} {c : C ⟶ Spec (CommRingCat.of K)}
    (M : Chapter01Model B c) : Prop :=
  Chapter01RegularScheme M.carrier

end
end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01
