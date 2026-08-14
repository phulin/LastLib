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
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.MvPolynomial
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
open scoped AlgebraicGeometry

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

def Chapter01ArithmeticSurface {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Chapter01RelativeDimensionOne f ∧ Chapter01PureDimensionTwo X

/-! ### Normality and regularity -/

def Chapter01NormalRing (R : Type u) [CommRing R] : Prop :=
  IsDomain R ∧ IsIntegrallyClosed R

def Chapter01NormalLocalRing (R : Type u) [CommRing R] : Prop :=
  IsLocalRing R ∧ Chapter01NormalRing R

def Chapter01NormalScheme (X : Scheme.{u}) : Prop :=
  ∀ x : X, Chapter01NormalLocalRing (X.presheaf.stalk x)

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

/- LOCAL_DEPENDENCY_GUESS: the three fields below are deliberately exposed as named propositions;
the pinned Mathlib
snapshot has no universally-catenary/excellent-ring API.  They are local dependency interfaces,
not assumptions engineered to imply a later conclusion. -/
class Chapter01Nagata (R : Type u) [CommRing R] : Prop where
  noetherian : IsNoetherianRing R
  japanese_quotient : ∀ (p : Ideal R) [p.IsPrime],
    Chapter01Japanese (R ⧸ p)

class Chapter01ExcellentRing (R : Type u) [CommRing R] : Prop where
  noetherian : IsNoetherianRing R
  universallyCatenary : Prop
  geometricallyRegularFormalFibers : Prop
  regularLocusOpen : Prop
  completionReflectsRegularity : Prop
  localizationReflectsRegularity : Prop

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
    genericFiberIso.hom ≫ pullback.snd structureMap B.genericPointMap = c

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
