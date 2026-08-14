import Mathlib.AlgebraicGeometry.Birational.Birational
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Topology.KrullDimension

import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter07.Core
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Dependencies
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.Dependencies
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.Section01TheUniversalRemedyForAnIdeal
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.Dependencies

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter13

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Set TopologicalSpace
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter07
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07
open scoped AlgebraicGeometry nonZeroDivisors

universe u v

/-!
Shared interfaces for Chapter 13.

The pinned library supplies schemes, the standard morphism properties, and the
relative normalization `Scheme.Hom.normalization`.  It does not yet package
the book's scheme-level Japanese/Nagata/excellent predicates, arithmetic
surface models, or the regularization and contraction constructions.  The
records below keep those missing interfaces explicit.  They are deliberately
properties of the canonical schemes and morphisms, rather than replacement
objects with the same informal names.
-/

/-! ### Normality, regularity, and the finiteness hierarchy -/

/-- The componentwise normal-domain condition used for affine charts. -/
def chapter13NormalRing (R : Type u) [CommRing R] : Prop :=
  ∀ (p : Ideal R) (hp : p.IsPrime),
    letI : p.IsPrime := hp
    IsDomain (Localization.AtPrime p) ∧
      IsIntegrallyClosed (Localization.AtPrime p)

def Chapter13ReducedScheme (X : Scheme.{u}) : Prop :=
  ∀ x : X, _root_.IsReduced (X.presheaf.stalk x)

/-- Book-facing normality, with the componentwise interpretation made explicit. -/
class Chapter13NormalScheme (X : Scheme.{u}) : Prop where
  reduced : Chapter13ReducedScheme X
  affine_normal : ∀ (U : X.Opens), IsAffineOpen U → chapter13NormalRing Γ(X, U)

/-- Regularity at a point is regularity of its noetherian local ring. -/
def chapter13RegularAt (X : Scheme.{u}) (x : X) : Prop :=
  IsRegularLocalRing (X.presheaf.stalk x)

class Chapter13RegularScheme (X : Scheme.{u}) : Prop where
  regular_at : ∀ x : X, chapter13RegularAt X x

theorem chapter13_regular_scheme_is_normal {X : Scheme.{u}}
    (hNoetherian : IsNoetherian X) (hX : Chapter13RegularScheme X) :
    Chapter13NormalScheme X := by
  sorry

def chapter13RegularLocus (X : Scheme.{u}) : Set X :=
  {x | chapter13RegularAt X x}

/-- The finite-extension condition on a domain used by the book. -/
def chapter13JapaneseDomain (R : Type u) [CommRing R] : Prop :=
  IsDomain R ∧
    ∀ [_hR : IsDomain R] (L : Type u) [Field L] [Algebra (FractionRing R) L]
      [FiniteDimensional (FractionRing R) L] [Algebra R L]
      [IsScalarTower R (FractionRing R) L],
      Module.Finite R (integralClosure R L)

/-- A noetherian ring is Nagata when every prime quotient is Japanese. -/
def chapter13NagataRing (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧
    ∀ (p : Ideal R) (hp : p.IsPrime),
      letI : p.IsPrime := hp
      chapter13JapaneseDomain (R ⧸ p)

class Chapter13NagataScheme (X : Scheme.{u}) : Prop where
  noetherian : IsNoetherian X
  affine_nagata : ∀ (U : X.Opens), IsAffineOpen U → chapter13NagataRing Γ(X, U)

/- LOCAL_DEPENDENCY_GUESS: the pinned Mathlib snapshot does not expose formal
fibers or universal catenarity at the scheme level.  The earlier chapter's
excellent affine-ring interface is the canonical local source for these two
predicates. -/
def Chapter13GeometricallyRegularFormalFibers (X : Scheme.{u}) : Prop :=
  ∀ U : X.affineOpens,
    LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.Chapter01GeometricallyRegularFormalFibers
      Γ(X, U)

def Chapter13UniversallyCatenary (X : Scheme.{u}) : Prop :=
  ∀ U : X.affineOpens,
    LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.Chapter01UniversallyCatenary
      Γ(X, U)

def Chapter13SurfaceDimensionBound (X : Scheme.{u}) : Prop :=
  ∀ x : X, Order.coheight x ≤ 2

/- A surface-resolution capability is conditional on the dimension bound.  This
keeps the dimension-two hypothesis of the resolution theorem visible instead
of putting arbitrary-dimensional resolution into the definition of excellence. -/
def Chapter13SurfaceResolutionCapability (X : Scheme.{u}) : Prop :=
  ∀ {S : Scheme.{u}} (f : X ⟶ S),
    Chapter13ReducedScheme X → Chapter13SurfaceDimensionBound X →
      Chapter09ProjectiveMorphism f →
      ∃ (X' : Scheme.{u}) (r : X' ⟶ X),
        IsProper r ∧ Chapter09ProjectiveMorphism (r ≫ f) ∧
          (∃ U : X.Opens, Dense (U : Set X) ∧
            Dense (r ⁻¹' (U : Set X)) ∧ IsIso (r ∣_ U)) ∧
          (∀ y : X, chapter13RegularAt X y →
            ∃ U : X.Opens, y ∈ U ∧ IsIso (r ∣_ U)) ∧
          Chapter13RegularScheme X'

def Chapter13GoodFormalFibers (X : Scheme.{u}) : Prop :=
  Chapter13GeometricallyRegularFormalFibers X

/- LOCAL_DEPENDENCY_GUESS: surface resolution is exposed as a theorem-level
two-dimensional excellent-surface input used by the book, not as a claim about
arbitrary-dimensional resolution. -/
class Chapter13ExcellentScheme (X : Scheme.{u}) : Prop where
  noetherian : IsNoetherian X
  affine_excellent : ∀ U : X.affineOpens,
    LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.Chapter01ExcellentRing
      Γ(X, U)
  regular_locus_open : IsOpen (chapter13RegularLocus X)

def Chapter13OneDimensionalScheme (S : Scheme.{u}) : Prop :=
  ∀ x : S, Order.coheight x ≤ 1

/- LOCAL_DEPENDENCY_GUESS: normality is recorded explicitly because the
model arguments use the codimension-one DVR description. -/
class Chapter13DedekindScheme (S : Scheme.{u}) : Prop where
  integral : IsIntegral S
  noetherian : IsNoetherian S
  dimension_one : Chapter13OneDimensionalScheme S
  nontrivial : ∃ x y : S, x ≠ y
  closed_point_exists : ∃ s : S, IsClosed ({s} : Set S)
  normal : Chapter13NormalScheme S
  affine_dedekind :
    LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.Chapter01DedekindScheme S

structure Chapter13ExcellentDedekindScheme (K : Type u) [Field K] where
  carrier : Scheme.{u}
  dedekind : Chapter13DedekindScheme carrier
  excellent : Chapter13ExcellentScheme carrier
  generic_point_data :
    LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.Chapter01GenericPointData
      carrier K

abbrev chapter13GenericPointMap {K : Type u} [Field K]
    (S : Chapter13ExcellentDedekindScheme K) :
    AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier :=
  S.generic_point_data.genericPointMap

theorem chapter13_excellent_implies_nagata {X : Scheme.{u}}
    (hX : Chapter13ExcellentScheme X) : Chapter13NagataScheme X :=
  by
    sorry

theorem chapter13_excellent_implies_surface_resolution
    {X : Scheme.{u}} (hX : Chapter13ExcellentScheme X)
    (hDim : Chapter13SurfaceDimensionBound X) :
    Chapter13SurfaceResolutionCapability X := by
  sorry

theorem chapter13_excellent_has_open_regular_locus {X : Scheme.{u}}
    (hX : Chapter13ExcellentScheme X) : IsOpen (chapter13RegularLocus X) :=
  hX.regular_locus_open

theorem chapter13_excellent_has_universally_catenary_affine_rings
    {X : Scheme.{u}} (hX : Chapter13ExcellentScheme X) :
    Chapter13UniversallyCatenary X := by
  intro U
  exact @LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.Chapter01ExcellentRing.universallyCatenary
    (Γ(X, U)) _ (hX.affine_excellent U)

theorem chapter13_excellent_has_geometrically_regular_formal_fibers
    {X : Scheme.{u}} (hX : Chapter13ExcellentScheme X) :
    Chapter13GoodFormalFibers X := by
  intro U
  exact @LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.Chapter01ExcellentRing.geometricallyRegularFormalFibers
    (Γ(X, U)) _ (hX.affine_excellent U)

/-! ### Canonical normalization and morphism properties -/

/-- The canonical relative normalization supplied by Mathlib. -/
noncomputable abbrev chapter13RelativeNormalization {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] : Scheme :=
  f.normalization

/-- The canonical map from the relative normalization back to the base. -/
noncomputable abbrev chapter13NormalizationMap {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    chapter13RelativeNormalization f ⟶ Y :=
  f.fromNormalization

/-- The canonical map from the original source to its normalization. -/
noncomputable abbrev chapter13ToNormalization {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    X ⟶ chapter13RelativeNormalization f :=
  f.toNormalization

theorem chapter13_to_normalization_factorization {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    chapter13ToNormalization f ≫ chapter13NormalizationMap f = f := by
  exact Scheme.Hom.toNormalization_fromNormalization f

theorem chapter13_normalization_map_is_integral {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    IsIntegralHom (chapter13NormalizationMap f) := by
  infer_instance

noncomputable def chapter13NormalizationDesc
    {X Y T : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (f₁ : X ⟶ T) (f₂ : T ⟶ Y) [IsIntegralHom f₂]
    (H : f = f₁ ≫ f₂) :
    chapter13RelativeNormalization f ⟶ T :=
  f.normalizationDesc f₁ f₂ H

theorem chapter13_normalization_desc_factors_the_first_map
    {X Y T : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (f₁ : X ⟶ T) (f₂ : T ⟶ Y) [IsIntegralHom f₂]
    (H : f = f₁ ≫ f₂) :
    chapter13ToNormalization f ≫
        chapter13NormalizationDesc f f₁ f₂ H = f₁ := by
  exact f.toNormalization_normalizationDesc f₁ f₂ H

theorem chapter13_normalization_desc_factors_the_base_map
    {X Y T : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (f₁ : X ⟶ T) (f₂ : T ⟶ Y) [IsIntegralHom f₂]
    (H : f = f₁ ≫ f₂) :
    chapter13NormalizationDesc f f₁ f₂ H ≫ f₂ =
      chapter13NormalizationMap f := by
  exact f.normalizationDesc_comp f₁ f₂ H

/-- Properness's valuative-extension half of the ledger. -/
def Chapter13ValuativeCriterion {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (g : AlgebraicGeometry.Spec (CommRingCat.of (FractionRing R)) ⟶ X)
    (h : AlgebraicGeometry.Spec (CommRingCat.of R) ⟶ Y),
    let η : AlgebraicGeometry.Spec (CommRingCat.of (FractionRing R)) ⟶
        AlgebraicGeometry.Spec (CommRingCat.of R) :=
      Scheme.Spec.map
        (CommRingCat.ofHom (algebraMap R (FractionRing R))).op
    g ≫ f = η ≫ h →
      ∃! l : AlgebraicGeometry.Spec (CommRingCat.of R) ⟶ X,
        l ≫ f = h ∧ η ≫ l = g

class Chapter13ValuativeExtension {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  extension_property : Chapter13ValuativeCriterion f

/- The earlier relative-curve chapter supplies the canonical fiber predicate;
we keep this name as the chapter-13-facing bridge. -/
abbrev Chapter13GeometricallyRegularFibers {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.Chapter01GeometricallyRegularFibers f

def chapter13ProjectiveMorphism {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Chapter09ProjectiveMorphism f

def chapter13ProjectiveHasPolarization {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ L : Chapter09LineBundle X, chapter09RelativelyAmple f L

/- LOCAL_DEPENDENCY_GUESS: the valuative criterion and the projective-bundle
polarization are exposed as theorem-level bridges until the preceding model
chapters are wired into the current source tree. -/
theorem chapter13_proper_has_valuative_extension {X S : Scheme.{u}}
    (f : X ⟶ S) [IsProper f] : Chapter13ValuativeExtension f := by
  sorry

theorem chapter13_projective_implies_proper {X S : Scheme.{u}} {f : X ⟶ S}
    (hproj : chapter13ProjectiveMorphism f) : IsProper f := by
  sorry

theorem chapter13_projective_has_ample_polarization {X S : Scheme.{u}} {f : X ⟶ S}
    (hproj : chapter13ProjectiveMorphism f) : chapter13ProjectiveHasPolarization f := by
  sorry

theorem chapter13_smooth_over_regular_base_is_regular
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    (hS : Chapter13RegularScheme S) : Chapter13RegularScheme X := by
  sorry

/-! ### Flatness over a Dedekind base -/

/-- Local affine-chart formulation of absence of torsion from the base. -/
def chapter13NoVerticalTorsion {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ (U : S.Opens) (_hU : IsAffineOpen U)
    (V : X.Opens) (_hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U),
    ∀ {r : Γ(S, U)} {a : Γ(X, V)}, r ≠ 0 →
      (f.appLE U V hVU).hom r * a = 0 → a = 0

/- “Well behaved” is the no-vertical-torsion consequence used by the model
construction.  It is deliberately separate from reducedness of fibers. -/
def Chapter13WellBehavedFiberCondition {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  chapter13NoVerticalTorsion f

class Chapter13WellBehavedFibers {X S : Scheme.{u}} (f : X ⟶ S) : Prop where
  fiber_condition : Chapter13WellBehavedFiberCondition f

def Chapter13ReducedFiberCondition {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ s : S, Chapter13ReducedScheme (f.fiber s)

class Chapter13ReducedFibers {X S : Scheme.{u}} (f : X ⟶ S) : Prop where
  all_fibers_reduced : Chapter13ReducedFiberCondition f

structure Chapter13FlatDedekindConsequences {X S : Scheme.{u}} (f : X ⟶ S) where
  base : Chapter13DedekindScheme S
  flat : Flat f
  no_vertical_torsion : chapter13NoVerticalTorsion f
  fibers : Chapter13WellBehavedFibers f

theorem chapter13_flat_over_dedekind_has_no_vertical_torsion
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hS : Chapter13DedekindScheme S) [Flat f] :
    chapter13NoVerticalTorsion f := by
  sorry

abbrev Chapter13GeometricallyConnected {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  GeometricallyConnected f

abbrev Chapter13PureDimensionOne : ObjectProperty Scheme.{u} :=
  LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.Chapter01PureDimensionOne

abbrev Chapter13RelativeDimensionOne {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.Chapter01RelativeDimensionOne f

abbrev Chapter13AbsoluteDimensionTwo (X : Scheme.{u}) : Prop :=
  LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.Chapter01PureDimensionTwo X

def chapter13NodeRingCondition (A : Type u) [CommRing A] [IsLocalRing A] : Prop :=
  _root_.IsReduced A ∧
    ∃ x y : A,
      x * y = 0 ∧ x ≠ 0 ∧ y ≠ 0 ∧
        IsLocalRing.maximalIdeal A = Ideal.span ({x, y} : Set A) ∧
        x ∉ Ideal.span ({y} : Set A) ∧
        y ∉ Ideal.span ({x} : Set A)

def chapter13FiberNodeCondition {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ (s : S) (x : f.fiber s),
    IsRegularLocalRing ((f.fiber s).presheaf.stalk x) ∨
      chapter13NodeRingCondition ((f.fiber s).presheaf.stalk x)

def Chapter13OrdinaryDoublePointCondition {X S : Scheme.{u}}
    (f : X ⟶ S) : Prop :=
  ∀ (s : S) (x : f.fiber s),
    IsRegularLocalRing ((f.fiber s).presheaf.stalk x) ∨
      chapter13NodeRingCondition ((f.fiber s).presheaf.stalk x)

def Chapter13TransverseComponentsCondition {X S : Scheme.{u}}
    (f : X ⟶ S) : Prop :=
  ∀ (s : S) (x : f.fiber s),
    IsRegularLocalRing ((f.fiber s).presheaf.stalk x) ∨
      ∃ a b : (f.fiber s).presheaf.stalk x,
        a * b = 0 ∧ a ≠ 0 ∧ b ≠ 0 ∧
          IsLocalRing.maximalIdeal ((f.fiber s).presheaf.stalk x) =
            Ideal.span ({a, b} : Set ((f.fiber s).presheaf.stalk x)) ∧
          a ∉ Ideal.span ({b} : Set ((f.fiber s).presheaf.stalk x)) ∧
          b ∉ Ideal.span ({a} : Set ((f.fiber s).presheaf.stalk x))

noncomputable abbrev chapter13NodeCompletedBaseRing
    (R : Type u) [CommRing R] [IsLocalRing R] :=
  AdicCompletion (IsLocalRing.maximalIdeal R) R

noncomputable abbrev chapter13NodePowerSeries
    (R : Type u) [CommRing R] [IsLocalRing R] :=
  MvPowerSeries (Fin 2) (chapter13NodeCompletedBaseRing R)

def chapter13NodeEquation (R : Type u) [CommRing R] [IsLocalRing R] (π : R) :
    chapter13NodePowerSeries R :=
  MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) -
    MvPowerSeries.C (algebraMap R (chapter13NodeCompletedBaseRing R) π)

def chapter13NodeIdeal (R : Type u) [CommRing R] [IsLocalRing R] (π : R) :
    Ideal (chapter13NodePowerSeries R) :=
  Ideal.span {chapter13NodeEquation R π}

abbrev chapter13NodeCompletedLocalRing
    (R : Type u) [CommRing R] [IsLocalRing R] (π : R) :=
  chapter13NodePowerSeries R ⧸ chapter13NodeIdeal R π

def chapter13Uniformizer (R : Type u) [CommRing R] [IsLocalRing R]
    (π : R) : Prop :=
  ¬ IsUnit π ∧ Ideal.span ({π} : Set R) = IsLocalRing.maximalIdeal R

def Chapter13NodeLocalEquationCondition {X S : Scheme.{u}}
    (f : X ⟶ S) : Prop :=
  ∀ (s : S) (x : f.fiber s),
    IsRegularLocalRing ((f.fiber s).presheaf.stalk x) ∨
      ∃ π : S.presheaf.stalk s,
        chapter13Uniformizer (S.presheaf.stalk s) π ∧
          Nonempty (
            AdicCompletion
                (IsLocalRing.maximalIdeal (X.presheaf.stalk (f.fiberι s x)))
                (X.presheaf.stalk (f.fiberι s x)) ≃+*
              chapter13NodeCompletedLocalRing (S.presheaf.stalk s) π)

/-! ### Generic and birational relations -/

/- The componentwise form is needed here because the resolution theorem is stated
for reduced schemes, not only for integral schemes. -/
def Chapter13BirationalMorphism {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∃ U : Y.Opens, Dense (U : Set Y) ∧
    Dense (f ⁻¹' (U : Set Y)) ∧ IsIso (f ∣_ U)

def Chapter13ProperBirationalMorphism {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  IsProper f ∧ Chapter13BirationalMorphism f

def Chapter13UniversalNormalization {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ (Z : Scheme.{u}) (g : Z ⟶ Y), Chapter13NormalScheme Z →
    Chapter13BirationalMorphism g → ∃! h : Z ⟶ X, h ≫ f = g

def Chapter13NodalModelProperty {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Flat f ∧ Chapter13RelativeDimensionOne f ∧
    (∀ s : S, Chapter13ReducedScheme (f.fiber s)) ∧
    Chapter13OrdinaryDoublePointCondition f ∧
    Chapter13TransverseComponentsCondition f ∧
    Chapter13NodeLocalEquationCondition f

/-! ### Generic curves and arithmetic surface models -/

structure Chapter13GeometricGenusTheory
    {K : Type u} [Field K] (X : Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of K)) where
  [h1Module : Module K
    (chapter04Cohomology (chapter04TrivialLineBundle X).sheaf 1)]
  h1Finite : FiniteDimensional K
    (chapter04Cohomology (chapter04TrivialLineBundle X).sheaf 1)

structure Chapter13SmoothProjectiveCurve (K : Type u) [Field K] where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ AlgebraicGeometry.Spec (CommRingCat.of K)
  smooth : Smooth structureMap
  proper : IsProper structureMap
  projective : chapter13ProjectiveMorphism structureMap
  geometrically_connected : Chapter13GeometricallyConnected structureMap
  pure_dimension_one : Chapter13PureDimensionOne carrier
  genus_theory : Chapter13GeometricGenusTheory carrier structureMap

noncomputable def Chapter13SmoothProjectiveCurve.genus
    {K : Type u} [Field K] (C : Chapter13SmoothProjectiveCurve K) : ℕ :=
  letI : Module K
      (chapter04Cohomology (chapter04TrivialLineBundle C.carrier).sheaf 1) :=
    C.genus_theory.h1Module
  Module.finrank K
    (chapter04Cohomology (chapter04TrivialLineBundle C.carrier).sheaf 1)

structure Chapter13ArithmeticSurfaceData (X S : Scheme.{u}) (f : X ⟶ S) where
  base_dedekind : Chapter13DedekindScheme S
  integral_total_space : IsIntegral X
  finite_type :
    LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.Chapter01FiniteType f
  normal_total_space : Chapter13NormalScheme X
  flat_over_base : Flat f
  relative_dimension_one : Chapter13RelativeDimensionOne f
  absolute_dimension_two : Chapter13AbsoluteDimensionTwo X

structure Chapter13RegularProperModel {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme K)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier) where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ S.carrier
  flat : Flat structureMap
  finite_type :
    LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.Chapter01FiniteType
      structureMap
  proper : IsProper structureMap
  projective : chapter13ProjectiveMorphism structureMap
  integral : IsIntegral carrier
  normal : Chapter13NormalScheme carrier
  regular : Chapter13RegularScheme carrier
  relative_dimension_one : Chapter13RelativeDimensionOne structureMap
  absolute_dimension_two : Chapter13AbsoluteDimensionTwo carrier
  generic_point_map_eq : η = chapter13GenericPointMap S
  generic_fiber_iso : Limits.pullback structureMap η ≅ C.carrier
  generic_fiber_iso_over :
    generic_fiber_iso.inv ≫ Limits.pullback.snd structureMap η = C.structureMap

abbrev Chapter13Model {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme K)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier) :=
  Chapter13RegularProperModel C S η

structure Chapter13PrescribedGoodOpenData {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme K)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier) where
  open_set : S.carrier.Opens
  nonempty : open_set ≠ ⊥
  prescribed_model : Scheme.{u}
  prescribed_map : prescribed_model ⟶ open_set
  prescribed_regular : Chapter13RegularScheme prescribed_model
  prescribed_projective : chapter13ProjectiveMorphism prescribed_map
  generic_map : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ open_set
  generic_map_over : generic_map ≫ open_set.ι = η
  generic_point_map_eq : η = chapter13GenericPointMap S
  generic_fiber_iso : Limits.pullback prescribed_map generic_map ≅ C.carrier
  generic_fiber_iso_over :
    generic_fiber_iso.inv ≫ Limits.pullback.snd prescribed_map generic_map =
      C.structureMap

structure Chapter13GoodOpenRestriction
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme K}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (M : Chapter13RegularProperModel C S η)
    (G : Chapter13PrescribedGoodOpenData C S η) where
  restriction_identification :
    (M.structureMap ⁻¹ᵁ G.open_set).toScheme ≅ G.prescribed_model
  restriction_over :
    restriction_identification.hom ≫ G.prescribed_map =
      M.structureMap ∣_ G.open_set

theorem chapter13_regular_proper_model_exists {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme K)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier)
    (hη : η = chapter13GenericPointMap S) :
    Nonempty (Chapter13RegularProperModel C S η) := by
  sorry

theorem chapter13_regular_model_preserves_a_prescribed_good_open
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme K)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier)
    (hη : η = chapter13GenericPointMap S)
    (G : Chapter13PrescribedGoodOpenData C S η) :
    ∃ M : Chapter13RegularProperModel C S η,
      Nonempty (Chapter13GoodOpenRestriction M G) := by
  sorry

/-! ### Projective closure, normalization, resolution, and domination -/

structure Chapter13GenericProjectiveEmbedding
    {K : Type u} [Field K] (C : Chapter13SmoothProjectiveCurve K) where
  N : ℕ
  ambient : Scheme.{u}
  ambient_map : ambient ⟶ AlgebraicGeometry.Spec (CommRingCat.of K)
  ambient_is_projective_space : Nonempty
    { e : ambient ≅ chapter07ProjectiveSpace K N //
      e.hom ≫ chapter07ProjectiveSpaceToBase K N = ambient_map }
  inclusion : C.carrier ⟶ ambient
  closed : IsClosedImmersion inclusion
  over_field : inclusion ≫ ambient_map = C.structureMap

structure Chapter13ProjectiveClosureData
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme K)
  (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier)
    (E : Chapter13GenericProjectiveEmbedding C) where
  closure : Scheme.{u}
  closure_map : closure ⟶ S.carrier
  projective : chapter13ProjectiveMorphism closure_map
  ambient : Scheme.{u}
  ambient_map : ambient ⟶ S.carrier
  ambient_projective : chapter13ProjectiveMorphism ambient_map
  embedding : closure ⟶ ambient
  embedding_closed : IsClosedImmersion embedding
  embedding_over : embedding ≫ ambient_map = closure_map
  ambient_generic_fiber_iso : Limits.pullback ambient_map η ≅ E.ambient
  ambient_generic_fiber_iso_over :
    ambient_generic_fiber_iso.inv ≫ Limits.pullback.snd ambient_map η = E.ambient_map
  integral : IsIntegral closure
  flat : Flat closure_map
  generic_fiber_iso : Limits.pullback closure_map η ≅ C.carrier
  generic_fiber_iso_over :
    generic_fiber_iso.inv ≫ Limits.pullback.snd closure_map η = C.structureMap
  generic_fiber_embedding :
    Limits.pullback closure_map η ⟶ Limits.pullback ambient_map η
  generic_fiber_embedding_fst :
    generic_fiber_embedding ≫ Limits.pullback.fst ambient_map η =
      Limits.pullback.fst closure_map η ≫ embedding
  generic_fiber_embedding_snd :
    generic_fiber_embedding ≫ Limits.pullback.snd ambient_map η =
      Limits.pullback.snd closure_map η
  generic_fiber_embedding_identification :
    generic_fiber_iso.inv ≫ generic_fiber_embedding ≫
        ambient_generic_fiber_iso.hom = E.inclusion
  schematic_closure_is_smallest :
    ∀ {Z : Scheme.{u}} (i : Z ⟶ ambient),
      IsClosedImmersion i →
        (∃ g : C.carrier ⟶ Z,
          g ≫ i =
            generic_fiber_iso.inv ≫
              Limits.pullback.fst closure_map η ≫ embedding) →
        ∃ h : closure ⟶ Z, h ≫ i = embedding
  generic_point_map_eq : η = chapter13GenericPointMap S

structure Chapter13NormalizationStage
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme K}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (E : Chapter13GenericProjectiveEmbedding C)
    (P : Chapter13ProjectiveClosureData C S η E) where
  normalized : Scheme.{u}
  normalization_map : normalized ⟶ P.closure
  finite : IsFinite normalization_map
  normal : Chapter13NormalScheme normalized
  integral : IsIntegral normalized
  birational : Chapter13BirationalMorphism normalization_map
  universal : Chapter13UniversalNormalization normalization_map

structure Chapter13RegularizationStage
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme K}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    {E : Chapter13GenericProjectiveEmbedding C}
    (P : Chapter13ProjectiveClosureData C S η E)
    (N : Chapter13NormalizationStage E P) where
  regularized : Scheme.{u}
  resolution_map : regularized ⟶ N.normalized
  proper : IsProper resolution_map
  proper_birational : Chapter13ProperBirationalMorphism resolution_map
  projective_resolution : chapter13ProjectiveMorphism resolution_map
  projective : chapter13ProjectiveMorphism
    (resolution_map ≫ N.normalization_map ≫ P.closure_map)
  regular : Chapter13RegularScheme regularized
  generic_fiber_iso :
    Limits.pullback
        (resolution_map ≫ N.normalization_map ≫ P.closure_map) η ≅ C.carrier
  generic_fiber_iso_over :
    generic_fiber_iso.inv ≫
        Limits.pullback.snd
          (resolution_map ≫ N.normalization_map ≫ P.closure_map) η = C.structureMap
  integral : IsIntegral regularized
  finite_type :
    LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.Chapter01FiniteType
      (resolution_map ≫ N.normalization_map ≫ P.closure_map)
  flat : Flat (resolution_map ≫ N.normalization_map ≫ P.closure_map)
  relative_dimension_one :
    Chapter13RelativeDimensionOne
      (resolution_map ≫ N.normalization_map ≫ P.closure_map)
  absolute_dimension_two : Chapter13AbsoluteDimensionTwo regularized

structure Chapter13ConstructionPipeline
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme K)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier) where
  embedding : Chapter13GenericProjectiveEmbedding C
  closure : Chapter13ProjectiveClosureData C S η embedding
  normalization : Chapter13NormalizationStage embedding closure
  regular_model : Chapter13RegularizationStage closure normalization
  normalization_arrow : normalization.normalized ⟶ closure.closure
  regularization_arrow : regular_model.regularized ⟶ normalization.normalized
  normalization_arrow_eq : normalization_arrow = normalization.normalization_map
  regularization_arrow_eq : regularization_arrow = regular_model.resolution_map
  generic_point_map_eq : η = chapter13GenericPointMap S

/- LOCAL_DEPENDENCY_GUESS: the preceding chapters supply the existence of the
closure and surface-resolution stages; this constructor records their exact
interface without taking the desired final model as a hypothesis. -/
theorem chapter13_construction_pipeline_exists {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme K)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier)
    (hη : η = chapter13GenericPointMap S) :
    Nonempty (Chapter13ConstructionPipeline C S η) := by
  sorry

def chapter13InducesIdentityOnGenericFiber
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Scheme.{u}}
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S)
    {X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (u : X ⟶ Y) (hu : u ≫ g = f)
    (eX : Limits.pullback f η ≅ C.carrier)
    (eY : Limits.pullback g η ≅ C.carrier) : Prop :=
  let uη : Limits.pullback f η ⟶ Limits.pullback g η :=
    Limits.pullback.lift
      (Limits.pullback.fst f η ≫ u)
      (Limits.pullback.snd f η)
      (by
        sorry)
  eX.inv ≫ uη ≫ eY.hom = 𝟙 C.carrier

noncomputable def chapter13GenericFiberMap
    {K : Type u} [Field K]
    {S : Scheme.{u}}
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S)
    {X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (u : X ⟶ Y) (hu : u ≫ g = f) :
    Limits.pullback f η ⟶ Limits.pullback g η :=
  Limits.pullback.lift
    (Limits.pullback.fst f η ≫ u)
    (Limits.pullback.snd f η)
    (by
      sorry)

/-! A generic-fiber-preservation predicate must mention the base and its generic
point.  Birationality alone is not enough: a birational morphism can still
change a special fiber, while this predicate records that the induced generic
fiber map is an isomorphism. -/
def Chapter13GenericFiberUnchanged
    {K : Type u} [Field K]
    {S : Scheme.{u}}
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S)
    {X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (u : X ⟶ Y) (hu : u ≫ g = f) : Prop :=
  IsIso (chapter13GenericFiberMap η f g u hu)

structure Chapter13CommonRegularDomination
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme K)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier)
    (X Y : Scheme.{u}) (fX : X ⟶ S.carrier) (fY : Y ⟶ S.carrier) where
  carrier : Scheme.{u}
  base : carrier ⟶ S.carrier
  to_left : carrier ⟶ X
  to_right : carrier ⟶ Y
  over_base_left : to_left ≫ fX = base
  over_base_right : to_right ≫ fY = base
  proper_left : IsProper to_left
  proper_right : IsProper to_right
  projective_left : chapter13ProjectiveMorphism to_left
  projective_right : chapter13ProjectiveMorphism to_right
  birational_left : Chapter13BirationalMorphism to_left
  birational_right : Chapter13BirationalMorphism to_right
  regular : Chapter13RegularScheme carrier
  projective_base : chapter13ProjectiveMorphism base
  generic_fiber_iso : Limits.pullback base η ≅ C.carrier
  generic_fiber_iso_over :
    generic_fiber_iso.inv ≫ Limits.pullback.snd base η = C.structureMap
  left_generic_fiber_iso : Limits.pullback fX η ≅ C.carrier
  left_generic_fiber_iso_over :
    left_generic_fiber_iso.inv ≫ Limits.pullback.snd fX η = C.structureMap
  right_generic_fiber_iso : Limits.pullback fY η ≅ C.carrier
  right_generic_fiber_iso_over :
    right_generic_fiber_iso.inv ≫ Limits.pullback.snd fY η = C.structureMap
  generic_identity_left :
    chapter13InducesIdentityOnGenericFiber η base fX to_left over_base_left
      generic_fiber_iso left_generic_fiber_iso
  generic_identity_right :
    chapter13InducesIdentityOnGenericFiber η base fY to_right over_base_right
      generic_fiber_iso right_generic_fiber_iso

structure Chapter13GenericFiniteCorrespondence {K : Type u} [Field K] where
  source : Chapter13SmoothProjectiveCurve K
  target : Chapter13SmoothProjectiveCurve K
  map : source.carrier ⟶ target.carrier
  over_map : map ≫ target.structureMap = source.structureMap
  finite : IsFinite map

/-! A resolved graph keeps the generic finite map attached to the actual
models.  The two generic-fiber equations say that the graph projection to the
source is the identity and that the projection to the target is the supplied
finite map. -/
structure Chapter13ResolvedFiniteCorrespondence
    {K : Type u} [Field K]
    (F : Chapter13GenericFiniteCorrespondence (K := K))
    (S : Chapter13ExcellentDedekindScheme K)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier)
    (X : Chapter13RegularProperModel F.source S η)
    (Y : Chapter13RegularProperModel F.target S η) where
  graph : Scheme.{u}
  graph_to_source : graph ⟶ X.carrier
  graph_to_target : graph ⟶ Y.carrier
  graph_structure_map : graph ⟶ S.carrier
  over_source : graph_to_source ≫ X.structureMap = graph_structure_map
  over_target : graph_to_target ≫ Y.structureMap = graph_structure_map
  proper_to_source : IsProper graph_to_source
  proper_to_target : IsProper graph_to_target
  projective_to_source : chapter13ProjectiveMorphism graph_to_source
  projective_to_target : chapter13ProjectiveMorphism graph_to_target
  regular : Chapter13RegularScheme graph
  generic_fiber_iso : Limits.pullback graph_structure_map η ≅ F.source.carrier
  generic_fiber_iso_over :
    generic_fiber_iso.inv ≫ Limits.pullback.snd graph_structure_map η =
      F.source.structureMap
  generic_source_identity :
    chapter13InducesIdentityOnGenericFiber η graph_structure_map
      X.structureMap graph_to_source over_source
      generic_fiber_iso X.generic_fiber_iso
  generic_target_map :
    generic_fiber_iso.inv ≫
        chapter13GenericFiberMap η graph_structure_map Y.structureMap
          graph_to_target over_target ≫ Y.generic_fiber_iso.hom =
      F.map

/-! ### Base change and the minimal/semistable endpoints -/

structure Chapter13FiniteSeparableExtension (K : Type u) [Field K] where
  extension : Type u
  [field_extension : Field extension]
  [algebra_extension : Algebra K extension]
  [finite_extension : FiniteDimensional K extension]
  [separable_extension : Algebra.IsSeparable K extension]

structure Chapter13FiniteExtension (K : Type u) [Field K] where
  extension : Type u
  [field_extension : Field extension]
  [algebra_extension : Algebra K extension]
  [finite_extension : FiniteDimensional K extension]

noncomputable def chapter13FieldBaseChangeMap
    {K L : Type u} [Field K] [Field L] [Algebra K L] :
    AlgebraicGeometry.Spec (CommRingCat.of L) ⟶
      AlgebraicGeometry.Spec (CommRingCat.of K) :=
  Scheme.Spec.map (CommRingCat.ofHom (algebraMap K L)).op

abbrev chapter13FiniteScalarExtension
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (C : Chapter13SmoothProjectiveCurve K) : Scheme.{u} :=
  Limits.pullback C.structureMap (chapter13FieldBaseChangeMap (K := K) (L := L))

structure Chapter13NormalizedExcellentDedekindBase
    {K : Type u} [Field K]
    (S : Chapter13ExcellentDedekindScheme K)
    (E : Chapter13FiniteExtension K) where
  carrier : Scheme.{u}
  map : carrier ⟶ S.carrier
  finite : IsFinite map
  dedekind : Chapter13DedekindScheme carrier
  excellent : Chapter13ExcellentScheme carrier
  generic_point_data :
    letI : Field E.extension := E.field_extension
    LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.Chapter01GenericPointData
      carrier E.extension
  generic_point_map_over :
    letI : Field E.extension := E.field_extension
    letI : Algebra K E.extension := E.algebra_extension
    generic_point_data.genericPointMap ≫ map =
      chapter13FieldBaseChangeMap (K := K) (L := E.extension) ≫
        chapter13GenericPointMap S

structure Chapter13BaseChangeRepair
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme K)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier)
    (M : Chapter13RegularProperModel C S η)
    (E : Chapter13FiniteExtension K) where
  normalized_base :
    letI : Field E.extension := E.field_extension
    Chapter13NormalizedExcellentDedekindBase S E
  base_change_to_model :
    Limits.pullback M.structureMap normalized_base.map ⟶ M.carrier
  base_change_to_model_canonical :
    base_change_to_model =
      Limits.pullback.fst M.structureMap normalized_base.map
  normalized : Scheme.{u}
  normalization_map :
    normalized ⟶ Limits.pullback M.structureMap normalized_base.map
  normalization_finite : IsFinite normalization_map
  normalized_normal : Chapter13NormalScheme normalized
  resolved : Scheme.{u}
  resolution_map : resolved ⟶ normalized
  resolved_regular : Chapter13RegularScheme resolved
  resolved_to_base_changed :
    resolved ⟶ Limits.pullback M.structureMap normalized_base.map
  resolution_over_base :
    resolution_map ≫ normalization_map = resolved_to_base_changed
  resolved_to_model : resolved ⟶ M.carrier
  resolved_to_model_eq :
    resolved_to_model = resolved_to_base_changed ≫ base_change_to_model
  resolved_projective : chapter13ProjectiveMorphism resolved_to_model
  resolved_structure_map : resolved ⟶ normalized_base.carrier
  resolved_structure_map_eq :
    resolved_structure_map =
      resolved_to_base_changed ≫
        Limits.pullback.snd M.structureMap normalized_base.map
  resolved_projective_over_base :
    chapter13ProjectiveMorphism resolved_structure_map
  resolved_proper_over_base : IsProper resolved_structure_map
  resolved_integral : IsIntegral resolved
  resolved_finite_type :
    LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.Chapter01FiniteType
      resolved_structure_map
  resolved_flat : Flat resolved_structure_map
  resolved_relative_dimension_one :
    Chapter13RelativeDimensionOne resolved_structure_map
  resolved_absolute_dimension_two : Chapter13AbsoluteDimensionTwo resolved
  resolved_generic_fiber_iso :
    letI : Field E.extension := E.field_extension
    letI : Algebra K E.extension := E.algebra_extension
    Limits.pullback resolved_structure_map
        normalized_base.generic_point_data.genericPointMap ≅
      chapter13FiniteScalarExtension (L := E.extension) C
  resolved_generic_fiber_iso_over :
    letI : Field E.extension := E.field_extension
    letI : Algebra K E.extension := E.algebra_extension
    resolved_generic_fiber_iso.inv ≫
        Limits.pullback.snd resolved_structure_map
          normalized_base.generic_point_data.genericPointMap =
      Limits.pullback.snd C.structureMap
        (chapter13FieldBaseChangeMap (K := K) (L := E.extension))

theorem chapter13_normalize_and_resolve_after_finite_base_change
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme K)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier)
    (hη : η = chapter13GenericPointMap S)
    (M : Chapter13RegularProperModel C S η)
    (E : Chapter13FiniteExtension K) :
    Nonempty (Chapter13BaseChangeRepair C S η M E) := by
  sorry

structure Chapter13LineBundleDegreeData (X : Scheme.{u}) where
  degree : Chapter07LineBundle X → ℤ
  degree_is_invariant :
    ∀ {L M : Chapter07LineBundle X}, Nonempty (L.sheaf ≅ M.sheaf) →
      degree L = degree M

structure Chapter13VerticalExceptionalCurve
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme K}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
  (M : Chapter13RegularProperModel C S η) where
  carrier : Scheme.{u}
  inclusion : carrier ⟶ M.carrier
  closed_immersion : IsClosedImmersion inclusion
  base_point : S.carrier
  base_point_closed : IsClosed ({base_point} : Set S.carrier)
  vertical : ∀ x : carrier, M.structureMap (inclusion x) = base_point
  residue_field_map :
    carrier ⟶ AlgebraicGeometry.Spec
      (CommRingCat.of (S.carrier.residueField base_point))
  residue_field_map_over :
    residue_field_map ≫ S.carrier.fromSpecResidueField base_point =
      inclusion ≫ M.structureMap
  residue_field_extension : Type u
  [residue_field_extension_field : Field residue_field_extension]
  [residue_field_extension_algebra :
    Algebra (S.carrier.residueField base_point) residue_field_extension]
  residue_field_extension_finite :
    FiniteDimensional (S.carrier.residueField base_point) residue_field_extension
  residue_field_extension_map :
    AlgebraicGeometry.Spec (CommRingCat.of residue_field_extension) ⟶
      AlgebraicGeometry.Spec (CommRingCat.of (S.carrier.residueField base_point))
  residue_field_extension_structure_map :
    carrier ⟶ AlgebraicGeometry.Spec (CommRingCat.of residue_field_extension)
  residue_field_extension_map_over :
    residue_field_extension_structure_map ≫ residue_field_extension_map =
      residue_field_map
  normal_bundle : Chapter07LineBundle carrier
  normal_ideal : M.carrier.IdealSheafData
  normal_ideal_subscheme_iso : Nonempty (carrier ≅ normal_ideal.subscheme)
  normal_ideal_subscheme_iso_over :
    ∀ e : carrier ≅ normal_ideal.subscheme,
      e.hom ≫ normal_ideal.subschemeι = inclusion
  conormal_line : Chapter07LineBundle carrier
  conormal_line_presentation :
    Nonempty (Chapter07IdealLineBundleIso
      (normal_ideal.comap inclusion) conormal_line)
  normal_bundle_is_dual_of_conormal :
    Nonempty (
      chapter04Tensor conormal_line.sheaf normal_bundle.sheaf ≅
        (chapter04TrivialLineBundle carrier).sheaf)
  projective_line_after_residue_extension :
    Nonempty (carrier ≅ chapter07ProjectiveSpace residue_field_extension 1)
  projective_line_after_residue_extension_over :
    ∀ e : carrier ≅ chapter07ProjectiveSpace residue_field_extension 1,
      e.hom ≫ chapter07ProjectiveSpaceToBase residue_field_extension 1 =
        residue_field_extension_structure_map
  degree_data : Chapter13LineBundleDegreeData carrier
  normal_bundle_degree_eq_minus_one :
    degree_data.degree normal_bundle = -1

def Chapter13ContractsAllVerticalExceptionalCurves
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme K}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (M : Chapter13RegularProperModel C S η)
    {Y : Scheme.{u}} (f : M.carrier ⟶ Y) : Prop :=
  ∀ E : Chapter13VerticalExceptionalCurve M,
    ∃ y : Y,
      IsClosed ({y} : Set Y) ∧
      (∀ x : E.carrier, f (E.inclusion x) = y) ∧
      ∃ h : E.carrier ⟶
          AlgebraicGeometry.Spec (CommRingCat.of (Y.residueField y)),
        h ≫ Y.fromSpecResidueField y = E.inclusion ≫ f

def chapter13RelativelyMinimal
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme K}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (M : Chapter13RegularProperModel C S η) : Prop :=
  ¬ Nonempty (Chapter13VerticalExceptionalCurve M)

structure Chapter13MinimalRegularModel
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme K)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier) where
  model : Chapter13RegularProperModel C S η
  generic_point_map_eq : η = chapter13GenericPointMap S
  positive_genus : 0 < C.genus
  relatively_minimal : chapter13RelativelyMinimal model

structure Chapter13ContractionToMinimal
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme K}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (M : Chapter13RegularProperModel C S η) where
  target : Chapter13MinimalRegularModel C S η
  contraction : M.carrier ⟶ target.model.carrier
  proper : IsProper contraction
  birational : Chapter13ProperBirationalMorphism contraction
  over_base : contraction ≫ target.model.structureMap = M.structureMap
  contracts_all : Chapter13ContractsAllVerticalExceptionalCurves M contraction
  generic_identity :
    chapter13InducesIdentityOnGenericFiber η M.structureMap
      target.model.structureMap contraction over_base
      M.generic_fiber_iso target.model.generic_fiber_iso

theorem chapter13_minimal_regular_model_exists
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (hgenus : 0 < C.genus)
    (S : Chapter13ExcellentDedekindScheme K)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier)
    (hη : η = chapter13GenericPointMap S) :
    Nonempty (Chapter13MinimalRegularModel C S η) := by
  sorry

theorem chapter13_regular_model_maps_uniquely_to_minimal
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme K)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier)
    (M : Chapter13RegularProperModel C S η)
    (Mmin : Chapter13MinimalRegularModel C S η) :
    ∃! u : M.carrier ⟶ Mmin.model.carrier,
      ∃ hu : u ≫ Mmin.model.structureMap = M.structureMap,
        chapter13InducesIdentityOnGenericFiber η M.structureMap
          Mmin.model.structureMap u hu M.generic_fiber_iso
          Mmin.model.generic_fiber_iso := by
  sorry

class Chapter13ReducedSpecialFibers
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme K}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (M : Chapter13RegularProperModel C S η) : Prop where
  all_fibers_reduced : ∀ s : S.carrier,
    Chapter13ReducedScheme (M.structureMap.fiber s)

class Chapter13OrdinaryDoublePoints
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme K}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (M : Chapter13RegularProperModel C S η) : Prop where
  ordinary_double_points : Chapter13OrdinaryDoublePointCondition M.structureMap

class Chapter13TransverseComponents
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme K}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (M : Chapter13RegularProperModel C S η) : Prop where
  transverse_components : Chapter13TransverseComponentsCondition M.structureMap

class Chapter13NodeLocalEquation
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme K}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (M : Chapter13RegularProperModel C S η) : Prop where
  node_local_equation : Chapter13NodeLocalEquationCondition M.structureMap

structure Chapter13SemistableModel
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme K)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier) where
  model : Chapter13RegularProperModel C S η
  reduced_special_fibers : Chapter13ReducedSpecialFibers model
  ordinary_double_points : Chapter13OrdinaryDoublePoints model
  transverse_components : Chapter13TransverseComponents model
  node_local_equation : Chapter13NodeLocalEquation model

structure Chapter13SemistableReductionInput
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme K)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier) where
  extension : Chapter13FiniteSeparableExtension K
  normalized_base : Scheme.{u}
  normalized_base_map : normalized_base ⟶ S.carrier
  normalized_base_map_finite : IsFinite normalized_base_map
  normalized_base_is_dedekind : Chapter13DedekindScheme normalized_base
  normalized_base_is_excellent : Chapter13ExcellentScheme normalized_base
  normalized_base_generic_point_data :
    letI : Field extension.extension := extension.field_extension
    LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.Chapter01GenericPointData
      normalized_base extension.extension
  normalized_base_generic_point_map_over :
    letI : Field extension.extension := extension.field_extension
    letI : Algebra K extension.extension := extension.algebra_extension
    normalized_base_generic_point_data.genericPointMap ≫
        normalized_base_map =
      chapter13FieldBaseChangeMap (K := K) (L := extension.extension) ≫
        chapter13GenericPointMap S
  open_set : normalized_base.Opens
  open_nonempty : open_set ≠ ⊥
  nodal_model : Scheme.{u}
  nodal_model_structure_map : nodal_model ⟶ open_set
  nodal_model_is_projective :
    chapter13ProjectiveMorphism nodal_model_structure_map
  nodal_model_is_semistable : Chapter13NodalModelProperty nodal_model_structure_map
  generic_point_map_eq : η = chapter13GenericPointMap S
  nodal_model_generic_point_map :
    letI : Field extension.extension := extension.field_extension
    letI : Algebra K extension.extension := extension.algebra_extension
    AlgebraicGeometry.Spec (CommRingCat.of extension.extension) ⟶ open_set
  nodal_model_generic_point_map_over :
    letI : Field extension.extension := extension.field_extension
    letI : Algebra K extension.extension := extension.algebra_extension
    nodal_model_generic_point_map ≫ open_set.ι =
      normalized_base_generic_point_data.genericPointMap
  nodal_model_generic_fiber_iso :
    letI : Field extension.extension := extension.field_extension
    letI : Algebra K extension.extension := extension.algebra_extension
    Limits.pullback nodal_model_structure_map
        nodal_model_generic_point_map ≅
      chapter13FiniteScalarExtension (L := extension.extension) C
  nodal_model_generic_fiber_iso_over :
    letI : Field extension.extension := extension.field_extension
    letI : Algebra K extension.extension := extension.algebra_extension
    nodal_model_generic_fiber_iso.inv ≫
        Limits.pullback.snd nodal_model_structure_map
          nodal_model_generic_point_map =
      Limits.pullback.snd C.structureMap
        (chapter13FieldBaseChangeMap (K := K) (L := extension.extension))

structure Chapter13SemistableRegularIncarnation
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme K}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (H : Chapter13SemistableReductionInput C S η) where
  candidate : Scheme.{u}
  candidate_structure_map : candidate ⟶ H.normalized_base
  candidate_projective_over_normalized_base :
    chapter13ProjectiveMorphism candidate_structure_map
  candidate_restriction_identification :
    (candidate_structure_map ⁻¹ᵁ H.open_set).toScheme ≅ H.nodal_model
  candidate_restriction_over :
    candidate_restriction_identification.hom ≫ H.nodal_model_structure_map =
      candidate_structure_map ∣_ H.open_set
  regularized : Scheme.{u}
  resolution_map : regularized ⟶ candidate
  proper_birational : Chapter13ProperBirationalMorphism resolution_map
  regular : Chapter13RegularScheme regularized
  structure_map : regularized ⟶ H.normalized_base
  over_base : resolution_map ≫ candidate_structure_map = structure_map
  projective_over_normalized_base : chapter13ProjectiveMorphism structure_map
  proper_over_normalized_base : IsProper structure_map
  integral : IsIntegral regularized
  finite_type :
    LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.Chapter01FiniteType
      structure_map
  flat : Flat structure_map
  relative_dimension_one : Chapter13RelativeDimensionOne structure_map
  absolute_dimension_two : Chapter13AbsoluteDimensionTwo regularized
  restriction_identification :
    (structure_map ⁻¹ᵁ H.open_set).toScheme ≅ H.nodal_model
  restriction_over :
    restriction_identification.hom ≫ H.nodal_model_structure_map =
      structure_map ∣_ H.open_set
  generic_fiber_iso :
    letI : Field H.extension.extension := H.extension.field_extension
    letI : Algebra K H.extension.extension := H.extension.algebra_extension
    Limits.pullback structure_map
        H.normalized_base_generic_point_data.genericPointMap ≅
      chapter13FiniteScalarExtension (L := H.extension.extension) C
  generic_fiber_iso_over :
    letI : Field H.extension.extension := H.extension.field_extension
    letI : Algebra K H.extension.extension := H.extension.algebra_extension
    generic_fiber_iso.inv ≫
        Limits.pullback.snd structure_map
          H.normalized_base_generic_point_data.genericPointMap =
      Limits.pullback.snd C.structureMap
        (chapter13FieldBaseChangeMap (K := K) (L := H.extension.extension))
  generic_fiber_unchanged :
    letI : Field H.extension.extension := H.extension.field_extension
    Chapter13GenericFiberUnchanged
      H.normalized_base_generic_point_data.genericPointMap
      structure_map candidate_structure_map resolution_map over_base
  resolution_isomorphism_on_semistable_open :
    IsIso (resolution_map ∣_
      (candidate_structure_map ⁻¹ᵁ H.open_set))

theorem chapter13_semistable_input_gives_regular_incarnation
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme K)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier)
    (hη : η = chapter13GenericPointMap S)
    (H : Chapter13SemistableReductionInput C S η) :
    Nonempty (Chapter13SemistableRegularIncarnation H) := by
  sorry

/-! ### Book-facing conclusion data -/

def Chapter13HorizontalComponent {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  ∃ η : S, IsGenericPoint η Set.univ ∧ f x = η ∧ Order.coheight x = 1

def Chapter13VerticalComponent (X S : Scheme.{u}) (f : X ⟶ S) (x : X) : Prop :=
  ∃ s : S, IsClosed ({s} : Set S) ∧ f x = s ∧ Order.coheight x = 1

/-! The valuation calculation after a finite base change is recorded as a
positive integral profile.  Its equation is the scheme-independent form of
`e v_E(π') = r(E/Γ) m`. -/
structure Chapter13RamificationMultiplicityProfile where
  base_ramification_index : ℕ
  divisorial_ramification_index : ℕ
  base_component_multiplicity : ℕ
  normalized_component_multiplicity : ℕ
  base_ramification_index_pos : 0 < base_ramification_index
  divisorial_ramification_index_pos : 0 < divisorial_ramification_index
  base_component_multiplicity_pos : 0 < base_component_multiplicity
  normalized_component_multiplicity_pos : 0 < normalized_component_multiplicity
  multiplicity_formula :
    base_ramification_index * normalized_component_multiplicity =
      divisorial_ramification_index * base_component_multiplicity

structure Chapter13BaseChangeVerticalMultiplicity
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme K)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier)
    (M : Chapter13RegularProperModel C S η)
    (E : Chapter13FiniteExtension K)
    (R : Chapter13BaseChangeRepair C S η M E) where
  original_component : M.carrier
  original_vertical :
    Chapter13VerticalComponent M.carrier S.carrier M.structureMap original_component
  normalized_component : R.resolved
  normalized_vertical :
    Chapter13VerticalComponent R.resolved R.normalized_base.carrier
      R.resolved_structure_map normalized_component
  maps_to_original : R.resolved_to_model normalized_component = original_component
  profile : Chapter13RamificationMultiplicityProfile

def Chapter13ValuationExtensionAt (X S : Scheme.{u})
    (_f : X ⟶ S) (x : X) : Prop :=
  ∃ hDomain : IsDomain (X.presheaf.stalk x),
    letI : IsDomain (X.presheaf.stalk x) := hDomain
    IsDiscreteValuationRing (X.presheaf.stalk x)

def Chapter13BadReductionAt (X S : Scheme.{u}) (f : X ⟶ S) (x : X) : Prop :=
  ∃ s : S, f x = s ∧ ¬ Chapter13ReducedScheme (f.fiber s)

def Chapter13BirationalResolution {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  Chapter13ProperBirationalMorphism f

def Chapter13ControlledExceptionalLocus {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∃ E : Set Y, IsClosed E ∧
    (∀ y : Y, y ∈ E → ¬ chapter13RegularAt Y y) ∧
    ∀ y : Y, y ∉ E → ∃ U : Y.Opens, y ∈ U ∧ IsIso (f ∣_ U)

def Chapter13IsomorphismOffSingularLocus {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ y : Y, chapter13RegularAt Y y →
    ∃ U : Y.Opens, y ∈ U ∧ IsIso (f ∣_ U)

structure Chapter13ResolutionComplexity where
  multiplicity : ℕ
  tangent_data : ℕ
  conductor_complexity : ℕ

def chapter13ComplexityLt (a b : Chapter13ResolutionComplexity) : Prop :=
  a.multiplicity < b.multiplicity ∨
    (a.multiplicity = b.multiplicity ∧
      (a.tangent_data < b.tangent_data ∨
        (a.tangent_data = b.tangent_data ∧
          a.conductor_complexity < b.conductor_complexity)))

def Chapter13ResolutionTerminates (_X : Scheme.{u}) : Prop :=
  WellFounded chapter13ComplexityLt

theorem chapter13_resolution_complexity_well_founded :
    WellFounded chapter13ComplexityLt := by
  sorry

structure Chapter13HorizontalDivisorData (X S : Scheme.{u}) (f : X ⟶ S) where
  generic_point : X
  horizontal : Chapter13HorizontalComponent f generic_point
  markings : Finset X
  markings_horizontal : ∀ x : X, x ∈ markings → Chapter13HorizontalComponent f x

structure Chapter13VerticalComponentData (X S : Scheme.{u}) (f : X ⟶ S) where
  component : X
  vertical : Chapter13VerticalComponent X S f component
  valuation_extension : Chapter13ValuationExtensionAt X S f component
  bad_reduction : Option (PLift (Chapter13BadReductionAt X S f component))

structure Chapter13ArithmeticCurveTwoLives
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme K)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier) where
  generic_life : Chapter13SmoothProjectiveCurve K
  generic_life_is_C : generic_life = C
  integral_life : Chapter13RegularProperModel C S η
  generic_point_map_eq : η = chapter13GenericPointMap S
  generic_dimension_one : Chapter13PureDimensionOne generic_life.carrier
  integral_dimension_two : Chapter13AbsoluteDimensionTwo integral_life.carrier
  horizontal_data : Chapter13HorizontalDivisorData
    integral_life.carrier S.carrier integral_life.structureMap
  vertical_data : Chapter13VerticalComponentData
    integral_life.carrier S.carrier integral_life.structureMap

structure Chapter13SurfaceResolutionResult
    {X S : Scheme.{u}} (f : X ⟶ S) where
  resolved : Scheme.{u}
  map : resolved ⟶ X
  reduced : Chapter13ReducedScheme X
  proper : IsProper map
  projective : chapter13ProjectiveMorphism (map ≫ f)
  birational : Chapter13BirationalResolution map
  regular : Chapter13RegularScheme resolved
  dimension_bound : Chapter13SurfaceDimensionBound X
  controlled_exceptional_locus : Chapter13ControlledExceptionalLocus map
  isomorphism_off_singular_locus : Chapter13IsomorphismOffSingularLocus map
  complexity_termination : Chapter13ResolutionTerminates X

theorem chapter13_resolution_descent_cannot_be_infinite
    (c : ℕ → Chapter13ResolutionComplexity)
    (h : ∀ n, chapter13ComplexityLt (c (n + 1)) (c n)) : False := by
  sorry

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter13
