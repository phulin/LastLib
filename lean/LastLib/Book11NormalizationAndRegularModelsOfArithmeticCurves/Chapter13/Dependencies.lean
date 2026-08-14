import Mathlib.AlgebraicGeometry.Birational.Birational
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Algebra.MvPolynomial.Basic

import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter07.Core
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Dependencies

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter13

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter07
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09
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

/-- Book-facing normality, with the componentwise interpretation made explicit. -/
class Chapter13NormalScheme (X : Scheme.{u}) : Prop where
  reduced : IsReduced X
  affine_normal : ∀ (U : X.Opens), IsAffineOpen U → chapter13NormalRing Γ(X, U)

/-- Regularity at a point is regularity of its noetherian local ring. -/
def chapter13RegularAt (X : Scheme.{u}) (x : X) : Prop :=
  IsRegularLocalRing (X.presheaf.stalk x)

class Chapter13RegularScheme (X : Scheme.{u}) : Prop where
  regular_at : ∀ x : X, chapter13RegularAt X x

def chapter13RegularLocus (X : Scheme.{u}) : Set X :=
  {x | chapter13RegularAt X x}

/-- The finite-extension condition on a domain used by the book. -/
def chapter13JapaneseDomain (R : Type u) [CommRing R] : Prop :=
  IsDomain R ∧
    ∀ (L : Type v) [Field L] [Algebra (FractionRing R) L]
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

/- LOCAL_DEPENDENCY_GUESS: these predicates name excellent-scheme properties
not yet bundled by the pinned Mathlib interfaces. -/
class Chapter13GeometricallyRegularFormalFibers (X : Scheme.{u}) : Prop where

class Chapter13UniversallyCatenary (X : Scheme.{u}) : Prop where

class Chapter13SurfaceResolutionCapability (X : Scheme.{u}) : Prop where

/- LOCAL_DEPENDENCY_GUESS: the formal-fiber predicate is not packaged at the
scheme level in the pinned Mathlib tree.  Its field is kept as a named
property so excellence cannot silently be weakened to Nagata finiteness. -/
class Chapter13GoodFormalFibers (X : Scheme.{u}) : Prop where
  geometrically_regular_formal_fibers : Chapter13GeometricallyRegularFormalFibers X

/- LOCAL_DEPENDENCY_GUESS: surface resolution is included only as the
two-dimensional excellent-surface input used by the book, not as a claim about
arbitrary-dimensional resolution. -/
class Chapter13ExcellentScheme (X : Scheme.{u}) : Prop where
  noetherian : IsNoetherian X
  nagata : Chapter13NagataScheme X
  universally_catenary : Chapter13UniversallyCatenary X
  good_formal_fibers : Chapter13GoodFormalFibers X
  regular_locus_open : IsOpen (chapter13RegularLocus X)
  surface_resolution : Chapter13SurfaceResolutionCapability X

class Chapter13OneDimensionalScheme (S : Scheme.{u}) : Prop where

/- LOCAL_DEPENDENCY_GUESS: a Dedekind scheme is represented by the global
integral/noetherian and one-dimensional package needed by the model theorems. -/
class Chapter13DedekindScheme (S : Scheme.{u}) : Prop where
  integral : IsIntegral S
  noetherian : IsNoetherian S
  dimension_one : Chapter13OneDimensionalScheme S

structure Chapter13ExcellentDedekindScheme where
  carrier : Scheme.{u}
  dedekind : Chapter13DedekindScheme carrier
  excellent : Chapter13ExcellentScheme carrier

theorem chapter13_excellent_implies_nagata {X : Scheme.{u}}
    (hX : Chapter13ExcellentScheme X) : Chapter13NagataScheme X :=
  hX.nagata

theorem chapter13_excellent_has_open_regular_locus {X : Scheme.{u}}
    (hX : Chapter13ExcellentScheme X) : IsOpen (chapter13RegularLocus X) :=
  hX.regular_locus_open

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
class Chapter13ValuativeCriterion {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where

class Chapter13ValuativeExtension (f : Scheme.{u} ⟶ Scheme.{u}) : Prop where
  extension_property : Chapter13ValuativeCriterion f

/- LOCAL_DEPENDENCY_GUESS: geometric regularity of all geometric fibers is
kept as a separate relative predicate because `Smooth` in Mathlib exposes the
flatness implication but not this book-facing fiber ledger. -/
class Chapter13GeometricallyRegularFibers {X S : Scheme.{u}} (f : X ⟶ S) : Prop where

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

/-! ### Flatness over a Dedekind base -/

/-- Local affine-chart formulation of absence of torsion from the base. -/
def chapter13NoVerticalTorsion {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ (U : S.Opens) (hU : IsAffineOpen U)
    (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U),
    ∀ {r : Γ(S, U)} {a : Γ(X, V)}, r ≠ 0 →
      (f.appLE U V hVU).hom r * a = 0 → a = 0

/- LOCAL_DEPENDENCY_GUESS: “well-behaved fibers” is retained as a named
relative-fiber interface; it is intentionally not identified with reducedness. -/
class Chapter13WellBehavedFiberCondition {X S : Scheme.{u}} (f : X ⟶ S) : Prop where

class Chapter13WellBehavedFibers {X S : Scheme.{u}} (f : X ⟶ S) : Prop where
  fiber_condition : Chapter13WellBehavedFiberCondition f

/- LOCAL_DEPENDENCY_GUESS: reducedness of every special fiber is kept distinct
from flatness and from the weaker fiber ledger above. -/
class Chapter13ReducedFiberCondition {X S : Scheme.{u}} (f : X ⟶ S) : Prop where

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

class Chapter13GeometricallyConnected (X : Scheme.{u}) : Prop where

class Chapter13PureDimensionOne (X : Scheme.{u}) : Prop where

class Chapter13RelativeDimensionOne {X S : Scheme.{u}} (f : X ⟶ S) : Prop where

class Chapter13AbsoluteDimensionTwo (X : Scheme.{u}) : Prop where

/- LOCAL_DEPENDENCY_GUESS: the following named predicates keep the geometric
relations from being collapsed into untyped `Prop` fields. -/
class Chapter13GenericClosureProperty {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where

class Chapter13NoUnwantedVerticalComponents {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where

class Chapter13BirationalMorphism {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where

class Chapter13ProperBirationalMorphism {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where

class Chapter13UniversalNormalization {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where

class Chapter13AgreesOnGoodOpen (X : Scheme.{u}) : Prop where

class Chapter13GenericCompatibility (X : Scheme.{u}) : Prop where

class Chapter13FiniteOnGenericFiber {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where

class Chapter13DesiredGenericComponent (X : Scheme.{u}) : Prop where

class Chapter13VerticalExceptionalProperty {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where

class Chapter13ProjectiveLineAfterResidueExtension {X Y : Scheme.{u}}
    (f : X ⟶ Y) : Prop where

class Chapter13ContractsAllVerticalExceptionalCurves
    {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where

class Chapter13NodalModelProperty (X : Scheme.{u}) : Prop where

class Chapter13GenericFiberUnchanged {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where

/-! ### Generic curves and arithmetic surface models -/

structure Chapter13SmoothProjectiveCurve (K : Type u) [Field K] where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ AlgebraicGeometry.Spec (CommRingCat.of K)
  smooth : Smooth structureMap
  proper : IsProper structureMap
  projective : chapter13ProjectiveMorphism structureMap
  geometrically_connected : Chapter13GeometricallyConnected carrier
  pure_dimension_one : Chapter13PureDimensionOne carrier
  genus : ℕ

structure Chapter13ArithmeticSurfaceData (X S : Scheme.{u}) (f : X ⟶ S) where
  base_dedekind : Chapter13DedekindScheme S
  integral_total_space : IsIntegral X
  regular_total_space : Chapter13RegularScheme X
  flat_over_base : Flat f
  relative_dimension_one : Chapter13RelativeDimensionOne f
  absolute_dimension_two : Chapter13AbsoluteDimensionTwo X

structure Chapter13RegularProperModel {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier) where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ S.carrier
  flat : Flat structureMap
  finite_type : LocallyOfFiniteType structureMap
  proper : IsProper structureMap
  projective : chapter13ProjectiveMorphism structureMap
  regular : Chapter13RegularScheme carrier
  relative_dimension_one : Chapter13RelativeDimensionOne structureMap
  absolute_dimension_two : Chapter13AbsoluteDimensionTwo carrier
  generic_fiber_iso : Limits.pullback structureMap η ≅ C.carrier

abbrev Chapter13Model {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier) :=
  Chapter13RegularProperModel C S η

structure Chapter13PrescribedGoodOpenData {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier) where
  open : S.carrier.Opens
  nonempty : open.Nonempty
  prescribed_model : Scheme.{u}
  prescribed_map : prescribed_model ⟶ open
  prescribed_smooth : Smooth prescribed_map
  prescribed_projective : chapter13ProjectiveMorphism prescribed_map

structure Chapter13GoodOpenRestriction
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (M : Chapter13RegularProperModel C S η)
    (G : Chapter13PrescribedGoodOpenData C S η) : Prop where
  restriction_identification : Chapter13GenericCompatibility M.carrier

theorem chapter13_regular_proper_model_exists {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier) :
    Nonempty (Chapter13RegularProperModel C S η) := by
  sorry

theorem chapter13_regular_model_preserves_a_prescribed_good_open
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier)
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
    (S : Chapter13ExcellentDedekindScheme)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier)
    (E : Chapter13GenericProjectiveEmbedding C) where
  closure : Scheme.{u}
  closure_map : closure ⟶ S.carrier
  projective : chapter13ProjectiveMorphism closure_map
  generic_closure : Chapter13GenericClosureProperty closure closure_map
  no_unwanted_vertical_components : Chapter13NoUnwantedVerticalComponents
    closure closure_map

structure Chapter13NormalizationStage
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (E : Chapter13GenericProjectiveEmbedding C)
    (P : Chapter13ProjectiveClosureData C S η E) where
  normalized : Scheme.{u}
  normalization_map : normalized ⟶ P.closure
  finite : IsFinite normalization_map
  normal : Chapter13NormalScheme normalized
  birational : Chapter13BirationalMorphism normalization_map
  universal : Chapter13UniversalNormalization normalization_map

structure Chapter13RegularizationStage
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    {E : Chapter13GenericProjectiveEmbedding C}
    (P : Chapter13ProjectiveClosureData C S η E)
    (N : Chapter13NormalizationStage E P) where
  regularized : Scheme.{u}
  resolution_map : regularized ⟶ N.normalized
  proper : IsProper resolution_map
  proper_birational : Chapter13ProperBirationalMorphism resolution_map
  projective : chapter13ProjectiveMorphism
    (resolution_map ≫ P.closure_map)
  regular : Chapter13RegularScheme regularized
  agrees_on_good_open : Chapter13AgreesOnGoodOpen regularized

structure Chapter13ConstructionPipeline
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier) where
  embedding : Chapter13GenericProjectiveEmbedding C
  closure : Chapter13ProjectiveClosureData C S η embedding
  normalization : Chapter13NormalizationStage embedding closure
  regular_model : Chapter13RegularizationStage closure normalization
  normalization_arrow : normalization.normalized ⟶ closure.closure
  regularization_arrow : regular_model.regularized ⟶ normalization.normalized
  normalization_arrow_eq : normalization_arrow = normalization.normalization_map
  regularization_arrow_eq : regularization_arrow = regular_model.resolution_map

/- LOCAL_DEPENDENCY_GUESS: the preceding chapters supply the existence of the
closure and surface-resolution stages; this constructor records their exact
interface without taking the desired final model as a hypothesis. -/
theorem chapter13_construction_pipeline_exists {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier) :
    Nonempty (Chapter13ConstructionPipeline C S η) := by
  sorry

structure Chapter13CommonRegularDomination
    {S : Scheme.{u}} (X Y : Scheme.{u}) (fX : X ⟶ S) (fY : Y ⟶ S) where
  carrier : Scheme.{u}
  base : carrier ⟶ S
  to_left : carrier ⟶ X
  to_right : carrier ⟶ Y
  over_base_left : to_left ≫ fX = base
  over_base_right : to_right ≫ fY = base
  proper_left : IsProper to_left
  proper_right : IsProper to_right
  regular : Chapter13RegularScheme carrier
  generic_compatibility : Chapter13GenericCompatibility carrier

structure Chapter13GenericFiniteCorrespondence {K : Type u} [Field K] where
  source : Scheme.{u}
  target : Scheme.{u}
  map : source ⟶ target
  finite_on_generic_fiber : Chapter13FiniteOnGenericFiber map

/-! ### Base change and the minimal/semistable endpoints -/

structure Chapter13FiniteSeparableExtension (K : Type u) [Field K] where
  extension : Type v
  [field_extension : Field extension]
  [algebra_extension : Algebra K extension]
  [finite_extension : FiniteDimensional K extension]
  [separable_extension : Algebra.IsSeparable K extension]

structure Chapter13BaseChangeRepair
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier)
    (M : Chapter13RegularProperModel C S η)
    (E : Chapter13FiniteSeparableExtension K) where
  base_changed : Scheme.{v}
  base_changed_reduced : IsReduced base_changed
  normalized : Scheme.{v}
  normalization_map : normalized ⟶ base_changed
  normalization_finite : IsFinite normalization_map
  normalized_normal : Chapter13NormalScheme normalized
  resolved : Scheme.{v}
  resolution_map : resolved ⟶ normalized
  resolved_regular : Chapter13RegularScheme resolved
  resolved_to_base_changed : resolved ⟶ base_changed
  resolution_over_base :
    resolution_map ≫ normalization_map = resolved_to_base_changed
  resolved_projective : chapter13ProjectiveMorphism resolved_to_base_changed
  desired_generic_component : Chapter13DesiredGenericComponent resolved

theorem chapter13_normalize_and_resolve_after_finite_base_change
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier)
    (M : Chapter13RegularProperModel C S η)
    (E : Chapter13FiniteSeparableExtension K) :
    Nonempty (Chapter13BaseChangeRepair C S η M E) := by
  sorry

structure Chapter13VerticalExceptionalCurve
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (M : Chapter13RegularProperModel C S η) where
  carrier : Scheme.{u}
  inclusion : carrier ⟶ M.carrier
  vertical : Chapter13VerticalExceptionalProperty inclusion
  projective_line_after_residue_extension :
    Chapter13ProjectiveLineAfterResidueExtension inclusion
  normal_bundle_degree : ℤ
  normal_bundle_degree_eq_minus_one : normal_bundle_degree = -1

def chapter13RelativelyMinimal
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (M : Chapter13RegularProperModel C S η) : Prop :=
  ¬ Nonempty (Chapter13VerticalExceptionalCurve M)

structure Chapter13MinimalRegularModel
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier) where
  model : Chapter13RegularProperModel C S η
  positive_genus : 0 < C.genus
  relatively_minimal : chapter13RelativelyMinimal model

structure Chapter13ContractionToMinimal
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (M : Chapter13RegularProperModel C S η) where
  target : Chapter13MinimalRegularModel C S η
  contraction : M.carrier ⟶ target.model.carrier
  proper : IsProper contraction
  over_base : contraction ≫ target.model.structureMap = M.structureMap
  contracts_all : Chapter13ContractsAllVerticalExceptionalCurves contraction

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
        rw [Category.assoc, hu]
        simp)
  eX.inv ≫ uη ≫ eY.hom = 𝟙 C.carrier

theorem chapter13_minimal_regular_model_exists
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (hgenus : 0 < C.genus)
    (S : Chapter13ExcellentDedekindScheme)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier) :
    Nonempty (Chapter13MinimalRegularModel C S η) := by
  sorry

theorem chapter13_regular_model_maps_uniquely_to_minimal
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme)
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
    {S : Chapter13ExcellentDedekindScheme}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (M : Chapter13RegularProperModel C S η) : Prop where

class Chapter13OrdinaryDoublePoints
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (M : Chapter13RegularProperModel C S η) : Prop where

class Chapter13TransverseComponents
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (M : Chapter13RegularProperModel C S η) : Prop where

class Chapter13NodeLocalEquation
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (M : Chapter13RegularProperModel C S η) : Prop where

structure Chapter13SemistableModel
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier) where
  model : Chapter13RegularProperModel C S η
  reduced_special_fibers : Chapter13ReducedSpecialFibers model
  ordinary_double_points : Chapter13OrdinaryDoublePoints model
  transverse_components : Chapter13TransverseComponents model
  node_local_equation : Chapter13NodeLocalEquation model

structure Chapter13SemistableReductionInput
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier) where
  extension : Chapter13FiniteSeparableExtension K
  normalized_base : Scheme.{v}
  normalized_base_is_dedekind : Chapter13DedekindScheme normalized_base
  normalized_base_is_excellent : Chapter13ExcellentScheme normalized_base
  nodal_model : Scheme.{v}
  nodal_model_structure_map : nodal_model ⟶ normalized_base
  nodal_model_is_projective :
    chapter13ProjectiveMorphism nodal_model_structure_map
  nodal_model_is_semistable : Chapter13NodalModelProperty nodal_model

structure Chapter13SemistableRegularIncarnation
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (H : Chapter13SemistableReductionInput C S η) where
  regularized : Scheme.{v}
  resolution_map : regularized ⟶ H.nodal_model
  proper_birational : Chapter13ProperBirationalMorphism resolution_map
  regular : Chapter13RegularScheme regularized
  structure_map : regularized ⟶ H.normalized_base
  projective_over_normalized_base : chapter13ProjectiveMorphism structure_map
  generic_fiber_unchanged :
    Chapter13GenericFiberUnchanged resolution_map

theorem chapter13_semistable_input_gives_regular_incarnation
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier)
    (H : Chapter13SemistableReductionInput C S η) :
    Nonempty (Chapter13SemistableRegularIncarnation H) := by
  sorry

/-! ### Book-facing conclusion data -/

class Chapter13HorizontalComponent (X : Scheme.{u}) (x : X) : Prop where

class Chapter13GenericPointRetained (X : Scheme.{u}) (x : X) : Prop where

class Chapter13VerticalComponent (X S : Scheme.{u}) (f : X ⟶ S) (x : X) : Prop where

class Chapter13ValuationExtensionAt (X S : Scheme.{u})
    (f : X ⟶ S) (x : X) : Prop where

class Chapter13BadReductionAt (X S : Scheme.{u}) (f : X ⟶ S) (x : X) : Prop where

class Chapter13BirationalResolution {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where

class Chapter13ControlledVerticalExceptionalLocus
    {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where

class Chapter13IsomorphismOffSingularLocus
    {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where

class Chapter13ResolutionTerminates (X : Scheme.{u}) : Prop where

structure Chapter13HorizontalDivisorData (X : Scheme.{u}) where
  generic_point : X
  horizontal : Chapter13HorizontalComponent X generic_point
  markings : Finset X
  generic_point_retained : Chapter13GenericPointRetained X generic_point

structure Chapter13VerticalComponentData (X S : Scheme.{u}) (f : X ⟶ S) where
  component : X
  vertical : Chapter13VerticalComponent X S f component
  valuation_extension : Chapter13ValuationExtensionAt X S f component
  bad_reduction : Chapter13BadReductionAt X S f component

structure Chapter13ArithmeticCurveTwoLives
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier) where
  generic_life : Chapter13SmoothProjectiveCurve K
  generic_life_is_C : generic_life = C
  integral_life : Chapter13RegularProperModel C S η
  generic_dimension_one : Chapter13PureDimensionOne generic_life.carrier
  integral_dimension_two : Chapter13AbsoluteDimensionTwo integral_life.carrier
  horizontal_data : Chapter13HorizontalDivisorData integral_life.carrier
  vertical_data : Chapter13VerticalComponentData
    integral_life.carrier S.carrier integral_life.structureMap

structure Chapter13SurfaceResolutionResult (X : Scheme.{u}) where
  resolved : Scheme.{u}
  map : resolved ⟶ X
  proper : IsProper map
  birational : Chapter13BirationalResolution map
  regular : Chapter13RegularScheme resolved
  controlled_vertical_exceptional_curves :
    Chapter13ControlledVerticalExceptionalLocus map
  isomorphism_off_singular_locus : Chapter13IsomorphismOffSingularLocus map
  complexity_termination : Chapter13ResolutionTerminates X

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

theorem chapter13_resolution_complexity_well_founded :
    WellFounded chapter13ComplexityLt := by
  sorry

theorem chapter13_resolution_descent_cannot_be_infinite
    (c : ℕ → Chapter13ResolutionComplexity)
    (h : ∀ n, chapter13ComplexityLt (c (n + 1)) (c n)) : False := by
  sorry

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter13
