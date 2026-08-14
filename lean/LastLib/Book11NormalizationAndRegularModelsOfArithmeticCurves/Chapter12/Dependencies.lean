import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Dependencies
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.Section01DescentOfMaps
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.Dependencies
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.Section03StandingConventions
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter03.Core
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04.Dependencies
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.Section04LocalityAndProjectivity
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter08.Section04Termination

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter12

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter03
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter08
open scoped AlgebraicGeometry

universe u v

/-! ## Shared interfaces for the model package

The preceding chapters package affine normalizations and surface resolution, but the chapter
works with an arbitrary excellent Dedekind scheme and with generic curves over its function
field.  The records below are the weakest interfaces needed to pass those constructions between
the modular, Shimura, semistable, and correspondence applications.
-/

/- LOCAL_DEPENDENCY_GUESS: The workspace does not yet expose the intervening Chapters 9--11
 interfaces for semistability, moduli, or quotient actions.  The domain-specific `Prop` fields
 below name those hypotheses without smuggling any later conclusion into the API. -/

structure Chapter12ExcellentDedekindBase (S : Scheme.{u}) (K : Type u) [Field K] where
  dedekind : Chapter01DedekindBase S K
  excellent : Chapter01ExcellentScheme S

abbrev chapter12GenericPointMap {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter12ExcellentDedekindBase S K) :
    Spec (CommRingCat.of K) ⟶ S :=
  B.dedekind.genericPointMap

def chapter12GenericComponentControl
    {K : Type u} [Field K]
    (C : Chapter01SmoothProperCurveOverField K) : Prop :=
  GeometricallyConnected C.structureMap

theorem chapter12_geometricallyConnected_controls_generic_components
    {K : Type u} [Field K] (C : Chapter01SmoothProperCurveOverField K) :
    chapter12GenericComponentControl C :=
  C.geometricallyConnected

/- A model includes the generic-fiber map explicitly.  In particular, properness is not silently
   identified with projectivity or with the existence of a chosen embedding. -/
structure Chapter12FlatProjectiveModel
    {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter12ExcellentDedekindBase S K)
    (C : Chapter01SmoothProperCurveOverField K) where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ S
  flat : Flat structureMap
  finiteType : Chapter01FiniteType structureMap
  projective : Chapter07IsProjectiveMorphism structureMap
  proper : IsProper structureMap
  integral : IsIntegral carrier
  genericFiberIso : pullback structureMap (chapter12GenericPointMap B) ≅ C.carrier
  genericFiberIso_over :
    genericFiberIso.hom ≫ C.structureMap =
      pullback.snd structureMap (chapter12GenericPointMap B)

instance {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K}
    (M : Chapter12FlatProjectiveModel B C) : IsIntegral M.carrier :=
  M.integral

instance {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K}
    (M : Chapter12FlatProjectiveModel B C) : IsProper M.structureMap :=
  M.proper

structure Chapter12NormalFlatProjectiveModel
    {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter12ExcellentDedekindBase S K)
    (C : Chapter01SmoothProperCurveOverField K)
    extends Chapter12FlatProjectiveModel B C where
  normal : Chapter07NormalIntegralScheme carrier

structure Chapter12RegularFlatProjectiveModel
    {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter12ExcellentDedekindBase S K)
    (C : Chapter01SmoothProperCurveOverField K)
    extends Chapter12FlatProjectiveModel B C where
  locallyNoetherian : IsLocallyNoetherian carrier
  regular : Chapter04RegularScheme carrier

abbrev chapter12NormalModelToFlat
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K}
    (M : Chapter12NormalFlatProjectiveModel B C) :
    Chapter12FlatProjectiveModel B C :=
  M.toChapter12FlatProjectiveModel

abbrev chapter12RegularModelToFlat
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K}
    (M : Chapter12RegularFlatProjectiveModel B C) :
    Chapter12FlatProjectiveModel B C :=
  M.toChapter12FlatProjectiveModel

/-! ### Prescribed open models and restriction bridges -/

structure Chapter12SmoothProjectiveOpenModel
    {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter12ExcellentDedekindBase S K)
    (C : Chapter01SmoothProperCurveOverField K)
    (U : S.Opens) where
  open_nonempty : U ≠ ⊥
  carrier : Scheme.{u}
  structureMap : carrier ⟶ U.toScheme
  finiteType : Chapter01FiniteType structureMap
  projective : Chapter07IsProjectiveMorphism structureMap
  proper : IsProper structureMap
  smooth : Smooth structureMap
  genericMap : Spec (CommRingCat.of K) ⟶ U.toScheme
  genericMap_over : genericMap ≫ U.ι = chapter12GenericPointMap B
  genericFiberIso : pullback structureMap genericMap ≅ C.carrier
  genericFiberIso_over :
    genericFiberIso.hom ≫ C.structureMap = pullback.snd structureMap genericMap

instance {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K} {U : S.Opens}
    (M : Chapter12SmoothProjectiveOpenModel B C U) : Smooth M.structureMap :=
  M.smooth

abbrev chapter12ModelRestriction
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K}
    (M : Chapter12FlatProjectiveModel B C) (U : S.Opens) :
    (M.structureMap ⁻¹ᵁ U).toScheme ⟶ U.toScheme :=
  M.structureMap ∣_ U

theorem chapter12_model_restriction_is_projective
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K}
    (M : Chapter12FlatProjectiveModel B C) (U : S.Opens) :
    Chapter07IsProjectiveMorphism (chapter12ModelRestriction M U) := by
  sorry

structure Chapter12ModelExtension
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K} {U : S.Opens}
    (M : Chapter12SmoothProjectiveOpenModel B C U)
    (N : Chapter12FlatProjectiveModel B C) where
  openIso : M.carrier ≅ (N.structureMap ⁻¹ᵁ U).toScheme
  over_base : openIso.hom ≫
      (chapter12ModelRestriction (B := B) (C := C) N U) = M.structureMap

theorem chapter12_model_extension_restricts_to
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K} {U : S.Opens}
    {M : Chapter12SmoothProjectiveOpenModel B C U}
    {N : Chapter12FlatProjectiveModel B C}
    (E : Chapter12ModelExtension M N) :
    E.openIso.hom ≫ chapter12ModelRestriction N U = M.structureMap :=
  E.over_base

structure Chapter12RegularModification
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K} {U : S.Opens}
    (M : Chapter12SmoothProjectiveOpenModel B C U)
    (N : Chapter12NormalFlatProjectiveModel B C)
    (R : Chapter12RegularFlatProjectiveModel B C)
    (normalExtension : Chapter12ModelExtension M (chapter12NormalModelToFlat N))
    (regularExtension : Chapter12ModelExtension M (chapter12RegularModelToFlat R)) where
  map : R.carrier ⟶ N.carrier
  over_base : (map ≫ N.structureMap) = R.structureMap
  projective : Chapter07IsProjectiveMorphism map
  proper : IsProper map
  birational : Chapter07Birational map
  identical_over_U :
    map.resLE (N.structureMap ⁻¹ᵁ U) (R.structureMap ⁻¹ᵁ U) (by
      rw [← Scheme.Hom.comp_preimage, over_base]) =
      regularExtension.openIso.inv ≫ normalExtension.openIso.hom

/-! ### Base change, normalization, and resolution records -/

structure Chapter12FiniteSeparableExtension
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Prop where
  separable : Algebra.IsSeparable K L

def chapter12FieldBaseChangeMap
    (K L : Type u) [Field K] [Field L] [Algebra K L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K L))

abbrev chapter12FieldBaseChange
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of K)) : Scheme.{u} :=
  pullback c (chapter12FieldBaseChangeMap K L)

abbrev chapter12FieldBaseChangedStructureMap
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of K)) :
    chapter12FieldBaseChange (K := K) (L := L) C c ⟶ Spec (CommRingCat.of L) :=
  pullback.snd c (chapter12FieldBaseChangeMap K L)

structure Chapter12NormalizedDedekindBase
    {S : Scheme.{u}} {K L : Type u} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L]
    (B : Chapter12ExcellentDedekindBase S K) where
  carrier : Scheme.{u}
  map : carrier ⟶ S
  finite : IsFinite map
  normal : Chapter07NormalIntegralScheme carrier
  dedekind : Chapter01DedekindScheme carrier
  integralBase : Chapter01DedekindBase carrier L
  excellent : Chapter01ExcellentScheme carrier
  genericMap : Spec (CommRingCat.of L) ⟶ carrier
  genericMap_eq_integralBase : genericMap = integralBase.genericPointMap
  genericMap_over : genericMap ≫ map =
    chapter12FieldBaseChangeMap K L ≫ chapter12GenericPointMap B

def chapter12NormalizedBaseAsExcellentDedekindBase
    {S : Scheme.{u}} {K L : Type u} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L]
    {B : Chapter12ExcellentDedekindBase S K}
    (B' : Chapter12NormalizedDedekindBase (K := K) (L := L) B) :
    Chapter12ExcellentDedekindBase B'.carrier L where
  dedekind := B'.integralBase
  excellent := B'.excellent

structure Chapter12ReducedBaseChange
    {S : Scheme.{u}} {K L : Type u} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K}
    (M : Chapter12FlatProjectiveModel B C)
    (B' : Chapter12NormalizedDedekindBase (K := K) (L := L) B) where
  carrier : Scheme.{u}
  map : carrier ⟶ pullback M.structureMap B'.map
  reduced : IsReduced carrier
  projective : Chapter07IsProjectiveMorphism map

structure Chapter12NormalizedReducedBaseChange
    {S : Scheme.{u}} {K L : Type u} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K}
    (M : Chapter12FlatProjectiveModel B C)
    (B' : Chapter12NormalizedDedekindBase (K := K) (L := L) B) extends
      Chapter12ReducedBaseChange M B' where
  normalizationCarrier : Scheme.{u}
  normalization : normalizationCarrier ⟶ carrier
  normalization_finite : IsFinite normalization
  normalization_integral : IsIntegralHom normalization
  normalization_birational : Chapter07Birational normalization
  normalized : Chapter07NormalIntegralScheme normalizationCarrier

structure Chapter12ResolvedBaseChange
    {S : Scheme.{u}} {K L : Type u} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K}
    (M : Chapter12FlatProjectiveModel B C)
    (B' : Chapter12NormalizedDedekindBase (K := K) (L := L) B) extends
      Chapter12NormalizedReducedBaseChange M B' where
  resolvedCarrier : Scheme.{u}
  resolution : resolvedCarrier ⟶ normalizationCarrier
  locallyNoetherian : IsLocallyNoetherian resolvedCarrier
  regular : Chapter04RegularScheme resolvedCarrier
  resolution_projective : Chapter07IsProjectiveMorphism resolution
  resolution_proper : IsProper resolution
  resolution_birational : Chapter07Birational resolution
  structureMap : resolvedCarrier ⟶ B'.carrier
  structureMap_projective : Chapter07IsProjectiveMorphism structureMap
  structureMap_factor :
    structureMap = resolution ≫ normalization ≫ map ≫
      pullback.snd M.structureMap B'.map
  flat : Flat structureMap

/-! ### Rational maps, graphs, and proper correspondences -/

structure Chapter12RationalMapOver
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) where
  domain : X.Opens
  dense : Dense (domain : Set X)
  map : domain.toScheme ⟶ Y
  over_base : (map ≫ g) = (domain.ι ≫ f)

def chapter12RationalGraph
    {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (r : Chapter12RationalMapOver f g) :
    r.domain.toScheme ⟶ pullback f g :=
  pullback.lift r.domain.ι r.map r.over_base.symm

structure Chapter12ProperCorrespondence
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ S
  left : carrier ⟶ X
  right : carrier ⟶ Y
  left_over : left ≫ f = structureMap
  right_over : right ≫ g = structureMap
  left_proper : IsProper left
  right_proper : IsProper right

structure Chapter12GraphClosure
    {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (r : Chapter12RationalMapOver f g) extends
      Chapter12ProperCorrespondence f g where
  inclusion : carrier ⟶ pullback f g
  inclusion_closed : IsClosedImmersion inclusion
  left_eq : left = inclusion ≫ pullback.fst f g
  right_eq : right = inclusion ≫ pullback.snd f g
  contains_graph : ∃ q : r.domain.toScheme ⟶ carrier,
    q ≫ inclusion = chapter12RationalGraph r
  is_graph_closure : Prop

def chapter12GraphClosureToCorrespondence
    {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {r : Chapter12RationalMapOver f g}
    (G : Chapter12GraphClosure r) : Chapter12ProperCorrespondence f g :=
  G.toChapter12ProperCorrespondence

structure Chapter12ResolvedNormalizedGraph
    {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {r : Chapter12RationalMapOver f g}
    (G : Chapter12GraphClosure r) where
  normalizedCarrier : Scheme.{u}
  normalization : normalizedCarrier ⟶ G.carrier
  normalization_finite : IsFinite normalization
  normalization_integral : IsIntegralHom normalization
  normalized : Chapter07NormalIntegralScheme normalizedCarrier
  normalization_birational : Chapter07Birational normalization
  carrier : Scheme.{u}
  resolution : carrier ⟶ normalizedCarrier
  locallyNoetherian : IsLocallyNoetherian carrier
  regular : Chapter04RegularScheme carrier
  resolution_projective : Chapter07IsProjectiveMorphism resolution
  resolution_proper : IsProper resolution
  resolution_birational : Chapter07Birational resolution
  left : carrier ⟶ X
  right : carrier ⟶ Y
  left_factor : left = resolution ≫ normalization ≫ G.left
  right_factor : right = resolution ≫ normalization ≫ G.right
  left_proper : IsProper left
  right_proper : IsProper right

def chapter12ResolvedGraphCorrespondence
    {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {r : Chapter12RationalMapOver f g}
    (G : Chapter12GraphClosure r)
    (Z : Chapter12ResolvedNormalizedGraph G) :
    Chapter12ProperCorrespondence f g where
  carrier := Z.carrier
  structureMap := Z.left ≫ f
  left := Z.left
  right := Z.right
  left_over := rfl
  right_over := by sorry
  left_proper := Z.left_proper
  right_proper := Z.right_proper

/-! ### Generic maps and finite correspondence collections -/

structure Chapter12FiniteGenericMap
    {K : Type u} [Field K]
    (C D : Chapter01SmoothProperCurveOverField K) where
  map : C.carrier ⟶ D.carrier
  finite : IsFinite map
  over_base : (map ≫ D.structureMap) = C.structureMap

structure Chapter12FiniteGenericCorrespondence
    (K : Type u) [Field K]
    (C D : Chapter01SmoothProperCurveOverField K) where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ Spec (CommRingCat.of K)
  left : carrier ⟶ C.carrier
  right : carrier ⟶ D.carrier
  left_over : left ≫ C.structureMap = structureMap
  right_over : right ≫ D.structureMap = structureMap
  left_finite : IsFinite left
  right_finite : IsFinite right

structure Chapter12FiniteGenericCorrespondenceModelExtension
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C D : Chapter01SmoothProperCurveOverField K}
    (X : Chapter12FlatProjectiveModel B C)
    (Y : Chapter12FlatProjectiveModel B D)
    (F : Chapter12FiniteGenericCorrespondence K C D) where
  correspondence : Chapter12ProperCorrespondence X.structureMap Y.structureMap
  generic_correspondence_agreement : Prop

structure Chapter12FiniteProjectiveModelSystem
    {S : Scheme.{u}} {K : Type u} [Field K]
  (B : Chapter12ExcellentDedekindBase S K)
    (C : Chapter01SmoothProperCurveOverField K) where
  modelIndex : Type u
  finiteModels : Finite modelIndex
  model : modelIndex → Chapter12FlatProjectiveModel B C
  rationalMapIndex : Type u
  finiteRationalMaps : Finite rationalMapIndex
  rationalSource : rationalMapIndex → modelIndex
  rationalTarget : rationalMapIndex → modelIndex
  rationalMap : ∀ j,
    Chapter12RationalMapOver
      (model (rationalSource j)).structureMap
      (model (rationalTarget j)).structureMap
  correspondenceIndex : Type u
  finiteCorrespondences : Finite correspondenceIndex
  correspondenceSource : correspondenceIndex → modelIndex
  correspondenceTarget : correspondenceIndex → modelIndex
  correspondence : correspondenceIndex →
    Chapter12FiniteGenericCorrespondence K C C

structure Chapter12CommonRegularDomination
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K}
    (F : Chapter12FiniteProjectiveModelSystem B C) where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ S
  flat : Flat structureMap
  finiteType : Chapter01FiniteType structureMap
  projective : Chapter07IsProjectiveMorphism structureMap
  proper : IsProper structureMap
  integral : IsIntegral carrier
  locallyNoetherian : IsLocallyNoetherian carrier
  regular : Chapter04RegularScheme carrier
  dominates : ∀ i, ∃ q : carrier ⟶ (F.model i).carrier,
    q ≫ (F.model i).structureMap = structureMap
  graphClosure : ∀ j,
    Nonempty (Chapter12GraphClosure (F.rationalMap j))
  resolvedGraph : ∀ j,
    Nonempty (Chapter12ResolvedNormalizedGraph (Classical.choice (graphClosure j)))
  correspondenceClosure : ∀ j,
    Nonempty (Chapter12FiniteGenericCorrespondenceModelExtension
      (F.model (F.correspondenceSource j))
      (F.model (F.correspondenceTarget j))
      (F.correspondence j))
  correspondenceDomination : ∀ j,
    ∃ q : carrier ⟶
        (Classical.choice (correspondenceClosure j)).correspondence.carrier,
      q ≫ (Classical.choice (correspondenceClosure j)).correspondence.structureMap =
        structureMap

/-! ### Minimal regular models and vertical exceptional contractions -/

structure Chapter12VerticalExceptionalCurve
    {X S : Scheme.{u}} (f : X ⟶ S) where
  carrier : Scheme.{u}
  inclusion : carrier ⟶ X
  vertical : Prop
  exceptional : Prop
  rational : Prop

structure Chapter12MinimalRegularProperModel
    {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter12ExcellentDedekindBase S K)
  (C : Chapter01SmoothProperCurveOverField K) where
  model : Chapter12RegularFlatProjectiveModel B C
  minimal : ∀ E : Chapter12VerticalExceptionalCurve model.structureMap,
    E.vertical → E.exceptional → ¬ E.rational
  uniqueness : ∀ N : Chapter12RegularFlatProjectiveModel B C,
    ∃ e : N.carrier ≅ model.carrier, e.hom ≫ model.structureMap = N.structureMap

structure Chapter12MinimalContraction
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K}
    (R : Chapter12RegularFlatProjectiveModel B C) where
  minimal : Chapter12MinimalRegularProperModel B C
  contraction : R.carrier ⟶ minimal.model.carrier
  proper : IsProper contraction
  contracts_vertical_exceptional : Prop

structure Chapter12GenusData
    {K : Type u} [Field K] (C : Chapter01SmoothProperCurveOverField K)
    (g : ℕ) where
  geometric_genus : Prop

def Chapter12PositiveGenus
    {K : Type u} [Field K] (C : Chapter01SmoothProperCurveOverField K) : Prop :=
  ∃ g : ℕ, 0 < g ∧ Nonempty (Chapter12GenusData C g)

/-! ### Semistable local equations and algebraization input -/

def Chapter12Uniformizer
    (R : Type u) [CommRing R] [IsLocalRing R] (π : R) : Prop :=
  ¬ IsUnit π ∧ Ideal.span ({π} : Set R) = IsLocalRing.maximalIdeal R

abbrev chapter12NodePowerSeries (R : Type u) [CommRing R] :=
  MvPowerSeries (Fin 2) R

def chapter12NodeEquation
    (R : Type u) [CommRing R] (π : R) : chapter12NodePowerSeries R :=
  MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) -
    algebraMap R (chapter12NodePowerSeries R) π

def chapter12NodeIdeal
    (R : Type u) [CommRing R] (π : R) : Ideal (chapter12NodePowerSeries R) :=
  Ideal.span {chapter12NodeEquation R π}

abbrev chapter12NodeCompletedLocalRing
    (R : Type u) [CommRing R] (π : R) :=
  chapter12NodePowerSeries R ⧸ chapter12NodeIdeal R π

structure Chapter12NodeCompletedLocalPresentation
    (R A : Type u) [CommRing R] [CommRing A] [IsLocalRing R] [Algebra R A]
    (π : R) where
  uniformizer : Chapter12Uniformizer R π
  completedRing_isLocal : IsLocalRing A
  equationIso : A ≃+* chapter12NodeCompletedLocalRing R π
  regular : IsRegularLocalRing A

theorem chapter12_node_completed_local_ring_is_regular
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Chapter12Uniformizer R π) :
    IsRegularLocalRing (chapter12NodeCompletedLocalRing R π) := by
  sorry

structure Chapter12SemistableOpenModel
    {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter12ExcellentDedekindBase S K)
    (C : Chapter01SmoothProperCurveOverField K)
    (V : S.Opens) where
  open_nonempty : V ≠ ⊥
  carrier : Scheme.{u}
  structureMap : carrier ⟶ V.toScheme
  flat : Flat structureMap
  projective : Chapter07IsProjectiveMorphism structureMap
  proper : IsProper structureMap
  genericMap : Spec (CommRingCat.of K) ⟶ V.toScheme
  genericMap_over : genericMap ≫ V.ι = chapter12GenericPointMap B
  genericFiberIso : pullback structureMap genericMap ≅ C.carrier
  genericFiberIso_over :
    genericFiberIso.hom ≫ C.structureMap = pullback.snd structureMap genericMap
  semistable : Prop
  nodeIndex : Type u
  nodePoint : nodeIndex → carrier
  nodePresentation : ∀ _i : nodeIndex, Prop

structure Chapter12SemistableModelExtension
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K} {V : S.Opens}
    (N : Chapter12SemistableOpenModel B C V)
    (R : Chapter12RegularFlatProjectiveModel B C) where
  openIso : N.carrier ≅ (R.structureMap ⁻¹ᵁ V).toScheme
  over_base : openIso.hom ≫
      (chapter12ModelRestriction (B := B) (C := C)
        (chapter12RegularModelToFlat R) V) = N.structureMap
  centers_outside_V : Prop

structure Chapter12SemistableResolutionOutsideOpen
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K} {V : S.Opens}
    (N : Chapter12SemistableOpenModel B C V) where
  model : Chapter12RegularFlatProjectiveModel B C
  extension : Chapter12SemistableModelExtension N model
  semistable_locus_unchanged : Prop

def Chapter12MarkedSection {X S : Scheme.{u}} (f : X ⟶ S) : Type u :=
  Chapter10Section f

structure Chapter12MarkedSemistableModel
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K} {V : S.Opens}
    (M : Chapter12SemistableOpenModel B C V) where
  markIndex : Type u
  finiteMarks : Finite markIndex
  marks : ∀ _i : markIndex, Chapter12MarkedSection M.structureMap

structure Chapter12NodeSeparationData
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K} {V : S.Opens}
    {N : Chapter12SemistableOpenModel B C V}
    (M : Chapter12MarkedSemistableModel N) where
  blownUpModel : Scheme.{u}
  map : blownUpModel ⟶ N.carrier
  projective : Chapter07IsProjectiveMorphism map
  proper : IsProper map
  pointBlowupChain : Prop
  marks_avoid_nodes : Prop

structure Chapter12StableComponent
    {X : Scheme.{u}} where
  component : Set X
  rational : Prop
  meetsRemainderAndMarks : ℕ

def Chapter12StableComponentCondition
    {X : Scheme.{u}} (E : Chapter12StableComponent (X := X)) : Prop :=
  E.rational ∧ E.meetsRemainderAndMarks < 3

structure Chapter12StableContractionData
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) where
  contraction : X ⟶ Y
  over_base : (contraction ≫ g) = f
  proper : IsProper contraction
  contracted : ∀ E : Chapter12StableComponent (X := X),
    Chapter12StableComponentCondition E → Prop

structure Chapter12CompletedLocalModelInput (S : Scheme.{u}) where
  localIndex : Type u
  completedLocalData : localIndex → Prop

structure Chapter12CompatibleAlgebraicDescentData
    {S : Scheme.{u}} (D : Chapter12CompletedLocalModelInput S) where
  descentDatum : Prop
  cocycle : Prop

structure Chapter12ApproximationAlgebraizationData
    {S : Scheme.{u}} (D : Chapter12CompletedLocalModelInput S) where
  approximation : Prop
  algebraization : Prop

def Chapter12AlgebraizationInput
    {S : Scheme.{u}} (D : Chapter12CompletedLocalModelInput S) : Prop :=
  Nonempty (Chapter12CompatibleAlgebraicDescentData D) ∨
    Nonempty (Chapter12ApproximationAlgebraizationData D)

structure Chapter12AlgebraizedSemistableInput
    {S : Scheme.{u}} (D : Chapter12CompletedLocalModelInput S) where
  algebraization : Chapter12AlgebraizationInput D
  suppliedOpenModel : Prop
  commonDomination : Prop

/-! ### Polarized/fine-level and quotient interfaces -/

structure Chapter12PolarizedProjectiveModel
    {X S : Scheme.{u}} (f : X ⟶ S) where
  lineBundle : Chapter04LineBundle X
  ample : chapter04Ample f lineBundle
  projective : Chapter07IsProjectiveMorphism f

structure Chapter12FineLevelDescentData
    {S T : Scheme.{u}} (p : T ⟶ S) where
  cover : Chapter10FpqcCover p
  upstairsCarrier : Scheme.{u}
  upstairsMap : upstairsCarrier ⟶ T
  upstairsLineBundle : Chapter04LineBundle upstairsCarrier
  upstairsAmple : chapter04Ample upstairsMap upstairsLineBundle
  upstairsProjective : Chapter07IsProjectiveMorphism upstairsMap
  descentDatum : Prop
  cocycle : Prop
  polarization_compatible : Prop
  geometricNormality : Prop

structure Chapter12NormalizedQuotientSurface
    {X S : Scheme.{u}} (f : X ⟶ S) where
  quotient : Scheme.{u}
  quotientMap : X ⟶ quotient
  finite : IsFinite quotientMap
  normal : Chapter07NormalIntegralScheme quotient
  regular : Chapter04RegularScheme X
  fixedPointLocus : Set X
  quotientMayBeSingular : Prop

structure Chapter12FiniteGroupQuotientData
    {X S : Scheme.{u}} (f : X ⟶ S) where
  group : Type u
  [groupStructure : Group group]
  finiteGroup : Finite group
  regularSurface : Chapter04RegularScheme X
  action : Prop
  isolatedFixedPoints : Prop
  tame : Prop
  quotient : Scheme.{u}
  quotientMap : X ⟶ quotient
  finite : IsFinite quotientMap
  normal : Chapter07NormalIntegralScheme quotient
  quotientMayBeSingular : Prop

/-! ### Source-facing warnings with reusable propositions -/

def Chapter12PropernessWithoutProjectivity {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  IsProper f ∧ ¬ Chapter07IsProjectiveMorphism f

theorem chapter12_properness_does_not_choose_a_projective_embedding :
    ∃ (X S : Scheme.{u}) (f : X ⟶ S),
      Chapter12PropernessWithoutProjectivity f := by
  sorry

def Chapter12RegularBadFiber {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Chapter04RegularScheme X ∧ Flat f ∧
    ∃ s : S, ¬ Smooth (f.fiberToSpecResidueField s)

theorem chapter12_regularity_does_not_make_bad_fibers_smooth :
    ∃ (X S : Scheme.{u}) (f : X ⟶ S), Chapter12RegularBadFiber f := by
  sorry

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter12
