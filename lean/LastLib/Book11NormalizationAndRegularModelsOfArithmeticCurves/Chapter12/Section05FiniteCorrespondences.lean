import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter12.Section01TheExactReusableModelTheorem

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter12

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter03
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07
open scoped AlgebraicGeometry

universe u v

/-! ## 12.5. Finite correspondences -/

structure Chapter12FiniteGenericMapModelExtension
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C D : Chapter01SmoothProperCurveOverField K}
    (X : Chapter12NormalFlatProjectiveModel B C)
    (Y : Chapter12NormalFlatProjectiveModel B D)
    (F : Chapter12FiniteGenericMap C D) where
  rationalMap : Chapter12RationalMapOver X.structureMap Y.structureMap
  generic_map_agreement : Prop

theorem chapter12_finite_generic_map_produces_a_rational_map
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C D : Chapter01SmoothProperCurveOverField K}
    {X : Chapter12NormalFlatProjectiveModel B C}
    {Y : Chapter12NormalFlatProjectiveModel B D}
    (F : Chapter12FiniteGenericMap C D) :
    Nonempty (Chapter12FiniteGenericMapModelExtension X Y F) := by
  sorry

theorem chapter12_graph_closure_is_proper_over_both_models
    {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {r : Chapter12RationalMapOver f g}
    (G : Chapter12GraphClosure r) :
    IsProper G.left ∧ IsProper G.right :=
  ⟨G.left_proper, G.right_proper⟩

theorem chapter12_normalize_and_resolve_graph
    {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {r : Chapter12RationalMapOver f g}
    (G : Chapter12GraphClosure r) :
    Nonempty (Chapter12ResolvedNormalizedGraph G) := by
  sorry

theorem chapter12_resolved_graph_has_honest_proper_projections
    {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {r : Chapter12RationalMapOver f g}
    {G : Chapter12GraphClosure r}
    (Z : Chapter12ResolvedNormalizedGraph G) :
    IsProper Z.left ∧ IsProper Z.right :=
  ⟨Z.left_proper, Z.right_proper⟩

structure Chapter12ResolvedProjectionFinitenessWarning
    {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {r : Chapter12RationalMapOver f g}
    (G : Chapter12GraphClosure r)
    (Z : Chapter12ResolvedNormalizedGraph G) where
  genericLeftFinite : Prop
  genericRightFinite : Prop
  verticalCurveContracted : Prop
  left_not_finite : ¬ IsFinite Z.left
  right_not_finite : ¬ IsFinite Z.right

theorem chapter12_resolved_graph_projections_need_not_be_finite :
    ∃ (X Y S : Scheme.{u}) (f : X ⟶ S) (g : Y ⟶ S)
      (r : Chapter12RationalMapOver f g) (G : Chapter12GraphClosure r)
      (Z : Chapter12ResolvedNormalizedGraph G),
      Nonempty (Chapter12ResolvedProjectionFinitenessWarning G Z) := by
  sorry

/-! ### What normalization can and cannot do -/

structure Chapter12NormalizationUniversalFactorization
    {Z X N : Scheme.{u}} (ν : Z ⟶ X) (n : N ⟶ X) where
  sourceNormal : Chapter03NormalScheme Z
  targetNormal : Chapter03NormalScheme N
  normalizationMorphism : IsIntegralHom n
  existingMorphism : Z ⟶ N
  factor : existingMorphism ≫ n = ν
  unique : ∀ h : Z ⟶ N, h ≫ n = ν → h = existingMorphism

theorem chapter12_normalization_universal_property_factors_existing_morphism
    {Z X N : Scheme.{u}} {ν : Z ⟶ X} {n : N ⟶ X}
    (F : Chapter12NormalizationUniversalFactorization ν n) :
    F.existingMorphism ≫ n = ν :=
  F.factor

structure Chapter12A2CoordinateRationalMap (k : Type u) [Field k] where
  source : Scheme.{u}
  target : chapter04ProjectiveLine k
  source_is_affine_plane :
    source = Spec (.of (MvPolynomial (Fin 2) k))
  source_normal : Chapter03NormalScheme source
  origin : source
  origin_is_coordinate_zero : Prop
  domain : source.Opens
  dense_domain : Dense (domain : Set source)
  map : domain.toScheme ⟶ target
  undefined_at_origin : origin ∉ (domain : Set source)
  coordinates_are_x_over_y : Prop

theorem chapter12_affine_plane_coordinate_map_is_undefined_at_origin
    (D : Chapter12A2CoordinateRationalMap k) :
    D.origin ∉ (D.domain : Set D.source) :=
  D.undefined_at_origin

theorem chapter12_normal_source_does_not_remove_codimension_two_indeterminacy
    (k : Type u) [Field k] :
    Nonempty (Chapter12A2CoordinateRationalMap k) := by
  sorry

structure Chapter12GraphConstructionNecessity
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) where
  rationalMap : Chapter12RationalMapOver f g
  graphClosure : Chapter12GraphClosure rationalMap
  graphIsEssential : Prop

theorem chapter12_graph_construction_is_essential_for_indeterminacy
    {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (D : Chapter12GraphConstructionNecessity f g) :
    D.graphIsEssential :=
  D.graphIsEssential

/-! ### Generic finiteness versus global finiteness -/

structure Chapter12VerticalContractionWarning
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) where
  correspondence : Chapter12ProperCorrespondence f g
  genericLeftFinite : Prop
  genericRightFinite : Prop
  verticalCurveContracted : Prop
  left_not_finite : ¬ IsFinite correspondence.left
  right_not_finite : ¬ IsFinite correspondence.right

theorem chapter12_generic_finiteness_does_not_force_global_finiteness :
    ∃ (X Y S : Scheme.{u}) (f : X ⟶ S) (g : Y ⟶ S),
      Nonempty (Chapter12VerticalContractionWarning f g) := by
  sorry

structure Chapter12SteinFactorization
    {Z X : Scheme.{u}} (f : Z ⟶ X) where
  directImageRing : Type u
  [commRing : CommRing directImageRing]
  intermediate : Spec (.of directImageRing)
  directImageStructureSpectrum : Prop
  connectedFiberMap : Z ⟶ intermediate
  finiteMap : intermediate ⟶ X
  factor : connectedFiberMap ≫ finiteMap = f
  connectedFibers : Prop
  finitePart : IsFinite finiteMap

theorem chapter12_stein_factor_separates_connected_contraction_from_finite_map
    {Z X : Scheme.{u}} {f : Z ⟶ X}
    (F : Chapter12SteinFactorization f) :
    IsFinite F.finiteMap ∧ F.connectedFibers :=
  ⟨F.finitePart, F.connectedFibers⟩

/-! ### Correspondence action and common domination -/

structure Chapter12CommonRegularCorrespondenceDomination
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) where
  graph : Chapter12ProperCorrespondence f g
  regularCarrier : Scheme.{u}
  regularMap : regularCarrier ⟶ graph.carrier
  locallyNoetherian : IsLocallyNoetherian regularCarrier
  regular : Chapter04RegularScheme regularCarrier
  proper : IsProper regularMap
  leftProjection : regularCarrier ⟶ X
  rightProjection : regularCarrier ⟶ Y
  left_factor : leftProjection = regularMap ≫ graph.left
  right_factor : rightProjection = regularMap ≫ graph.right

def Chapter12CorrespondenceActionData
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) : Prop :=
  Nonempty (Chapter12CommonRegularCorrespondenceDomination f g)

theorem chapter12_common_regular_domination_keeps_both_projections
    {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (D : Chapter12CommonRegularCorrespondenceDomination f g) :
    D.leftProjection = D.regularMap ≫ D.graph.left ∧
      D.rightProjection = D.regularMap ≫ D.graph.right :=
  ⟨D.left_factor, D.right_factor⟩

structure Chapter12MinimalModelFunctorialityWarning
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) where
  sourceMinimalModel : Scheme.{u}
  targetMinimalModel : Scheme.{u}
  sourceProjection : sourceMinimalModel ⟶ X
  targetProjection : targetMinimalModel ⟶ Y
  neitherProjectionRequiredToBeMorphismBetweenPreselectedModels : Prop
  commonDomination : Chapter12CommonRegularCorrespondenceDomination f g
  laterIntersectionAction : Chapter12CorrespondenceActionData f g

theorem chapter12_domination_is_robust_for_correspondence_actions
    {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (D : Chapter12MinimalModelFunctorialityWarning f g) :
    Chapter12CorrespondenceActionData f g :=
  D.laterIntersectionAction

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter12
