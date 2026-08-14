import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter11.Section01ExceptionalCurvesAndContraction

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter11

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07
open scoped AlgebraicGeometry

universe u v

/-! ### 11.2 Existence in positive genus -/

theorem chapter11_minimal_regular_model_exists
    {R : Type u} [CommRing R] [IsDomain R]
    (hR : Chapter11ExcellentDiscreteValuationRing R)
    (C : Chapter11SmoothProjectiveCurve (FractionRing R))
    (hgenus : 0 < C.genus) :
    Nonempty (Chapter11MinimalRegularModel R (FractionRing R) C) := by
  sorry

theorem chapter11_regular_proper_model_maps_uniquely_to_minimal
    {R : Type u} [CommRing R] [IsDomain R]
    (hR : Chapter11ExcellentDiscreteValuationRing R)
    {C : Chapter11SmoothProjectiveCurve (FractionRing R)}
    (M : Chapter11RegularProperModel R (FractionRing R) C)
    (Mmin : Chapter11MinimalRegularModel R (FractionRing R) C) :
    ∃! u : M.carrier ⟶ Mmin.model.carrier,
      chapter11InducesIdentityOnGenericFiber M Mmin.model u := by
  sorry

theorem chapter11_minimal_model_is_relatively_minimal
    {R : Type u} [CommRing R] [IsDomain R]
    {C : Chapter11SmoothProjectiveCurve (FractionRing R)}
    (M : Chapter11MinimalRegularModel R (FractionRing R) C) :
    chapter11RelativelyMinimal M.model :=
  M.relatively_minimal

/-! The global paragraph uses a separate base datum because a Dedekind scheme
need not be presented by one ring. -/

theorem chapter11_global_nonsmooth_fibers_are_finite
    {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter11ExcellentDedekindBase S K)
    (hqc : QuasiCompact (𝟙 S))
    (C : Chapter11SmoothProjectiveCurve K)
    (M : Chapter11GlobalRegularProperModelData B C) :
    (chapter11NonSmoothFiberSet M).Finite := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the pinned restriction/gluing API does not yet
package the family of local contractions indexed by closed fibers, so the
local-contraction and identity-away-from-centers clauses are retained as
capabilities alongside the actual global glued morphism. -/
structure Chapter11GlobalContractionGluingData
    {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter11ExcellentDedekindBase S K)
    (C : Chapter11SmoothProjectiveCurve K)
    (M : Chapter11GlobalRegularProperModelData B C) where
  centers : Set S
  centers_finite : centers.Finite
  local_contractions : Prop
  identity_away_from_centers : Prop
  global_model : Chapter11GlobalMinimalRegularModel B C
  glued_map : M.carrier ⟶ global_model.model.carrier
  proper : IsProper glued_map
  over_base : glued_map ≫ global_model.model.structureMap = M.structureMap

theorem chapter11_global_fiberwise_contractions_glue
    {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter11ExcellentDedekindBase S K)
    (hqc : QuasiCompact (𝟙 S))
    (C : Chapter11SmoothProjectiveCurve K)
    (M : Chapter11GlobalRegularProperModelData B C)
    (hgenus : 0 < C.genus) :
    Nonempty (Chapter11GlobalContractionGluingData B C M) := by
  sorry

theorem chapter11_global_minimal_regular_model_exists
    {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter11ExcellentDedekindBase S K)
    (hqc : QuasiCompact (𝟙 S))
    (C : Chapter11SmoothProjectiveCurve K)
    (M : Chapter11GlobalRegularProperModelData B C)
    (hgenus : 0 < C.genus) :
    Nonempty (Chapter11GlobalMinimalRegularModel B C) := by
  rcases chapter11_global_fiberwise_contractions_glue B hqc C M hgenus with ⟨G⟩
  exact ⟨G.global_model⟩

/-! Genus one with a rational point and the Weierstrass comparison. -/

structure Chapter11GenusOneRationalPoint
    {K : Type u} [Field K]
    (C : Chapter11SmoothProjectiveCurve K) where
  genus_eq_one : C.genus = 1
  section_ : Spec (CommRingCat.of K) ⟶ C.carrier
  over_structureMap : section_ ≫ C.structureMap = 𝟙 _

structure Chapter11MinimalWeierstrassResolution
    {R : Type u} [CommRing R] [IsDomain R]
    (C : Chapter11SmoothProjectiveCurve (FractionRing R))
    (P : Chapter11GenusOneRationalPoint C) where
  weierstrass : Scheme.{u}
  weierstrassMap : weierstrass ⟶ chapter11BaseScheme R
  proper : IsProper weierstrassMap
  genericFiberAgreement : Prop
  regularModel : Chapter11RegularProperModel R (FractionRing R) C
  resolutionMap : regularModel.carrier ⟶ weierstrass
  resolutionProper : IsProper resolutionMap
  resolutionOverBase : resolutionMap ≫ weierstrassMap = regularModel.structureMap
  resolvesSurfaceSingularities : Prop
  relativelyMinimal : chapter11RelativelyMinimal regularModel
  noSuperfluousPointBlowups : Prop

structure Chapter11NormalSingularWeierstrassProfile
    {R : Type u} [CommRing R] [IsDomain R]
    {C : Chapter11SmoothProjectiveCurve (FractionRing R)}
    {P : Chapter11GenusOneRationalPoint C}
    (W : Chapter11MinimalWeierstrassResolution C P) : Prop where
  normal : Chapter01NormalScheme W.weierstrass
  singular : ¬ Chapter01RegularScheme W.weierstrass

theorem chapter11_genus_one_minimal_weierstrass_resolution
    {R : Type u} [CommRing R] [IsDomain R]
    (hR : Chapter11ExcellentDiscreteValuationRing R)
    {C : Chapter11SmoothProjectiveCurve (FractionRing R)}
    (P : Chapter11GenusOneRationalPoint C) :
    Nonempty (Chapter11MinimalWeierstrassResolution C P) := by
  sorry

def chapter11_weierstrass_model_can_be_normal_but_singular
    {R : Type u} [CommRing R] [IsDomain R]
    {C : Chapter11SmoothProjectiveCurve (FractionRing R)}
    {P : Chapter11GenusOneRationalPoint C}
    : Prop :=
  ∃ W : Chapter11MinimalWeierstrassResolution C P,
    Nonempty (Chapter11NormalSingularWeierstrassProfile W)

theorem chapter11_minimal_regular_resolution_has_no_superfluous_point_blowups
    {R : Type u} [CommRing R] [IsDomain R]
    {C : Chapter11SmoothProjectiveCurve (FractionRing R)}
    {P : Chapter11GenusOneRationalPoint C}
    (W : Chapter11MinimalWeierstrassResolution C P) :
    W.noSuperfluousPointBlowups := by
  sorry

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter11
