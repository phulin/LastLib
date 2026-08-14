import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter12.Section02ModularCurves

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter12

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07
open scoped AlgebraicGeometry

universe u v

/-! ## 12.3. Shimura curves -/

structure Chapter12ShimuraGoodOpenModel
    {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter12ExcellentDedekindBase S K)
    (C : Chapter01SmoothProperCurveOverField K)
    (U : S.Opens) extends Chapter12SmoothProjectiveOpenModel B C U where
  compact : Prop
  noCusps : Prop

structure Chapter12CompactShimuraCurve
    {K : Type u} [Field K]
    (C : Chapter01SmoothProperCurveOverField K) where
  cuspSupport : Set C.carrier
  cuspSupport_empty : cuspSupport = ∅
  compactification : Prop

theorem chapter12_compact_shimura_curve_has_no_boundary_divisor
    {K : Type u} [Field K] {C : Chapter01SmoothProperCurveOverField K}
    (D : Chapter12CompactShimuraCurve C) :
    D.cuspSupport = ∅ :=
  D.cuspSupport_empty

structure Chapter12ShimuraBadFiberProfile
    {S : Scheme.{u}} (f : Scheme.{u} ⟶ S) where
  discriminantPrimes : Set S
  levelPrimes : Set S
  badFiberLocus : Set S
  discriminant_in_bad : discriminantPrimes ⊆ badFiberLocus
  level_in_bad : levelPrimes ⊆ badFiberLocus

structure Chapter12ShimuraArithmeticSurface
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    (C : Chapter01SmoothProperCurveOverField K)
    {U : S.Opens} (M : Chapter12ShimuraGoodOpenModel B C U) where
  model : Chapter12RegularFlatProjectiveModel B C
  extension : Chapter12ModelExtension M.toChapter12SmoothProjectiveOpenModel
    (chapter12RegularModelToFlat model)
  arithmeticSurface : Chapter01ArithmeticSurface model.structureMap
  badFibers : Set S
  bad_fiber_profile : Prop

theorem chapter12_shimura_good_open_is_smooth_and_proper
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K} {U : S.Opens}
    (M : Chapter12ShimuraGoodOpenModel B C U) :
    Smooth M.structureMap ∧ IsProper M.structureMap :=
  ⟨M.smooth, M.proper⟩

theorem chapter12_shimura_arithmetic_surface_exists
    {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter12ExcellentDedekindBase S K)
    (C : Chapter01SmoothProperCurveOverField K)
    {U : S.Opens} (hU : U ≠ ⊥)
    (M : Chapter12SmoothProjectiveOpenModel B C U) :
    Nonempty (Chapter12ShimuraArithmeticSurface
      (C := C)
      { toChapter12SmoothProjectiveOpenModel := M
        compact := by sorry
        noCusps := by sorry }) := by
  sorry

/-! ### Fine versus coarse Shimura constructions -/

structure Chapter12ShimuraFineModuliInput
    {S T : Scheme.{u}} (p : T ⟶ S) where
  cover : Chapter10FpqcCover p
  polarizedModel : Chapter12FineLevelDescentData p
  fineModuli : Prop

structure Chapter12ShimuraCoarseQuotientInput
    {X S : Scheme.{u}} (f : X ⟶ S) where
  fineSurface : Chapter04RegularScheme X
  quotient : Chapter12FiniteGroupQuotientData f
  tameQuotient : Prop

theorem chapter12_shimura_fine_cover_can_be_descended
    {S T : Scheme.{u}} {p : T ⟶ S}
    (D : Chapter12ShimuraFineModuliInput p) :
    Nonempty (Chapter12DescendedPolarizedModel p D.polarizedModel) := by
  exact chapter12_fine_level_projective_model_descends D.polarizedModel

theorem chapter12_shimura_coarse_quotient_need_not_be_regular
    {X S : Scheme.{u}} {f : X ⟶ S}
    (D : Chapter12ShimuraCoarseQuotientInput f)
    (hfixed : D.quotient.isolatedFixedPoints) :
    ∃ Y : Scheme.{u},
      Chapter07NormalIntegralScheme Y ∧ ¬ Chapter04RegularScheme Y := by
  exact chapter12_tame_coarse_quotient_may_be_normal_singular
    D.quotient D.tameQuotient hfixed

theorem chapter12_shimura_coarse_quotient_can_be_resolved
    {X S : Scheme.{u}} {f : X ⟶ S}
    (D : Chapter12ShimuraCoarseQuotientInput f) :
    Nonempty (Chapter12ResolvedCoarseQuotient f D.quotient) := by
  exact chapter12_tame_coarse_quotient_can_be_resolved
    D.quotient D.tameQuotient

/-! ### Reflex-field and quaternionic/PEL descent -/

structure Chapter12ReflexFieldShimuraInput
    {S : Scheme.{u}} {K L : Type u} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L]
    (B : Chapter12ExcellentDedekindBase S K) where
  extension : Chapter12FiniteSeparableExtension K L
  normalizedBase : Chapter12NormalizedDedekindBase B
  quaternionicOrPEL : Prop
  polarization : Prop

structure Chapter12ShimuraDescentModel
    {S : Scheme.{u}} {K L : Type u} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L]
    {B : Chapter12ExcellentDedekindBase S K}
    (E : Chapter12ReflexFieldShimuraInput B) where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ S
  projective : Chapter07IsProjectiveMorphism structureMap
  proper : IsProper structureMap
  descentDatum : Prop
  polarization_descended : Prop
  normalizedDedekindBase_used : Prop

theorem chapter12_quaternionic_PEL_model_uses_normalized_reflex_base
    {S : Scheme.{u}} {K L : Type u} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L]
    {B : Chapter12ExcellentDedekindBase S K}
    (E : Chapter12ReflexFieldShimuraInput B) :
    E.normalizedBase.dedekind := by
  exact E.normalizedBase.dedekind

theorem chapter12_polarized_reflex_field_model_descends
    {S : Scheme.{u}} {K L : Type u} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L]
    {B : Chapter12ExcellentDedekindBase S K}
    (E : Chapter12ReflexFieldShimuraInput B) :
    Nonempty (Chapter12ShimuraDescentModel E) := by
  sorry

structure Chapter12RamifiedShimuraResolution
    {X S : Scheme.{u}} (f : X ⟶ S) where
  descendedModel : Scheme.{u}
  descentMap : descendedModel ⟶ X
  ramificationIntroducesSingularities : Prop
  normalizedModel : Scheme.{u}
  normalization : normalizedModel ⟶ descendedModel
  finite : IsFinite normalization
  normal : Chapter07NormalIntegralScheme normalizedModel
  resolvedModel : Scheme.{u}
  resolution : resolvedModel ⟶ normalizedModel
  regular : Chapter04RegularScheme resolvedModel
  projective : Chapter07IsProjectiveMorphism resolution
  proper : IsProper resolution
  commonEquivariantDomination : Prop

theorem chapter12_ramified_shimura_model_can_be_normalized_and_resolved
    {X S : Scheme.{u}} {f : X ⟶ S}
    (D : Chapter12RamifiedShimuraResolution f) :
    Chapter07NormalIntegralScheme D.normalizedModel ∧
      Chapter04RegularScheme D.resolvedModel :=
  ⟨D.normal, D.regular⟩

structure Chapter12CurveLevelShimuraOutput
    {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter12ExcellentDedekindBase S K)
    (C : Chapter01SmoothProperCurveOverField K) where
  regularProperCurveModel : Chapter12RegularFlatProjectiveModel B C
  regular : Chapter04RegularScheme regularProperCurveModel.carrier
  proper : IsProper regularProperCurveModel.structureMap
  projective : Chapter07IsProjectiveMorphism regularProperCurveModel.structureMap
  notRequiredSmoothModuliAtBadPrimes : Prop

theorem chapter12_shimura_output_is_curve_level_not_everywhere_smooth_moduli
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K}
    (O : Chapter12CurveLevelShimuraOutput B C) :
    Chapter04RegularScheme O.regularProperCurveModel.carrier ∧
      IsProper O.regularProperCurveModel.structureMap ∧
      Chapter07IsProjectiveMorphism O.regularProperCurveModel.structureMap :=
  ⟨O.regular, O.proper, O.projective⟩

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter12
