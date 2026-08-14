import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter10.Section02BaseChangeCanDestroyNormality

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter10

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter02
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter03
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter08
open scoped AlgebraicGeometry BigOperators

universe u v

/-! ## 10.3 The normalize-after-base-change rule -/

noncomputable def chapter10NormalizedReducedBaseChange
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (R : Chapter10ReductionData (chapter10BaseChange f p))
    (hqc : QuasiCompact (chapter10IntegralComponentGenericPointMap R.integralComponent))
    (hqs : QuasiSeparated (chapter10IntegralComponentGenericPointMap R.integralComponent)) :
    Scheme.{u} := by
  letI := hqc
  letI := hqs
  exact Chapter02AbsoluteNormalization R.integralComponent.carrier

noncomputable def chapter10NormalizedReducedBaseChangeToReduced
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (R : Chapter10ReductionData (chapter10BaseChange f p))
    (hqc : QuasiCompact (chapter10IntegralComponentGenericPointMap R.integralComponent))
    (hqs : QuasiSeparated (chapter10IntegralComponentGenericPointMap R.integralComponent)) :
    chapter10NormalizedReducedBaseChange f p R hqc hqs ⟶
      R.integralComponent.carrier := by
  letI := hqc
  letI := hqs
  exact chapter02AbsoluteNormalizationMap R.integralComponent.carrier

noncomputable def chapter10NormalizedReducedBaseChangeMap
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (R : Chapter10ReductionData (chapter10BaseChange f p))
    (hqc : QuasiCompact (chapter10IntegralComponentGenericPointMap R.integralComponent))
    (hqs : QuasiSeparated (chapter10IntegralComponentGenericPointMap R.integralComponent)) :
    chapter10NormalizedReducedBaseChange f p R hqc hqs ⟶ chapter10BaseChange f p :=
  chapter10NormalizedReducedBaseChangeToReduced f p R hqc hqs ≫
    R.integralComponent.inclusion ≫ R.projection

theorem chapter10_normalized_reduced_baseChange_map_is_integral
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (R : Chapter10ReductionData (chapter10BaseChange f p))
    (hqc : QuasiCompact (chapter10IntegralComponentGenericPointMap R.integralComponent))
    (hqs : QuasiSeparated (chapter10IntegralComponentGenericPointMap R.integralComponent)) :
    IsIntegralHom (chapter10NormalizedReducedBaseChangeMap f p R hqc hqs) := by
  sorry

theorem chapter10_normalized_reduced_baseChange_is_finite_over_excellent_base
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (R : Chapter10ReductionData (chapter10BaseChange f p))
    (hqc : QuasiCompact (chapter10IntegralComponentGenericPointMap R.integralComponent))
    (hqs : QuasiSeparated (chapter10IntegralComponentGenericPointMap R.integralComponent))
    (hT : Chapter03ExcellentDedekindScheme T)
    (hf : Chapter03ReducedFiniteTypeMorphism
      (R.integralComponent.inclusion ≫ R.projection ≫ chapter10BaseChangeToBase f p))
    (hν : Chapter03NormalizationMap
      (chapter10NormalizedReducedBaseChangeToReduced f p R hqc hqs)) :
    IsFinite (chapter10NormalizedReducedBaseChangeToReduced f p R hqc hqs) := by
  sorry

theorem chapter10_normalized_reduced_baseChange_map_is_finite
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (R : Chapter10ReductionData (chapter10BaseChange f p))
    (hqc : QuasiCompact (chapter10IntegralComponentGenericPointMap R.integralComponent))
    (hqs : QuasiSeparated (chapter10IntegralComponentGenericPointMap R.integralComponent))
    (hν : IsFinite (chapter10NormalizedReducedBaseChangeToReduced f p R hqc hqs))
    (hR : IsFinite (R.integralComponent.inclusion ≫ R.projection)) :
    IsFinite (chapter10NormalizedReducedBaseChangeMap f p R hqc hqs) := by
  sorry

theorem chapter10_normalized_reduced_baseChange_is_proper
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (R : Chapter10ReductionData (chapter10BaseChange f p))
    (hqc : QuasiCompact (chapter10IntegralComponentGenericPointMap R.integralComponent))
    (hqs : QuasiSeparated (chapter10IntegralComponentGenericPointMap R.integralComponent))
    (hfinite : IsFinite (chapter10NormalizedReducedBaseChangeToReduced f p R hqc hqs))
    (hR : IsProper (R.integralComponent.inclusion ≫ R.projection)) :
    IsProper (chapter10NormalizedReducedBaseChangeMap f p R hqc hqs) := by
  sorry

theorem chapter10_normalized_reduced_baseChange_is_projective
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (R : Chapter10ReductionData (chapter10BaseChange f p))
    (hqc : QuasiCompact (chapter10IntegralComponentGenericPointMap R.integralComponent))
    (hqs : QuasiSeparated (chapter10IntegralComponentGenericPointMap R.integralComponent))
    (hfinite : IsFinite (chapter10NormalizedReducedBaseChangeToReduced f p R hqc hqs))
    (hR : Chapter07IsProjectiveMorphism (R.integralComponent.inclusion ≫ R.projection)) :
    Chapter07IsProjectiveMorphism (chapter10NormalizedReducedBaseChangeMap f p R hqc hqs) := by
  sorry

theorem chapter10_normalized_reduced_baseChange_is_proper_over_base
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (R : Chapter10ReductionData (chapter10BaseChange f p))
    (hqc : QuasiCompact (chapter10IntegralComponentGenericPointMap R.integralComponent))
    (hqs : QuasiSeparated (chapter10IntegralComponentGenericPointMap R.integralComponent))
    (hfinite : IsFinite (chapter10NormalizedReducedBaseChangeToReduced f p R hqc hqs))
    (hR : IsProper (R.integralComponent.inclusion ≫ R.projection))
    (hbase : IsProper (chapter10BaseChangeToBase f p)) :
    IsProper (chapter10NormalizedReducedBaseChangeMap f p R hqc hqs ≫
      chapter10BaseChangeToBase f p) := by
  sorry

theorem chapter10_normalized_reduced_baseChange_is_projective_over_base
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (R : Chapter10ReductionData (chapter10BaseChange f p))
    (hqc : QuasiCompact (chapter10IntegralComponentGenericPointMap R.integralComponent))
    (hqs : QuasiSeparated (chapter10IntegralComponentGenericPointMap R.integralComponent))
    (hfinite : IsFinite (chapter10NormalizedReducedBaseChangeToReduced f p R hqc hqs))
    (hR : Chapter07IsProjectiveMorphism (R.integralComponent.inclusion ≫ R.projection))
    (hbase : Chapter07IsProjectiveMorphism (chapter10BaseChangeToBase f p)) :
    Chapter07IsProjectiveMorphism
      (chapter10NormalizedReducedBaseChangeMap f p R hqc hqs ≫
        chapter10BaseChangeToBase f p) := by
  sorry

def Chapter10ResolutionRequired (Y : Scheme.{u}) : Prop :=
  ¬ Chapter01RegularScheme Y

theorem chapter10_projective_resolution_data_provides_a_regular_model
    {Y : Scheme.{u}} {U : Y.Opens} (D : Chapter08ProjectiveResolutionData Y U) :
    Chapter01RegularScheme D.carrier ∧ Chapter07IsProjectiveMorphism D.map := by
  exact ⟨D.regular, D.projective⟩

/- The chosen generic component is represented by an explicit generic-fiber isomorphism.  This
 keeps component selection separate from the finite normalization map itself. -/
structure Chapter10ChosenGenericComponent {X S : Scheme.{u}}
    (f : X ⟶ S) (η : S) (C : Scheme.{u}) where
  carrier : Scheme.{u}
  inclusion : carrier ⟶ X
  genericFiberIso : (inclusion ≫ f).fiber η ≅ C

/-! ### The canonical comparison -/

noncomputable abbrev chapter10NormalizationAfterBaseChangeComparison
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] :
    (pullback.snd f p).normalization ⟶ pullback f.fromNormalization p :=
  chapter02NormalizationPullbackComparison f p

theorem chapter10_normalization_after_baseChange_comparison_over_base
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] :
    chapter10NormalizationAfterBaseChangeComparison f p ≫
        pullback.snd f.fromNormalization p =
      (pullback.snd f p).fromNormalization := by
  exact f.normalizationPullback_snd p

theorem chapter10_normalization_after_baseChange_comparison_isIso_of_smooth
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] (hp : Smooth p) :
    IsIso (chapter10NormalizationAfterBaseChangeComparison f p) := by
  let _ : Smooth p := hp
  exact chapter02_normalization_pullback_isIso f p

theorem chapter10_normalization_after_baseChange_need_not_be_an_isomorphism :
    Chapter03NormalizationNeedNotCommuteWithBaseChange := by
  exact chapter03_normalization_need_not_commute_with_base_change

theorem chapter10_geometrically_normal_base_change_is_normal
    {X : Scheme.{u}} {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    (f : X ⟶ Spec (CommRingCat.of K))
    (hX : Chapter10GeometricallyNormal f) :
    Chapter10NormalScheme (chapter10FieldBaseChange f (K := K')) := by
  exact hX K'

theorem chapter10_smooth_curve_is_geometrically_normal
    {X : Scheme.{u}} {K : Type u} [Field K]
    (f : X ⟶ Spec (CommRingCat.of K))
    (hfinite : Chapter01FiniteType f)
    (hsmooth : Smooth f)
    (hcurve : Chapter01PureDimensionOne X) :
    Chapter10GeometricallyNormal f := by
  sorry

theorem chapter10_separable_geometrically_normal_base_change_comparison_isIso
    {X : Scheme.{u}} {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    [FiniteDimensional K K']
    (f : X ⟶ Spec (CommRingCat.of K))
    [QuasiCompact f] [QuasiSeparated f]
    (hX : Chapter10GeometricallyNormal f)
    (hsep : Algebra.IsSeparable K K') :
    IsIso (chapter02NormalizationPullbackComparison f
      (Spec.map (CommRingCat.ofHom (algebraMap K K')))) := by
  sorry

def Chapter10SpecialFiberNormalizationObstruction {X S T : Scheme.{u}}
    (f : X ⟶ S) (p : T ⟶ S) : Prop :=
  ∃ R : Chapter10ReductionData (chapter10BaseChange f p),
    ¬ Chapter10NormalScheme R.carrier

end
end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter10
