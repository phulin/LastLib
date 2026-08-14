import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter12.Section01TheExactReusableModelTheorem

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter12

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07
open scoped AlgebraicGeometry

universe u v

/-! ## 12.2. Modular curves -/

structure Chapter12ModularOpenProblem
    {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter12ExcellentDedekindBase S K)
    (U : S.Opens) where
  genericCurve : Chapter01SmoothProperCurveOverField K
  moduliSpace : Scheme.{u}
  structureMap : moduliSpace ⟶ U.toScheme
  good_deformation_theory : Prop
  open_moduli_not_proper : ¬ IsProper structureMap
  genericCurve_is_moduli_completion : Prop

def Chapter12ModularOpenProblemIsNotProper
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {U : S.Opens} (P : Chapter12ModularOpenProblem B U) : Prop :=
  ¬ IsProper P.structureMap

theorem chapter12_modular_open_problem_is_not_proper
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {U : S.Opens} (P : Chapter12ModularOpenProblem B U) :
    Chapter12ModularOpenProblemIsNotProper P :=
  P.open_moduli_not_proper

structure Chapter12HorizontalDivisor
    {X S : Scheme.{u}} (f : X ⟶ S) where
  support : Set X
  finiteOverBase : Prop
  horizontal : Prop
  effectiveCartier : Prop

structure Chapter12CuspidalGenericCurve
    {K : Type u} [Field K]
    (C : Chapter01SmoothProperCurveOverField K) where
  cuspSupport : Set C.carrier
  cuspFinite : cuspSupport.Finite
  cuspDivisor : Prop

structure Chapter12GeneralizedModularCompactification
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {U : S.Opens}
    (P : Chapter12ModularOpenProblem B U) where
  compactification : Scheme.{u}
  compactificationMap : compactification ⟶ U.toScheme
  proper : IsProper compactificationMap
  projective : Chapter07IsProjectiveMorphism compactificationMap
  moduliOpen : P.moduliSpace ⟶ compactification
  moduliOpen_over : moduliOpen ≫ compactificationMap = P.structureMap
  moduliOpen_isOpenImmersion : IsOpenImmersion moduliOpen
  generalizedDegenerations : Prop
  genericCurveWithCusps : Chapter12CuspidalGenericCurve P.genericCurve
  cusps : Chapter12HorizontalDivisor compactificationMap

theorem chapter12_generalized_modular_compactification_is_proper
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K} {U : S.Opens}
    {P : Chapter12ModularOpenProblem B U}
    (Komp : Chapter12GeneralizedModularCompactification P) :
    IsProper Komp.compactificationMap :=
  Komp.proper

theorem chapter12_modular_cusps_are_finite_horizontal
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K} {U : S.Opens}
    {P : Chapter12ModularOpenProblem B U}
    (Komp : Chapter12GeneralizedModularCompactification P) :
    Komp.cusps.finiteOverBase ∧ Komp.cusps.horizontal :=
by
  sorry

/- The five construction stages are named separately so later applications can use the closure,
normalization, resolution, and cusp-separation facts independently. -/

structure Chapter12ModularProjectiveClosureStep
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K} {U : S.Opens}
    (M : Chapter12SmoothProjectiveOpenModel B C U) where
  closure : Chapter12FlatProjectiveModel B C
  extension : Chapter12ModelExtension M closure
  projectiveClosure : Prop

structure Chapter12ModularNormalizationStep
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K} {U : S.Opens}
    (M : Chapter12SmoothProjectiveOpenModel B C U)
    (P : Chapter12ModularProjectiveClosureStep M) where
  normalModel : Chapter12NormalFlatProjectiveModel B C
  extension : Chapter12ModelExtension M (chapter12NormalModelToFlat normalModel)
  normalizationMap : normalModel.carrier ⟶ P.closure.carrier
  normalization_over :
    normalizationMap ≫ P.closure.structureMap = normalModel.structureMap
  finite : IsFinite normalizationMap
  integral : IsIntegralHom normalizationMap
  retains_good_open : extension.openIso.hom ≫ chapter12ModelRestriction
      (chapter12NormalModelToFlat normalModel) U = M.structureMap
  repairs_branch_identifications_at_bad_primes : Prop

structure Chapter12ModularResolutionStep
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K} {U : S.Opens}
    (M : Chapter12SmoothProjectiveOpenModel B C U)
    (P : Chapter12ModularProjectiveClosureStep M)
    (N : Chapter12ModularNormalizationStep M P) where
  regularModel : Chapter12RegularFlatProjectiveModel B C
  extension : Chapter12ModelExtension M (chapter12RegularModelToFlat regularModel)
  map : regularModel.carrier ⟶ N.normalModel.carrier
  over_base : map ≫ N.normalModel.structureMap = regularModel.structureMap
  projective : Chapter07IsProjectiveMorphism map
  birational : Chapter07Birational map
  resolution_centers_above_bad_primes : Prop

structure Chapter12ModularCuspBlowupStep
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K} {U : S.Opens}
    (M : Chapter12SmoothProjectiveOpenModel B C U)
    (P : Chapter12ModularProjectiveClosureStep M)
    (N : Chapter12ModularNormalizationStep M P)
    (R : Chapter12ModularResolutionStep M P N) where
  model : Chapter12RegularFlatProjectiveModel B C
  extension : Chapter12ModelExtension M (chapter12RegularModelToFlat model)
  map : model.carrier ⟶ R.regularModel.carrier
  over_base : map ≫ R.regularModel.structureMap = model.structureMap
  projective : Chapter07IsProjectiveMorphism map
  proper : IsProper map
  cuspIndex : Type u
  finiteCusps : Finite cuspIndex
  cuspClosure : cuspIndex → Chapter12HorizontalDivisor model.structureMap
  disjoint : Prop
  regularHorizontal : Prop
  meetsFibersTransversely : Prop

structure Chapter12ModularArithmeticSurface
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    (C : Chapter01SmoothProperCurveOverField K)
    {U : S.Opens} (M : Chapter12SmoothProjectiveOpenModel B C U) where
  model : Chapter12RegularFlatProjectiveModel B C
  extension : Chapter12ModelExtension M (chapter12RegularModelToFlat model)
  arithmeticSurface : Chapter01ArithmeticSurface model.structureMap
  cuspIndex : Type u
  finiteCusps : Finite cuspIndex
  cuspClosure : cuspIndex → Chapter12HorizontalDivisor model.structureMap
  cuspClosures_disjoint : Prop
  cuspClosures_regular_horizontal : Prop
  cuspClosures_transverse : Prop

theorem chapter12_modular_surface_is_regular_proper_projective
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K} {U : S.Opens}
    {M : Chapter12SmoothProjectiveOpenModel B C U}
    (X : Chapter12ModularArithmeticSurface C M) :
    Chapter04RegularScheme X.model.carrier ∧
      IsProper X.model.structureMap ∧
      Chapter07IsProjectiveMorphism X.model.structureMap := by
  exact ⟨X.model.regular, X.model.proper, X.model.projective⟩

theorem chapter12_modular_surface_preserves_generic_curve_and_good_open
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K} {U : S.Opens}
    {M : Chapter12SmoothProjectiveOpenModel B C U}
    (X : Chapter12ModularArithmeticSurface C M) :
    X.extension.openIso.hom ≫ chapter12ModelRestriction
        (chapter12RegularModelToFlat X.model) U = M.structureMap :=
  X.extension.over_base

theorem chapter12_modular_arithmetic_surface_exists
    {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter12ExcellentDedekindBase S K)
    (C : Chapter01SmoothProperCurveOverField K)
    {U : S.Opens} (hU : U ≠ ⊥)
    (M : Chapter12SmoothProjectiveOpenModel B C U) :
    Nonempty (Chapter12ModularArithmeticSurface C M) := by
  obtain ⟨P⟩ := chapter12_arithmeticCurve_model_package B C U hU M
  exact ⟨{
    model := P.regularModel
    extension := P.regularExtension
    arithmeticSurface := by sorry
    cuspIndex := PUnit
    finiteCusps := inferInstance
    cuspClosure := fun _ => by sorry
    cuspClosures_disjoint := by sorry
    cuspClosures_regular_horizontal := by sorry
    cuspClosures_transverse := by sorry }⟩

/-! ### Fine level, descent, and coarse quotients -/

structure Chapter12NormalizedFineLevelModel
    {S T : Scheme.{u}} (p : T ⟶ S)
    (D : Chapter12FineLevelDescentData p) where
  normalizedCarrier : Scheme.{u}
  normalization : normalizedCarrier ⟶ D.upstairsCarrier
  finite : IsFinite normalization
  normal : Chapter07NormalIntegralScheme normalizedCarrier
  descentDatum_retained : Prop

theorem chapter12_fine_level_normalization_retains_descent_datum
    {S T : Scheme.{u}} {p : T ⟶ S}
    (D : Chapter12FineLevelDescentData p)
    (hgeometricNormality : D.geometricNormality) :
    Nonempty (Chapter12NormalizedFineLevelModel p D) := by
  sorry

structure Chapter12DescendedPolarizedModel
    {S T : Scheme.{u}} (p : T ⟶ S)
    (D : Chapter12FineLevelDescentData p) where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ S
  lineBundle : Chapter04LineBundle carrier
  ample : chapter04Ample structureMap lineBundle
  projective : Chapter07IsProjectiveMorphism structureMap
  descentRealization : Prop

theorem chapter12_fine_level_projective_model_descends
    {S T : Scheme.{u}} {p : T ⟶ S}
    (D : Chapter12FineLevelDescentData p) :
    Nonempty (Chapter12DescendedPolarizedModel p D) := by
  sorry

structure Chapter12ResolvedCoarseQuotient
    {X S : Scheme.{u}} (f : X ⟶ S)
    (Q : Chapter12FiniteGroupQuotientData f) where
  quotientNormal : Chapter07NormalIntegralScheme Q.quotient
  quotientMayBeSingular : Prop
  regularModel : Scheme.{u}
  resolution : regularModel ⟶ Q.quotient
  locallyNoetherian : IsLocallyNoetherian regularModel
  regular : Chapter04RegularScheme regularModel
  projective : Chapter07IsProjectiveMorphism resolution
  proper : IsProper resolution
  normalizedBlowupProcedure : Prop

theorem chapter12_tame_coarse_quotient_is_finite_and_normal
    {X S : Scheme.{u}} {f : X ⟶ S}
    (Q : Chapter12FiniteGroupQuotientData f)
    (_htame : Q.tame) :
    IsFinite Q.quotientMap ∧ Chapter07NormalIntegralScheme Q.quotient :=
  ⟨Q.finite, Q.normal⟩

theorem chapter12_tame_coarse_quotient_can_be_resolved
    {X S : Scheme.{u}} {f : X ⟶ S}
    (Q : Chapter12FiniteGroupQuotientData f)
    (htame : Q.tame) :
    Nonempty (Chapter12ResolvedCoarseQuotient f Q) := by
  sorry

theorem chapter12_tame_coarse_quotient_may_be_normal_singular
    {X S : Scheme.{u}} {f : X ⟶ S}
    (Q : Chapter12FiniteGroupQuotientData f)
    (htame : Q.tame)
    (hfixed : Q.isolatedFixedPoints) :
    ∃ Y : Scheme.{u},
      Chapter07NormalIntegralScheme Y ∧ ¬ Chapter04RegularScheme Y := by
  sorry

theorem chapter12_regular_upstairs_does_not_remove_quotient_singularities
    {X S : Scheme.{u}} {f : X ⟶ S}
    (Q : Chapter12FiniteGroupQuotientData f)
    (htame : Q.tame)
    (hfixed : Q.isolatedFixedPoints) :
    ∃ Y : Scheme.{u},
      Chapter04RegularScheme X ∧ Chapter07NormalIntegralScheme Y ∧
        ¬ Chapter04RegularScheme Y := by
  sorry

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter12
