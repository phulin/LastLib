import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter10.Dependencies

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter10

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter02
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter03
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07
open scoped AlgebraicGeometry BigOperators

universe u v

/-! ## 10.1 Integral closure of the base -/

abbrev chapter10BaseNormalization {S : Scheme.{u}} {K K' : Type u}
    [Field K] [Field K'] [Algebra K K']
    (B : Chapter10ExcellentDedekindBase S K)
    [QuasiCompact (chapter10BaseExtensionMap (K' := K') B)]
    [QuasiSeparated (chapter10BaseExtensionMap (K' := K') B)] : Scheme.{u} :=
  (chapter10BaseExtensionMap (K' := K') B).normalization

abbrev chapter10BaseNormalizationMap {S : Scheme.{u}} {K K' : Type u}
    [Field K] [Field K'] [Algebra K K']
    (B : Chapter10ExcellentDedekindBase S K)
    [QuasiCompact (chapter10BaseExtensionMap (K' := K') B)]
    [QuasiSeparated (chapter10BaseExtensionMap (K' := K') B)] :
    chapter10BaseNormalization (K' := K') B ⟶ S :=
  (chapter10BaseExtensionMap (K' := K') B).fromNormalization

theorem chapter10_base_normalization_factorization
    {S : Scheme.{u}} {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    (B : Chapter10ExcellentDedekindBase S K)
    [QuasiCompact (chapter10BaseExtensionMap (K' := K') B)]
    [QuasiSeparated (chapter10BaseExtensionMap (K' := K') B)] :
    (chapter10BaseExtensionMap (K' := K') B).toNormalization ≫
        chapter10BaseNormalizationMap (K' := K') B =
      chapter10BaseExtensionMap (K' := K') B := by
  exact chapter02_normalization_factorization (chapter10BaseExtensionMap (K' := K') B)

theorem chapter10_base_normalization_is_integral_affine
    {S : Scheme.{u}} {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    (B : Chapter10ExcellentDedekindBase S K)
    [QuasiCompact (chapter10BaseExtensionMap (K' := K') B)]
    [QuasiSeparated (chapter10BaseExtensionMap (K' := K') B)] :
    IsIntegralHom (chapter10BaseNormalizationMap (K' := K') B) ∧
      IsAffineHom (chapter10BaseNormalizationMap (K' := K') B) := by
  exact chapter02_normalization_is_integral_affine (chapter10BaseExtensionMap (K' := K') B)

/- The excellence and Dedekind conclusion is the scheme-level finite-normalization theorem from
 Chapter 3, with the finite field extension and the generic-point identification made explicit at
 this boundary. -/
theorem chapter10_base_normalization_finite_and_excellentDedekind
    {S : Scheme.{u}} {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    (B : Chapter10ExcellentDedekindBase S K)
    (hKK' : Chapter10FiniteFieldExtension K K')
    [QuasiCompact (chapter10BaseExtensionMap (K' := K') B)]
    [QuasiSeparated (chapter10BaseExtensionMap (K' := K') B)] :
    IsFinite (chapter10BaseNormalizationMap (K' := K') B) ∧
      Chapter03ExcellentDedekindScheme (chapter10BaseNormalization (K' := K') B) := by
  sorry

theorem chapter10_base_normalization_is_proper
    {S : Scheme.{u}} {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    (B : Chapter10ExcellentDedekindBase S K)
    (hfinite : IsFinite (chapter10BaseNormalizationMap (K' := K') B))
    [QuasiCompact (chapter10BaseExtensionMap (K' := K') B)]
    [QuasiSeparated (chapter10BaseExtensionMap (K' := K') B)] :
    IsProper (chapter10BaseNormalizationMap (K' := K') B) := by
  sorry

/-! The finite reduced-algebra version is componentwise: the factors are indexed by minimal
 primes, and the total normalization is presented as a finite coproduct of normal components. -/

theorem chapter10_finite_reduced_algebra_normalization_is_finite_disjoint_union
    (K A : Type u) [Field K] [CommRing A] [Algebra K A]
    (hA : Chapter10FiniteReducedAlgebra K A) :
    letI : Chapter02ReducedFiniteMinimalPrimes A :=
      { reduced := hA.reduced, finite := hA.finiteMinimalPrimes }
    ∃ D : Chapter10FiniteReducedAlgebraNormalizationData A, IsFinite D.map := by
  sorry

theorem chapter10_finite_reduced_algebra_component_membership
    (K A : Type u) [Field K] [CommRing A] [Algebra K A]
    (hA : Chapter10FiniteReducedAlgebra K A) :
    letI : Chapter02ReducedFiniteMinimalPrimes A :=
      { reduced := hA.reduced, finite := hA.finiteMinimalPrimes }
    letI : Algebra A (Chapter02TotalRingOfFractions A) :=
      (chapter02TotalRingOfFractionsMap A).toAlgebra
    ∀ (x : Chapter02TotalRingOfFractions A),
      x ∈ integralClosure A (Chapter02TotalRingOfFractions A) ↔
        ∀ p : Chapter02MinimalPrime A,
          x p ∈ Chapter02ComponentIntegralClosure A p := by
  let : Chapter02ReducedFiniteMinimalPrimes A :=
    { reduced := hA.reduced, finite := hA.finiteMinimalPrimes }
  let : Algebra A (Chapter02TotalRingOfFractions A) :=
    (chapter02TotalRingOfFractionsMap A).toAlgebra
  exact chapter02_integralClosure_totalRing_components A

/- The local valuation statement is deliberately abstracted from a choice of uniformizer.  The
 stalk hypotheses expose the exact DVR conclusion used later by the ramification formula. -/
theorem chapter10_points_over_a_closed_point_correspond_to_valuation_extensions
    {S S' : Scheme.{u}} (ν : S' ⟶ S)
    {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    (hS : Chapter01DedekindScheme S) (hS' : Chapter01DedekindScheme S')
    (hν : IsFinite ν) (s : S) (hs : IsClosed ({s} : Set S)) :
    Nonempty (Chapter10DVRPointCorrespondence (K := K) (K' := K') ν s) := by
  sorry

/-! ### Base change of a model -/

theorem chapter10_model_baseChange_preserves_flatness
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S) (hf : Flat f) :
    Flat (chapter10BaseChangeToBase f p) := by
  sorry

theorem chapter10_model_baseChange_preserves_properness
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S) (hf : IsProper f) :
    IsProper (chapter10BaseChangeToBase f p) := by
  sorry

theorem chapter10_model_baseChange_preserves_projectivity
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (hf : Chapter07IsProjectiveMorphism f) :
    Chapter07IsProjectiveMorphism (chapter10BaseChangeToBase f p) := by
  sorry

theorem chapter10_baseChange_preserves_model_morphism_properties
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (hf : Chapter10ModelMorphismProperties f) :
    Chapter10ModelMorphismProperties (chapter10BaseChangeToBase f p) := by
  exact ⟨chapter10_model_baseChange_preserves_flatness f p hf.1,
    chapter10_model_baseChange_preserves_properness f p hf.2.1,
    chapter10_model_baseChange_preserves_projectivity f p hf.2.2⟩

def Chapter10IntegralBaseChangeFailure.{w} : Prop :=
  Chapter10BaseChangeFailure (IsIntegral : ObjectProperty Scheme.{w})

def Chapter10ReducedBaseChangeFailure.{w} : Prop :=
  Chapter10BaseChangeFailure (IsReduced : ObjectProperty Scheme.{w})

def Chapter10NormalBaseChangeFailure.{w} : Prop :=
  Chapter10BaseChangeFailure (Chapter10NormalScheme : ObjectProperty Scheme.{w})

def Chapter10RegularBaseChangeFailure.{w} : Prop :=
  Chapter10BaseChangeFailure (Chapter10RegularScheme : ObjectProperty Scheme.{w})

structure Chapter10BaseChangeFailureProfile.{w} : Prop where
  integral : Chapter10IntegralBaseChangeFailure.{w}
  reduced : Chapter10ReducedBaseChangeFailure.{w}
  normal : Chapter10NormalBaseChangeFailure.{w}
  regular : Chapter10RegularBaseChangeFailure.{w}

theorem chapter10_base_change_can_lose_integrality_reducedness_normality_regularity :
    Nonempty Chapter10BaseChangeFailureProfile.{u} := by
  sorry

theorem chapter10_generic_fiber_is_the_scalar_extension
    {C : Scheme.{u}} {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    (c : C ⟶ Spec (CommRingCat.of K)) :
    chapter10FieldBaseChange c (K := K') =
      pullback c (Spec.map (CommRingCat.ofHom (algebraMap K K'))) := by
  rfl

def Chapter10GenericFiberSplits {C : Scheme.{u}} {K : Type u} [Field K]
    (c : C ⟶ Spec (CommRingCat.of K)) : Prop :=
  ∃ (K' : Type u) (hK' : Field K'),
    letI : Field K' := hK'
    ∃ (hAlg : Algebra K K'),
      letI : Algebra K K' := hAlg
      ¬ IsIntegral (chapter10FieldBaseChange c (K := K'))

theorem chapter10_geometricallyIntegral_generic_fiber_stays_integral
    {C : Scheme.{u}} {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    (c : C ⟶ Spec (CommRingCat.of K))
    (hC : Chapter10GeometricallyIntegral c) :
    IsIntegral (chapter10FieldBaseChange c (K := K')) := by
  exact hC K'

theorem chapter10_non_geometrically_integral_generic_fiber_can_split
    {C : Scheme.{u}} {K : Type u} [Field K]
    (c : C ⟶ Spec (CommRingCat.of K))
    (hC : ¬ Chapter10GeometricallyIntegral c) :
    Chapter10GenericFiberSplits c := by
  sorry

end
end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter10
