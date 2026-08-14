import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter10.Section03TheNormalizeAfterBaseChangeRule

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter10

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter08
open scoped AlgebraicGeometry BigOperators

universe u v

/-! ## 10.4 Ramification and vertical multiplicities -/

structure Chapter10DVRExtensionData (R R' : Type u)
    [CommRing R] [CommRing R'] [Algebra R R'] where
  baseDVR : IsDiscreteValuationRing R
  extensionDVR : IsDiscreteValuationRing R'
  ramificationIndex : ℕ
  positiveRamification : 0 < ramificationIndex
  baseUniformizer : R
  extensionUniformizer : R'
  unit : R'
  unit_isUnit : IsUnit unit
  uniformizer_relation :
    algebraMap R R' baseUniformizer = unit * extensionUniformizer ^ ramificationIndex

structure Chapter10VerticalDivisorialValuationData
    (F F' : Type u) [Field F] [Field F'] [Algebra F F'] where
  baseValue : F → ℤ
  extensionValue : F' → ℤ
  baseValue_zero : baseValue 0 = 0
  baseValue_one : baseValue 1 = 0
  baseValue_mul : ∀ {x y : F}, x ≠ 0 → y ≠ 0 →
    baseValue (x * y) = baseValue x + baseValue y
  baseValue_add : ∀ x y : F, baseValue (x + y) ≥ min (baseValue x) (baseValue y)
  baseValue_nontrivial : ∃ x : F, baseValue x ≠ 0
  extensionValue_zero : extensionValue 0 = 0
  extensionValue_one : extensionValue 1 = 0
  extensionValue_mul : ∀ {x y : F'}, x ≠ 0 → y ≠ 0 →
    extensionValue (x * y) = extensionValue x + extensionValue y
  extensionValue_add : ∀ x y : F',
    extensionValue (x + y) ≥ min (extensionValue x) (extensionValue y)
  extensionValue_nontrivial : ∃ x : F', extensionValue x ≠ 0
  baseExtensionRamificationIndex : ℕ
  positiveBaseExtensionRamification : 0 < baseExtensionRamificationIndex
  divisorialRamificationIndex : ℕ
  positiveDivisorialRamification : 0 < divisorialRamificationIndex
  baseUniformizer : F
  extensionUniformizer : F'
  unit : F'
  unit_isUnit : IsUnit unit
  baseMultiplicity : ℕ
  extensionUniformizer_positive : 0 < extensionValue extensionUniformizer
  ramificationScale : ∀ x : F,
    extensionValue (algebraMap F F' x) =
      (divisorialRamificationIndex : ℤ) * baseValue x
  baseUniformizer_has_multiplicity :
    baseValue baseUniformizer = (baseMultiplicity : ℤ)
  unit_has_zero_value : extensionValue unit = 0
  uniformizer_relation :
    algebraMap F F' baseUniformizer =
      unit * extensionUniformizer ^ baseExtensionRamificationIndex

def chapter10VerticalMultiplicity
    {F F' : Type u} [Field F] [Field F'] [Algebra F F']
    (D : Chapter10VerticalDivisorialValuationData F F') : ℤ :=
  D.extensionValue D.extensionUniformizer

def chapter10MultiplicityOfEInNormalizedSpecialFiber
    {F F' : Type u} [Field F] [Field F'] [Algebra F F']
    (D : Chapter10VerticalDivisorialValuationData F F') : ℤ :=
  chapter10VerticalMultiplicity D

theorem chapter10_vertical_valuation_scale
    {F F' : Type u} [Field F] [Field F'] [Algebra F F']
    (D : Chapter10VerticalDivisorialValuationData F F') (x : F) :
    D.extensionValue (algebraMap F F' x) =
      (D.divisorialRamificationIndex : ℤ) * D.baseValue x := by
  exact D.ramificationScale x

theorem chapter10_vertical_multiplicity_equation
    {F F' : Type u} [Field F] [Field F'] [Algebra F F']
    (D : Chapter10VerticalDivisorialValuationData F F') :
    (D.baseExtensionRamificationIndex : ℤ) * chapter10VerticalMultiplicity D =
      (D.divisorialRamificationIndex : ℤ) * (D.baseMultiplicity : ℤ) := by
  sorry

theorem chapter10_vertical_multiplicity_formula
    {F F' : Type u} [Field F] [Field F'] [Algebra F F']
    (D : Chapter10VerticalDivisorialValuationData F F') :
    (D.baseExtensionRamificationIndex : ℤ) * chapter10VerticalMultiplicity D =
      D.ramificationScale D.baseUniformizer := by
  sorry

def chapter10SemistableNodeRelation (R : Type u) [CommRing R] (π : R) :
    Ideal (MvPolynomial (Fin 2) R) :=
  chapter01NodalSurfaceRelation R π

abbrev chapter10SemistableNodeRing (R : Type u) [CommRing R] (π : R) :=
  chapter01NodalSurfaceRing R π

abbrev chapter10SemistableNodeScheme (R : Type u) [CommRing R] (π : R) :=
  chapter01NodalSurfaceScheme R π

abbrev chapter10SemistableSpecialFiberScheme (R : Type u) [CommRing R] (π : R) :=
  chapter01NodalSpecialFiberScheme R π

/- LOCAL_DEPENDENCY_GUESS: Mathlib has no single scheme-level normal-crossings predicate in the
 pinned snapshot.  The profile below records finite affine coverage, reducedness, and the local
 regular/node charts used by this chapter. -/
structure Chapter10NodeChart (A : Type u) [CommRing A] where
  base : Type u
  [baseCommRing : CommRing base]
  uniformizer : base
  coordinateIso : A ≃+* chapter10SemistableNodeRing base uniformizer

structure Chapter10NormalCrossingsProfile (X : Scheme.{u}) : Prop where
  charts : FiniteAffineOpenCover X
  specialFiberReduced : IsReduced X
  localChart : ∀ i,
    IsRegularRing Γ(X, charts.opens i) ∨
      Nonempty (Chapter10NodeChart (Γ(X, charts.opens i)))

abbrev Chapter10NormalCrossings (X : Scheme.{u}) : Prop :=
  Nonempty (Chapter10NormalCrossingsProfile X)

def chapter10SemistableNodeBaseChangeRelation
    (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R R']
    (π : R) (π' u : R') (e : ℕ) : Ideal (MvPolynomial (Fin 2) R') :=
  chapter10SemistableNodeRelation R' (u * π' ^ e)

theorem chapter10_semistable_equation_after_ramified_base_change
    (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R R']
    (π : R) (π' u : R') (e : ℕ)
    (hπ : algebraMap R R' π = u * π' ^ e) :
    chapter10SemistableNodeBaseChangeRelation R R' π π' u e =
      chapter10SemistableNodeRelation R' (algebraMap R R' π) := by
  rw [hπ]
  rfl

structure Chapter10RamifiedSemistableNodeResolutionProfile
    (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R R']
    (π : R) (π' u : R') (e : ℕ) where
  e_gt_one : 1 < e
  unit_isUnit : IsUnit u
  equation : algebraMap R R' π = u * π' ^ e
  originalRegular : Chapter01RegularScheme (chapter10SemistableNodeScheme R π)
  baseChanged : Scheme.{u}
  baseChanged_eq : baseChanged =
    chapter10SemistableNodeScheme R' (u * π' ^ e)
  baseChangedSingular : ¬ Chapter01RegularScheme baseChanged
  normalization : Scheme.{u}
  normalizationMap : normalization ⟶ baseChanged
  normalizationNotRegular : ¬ Chapter01RegularScheme normalization
  resolved : Scheme.{u}
  resolutionMap : resolved ⟶ normalization
  modification : Chapter07ProjectiveModification resolutionMap
  resolvedRegular : Chapter01RegularScheme resolved
  resolvedSpecialFiber : Scheme.{u}
  reducedSpecialFiberNormalCrossings : Chapter10NormalCrossings resolvedSpecialFiber

theorem chapter10_ramified_node_base_change_is_singular_at_the_crossing
    (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R R']
    [IsDomain R] [IsDomain R'] [IsDiscreteValuationRing R]
    (π : R) (π' u : R') (e : ℕ) (he : 1 < e)
    (hu : IsUnit u) (hπ : algebraMap R R' π = u * π' ^ e) :
    ¬ Chapter01RegularScheme
      (chapter10SemistableNodeScheme R' (u * π' ^ e)) := by
  sorry

structure Chapter10RamifiedNodeResolutionWitness where
  R R' : Type u
  [commRingR : CommRing R]
  [commRingR' : CommRing R']
  [algebraRR' : Algebra R R']
  π : R
  extensionUniformizer : R'
  unit : R'
  e : ℕ
  profile : Nonempty
    (Chapter10RamifiedSemistableNodeResolutionProfile
      R R' π extensionUniformizer unit e)

def Chapter10NormalizationAloneMayRemainSingular : Prop :=
  Nonempty Chapter10RamifiedNodeResolutionWitness

theorem chapter10_normalization_alone_need_not_resolve_the_ramified_node :
    Chapter10NormalizationAloneMayRemainSingular := by
  sorry

structure Chapter10RegularModelRamifiedBaseChangeWitness where
  R R' : Type u
  [commRingR : CommRing R]
  [commRingR' : CommRing R']
  [algebraRR' : Algebra R R']
  [domainR : IsDomain R]
  [domainR' : IsDomain R']
  [dvrR : IsDiscreteValuationRing R]
  π : R
  extensionUniformizer : R'
  unit : R'
  e : ℕ
  ramified : 1 < e
  unit_isUnit : IsUnit unit
  originalRegular : Chapter01RegularScheme (chapter10SemistableNodeScheme R π)
  baseChangedSingular :
    ¬ Chapter01RegularScheme
      (chapter10SemistableNodeScheme R' (unit * extensionUniformizer ^ e))

def Chapter10RegularModelRamifiedBaseChangeFailure : Prop :=
  Nonempty Chapter10RegularModelRamifiedBaseChangeWitness

theorem chapter10_regular_model_does_not_commute_with_ramified_base_change :
    Chapter10RegularModelRamifiedBaseChangeFailure := by
  sorry

theorem chapter10_etale_base_change_preserves_regular_total_space
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (hX : Chapter01RegularScheme X) (hp : Etale p) :
    Chapter01RegularScheme (chapter10BaseChange f p) := by
  sorry

structure Chapter10UnramifiedNodeComparison
    (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R R']
    (π : R) (π' u : R') where
  unit_isUnit : IsUnit u
  equation : algebraMap R R' π = u * π'
  nodeIso : chapter10SemistableNodeScheme R' (u * π') ≅
    chapter10SemistableNodeScheme R' π'

theorem chapter10_unramified_etale_base_change_remains_semistable
    (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R R']
    (π : R) (π' u : R')
    (hu : IsUnit u) (hπ : algebraMap R R' π = u * π') :
    Nonempty (Chapter10UnramifiedNodeComparison R R' π π' u) := by
  sorry

def Chapter10InertiaAndRamificationControlVerticalMultiplicity : Prop :=
  ∀ {F F' : Type u} [Field F] [Field F'] [Algebra F F']
    (D : Chapter10VerticalDivisorialValuationData F F'),
    (D.baseExtensionRamificationIndex : ℤ) * chapter10VerticalMultiplicity D =
      D.ramificationScale D.baseUniformizer

theorem chapter10_inertia_and_ramification_enter_the_vertical_geometry :
    Chapter10InertiaAndRamificationControlVerticalMultiplicity := by
  intro F F' _ _ _ D
  exact chapter10_vertical_multiplicity_formula D

end
end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter10
