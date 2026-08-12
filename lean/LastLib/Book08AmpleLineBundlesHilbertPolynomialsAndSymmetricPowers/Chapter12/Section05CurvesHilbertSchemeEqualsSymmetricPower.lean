import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter12.Section04FiniteLengthHilbertScheme

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter12

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped BigOperators

/-! ## 12.5. Curves: Hilbert scheme equals symmetric power -/

/-- A smooth quasi-projective relative curve. -/
structure Chapter12SmoothQuasiProjectiveCurve where
  base : Scheme
  curve : Scheme
  structureMap : curve ⟶ base
  smooth : Smooth structureMap
  relative_dimension_one : chapter12HasRelativeDimension structureMap 1
  quasi_projective : chapter12IsQuasiProjectiveMorphism structureMap

attribute [instance] Chapter12SmoothQuasiProjectiveCurve.smooth

/-- The base change of a relative curve to a test scheme. -/
def chapter12CurveBaseChange
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (T : Chapter12SchemeOver C.base) : Scheme :=
  pullback C.structureMap T.hom

def chapter12CurveBaseChangeToCurve
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (T : Chapter12SchemeOver C.base) :
    chapter12CurveBaseChange C T ⟶ C.curve :=
  pullback.fst C.structureMap T.hom

def chapter12CurveBaseChangeToTest
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (T : Chapter12SchemeOver C.base) :
    chapter12CurveBaseChange C T ⟶ T.left :=
  pullback.snd C.structureMap T.hom

@[simp]
theorem chapter12CurveBaseChange_condition
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (T : Chapter12SchemeOver C.base) :
    chapter12CurveBaseChangeToCurve C T ≫ C.structureMap =
      chapter12CurveBaseChangeToTest C T ≫ T.hom := by
  exact pullback.condition

def chapter12CurveFamilyProjection
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (T : Chapter12SchemeOver C.base)
    (I : (chapter12CurveBaseChange C T).IdealSheafData) :
    I.subscheme ⟶ T.left :=
  I.subschemeι ≫ chapter12CurveBaseChangeToTest C T

/- LOCAL_DEPENDENCY_GUESS: the pinned Mathlib checkout has no relative Cartier
  divisor predicate for smooth morphisms, so the effective-Cartier marker in
  the family interface is reserved for the earlier divisor chapters. -/
/-- A finite locally free length-`d` closed family on a relative curve. -/
structure Chapter12CurveHilbertFamily
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (L : Chapter12FiberLengthTheory)
    (T : Chapter12SchemeOver C.base) (d : ℕ) where
  ideal : (chapter12CurveBaseChange C T).IdealSheafData
  flat : Flat (chapter12CurveFamilyProjection C T ideal)
  finitePresentation : LocallyOfFinitePresentation (chapter12CurveFamilyProjection C T ideal)
  finiteLocallyFree :
    Chapter12FiniteLocallyFreeRank L (chapter12CurveFamilyProjection C T ideal) d

def chapter12IsEffectiveCartierFamily
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (L : Chapter12FiberLengthTheory)
    (T : Chapter12SchemeOver C.base) (d : ℕ)
    (F : Chapter12CurveHilbertFamily C L T d) : Prop := by
  sorry

/-- A relative effective Cartier divisor of degree `d`. -/
structure Chapter12RelativeEffectiveCartierDivisor
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (L : Chapter12FiberLengthTheory)
  (T : Chapter12SchemeOver C.base) (d : ℕ) where
  family : Chapter12CurveHilbertFamily C L T d
  effective_cartier : chapter12IsEffectiveCartierFamily C L T d family

abbrev chapter12RelativeEffectiveDivisor
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (L : Chapter12FiberLengthTheory)
    (T : Chapter12SchemeOver C.base) (d : ℕ) :=
  Chapter12RelativeEffectiveCartierDivisor C L T d

/-- On a smooth relative curve, length-`d` closed families and relative effective divisors agree. -/
noncomputable def chapter12_curve_hilbert_eq_effective_divisor
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (L : Chapter12FiberLengthTheory)
    (T : Chapter12SchemeOver C.base) (d : ℕ) :
    Chapter12CurveHilbertFamily C L T d ≃
      Chapter12RelativeEffectiveCartierDivisor C L T d := by
  sorry

theorem chapter12_curve_hilbert_family_is_effective_cartier
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (L : Chapter12FiberLengthTheory)
    (T : Chapter12SchemeOver C.base) (d : ℕ)
    (Z : Chapter12CurveHilbertFamily C L T d) :
    ∃ D : Chapter12RelativeEffectiveCartierDivisor C L T d, D.family = Z := by
  sorry

/-!
The symmetric power is exposed by the finite permutation quotient. The
quotient theorem itself is a dependency from the preceding symmetric-power
chapter; the universal divisor below records the stronger curve-specific
base-change and moduli property.
-/

/- LOCAL_DEPENDENCY_GUESS: use the canonical finite permutation quotient from
  Chapter 11 when it is merged, together with its smoothness and relative-
  dimension interfaces. -/
structure Chapter12SymmetricPowerData
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ) where
  carrier : Scheme
  structureMap : carrier ⟶ C.base
  orderedPower : Scheme
  orderedMap : orderedPower ⟶ C.base
  quotient : orderedPower ⟶ carrier
  quotient_over_base : quotient ≫ structureMap = orderedMap
  quotient_integral : IsIntegralHom quotient
  quotient_finite : IsFinite quotient
  quotient_surjective : Prop
  flat_base_change : Prop
  arbitrary_base_change_for_curve : Prop
  symmetric_group_action : Prop
  relative_dimension : chapter12HasRelativeDimension structureMap d
  smooth : Smooth structureMap
  zero_identification : d = 0 → Nonempty (carrier ≅ C.base)
  one_identification : d = 1 → Nonempty (carrier ≅ C.curve)

theorem chapter12_symmetric_power_exists
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ) :
    Nonempty (Chapter12SymmetricPowerData C d) := by
  sorry

noncomputable def chapter12SymmetricPowerData
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ) :
    Chapter12SymmetricPowerData C d :=
  Classical.choice (chapter12_symmetric_power_exists C d)

abbrev chapter12SymmetricPower
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ) : Scheme :=
  (chapter12SymmetricPowerData C d).carrier

abbrev chapter12SymmetricPowerMap
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ) :
    chapter12SymmetricPower C d ⟶ C.base :=
  (chapter12SymmetricPowerData C d).structureMap

theorem chapter12_symmetric_power_quotient_is_finite
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ) :
    IsFinite (chapter12SymmetricPowerData C d).quotient := by
  exact (chapter12SymmetricPowerData C d).quotient_finite

theorem chapter12_symmetric_power_zero
    (C : Chapter12SmoothQuasiProjectiveCurve) :
    Nonempty (chapter12SymmetricPower C 0 ≅ C.base) := by
  exact (chapter12SymmetricPowerData C 0).zero_identification rfl

theorem chapter12_symmetric_power_one
    (C : Chapter12SmoothQuasiProjectiveCurve) :
    Nonempty (chapter12SymmetricPower C 1 ≅ C.curve) := by
  exact (chapter12SymmetricPowerData C 1).one_identification rfl

/- The base-change isomorphism is kept as data so its two projections and its
  compatibility with the structure map remain available to later proofs. -/
def chapter12IsSymmetricPowerOfBaseChangedCurve
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ)
    (T : Chapter12SchemeOver C.base) (X : Scheme) : Prop := by
  sorry

structure Chapter12SymmetricPowerBaseChangeData
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ)
    (T : Chapter12SchemeOver C.base) where
  baseChangedSymmetricPower : Scheme
  baseChangedMap : baseChangedSymmetricPower ⟶ T.left
  is_symmetric_power_of_base_changed_curve :
    chapter12IsSymmetricPowerOfBaseChangedCurve C d T baseChangedSymmetricPower
  iso : pullback (chapter12SymmetricPowerMap C d) T.hom ≅ baseChangedSymmetricPower
  iso_over_test : iso.hom ≫ baseChangedMap = pullback.snd _ _

theorem chapter12_symmetric_power_base_change_exists
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ)
    (T : Chapter12SchemeOver C.base) :
    Nonempty (Chapter12SymmetricPowerBaseChangeData C d T) := by
  sorry

noncomputable def chapter12SymmetricPowerBaseChangeData
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ)
    (T : Chapter12SchemeOver C.base) :
    Chapter12SymmetricPowerBaseChangeData C d T :=
  Classical.choice (chapter12_symmetric_power_base_change_exists C d T)

theorem chapter12_symmetric_power_base_change
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ)
    (T : Chapter12SchemeOver C.base) :
    chapter12IsSymmetricPowerOfBaseChangedCurve C d T
      (chapter12SymmetricPowerBaseChangeData C d T).baseChangedSymmetricPower := by
  exact (chapter12SymmetricPowerBaseChangeData C d T).is_symmetric_power_of_base_changed_curve

/-- The ordered-root polynomial used on a smooth affine chart. -/
def chapter12UniversalRootPolynomial
    (A : Type*) [CommRing A] (d : ℕ) (t : Fin d → A) : Polynomial A :=
  ∏ i : Fin d, (Polynomial.X - Polynomial.C (t i))

theorem chapter12UniversalRootPolynomial_expands
    (A : Type*) [CommRing A] (d : ℕ) (t : Fin d → A) :
    chapter12UniversalRootPolynomial A d t =
      ∏ i : Fin d, (Polynomial.X - Polynomial.C (t i)) := by
  rfl

theorem chapter12UniversalRootPolynomial_eval
    (A : Type*) [CommRing A] (d : ℕ) (z : A) (t : Fin d → A) :
    (chapter12UniversalRootPolynomial A d t).eval z =
      ∏ i : Fin d, (z - t i) := by
  sorry

/- The ambient of the universal divisor is the canonical fiber product
  `C ×_S Sym^d(C)`, with both projections exposed for later pullback proofs. -/
def chapter12CurveSymmetricPowerAmbient
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ) : Scheme :=
  pullback C.structureMap (chapter12SymmetricPowerMap C d)

def chapter12CurveSymmetricPowerAmbientToCurve
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ) :
    chapter12CurveSymmetricPowerAmbient C d ⟶ C.curve :=
  pullback.fst C.structureMap (chapter12SymmetricPowerMap C d)

def chapter12CurveSymmetricPowerAmbientToSymmetricPower
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ) :
    chapter12CurveSymmetricPowerAmbient C d ⟶ chapter12SymmetricPower C d :=
  pullback.snd C.structureMap (chapter12SymmetricPowerMap C d)

@[simp]
theorem chapter12CurveSymmetricPowerAmbient_condition
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ) :
    chapter12CurveSymmetricPowerAmbientToCurve C d ≫ C.structureMap =
      chapter12CurveSymmetricPowerAmbientToSymmetricPower C d ≫
        chapter12SymmetricPowerMap C d := by
  exact pullback.condition

/-- The universal degree-`d` divisor on `C ×ₛ Sym^d(C)`. -/
structure Chapter12UniversalDivisor
    (C : Chapter12SmoothQuasiProjectiveCurve) (L : Chapter12FiberLengthTheory)
    (d : ℕ) where
  family : Chapter12CurveHilbertFamily C L
    (Over.mk (chapter12SymmetricPowerMap C d)) d
  effective_cartier : chapter12IsEffectiveCartierFamily C L
    (Over.mk (chapter12SymmetricPowerMap C d)) d family
  invariant_under_permutations : Prop
  local_monic_equation : Prop

theorem chapter12_universal_divisor_exists
    (C : Chapter12SmoothQuasiProjectiveCurve) (L : Chapter12FiberLengthTheory)
    (d : ℕ) :
    Nonempty (Chapter12UniversalDivisor C L d) := by
  sorry

noncomputable def chapter12UniversalDivisor
    (C : Chapter12SmoothQuasiProjectiveCurve) (L : Chapter12FiberLengthTheory)
    (d : ℕ) : Chapter12UniversalDivisor C L d :=
  Classical.choice (chapter12_universal_divisor_exists C L d)

theorem chapter12UniversalDivisor_is_finite_locally_free
    (C : Chapter12SmoothQuasiProjectiveCurve) (L : Chapter12FiberLengthTheory)
    (d : ℕ) :
    Chapter12FiniteLocallyFreeRank L
      (chapter12CurveFamilyProjection C
        (Over.mk (chapter12SymmetricPowerMap C d))
        (chapter12UniversalDivisor C L d).family.ideal) d := by
  exact (chapter12UniversalDivisor C L d).family.finiteLocallyFree

/-- The universal divisor represents relative effective Cartier divisors of degree `d`. -/
noncomputable def chapter12_universal_divisor_represents
    (C : Chapter12SmoothQuasiProjectiveCurve) (L : Chapter12FiberLengthTheory)
    (d : ℕ) (T : Chapter12SchemeOver C.base) :
    (T ⟶ Over.mk (chapter12SymmetricPowerMap C d)) ≃
      Chapter12RelativeEffectiveCartierDivisor C L T d := by
  sorry

/-- A curve Hilbert scheme representation, used only to state uniqueness of representers. -/
structure Chapter12CurveHilbertSchemeData
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (L : Chapter12FiberLengthTheory) (d : ℕ) where
  carrier : Scheme
  structureMap : carrier ⟶ C.base
  representingEquivalence : ∀ T : Chapter12SchemeOver C.base,
    (T ⟶ Over.mk structureMap) ≃ Chapter12CurveHilbertFamily C L T d
  universalFamily : Chapter12CurveHilbertFamily C L (Over.mk structureMap) d

theorem chapter12_curve_hilbert_scheme_exists
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (L : Chapter12FiberLengthTheory) (d : ℕ) :
    Nonempty (Chapter12CurveHilbertSchemeData C L d) := by
  sorry

noncomputable def chapter12CurveHilbertSchemeData
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (L : Chapter12FiberLengthTheory) (d : ℕ) :
    Chapter12CurveHilbertSchemeData C L d :=
  Classical.choice (chapter12_curve_hilbert_scheme_exists C L d)

theorem chapter12_curve_hilbert_scheme_eq_symmetric_power
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (L : Chapter12FiberLengthTheory) (d : ℕ) :
    Nonempty (Chapter12RepresentingOverIso
      (chapter12CurveHilbertSchemeData C L d).structureMap
      (chapter12SymmetricPowerMap C d)) := by
  sorry

/-- The two universal families agree under the representing isomorphism. -/
structure Chapter12CurveUniversalFamilyAgreement
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (L : Chapter12FiberLengthTheory) (d : ℕ) :
    Type where
  representingIso : Chapter12RepresentingOverIso
    (chapter12CurveHilbertSchemeData C L d).structureMap
    (chapter12SymmetricPowerMap C d)
  pullback_universal_families_agree : Prop
  universal_divisor_is_the_pulled_back_family : Prop

theorem chapter12_curve_universal_families_agree
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (L : Chapter12FiberLengthTheory) (d : ℕ) :
    Nonempty (Chapter12CurveUniversalFamilyAgreement C L d) := by
  sorry

/-- Addition of effective divisors gives the symmetric-power addition morphism. -/
theorem chapter12_symmetric_power_addition_exists
    (C : Chapter12SmoothQuasiProjectiveCurve) (d e : ℕ) :
    Nonempty (pullback (chapter12SymmetricPowerMap C d) (chapter12SymmetricPowerMap C e) ⟶
      chapter12SymmetricPower C (d + e)) := by
  sorry

noncomputable def chapter12SymmetricPowerAddition
    (C : Chapter12SmoothQuasiProjectiveCurve) (d e : ℕ) :
    pullback (chapter12SymmetricPowerMap C d) (chapter12SymmetricPowerMap C e) ⟶
      chapter12SymmetricPower C (d + e) :=
  Classical.choice (chapter12_symmetric_power_addition_exists C d e)

/-- The ideal-sheaf equation defining the sum of two effective divisors. -/
def chapter12DivisorSum
    {C : Chapter12SmoothQuasiProjectiveCurve}
    {L : Chapter12FiberLengthTheory}
    {T : Chapter12SchemeOver C.base}
    {d e : ℕ}
    (D : Chapter12RelativeEffectiveCartierDivisor C L T d)
    (E : Chapter12RelativeEffectiveCartierDivisor C L T e)
    (F : Chapter12RelativeEffectiveCartierDivisor C L T (d + e)) : Prop :=
  F.family.ideal = D.family.ideal * E.family.ideal

theorem chapter12_symmetric_power_addition_associative
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (L : Chapter12FiberLengthTheory)
    {T : Chapter12SchemeOver C.base}
    (d e f : ℕ)
    (D : Chapter12RelativeEffectiveCartierDivisor C L T d)
    (E : Chapter12RelativeEffectiveCartierDivisor C L T e)
    (F : Chapter12RelativeEffectiveCartierDivisor C L T f)
    (G : Chapter12RelativeEffectiveCartierDivisor C L T (d + e + f)) :
    (G.family.ideal = (D.family.ideal * E.family.ideal) * F.family.ideal) ↔
      (G.family.ideal = D.family.ideal * (E.family.ideal * F.family.ideal)) := by
  sorry

theorem chapter12_symmetric_power_addition_commutative
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (L : Chapter12FiberLengthTheory)
    {T : Chapter12SchemeOver C.base}
    (d e : ℕ)
    (D : Chapter12RelativeEffectiveCartierDivisor C L T d)
    (E : Chapter12RelativeEffectiveCartierDivisor C L T e) :
    D.family.ideal * E.family.ideal = E.family.ideal * D.family.ideal := by
  sorry

structure Chapter12SymmetricPowerAdditionBaseChangeData
    (C : Chapter12SmoothQuasiProjectiveCurve) (d e : ℕ)
    (T : Chapter12SchemeOver C.base) where
  degree_d : Chapter12SymmetricPowerBaseChangeData C d T
  degree_e : Chapter12SymmetricPowerBaseChangeData C e T
  degree_sum : Chapter12SymmetricPowerBaseChangeData C (d + e) T
  baseChangedAddition :
    pullback degree_d.baseChangedMap degree_e.baseChangedMap ⟶
      degree_sum.baseChangedSymmetricPower
  addition_compatibility : Prop

def chapter12_symmetric_power_addition_base_change_statement
    (C : Chapter12SmoothQuasiProjectiveCurve) (d e : ℕ)
    (T : Chapter12SchemeOver C.base) : Prop :=
  Nonempty (Chapter12SymmetricPowerAdditionBaseChangeData C d e T)

theorem chapter12_symmetric_power_addition_base_change
    (C : Chapter12SmoothQuasiProjectiveCurve) (d e : ℕ)
    (T : Chapter12SchemeOver C.base) :
    chapter12_symmetric_power_addition_base_change_statement C d e T := by
  sorry

/-- The graded commutative monoid of all symmetric powers. -/
structure Chapter12SymmetricPowerGradedMonoid
    (C : Chapter12SmoothQuasiProjectiveCurve) where
  component : ℕ → Scheme
  component_map : ∀ d, component d ⟶ C.base
  identifies_component : ∀ d, Nonempty (component d ≅ chapter12SymmetricPower C d)
  addition : ∀ d e,
    pullback (component_map d) (component_map e) ⟶ component (d + e)
  associative : Prop
  commutative : Prop
  unit_component : Prop
  not_finite_type_as_disjoint_union : Prop

theorem chapter12_symmetric_powers_form_graded_commutative_monoid
    (C : Chapter12SmoothQuasiProjectiveCurve) :
    Nonempty (Chapter12SymmetricPowerGradedMonoid C) := by
  sorry

/-!
The local monic-polynomial chart explains both collisions and smoothness: the
coefficients are coordinates, while repeated roots are retained as a
nonreduced divisor rather than discarded.
-/

structure Chapter12MonicPolynomialChart
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ) where
  chart : Scheme
  chartMap : chart ⟶ chapter12SymmetricPower C d
  coefficientRing : Type*
  coefficientRing_commRing : CommRing coefficientRing
  affineIdentification : Prop
  coefficients : Fin d → coefficientRing
  monic_equation : Prop
  roots_may_collide : Prop

attribute [instance] Chapter12MonicPolynomialChart.coefficientRing_commRing

theorem chapter12_symmetric_power_monic_coefficient_charts
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ) :
    Nonempty (Chapter12MonicPolynomialChart.{0} C d) := by
  sorry

theorem chapter12_symmetric_power_is_smooth
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ) :
    Smooth (chapter12SymmetricPowerMap C d) := by
  exact (chapter12SymmetricPowerData C d).smooth

theorem chapter12_symmetric_power_relative_dimension
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ) :
    chapter12HasRelativeDimension (chapter12SymmetricPowerMap C d) d := by
  exact (chapter12SymmetricPowerData C d).relative_dimension

/-- The proper Hilbert-to-cycle comparison for a projective singular curve. -/
structure Chapter12SingularCurveCycleComparison where
  base : Scheme
  curve : Scheme
  structureMap : curve ⟶ base
  projective_curve : chapter12IsProjectiveMorphism structureMap
  hilbertScheme : Scheme
  cycleSpace : Scheme
  hilbertToCycle : hilbertScheme ⟶ cycleSpace
  proper : IsProper hilbertToCycle
  isomorphism_away_from_singular_locus : Prop
  singular_fiber_contains_distinct_embedded_ideals : Prop
  same_cycle : Prop

theorem chapter12_singular_curve_hilbert_to_cycle_comparison :
    Nonempty Chapter12SingularCurveCycleComparison := by
  sorry

theorem chapter12_singular_curve_cycle_warning
    (C : Chapter12SingularCurveCycleComparison) :
    C.singular_fiber_contains_distinct_embedded_ideals ∧ C.same_cycle := by
  sorry

end
end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter12
