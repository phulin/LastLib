import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter06.Section02SmoothCurvesTurnPointsIntoDivisors

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter06

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11
open RelativeScheme
open scoped BigOperators

universe u

/-! ## 6.3. Universal divisors and addition -/

abbrev Chapter06SymmetricPower {S : Scheme.{u}}
    (C : RelativeScheme S) (d : ℕ)
    [Chapter06SmoothProjectiveRelativeCurve C] :=
  symmetricPower C d

abbrev Chapter06SymmetricPowerMap {S : Scheme.{u}}
    (C : RelativeScheme S) (d : ℕ)
    [Chapter06SmoothProjectiveRelativeCurve C] :
    (Chapter06SymmetricPower C d).carrier ⟶ S :=
  (symmetricPower C d).structuralMap

abbrev Chapter06SymmetricPowerQuotientMap {S : Scheme.{u}}
    (C : RelativeScheme S) (d : ℕ)
    [Chapter06SmoothProjectiveRelativeCurve C] :
    (relativePower C d).carrier ⟶ Chapter06SymmetricPower C d :=
  symmetricPowerMap C d

abbrev Chapter06UniversalDivisorAmbient {S : Scheme.{u}}
    (C : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver C] : Scheme.{u} :=
  curveSymmetricAmbient C d

abbrev Chapter06UniversalDivisor {S : Scheme.{u}}
    (C : RelativeScheme S) (d : ℕ)
    [Chapter06SmoothProjectiveRelativeCurve C] :
    EffectiveCartierDivisor (Chapter06UniversalDivisorAmbient C d) :=
  universalDivisor C d

theorem chapter06_universal_divisor_is_finite_flat_of_rank
    {S : Scheme.{u}} (C : RelativeScheme S) (d : ℕ)
    [Chapter06SmoothProjectiveRelativeCurve C] :
    Chapter06FiniteFlatRank
      ((Chapter06UniversalDivisor C d).inclusion ≫
        pullback.snd C.structuralMap (Chapter06SymmetricPowerMap C d)) d :=
  universalDivisor_finiteLocallyFree C d

abbrev Chapter06UniversalDivisorOnTest {S : Scheme.{u}}
    (C T : RelativeScheme S) (d : ℕ)
    [Chapter06SmoothProjectiveRelativeCurve C] :=
  Chapter06RelativeEffectiveDivisor C T d

noncomputable def chapter06UniversalDivisorEquiv
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [Chapter06SmoothProjectiveRelativeCurve C] :
    (T ⟶ Chapter06SymmetricPower C d) ≃
      Chapter06UniversalDivisorOnTest C T d :=
  universalDivisorEquiv C T d

theorem chapter06_universal_divisor_pullback_is_universal
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [Chapter06SmoothProjectiveRelativeCurve C]
    (f : T ⟶ Chapter06SymmetricPower C d) :
    Chapter11UniversalDivisorPullbackRelation C T d f
      (chapter06UniversalDivisorEquiv C T d f) :=
  pullbackUniversalDivisor_is_universal C T d f

theorem chapter06_universal_divisor_is_natural_under_base_change
    {S : Scheme.{u}} (C T U : RelativeScheme S) (d : ℕ)
    [Chapter06SmoothProjectiveRelativeCurve C] (u : U ⟶ T)
    (f : T ⟶ Chapter06SymmetricPower C d) :
    divisorRestriction d u (chapter06UniversalDivisorEquiv C T d f) =
      chapter06UniversalDivisorEquiv C U d (u ≫ f) :=
  universalDivisorEquiv_natural C T U d u f

theorem chapter06_universal_divisor_pointwise_bijective
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [Chapter06SmoothProjectiveRelativeCurve C] :
    Function.Bijective (fun f : T ⟶ Chapter06SymmetricPower C d =>
      chapter06UniversalDivisorEquiv C T d f) :=
  (chapter06UniversalDivisorEquiv C T d).bijective

noncomputable def chapter06SymmetricPowerClassifiesLengthFamilies
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [Chapter06SmoothProjectiveRelativeCurve C] :
    (T ⟶ Chapter06SymmetricPower C d) ≃
      Chapter06FiniteFlatClosedFamily C T d := by
  let e := chapter06UniversalDivisorEquiv C T d
  let h := chapter06_length_d_family_divisor_equiv C T d
  refine
    { toFun := fun f =>
        { ideal := (e f).divisor.ideal
          finite_flat_rank := (e f).finite_flat_rank }
      invFun := fun Z => e.symm (h Z)
      left_inv := by
        intro f
        apply e.injective
        rw [e.apply_symm_apply]
        apply chapter06_relative_effective_divisor_ext
        exact chapter06FiniteFlatFamilyToRelativeDivisor_ideal C T d
          { ideal := (e f).divisor.ideal
            finite_flat_rank := (e f).finite_flat_rank }
      right_inv := by
        intro Z
        apply chapter06FiniteFlatClosedFamily_ext
        change (e (e.symm (h Z))).divisor.ideal = Z.ideal
        rw [e.apply_symm_apply]
        exact chapter06FiniteFlatFamilyToRelativeDivisor_ideal C T d Z }

theorem chapter06_symmetric_power_classifies_length_d_families
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [Chapter06SmoothProjectiveRelativeCurve C] :
    Nonempty ((T ⟶ Chapter06SymmetricPower C d) ≃
      Chapter06FiniteFlatClosedFamily C T d) :=
  ⟨chapter06SymmetricPowerClassifiesLengthFamilies C T d⟩

theorem chapter06_symmetric_power_classifies_length_families_natural
    {S : Scheme.{u}} (C T U : RelativeScheme S) (d : ℕ)
    [Chapter06SmoothProjectiveRelativeCurve C] (u : U ⟶ T)
    (f : T ⟶ Chapter06SymmetricPower C d) :
    chapter06FiniteFlatClosedFamilyBaseChange C T U u d
        (chapter06SymmetricPowerClassifiesLengthFamilies C T d f) =
      chapter06SymmetricPowerClassifiesLengthFamilies C U d (u ≫ f) := by
  sorry

noncomputable def chapter06RelativeDivisorSum
    {S : Scheme.{u}} {C T : RelativeScheme S} {d e : ℕ}
    (D : Chapter06RelativeEffectiveDivisor C T d)
    (E : Chapter06RelativeEffectiveDivisor C T e) :
    Chapter06RelativeEffectiveDivisor C T (d + e) :=
  { divisor := D.divisor.add E.divisor
    finite_flat_rank := relativeEffectiveCartierDivisor_add_rank d e D E }

theorem chapter06_relative_divisor_sum_ideal
    {S : Scheme.{u}} {C T : RelativeScheme S} {d e : ℕ}
    (D : Chapter06RelativeEffectiveDivisor C T d)
    (E : Chapter06RelativeEffectiveDivisor C T e) :
    (chapter06RelativeDivisorSum D E).divisor.ideal =
      D.divisor.ideal * E.divisor.ideal :=
  rfl

theorem chapter06_relative_divisor_sum_is_effective_cartier
    {S : Scheme.{u}} {C T : RelativeScheme S} {d e : ℕ}
    (D : Chapter06RelativeEffectiveDivisor C T d)
    (E : Chapter06RelativeEffectiveDivisor C T e) :
    (chapter06RelativeDivisorSum D E).divisor.ideal.IsEffectiveCartier := by
  exact (chapter06RelativeDivisorSum D E).divisor.isEffectiveCartier

noncomputable def chapter06SymmetricPowerAddition
    {S : Scheme.{u}} (C : RelativeScheme S) (d e : ℕ)
    [Chapter06SmoothProjectiveRelativeCurve C] :
    (relativeProduct (Chapter06SymmetricPower C d)
      (Chapter06SymmetricPower C e)).carrier ⟶ Chapter06SymmetricPower C (d + e) :=
  symmetricPowerAddition C d e

theorem chapter06_symmetric_power_addition_is_divisor_sum
    {S : Scheme.{u}} (C : RelativeScheme S) (d e : ℕ)
    [Chapter06SmoothProjectiveRelativeCurve C] :
    ∃ D : Chapter06RelativeEffectiveDivisor C
        (relativeProduct (Chapter06SymmetricPower C d)
          (Chapter06SymmetricPower C e)).carrier (d + e),
      D.divisor =
          (chapter06UniversalDivisorEquiv C
            (relativeProduct (Chapter06SymmetricPower C d)
              (Chapter06SymmetricPower C e)).carrier d
            (relativeProduct (Chapter06SymmetricPower C d)
              (Chapter06SymmetricPower C e)).fst).divisor.add
            (chapter06UniversalDivisorEquiv C
            (relativeProduct (Chapter06SymmetricPower C d)
              (Chapter06SymmetricPower C e)).carrier e
              (relativeProduct (Chapter06SymmetricPower C d)
                (Chapter06SymmetricPower C e)).snd).divisor ∧
      chapter06SymmetricPowerAddition C d e =
        divisorToSymmetricPoint C
          (relativeProduct (Chapter06SymmetricPower C d)
            (Chapter06SymmetricPower C e)).carrier (d + e) D ∧
      Chapter06FiniteFlatRank
        (D.divisor.inclusion ≫
          pullback.snd C.structuralMap
            (relativeProduct (Chapter06SymmetricPower C d)
              (Chapter06SymmetricPower C e)).carrier.structuralMap) (d + e) := by
  rcases symmetricPowerAddition_from_divisor_sum C d e with ⟨D, hD, hRank⟩
  refine ⟨D, hD, ?_, hRank⟩
  unfold chapter06SymmetricPowerAddition symmetricPowerAddition
  let P := relativeProduct (symmetricPower C d) (symmetricPower C e)
  let Dd := pullbackUniversalDivisor C P.carrier d P.fst
  let De := pullbackUniversalDivisor C P.carrier e P.snd
  let D₀ : RelativeEffectiveCartierDivisor C P.carrier (d + e) :=
    { divisor := Dd.divisor.add De.divisor
      finite_flat_rank := relativeEffectiveCartierDivisor_add_rank d e Dd De }
  change divisorToSymmetricPoint C P.carrier (d + e) D₀ =
    divisorToSymmetricPoint C P.carrier (d + e) D
  unfold divisorToSymmetricPoint
  have hD₀ : D₀.divisor = D.divisor := by
    simpa [D₀, Dd, De, P] using hD.symm
  have hD₀' : D₀ = D := by
    dsimp [D₀]
    cases D
    congr
  exact congrArg ((universalDivisorRepresentingData C (d + e)).equivalence P.carrier).symm
    hD₀'

theorem chapter06_symmetric_power_addition_is_over_base
    {S : Scheme.{u}} (C : RelativeScheme S) (d e : ℕ)
    [Chapter06SmoothProjectiveRelativeCurve C] :
    (chapter06SymmetricPowerAddition C d e).hom ≫
        Chapter06SymmetricPowerMap C (d + e) =
      (relativeProduct (Chapter06SymmetricPower C d)
        (Chapter06SymmetricPower C e)).carrier.structuralMap := by
  exact (chapter06SymmetricPowerAddition C d e).comm

def chapter06GeometricPointCollision {α : Type u}
    (p : Multiset α) (q : Multiset α) : Prop :=
  ∃ a, a ∈ p ∧ a ∈ q

def chapter06GeometricPointSum {α : Type u}
    (p : Multiset α) (q : Multiset α) : Multiset α := p + q

theorem chapter06_geometric_point_sum_is_concatenation
    {α : Type u} (p q : Multiset α) :
    chapter06GeometricPointSum p q = p + q :=
  rfl

theorem chapter06_geometric_point_sum_retains_multiplicity
    {α : Type u} [DecidableEq α] (p q : Multiset α) (a : α) :
    (chapter06GeometricPointSum p q).count a = p.count a + q.count a := by
  simp [chapter06GeometricPointSum]

theorem chapter06_collision_gives_multiplicity_two
    {α : Type u} [DecidableEq α] {p q : Multiset α}
    (h : chapter06GeometricPointCollision p q) :
    ∃ a, 2 ≤ (chapter06GeometricPointSum p q).count a := by
  rcases h with ⟨a, hpa, hqa⟩
  refine ⟨a, ?_⟩
  rw [chapter06_geometric_point_sum_retains_multiplicity]
  have hp : 0 < p.count a := Multiset.count_pos.mpr hpa
  have hq : 0 < q.count a := Multiset.count_pos.mpr hqa
  omega

def chapter06RepeatedSectionLocalEquation {R : Type u} [CommRing R]
    (t : R) (d : ℕ) : R :=
  t ^ d

abbrev chapter06RepeatedSectionLocalRing {R : Type u} [CommRing R]
    (t : R) (d : ℕ) :=
  R ⧸ Ideal.span ({chapter06RepeatedSectionLocalEquation t d} : Set R)

theorem chapter06_repeated_section_local_equation
    {R : Type u} [CommRing R] (t : R) (d : ℕ) :
    chapter06RepeatedSectionLocalEquation t d = t ^ d :=
  rfl

theorem chapter06_repeated_section_structure_sheaf
    {R : Type u} [CommRing R] (t : R) (d : ℕ) :
    chapter06RepeatedSectionLocalRing t d =
      (R ⧸ Ideal.span ({t ^ d} : Set R)) :=
  rfl

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter06
