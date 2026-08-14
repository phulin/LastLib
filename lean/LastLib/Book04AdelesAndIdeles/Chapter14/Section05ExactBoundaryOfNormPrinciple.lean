import LastLib.Book04AdelesAndIdeles.Chapter10.Dependencies
import LastLib.Book04AdelesAndIdeles.Chapter14.Dependencies

/-!
# 14.5. The exact boundary of the norm principle
-/

noncomputable section

namespace LastLib.Book04AdelesAndIdeles.Chapter14

theorem chapter14_local_norm_numerator_is_the_everywhere_local_subgroup
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (N : Chapter14AdelicNormInterface K L) (x : Kˣ) :
    x ∈ chapter14EverywhereLocalNormSubgroup N ↔ N.localNormAtEveryPlace x :=
  Iff.rfl

theorem chapter14_global_norm_denominator_is_contained_in_the_numerator
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (N : Chapter14AdelicNormInterface K L) :
    chapter14GlobalNormSubgroup N ≤ chapter14EverywhereLocalNormSubgroup N :=
  chapter14GlobalNormSubgroup_le_local N

theorem chapter14_knot_group_is_the_local_global_defect
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (N : Chapter14AdelicNormInterface K L) :
    chapter14KnotGroup N =
      (chapter14EverywhereLocalNormSubgroup N ⧸
        (chapter14GlobalNormSubgroup N).subgroupOf
          (chapter14EverywhereLocalNormSubgroup N)) :=
  rfl

def chapter14CyclicExtension (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] : Prop :=
  IsCyclic Gal(L/K)

theorem chapter14_hasse_norm_theorem
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic Gal(L/K)] (N : Chapter14AdelicNormInterface K L) :
    Subsingleton (chapter14KnotGroup N) := by
  sorry

theorem chapter14_cyclic_knot_group_is_trivial
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic Gal(L/K)] (N : Chapter14AdelicNormInterface K L) :
    ∀ x : chapter14KnotGroup N, x = 1 := by
  intro x
  have h : Subsingleton (chapter14KnotGroup N) :=
    chapter14_hasse_norm_theorem N
  exact h.elim x 1

/- LOCAL_DEPENDENCY_GUESS: the source invokes a biquadratic counterexample without fixing a
specific base field and polynomial; the predicates below keep the exact counterexample interface
available until that concrete example is supplied by the examples chapter. -/
def chapter14BiquadraticExtension (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] : Prop :=
  Module.finrank K L = 4 ∧ ¬ IsCyclic Gal(L/K)

def chapter14BiquadraticNormFailure
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (N : Chapter14AdelicNormInterface K L) : Prop :=
  chapter14BiquadraticExtension K L ∧
    ∃ b : Kˣ,
      b ∈ chapter14EverywhereLocalNormSubgroup N ∧
        b ∉ chapter14GlobalNormSubgroup N

/- The source asserts existence of such extensions without fixing a numerical
example, so package the existential witness together with all its field data. -/
structure Chapter14BiquadraticNormCounterexample where
  K : Type
  [field_K : Field K]
  [numberField_K : NumberField K]
  L : Type
  [field_L : Field L]
  [numberField_L : NumberField L]
  [algebra_K_L : Algebra K L]
  [finiteDimensional_K_L : FiniteDimensional K L]
  [galois_K_L : IsGalois K L]
  normData : Chapter14AdelicNormInterface K L
  failure : chapter14BiquadraticNormFailure normData

theorem chapter14_exists_biquadratic_norm_failure :
    Nonempty Chapter14BiquadraticNormCounterexample := by
  sorry

theorem chapter14_biquadratic_failure_makes_the_knot_nontrivial
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (N : Chapter14AdelicNormInterface K L)
    (hfailure : chapter14BiquadraticNormFailure N) :
    Nontrivial (chapter14KnotGroup N) := by
  sorry

theorem chapter14_knot_trivial_iff_local_global
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (N : Chapter14AdelicNormInterface K L)
    (htrivial : Subsingleton (chapter14KnotGroup N)) (b : Kˣ) :
    b ∈ chapter14EverywhereLocalNormSubgroup N ↔
      b ∈ chapter14GlobalNormSubgroup N := by
  constructor
  · intro hb
    let b' : chapter14EverywhereLocalNormSubgroup N := ⟨b, hb⟩
    have hq : (QuotientGroup.mk b' : chapter14KnotGroup N) = 1 :=
      htrivial.elim _ _
    exact (chapter14KnotGroup_eq_one_iff N b').mp hq
  · exact fun hb => chapter14GlobalNormSubgroup_le_local N hb

/-! Positivity and valuation divisibility are local obstructions, not global norm principles. -/

def chapter14PositiveRealNormCondition (x : ℝ) : Prop :=
  0 < x

def chapter14ComplexRealNormCondition (z : ℂ) : Prop :=
  chapter14PositiveRealNormCondition (Complex.normSq z)

theorem chapter14_complex_norm_to_real_is_positive {z : ℂ} (hz : z ≠ 0) :
    chapter14ComplexRealNormCondition z := by
  sorry

def chapter14UnramifiedNormValuationCondition (f : ℕ) (n : ℤ) : Prop :=
  0 < f ∧ (f : ℤ) ∣ n

def chapter14UnramifiedNormValuationObstruction (f : ℕ) (n : ℤ) : Prop :=
  ¬ chapter14UnramifiedNormValuationCondition f n

theorem chapter14_unramified_norms_have_divisible_valuation
    {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (vF : AddValuation F (WithTop ℤ)) (vE : AddValuation E (WithTop ℤ))
    (f : ℕ) (hf : 0 < f)
    (hformula :
      LastLib.Book04AdelesAndIdeles.Chapter10.chapter10NormValuationFormula F E vF vE f)
    {y : E} (hy : y ≠ 0) :
    LastLib.Book04AdelesAndIdeles.Chapter10.chapter10LocalNorm F E y ∈
      LastLib.Book04AdelesAndIdeles.Chapter10.chapter10ValuationDivisibleSet vF f := by
  sorry

end LastLib.Book04AdelesAndIdeles.Chapter14
