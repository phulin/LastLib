import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Section01WhyFrobeniusIsCanonical
import LastLib.Book04AdelesAndIdeles.Chapter14.Dependencies

/-!
# 14.3. Local components and normalization
-/

noncomputable section

namespace LastLib.Book04AdelesAndIdeles.Chapter14

open scoped NNReal NumberField

noncomputable def chapter14FrobeniusAtConvention (c : Chapter14FrobeniusConvention)
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l] : Gal(l/k) :=
  match c with
  | .arithmetic =>
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.chapter06ArithmeticFrobenius k l
  | .geometric =>
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.chapter06GeometricFrobenius k l

abbrev chapter14ArithmeticFrobenius (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l] : Gal(l/k) :=
  chapter14FrobeniusAtConvention .arithmetic k l

abbrev chapter14GeometricFrobenius (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l] : Gal(l/k) :=
  chapter14FrobeniusAtConvention .geometric k l

theorem chapter14_arithmetic_frobenius_apply (k l : Type*) [Field k] [Fintype k]
    [Field l] [Finite l] [Algebra k l] [Algebra.IsAlgebraic k l] (x : l) :
    chapter14ArithmeticFrobenius k l x = x ^ Fintype.card k := by
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.chapter06_arithmetic_frobenius_apply
    k l x

theorem chapter14_geometric_frobenius_is_inverse (k l : Type*) [Field k] [Fintype k]
    [Field l] [Finite l] [Algebra k l] [Algebra.IsAlgebraic k l] :
    chapter14GeometricFrobenius k l = (chapter14ArithmeticFrobenius k l)⁻¹ := by
  rfl

theorem chapter14_frobenius_convention_cases (c : Chapter14FrobeniusConvention)
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l] :
    c = .arithmetic ∨ c = .geometric := by
  cases c <;> simp

/-! The finite-place normalization is independent of the Frobenius convention. -/

def chapter14FiniteUniformizer (K : Type*) [Field K] [NumberField K]
    (v : NumberField.FinitePlace K) (π : K) : Prop :=
  v.maximalIdeal.valuation K π = WithZero.exp (-1 : ℤ)

def chapter14FiniteUniformizerNormalization (K : Type*) [Field K] [NumberField K]
    (v : NumberField.FinitePlace K) (π : K) : Prop :=
  (((Ideal.absNorm v.maximalIdeal.asIdeal : ℝ≥0) ^
      (-LastLib.Book04AdelesAndIdeles.Chapter08.chapter08LocalOrder v.maximalIdeal
        (NumberField.FinitePlace.embedding v.maximalIdeal π)) : ℝ≥0) : ℝ) =
    (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ)⁻¹

theorem chapter14_finite_uniformizer_has_normalized_magnitude {K : Type*} [Field K]
    [NumberField K] (v : NumberField.FinitePlace K) (π : K)
    (hπ : chapter14FiniteUniformizer K v π) :
    chapter14FiniteUniformizerNormalization K v π := by
  sorry

def chapter14InfiniteNormalizedMagnitude {K : Type*} [Field K]
    (w : NumberField.InfinitePlace K) (x : K) : ℝ :=
  w x ^ w.mult

theorem chapter14_real_infinite_magnitude_is_ordinary {K : Type*} [Field K]
    (w : NumberField.InfinitePlace K) (hw : w.IsReal) (x : K) :
    chapter14InfiniteNormalizedMagnitude w x = w x := by
  simp [chapter14InfiniteNormalizedMagnitude, hw.mult_eq_one]

theorem chapter14_complex_infinite_magnitude_is_squared {K : Type*} [Field K]
    (w : NumberField.InfinitePlace K) (hw : w.IsComplex) (x : K) :
    chapter14InfiniteNormalizedMagnitude w x = (w x) ^ 2 := by
  simp [chapter14InfiniteNormalizedMagnitude, hw.mult_eq_two]

/-! The principal-unit filtration at a finite place. -/

def chapter14PrincipalUnitSubgroup (R : Type*) [CommRing R] (I : Ideal R) (n : ℕ) :
    Subgroup Rˣ where
  carrier := {u | (u : R) - 1 ∈ I ^ n}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    sorry
  inv_mem' := by
    intro a ha
    sorry

def chapter14LocalFieldUnitEmbedding {K : Type*} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K) :
    (v.maximalIdeal.adicCompletionIntegers K)ˣ →*
      (v.maximalIdeal.adicCompletion K)ˣ :=
  Units.map (algebraMap (v.maximalIdeal.adicCompletionIntegers K)
    (v.maximalIdeal.adicCompletion K)).toMonoidHom

def chapter14LocalUnitFiltrationAtFinitePlace {K : Type*} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K) (n : ℕ) :
    Subgroup (v.maximalIdeal.adicCompletionIntegers K)ˣ :=
    if n = 0 then ⊤ else
    chapter14PrincipalUnitSubgroup
      (v.maximalIdeal.adicCompletionIntegers K)
      (IsLocalRing.maximalIdeal (v.maximalIdeal.adicCompletionIntegers K)) n

def chapter14LocalFieldUnitFiltrationAtFinitePlace {K : Type*} [Field K]
    [NumberField K] (v : NumberField.FinitePlace K) (n : ℕ) :
    Subgroup (v.maximalIdeal.adicCompletion K)ˣ :=
  Subgroup.map (chapter14LocalFieldUnitEmbedding v)
    (chapter14LocalUnitFiltrationAtFinitePlace v n)

theorem chapter14_local_field_unit_filtration_zero {K : Type*} [Field K]
    [NumberField K] (v : NumberField.FinitePlace K) :
    chapter14LocalFieldUnitFiltrationAtFinitePlace v 0 =
      Subgroup.map (chapter14LocalFieldUnitEmbedding v) (⊤ :
        Subgroup (v.maximalIdeal.adicCompletionIntegers K)ˣ) := by
  simp [chapter14LocalFieldUnitFiltrationAtFinitePlace,
    chapter14LocalUnitFiltrationAtFinitePlace]

theorem chapter14_local_unit_filtration_zero {K : Type*} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K) :
    chapter14LocalUnitFiltrationAtFinitePlace v 0 = ⊤ := by
  simp [chapter14LocalUnitFiltrationAtFinitePlace]

theorem chapter14_local_unit_filtration_succ {K : Type*} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K) (n : ℕ) :
    chapter14LocalUnitFiltrationAtFinitePlace v (n + 1) =
      chapter14PrincipalUnitSubgroup
        (v.maximalIdeal.adicCompletionIntegers K)
        (IsLocalRing.maximalIdeal (v.maximalIdeal.adicCompletionIntegers K)) (n + 1) := by
  simp [chapter14LocalUnitFiltrationAtFinitePlace]

theorem chapter14_local_unit_filtration_descends {K : Type*} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K) (n : ℕ) :
    chapter14LocalUnitFiltrationAtFinitePlace v (n + 1) ≤
      chapter14LocalUnitFiltrationAtFinitePlace v n := by
  sorry

theorem chapter14_real_local_quotient_records_sign :
    Nonempty (chapter14RealSignQuotient ≃* Multiplicative (ZMod 2)) :=
  chapter14_real_sign_quotient_has_order_two

theorem chapter14_complex_local_quotient_has_no_exponent :
    Subsingleton chapter14ComplexMagnitudeQuotient := by
  sorry

end LastLib.Book04AdelesAndIdeles.Chapter14
