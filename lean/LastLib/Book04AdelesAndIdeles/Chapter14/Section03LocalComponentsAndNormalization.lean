import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Section01WhyFrobeniusIsCanonical
import LastLib.Book04AdelesAndIdeles.Chapter14.Dependencies
import LastLib.Book04AdelesAndIdeles.Chapter14.Section02FiniteLevelsAndRayNeighborhoods

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
    (v : NumberField.FinitePlace K)
    (π : (v.maximalIdeal.adicCompletion K)ˣ) : Prop :=
  Valued.v (π : v.maximalIdeal.adicCompletion K) = WithZero.exp (-1 : ℤ)

def chapter14FiniteUniformizerNormalization (K : Type*) [Field K] [NumberField K]
    (v : NumberField.FinitePlace K)
    (π : (v.maximalIdeal.adicCompletion K)ˣ) : Prop :=
  ((Chapter09.chapter09FiniteNormUnit v.maximalIdeal π :
      Chapter09.Chapter09PositiveReal) : ℝ) =
    (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ)⁻¹

theorem chapter14_finite_uniformizer_has_normalized_magnitude {K : Type*} [Field K]
    [NumberField K] (v : NumberField.FinitePlace K)
    (π : (v.maximalIdeal.adicCompletion K)ˣ)
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

/-! The principal-unit filtration at a finite place is the canonical Chapter 11 filtration. -/

def chapter14LocalUnitFiltrationAtFinitePlace {K : Type*} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K) (n : ℕ) :
    Subgroup (v.maximalIdeal.adicCompletionIntegers K)ˣ :=
  Chapter11.chapter11LocalUnitFiltration n

def chapter14LocalFieldUnitFiltrationAtFinitePlace {K : Type*} [Field K]
    [NumberField K] (v : NumberField.FinitePlace K) (n : ℕ) :
  Subgroup (v.maximalIdeal.adicCompletion K)ˣ :=
  Chapter11.chapter11FiniteLocalUnitGroup K v.maximalIdeal n

/-! Add the valuation coordinate to the unit filtration: level zero is the whole local
multiplicative group, level one is the valuation-ring unit group, and higher levels are principal
units. -/
def chapter14LocalMultiplicativeFiltrationAtFinitePlace {K : Type*} [Field K]
    [NumberField K] (v : NumberField.FinitePlace K) (n : ℕ) :
    Subgroup (v.maximalIdeal.adicCompletion K)ˣ :=
  if n = 0 then ⊤ else chapter14LocalFieldUnitFiltrationAtFinitePlace v (n - 1)

theorem chapter14_local_multiplicative_filtration_zero {K : Type*} [Field K]
    [NumberField K] (v : NumberField.FinitePlace K) :
    chapter14LocalMultiplicativeFiltrationAtFinitePlace v 0 = ⊤ := by
  simp [chapter14LocalMultiplicativeFiltrationAtFinitePlace]

theorem chapter14_local_multiplicative_filtration_succ {K : Type*} [Field K]
    [NumberField K] (v : NumberField.FinitePlace K) (n : ℕ) :
    chapter14LocalMultiplicativeFiltrationAtFinitePlace v (n + 1) =
      chapter14LocalFieldUnitFiltrationAtFinitePlace v n := by
  simp [chapter14LocalMultiplicativeFiltrationAtFinitePlace]

theorem chapter14_local_field_unit_filtration_zero {K : Type*} [Field K]
    [NumberField K] (v : NumberField.FinitePlace K) :
    chapter14LocalFieldUnitFiltrationAtFinitePlace v 0 =
      (v.maximalIdeal.adicCompletionIntegers K).unitGroup := by
  exact Chapter11.chapter11FiniteLocalUnitGroup_zero K v.maximalIdeal

theorem chapter14_local_unit_filtration_zero {K : Type*} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K) :
    chapter14LocalUnitFiltrationAtFinitePlace v 0 = ⊤ := by
  exact Chapter11.chapter11LocalUnitFiltration_zero

theorem chapter14_local_unit_filtration_succ {K : Type*} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K) (n : ℕ) :
    chapter14LocalUnitFiltrationAtFinitePlace v (n + 1) =
      Chapter11.chapter11LocalUnitFiltration (A :=
        v.maximalIdeal.adicCompletionIntegers K) (n + 1) := by
  rfl

theorem chapter14_local_unit_filtration_descends {K : Type*} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K) (n : ℕ) :
    chapter14LocalUnitFiltrationAtFinitePlace v (n + 1) ≤
      chapter14LocalUnitFiltrationAtFinitePlace v n := by
  sorry

theorem chapter14_real_local_quotient_records_sign :
    Nonempty (chapter14RealSignQuotient ≃* Multiplicative (ZMod 2)) :=
  chapter14_real_sign_quotient_has_order_two

theorem chapter14_complex_local_quotient_has_no_exponent
    {H : Type*} [CommGroup H] [Finite H] [TopologicalSpace H] [DiscreteTopology H]
    (f : ℂˣ →* H) (hf : Continuous f) :
    ∀ z, f z = 1 := by
  exact chapter14_complex_finite_continuous_quotient_is_trivial f hf

end LastLib.Book04AdelesAndIdeles.Chapter14
