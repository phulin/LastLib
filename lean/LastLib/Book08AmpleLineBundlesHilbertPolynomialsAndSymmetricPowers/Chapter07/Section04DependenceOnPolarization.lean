import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter07.Section03DegreeDimensionAndExamples
import Mathlib.Algebra.Polynomial.Degree.Lemmas

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter07

noncomputable section

universe u

open CategoryTheory
open AlgebraicGeometry
open Polynomial

/-! ## 7.4. Dependence on the polarization -/

def chapter07PowerPolynomial (P : Polynomial ℚ) (q : ℕ) : Polynomial ℚ :=
  P.comp (Polynomial.C (q : ℚ) * Polynomial.X)

/-!
The tensor-power comparison is recorded at the numerical field-aware level.
Each setup already identifies its module-valued cohomology with the canonical
cohomology of the corresponding twisted sheaf, so this relation compares the
geometric cohomology dimensions used by the Hilbert functions.
-/
structure Chapter07TensorPowerCohomologyBridge
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (S T : Chapter07HilbertSetup k C) (q : ℕ) where
  positive : 0 < q
  geometricFinrank_eq :
    ∀ (i n : ℕ),
      chapter07GeometricCohomologyFinrank
          (T.cohomologyRepresentsTwistedSheaf i n) =
        chapter07GeometricCohomologyFinrank
          (S.cohomologyRepresentsTwistedSheaf i (q * n))

theorem chapter07_powerPolynomial_eval
    (P : Polynomial ℚ) (q n : ℕ) :
    (chapter07PowerPolynomial P q).eval (n : ℚ) =
      P.eval ((q * n : ℕ) : ℚ) := by
  simp [chapter07PowerPolynomial, Polynomial.eval_comp]
  push_cast
  ring

theorem chapter07_polynomial_reparametrization_of_eventual_power_relation
    {P Q : Polynomial ℚ} (q : ℕ)
    (h : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Q.eval (n : ℚ) = P.eval ((q * n : ℕ) : ℚ)) :
    Q = chapter07PowerPolynomial P q := by
  apply chapter07_polynomial_eq_of_eventually_equal
  rcases h with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  rw [hN n hn, chapter07_powerPolynomial_eval]

theorem chapter07_power_polynomial_integer_valued
    (P : Polynomial ℚ) (q : ℕ)
    (hP : Chapter07IntegerValuedOnIntegers P) :
    Chapter07IntegerValuedOnIntegers (chapter07PowerPolynomial P q) := by
  intro n
  rcases hP (q * n) with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  simpa [chapter07PowerPolynomial, Polynomial.eval_comp] using hz

theorem chapter07_hilbert_polynomial_of_tensor_power
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (S T : Chapter07HilbertSetup k C) (q : ℕ)
    (hTwist : Chapter07TensorPowerCohomologyBridge S T q) :
    chapter07HilbertPolynomial T =
      chapter07PowerPolynomial (chapter07HilbertPolynomial S) q := by
  apply chapter07_polynomial_eq_of_eventually_equal
  rcases chapter07_hilbert_polynomial_matches_function_eventually T with
    ⟨NT, hNT⟩
  rcases chapter07_hilbert_polynomial_matches_function_eventually S with
    ⟨NS, hNS⟩
  refine ⟨max NT NS, fun n hn => ?_⟩
  have hT := hNT n (le_trans (Nat.le_max_left _ _) hn)
  have hS := hNS (q * n) (by
    have hn' : NS ≤ n := le_trans (Nat.le_max_right _ _) hn
    exact le_trans hn' (Nat.le_mul_of_pos_left n hTwist.positive))
  have hfin := hTwist.geometricFinrank_eq 0 n
  have hfun : chapter07HilbertFunction T n =
      chapter07HilbertFunction S (q * n) := by
    simpa [chapter07HilbertFunction, chapter07GeometricCohomologyFinrank] using hfin
  calc
    (chapter07HilbertPolynomial T).eval (n : ℚ) =
        (chapter07HilbertFunction T n : ℚ) := hT
    _ = (chapter07HilbertFunction S (q * n) : ℚ) := by rw [hfun]
    _ = (chapter07HilbertPolynomial S).eval ((q * n : ℕ) : ℚ) := hS.symm
    _ = (chapter07PowerPolynomial (chapter07HilbertPolynomial S) q).eval
        (n : ℚ) := (chapter07_powerPolynomial_eval
          (chapter07HilbertPolynomial S) q n).symm

theorem chapter07_power_polynomial_degree
    (P : Polynomial ℚ) (q : ℕ) (hq : 0 < q) (hP : P ≠ 0) :
    (chapter07PowerPolynomial P q).natDegree = P.natDegree := by
  unfold chapter07PowerPolynomial
  have hqQ : (q : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hq)
  have hcomp : (Polynomial.C (q : ℚ) * Polynomial.X).natDegree = 1 := by
    rw [Polynomial.natDegree_C_mul hqQ, Polynomial.natDegree_X]
  rw [Polynomial.natDegree_comp, hcomp, Nat.mul_one]

theorem chapter07_power_polynomial_leading_coefficient
    (P : Polynomial ℚ) (q : ℕ) (hq : 0 < q) (hP : P ≠ 0) :
    (chapter07PowerPolynomial P q).leadingCoeff =
      (q : ℚ) ^ P.natDegree * P.leadingCoeff := by
  unfold chapter07PowerPolynomial
  have hqQ : (q : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hq)
  have hcomp : (Polynomial.C (q : ℚ) * Polynomial.X).natDegree ≠ 0 := by
    rw [Polynomial.natDegree_C_mul hqQ, Polynomial.natDegree_X]
    norm_num
  rw [Polynomial.leadingCoeff_comp hcomp]
  rw [Polynomial.leadingCoeff_C_mul_X]
  ring

/-!
The support dimension is a property of the coherent sheaf, while the
coefficient of the top term is a degree measured by the chosen polarization.
-/
def Chapter07SupportHasDimension
    {X : Scheme.{u}} (F : Chapter07CoherentSheaf X) (d : ℕ) : Prop :=
  ∃ D : Chapter07SupportDimensionCertificate F, D.dimension = d

theorem chapter07_support_has_dimension_iff
    {X : Scheme.{u}} (F : Chapter07CoherentSheaf X) (d : ℕ) :
    Chapter07SupportHasDimension F d ↔
      LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04SheafHasSupportDimension
        F.sheaf d := by
  constructor
  · rintro ⟨D, hD⟩
    simpa [hD] using D.dimension_has_supportDimension
  · intro hD
    exact ⟨{ dimension := d, dimension_has_supportDimension := hD }, rfl⟩

theorem chapter07_support_dimension_independent_of_polarization
    {X : Scheme.{u}} (F : Chapter07CoherentSheaf X)
    (d : ℕ)
    (h₁ : Chapter07SupportHasDimension F d) :
    ∀ _L : Chapter07LineBundle X, Chapter07SupportHasDimension F d := by
  intro _L
  exact h₁

theorem chapter07_curve_linear_coefficient_is_polarized_degree
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (S : Chapter07HilbertSetup k C)
    (D : Chapter07SupportDimensionCertificate S.F)
    (hDimensionData : Chapter07HilbertPolynomialDimensionCertificate S D)
    (hcurve : D.dimension = 1)
    (hF : Chapter07NonzeroCoherentSheaf S.F) :
    ∃ e : ℕ, 0 < e ∧
      (chapter07HilbertPolynomial S).coeff 1 = (e : ℚ) := by
  rcases chapter07_projective_curve_hilbert_polynomial_shape
      S D hDimensionData hcurve hF with ⟨e, he, c, hshape⟩
  refine ⟨e, he, ?_⟩
  rw [hshape]
  simp

theorem chapter07_finite_scheme_length_is_polarization_independent
    {k : Type u} [Field k]
    {C₁ C₂ : Chapter07PolarizedScheme k}
    (D₁ : Chapter07ZeroDimensionalHilbertData (k := k) (C := C₁))
    (D₂ : Chapter07ZeroDimensionalHilbertData (k := k) (C := C₂))
    (hLength : D₁.length = D₂.length) :
    chapter07HilbertPolynomial D₁.setup =
      chapter07HilbertPolynomial D₂.setup := by
  rw [chapter07_zero_dimensional_hilbert_polynomial D₁,
    chapter07_zero_dimensional_hilbert_polynomial D₂, hLength]

/-!
This is the source-facing moduli boundary: a Hilbert polynomial is specified
only after the polarization/embedding has been fixed.
-/
def Chapter07FixedHilbertPolynomialCondition
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (S : Chapter07HilbertSetup k C) (P : Polynomial ℚ) : Prop :=
  chapter07HilbertPolynomial S = P

structure Chapter07HilbertModuliSpecification
    (k : Type u) [Field k] where
  polarization : Chapter07PolarizedScheme k
  targetPolynomial : Polynomial ℚ
  targetIsIntegerValued : Chapter07IntegerValuedOnIntegers targetPolynomial
  object : Chapter07HilbertSetup k polarization
  satisfiesTarget : Chapter07FixedHilbertPolynomialCondition object targetPolynomial

theorem chapter07_fixed_polarization_is_part_of_hilbert_moduli_data
    {k : Type u} [Field k]
    (M : Chapter07HilbertModuliSpecification k) :
    Chapter07FixedHilbertPolynomialCondition M.object M.targetPolynomial := by
  exact M.satisfiesTarget

theorem chapter07_polarizations_can_change_leading_coefficients
    (P : Polynomial ℚ) (hP : P ≠ 0) (hpositive : 0 < P.natDegree) :
    ∃ q : ℕ, 1 < q ∧
      (chapter07PowerPolynomial P q).natDegree = P.natDegree ∧
        (chapter07PowerPolynomial P q).leadingCoeff ≠ P.leadingCoeff := by
  refine ⟨2, by norm_num, ?_, ?_⟩
  · exact chapter07_power_polynomial_degree P 2 (by norm_num) hP
  · rw [chapter07_power_polynomial_leading_coefficient P 2 (by norm_num) hP]
    have hpow : 1 < (2 : ℚ) ^ P.natDegree :=
      one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hpositive)
    intro hEq
    have hzero : ((2 : ℚ) ^ P.natDegree - 1) * P.leadingCoeff = 0 := by
      calc
        ((2 : ℚ) ^ P.natDegree - 1) * P.leadingCoeff =
            (2 : ℚ) ^ P.natDegree * P.leadingCoeff - P.leadingCoeff := by ring
        _ = 0 := sub_eq_zero.mpr hEq
    exact (mul_ne_zero (sub_ne_zero.mpr (ne_of_gt hpow))
      (Polynomial.leadingCoeff_ne_zero.mpr hP)) hzero

theorem chapter07_finite_length_has_intrinsic_hilbert_polynomial
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (D : Chapter07ZeroDimensionalHilbertData (k := k) (C := C)) :
    chapter07HilbertPolynomial D.setup = Polynomial.C (D.length : ℚ) := by
  exact chapter07_zero_dimensional_hilbert_polynomial D

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter07
