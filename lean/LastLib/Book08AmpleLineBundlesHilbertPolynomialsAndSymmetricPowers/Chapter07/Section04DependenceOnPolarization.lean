import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter07.Section03DegreeDimensionAndExamples

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter07

noncomputable section

universe u

open CategoryTheory
open AlgebraicGeometry
open Polynomial

/-! ## 7.4. Dependence on the polarization -/

def chapter07PowerPolynomial (P : Polynomial ℚ) (q : ℕ) : Polynomial ℚ :=
  P.comp (Polynomial.C (q : ℚ) * Polynomial.X)

theorem chapter07_powerPolynomial_eval
    (P : Polynomial ℚ) (q n : ℕ) :
    (chapter07PowerPolynomial P q).eval (n : ℚ) =
      P.eval ((q * n : ℕ) : ℚ) := by
  sorry

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
  sorry

theorem chapter07_hilbert_polynomial_of_tensor_power
    {P Q : Polynomial ℚ} (q : ℕ) (_hq : 0 < q)
    (h : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Q.eval (n : ℚ) = P.eval ((q * n : ℕ) : ℚ)) :
    Q = P.comp (Polynomial.C (q : ℚ) * Polynomial.X) := by
  simpa [chapter07PowerPolynomial] using
    chapter07_polynomial_reparametrization_of_eventual_power_relation q h

theorem chapter07_power_polynomial_degree
    (P : Polynomial ℚ) (q : ℕ) (hq : 0 < q) (hP : P ≠ 0) :
    (chapter07PowerPolynomial P q).natDegree = P.natDegree := by
  sorry

theorem chapter07_power_polynomial_leading_coefficient
    (P : Polynomial ℚ) (q : ℕ) (hq : 0 < q) (hP : P ≠ 0) :
    (chapter07PowerPolynomial P q).leadingCoeff =
      (q : ℚ) ^ P.natDegree * P.leadingCoeff := by
  sorry

/-!
The support dimension is a property of the coherent sheaf, while the
coefficient of the top term is a degree measured by the chosen polarization.
-/
def Chapter07SupportHasDimension
    {X : Scheme.{u}} (F : Chapter07CoherentSheaf X) (d : ℕ) : Prop :=
  ∃ D : Chapter07SupportDimensionCertificate F, D.dimension = d

theorem chapter07_support_dimension_independent_of_polarization
    {k : Type u} [Field k]
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
    (hcurve : D.dimension = 1)
    (hF : Chapter07NonzeroCoherentSheaf S.F) :
    ∃ e : ℕ, 0 < e ∧
      (chapter07HilbertPolynomial S).coeff 1 = (e : ℚ) := by
  sorry

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
  sorry

theorem chapter07_finite_length_has_intrinsic_hilbert_polynomial
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (D : Chapter07ZeroDimensionalHilbertData (k := k) (C := C)) :
    chapter07HilbertPolynomial D.setup = Polynomial.C (D.length : ℚ) := by
  exact chapter07_zero_dimensional_hilbert_polynomial D

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter07
