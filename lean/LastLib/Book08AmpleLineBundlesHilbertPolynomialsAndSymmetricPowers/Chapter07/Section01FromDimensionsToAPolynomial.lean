import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter07.Core

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter07

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open Polynomial

/-! ## 7.1. From dimensions to a polynomial -/

theorem chapter07_hilbert_function_eq_euler_characteristic_eventually
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (S : Chapter07HilbertSetup k C) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (chapter07HilbertFunction S n : ℤ) = chapter07EulerCharacteristic S n := by
  sorry

theorem chapter07_polynomial_eq_of_eventually_equal
    {P Q : Polynomial ℚ}
    (h : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      P.eval (n : ℚ) = Q.eval (n : ℚ)) :
    P = Q := by
  sorry

/-! A finite-difference profile is the numerical form of the support
filtration argument.  The Newton basis gives an integer-valued polynomial on
all of `ℤ`, not merely on the nonnegative subsequence. -/
theorem chapter07_polynomial_exists_of_vanishing_forward_differences
    (f : ℤ → ℤ) (d : ℕ)
    (h : ∀ n : ℤ,
      chapter07IteratedForwardDifference d f n = 0) :
    ∃ P : Polynomial ℚ,
      Chapter07IntegerValuedOnIntegers P ∧
        ∀ n : ℤ, P.eval (n : ℚ) = (f n : ℚ) := by
  sorry

/-! The support-filtration argument also bounds the degree of the Newton
polynomial.  Keeping this as a separate strengthening leaves the basic
finite-difference existence lemma useful without extra bookkeeping. -/
theorem chapter07_polynomial_exists_of_vanishing_forward_differences_with_degree_bound
    (f : ℤ → ℤ) (d : ℕ)
    (h : ∀ n : ℤ,
      chapter07IteratedForwardDifference d f n = 0) :
    ∃ P : Polynomial ℚ,
      Chapter07IntegerValuedOnIntegers P ∧
        (∀ n : ℤ, P.eval (n : ℚ) = (f n : ℚ)) ∧
          P.natDegree ≤ d := by
  sorry

/-!
The Hilbert-polynomial theorem is stated with both the Euler characteristic
and the Hilbert function.  The latter equality is redundant after the first
theorem, but exposing both forms makes the API convenient for later exact
sequence and polarization arguments.
-/
theorem chapter07_hilbert_polynomial_exists_unique
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (S : Chapter07HilbertSetup k C) :
    ∃! P : Polynomial ℚ,
      Chapter07IntegerValuedOnIntegers P ∧
        Chapter07PolynomialMatchesEventually P
          (chapter07EulerCharacteristic S) ∧
        Chapter07PolynomialMatchesEventually P
          (fun n : ℕ => (chapter07HilbertFunction S n : ℤ)) := by
  sorry

noncomputable def chapter07HilbertPolynomial
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (S : Chapter07HilbertSetup k C) : Polynomial ℚ :=
  Classical.choose (chapter07_hilbert_polynomial_exists_unique S).exists

theorem chapter07_hilbert_polynomial_spec
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (S : Chapter07HilbertSetup k C) :
    Chapter07IntegerValuedOnIntegers (chapter07HilbertPolynomial S) ∧
      Chapter07PolynomialMatchesEventually (chapter07HilbertPolynomial S)
        (chapter07EulerCharacteristic S) ∧
      Chapter07PolynomialMatchesEventually (chapter07HilbertPolynomial S)
        (fun n : ℕ => (chapter07HilbertFunction S n : ℤ)) := by
  exact Classical.choose_spec (chapter07_hilbert_polynomial_exists_unique S).exists

theorem chapter07_hilbert_polynomial_integer_valued
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (S : Chapter07HilbertSetup k C) :
    Chapter07IntegerValuedOnIntegers (chapter07HilbertPolynomial S) := by
  exact (chapter07_hilbert_polynomial_spec S).1

theorem chapter07_hilbert_polynomial_matches_euler_eventually
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (S : Chapter07HilbertSetup k C) :
    Chapter07PolynomialMatchesEventually (chapter07HilbertPolynomial S)
      (chapter07EulerCharacteristic S) := by
  exact (chapter07_hilbert_polynomial_spec S).2.1

theorem chapter07_hilbert_polynomial_matches_function_eventually
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (S : Chapter07HilbertSetup k C) :
    Chapter07PolynomialMatchesEventually (chapter07HilbertPolynomial S)
      (fun n : ℕ => (chapter07HilbertFunction S n : ℤ)) := by
  exact (chapter07_hilbert_polynomial_spec S).2.2

/-! The Euler-characteristic polynomial is defined on all integer twists, not
only on the nonnegative twists used by the Hilbert function. -/
theorem chapter07_hilbert_polynomial_matches_euler_at_all_integers
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (S : Chapter07HilbertSetup k C) :
    ∀ n : ℤ,
      (chapter07HilbertPolynomial S).eval (n : ℚ) =
        chapter07EulerCharacteristicAtInteger S n := by
  sorry

theorem chapter07_hilbert_polynomial_eq_zero_of_zero_sheaf
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (S : Chapter07HilbertSetup k C) (hzero : IsZero S.F.sheaf) :
    chapter07HilbertPolynomial S = 0 := by
  sorry

theorem chapter07_hilbert_polynomial_unique
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (S : Chapter07HilbertSetup k C) {P : Polynomial ℚ}
    (hP_eventual : Chapter07PolynomialMatchesEventually P
      (chapter07EulerCharacteristic S)) :
    P = chapter07HilbertPolynomial S := by
  apply chapter07_polynomial_eq_of_eventually_equal
  rcases hP_eventual with ⟨NP, hNP⟩
  rcases chapter07_hilbert_polynomial_matches_euler_eventually S with ⟨NQ, hNQ⟩
  refine ⟨max NP NQ, fun n hn => ?_⟩
  rw [hNP n (le_trans (Nat.le_max_left _ _) hn),
    hNQ n (le_trans (Nat.le_max_right _ _) hn)]

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter07
