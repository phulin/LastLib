import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter07.Core
import Mathlib.Algebra.Polynomial.Roots

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter07

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open Polynomial
open scoped BigOperators

/-! ## 7.1. From dimensions to a polynomial -/

/-! A finite graded resolution expresses a Hilbert polynomial as an integral
linear combination of the shifted binomial polynomials attached to one
projective embedding. -/
def Chapter07IntegralBinomialExpansion (P : Polynomial ℚ) (r : ℕ) : Prop :=
  ∃ m : ℕ, ∃ c : Fin m → ℤ, ∃ a : Fin m → ℕ,
    P = ∑ i, Polynomial.C (c i : ℚ) * chapter07BinomialPolynomial r (a i)

theorem chapter07_hilbert_function_eq_euler_characteristic_eventually
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (S : Chapter07HilbertSetup k C) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (chapter07HilbertFunction S n : ℤ) = chapter07EulerCharacteristic S n := by
  rcases S.higherCohomologyVanishesEventually with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  change (Module.finrank k (S.cohomology 0 (n : ℤ)) : ℤ) =
    ∑ i ∈ Finset.range S.cohomologicalBound,
      (-1 : ℤ) ^ i * (Module.finrank k (S.cohomology i (n : ℤ)) : ℤ)
  by_cases hbound : S.cohomologicalBound = 0
  · have hzero := S.vanishes_above 0 (n : ℤ) (by simpa [hbound])
    letI : Subsingleton (S.cohomology 0 (n : ℤ)) :=
      ModuleCat.subsingleton_of_isZero hzero
    have hfin : Module.finrank k (S.cohomology 0 (n : ℤ)) = 0 :=
      Module.finrank_zero_of_subsingleton
    rw [hfin]
    simp [hbound]
  · have hbound_pos : 0 < S.cohomologicalBound := Nat.pos_of_ne_zero hbound
    have hsum :
        (∑ i ∈ Finset.range S.cohomologicalBound,
          (-1 : ℤ) ^ i * (Module.finrank k (S.cohomology i (n : ℤ)) : ℤ)) =
          (-1 : ℤ) ^ 0 * (Module.finrank k (S.cohomology 0 (n : ℤ)) : ℤ) := by
      apply Finset.sum_eq_single 0
      · intro b hb hne
        have hzero := hN n hn b (Nat.pos_of_ne_zero hne)
        letI : Subsingleton (S.cohomology b (n : ℤ)) :=
          ModuleCat.subsingleton_of_isZero hzero
        have hfin : Module.finrank k (S.cohomology b (n : ℤ)) = 0 :=
          Module.finrank_zero_of_subsingleton
        simp [hfin]
      · exact fun hnot => (hnot (Finset.mem_range.mpr hbound_pos)).elim
    rw [hsum]
    simp

theorem chapter07_polynomial_eq_of_eventually_equal
    {P Q : Polynomial ℚ}
    (h : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      P.eval (n : ℚ) = Q.eval (n : ℚ)) :
    P = Q := by
  rcases h with ⟨N, hN⟩
  apply Polynomial.eq_of_infinite_eval_eq
  let f : ℕ → ℚ := fun n => ((n + N : ℕ) : ℚ)
  have hf : Function.Injective f := by
    intro m n hmn
    exact_mod_cast hmn
  apply Set.Infinite.mono
    (show Set.range f ⊆ {x : ℚ | P.eval x = Q.eval x} from ?_)
    (Set.infinite_range_of_injective hf)
  rintro x ⟨n, rfl⟩
  exact hN (n + N) (Nat.le_add_left N n)

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
  rcases chapter07_polynomial_exists_of_vanishing_forward_differences
      (fun m : ℤ =>
        ∑ i ∈ Finset.range S.cohomologicalBound,
          (-1 : ℤ) ^ i * (Module.finrank k (S.cohomology i m) : ℤ))
      S.eulerCharacteristicDifferenceOrder
      S.eulerCharacteristicForwardDifferenceVanishes with
    ⟨P, hPint, hPeval⟩
  rcases chapter07_hilbert_function_eq_euler_characteristic_eventually S with
    ⟨N, hN⟩
  refine ⟨P, ⟨hPint, ?_, ?_⟩, ?_⟩
  · refine ⟨0, fun n _ => ?_⟩
    simpa [chapter07EulerCharacteristic, chapter07EulerCharacteristicAtInteger] using
      hPeval (n : ℤ)
  · refine ⟨N, fun n hn => ?_⟩
    have hEuler :
        P.eval (n : ℚ) = (chapter07EulerCharacteristic S n : ℚ) := by
      simpa [chapter07EulerCharacteristic, chapter07EulerCharacteristicAtInteger] using
        hPeval (n : ℤ)
    have hDim := congrArg (fun z : ℤ => (z : ℚ)) (hN n hn)
    exact hEuler.trans hDim.symm
  · intro Q hQ
    apply chapter07_polynomial_eq_of_eventually_equal
    rcases hQ.2.1 with ⟨NQ, hNQ⟩
    rcases (show Chapter07PolynomialMatchesEventually P
        (chapter07EulerCharacteristic S) from by
          exact ⟨0, fun n _ => by
            simpa [chapter07EulerCharacteristic, chapter07EulerCharacteristicAtInteger] using
              hPeval (n : ℤ)⟩) with ⟨NP, hNP⟩
    refine ⟨max NQ NP, fun n hn => ?_⟩
    rw [hNQ n (le_trans (Nat.le_max_left _ _) hn),
      hNP n (le_trans (Nat.le_max_right _ _) hn)]

noncomputable def chapter07HilbertPolynomial
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (S : Chapter07HilbertSetup k C) : Polynomial ℚ :=
  Classical.choose (chapter07_hilbert_polynomial_exists_unique S).exists

theorem chapter07_hilbert_polynomial_has_integral_binomial_expansion
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (S : Chapter07HilbertSetup k C)
    (hVeryAmple :
      LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04VeryAmple
        C.structureMap C.L) :
    ∃ r : ℕ, Chapter07IntegralBinomialExpansion
      (chapter07HilbertPolynomial S) r := by
  sorry

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
  rcases chapter07_polynomial_exists_of_vanishing_forward_differences
      (fun m : ℤ =>
        ∑ i ∈ Finset.range S.cohomologicalBound,
          (-1 : ℤ) ^ i * (Module.finrank k (S.cohomology i m) : ℤ))
      S.eulerCharacteristicDifferenceOrder
      S.eulerCharacteristicForwardDifferenceVanishes with
    ⟨P, hPint, hPeval⟩
  have hEq : P = chapter07HilbertPolynomial S := by
    apply chapter07_hilbert_polynomial_unique S
    refine ⟨0, fun n _ => ?_⟩
    simpa [chapter07EulerCharacteristic, chapter07EulerCharacteristicAtInteger] using
      hPeval (n : ℤ)
  rw [← hEq]
  simpa [chapter07EulerCharacteristicAtInteger] using hPeval n

theorem chapter07_hilbert_polynomial_eq_zero_of_zero_sheaf
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (S : Chapter07HilbertSetup k C) (hzero : IsZero S.F.sheaf) :
    chapter07HilbertPolynomial S = 0 := by
  apply chapter07_polynomial_eq_of_eventually_equal
  refine ⟨0, fun n _ => ?_⟩
  rw [chapter07_hilbert_polynomial_matches_euler_at_all_integers S (n : ℤ)]
  have hsum : chapter07EulerCharacteristicAtInteger S (n : ℤ) = 0 := by
    simp only [chapter07EulerCharacteristicAtInteger]
    apply Finset.sum_eq_zero
    intro i hi
    have hzi := S.cohomology_vanishes_when_sheaf_is_zero hzero i (n : ℤ)
    letI : Subsingleton (S.cohomology i (n : ℤ)) :=
      ModuleCat.subsingleton_of_isZero hzi
    have hfin : Module.finrank k (S.cohomology i (n : ℤ)) = 0 :=
      Module.finrank_zero_of_subsingleton
    simp [hfin]
  rw [hsum]
  simp

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
