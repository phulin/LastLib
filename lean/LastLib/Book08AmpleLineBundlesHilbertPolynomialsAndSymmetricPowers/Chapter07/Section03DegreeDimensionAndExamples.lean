import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter07.Section02PolynomialOfProjectiveScheme
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter07

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open Polynomial

/-! ## 7.3. Degree, dimension, and examples -/

def Chapter07NonzeroCoherentSheaf
    {X : Scheme.{u}} (F : Chapter07CoherentSheaf X) : Prop :=
  ¬ IsZero F.sheaf

theorem chapter07_degree_dimension_and_leading_term
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (S : Chapter07HilbertSetup k C)
    (D : Chapter07SupportDimensionCertificate S.F)
    (hDimensionData : Chapter07HilbertPolynomialDimensionCertificate S D)
    (hF : Chapter07NonzeroCoherentSheaf S.F) :
    ∃ e : ℕ, 0 < e ∧
      (chapter07HilbertPolynomial S).natDegree = D.dimension ∧
      (chapter07HilbertPolynomial S).leadingCoeff =
        (e : ℚ) / Nat.factorial D.dimension := by
  rcases hDimensionData.topDifference_positive with ⟨e, he, htop⟩
  have horder : S.eulerCharacteristicDifferenceOrder = D.dimension + 1 :=
    hDimensionData.differenceOrder_eq
  have heQ : (e : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt he)
  have hEval (n : ℤ) :
      (chapter07HilbertPolynomial S).eval (n : ℚ) =
        (chapter07EulerCharacteristicAtInteger S n : ℚ) :=
    chapter07_hilbert_polynomial_matches_euler_at_all_integers S n
  have hIterEval (j : ℕ) (n : ℤ) :
      (fwdDiff (1 : ℚ))^[j]
          (fun x : ℚ => (chapter07HilbertPolynomial S).eval x) (n : ℚ) =
        (chapter07IteratedForwardDifference j
          (fun m : ℤ => chapter07EulerCharacteristicAtInteger S m) n : ℚ) := by
    induction j generalizing n with
    | zero => simpa using hEval n
    | succ j ih =>
        rw [Function.iterate_succ_apply']
        simp only [fwdDiff]
        rw [show (n : ℚ) + 1 = ((n + 1 : ℤ) : ℚ) by push_cast,
          ih (n + 1), ih n]
        simp [chapter07IteratedForwardDifference, chapter07ForwardDifference] <;>
          push_cast
  have hTopPoly (n : ℤ) :
      (fwdDiff (1 : ℚ))^[D.dimension]
          (fun x : ℚ => (chapter07HilbertPolynomial S).eval x) (n : ℚ) =
        (e : ℚ) := by
    calc
      _ = (chapter07IteratedForwardDifference D.dimension
          (fun m : ℤ => chapter07EulerCharacteristicAtInteger S m) n : ℚ) :=
        hIterEval D.dimension n
      _ = (e : ℚ) := by rw [htop n]
  have hTopOrderPoly (n : ℤ) :
      (fwdDiff (1 : ℚ))^[D.dimension + 1]
          (fun x : ℚ => (chapter07HilbertPolynomial S).eval x) (n : ℚ) = 0 := by
    calc
      _ = (chapter07IteratedForwardDifference (D.dimension + 1)
          (fun m : ℤ => chapter07EulerCharacteristicAtInteger S m) n : ℚ) :=
        hIterEval (D.dimension + 1) n
      _ = 0 := by
        have hzero := S.eulerCharacteristicForwardDifferenceVanishes n
        have hzero' := congrArg (fun z : ℤ => (z : ℚ)) hzero
        simpa [horder, chapter07EulerCharacteristicAtInteger] using hzero'
  let delta : Polynomial ℚ → Polynomial ℚ := fun P =>
    P.comp (Polynomial.X + Polynomial.C 1) - P
  have hdelta_one (P : Polynomial ℚ) :
      fwdDiff (1 : ℚ) (fun x : ℚ => P.eval x) =
        (delta P).eval := by
    ext x
    simp [fwdDiff, delta, Polynomial.eval_sub, Polynomial.eval_comp]
  have hdelta_iter (j : ℕ) :
      (fwdDiff (1 : ℚ))^[j]
          (fun x : ℚ => (chapter07HilbertPolynomial S).eval x) =
        (delta^[j] (chapter07HilbertPolynomial S)).eval := by
    induction j with
    | zero => rfl
    | succ j ih =>
        simpa only [Function.iterate_succ_apply', ih] using
          hdelta_one (delta^[j] (chapter07HilbertPolynomial S))
  have hzeroDelta :
      delta^[D.dimension + 1] (chapter07HilbertPolynomial S) = 0 := by
    apply chapter07_polynomial_eq_of_eventually_equal
    refine ⟨0, fun n _ => ?_⟩
    calc
      (delta^[D.dimension + 1] (chapter07HilbertPolynomial S)).eval (n : ℚ) =
          (fwdDiff (1 : ℚ))^[D.dimension + 1]
            (fun x : ℚ => (chapter07HilbertPolynomial S).eval x) (n : ℚ) :=
              (congrFun (hdelta_iter (D.dimension + 1)) (n : ℚ)).symm
      _ = 0 := hTopOrderPoly (n : ℤ)
      _ = (0 : Polynomial ℚ).eval (n : ℚ) := by simp
  have hzeroPfun :
      (fwdDiff (1 : ℚ))^[D.dimension + 1]
          (fun x : ℚ => (chapter07HilbertPolynomial S).eval x) = 0 := by
    rw [hdelta_iter (D.dimension + 1), hzeroDelta]
    simp
  have hPne : chapter07HilbertPolynomial S ≠ 0 := by
    intro hP
    have h := hTopPoly 0
    rw [hP] at h
    simp at h
    exact heQ h.symm
  have hDegreeUpper :
      (chapter07HilbertPolynomial S).natDegree ≤ D.dimension := by
    by_contra hnot
    have hle : D.dimension + 1 ≤
        (chapter07HilbertPolynomial S).natDegree := by omega
    have hzeroTop :
        (fwdDiff (1 : ℚ))^[((chapter07HilbertPolynomial S).natDegree)]
            (fun x : ℚ => (chapter07HilbertPolynomial S).eval x) = 0 := by
      rw [← Nat.sub_add_cancel hle, Function.iterate_add_apply, hzeroPfun]
      simp
    have hfactor := congrFun
      (Polynomial.fwdDiff_iter_degree_eq_factorial
        (chapter07HilbertPolynomial S)) 0
    rw [hzeroTop] at hfactor
    have hfactor_zero :
        (chapter07HilbertPolynomial S).leadingCoeff *
            ((chapter07HilbertPolynomial S).natDegree.factorial : ℚ) = 0 := by
      simpa [Pi.smul_apply, smul_eq_mul] using hfactor.symm
    exact (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hPne)
      (by exact_mod_cast Nat.factorial_ne_zero
        (chapter07HilbertPolynomial S).natDegree)) hfactor_zero
  have hDegreeLower :
      D.dimension ≤ (chapter07HilbertPolynomial S).natDegree := by
    by_contra hnot
    have hlt : (chapter07HilbertPolynomial S).natDegree < D.dimension :=
      Nat.lt_of_not_ge hnot
    have hzero :=
      Polynomial.fwdDiff_iter_eq_zero_of_degree_lt
        (P := chapter07HilbertPolynomial S) hlt
    have hzero' := congrFun hzero 0
    have htop' := hTopPoly 0
    have hezero : (e : ℚ) = 0 := by
      calc
        (e : ℚ) =
            (fwdDiff (1 : ℚ))^[D.dimension]
              (fun x : ℚ => (chapter07HilbertPolynomial S).eval x) 0 :=
          htop'.symm
        _ = 0 := hzero'
    exact heQ hezero
  have hdegree :
      (chapter07HilbertPolynomial S).natDegree = D.dimension :=
    Nat.le_antisymm hDegreeUpper hDegreeLower
  refine ⟨e, he, hdegree, ?_⟩
  have hfactor := congrFun
    (Polynomial.fwdDiff_iter_degree_eq_factorial
      (chapter07HilbertPolynomial S)) 0
  rw [hdegree] at hfactor
  have hleading :
      (chapter07HilbertPolynomial S).leadingCoeff *
          (D.dimension.factorial : ℚ) = (e : ℚ) := by
    calc
      (chapter07HilbertPolynomial S).leadingCoeff *
          (D.dimension.factorial : ℚ) =
          (fwdDiff (1 : ℚ))^[D.dimension]
            (fun x : ℚ => (chapter07HilbertPolynomial S).eval x) 0 := by
              simpa [Pi.smul_apply, smul_eq_mul] using hfactor.symm
      _ = (e : ℚ) := hTopPoly 0
  apply (eq_div_iff (by exact_mod_cast
    Nat.factorial_ne_zero D.dimension :
      (D.dimension.factorial : ℚ) ≠ 0)).2
  exact hleading

theorem chapter07_hilbert_polynomial_has_positive_degree_coefficient
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (S : Chapter07HilbertSetup k C)
    (D : Chapter07SupportDimensionCertificate S.F)
    (hDimensionData : Chapter07HilbertPolynomialDimensionCertificate S D)
    (hF : Chapter07NonzeroCoherentSheaf S.F) :
    ∃ e : ℕ, 0 < e ∧
      (chapter07HilbertPolynomial S).coeff D.dimension =
        (e : ℚ) / Nat.factorial D.dimension := by
  rcases chapter07_degree_dimension_and_leading_term
      S D hDimensionData hF with ⟨e, he, hdegree, hleading⟩
  refine ⟨e, he, ?_⟩
  rw [← hdegree]
  simpa [Polynomial.leadingCoeff] using hleading

/-!
The error term records the lower-dimensional contribution left by a hyperplane
which is not assumed to be a nonzerodivisor on every associated component.
-/
structure Chapter07HyperplaneSection
    {k : Type u} [Field k]
    (C : Chapter07PolarizedScheme k) where
  H : Chapter07PolarizedScheme k
  inclusion : H.X ⟶ C.X
  isClosedImmersion : IsClosedImmersion inclusion
  overBase : inclusion ≫ C.structureMap = H.structureMap
  inducedPolarization :
    H.L.sheaf ≅ (Scheme.Modules.pullback inclusion).obj C.L.sheaf

/-! The colon/kernel correction in the general hyperplane argument is carried
by an explicit lower-dimensional error profile.  The Euler relation is the
cohomological content of the restriction sequence; the support disjunction
is the dimension estimate used for the error polynomial. -/
structure Chapter07HyperplaneRestrictionData
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (H : Chapter07HyperplaneSection C)
    (S : Chapter07HilbertSetup k C)
    (R : Chapter07HilbertSetup k H.H) (d : ℕ) where
  error : Chapter07HilbertSetup k C
  restrictionSheaf :
    R.F.sheaf ≅ (Scheme.Modules.pullback H.inclusion).obj S.F.sheaf
  eulerRelation : ∀ n : ℕ,
    chapter07EulerCharacteristicAtInteger S (n : ℤ) -
        chapter07EulerCharacteristicAtInteger S ((n : ℤ) - 1) =
      chapter07EulerCharacteristicAtInteger R (n : ℤ) -
        chapter07EulerCharacteristicAtInteger error ((n : ℤ) - 1)
  errorLowerDimensional :
    IsZero error.F.sheaf ∨
      ∃ D : Chapter07SupportDimensionCertificate error.F,
        ¬ IsZero error.F.sheaf ∧ D.dimension < d ∧
          Nonempty (Chapter07HilbertPolynomialDimensionCertificate error D)

def chapter07FiniteDifference (P : Polynomial ℚ) : Polynomial ℚ :=
  P - P.comp (Polynomial.X - Polynomial.C 1)

theorem chapter07_finiteDifference_eval
    (P : Polynomial ℚ) (n : ℤ) :
    (chapter07FiniteDifference P).eval (n : ℚ) =
      P.eval (n : ℚ) - P.eval ((n - 1 : ℤ) : ℚ) := by
  simp [chapter07FiniteDifference, Polynomial.eval_sub, Polynomial.eval_comp]
  congr 1
  push_cast
  ring

theorem chapter07_hyperplane_finite_difference
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (S : Chapter07HilbertSetup k C)
    (H : Chapter07HyperplaneSection C)
    (R : Chapter07HilbertSetup k H.H)
    (d : ℕ)
    (hDim : ∃ D : Chapter07SupportDimensionCertificate S.F,
      D.dimension = d)
    (hRestriction :
      Nonempty (Chapter07HyperplaneRestrictionData H S R d)) :
    ∃ E : Polynomial ℚ,
      (E = 0 ∨ E.natDegree < d) ∧
        chapter07FiniteDifference (chapter07HilbertPolynomial S) =
          chapter07HilbertPolynomial R + E := by
  rcases hRestriction with ⟨hRestriction⟩
  let E : Polynomial ℚ :=
    -(chapter07HilbertPolynomial hRestriction.error).comp
      (Polynomial.X - Polynomial.C 1)
  refine ⟨E, ?_, ?_⟩
  · rcases hRestriction.errorLowerDimensional with hzero | hdim
    · left
      have hPzero := chapter07_hilbert_polynomial_eq_zero_of_zero_sheaf
        hRestriction.error hzero
      simp [E, hPzero]
    · right
      rcases hdim with ⟨Derror, hdim, hnonzero, hcert⟩
      rcases hcert with ⟨hcert⟩
      rcases chapter07_degree_dimension_and_leading_term
          hRestriction.error Derror hcert hnonzero with
        ⟨e, he, hdegree, hleading⟩
      have hcomp :
          ((chapter07HilbertPolynomial hRestriction.error).comp
              (Polynomial.X - Polynomial.C 1)).natDegree = Derror.dimension := by
        rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_sub_C, hdegree]
        simp
      simpa [E, hcomp] using hdim
  · apply chapter07_polynomial_eq_of_eventually_equal
    refine ⟨0, fun n _ => ?_⟩
    calc
      (chapter07FiniteDifference (chapter07HilbertPolynomial S)).eval (n : ℚ) =
          (chapter07HilbertPolynomial S).eval (n : ℚ) -
            (chapter07HilbertPolynomial S).eval ((n - 1 : ℤ) : ℚ) :=
        chapter07_finiteDifference_eval (chapter07HilbertPolynomial S) (n : ℤ)
      _ = chapter07EulerCharacteristicAtInteger S (n : ℤ) -
          chapter07EulerCharacteristicAtInteger S ((n : ℤ) - 1) := by
            rw [chapter07_hilbert_polynomial_matches_euler_at_all_integers,
              chapter07_hilbert_polynomial_matches_euler_at_all_integers]
      _ = chapter07EulerCharacteristicAtInteger R (n : ℤ) -
          chapter07EulerCharacteristicAtInteger hRestriction.error ((n : ℤ) - 1) :=
        hRestriction.eulerRelation n
      _ = (chapter07HilbertPolynomial R).eval (n : ℚ) -
          (chapter07HilbertPolynomial hRestriction.error).eval
            (((n : ℤ) - 1 : ℤ) : ℚ) := by
            rw [chapter07_hilbert_polynomial_matches_euler_at_all_integers,
              chapter07_hilbert_polynomial_matches_euler_at_all_integers]
      _ = (chapter07HilbertPolynomial R + E).eval (n : ℚ) := by
            simp [E, Polynomial.eval_add, Polynomial.eval_comp]
            push_cast
            ring

theorem chapter07_zero_dimensional_polynomial_is_total_length
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (D : Chapter07ZeroDimensionalHilbertData (k := k) (C := C)) :
    chapter07HilbertPolynomial D.setup = Polynomial.C (D.length : ℚ) := by
  exact chapter07_zero_dimensional_hilbert_polynomial D

theorem chapter07_projective_curve_hilbert_polynomial_shape
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (S : Chapter07HilbertSetup k C)
    (D : Chapter07SupportDimensionCertificate S.F)
    (hDimensionData : Chapter07HilbertPolynomialDimensionCertificate S D)
    (hcurve : D.dimension = 1)
    (hF : Chapter07NonzeroCoherentSheaf S.F) :
    ∃ e : ℕ, 0 < e ∧ ∃ c : ℚ,
      chapter07HilbertPolynomial S =
        Polynomial.C (e : ℚ) * Polynomial.X + Polynomial.C c := by
  rcases chapter07_degree_dimension_and_leading_term
      S D hDimensionData hF with ⟨e, he, hdegree, hleading⟩
  have hnat : (chapter07HilbertPolynomial S).natDegree = 1 :=
    hdegree.trans hcurve
  have hleading' : (chapter07HilbertPolynomial S).leadingCoeff = (e : ℚ) := by
    rw [hcurve] at hleading
    simpa using hleading
  have hcoeff : (chapter07HilbertPolynomial S).coeff 1 = (e : ℚ) := by
    rw [← hnat]
    simpa [Polynomial.leadingCoeff] using hleading'
  refine ⟨e, he, (chapter07HilbertPolynomial S).coeff 0, ?_⟩
  simpa [hcoeff] using
    (Polynomial.eq_X_add_C_of_natDegree_le_one hnat.le)

/-!
The union sequence is the sheaf-theoretic form of inclusion--exclusion:
`0 → 𝓞_{Y ∪ Z} → 𝓞_Y ⊕ 𝓞_Z → 𝓞_{Y ∩ Z} → 0`.
-/
structure Chapter07UnionHilbertData
    {k : Type u} [Field k]
    (C : Chapter07PolarizedScheme k) where
  union : Chapter07HilbertSetup k C
  left : Chapter07HilbertSetup k C
  right : Chapter07HilbertSetup k C
  intersection : Chapter07HilbertSetup k C
  middle : Chapter07HilbertSetup k C
  exactSequence : Chapter07ShortExactSequence union.F middle.F intersection.F
  euler_additive : ∀ n : ℕ,
    chapter07EulerCharacteristic middle n =
      chapter07EulerCharacteristic union n +
        chapter07EulerCharacteristic intersection n
  middle_euler_additive : ∀ n : ℕ,
    chapter07EulerCharacteristic middle n =
      chapter07EulerCharacteristic left n +
        chapter07EulerCharacteristic right n

theorem chapter07_union_hilbert_polynomial_inclusion_exclusion
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (D : Chapter07UnionHilbertData C) :
    chapter07HilbertPolynomial D.union =
      chapter07HilbertPolynomial D.left +
        chapter07HilbertPolynomial D.right -
          chapter07HilbertPolynomial D.intersection := by
  have hMiddleUnion := chapter07_hilbert_polynomial_additive_of_short_exact
    D.exactSequence D.euler_additive
  have hMiddleLeftRight :
      chapter07HilbertPolynomial D.middle =
        chapter07HilbertPolynomial D.left + chapter07HilbertPolynomial D.right := by
    apply chapter07_polynomial_eq_of_eventually_equal
    rcases chapter07_hilbert_polynomial_matches_euler_eventually D.left with
      ⟨NL, hNL⟩
    rcases chapter07_hilbert_polynomial_matches_euler_eventually D.middle with
      ⟨NM, hNM⟩
    rcases chapter07_hilbert_polynomial_matches_euler_eventually D.right with
      ⟨NR, hNR⟩
    refine ⟨max NL (max NM NR), fun n hn => ?_⟩
    have hL := hNL n (le_trans (Nat.le_max_left _ _) hn)
    have hM := hNM n (le_trans
      (le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn)
    have hR := hNR n (le_trans
      (le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn)
    calc
      (chapter07HilbertPolynomial D.middle).eval (n : ℚ) =
          (chapter07EulerCharacteristic D.middle n : ℚ) := hM
      _ = ((chapter07EulerCharacteristic D.left n +
          chapter07EulerCharacteristic D.right n : ℤ) : ℚ) := by
            exact_mod_cast D.middle_euler_additive n
      _ = (chapter07HilbertPolynomial D.left +
          chapter07HilbertPolynomial D.right).eval (n : ℚ) := by
            rw [Polynomial.eval_add, hL, hR]
            norm_num
  calc
    chapter07HilbertPolynomial D.union =
        (chapter07HilbertPolynomial D.union +
          chapter07HilbertPolynomial D.intersection) -
          chapter07HilbertPolynomial D.intersection := by ring
    _ = chapter07HilbertPolynomial D.middle -
        chapter07HilbertPolynomial D.intersection := by rw [← hMiddleUnion]
    _ = chapter07HilbertPolynomial D.left +
        chapter07HilbertPolynomial D.right -
          chapter07HilbertPolynomial D.intersection := by rw [hMiddleLeftRight]

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter07
