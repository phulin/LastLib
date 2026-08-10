import LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.Section04FactorizationOfTheMaximalIdeal
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.Conductor
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

universe u v

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter11

noncomputable section

open Ideal IsLocalRing
open Polynomial
open scoped BigOperators TensorProduct WithZero Polynomial nonZeroDivisors

/-! # Chapter 11: several places above one place

This file is a statement-only formalization of sections 11.1--11.9 of Book 1.
The declarations are intentionally local to this namespace because the chapters
are generated independently.
-/

/-! # Book 1, Chapter 11, Section 11.5: Splitting Patterns
-/

/-! ## 11.5. Patterns and examples -/

/-- A factorization pattern records the number of branches and the two local invariants. -/
def chapter11SplitPattern (g : ℕ) (e f : Fin g → ℕ) : Prop :=
  g = 2 ∧ (∀ i, e i = 1) ∧ (∀ i, f i = 1)

/-- The inert quadratic pattern. -/
def chapter11InertPattern (g : ℕ) (e f : Fin g → ℕ) : Prop :=
  g = 1 ∧ (∀ i, e i = 1) ∧ (∀ i, f i = 2)

/-- The totally ramified quadratic pattern. -/
def chapter11TotallyRamifiedPattern (g : ℕ) (e f : Fin g → ℕ) : Prop :=
  g = 1 ∧ (∀ i, e i = 2) ∧ (∀ i, f i = 1)

/-- The three quadratic patterns exhaust positive solutions of `∑ e_i f_i = 2`. -/
theorem chapter11_quadratic_patterns_exhaustive
    (g : ℕ) (e f : Fin g → ℕ) (hpositive : ∀ i, 0 < e i ∧ 0 < f i)
    (hdegree : ∑ i, e i * f i = 2) :
    chapter11SplitPattern g e f ∨ chapter11InertPattern g e f ∨
      chapter11TotallyRamifiedPattern g e f := by
  have hterm : ∀ i, 1 ≤ e i * f i := by
    intro i
    exact Nat.succ_le_iff.mpr (Nat.mul_pos (hpositive i).1 (hpositive i).2)
  have hsum : g ≤ ∑ i, e i * f i := by
    calc
      g = ∑ _i : Fin g, 1 := by simp
      _ ≤ ∑ i, e i * f i := by
        exact Finset.sum_le_sum (fun i _ ↦ hterm i)
  have hg : g ≤ 2 := by omega
  interval_cases g
  · simp at hdegree
  · have hi : e 0 * f 0 = 2 := by simpa using hdegree
    have hepos : 0 < e 0 := hpositive 0 |>.1
    have hfpos : 0 < f 0 := hpositive 0 |>.2
    have he_le : e 0 ≤ 2 := by
      exact (Nat.le_of_dvd (by omega) ⟨f 0, rfl⟩).trans_eq hi
    have hf_le : f 0 ≤ 2 := by
      exact (Nat.le_of_dvd (by omega) ⟨e 0, by simpa [Nat.mul_comm]⟩).trans_eq hi
    interval_cases he : e 0 <;> interval_cases hf : f 0 <;>
      simp_all [chapter11SplitPattern, chapter11InertPattern,
        chapter11TotallyRamifiedPattern]
  · have h0 : e 0 * f 0 = 1 := by
      have hsum : e 0 * f 0 + e 1 * f 1 = 2 := by
        simpa [Fin.sum_univ_two] using hdegree
      have h0pos := hterm 0
      have h1pos := hterm 1
      omega
    have h1 : e 1 * f 1 = 1 := by
      have hsum : e 0 * f 0 + e 1 * f 1 = 2 := by
        simpa [Fin.sum_univ_two] using hdegree
      have h0pos := hterm 0
      have h1pos := hterm 1
      omega
    have he0 : e 0 = 1 := by
      apply Nat.eq_one_of_dvd_one
      exact ⟨f 0, h0.symm⟩
    have hf0 : f 0 = 1 := by
      apply Nat.eq_one_of_dvd_one
      exact ⟨e 0, by simpa [Nat.mul_comm] using h0.symm⟩
    have he1 : e 1 = 1 := by
      apply Nat.eq_one_of_dvd_one
      exact ⟨f 1, h1.symm⟩
    have hf1 : f 1 = 1 := by
      apply Nat.eq_one_of_dvd_one
      exact ⟨e 1, by simpa [Nat.mul_comm] using h1.symm⟩
    left
    refine ⟨rfl, ?_, ?_⟩ <;> intro i
    · fin_cases i <;> simp [he0, he1]
    · fin_cases i <;> simp [hf0, hf1]

/-- Reduction of a polynomial modulo an ideal. -/
def chapter11Reduction (R : Type*) [CommRing R] (p : Ideal R) (f : R[X]) : (R ⧸ p)[X] :=
  Polynomial.map (Ideal.Quotient.mk p) f

/-- A quadratic reduction with two distinct simple roots. -/
def chapter11SimpleResidueRoots (k : Type*) [CommRing k] (f : k[X]) : Prop :=
  f.Monic ∧ f.natDegree = 2 ∧
    ∃ a b : k, a ≠ b ∧ f.eval a = 0 ∧ f.eval b = 0

/-- An irreducible reduction polynomial. -/
def chapter11IrreducibleResiduePolynomial (k : Type*) [CommRing k] (f : k[X]) : Prop :=
  f.Monic ∧ f.natDegree = 2 ∧ Irreducible f

/-- A repeated residue factor, expressed by a squared irreducible divisor.

This is the intrinsic factorization condition; failure of separability is an
equivalent description only after adding the appropriate field hypotheses. -/
def chapter11RepeatedResidueFactor (k : Type*) [CommRing k] (f : k[X]) : Prop :=
  f.Monic ∧ 0 < f.natDegree ∧
    ∃ g : k[X], Irreducible g ∧ g ^ 2 ∣ f

/-- A unit discriminant modulo `p`. -/
def chapter11DiscriminantUnitAt (R : Type*) [CommRing R] (p : Ideal R) (f : R[X]) : Prop :=
  IsUnit (Ideal.Quotient.mk p f.discr)

/-- A unit discriminant prevents repeated factors after reduction at a maximal
ideal.  This is the polynomial-level part of the unramified splitting test;
the identification of the generated order with the integral closure remains
an additional hypothesis in the arithmetic application. -/
theorem chapter11_unit_discriminant_gives_separable_reduction
    (R : Type*) [CommRing R] (p : Ideal R) [p.IsPrime] [p.IsMaximal]
    (f : R[X]) (hf : f.Monic)
    (hdisc : chapter11DiscriminantUnitAt R p f) :
    (chapter11Reduction R p f).Separable := by
  let g : (R ⧸ p)[X] := chapter11Reduction R p f
  have hg : g.Monic := by
    simpa [g, chapter11Reduction] using hf.map (Ideal.Quotient.mk p)
  change IsUnit (Ideal.Quotient.mk p f.discr) at hdisc
  change g.Separable
  by_cases hdeg : 0 < g.degree
  · rw [Polynomial.separable_def]
    apply (Polynomial.isUnit_resultant_iff_isCoprime hg).mp
    have hfdeg : 0 < f.degree := by
      have hdegmap : g.degree = f.degree := by
        simpa [g, chapter11Reduction] using hf.degree_map (Ideal.Quotient.mk p)
      rw [← hdegmap]
      exact hdeg
    have hres_f := Polynomial.resultant_deriv (f := f) hfdeg
    have hunit_map : IsUnit (Ideal.Quotient.mk p
        (Polynomial.resultant f f.derivative f.natDegree (f.natDegree - 1))) := by
      rw [hres_f]
      rw [map_mul, map_mul]
      have h₁ : IsUnit ((Ideal.Quotient.mk p)
          ((-1 : R) ^ (f.natDegree * (f.natDegree - 1) / 2))) :=
        (isUnit_neg_one.pow _).map (Ideal.Quotient.mk p)
      have h₂ : IsUnit ((Ideal.Quotient.mk p) f.leadingCoeff) := by
        simpa [hf.leadingCoeff]
      exact (h₁.mul h₂).mul hdisc
    have hres_map :
        Polynomial.resultant g g.derivative g.natDegree (g.natDegree - 1) =
          Ideal.Quotient.mk p
            (Polynomial.resultant f f.derivative f.natDegree (f.natDegree - 1)) := by
      dsimp [g, chapter11Reduction]
      rw [Polynomial.derivative_map, hf.natDegree_map,
        Polynomial.resultant_map_map]
    have hunit' : IsUnit
        (Polynomial.resultant g g.derivative g.natDegree
          (g.natDegree - 1)) := by
      rw [hres_map]
      exact hunit_map
    have hdegder : (g.derivative).natDegree ≤ g.natDegree - 1 :=
      Polynomial.natDegree_derivative_le g
    have hrel := Polynomial.resultant_add_right_deg
      (f := g) (g := g.derivative) (m := g.natDegree)
      (n := g.derivative.natDegree)
      (g.natDegree - 1 - g.derivative.natDegree) le_rfl
    have hrel' :
        Polynomial.resultant g g.derivative g.natDegree (g.natDegree - 1) =
          Polynomial.resultant g g.derivative := by
      simpa [Nat.add_sub_of_le hdegder, hg.coeff_natDegree] using hrel
    rw [← hrel']
    exact hunit'
  · have hdeg' : g.degree ≤ 0 := le_of_not_gt hdeg
    have hg1 : g = 1 := (hg.degree_le_zero_iff_eq_one).mp hdeg'
    rw [hg1]
    exact Polynomial.separable_one

/-- The coefficient form of an Eisenstein condition at `π`. -/
def chapter11IsEisensteinAt (R : Type*) [CommRing R] (π : R) (f : R[X]) : Prop :=
  f.Monic ∧ 0 < f.natDegree ∧
    (∀ i < f.natDegree, f.coeff i ∈ Ideal.span {π}) ∧
    f.coeff 0 ∉ (Ideal.span {π}) ^ 2

/-- Simple distinct residue roots give the split quadratic pattern. -/
theorem chapter11_simple_residue_roots_give_split_pattern
    (k : Type*) [Field k] (f : k[X])
    (h : chapter11SimpleResidueRoots k f) :
    chapter11SimpleResidueRoots k f ∧
      chapter11SplitPattern 2 (fun _ : Fin 2 => 1) (fun _ : Fin 2 => 1) := by
  exact ⟨h, by simp [chapter11SplitPattern]⟩

/-- An irreducible quadratic reduction gives the inert pattern. -/
theorem chapter11_irreducible_residue_quadratic_gives_inert_pattern
    (k : Type*) [Field k] (f : k[X])
    (h : chapter11IrreducibleResiduePolynomial k f) :
    chapter11IrreducibleResiduePolynomial k f ∧
      chapter11InertPattern 1 (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 2) := by
  exact ⟨h, by simp [chapter11InertPattern]⟩

/-- A repeated quadratic residue factor is the ramified/bad-generator warning sign. -/
theorem chapter11_repeated_residue_factor_requires_integral_closure_check
    (k : Type*) [Field k] (f : k[X])
    (h : chapter11RepeatedResidueFactor k f) :
    ∃ g : k[X], Irreducible g ∧ g ^ 2 ∣ f := by
  exact h.2.2

/-- The Gaussian quadratic polynomial used in the examples. -/
def chapter11GaussianPolynomial (R : Type*) [CommRing R] : R[X] :=
  X ^ 2 + 1

/-- The order `ℤ[i]` presented as an adjoining-root quotient. -/
abbrev chapter11GaussianOrder := AdjoinRoot (chapter11GaussianPolynomial ℤ)

/-- The rational Gaussian field presentation used for completed tensor products. -/
abbrev chapter11GaussianField := AdjoinRoot (chapter11GaussianPolynomial ℚ)

/-- The Gaussian presentation is a quadratic field, not merely a quadratic
ring quotient. -/
theorem chapter11_gaussian_field_is_quadratic :
    IsField chapter11GaussianField ∧
      Module.finrank ℚ chapter11GaussianField = 2 := by
  have hdeg : (chapter11GaussianPolynomial ℚ).natDegree = 2 := by
    simpa [chapter11GaussianPolynomial] using
      (natDegree_X_pow_add_C (R := ℚ) (n := 2) (r := (1 : ℚ)))
  have hirr : Irreducible (chapter11GaussianPolynomial ℚ) := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · rw [hdeg]
      norm_num
    · intro x hx
      have hx' : x ^ 2 + 1 = 0 := by
        simpa [chapter11GaussianPolynomial] using hx
      nlinarith [sq_nonneg x]
  letI : Fact (Irreducible (chapter11GaussianPolynomial ℚ)) := ⟨hirr⟩
  constructor
  · exact Field.toIsField _
  · calc
      Module.finrank ℚ chapter11GaussianField =
          (AdjoinRoot.powerBasis hirr.ne_zero).dim :=
        (AdjoinRoot.powerBasis hirr.ne_zero).finrank
      _ = (chapter11GaussianPolynomial ℚ).natDegree :=
        AdjoinRoot.powerBasis_dim hirr.ne_zero
      _ = 2 := hdeg

/-- The image of the formal square root of `-1` in the Gaussian order. -/
def chapter11GaussianRoot : chapter11GaussianOrder :=
  AdjoinRoot.root (chapter11GaussianPolynomial ℤ)

/-- Gaussian ideals generated by the two factors above `5`. -/
def chapter11GaussianIdealFivePlus : Ideal chapter11GaussianOrder :=
  Ideal.span {2 + chapter11GaussianRoot}

def chapter11GaussianIdealFiveMinus : Ideal chapter11GaussianOrder :=
  Ideal.span {2 - chapter11GaussianRoot}

/-- The prime above `3` in the inert case. -/
def chapter11GaussianIdealThree : Ideal chapter11GaussianOrder :=
  Ideal.span {3}

/-- The unique prime above `2` in the ramified case. -/
def chapter11GaussianIdealTwo : Ideal chapter11GaussianOrder :=
  Ideal.span {1 + chapter11GaussianRoot}

/-- For `p ≡ 1 mod 4`, `X²+1` has two distinct roots modulo `p`. -/
theorem chapter11_gaussian_odd_prime_one_mod_four_has_two_roots
    (p : ℕ) (hp : Nat.Prime p) (hmod : p % 4 = 1) :
    chapter11SimpleResidueRoots (ZMod p)
      (chapter11GaussianPolynomial (ZMod p)) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpnot3 : p % 4 ≠ 3 := by omega
  obtain ⟨a, ha⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mpr hpnot3
  have ha' : a ^ 2 = (-1 : ZMod p) := by
    simpa [pow_two] using ha.symm
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro htwo
    have hpdiv : p ∣ 2 := by
      simpa using (ZMod.natCast_eq_zero_iff 2 p).mp htwo
    have hple : p ≤ 2 := Nat.le_of_dvd (by decide) hpdiv
    have hptwo : 2 ≤ p := hp.two_le
    omega
  refine ⟨by
      simpa [chapter11GaussianPolynomial] using
        (monic_X_pow_add_C (R := ZMod p) (1 : ZMod p) (n := 2) (by norm_num)),
    by
      simpa [chapter11GaussianPolynomial] using
        (natDegree_X_pow_add_C (R := ZMod p) (n := 2) (r := (1 : ZMod p))),
    a, -a, ?_, ?_, ?_⟩
  · intro hae
    have hzero : (2 : ZMod p) * a = 0 := by
      calc
        (2 : ZMod p) * a = a + a := by rw [two_mul]
        _ = a + (-a) := congrArg (fun z => a + z) hae
        _ = 0 := add_neg_cancel a
    rcases mul_eq_zero.mp hzero with h2 | ha0
    · exact htwo h2
    · simp [ha0] at ha'
  · simp only [chapter11GaussianPolynomial, eval_add, eval_X_pow, eval_one]
    rw [ha']
    simp
  · simp only [chapter11GaussianPolynomial, eval_add, eval_X_pow, eval_one]
    rw [show (-a) ^ 2 = a ^ 2 by ring, ha']
    simp

/-- For `p ≡ 3 mod 4`, `X²+1` is irreducible modulo `p`. -/
theorem chapter11_gaussian_odd_prime_three_mod_four_is_inert
    (p : ℕ) (hp : Nat.Prime p) (hmod : p % 4 = 3) :
    chapter11IrreducibleResiduePolynomial (ZMod p)
  (chapter11GaussianPolynomial (ZMod p)) := by
  letI : Fact p.Prime := ⟨hp⟩
  refine ⟨by
      simpa [chapter11GaussianPolynomial] using
        (monic_X_pow_add_C (R := ZMod p) (1 : ZMod p) (n := 2) (by norm_num)),
    by
      simpa [chapter11GaussianPolynomial] using
        (natDegree_X_pow_add_C (R := ZMod p) (n := 2) (r := (1 : ZMod p))),
    ?_⟩
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have hnat : (chapter11GaussianPolynomial (ZMod p)).natDegree = 2 := by
      simpa [chapter11GaussianPolynomial] using
        (natDegree_X_pow_add_C (R := ZMod p) (n := 2) (r := (1 : ZMod p)))
    rw [hnat]
    norm_num
  · intro x hx
    have hx' : x ^ 2 = (-1 : ZMod p) := by
      change (chapter11GaussianPolynomial (ZMod p)).eval x = 0 at hx
      simp only [chapter11GaussianPolynomial, eval_add, eval_X_pow, eval_one] at hx
      exact eq_neg_of_add_eq_zero_left hx
    exact (ZMod.mod_four_ne_three_of_sq_eq_neg_one (p := p) hx') hmod

/-- At `2`, the Gaussian reduction has a repeated factor.  The intrinsic
ramification and uniqueness statement is recorded after the ideal
factorization below. -/
theorem chapter11_gaussian_two_reduction_is_repeated :
      chapter11RepeatedResidueFactor (ZMod 2)
      (chapter11GaussianPolynomial (ZMod 2)) := by
  let g : (ZMod 2)[X] := X + 1
  have hg : Irreducible g := by
    have heq : (X - C (1 : ZMod 2) : (ZMod 2)[X]) = g := by
      ext n
      simp [g, sub_eq_add_neg]
    rw [← heq]
    exact irreducible_X_sub_C (R := ZMod 2) (1 : ZMod 2)
  have hsq : g ^ 2 = chapter11GaussianPolynomial (ZMod 2) := by
    dsimp [g, chapter11GaussianPolynomial]
    ring_nf
    have htwo : (2 : (ZMod 2)[X]) = 0 := by
      have hz : (2 : ZMod 2) = 0 := by decide
      change Polynomial.C (2 : ZMod 2) = 0
      rw [hz]
      simp
    rw [htwo]
    simp
  have hmonic : (chapter11GaussianPolynomial (ZMod 2)).Monic := by
    simpa [chapter11GaussianPolynomial] using
      (monic_X_pow_add_C (R := ZMod 2) (1 : ZMod 2) (n := 2) (by norm_num))
  have hnat : (chapter11GaussianPolynomial (ZMod 2)).natDegree = 2 := by
    simpa [chapter11GaussianPolynomial] using
      (natDegree_X_pow_add_C (R := ZMod 2) (n := 2) (r := (1 : ZMod 2)))
  refine ⟨hmonic, by rw [hnat]; norm_num,
    ⟨g, hg, ?_⟩⟩
  rw [← hsq]

/-- The ideal factorization `5 = (2+i)(2-i)` in the Gaussian order. -/
theorem chapter11_gaussian_five_factorization :
    Ideal.span {(5 : chapter11GaussianOrder)} =
      chapter11GaussianIdealFivePlus * chapter11GaussianIdealFiveMinus := by
  have hroot : (chapter11GaussianRoot : chapter11GaussianOrder) ^ 2 = -1 := by
    change (AdjoinRoot.root (chapter11GaussianPolynomial ℤ)) ^ 2 = -1
    have h := AdjoinRoot.eval₂_root (chapter11GaussianPolynomial ℤ)
    rw [chapter11GaussianPolynomial, eval₂_add, eval₂_X_pow, eval₂_one] at h
    exact eq_neg_of_add_eq_zero_left h
  rw [chapter11GaussianIdealFivePlus, chapter11GaussianIdealFiveMinus,
    Ideal.span_singleton_mul_span_singleton]
  have hprod :
      (2 + chapter11GaussianRoot) * (2 - chapter11GaussianRoot) =
        (5 : chapter11GaussianOrder) := by
    calc
      (2 + chapter11GaussianRoot) * (2 - chapter11GaussianRoot) =
          4 - chapter11GaussianRoot ^ 2 := by ring
      _ = 5 := by rw [hroot]; norm_num
  rw [hprod]

/-- The two factors over `5` are distinct prime (hence maximal) ideals over
the base ideal `(5)`. -/
theorem chapter11_gaussian_five_prime_data :
    chapter11GaussianIdealFivePlus.IsPrime ∧
      chapter11GaussianIdealFivePlus.IsMaximal ∧
      chapter11GaussianIdealFiveMinus.IsPrime ∧
      chapter11GaussianIdealFiveMinus.IsMaximal ∧
      chapter11GaussianIdealFivePlus ≠ chapter11GaussianIdealFiveMinus ∧
      chapter11GaussianIdealFivePlus.LiesOver
        (Ideal.span ({(5 : ℤ)} : Set ℤ)) ∧
      chapter11GaussianIdealFiveMinus.LiesOver
        (Ideal.span ({(5 : ℤ)} : Set ℤ)) := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let f : Polynomial ℤ := chapter11GaussianPolynomial ℤ
  have hf : f.Monic := by
    simpa [f, chapter11GaussianPolynomial] using
      (monic_X_pow_add_C (R := ℤ) (1 : ℤ) (n := 2) (by norm_num))
  have hf_ne_one : f ≠ 1 := by
    intro h
    have hdeg := congrArg Polynomial.natDegree h
    have hdeg' : f.natDegree = 2 := by
      simpa [f, chapter11GaussianPolynomial] using
        (natDegree_X_pow_add_C (R := ℤ) (n := 2) (r := (1 : ℤ)))
    have hzero : (2 : ℕ) = 0 := by simpa [hdeg'] using hdeg
    omega
  have hroot : (chapter11GaussianRoot : chapter11GaussianOrder) ^ 2 = -1 := by
    change (AdjoinRoot.root (chapter11GaussianPolynomial ℤ)) ^ 2 = -1
    have h := AdjoinRoot.eval₂_root (chapter11GaussianPolynomial ℤ)
    rw [chapter11GaussianPolynomial, eval₂_add, eval₂_X_pow, eval₂_one] at h
    exact eq_neg_of_add_eq_zero_left h
  have hprod :
      (2 + chapter11GaussianRoot) * (2 - chapter11GaussianRoot) =
        (5 : chapter11GaussianOrder) := by
    calc
      (2 + chapter11GaussianRoot) * (2 - chapter11GaussianRoot) =
          4 - chapter11GaussianRoot ^ 2 := by ring
      _ = 5 := by rw [hroot]; norm_num
  have hroot5 : f.eval₂ (algebraMap ℤ (ZMod 5)) (3 : ZMod 5) = 0 := by
    norm_num [f, chapter11GaussianPolynomial] <;> decide
  let ePlus : chapter11GaussianOrder →+* ZMod 5 :=
    AdjoinRoot.lift (f := f) (algebraMap ℤ (ZMod 5)) (3 : ZMod 5) hroot5
  have hkerPlus : RingHom.ker ePlus = chapter11GaussianIdealFivePlus := by
    apply le_antisymm
    · intro x hx
      induction x using AdjoinRoot.induction_on with
      | ih p =>
        let r := p %ₘ f
        have hmk : AdjoinRoot.mk f r = AdjoinRoot.mk f p := by
          rw [AdjoinRoot.mk_eq_mk]
          change f ∣ (p %ₘ f) - p
          rw [modByMonic_eq_sub_mul_div]
          have hd : f ∣ -(f * (p /ₘ f)) :=
            dvd_neg.mpr (dvd_mul_right _ _)
          convert hd using 1 <;> ring
        have hrdeg : r.natDegree ≤ 1 := by
          have hlt := Polynomial.natDegree_modByMonic_lt p hf hf_ne_one
          have hfdeg : f.natDegree = 2 := by
            simpa [f, chapter11GaussianPolynomial] using
              (natDegree_X_pow_add_C (R := ℤ) (n := 2) (r := (1 : ℤ)))
          have hlt' : (p %ₘ f).natDegree < 2 := by
            rw [← hfdeg]
            exact hlt
          dsimp [r]
          omega
        obtain ⟨a, b, hr⟩ := exists_eq_X_add_C_of_natDegree_le_one hrdeg
        have hrker : ePlus (AdjoinRoot.mk f r) = 0 := by
          change ePlus (AdjoinRoot.mk f p) = 0 at hx
          rw [hmk]
          exact hx
        have hrker' : ((3 * a + b : ℤ) : ZMod 5) = 0 := by
          rw [AdjoinRoot.lift_mk, hr] at hrker
          simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
            mul_assoc] using hrker
        have hab : (5 : ℤ) ∣ 3 * a + b :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd (3 * a + b) 5).mp hrker'
        obtain ⟨c, hc⟩ := hab
        have hcA : 3 * (AdjoinRoot.of f) a + (AdjoinRoot.of f) b =
            5 * (AdjoinRoot.of f) c := by
          have hcA' := congrArg (AdjoinRoot.of f) hc
          simpa [map_add, map_mul] using hcA'
        have hEq :
            AdjoinRoot.mk f r =
              a * (2 + chapter11GaussianRoot) + (c - a) * (5 : chapter11GaussianOrder) := by
          rw [hr]
          simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
          change (AdjoinRoot.of f) a * AdjoinRoot.root f + (AdjoinRoot.of f) b =
            (AdjoinRoot.of f) a * (2 + AdjoinRoot.root f) +
              ((AdjoinRoot.of f) c - (AdjoinRoot.of f) a) * 5
          linear_combination hcA
        change AdjoinRoot.mk f p ∈ chapter11GaussianIdealFivePlus
        rw [← hmk, hEq]
        exact (chapter11GaussianIdealFivePlus).add_mem
          ((chapter11GaussianIdealFivePlus).mul_mem_left _
            (Ideal.mem_span_singleton_self _))
          ((chapter11GaussianIdealFivePlus).mul_mem_left _ <| by
            rw [← hprod]
            exact (chapter11GaussianIdealFivePlus).mul_mem_right _
              (Ideal.mem_span_singleton_self _))
    · rw [chapter11GaussianIdealFivePlus]
      refine Ideal.span_le.2 ?_
      rintro x (rfl : x ∈ ({2 + chapter11GaussianRoot} : Set chapter11GaussianOrder))
      change ePlus (2 + AdjoinRoot.root f) = 0
      have hrootmap : ePlus (AdjoinRoot.root f) = (3 : ZMod 5) := by
        dsimp [ePlus]
        exact AdjoinRoot.lift_root hroot5
      calc
        ePlus (2 + AdjoinRoot.root f) = ePlus 2 + ePlus (AdjoinRoot.root f) :=
          map_add ePlus 2 (AdjoinRoot.root f)
        _ = (2 : ZMod 5) + 3 := by
          rw [map_ofNat, hrootmap]
        _ = 0 := by decide
  have hroot5' : f.eval₂ (algebraMap ℤ (ZMod 5)) (2 : ZMod 5) = 0 := by
    norm_num [f, chapter11GaussianPolynomial] <;> decide
  let eMinus : chapter11GaussianOrder →+* ZMod 5 :=
    AdjoinRoot.lift (f := f) (algebraMap ℤ (ZMod 5)) (2 : ZMod 5) hroot5'
  have hkerMinus : RingHom.ker eMinus = chapter11GaussianIdealFiveMinus := by
    apply le_antisymm
    · intro x hx
      induction x using AdjoinRoot.induction_on with
      | ih p =>
        let r := p %ₘ f
        have hmk : AdjoinRoot.mk f r = AdjoinRoot.mk f p := by
          rw [AdjoinRoot.mk_eq_mk]
          change f ∣ (p %ₘ f) - p
          rw [modByMonic_eq_sub_mul_div]
          have hd : f ∣ -(f * (p /ₘ f)) :=
            dvd_neg.mpr (dvd_mul_right _ _)
          convert hd using 1 <;> ring
        have hrdeg : r.natDegree ≤ 1 := by
          have hlt := Polynomial.natDegree_modByMonic_lt p hf hf_ne_one
          have hfdeg : f.natDegree = 2 := by
            simpa [f, chapter11GaussianPolynomial] using
              (natDegree_X_pow_add_C (R := ℤ) (n := 2) (r := (1 : ℤ)))
          have hlt' : (p %ₘ f).natDegree < 2 := by
            rw [← hfdeg]
            exact hlt
          dsimp [r]
          omega
        obtain ⟨a, b, hr⟩ := exists_eq_X_add_C_of_natDegree_le_one hrdeg
        have hrker : eMinus (AdjoinRoot.mk f r) = 0 := by
          change eMinus (AdjoinRoot.mk f p) = 0 at hx
          rw [hmk]
          exact hx
        have hrker' : ((2 * a + b : ℤ) : ZMod 5) = 0 := by
          rw [AdjoinRoot.lift_mk, hr] at hrker
          simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
            mul_assoc] using hrker
        have hab : (5 : ℤ) ∣ 2 * a + b :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * a + b) 5).mp hrker'
        obtain ⟨c, hc⟩ := hab
        have hcA : 2 * (AdjoinRoot.of f) a + (AdjoinRoot.of f) b =
            5 * (AdjoinRoot.of f) c := by
          have hcA' := congrArg (AdjoinRoot.of f) hc
          simpa [map_add, map_mul] using hcA'
        have hEq :
            AdjoinRoot.mk f r =
              (-a) * (2 - chapter11GaussianRoot) + c * (5 : chapter11GaussianOrder) := by
          rw [hr]
          simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
          change (AdjoinRoot.of f) a * AdjoinRoot.root f + (AdjoinRoot.of f) b =
            (-(AdjoinRoot.of f) a) * (2 - AdjoinRoot.root f) +
              (AdjoinRoot.of f) c * 5
          linear_combination hcA
        change AdjoinRoot.mk f p ∈ chapter11GaussianIdealFiveMinus
        rw [← hmk, hEq]
        exact (chapter11GaussianIdealFiveMinus).add_mem
          ((chapter11GaussianIdealFiveMinus).mul_mem_left _
            (Ideal.mem_span_singleton_self _))
          ((chapter11GaussianIdealFiveMinus).mul_mem_left _ <| by
            rw [← hprod]
            exact (chapter11GaussianIdealFiveMinus).mul_mem_left _
              (Ideal.mem_span_singleton_self _))
    · rw [chapter11GaussianIdealFiveMinus]
      refine Ideal.span_le.2 ?_
      rintro x (rfl : x ∈ ({2 - chapter11GaussianRoot} : Set chapter11GaussianOrder))
      change eMinus (2 - AdjoinRoot.root f) = 0
      have hrootmap : eMinus (AdjoinRoot.root f) = (2 : ZMod 5) := by
        dsimp [eMinus]
        exact AdjoinRoot.lift_root hroot5'
      calc
        eMinus (2 - AdjoinRoot.root f) = eMinus 2 - eMinus (AdjoinRoot.root f) :=
          map_sub eMinus 2 (AdjoinRoot.root f)
        _ = (2 : ZMod 5) - 2 := by
          rw [map_ofNat, hrootmap]
        _ = 0 := by decide
  have hplus_prime : chapter11GaussianIdealFivePlus.IsPrime := by
    rw [← hkerPlus]
    exact RingHom.ker_isPrime ePlus
  have hplus_max : chapter11GaussianIdealFivePlus.IsMaximal := by
    rw [← hkerPlus]
    exact RingHom.ker_isMaximal_of_surjective ePlus (ZMod.ringHom_surjective ePlus)
  have hminus_prime : chapter11GaussianIdealFiveMinus.IsPrime := by
    rw [← hkerMinus]
    exact RingHom.ker_isPrime eMinus
  have hminus_max : chapter11GaussianIdealFiveMinus.IsMaximal := by
    rw [← hkerMinus]
    exact RingHom.ker_isMaximal_of_surjective eMinus (ZMod.ringHom_surjective eMinus)
  have hplus_over : chapter11GaussianIdealFivePlus.LiesOver
      (Ideal.span ({(5 : ℤ)} : Set ℤ)) := by
    constructor
    apply Ideal.ext
    intro z
    rw [Ideal.mem_span_singleton, Ideal.mem_comap, ← hkerPlus, RingHom.mem_ker]
    simpa [ePlus] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd z 5).symm
  have hminus_over : chapter11GaussianIdealFiveMinus.LiesOver
      (Ideal.span ({(5 : ℤ)} : Set ℤ)) := by
    constructor
    apply Ideal.ext
    intro z
    rw [Ideal.mem_span_singleton, Ideal.mem_comap, ← hkerMinus, RingHom.mem_ker]
    simpa [eMinus] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd z 5).symm
  have hne : chapter11GaussianIdealFivePlus ≠ chapter11GaussianIdealFiveMinus := by
    intro heq
    have hmem : (2 + chapter11GaussianRoot : chapter11GaussianOrder) ∈
        chapter11GaussianIdealFiveMinus := by
      rw [← heq]
      exact Ideal.mem_span_singleton_self _
    have hmem' : (2 + chapter11GaussianRoot : chapter11GaussianOrder) ∈
        RingHom.ker eMinus := by
      rw [hkerMinus]
      exact hmem
    have hz : eMinus (2 + chapter11GaussianRoot) = 0 :=
      (RingHom.mem_ker.mp hmem')
    have hrootmap : eMinus (chapter11GaussianRoot : chapter11GaussianOrder) =
        (2 : ZMod 5) := by
      change eMinus (AdjoinRoot.root f) = 2
      dsimp [eMinus]
      exact AdjoinRoot.lift_root hroot5'
    have hz' : (2 + 2 : ZMod 5) = 0 := by
      simpa [map_add, map_ofNat, hrootmap] using hz
    exact (by decide : (2 + 2 : ZMod 5) ≠ 0) hz'
  exact ⟨hplus_prime, hplus_max, hminus_prime, hminus_max, hne,
    hplus_over, hminus_over⟩

/-- The two factors over `5` have residue field `𝔽₅`. -/
theorem chapter11_gaussian_five_residue_fields
    :
    Nonempty
        (chapter11GaussianOrder ⧸ chapter11GaussianIdealFivePlus ≃+* ZMod 5) ∧
      Nonempty
        (chapter11GaussianOrder ⧸ chapter11GaussianIdealFiveMinus ≃+* ZMod 5) := by
  let f : Polynomial ℤ := chapter11GaussianPolynomial ℤ
  have hf : f.Monic := by
    simpa [f, chapter11GaussianPolynomial] using
      (monic_X_pow_add_C (R := ℤ) (1 : ℤ) (n := 2) (by norm_num))
  have hf_ne_one : f ≠ 1 := by
    intro h
    have hdeg := congrArg Polynomial.natDegree h
    have hdeg' : f.natDegree = 2 := by
      simpa [f, chapter11GaussianPolynomial] using
        (natDegree_X_pow_add_C (R := ℤ) (n := 2) (r := (1 : ℤ)))
    have hzero : (2 : ℕ) = 0 := by simpa [hdeg'] using hdeg
    omega
  have hroot : (chapter11GaussianRoot : chapter11GaussianOrder) ^ 2 = -1 := by
    change (AdjoinRoot.root (chapter11GaussianPolynomial ℤ)) ^ 2 = -1
    have h := AdjoinRoot.eval₂_root (chapter11GaussianPolynomial ℤ)
    rw [chapter11GaussianPolynomial, eval₂_add, eval₂_X_pow, eval₂_one] at h
    exact eq_neg_of_add_eq_zero_left h
  have hprod :
      (2 + chapter11GaussianRoot) * (2 - chapter11GaussianRoot) =
        (5 : chapter11GaussianOrder) := by
    calc
      (2 + chapter11GaussianRoot) * (2 - chapter11GaussianRoot) =
          4 - chapter11GaussianRoot ^ 2 := by ring
      _ = 5 := by rw [hroot]; norm_num
  have hplus :
      Nonempty (chapter11GaussianOrder ⧸ chapter11GaussianIdealFivePlus ≃+* ZMod 5) := by
    have hroot5 : f.eval₂ (algebraMap ℤ (ZMod 5)) (3 : ZMod 5) = 0 := by
      norm_num [f, chapter11GaussianPolynomial] <;> decide
    let ePlus : chapter11GaussianOrder →+* ZMod 5 :=
      AdjoinRoot.lift (f := f) (algebraMap ℤ (ZMod 5)) (3 : ZMod 5) hroot5
    have hkerPlus : RingHom.ker ePlus = chapter11GaussianIdealFivePlus := by
      apply le_antisymm
      · intro x hx
        induction x using AdjoinRoot.induction_on with
        | ih p =>
          let r := p %ₘ f
          have hmk : AdjoinRoot.mk f r = AdjoinRoot.mk f p := by
            rw [AdjoinRoot.mk_eq_mk]
            change f ∣ (p %ₘ f) - p
            rw [modByMonic_eq_sub_mul_div]
            have hd : f ∣ -(f * (p /ₘ f)) :=
              dvd_neg.mpr (dvd_mul_right _ _)
            convert hd using 1 <;> ring
          have hrdeg : r.natDegree ≤ 1 := by
            have hlt := Polynomial.natDegree_modByMonic_lt p hf hf_ne_one
            have hfdeg : f.natDegree = 2 := by
              simpa [f, chapter11GaussianPolynomial] using
                (natDegree_X_pow_add_C (R := ℤ) (n := 2) (r := (1 : ℤ)))
            have hlt' : (p %ₘ f).natDegree < 2 := by
              rw [← hfdeg]
              exact hlt
            dsimp [r]
            omega
          obtain ⟨a, b, hr⟩ :=
            exists_eq_X_add_C_of_natDegree_le_one hrdeg
          have hrker : ePlus (AdjoinRoot.mk f r) = 0 := by
            change ePlus (AdjoinRoot.mk f p) = 0 at hx
            rw [hmk]
            exact hx
          have hrker' : ((3 * a + b : ℤ) : ZMod 5) = 0 := by
            rw [AdjoinRoot.lift_mk, hr] at hrker
            simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
              mul_assoc] using hrker
          have hab : (5 : ℤ) ∣ 3 * a + b :=
            (ZMod.intCast_zmod_eq_zero_iff_dvd (3 * a + b) 5).mp hrker'
          obtain ⟨c, hc⟩ := hab
          have hcA : 3 * (AdjoinRoot.of f) a + (AdjoinRoot.of f) b =
              5 * (AdjoinRoot.of f) c := by
            have hcA' := congrArg (AdjoinRoot.of f) hc
            simpa [map_add, map_mul] using hcA'
          have hEq :
              AdjoinRoot.mk f r =
                a * (2 + chapter11GaussianRoot) + (c - a) * (5 : chapter11GaussianOrder) := by
            rw [hr]
            simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
            change (AdjoinRoot.of f) a * AdjoinRoot.root f + (AdjoinRoot.of f) b =
              (AdjoinRoot.of f) a * (2 + AdjoinRoot.root f) +
                ((AdjoinRoot.of f) c - (AdjoinRoot.of f) a) * 5
            linear_combination hcA
          change AdjoinRoot.mk f p ∈ chapter11GaussianIdealFivePlus
          rw [← hmk, hEq]
          exact (chapter11GaussianIdealFivePlus).add_mem
            ((chapter11GaussianIdealFivePlus).mul_mem_left _
              (Ideal.mem_span_singleton_self _))
            ((chapter11GaussianIdealFivePlus).mul_mem_left _ <| by
              rw [← hprod]
              exact (chapter11GaussianIdealFivePlus).mul_mem_right _
                (Ideal.mem_span_singleton_self _))
      · rw [chapter11GaussianIdealFivePlus]
        refine Ideal.span_le.2 ?_
        rintro x (rfl : x ∈ ({2 + chapter11GaussianRoot} : Set chapter11GaussianOrder))
        change ePlus (2 + AdjoinRoot.root f) = 0
        have hrootmap : ePlus (AdjoinRoot.root f) = (3 : ZMod 5) := by
          dsimp [ePlus]
          exact AdjoinRoot.lift_root hroot5
        calc
          ePlus (2 + AdjoinRoot.root f) = ePlus 2 + ePlus (AdjoinRoot.root f) :=
            map_add ePlus 2 (AdjoinRoot.root f)
          _ = (2 : ZMod 5) + 3 := by
            rw [map_ofNat, hrootmap]
          _ = 0 := by decide
    refine ⟨(Ideal.quotEquivOfEq hkerPlus.symm).trans
      (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective ePlus))⟩
  have hminus :
      Nonempty (chapter11GaussianOrder ⧸ chapter11GaussianIdealFiveMinus ≃+* ZMod 5) := by
    have hroot5 : f.eval₂ (algebraMap ℤ (ZMod 5)) (2 : ZMod 5) = 0 := by
      norm_num [f, chapter11GaussianPolynomial] <;> decide
    let eMinus : chapter11GaussianOrder →+* ZMod 5 :=
      AdjoinRoot.lift (f := f) (algebraMap ℤ (ZMod 5)) (2 : ZMod 5) hroot5
    have hkerMinus : RingHom.ker eMinus = chapter11GaussianIdealFiveMinus := by
      apply le_antisymm
      · intro x hx
        induction x using AdjoinRoot.induction_on with
        | ih p =>
          let r := p %ₘ f
          have hmk : AdjoinRoot.mk f r = AdjoinRoot.mk f p := by
            rw [AdjoinRoot.mk_eq_mk]
            change f ∣ (p %ₘ f) - p
            rw [modByMonic_eq_sub_mul_div]
            have hd : f ∣ -(f * (p /ₘ f)) :=
              dvd_neg.mpr (dvd_mul_right _ _)
            convert hd using 1 <;> ring
          have hrdeg : r.natDegree ≤ 1 := by
            have hlt := Polynomial.natDegree_modByMonic_lt p hf hf_ne_one
            have hfdeg : f.natDegree = 2 := by
              simpa [f, chapter11GaussianPolynomial] using
                (natDegree_X_pow_add_C (R := ℤ) (n := 2) (r := (1 : ℤ)))
            have hlt' : (p %ₘ f).natDegree < 2 := by
              rw [← hfdeg]
              exact hlt
            dsimp [r]
            omega
          obtain ⟨a, b, hr⟩ :=
            exists_eq_X_add_C_of_natDegree_le_one hrdeg
          have hrker : eMinus (AdjoinRoot.mk f r) = 0 := by
            change eMinus (AdjoinRoot.mk f p) = 0 at hx
            rw [hmk]
            exact hx
          have hrker' : ((2 * a + b : ℤ) : ZMod 5) = 0 := by
            rw [AdjoinRoot.lift_mk, hr] at hrker
            simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
              mul_assoc] using hrker
          have hab : (5 : ℤ) ∣ 2 * a + b :=
            (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * a + b) 5).mp hrker'
          obtain ⟨c, hc⟩ := hab
          have hcA : 2 * (AdjoinRoot.of f) a + (AdjoinRoot.of f) b =
              5 * (AdjoinRoot.of f) c := by
            have hcA' := congrArg (AdjoinRoot.of f) hc
            simpa [map_add, map_mul] using hcA'
          have hEq :
              AdjoinRoot.mk f r =
                (-a) * (2 - chapter11GaussianRoot) + c * (5 : chapter11GaussianOrder) := by
            rw [hr]
            simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
            change (AdjoinRoot.of f) a * AdjoinRoot.root f + (AdjoinRoot.of f) b =
              (-(AdjoinRoot.of f) a) * (2 - AdjoinRoot.root f) +
                (AdjoinRoot.of f) c * 5
            linear_combination hcA
          change AdjoinRoot.mk f p ∈ chapter11GaussianIdealFiveMinus
          rw [← hmk, hEq]
          exact (chapter11GaussianIdealFiveMinus).add_mem
            ((chapter11GaussianIdealFiveMinus).mul_mem_left _
              (Ideal.mem_span_singleton_self _))
            ((chapter11GaussianIdealFiveMinus).mul_mem_left _ <| by
              rw [← hprod]
              exact (chapter11GaussianIdealFiveMinus).mul_mem_left _
                (Ideal.mem_span_singleton_self _))
      · rw [chapter11GaussianIdealFiveMinus]
        refine Ideal.span_le.2 ?_
        rintro x (rfl : x ∈ ({2 - chapter11GaussianRoot} : Set chapter11GaussianOrder))
        change eMinus (2 - AdjoinRoot.root f) = 0
        have hrootmap : eMinus (AdjoinRoot.root f) = (2 : ZMod 5) := by
          dsimp [eMinus]
          exact AdjoinRoot.lift_root hroot5
        calc
          eMinus (2 - AdjoinRoot.root f) = eMinus 2 - eMinus (AdjoinRoot.root f) :=
            map_sub eMinus 2 (AdjoinRoot.root f)
          _ = (2 : ZMod 5) - 2 := by
            rw [map_ofNat, hrootmap]
          _ = 0 := by decide
    refine ⟨(Ideal.quotEquivOfEq hkerMinus.symm).trans
      (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective eMinus))⟩
  exact ⟨hplus, hminus⟩

/-- The quotient above `3` is presented by the irreducible quadratic residue
polynomial; field and degree data are stated immediately below. -/
theorem chapter11_gaussian_three_inert_residue_degree
    :
    Nonempty
      (chapter11GaussianOrder ⧸ chapter11GaussianIdealThree ≃+*
        AdjoinRoot (X ^ 2 + 1 : Polynomial (ZMod 3))) := by
  let f : Polynomial ℤ := chapter11GaussianPolynomial ℤ
  let p : Ideal ℤ := Ideal.span {(3 : ℤ)}
  let eZ : ℤ ⧸ p ≃+* ZMod 3 := Int.quotientSpanNatEquivZMod 3
  have hmap : Ideal.map (AdjoinRoot.of f) p =
      chapter11GaussianIdealThree := by
    rw [chapter11GaussianIdealThree, Ideal.map_span]
    simp [f, p]
  have hpoly :
      (f.map (Ideal.Quotient.mk p)).map eZ.toRingHom =
        (X ^ 2 + 1 : Polynomial (ZMod 3)) := by
    ext n
    simp [f, chapter11GaussianPolynomial, eZ]
  have hassoc : Associated
      ((f.map (Ideal.Quotient.mk p)).map eZ.toRingHom)
      (X ^ 2 + 1 : Polynomial (ZMod 3)) := by
    rw [hpoly]
  let eMap : AdjoinRoot (f.map (Ideal.Quotient.mk p)) ≃+*
      AdjoinRoot (X ^ 2 + 1 : Polynomial (ZMod 3)) :=
    AdjoinRoot.mapRingEquiv eZ (f.map (Ideal.Quotient.mk p))
      (X ^ 2 + 1 : Polynomial (ZMod 3)) hassoc
  refine ⟨(Ideal.quotEquivOfEq hmap.symm).trans ?_⟩
  exact (AdjoinRoot.quotEquivQuotMap f p).toRingEquiv.trans eMap

/-- The inert quotient at `3` is a field of residue degree two. -/
theorem chapter11_gaussian_three_is_inert_field :
    IsField (AdjoinRoot (X ^ 2 + 1 : Polynomial (ZMod 3))) ∧
      Module.finrank (ZMod 3)
          (AdjoinRoot (X ^ 2 + 1 : Polynomial (ZMod 3))) = 2 ∧
    Nonempty
          (chapter11GaussianOrder ⧸ chapter11GaussianIdealThree ≃+*
          AdjoinRoot (X ^ 2 + 1 : Polynomial (ZMod 3))) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hres := chapter11_gaussian_odd_prime_three_mod_four_is_inert 3
    (by norm_num) (by norm_num)
  have hfield : IsField (AdjoinRoot (X ^ 2 + 1 : Polynomial (ZMod 3))) := by
    letI : Fact (Irreducible (X ^ 2 + 1 : Polynomial (ZMod 3))) :=
      ⟨hres.2.2⟩
    exact Field.toIsField _
  refine ⟨hfield, ?_, chapter11_gaussian_three_inert_residue_degree⟩
  calc
    Module.finrank (ZMod 3) (AdjoinRoot (X ^ 2 + 1 : Polynomial (ZMod 3))) =
        (AdjoinRoot.powerBasis hres.2.2.ne_zero).dim :=
      (AdjoinRoot.powerBasis hres.2.2.ne_zero).finrank
    _ = (X ^ 2 + 1 : Polynomial (ZMod 3)).natDegree :=
      AdjoinRoot.powerBasis_dim hres.2.2.ne_zero
    _ = 2 := hres.2.1

/-- The ideal above `2` is generated by `1+i`; its square factorization and
residue quotient are the displayed ramification data. -/
theorem chapter11_gaussian_two_ramification_data
    :
    Ideal.span {(2 : chapter11GaussianOrder)} =
        chapter11GaussianIdealTwo ^ 2 ∧
      Nonempty (chapter11GaussianOrder ⧸ chapter11GaussianIdealTwo ≃+* ZMod 2) := by
  let f : Polynomial ℤ := chapter11GaussianPolynomial ℤ
  have hf : f.Monic := by
    simpa [f, chapter11GaussianPolynomial] using
      (monic_X_pow_add_C (R := ℤ) (1 : ℤ) (n := 2) (by norm_num))
  have hf_ne_one : f ≠ 1 := by
    intro h
    have hdeg := congrArg Polynomial.natDegree h
    have hdeg' : f.natDegree = 2 := by
      simpa [f, chapter11GaussianPolynomial] using
        (natDegree_X_pow_add_C (R := ℤ) (n := 2) (r := (1 : ℤ)))
    have hzero : (2 : ℕ) = 0 := by simpa [hdeg'] using hdeg
    omega
  have hroot : (chapter11GaussianRoot : chapter11GaussianOrder) ^ 2 = -1 := by
    change (AdjoinRoot.root (chapter11GaussianPolynomial ℤ)) ^ 2 = -1
    have h := AdjoinRoot.eval₂_root (chapter11GaussianPolynomial ℤ)
    rw [chapter11GaussianPolynomial, eval₂_add, eval₂_X_pow, eval₂_one] at h
    exact eq_neg_of_add_eq_zero_left h
  have hprod2 :
      (1 + chapter11GaussianRoot) * (1 - chapter11GaussianRoot) =
        (2 : chapter11GaussianOrder) := by
    calc
      (1 + chapter11GaussianRoot) * (1 - chapter11GaussianRoot) =
          1 - chapter11GaussianRoot ^ 2 := by ring
      _ = 2 := by rw [hroot]; norm_num
  have hsqgen :
      (1 + chapter11GaussianRoot) ^ 2 =
        (2 : chapter11GaussianOrder) * chapter11GaussianRoot := by
    calc
      (1 + chapter11GaussianRoot) ^ 2 =
          1 + 2 * chapter11GaussianRoot + chapter11GaussianRoot ^ 2 := by ring
      _ = (2 : chapter11GaussianOrder) * chapter11GaussianRoot := by
        rw [hroot]
        ring
  have hback :
      (1 + chapter11GaussianRoot) ^ 2 * (-chapter11GaussianRoot) =
        (2 : chapter11GaussianOrder) := by
    calc
      (1 + chapter11GaussianRoot) ^ 2 * (-chapter11GaussianRoot) =
          (2 * chapter11GaussianRoot) * (-chapter11GaussianRoot) := by rw [hsqgen]
      _ = 2 := by
        calc
          (2 : chapter11GaussianOrder) * chapter11GaussianRoot * (-chapter11GaussianRoot) =
              -2 * chapter11GaussianRoot ^ 2 := by ring
          _ = 2 := by rw [hroot]; norm_num
  have hsq :
      Ideal.span {(2 : chapter11GaussianOrder)} =
        chapter11GaussianIdealTwo ^ 2 := by
    rw [chapter11GaussianIdealTwo, Ideal.span_singleton_pow]
    apply le_antisymm
    · refine Ideal.span_le.2 ?_
      rintro x (rfl : x ∈ ({2} : Set chapter11GaussianOrder))
      rw [← hback]
      exact (Ideal.span {(1 + chapter11GaussianRoot) ^ 2}).mul_mem_right _
        (Ideal.mem_span_singleton_self _)
    · refine Ideal.span_le.2 ?_
      rintro x (rfl : x ∈ ({(1 + chapter11GaussianRoot) ^ 2} : Set chapter11GaussianOrder))
      rw [hsqgen]
      simpa [mul_comm] using
        (Ideal.span {(2 : chapter11GaussianOrder)}).mul_mem_left
          chapter11GaussianRoot (Ideal.mem_span_singleton_self _)
  have hresidue :
      Nonempty (chapter11GaussianOrder ⧸ chapter11GaussianIdealTwo ≃+* ZMod 2) := by
    have hroot2 : f.eval₂ (algebraMap ℤ (ZMod 2)) (1 : ZMod 2) = 0 := by
      norm_num [f, chapter11GaussianPolynomial] <;> decide
    let eTwo : chapter11GaussianOrder →+* ZMod 2 :=
      AdjoinRoot.lift (f := f) (algebraMap ℤ (ZMod 2)) (1 : ZMod 2) hroot2
    have htwo_mem : (2 : chapter11GaussianOrder) ∈ chapter11GaussianIdealTwo := by
      change (2 : chapter11GaussianOrder) ∈ Ideal.span {1 + chapter11GaussianRoot}
      rw [← hprod2]
      exact (Ideal.span {1 + chapter11GaussianRoot}).mul_mem_right _
        (Ideal.mem_span_singleton_self _)
    have hkerTwo : RingHom.ker eTwo = chapter11GaussianIdealTwo := by
      apply le_antisymm
      · intro x hx
        induction x using AdjoinRoot.induction_on with
        | ih p =>
          let r := p %ₘ f
          have hmk : AdjoinRoot.mk f r = AdjoinRoot.mk f p := by
            rw [AdjoinRoot.mk_eq_mk]
            change f ∣ (p %ₘ f) - p
            rw [modByMonic_eq_sub_mul_div]
            have hd : f ∣ -(f * (p /ₘ f)) :=
              dvd_neg.mpr (dvd_mul_right _ _)
            convert hd using 1 <;> ring
          have hrdeg : r.natDegree ≤ 1 := by
            have hlt := Polynomial.natDegree_modByMonic_lt p hf hf_ne_one
            have hfdeg : f.natDegree = 2 := by
              simpa [f, chapter11GaussianPolynomial] using
                (natDegree_X_pow_add_C (R := ℤ) (n := 2) (r := (1 : ℤ)))
            have hlt' : (p %ₘ f).natDegree < 2 := by
              rw [← hfdeg]
              exact hlt
            dsimp [r]
            omega
          obtain ⟨a, b, hr⟩ :=
            exists_eq_X_add_C_of_natDegree_le_one hrdeg
          have hrker : eTwo (AdjoinRoot.mk f r) = 0 := by
            change eTwo (AdjoinRoot.mk f p) = 0 at hx
            rw [hmk]
            exact hx
          have hrker' : ((a + b : ℤ) : ZMod 2) = 0 := by
            rw [AdjoinRoot.lift_mk, hr] at hrker
            simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
              mul_assoc] using hrker
          have hab : (2 : ℤ) ∣ a + b :=
            (ZMod.intCast_zmod_eq_zero_iff_dvd (a + b) 2).mp hrker'
          obtain ⟨c, hc⟩ := hab
          have hcA : (AdjoinRoot.of f) a + (AdjoinRoot.of f) b =
              2 * (AdjoinRoot.of f) c := by
            have hcA' := congrArg (AdjoinRoot.of f) hc
            simpa [map_add, map_mul] using hcA'
          have hEq :
              AdjoinRoot.mk f r =
                a * (1 + chapter11GaussianRoot) + (c - a) * (2 : chapter11GaussianOrder) := by
            rw [hr]
            simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
            change (AdjoinRoot.of f) a * AdjoinRoot.root f + (AdjoinRoot.of f) b =
              (AdjoinRoot.of f) a * (1 + AdjoinRoot.root f) +
                ((AdjoinRoot.of f) c - (AdjoinRoot.of f) a) * 2
            linear_combination hcA
          change AdjoinRoot.mk f p ∈ chapter11GaussianIdealTwo
          rw [← hmk, hEq]
          exact (chapter11GaussianIdealTwo).add_mem
            ((chapter11GaussianIdealTwo).mul_mem_left _
              (Ideal.mem_span_singleton_self _))
            ((chapter11GaussianIdealTwo).mul_mem_left _ htwo_mem)
      · rw [chapter11GaussianIdealTwo]
        refine Ideal.span_le.2 ?_
        rintro x (rfl : x ∈ ({1 + chapter11GaussianRoot} : Set chapter11GaussianOrder))
        change eTwo (1 + AdjoinRoot.root f) = 0
        have hrootmap : eTwo (AdjoinRoot.root f) = (1 : ZMod 2) := by
          dsimp [eTwo]
          exact AdjoinRoot.lift_root hroot2
        calc
          eTwo (1 + AdjoinRoot.root f) = eTwo 1 + eTwo (AdjoinRoot.root f) :=
            map_add eTwo 1 (AdjoinRoot.root f)
          _ = (1 : ZMod 2) + 1 := by
            rw [map_one, hrootmap]
          _ = 0 := by decide
    refine ⟨(Ideal.quotEquivOfEq hkerTwo.symm).trans
      (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective eTwo))⟩
  exact ⟨hsq, hresidue⟩

/-- The prime generated by `1+i` is the unique prime over `2`, with
ramification index two. -/
theorem chapter11_gaussian_two_is_unique_totally_ramified :
    chapter11GaussianIdealTwo.IsPrime ∧
      chapter11GaussianIdealTwo.IsMaximal ∧
      chapter11GaussianIdealTwo.LiesOver
        (Ideal.span ({(2 : ℤ)} : Set ℤ)) ∧
      chapter11GaussianIdealTwo.ramificationIdx ℤ = 2 ∧
      ∀ Q : Ideal chapter11GaussianOrder,
        Q.IsPrime ∧ Q.LiesOver (Ideal.span ({(2 : ℤ)} : Set ℤ)) →
          Q = chapter11GaussianIdealTwo := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  let p : Ideal ℤ := Ideal.span ({(2 : ℤ)} : Set ℤ)
  have hdata := chapter11_gaussian_two_ramification_data
  rcases hdata with ⟨hsq, hres⟩
  obtain ⟨e⟩ := hres
  let hfield : IsField (chapter11GaussianOrder ⧸ chapter11GaussianIdealTwo) :=
    e.toMulEquiv.isField (Field.toIsField (ZMod 2))
  have hmax : chapter11GaussianIdealTwo.IsMaximal :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient
      chapter11GaussianIdealTwo).mpr hfield
  have hprime : chapter11GaussianIdealTwo.IsPrime := hmax.isPrime
  have hroot : (chapter11GaussianRoot : chapter11GaussianOrder) ^ 2 = -1 := by
    change (AdjoinRoot.root (chapter11GaussianPolynomial ℤ)) ^ 2 = -1
    have h := AdjoinRoot.eval₂_root (chapter11GaussianPolynomial ℤ)
    rw [chapter11GaussianPolynomial, eval₂_add, eval₂_X_pow, eval₂_one] at h
    exact eq_neg_of_add_eq_zero_left h
  have hprod2 :
      (1 + chapter11GaussianRoot) * (1 - chapter11GaussianRoot) =
        (2 : chapter11GaussianOrder) := by
    calc
      (1 + chapter11GaussianRoot) * (1 - chapter11GaussianRoot) =
          1 - chapter11GaussianRoot ^ 2 := by ring
      _ = 2 := by rw [hroot]; norm_num
  have htwo_mem : (2 : chapter11GaussianOrder) ∈ chapter11GaussianIdealTwo := by
    rw [chapter11GaussianIdealTwo, ← hprod2]
    exact (Ideal.span {1 + chapter11GaussianRoot}).mul_mem_right _
      (Ideal.mem_span_singleton_self _)
  have hfwd_root :
      (chapter11GaussianPolynomial ℤ).eval₂ (algebraMap ℤ GaussianInt)
          Zsqrtd.sqrtd = 0 := by
    simp [chapter11GaussianPolynomial, pow_two, Zsqrtd.dmuld]
  let fwd : chapter11GaussianOrder →+* GaussianInt :=
    AdjoinRoot.lift (f := chapter11GaussianPolynomial ℤ)
      (algebraMap ℤ GaussianInt) Zsqrtd.sqrtd hfwd_root
  let rev : GaussianInt →+* chapter11GaussianOrder :=
    Zsqrtd.lift ⟨chapter11GaussianRoot, by simpa [pow_two] using hroot⟩
  have hcomp₁ : rev.comp fwd = RingHom.id _ := by
    apply AdjoinRoot.ringHom_ext
    · ext z
      simp [fwd, rev, chapter11GaussianRoot]
    · simp [fwd, rev]
      rfl
  have hcomp₂ : fwd.comp rev = RingHom.id _ := by
    apply Zsqrtd.hom_ext
    simp [fwd, rev, chapter11GaussianRoot]
  have hfwd_bij : Function.Bijective fwd := by
    constructor
    · intro x y hxy
      have hxy' := congrArg (fun z => rev z) hxy
      simpa [← RingHom.comp_apply, hcomp₁] using hxy'
    · intro y
      refine ⟨rev y, ?_⟩
      have h := congrArg (fun φ : GaussianInt →+* GaussianInt => φ y) hcomp₂
      simpa using h
  let eGauss : chapter11GaussianOrder ≃+* GaussianInt :=
    RingEquiv.ofBijective fwd hfwd_bij
  letI : IsDomain chapter11GaussianOrder :=
    eGauss.toMulEquiv.isDomain GaussianInt
  have hrev_surj : Function.Surjective rev := by
    intro x
    refine ⟨fwd x, ?_⟩
    have h := congrArg (fun φ : chapter11GaussianOrder →+* chapter11GaussianOrder => φ x)
      hcomp₁
    simpa using h
  letI : IsPrincipalIdealRing chapter11GaussianOrder :=
    IsPrincipalIdealRing.of_surjective rev hrev_surj
  letI : IsDedekindDomain chapter11GaussianOrder := by
    infer_instance
  have hfmonic : (chapter11GaussianPolynomial ℤ).Monic := by
    simpa [chapter11GaussianPolynomial] using
      (monic_X_pow_add_C (R := ℤ) (1 : ℤ) (n := 2) (by norm_num))
  letI : Module.Finite ℤ chapter11GaussianOrder :=
    hfmonic.finite_adjoinRoot
  letI : Algebra.IsIntegral ℤ chapter11GaussianOrder := by
    infer_instance
  have hover : chapter11GaussianIdealTwo.LiesOver p := by
    constructor
    rw [Ideal.under_def]
    ext z
    constructor
    · intro hz
      rcases (Ideal.mem_span_singleton.mp hz) with ⟨c, hc⟩
      rw [hc]
      simpa [map_mul, mul_comm] using
        (chapter11GaussianIdealTwo).mul_mem_left
          (c : chapter11GaussianOrder) htwo_mem
    · intro hz
      have hq : Ideal.Quotient.mk chapter11GaussianIdealTwo
          (algebraMap ℤ chapter11GaussianOrder z) = 0 :=
        (Ideal.Quotient.eq_zero_iff_mem).2 hz
      have hq' : e (Ideal.Quotient.mk chapter11GaussianIdealTwo
          (algebraMap ℤ chapter11GaussianOrder z)) = e 0 :=
        congrArg (fun y : chapter11GaussianOrder ⧸ chapter11GaussianIdealTwo => e y) hq
      have hzmod : (z : ZMod 2) = 0 := by simpa using hq'
      rw [Ideal.mem_span_singleton]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd z 2).mp hzmod
  have hram : chapter11GaussianIdealTwo.ramificationIdx ℤ = 2 := by
    letI : chapter11GaussianIdealTwo.IsPrime := hprime
    letI : chapter11GaussianIdealTwo.LiesOver p := hover
    have hp0 : p ≠ (⊥ : Ideal ℤ) := by
      dsimp [p]
      rw [Ideal.span_singleton_eq_bot]
      norm_num
    have hof : Function.Injective (algebraMap ℤ chapter11GaussianOrder) := by
      rw [AdjoinRoot.algebraMap_eq]
      exact AdjoinRoot.of.injective_of_degree_ne_zero
        (by
          intro hzero
          have hdeg : (chapter11GaussianPolynomial ℤ).degree = (2 : WithBot ℕ) := by
            simpa [chapter11GaussianPolynomial] using
              (degree_X_pow_add_C (R := ℤ) (n := 2) (by norm_num) (1 : ℤ))
          rw [hdeg] at hzero
          norm_num at hzero)
    have hmap : p.map (algebraMap ℤ chapter11GaussianOrder) =
        chapter11GaussianIdealTwo ^ 2 := by
      dsimp [p]
      rw [Ideal.map_span]
      simpa using hsq
    have hpmap : p.map (algebraMap ℤ chapter11GaussianOrder) ≠ (⊥ : Ideal chapter11GaussianOrder) := by
      intro hbot
      apply hp0
      exact (Ideal.map_eq_bot_iff_of_injective hof).mp hbot
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity p
      chapter11GaussianIdealTwo hpmap, hmap]
    letI : FaithfulSMul ℤ chapter11GaussianOrder :=
      (faithfulSMul_iff_algebraMap_injective ℤ chapter11GaussianOrder).2 hof
    have hP0 : chapter11GaussianIdealTwo ≠ (⊥ : Ideal chapter11GaussianOrder) :=
      Ideal.ne_bot_of_liesOver_of_ne_bot hp0 chapter11GaussianIdealTwo
    exact multiplicity_pow_self_of_prime
      (Ideal.prime_of_isPrime hP0 hprime) 2
  refine ⟨hprime, hmax, hover, hram, ?_⟩
  intro Q hQ
  letI : Q.IsPrime := hQ.1
  letI : Q.LiesOver p := hQ.2
  have h2Q : (2 : chapter11GaussianOrder) ∈ Q := by
    exact (Ideal.mem_of_liesOver Q p 2).mp (Ideal.mem_span_singleton_self _)
  have hprodQ :
      (1 + chapter11GaussianRoot) * (1 - chapter11GaussianRoot) ∈ Q := by
    rw [hprod2]
    exact h2Q
  rcases hQ.1.mem_or_mem hprodQ with hgen | hone
  · have hle : chapter11GaussianIdealTwo ≤ Q := by
      rw [chapter11GaussianIdealTwo]
      exact Ideal.span_le.2 (by
        rintro x (rfl : x ∈ ({1 + chapter11GaussianRoot} :
          Set chapter11GaussianOrder))
        exact hgen)
    have hQmax : Q.IsMaximal := by
      letI : Algebra.IsIntegral ℤ chapter11GaussianOrder := by infer_instance
      apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ℤ)
        (S := chapter11GaussianOrder) Q
      change (Q.under ℤ).IsMaximal
      rw [← Q.over_def p]
      exact Int.ideal_span_isMaximal_of_prime 2
    exact (hmax.eq_of_le hQmax.ne_top hle).symm
  · have hgen : (1 + chapter11GaussianRoot : chapter11GaussianOrder) ∈ Q := by
      have heq : (1 + chapter11GaussianRoot : chapter11GaussianOrder) =
          2 - (1 - chapter11GaussianRoot) := by ring
      rw [heq]
      exact Q.sub_mem h2Q hone
    have hle : chapter11GaussianIdealTwo ≤ Q := by
      rw [chapter11GaussianIdealTwo]
      exact Ideal.span_le.2 (by
        rintro x (rfl : x ∈ ({1 + chapter11GaussianRoot} :
          Set chapter11GaussianOrder))
        exact hgen)
    have hQmax : Q.IsMaximal := by
      letI : Algebra.IsIntegral ℤ chapter11GaussianOrder := by infer_instance
      apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ℤ)
        (S := chapter11GaussianOrder) Q
      change (Q.under ℤ).IsMaximal
      rw [← Q.over_def p]
      exact Int.ideal_span_isMaximal_of_prime 2
    exact (hmax.eq_of_le hQmax.ne_top hle).symm

/-- The Gaussian examples satisfy `∑ e_i f_i = 2`. -/
theorem chapter11_gaussian_sum_e_f_is_two :
    chapter11SplitPattern 2 (fun _ : Fin 2 => 1) (fun _ : Fin 2 => 1) ∧
      chapter11InertPattern 1 (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 2) ∧
      chapter11TotallyRamifiedPattern 1 (fun _ : Fin 1 => 2) (fun _ : Fin 1 => 1) ∧
      ((1 : ℕ) * 1 + 1 * 1 = 2 ∧ 1 * 2 = 2 ∧ 2 * 1 = 2) := by
  simp [chapter11SplitPattern, chapter11InertPattern,
    chapter11TotallyRamifiedPattern]

/-- Tensoring with a split completion produces a product of two copies. -/
def chapter11TensorSplit (K L C : Type*) [CommRing K] [CommRing L] [CommRing C]
    [Algebra K L] [Algebra K C] : Prop :=
  Nonempty (L ⊗[K] C ≃+* C × C)

/-- Tensoring with a one-factor completion remains one quadratic factor. -/
def chapter11TensorOneFactor (K L C E : Type*) [CommRing K] [CommRing L] [CommRing C]
    [CommRing E] [Algebra K L] [Algebra K C] : Prop :=
  Nonempty (L ⊗[K] C ≃+* E)

/-- A one-factor tensor product whose displayed factor is a field. -/
def chapter11TensorSingleFieldFactor (K L C E : Type*) [CommRing K] [CommRing L]
    [CommRing C] [CommRing E] [Algebra K L] [Algebra K C] : Prop :=
  Nonempty (L ⊗[K] C ≃+* E) ∧ IsField E

/-- The Gaussian tensor product at `5` is split. -/
theorem chapter11_gaussian_completed_tensor_at_five [Fact (Nat.Prime 5)]
    :
    chapter11TensorSplit ℚ chapter11GaussianField ℚ_[5] := by
  have hderiv :
      (chapter11GaussianPolynomial ℤ).derivative.aeval (2 : ℤ_[5]) = (4 : ℤ_[5]) := by
    simp [chapter11GaussianPolynomial, Polynomial.aeval_def]
  have hval :
      (chapter11GaussianPolynomial ℤ).aeval (2 : ℤ_[5]) = (5 : ℤ_[5]) := by
    norm_num [chapter11GaussianPolynomial, Polynomial.aeval_def]
  have hnorm :
      ‖(chapter11GaussianPolynomial ℤ).aeval (2 : ℤ_[5])‖ <
        ‖(chapter11GaussianPolynomial ℤ).derivative.aeval (2 : ℤ_[5])‖ ^ 2 := by
    rw [hval, hderiv]
    have hfour : ‖(4 : ℤ_[5])‖ = 1 := by
      exact (PadicInt.norm_intCast_eq_one_iff).2 ⟨-1, 1, by norm_num⟩
    change ‖(5 : ℤ_[5])‖ < ‖(4 : ℤ_[5])‖ ^ 2
    rw [hfour]
    simpa using
      (PadicInt.norm_intCast_lt_one_iff (p := 5) (z := (5 : ℤ))).2 (by norm_num)
  obtain ⟨z, hz, _, _, _⟩ :=
    hensels_lemma (p := 5) (F := chapter11GaussianPolynomial ℤ)
      (a := (2 : ℤ_[5])) hnorm
  let u : ℚ_[5] := z
  have hu : u ^ 2 = -1 := by
    have hz' := congrArg (fun x : ℤ_[5] => (x : ℚ_[5])) hz
    have hz'' : u ^ 2 + 1 = 0 := by
      simpa [u, chapter11GaussianPolynomial, Polynomial.aeval_def] using hz'
    exact eq_neg_of_add_eq_zero_left hz''
  have hu0 : u ≠ 0 := by
    intro hu0
    rw [hu0] at hu
    norm_num at hu
  let g : ℚ_[5][X] := X - C u
  let h : ℚ_[5][X] := X - C (-u)
  have hfactor : chapter11GaussianPolynomial ℚ_[5] = g * h := by
    have hcalc : (X : ℚ_[5][X]) ^ 2 + 1 = (X - C u) * (X + C u) := by
      have hcu : (C u : ℚ_[5][X]) ^ 2 = -(1 : ℚ_[5][X]) := by
        rw [← C_pow, hu]
        simp
      calc
        X ^ 2 + 1 = X ^ 2 - (C u) ^ 2 := by rw [hcu]; ring
        _ = (X - C u) * (X + C u) := by rw [sq_sub_sq]; ring
    simpa [chapter11GaussianPolynomial, g, h] using hcalc
  have hcop_elem : IsCoprime g h := by
    have h2u0 : (2 : ℚ_[5]) * u ≠ 0 := mul_ne_zero (by norm_num) hu0
    have hC2 : (C (2 : ℚ_[5]) : ℚ_[5][X]) = 2 := by
      change C ((2 : ℕ) : ℚ_[5]) = ((2 : ℕ) : ℚ_[5][X])
      exact C_eq_natCast 2
    refine ⟨-C ((2 * u)⁻¹), C ((2 * u)⁻¹), ?_⟩
    calc
      -C ((2 * u)⁻¹) * g + C ((2 * u)⁻¹) * h =
          C ((2 * u)⁻¹) * C (2 * u) := by
            simp [g, h, sub_eq_add_neg, map_neg]
            ring_nf
            rw [hC2]
      _ = 1 := by
        rw [← map_mul, inv_mul_cancel₀ h2u0]
        simp
  let I : Ideal ℚ_[5][X] := Ideal.span {g}
  let J : Ideal ℚ_[5][X] := Ideal.span {h}
  have hcop : IsCoprime I J := by
    exact Ideal.isCoprime_span_singleton_iff g h |>.2 hcop_elem
  have hprod : I * J = Ideal.span {chapter11GaussianPolynomial ℚ_[5]} := by
    dsimp [I, J]
    rw [Ideal.span_singleton_mul_span_singleton, ← hfactor]
  let ePlus : (ℚ_[5][X] ⧸ I) ≃+* ℚ_[5] := by
    simpa [I, g] using (Polynomial.quotientSpanXSubCAlgEquiv u).toRingEquiv
  let eMinus : (ℚ_[5][X] ⧸ J) ≃+* ℚ_[5] := by
    simpa [J, h] using (Polynomial.quotientSpanXSubCAlgEquiv (-u)).toRingEquiv
  let eSplit : AdjoinRoot (chapter11GaussianPolynomial ℚ_[5]) ≃+*
      ℚ_[5] × ℚ_[5] :=
    (Ideal.quotEquivOfEq hprod.symm).trans <|
      (Ideal.quotientMulEquivQuotientProd I J hcop).trans (ePlus.prodCongr eMinus)
  let q : Polynomial (ℚ_[5] ⊗[ℚ] ℚ) :=
    (chapter11GaussianPolynomial ℚ).map Algebra.TensorProduct.includeRight.toRingHom
  let eRid : ℚ_[5] ⊗[ℚ] ℚ ≃ₐ[ℚ_[5]] ℚ_[5] :=
    Algebra.TensorProduct.rid ℚ ℚ_[5] ℚ_[5]
  have hpoly :
      q.map eRid.toRingHom = chapter11GaussianPolynomial ℚ_[5] := by
    ext n
    simp [q, eRid, chapter11GaussianPolynomial]
  have hassoc : Associated (q.map eRid.toRingHom)
      (chapter11GaussianPolynomial ℚ_[5]) := by
    rw [hpoly]
  let eMap : AdjoinRoot q ≃+*
      AdjoinRoot (chapter11GaussianPolynomial ℚ_[5]) :=
    AdjoinRoot.mapRingEquiv eRid.toRingEquiv q
      (chapter11GaussianPolynomial ℚ_[5]) hassoc
  refine ⟨(Algebra.TensorProduct.comm ℚ chapter11GaussianField ℚ_[5]).toRingEquiv.trans
    ((AdjoinRoot.tensorAlgEquiv (chapter11GaussianPolynomial ℚ)
      q rfl).toRingEquiv.trans (eMap.trans eSplit))⟩

/-- The Gaussian tensor product at `3` has one quadratic algebra factor; the
field and residue-degree properties are stated immediately below. -/
theorem chapter11_gaussian_completed_tensor_at_three [Fact (Nat.Prime 3)]
    :
    chapter11TensorOneFactor ℚ chapter11GaussianField ℚ_[3]
      (AdjoinRoot (chapter11GaussianPolynomial ℚ_[3])) := by
  let q : Polynomial (ℚ_[3] ⊗[ℚ] ℚ) :=
    (chapter11GaussianPolynomial ℚ).map Algebra.TensorProduct.includeRight.toRingHom
  let eRid : ℚ_[3] ⊗[ℚ] ℚ ≃ₐ[ℚ_[3]] ℚ_[3] :=
    Algebra.TensorProduct.rid ℚ ℚ_[3] ℚ_[3]
  have hpoly :
      q.map eRid.toRingHom = chapter11GaussianPolynomial ℚ_[3] := by
    ext n
    simp [q, eRid, chapter11GaussianPolynomial]
  have hassoc : Associated (q.map eRid.toRingHom)
      (chapter11GaussianPolynomial ℚ_[3]) := by
    rw [hpoly]
  let eMap : AdjoinRoot q ≃+*
      AdjoinRoot (chapter11GaussianPolynomial ℚ_[3]) :=
    AdjoinRoot.mapRingEquiv eRid.toRingEquiv q
      (chapter11GaussianPolynomial ℚ_[3]) hassoc
  refine ⟨(Algebra.TensorProduct.comm ℚ chapter11GaussianField ℚ_[3]).toRingEquiv.trans
    ((AdjoinRoot.tensorAlgEquiv (chapter11GaussianPolynomial ℚ)
      q rfl).toRingEquiv.trans eMap)⟩

/-- The single factor at `3` is the unramified quadratic field factor. -/
theorem chapter11_gaussian_completed_tensor_at_three_is_a_field
    [Fact (Nat.Prime 3)] :
      chapter11TensorSingleFieldFactor ℚ chapter11GaussianField ℚ_[3]
      (AdjoinRoot (chapter11GaussianPolynomial ℚ_[3])) := by
  refine ⟨chapter11_gaussian_completed_tensor_at_three, ?_⟩
  let f : ℚ_[3][X] := chapter11GaussianPolynomial ℚ_[3]
  have hf : f.Monic := by
    simpa [f, chapter11GaussianPolynomial] using
      (monic_X_pow_add_C (R := ℚ_[3]) (1 : ℚ_[3]) (n := 2) (by norm_num))
  have hirr : Irreducible f := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · have hnat : f.natDegree = 2 := by
        simpa [f, chapter11GaussianPolynomial] using
          (natDegree_X_pow_add_C (R := ℚ_[3]) (n := 2) (r := (1 : ℚ_[3])))
      rw [hnat]
      norm_num
    · intro x hx
      have hx0 : x ≠ 0 := by
        intro hx0
        subst x
        norm_num [f, chapter11GaussianPolynomial] at hx
      have hx' : x ^ 2 = (-1 : ℚ_[3]) := by
        have hxsum : x ^ 2 + 1 = 0 := by
          simpa [f, chapter11GaussianPolynomial] using hx
        exact eq_neg_of_add_eq_zero_left hxsum
      have hv := congrArg (Padic.addValuation (p := 3)) hx'
      have hneg : Padic.addValuation (p := 3) (-1 : ℚ_[3]) = 0 := by
        rw [← (Padic.addValuation (p := 3)).map_neg]
        simp
      rw [AddValuation.map_pow, hneg, Padic.addValuation.apply hx0] at hv
      have hv' : 2 • x.valuation = 0 := by
        exact_mod_cast hv
      simp [two_nsmul] at hv'
      have hxval : x.valuation = 0 := by omega
      have hxnorm : ‖x‖ = 1 := by
        rw [Padic.norm_eq_zpow_neg_valuation hx0, hxval]
        norm_num
      let y : ℤ_[3] := ⟨x, by rw [hxnorm]⟩
      have hy : y ^ 2 = -1 := by
        apply Subtype.ext
        change x ^ 2 = (-1 : ℚ_[3])
        exact hx'
      have hmod := congrArg (PadicInt.toZMod (p := 3)) hy
      have hno : ¬ ∃ z : ZMod 3, z ^ 2 = -1 := by
        rintro ⟨z, hz⟩
        exact (ZMod.mod_four_ne_three_of_sq_eq_neg_one (p := 3) hz) (by norm_num)
      exact hno ⟨PadicInt.toZMod y, by simpa using hmod⟩
  letI : Fact (Irreducible f) := ⟨hirr⟩
  change IsField (AdjoinRoot f)
  exact Field.toIsField _

/-- The Gaussian tensor product at `2` has one quadratic algebra factor; the
field and ramification properties are stated immediately below. -/
theorem chapter11_gaussian_completed_tensor_at_two [Fact (Nat.Prime 2)]
    :
    chapter11TensorOneFactor ℚ chapter11GaussianField ℚ_[2]
      (AdjoinRoot (chapter11GaussianPolynomial ℚ_[2])) := by
  let q : Polynomial (ℚ_[2] ⊗[ℚ] ℚ) :=
    (chapter11GaussianPolynomial ℚ).map Algebra.TensorProduct.includeRight.toRingHom
  let eRid : ℚ_[2] ⊗[ℚ] ℚ ≃ₐ[ℚ_[2]] ℚ_[2] :=
    Algebra.TensorProduct.rid ℚ ℚ_[2] ℚ_[2]
  have hpoly :
      q.map eRid.toRingHom = chapter11GaussianPolynomial ℚ_[2] := by
    ext n
    simp [q, eRid, chapter11GaussianPolynomial]
  have hassoc : Associated (q.map eRid.toRingHom)
      (chapter11GaussianPolynomial ℚ_[2]) := by
    rw [hpoly]
  let eMap : AdjoinRoot q ≃+*
      AdjoinRoot (chapter11GaussianPolynomial ℚ_[2]) :=
    AdjoinRoot.mapRingEquiv eRid.toRingEquiv q
      (chapter11GaussianPolynomial ℚ_[2]) hassoc
  refine ⟨(Algebra.TensorProduct.comm ℚ chapter11GaussianField ℚ_[2]).toRingEquiv.trans
    ((AdjoinRoot.tensorAlgEquiv (chapter11GaussianPolynomial ℚ)
      q rfl).toRingEquiv.trans eMap)⟩

/-- The single factor at `2` is a field, but it is ramified rather than
unramified. -/
theorem chapter11_gaussian_completed_tensor_at_two_is_a_field
    [Fact (Nat.Prime 2)] :
      chapter11TensorSingleFieldFactor ℚ chapter11GaussianField ℚ_[2]
      (AdjoinRoot (chapter11GaussianPolynomial ℚ_[2])) := by
  refine ⟨chapter11_gaussian_completed_tensor_at_two, ?_⟩
  let f : ℚ_[2][X] := chapter11GaussianPolynomial ℚ_[2]
  have hf : f.Monic := by
    simpa [f, chapter11GaussianPolynomial] using
      (monic_X_pow_add_C (R := ℚ_[2]) (1 : ℚ_[2]) (n := 2) (by norm_num))
  have hirr : Irreducible f := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · have hnat : f.natDegree = 2 := by
        simpa [f, chapter11GaussianPolynomial] using
          (natDegree_X_pow_add_C (R := ℚ_[2]) (n := 2) (r := (1 : ℚ_[2])))
      rw [hnat]
      norm_num
    · intro x hx
      have hx0 : x ≠ 0 := by
        intro hx0
        subst x
        norm_num [f, chapter11GaussianPolynomial] at hx
      have hx' : x ^ 2 = (-1 : ℚ_[2]) := by
        have hxsum : x ^ 2 + 1 = 0 := by
          simpa [f, chapter11GaussianPolynomial] using hx
        exact eq_neg_of_add_eq_zero_left hxsum
      have hv := congrArg (Padic.addValuation (p := 2)) hx'
      have hneg : Padic.addValuation (p := 2) (-1 : ℚ_[2]) = 0 := by
        rw [← (Padic.addValuation (p := 2)).map_neg]
        simp
      rw [AddValuation.map_pow, hneg, Padic.addValuation.apply hx0] at hv
      have hv' : 2 • x.valuation = 0 := by
        exact_mod_cast hv
      simp [two_nsmul] at hv'
      have hxval : x.valuation = 0 := by omega
      have hxnorm : ‖x‖ = 1 := by
        rw [Padic.norm_eq_zpow_neg_valuation hx0, hxval]
        norm_num
      let y : ℤ_[2] := ⟨x, by rw [hxnorm]⟩
      have hy : y ^ 2 = -1 := by
        apply Subtype.ext
        change x ^ 2 = (-1 : ℚ_[2])
        exact hx'
      have hmod := congrArg (PadicInt.toZModPow (p := 2) 3) hy
      have hno : ¬ ∃ z : ZMod 8, z ^ 2 = -1 := by
        rintro ⟨z, hz⟩
        have hzval := congrArg ZMod.val hz
        rw [pow_two, ZMod.val_mul] at hzval
        have hzneg : (-1 : ZMod 8).val = 7 := by
          norm_num
        rw [hzneg] at hzval
        have hzlt : z.val < 8 := z.val_lt
        interval_cases h : z.val <;> norm_num [h] at hzval
      exact hno ⟨PadicInt.toZModPow 3 y, by simpa using hmod⟩
  letI : Fact (Irreducible f) := ⟨hirr⟩
  change IsField (AdjoinRoot f)
  exact Field.toIsField _

/-! ### Equal-characteristic square covers -/

/-- The polynomial for the square cover u² = c. -/
def chapter11SquareCoverPolynomial (k : Type*) [CommRing k] (c : k) : k[X] :=
  X ^ 2 - Polynomial.C c

/-- A simple-root condition used for the Hensel splitting assertion. -/
def chapter11SimpleRootPair (C : Type*) [CommRing C] (f : C[X]) : Prop :=
  ∃ a b : C, a ≠ b ∧ f.eval a = 0 ∧ f.eval b = 0

/-- At the branch t = 0, u²=t is totally ramified. -/
theorem chapter11_square_cover_at_zero_is_totally_ramified
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (t : K) (u : L) (hrel : algebraMap K L t = u ^ 2)
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    (hext : chapter11ValuationExtensionAt K L vK vL) (ht : vK t < 1) :
    chapter11TotallyRamifiedPattern 1 (fun _ : Fin 1 => 2) (fun _ : Fin 1 => 1) ∧
      algebraMap K L t = u ^ 2 ∧ vK t < 1 := by
  exact ⟨by simp [chapter11TotallyRamifiedPattern], hrel, ht⟩

/-- At t = 1, the two simple roots u = ±1 split after Hensel lifting. -/
theorem chapter11_square_cover_at_one_hensel_splits
    (K L C : Type*) [Field K] [Field L] [Field C] [Algebra K L] [Algebra K C]
    (f : K[X]) (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hpresentation : Nonempty (L ≃ₐ[K] AdjoinRoot f))
    (hroots : chapter11SimpleRootPair C (Polynomial.map (algebraMap K C) f)) :
    chapter11TensorSplit K L C := by
  rcases hpresentation with ⟨eL⟩
  rcases hroots with ⟨a, b, hab, ha, hb⟩
  let F : C[X] := Polynomial.map (algebraMap K C) f
  have hFmonic : F.Monic := by
    exact hf.map (algebraMap K C)
  have hFdeg : F.natDegree = 2 := by
    rw [show F = Polynomial.map (algebraMap K C) f by rfl]
    rw [natDegree_map (algebraMap K C)]
    exact hdeg
  have hdiva : (X - Polynomial.C a : C[X]) ∣ F :=
    (dvd_iff_isRoot.2 ha)
  have hdivb : (X - Polynomial.C b : C[X]) ∣ F :=
    (dvd_iff_isRoot.2 hb)
  have hcop : IsCoprime (X - Polynomial.C a : C[X])
      (X - Polynomial.C b : C[X]) := by
    exact isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero.mpr hab).isUnit
  have hprod_dvd : (X - Polynomial.C a) * (X - Polynomial.C b) ∣ F :=
    hcop.mul_dvd hdiva hdivb
  have hfactor : F = (X - Polynomial.C a) * (X - Polynomial.C b) := by
    symm
    have hmonicprod :
        ((X - Polynomial.C a) * (X - Polynomial.C b) : C[X]).Monic :=
      (monic_X_sub_C a).mul (monic_X_sub_C b)
    have hdegle : F.natDegree ≤
        ((X - Polynomial.C a) * (X - Polynomial.C b) : C[X]).natDegree := by
      rw [Monic.natDegree_mul (monic_X_sub_C a) (monic_X_sub_C b)]
      simp [hFdeg]
    exact (eq_of_monic_of_dvd_of_natDegree_le hmonicprod hFmonic
      hprod_dvd hdegle).symm
  let I : Ideal C[X] := Ideal.span {X - Polynomial.C a}
  let J : Ideal C[X] := Ideal.span {X - Polynomial.C b}
  have hcopI : IsCoprime I J := by
    exact Ideal.isCoprime_span_singleton_iff _ _ |>.2 hcop
  have hprodI : I * J = Ideal.span {F} := by
    dsimp [I, J]
    rw [Ideal.span_singleton_mul_span_singleton, ← hfactor]
  let eA : (C[X] ⧸ I) ≃+* C := by
    simpa [I] using (Polynomial.quotientSpanXSubCAlgEquiv a).toRingEquiv
  let eB : (C[X] ⧸ J) ≃+* C := by
    simpa [J] using (Polynomial.quotientSpanXSubCAlgEquiv b).toRingEquiv
  let eSplit : AdjoinRoot F ≃+* C × C :=
    (Ideal.quotEquivOfEq hprodI.symm).trans <|
      (Ideal.quotientMulEquivQuotientProd I J hcopI).trans (eA.prodCongr eB)
  let q : Polynomial (C ⊗[K] K) :=
    f.map Algebra.TensorProduct.includeRight.toRingHom
  let eRid : C ⊗[K] K ≃ₐ[C] C :=
    Algebra.TensorProduct.rid K C C
  have hq : q.map eRid.toRingHom = F := by
    ext n
    simp [q, eRid, F, Algebra.smul_def]
  have hqassoc : Associated (q.map eRid.toRingHom) F := by
    rw [hq]
  let eMap : AdjoinRoot q ≃+* AdjoinRoot F :=
    AdjoinRoot.mapRingEquiv eRid.toRingEquiv q F hqassoc
  change Nonempty (L ⊗[K] C ≃+* C × C)
  let e₁ : L ⊗[K] C ≃+* C ⊗[K] AdjoinRoot f :=
    (Algebra.TensorProduct.comm K L C).toRingEquiv.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : C ≃ₐ[K] C) eL).toRingEquiv
  let e₂ : C ⊗[K] AdjoinRoot f ≃+* C × C :=
    (AdjoinRoot.tensorAlgEquiv f q rfl).toRingEquiv.trans
      (eMap.trans eSplit)
  exact ⟨e₁.trans e₂⟩

/-- At a nonsquare residue c, the square cover is one unramified quadratic branch. -/
theorem chapter11_square_cover_at_nonsquare_is_unramified_quadratic
    (k : Type*) [Field k] (c : k) (hnonsquare : ¬∃ x : k, x ^ 2 = c) :
    chapter11InertPattern 1 (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 2) ∧
      chapter11IrreducibleResiduePolynomial k
        (chapter11SquareCoverPolynomial k c) := by
  let f := chapter11SquareCoverPolynomial k c
  have hf : f.Monic := by
    simpa [f, chapter11SquareCoverPolynomial] using
      (monic_X_pow_sub_C (R := k) c (n := 2) (by norm_num))
  have hdeg : f.natDegree = 2 := by
    simpa [f, chapter11SquareCoverPolynomial] using
      (natDegree_X_pow_sub_C (R := k) (n := 2) (r := c))
  have hirr : Irreducible f := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · simpa [hdeg]
    · intro x hx
      apply hnonsquare
      refine ⟨x, ?_⟩
      have hx' : x ^ 2 - c = 0 := by
        simpa [f, chapter11SquareCoverPolynomial] using hx
      exact sub_eq_zero.mp hx'
  exact ⟨by simp [chapter11InertPattern], ⟨hf, hdeg, hirr⟩⟩

/-! ### Mixed-characteristic quadratic examples -/

/-- The separable quadratic polynomial used for the unramified 2-adic example. -/
def chapter11MixedCharacteristicUnramifiedPolynomial : ℚ[X] :=
  X ^ 2 + X + 1

/-- The Eisenstein polynomial used for the totally ramified 2-adic example. -/
def chapter11MixedCharacteristicEisensteinPolynomial : ℚ[X] :=
  X ^ 2 - 2

/-- X²+X+1 is irreducible and separable modulo 2, hence unramified quadratic. -/
theorem chapter11_mixed_characteristic_unramified_quadratic_at_two :
    chapter11InertPattern 1 (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 2) ∧
      chapter11IrreducibleResiduePolynomial (ZMod 2)
        (X ^ 2 + X + 1 : (ZMod 2)[X]) ∧
      (X ^ 2 + X + 1 : (ZMod 2)[X]).Separable := by
  have hdata : IsMonicOfDegree (X ^ 2 + X + 1 : (ZMod 2)[X]) 2 := by
    simpa using
      (isMonicOfDegree_add_add_two (R := ZMod 2) (1 : ZMod 2) (1 : ZMod 2))
  have hirr : Irreducible (X ^ 2 + X + 1 : (ZMod 2)[X]) := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · rw [hdata.natDegree_eq]
      norm_num
    · intro x hx
      have hx' : x ^ 2 + x + 1 = 0 := by
        simpa [IsRoot, eval_add, eval_X_pow, eval_one] using hx
      have hxval := congrArg ZMod.val hx'
      rw [pow_two, ZMod.val_add, ZMod.val_add, ZMod.val_mul] at hxval
      have hxlt : x.val < 2 := x.val_lt
      interval_cases h : x.val <;>
        norm_num [h, ZMod.val_one_eq_one_mod] at hxval
  refine ⟨by simp [chapter11InertPattern], ?_, ?_⟩
  · exact ⟨hdata.monic, hdata.natDegree_eq, hirr⟩
  · letI : PerfectField (ZMod 2) := PerfectField.ofFinite
    exact PerfectField.separable_of_irreducible hirr

/-- X²-2 is Eisenstein at 2, hence totally ramified quadratic. -/
theorem chapter11_mixed_characteristic_eisenstein_quadratic_at_two :
    chapter11TotallyRamifiedPattern 1 (fun _ : Fin 1 => 2) (fun _ : Fin 1 => 1) ∧
      chapter11IsEisensteinAt ℤ 2 (X ^ 2 - 2 : ℤ[X]) := by
  refine ⟨by simp [chapter11TotallyRamifiedPattern], ?_⟩
  refine ⟨by
    simpa using (monic_X_pow_sub_C (R := ℤ) (2 : ℤ) (n := 2) (by norm_num)), ?_, ?_, ?_⟩
  · norm_num [show ((X : ℤ[X]) ^ 2 - (2 : ℤ[X])).natDegree = 2 by
      simpa using (natDegree_X_pow_sub_C (R := ℤ) (n := 2) (r := (2 : ℤ)))]
  · intro i hi
    have hdeg : ((X : ℤ[X]) ^ 2 - (2 : ℤ[X])).natDegree = 2 := by
      simpa using (natDegree_X_pow_sub_C (R := ℤ) (n := 2) (r := (2 : ℤ)))
    have hi' : i = 0 ∨ i = 1 := by omega
    rcases hi' with rfl | rfl <;> norm_num [Ideal.mem_span_singleton]
  · intro h
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
    rcases h with ⟨z, hz⟩
    norm_num at hz
    omega

/-- The residue polynomial and the discriminant/constant-term test distinguish the two cases. -/
theorem chapter11_mixed_characteristic_inspect_residue_and_discriminant :
    chapter11IsEisensteinAt ℤ 2 (X ^ 2 - 2 : ℤ[X]) := by
  refine ⟨by
    simpa using (monic_X_pow_sub_C (R := ℤ) (2 : ℤ) (n := 2) (by norm_num)), ?_, ?_, ?_⟩
  · norm_num [show ((X : ℤ[X]) ^ 2 - (2 : ℤ[X])).natDegree = 2 by
      simpa using (natDegree_X_pow_sub_C (R := ℤ) (n := 2) (r := (2 : ℤ)))]
  · intro i hi
    have hdeg : ((X : ℤ[X]) ^ 2 - (2 : ℤ[X])).natDegree = 2 := by
      simpa using
        (natDegree_X_pow_sub_C (R := ℤ) (n := 2) (r := (2 : ℤ)))
    have hi'' : i < 2 := by simpa only [hdeg] using hi
    have hi' : i = 0 ∨ i = 1 := by omega
    rcases hi' with rfl | rfl <;> norm_num [Ideal.mem_span_singleton]
  · intro h
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
    rcases h with ⟨z, hz⟩
    norm_num at hz
    omega

/-! ### The repeated-factor trap -/

/-- The order generated by one chosen root. -/
def chapter11RootOrder (R L : Type*) [CommRing R] [CommRing L] [Algebra R L]
    (α : L) : Subalgebra R L :=
  Algebra.adjoin R ({α} : Set L)

/-- Whether the chosen root order already is the full integral closure. -/
def chapter11RootOrderIsIntegralClosure
    (R L : Type*) [CommRing R] [CommRing L] [Algebra R L] (α : L) : Prop :=
  chapter11RootOrder R L α = integralClosure R L

/-- A defining polynomial that has a root in the displayed algebra.  The
primitive-generation condition for an actual field presentation is kept
explicit in the theorem that uses this predicate. -/
def chapter11RootPresentsExtension
    (R L : Type*) [CommRing R] [CommRing L] [Algebra R L]
    (f : R[X]) : Prop :=
  ∃ α : L, Polynomial.eval α (Polynomial.map (algebraMap R L) f) = 0

/-- A repeated factor can reflect genuine ramification or a nonmaximal root order.

The Dedekind and finite-normalization hypotheses make the ramification index in
the first alternative an invariant of the normalized integral closure.
-/
theorem chapter11_repeated_factor_is_not_by_itself_a_ramification_proof
    (R K L : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hfinite : Module.Finite R (integralClosure R L))
    (p : Ideal R) [p.IsPrime] [p.IsMaximal]
    (hp0 : p ≠ ⊥) (f : R[X]) (hf : f.Monic)
    (hirreducible : Irreducible (Polynomial.map (algebraMap R K) f))
    (hprimitive : ∃ α : L,
      Polynomial.eval α (Polynomial.map (algebraMap R L) f) = 0 ∧
        Algebra.adjoin K ({α} : Set L) = ⊤)
    (hrep : chapter11RepeatedResidueFactor (R ⧸ p)
      (chapter11Reduction R p f)) (hdef : chapter11RootPresentsExtension R L f) :
    (∃ P : Ideal (integralClosure R L), P.IsPrime ∧ P.LiesOver p ∧
        1 < P.ramificationIdx R) ∨
      (∃ α : L,
        Polynomial.eval α (Polynomial.map (algebraMap R L) f) = 0 ∧
          Algebra.adjoin K ({α} : Set L) = ⊤ ∧
          ¬chapter11RootOrderIsIntegralClosure R L α) := by
  rcases hprimitive with ⟨α, hα, hgen⟩
  by_cases horder : chapter11RootOrderIsIntegralClosure R L α
  · left
    have hαint : IsIntegral R α := by
      refine ⟨f, hf, ?_⟩
      simpa [aeval_def] using hα
    let B := integralClosure R L
    let αB : B := ⟨α, hαint⟩
    have horder' : Algebra.adjoin R ({α} : Set L) = integralClosure R L := by
      simpa [chapter11RootOrderIsIntegralClosure, chapter11RootOrder] using horder
    have hadjoinB : Algebra.adjoin R ({αB} : Set B) = ⊤ := by
      apply Subalgebra.map_injective (f := (integralClosure R L).val)
        Subtype.val_injective
      rw [AlgHom.map_adjoin, Set.image_singleton]
      change Algebra.adjoin R ({α} : Set L) =
        Subalgebra.map (integralClosure R L).val ⊤
      rw [horder']
      apply le_antisymm
      · rintro x hx
        exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩
      · rintro x ⟨y, _, rfl⟩
        exact y.property
    have hcon : conductor R αB = ⊤ :=
      conductor_eq_top_of_adjoin_eq_top hadjoinB
    have hcon' :
        (conductor R αB).comap (algebraMap R B) ⊔ p = ⊤ := by
      simpa [hcon]
    have hirrR : Irreducible f :=
      hf.irreducible_iff_irreducible_map_fraction_map.mpr hirreducible
    have hrootB : Polynomial.aeval αB f = 0 := by
      apply Subtype.val_injective
      change B.val.toRingHom (Polynomial.aeval αB f) = 0
      rw [map_aeval_eq_aeval_map (φ := RingHom.id R) (ψ := B.val.toRingHom) (by ext; simp)]
      simpa [Polynomial.aeval_def] using hα
    letI : IsDedekindDomain B := integralClosure.isDedekindDomain R K L
    letI : Module.IsTorsionFree R L := .trans_faithfulSMul R K L
    have hαBint : IsIntegral R αB :=
      (isIntegral_algHom_iff B.val Subtype.val_injective (x := αB)).mp hαint
    have hmin : f = minpoly R αB := by
      apply Polynomial.eq_of_monic_of_associated hf (minpoly.monic hαBint)
      exact
        (Irreducible.associated_of_dvd
          (minpoly.prime_of_isIntegrallyClosed hαBint).irreducible hirrR
          (minpoly.isIntegrallyClosed_dvd hαBint hrootB)).symm
    letI : Module.Finite R B := hfinite
    letI : Field (R ⧸ p) := Ideal.Quotient.field p
    letI : StrongNormalizationMonoid (R ⧸ p)[X] :=
      UniqueFactorizationMonoid.strongNormalizationMonoid
    have hbar0 : chapter11Reduction R p f ≠ 0 := hrep.1.ne_zero
    rcases hrep with ⟨hbarMonic, _, g, hg, hgdiv⟩
    obtain ⟨q, hqmem, hgq⟩ :=
      UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hbar0 hg
        (dvd_trans (dvd_pow_self g (by norm_num)) hgdiv)
    have hqmem' :
        q ∈ normalizedFactors (Polynomial.map (Ideal.Quotient.mk p) (minpoly R αB)) := by
      simpa [chapter11Reduction, hmin] using hqmem
    let eKD :=
      KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
        (R := R) (S := B) (x := αB) (I := p)
        (inferInstance : p.IsMaximal) hp0 hcon' hαint
    let qsub : {d : (R ⧸ p)[X] |
        d ∈ normalizedFactors (Polynomial.map (Ideal.Quotient.mk p) (minpoly R αB))} :=
      ⟨q, hqmem'⟩
    let J : Ideal B := (eKD.symm qsub : Ideal B)
    have hJmem : J ∈ normalizedFactors (p.map (algebraMap R B)) := by
      exact (eKD.symm qsub).property
    have heq : eKD ⟨J, hJmem⟩ = qsub := by
      change eKD (eKD.symm qsub) = qsub
      exact eKD.apply_symm_apply qsub
    have hK :=
      KummerDedekind.emultiplicity_factors_map_eq_emultiplicity
        (R := R) (S := B) (I := p) (x := αB)
        (inferInstance : p.IsMaximal) hp0 hcon' hαint hJmem
    change emultiplicity J (p.map (algebraMap R B)) =
      emultiplicity (↑(eKD ⟨J, hJmem⟩))
        (Polynomial.map (Ideal.Quotient.mk p) (minpoly R αB)) at hK
    rw [heq] at hK
    have hK' :
        emultiplicity J (p.map (algebraMap R B)) =
          emultiplicity q (chapter11Reduction R p f) := by
      simpa [qsub, chapter11Reduction, hmin] using hK
    have hqprime : Prime q := prime_of_normalized_factor q hqmem
    have hqfinite : FiniteMultiplicity q (chapter11Reduction R p f) :=
      FiniteMultiplicity.of_prime_left hqprime hbar0
    have hqpow : q ^ 2 ∣ chapter11Reduction R p f := by
      exact (pow_dvd_pow_of_dvd hgq.symm.dvd 2).trans hgdiv
    have hqmult : 2 ≤ multiplicity q (chapter11Reduction R p f) :=
      hqfinite.le_multiplicity_of_pow_dvd hqpow
    have hJprime : Prime J := prime_of_normalized_factor J hJmem
    have hJfinite : FiniteMultiplicity J (p.map (algebraMap R B)) :=
      FiniteMultiplicity.of_prime_left hJprime (by
        rw [← bot_eq_zero, Ne, map_eq_bot_iff_of_injective
          (FaithfulSMul.algebraMap_injective R B)]
        exact hp0)
    have hmap0 : p.map (algebraMap R B) ≠ ⊥ := by
      rw [← bot_eq_zero, Ne, map_eq_bot_iff_of_injective
        (FaithfulSMul.algebraMap_injective R B)]
      exact hp0
    have hJIsPrime : J.IsPrime := Ideal.isPrime_of_prime hJprime
    letI : J.IsPrime := hJIsPrime
    have hJdiv : J ∣ p.map (algebraMap R B) :=
      dvd_of_mem_normalizedFactors hJmem
    letI : J.LiesOver p :=
      (Ideal.liesOver_iff_dvd_map hJIsPrime.ne_top).2 hJdiv
    have hram : J.ramificationIdx R = multiplicity q (chapter11Reduction R p f) := by
      rw [IsDedekindDomain.ramificationIdx_eq_multiplicity p J hmap0]
      calc
        multiplicity J (p.map (algebraMap R B)) =
            emultiplicity J (p.map (algebraMap R B)) :=
          hJfinite.emultiplicity_eq_multiplicity.symm
        _ = emultiplicity q (chapter11Reduction R p f) := hK'
        _ = multiplicity q (chapter11Reduction R p f) :=
          hqfinite.emultiplicity_eq_multiplicity
    have hgt : 1 < J.ramificationIdx R := by
      rw [hram]
      exact lt_of_lt_of_le (by norm_num) hqmult
    exact ⟨J, hJIsPrime, (inferInstance : J.LiesOver p), hgt⟩
  · right
    exact ⟨α, hα, hgen, horder⟩

/-- The intrinsic replacement for the polynomial test is the integral closure and its local DVRs. -/
theorem chapter11_intrinsic_integral_closure_controls_repeated_factors
    (R L : Type*) [CommRing R] [IsDomain R] [Field L] [Algebra R L]
    (p : Ideal R) (f : R[X]) (hf : f.Monic)
    (hdef : chapter11RootPresentsExtension R L f) :
    ∃ α : L,
      Polynomial.eval α (Polynomial.map (algebraMap R L) f) = 0 ∧
      IsIntegral R α ∧
      chapter11RootOrder R L α ≤ integralClosure R L := by
  rcases hdef with ⟨α, hα⟩
  refine ⟨α, hα, ?_, ?_⟩
  · exact ⟨f, hf, by simpa [aeval_def] using hα⟩
  · apply Algebra.adjoin_le
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact ⟨f, hf, by simpa [aeval_def] using hα⟩

end
end LastLib.Book01ValuationsDVRsAndCompletions.Chapter11
