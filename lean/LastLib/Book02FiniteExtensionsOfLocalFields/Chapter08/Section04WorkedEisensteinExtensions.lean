import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.Section03UniformizersAndMinimalPolynomials
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter03

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08

noncomputable section

open Polynomial
open scoped WithTop

/-! # 8.4. Worked Eisenstein extensions -/

/-- The radical polynomial `T^n - a` used in the examples. -/
def chapter08RadicalPolynomial
    {R : Type*} [CommRing R] (a : R) (n : ℕ) : R[X] :=
  X ^ n - C a

/-- Book §8.4: `T^n - π` is Eisenstein at a generator of the maximal ideal
of a DVR. -/
theorem chapter08_radical_polynomial_is_eisenstein
    {A : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    (π : A) (hπ : IsLocalRing.maximalIdeal A = Ideal.span ({π} : Set A))
    (n : ℕ) (hn : 0 < n) :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt π
      (chapter08RadicalPolynomial π n) := by
  unfold LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt
    chapter08RadicalPolynomial
  refine ⟨monic_X_pow_sub_C π hn.ne', ?_, ?_, ?_, hπ.symm⟩
  · rw [natDegree_X_pow_sub_C]
    exact hn
  · intro i hi
    have hi' : i < n := by simpa [natDegree_X_pow_sub_C] using hi
    by_cases hi0 : i = 0
    · subst i
      simp [coeff_sub, coeff_X_pow, hn.ne', eq_comm, Ideal.mem_span_singleton]
    · rw [coeff_sub]
      simp [coeff_C, Nat.ne_of_lt hi', hi0, Ideal.mem_span_singleton]
  · have hπ0 : π ≠ 0 := by
      intro hzero
      have hbot : IsLocalRing.maximalIdeal A = (⊥ : Ideal A) := by
        rw [hπ, hzero]
        simp
      exact IsDiscreteValuationRing.not_a_field A hbot
    have hirr : Irreducible π :=
      IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal π hπ0 hπ
    intro hmem
    have hmem' : -π ∈ Ideal.span ({π ^ 2} : Set A) := by
      simpa [coeff_zero_eq_eval_zero, eval_sub, eval_pow, eval_X, eval_C,
        hn.ne'] using hmem
    have hdiv : π ^ 2 ∣ -π := (Ideal.mem_span_singleton.mp hmem')
    rcases hdiv with ⟨c, hc⟩
    have hcancel : -1 = π * c := by
      apply (mul_left_cancel₀ hπ0)
      simpa [pow_two, mul_assoc] using hc
    have hunit : IsUnit π := by
      apply isUnit_of_dvd_one
      refine ⟨-c, ?_⟩
      simpa [mul_neg] using congrArg Neg.neg hcancel
    exact hirr.not_isUnit hunit

/-- The integral model of `T^n-p` over the p-adic integers. -/
def chapter08PadicIntegralRadicalPolynomial
    (p n : ℕ) [Fact p.Prime] : (ℤ_[p])[X] :=
  chapter08RadicalPolynomial (p : ℤ_[p]) n

/-- The same p-adic polynomial after mapping its coefficients to `ℚ_[p]`. -/
def chapter08PadicRadicalPolynomial
    (p n : ℕ) [Fact p.Prime] : (ℚ_[p])[X] :=
  (chapter08PadicIntegralRadicalPolynomial p n).map (algebraMap (ℤ_[p]) (ℚ_[p]))

/-- Book §8.4: for every prime `p` and positive `n`, `T^n-p` is Eisenstein
over `ℤ_[p]`, including the wild case `p ∣ n`. -/
theorem chapter08_padic_radical_polynomial_is_eisenstein
    (p n : ℕ) [Fact p.Prime] (hn : 0 < n) :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt (p : ℤ_[p])
      (chapter08PadicIntegralRadicalPolynomial p n) := by
  simpa [chapter08PadicIntegralRadicalPolynomial] using
    (chapter08_radical_polynomial_is_eisenstein
      (A := ℤ_[p]) (p : ℤ_[p]) PadicInt.maximalIdeal_eq_span_p n hn)

/-- Book §8.4: adjoining a root of `T^n-p` gives the stated totally ramified
p-adic profile and the generated integral ring. -/
theorem chapter08_padic_radical_extension
    (p n : ℕ) [Fact p.Prime] (hn : 0 < n)
    {L : Type*} [Field L]
    [Algebra (ℚ_[p]) L] [FiniteDimensional (ℚ_[p]) L]
    [Algebra (ℤ_[p]) L]
    [IsScalarTower (ℤ_[p]) (ℚ_[p]) L]
    (α : L)
    (hroot : aeval α (chapter08PadicRadicalPolynomial p n) = 0)
    (hgen : Algebra.adjoin (ℚ_[p]) ({α} : Set L) = ⊤)
    (hdegree : Module.finrank (ℚ_[p]) L = n) :
    ∃ q : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10FiniteExtensionProfile,
      q.degree = n ∧ q.ramificationIndex = n ∧ q.residueDegree = 1 ∧
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10TotallyRamified q ∧
        (integralClosure (ℤ_[p]) L : Set L) =
          (Algebra.adjoin (ℤ_[p]) ({α} : Set L) : Set L) := by
  let q : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10FiniteExtensionProfile :=
    { degree := n, ramificationIndex := n, residueDegree := 1 }
  have hroot' :
      aeval α (chapter08PadicIntegralRadicalPolynomial p n) = 0 := by
    simpa [chapter08PadicRadicalPolynomial] using hroot
  have hdegree' :
      (chapter08PadicIntegralRadicalPolynomial p n).natDegree = n := by
    rw [chapter08PadicIntegralRadicalPolynomial, chapter08RadicalPolynomial,
      natDegree_X_pow_sub_C]
  have hclosure :
      (integralClosure (ℤ_[p]) L : Set L) =
        (Algebra.adjoin (ℤ_[p]) ({α} : Set L) : Set L) :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.eisenstein_integral_closure_is_root_order
      (p : ℤ_[p]) (chapter08PadicIntegralRadicalPolynomial p n) α
      (chapter08_padic_radical_polynomial_is_eisenstein p n hn)
      hroot' hdegree' hgen
  exact ⟨q, rfl, rfl, rfl, rfl, hclosure⟩

/-- The equal-characteristic radical polynomial over `k((t))`. -/
def chapter08LaurentRadicalPolynomial
    (k : Type*) [Field k] (n : ℕ) : (LaurentSeries k)[X] :=
  chapter08RadicalPolynomial
    (LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.laurentSeriesUniformizer k) n

/-- A radical polynomial with exponent prime to the characteristic is
separable, provided its constant term is nonzero. -/
theorem chapter08_radical_polynomial_separable_of_coprime_exponent
    {K : Type*} [Field K] (a : K) (p n : ℕ)
    [Fact p.Prime] [CharP K p]
    (ha : a ≠ 0) (hcoprime : Nat.Coprime n p) :
    (chapter08RadicalPolynomial a n).Separable := by
  have hpn : ¬p ∣ n := by
    exact ((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp hcoprime.symm)
  simpa [chapter08RadicalPolynomial] using
    (separable_X_pow_sub_C' p n a hpn ha)

/-- In characteristic `p`, the derivative of `T^p-a` vanishes. -/
theorem chapter08_char_p_radical_derivative_zero
    {K : Type*} [Field K] (a : K) (p : ℕ) [CharP K p] :
    (chapter08RadicalPolynomial a p).derivative = 0 := by
  rw [show chapter08RadicalPolynomial a p = X ^ p - C a by rfl]
  simp [Polynomial.derivative_sub, Polynomial.derivative_pow, CharP.cast_eq_zero K p]

/-- Book §8.4: in equal characteristic `p`, the exponent-`p` radical is the
purely inseparable endpoint, while the valuation-theoretic profile remains
the same as in the separable Eisenstein examples. -/
theorem chapter08_laurent_radical_purely_inseparable_profile
    {k L : Type*} [Field k] [Field L]
    [Algebra (LaurentSeries k) L] [FiniteDimensional (LaurentSeries k) L]
    [IsPurelyInseparable (LaurentSeries k) L]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (α : L)
    (hroot : aeval α (chapter08LaurentRadicalPolynomial k p) = 0)
    (hgen : Algebra.adjoin (LaurentSeries k) ({α} : Set L) = ⊤)
    (hdegree : Module.finrank (LaurentSeries k) L = p)
    (vK : AddValuation (LaurentSeries k) (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hval : vK.IsEquiv
      (AddValuation.comap (algebraMap (LaurentSeries k) L) vL))
    (e : ℕ)
    (he_lower : p ≤ e)
    (hfundamental : Module.finrank (LaurentSeries k) L =
      e * LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
        vK vL hval) :
    e = p ∧ chapter08TotallyRamified vK vL hval := by
  let residueDegree :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
      vK vL hval
  have hfundamental' : p = e * residueDegree := by
    calc
      p = Module.finrank (LaurentSeries k) L := hdegree.symm
      _ = e * residueDegree := hfundamental
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have hresidue_pos : 0 < residueDegree := by
    by_contra hnot
    have hresidue_zero : residueDegree = 0 := Nat.eq_zero_of_not_pos hnot
    have hp_zero : p = 0 := by simpa [hresidue_zero] using hfundamental'
    exact (Fact.out : Nat.Prime p).ne_zero hp_zero
  have he_pos : 0 < e := by
    have hprod_pos : 0 < e * residueDegree := by
      simpa [hfundamental'] using hp_pos
    have he_ne : e ≠ 0 := by
      intro he_zero
      simp [he_zero] at hprod_pos
    exact Nat.pos_of_ne_zero he_ne
  have hprod_le : e * residueDegree ≤ e := by
    calc
      e * residueDegree = p := hfundamental'.symm
      _ ≤ e := he_lower
  have hresidue_one : residueDegree = 1 := by
    apply le_antisymm
    · by_contra hnot
      have htwo : 2 ≤ residueDegree := by omega
      have hlt : e < e * residueDegree := by
        calc
          e = e * 1 := (Nat.mul_one e).symm
          _ < e * 2 := (Nat.mul_lt_mul_left he_pos).2 (by omega)
          _ ≤ e * residueDegree := Nat.mul_le_mul_left e htwo
      exact (Nat.not_lt_of_ge hprod_le) hlt
    · exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hresidue_pos)
  refine ⟨?_, ?_⟩
  · simpa [hresidue_one] using hfundamental'.symm
  · exact hresidue_one

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08
