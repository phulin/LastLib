import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12.Section05Conclusion
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.Section05MixedAndEqualCharacteristic

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12

noncomputable section

open Polynomial

/-! ## 12.6. What separability is doing -/

/-- In positive characteristic the derivative of `T^p-a` vanishes. -/
theorem chapter12_pth_power_derivative_zero
    {K : Type*} [Field K] (p : ℕ) (hp : Nat.Prime p) [CharP K p]
    (a : K) :
    (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03PurelyInseparableResiduePolynomial
      K p a).derivative = 0 := by
  simp [LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03PurelyInseparableResiduePolynomial,
    Polynomial.derivative_sub, Polynomial.derivative_pow, hp.ne_zero]

private theorem chapter12_sub_pow_of_charP
    {R : Type*} [CommRing R] (p : ℕ) (hp : Nat.Prime p) [CharP R p]
    (x y : R) : (x - y) ^ p = x ^ p - y ^ p := by
  rw [sub_pow]
  let s : Finset ℕ := Finset.range (p + 1)
  let t : ℕ → R := fun m =>
    (-1 : R) ^ (m + p) * x ^ m * y ^ (p - m) * (p.choose m : R)
  have h0 : 0 ∈ s := by
    simp [s]
  rw [show (∑ m ∈ s, t m) = _ by rfl]
  rw [← Finset.add_sum_erase s t h0]
  have hp_mem : p ∈ s.erase 0 := by
    simp [s, hp.ne_zero]
  rw [← Finset.add_sum_erase (s.erase 0) t hp_mem]
  have hinterior : ∑ m ∈ (s.erase 0).erase p, t m = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    rcases Finset.mem_erase.mp hm with ⟨hmp, hm0mem⟩
    rcases Finset.mem_erase.mp hm0mem with ⟨hm0, hmS⟩
    have hdiv : p ∣ p.choose m := by
      simpa using (hp.dvd_choose_pow (n := 1) hm0 (by simpa using hmp))
    rcases hdiv with ⟨q, hq⟩
    have hcast : (p.choose m : R) = 0 := by
      rw [hq, Nat.cast_mul, CharP.cast_eq_zero R p, zero_mul]
    rw [show t m =
        (-1 : R) ^ (m + p) * x ^ m * y ^ (p - m) * (p.choose m : R) by rfl]
    rw [hcast, mul_zero]
  rw [hinterior]
  have hsign : (-1 : R) ^ p = -1 := by
    rcases hp.eq_two_or_odd' with rfl | hpodd
    · have htwo : (2 : R) = 0 := CharP.cast_eq_zero R 2
      have hneg : (-1 : R) = 1 := by
        apply sub_eq_zero.mp
        calc
          (-1 : R) - 1 = -(2 : R) := by ring
          _ = 0 := by rw [htwo, neg_zero]
      calc
        (-1 : R) ^ 2 = 1 := by simp
        _ = -1 := hneg.symm
    · exact Odd.neg_one_pow hpodd
  simp [t]
  rw [hsign]
  have hadd : -(y ^ p) + x ^ p = x ^ p + -(y ^ p) :=
    add_comm (-(y ^ p)) (x ^ p)
  simpa only [neg_one_mul, sub_eq_add_neg] using hadd

/-- Over a field of characteristic `p`, a chosen root of `T^p-a` is its only
geometric root and the polynomial has multiplicity `p` there. -/
theorem chapter12_pth_power_has_one_geometric_root
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (p : ℕ) (hp : Nat.Prime p) [CharP K p] [CharP L p]
    (a : K) (α : L)
    (hroot : aeval α
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03PurelyInseparableResiduePolynomial
        K p a) = 0) :
    Polynomial.map (algebraMap K L)
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03PurelyInseparableResiduePolynomial
          K p a) =
        ((X : L[X]) - C α) ^ p ∧
    ∀ β : L,
        aeval β
          (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03PurelyInseparableResiduePolynomial
            K p a) = 0 → β = α := by
  classical
  have hαpow : α ^ p = algebraMap K L a := by
    have h := hroot
    simp [LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03PurelyInseparableResiduePolynomial] at h
    exact sub_eq_zero.mp h
  constructor
  · simp only [LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03PurelyInseparableResiduePolynomial,
      Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    rw [chapter12_sub_pow_of_charP p hp X (C α)]
    rw [← hαpow]
    simp only [map_pow]
  · intro β hβ
    have hβpow : β ^ p = algebraMap K L a := by
      have h := hβ
      simp [LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03PurelyInseparableResiduePolynomial] at h
      exact sub_eq_zero.mp h
    have hdiff : (β - α) ^ p = 0 := by
      rw [chapter12_sub_pow_of_charP p hp β α, hβpow, hαpow, sub_self]
    have hzero : β - α = 0 := by
      exact eq_zero_of_pow_eq_zero hdiff
    exact sub_eq_zero.mp hzero

/- A nonzero linear coefficient can be made arbitrarily small.  Adding it to
the inseparable equation gives a separable nearby polynomial. -/
theorem chapter12_pth_power_coefficients_can_be_perturbed
    {K : Type*} [NontriviallyNormedField K] (p : ℕ) (hp : Nat.Prime p)
    [CharP K p] (a : K) :
    ∀ ε : ℝ, 0 < ε →
      ∃ c : K, c ≠ 0 ∧ ‖c‖ < ε ∧
        (X : K[X]) ^ p + C c * X - C a ≠
          LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03PurelyInseparableResiduePolynomial
            K p a ∧
        ((X : K[X]) ^ p + C c * X - C a).Separable := by
  intro ε hε
  obtain ⟨c, hcpos, hcε⟩ := NormedField.exists_norm_lt K hε
  have hc : c ≠ 0 := norm_pos_iff.mp hcpos
  refine ⟨c, hc, hcε, ?_, ?_⟩
  · intro h
    have hcoeff := congrArg (fun q : K[X] => q.coeff 1) h
    have hc0 : c = 0 := by
      simpa [LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03PurelyInseparableResiduePolynomial,
        Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
        Polynomial.coeff_C_mul_X, Polynomial.coeff_C, hp.ne_one] using hcoeff
    exact hc hc0
  · have hunit : IsUnit c := isUnit_iff_ne_zero.mpr hc
    have hsep :=
      Polynomial.separable_C_mul_X_pow_add_C_mul_X_add_C'
        p p (1 : K) c (-a) (dvd_refl p) hunit
    simpa [sub_eq_add_neg] using hsep

/-- Every finite extension of a characteristic-zero field is separable. -/
theorem chapter12_characteristic_zero_finite_extensions_are_separable
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [CharZero K] :
    Algebra.IsSeparable K L := by
  infer_instance

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12
