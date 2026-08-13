import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03.Dependencies
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03.Section03LogarithmicDerivatives
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03

noncomputable section

open NumberField IsDedekindDomain
open scoped BigOperators nonZeroDivisors

/-! ### 3.4 Prime powers and positivity -/

private theorem chapter03_gaussian_primitive_root
    (K : Type*) [Field K] [NumberField K] {ι : K}
    (hιsq : ι ^ 2 = -1) :
    IsPrimitiveRoot ι 4 := by
  have hιpow4 : ι ^ 4 = 1 := by
    calc
      ι ^ 4 = (ι ^ 2) ^ 2 := by ring
      _ = (-1 : K) ^ 2 := by rw [hιsq]
      _ = 1 := by ring
  have hιpow1 : ι ^ 1 ≠ (1 : K) := by
    intro h
    have hι : ι = 1 := by simpa using h
    rw [hι] at hιsq
    norm_num at hιsq
  have hιpow2 : ι ^ 2 ≠ (1 : K) := by
    rw [hιsq]
    norm_num
  have hιpow3 : ι ^ 3 ≠ (1 : K) := by
    intro h
    have hneg : -ι = (1 : K) := by
      calc
        -ι = ι ^ 3 := by rw [show (3 : ℕ) = 1 + 2 by norm_num, pow_add, hιsq]; ring
        _ = 1 := h
    have hι : ι = -1 := by
      calc
        ι = -(-ι) := by ring
        _ = -1 := by rw [hneg]
    rw [hι] at hιsq
    norm_num at hιsq
  apply IsPrimitiveRoot.mk_of_lt ι (by norm_num) hιpow4
  intro l hl₁ hl₄
  interval_cases l
  · exact hιpow1
  · exact hιpow2
  · exact hιpow3

private theorem chapter03_isCyclotomic_of_gaussian
    (K : Type*) [Field K] [NumberField K] {ι : K}
    (hιsq : ι ^ 2 = -1) (hgen : Algebra.adjoin ℚ {ι} = ⊤) :
    IsCyclotomicExtension {4} ℚ K := by
  have hι := chapter03_gaussian_primitive_root K hιsq
  have hcycl_top : IsCyclotomicExtension {4} ℚ (⊤ : Subalgebra ℚ K) := by
    exact (isCyclotomicExtension_singleton_iff_eq_adjoin (n := 4)
      (⊤ : Subalgebra ℚ K) hι).2
      hgen.symm
  exact IsCyclotomicExtension.equiv (S := {4}) (A := ℚ)
    (B := (⊤ : Subalgebra ℚ K)) (C := K) (h := hcycl_top) Subalgebra.topEquiv

theorem chapter03_prime_ideal_norm_ge_two
    (K : Type*) [Field K] [NumberField K] (P : Chapter03PrimeIdeal K) :
    2 ≤ chapter03PrimeIdealNorm P := by
  have h := chapter03_prime_ideal_norm_gt_one P
  omega

theorem chapter03_prime_ideal_log_norm_pos
    (K : Type*) [Field K] [NumberField K] (P : Chapter03PrimeIdeal K) :
    0 < Real.log (chapter03PrimeIdealNorm P : ℝ) := by
  apply Real.log_pos
  exact_mod_cast chapter03_prime_ideal_norm_gt_one P

theorem chapter03_weighted_prime_power_term_nonneg
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : ∀ x, 0 ≤ F x) (q : Chapter03PrimePower K) :
    0 ≤ chapter03WeightedPrimePowerTerm F q := by
  unfold chapter03WeightedPrimePowerTerm
  exact mul_nonneg (le_of_lt (chapter03_prime_ideal_log_norm_pos K q.1)) (hF _)

theorem chapter03_weighted_prime_power_sum_nonneg
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : ∀ x, 0 ≤ F x) (S : Finset (Chapter03PrimePower K)) :
    0 ≤ ∑ q ∈ S, chapter03WeightedPrimePowerTerm F q := by
  exact Finset.sum_nonneg fun q hq =>
    chapter03_weighted_prime_power_term_nonneg K hF q

theorem chapter03_weighted_prime_power_tsum_nonneg
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : ∀ x, 0 ≤ F x)
    (hsum : Summable (fun q : Chapter03PrimePower K =>
      chapter03WeightedPrimePowerTerm F q)) :
    0 ≤ ∑' q : Chapter03PrimePower K, chapter03WeightedPrimePowerTerm F q := by
  have _hsum := hsum
  exact tsum_nonneg fun q => chapter03_weighted_prime_power_term_nonneg K hF q

theorem chapter03_weighted_prime_power_sum_mono
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : ∀ x, 0 ≤ F x) {S T : Finset (Chapter03PrimePower K)}
    (hST : S ⊆ T) :
    (∑ q ∈ S, chapter03WeightedPrimePowerTerm F q) ≤
      ∑ q ∈ T, chapter03WeightedPrimePowerTerm F q := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hST fun q hq hqS =>
    chapter03_weighted_prime_power_term_nonneg K hF q

theorem chapter03_weighted_prime_power_partial_sum_le_full
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : ∀ x, 0 ≤ F x) (S : Finset (Chapter03PrimePower K))
    (hsum : Summable (fun q : Chapter03PrimePower K =>
      chapter03WeightedPrimePowerTerm F q)) :
    (∑ q ∈ S, chapter03WeightedPrimePowerTerm F q) ≤
      ∑' q : Chapter03PrimePower K, chapter03WeightedPrimePowerTerm F q := by
  exact hsum.sum_le_tsum S fun q hq =>
    chapter03_weighted_prime_power_term_nonneg K hF q

/-! The next interfaces record the residue-degree normalization behind the
prime-ideal examples. -/

def chapter03ResidueDegreeOverNatPrime
    {K : Type*} [Field K] [NumberField K]
    (p : ℕ) (P : Ideal (𝓞 K)) : ℕ :=
  (Ideal.span ({(p : ℤ)} : Set ℤ)).inertiaDeg' P

theorem chapter03_prime_ideal_norm_eq_prime_pow_residue_degree
    (K : Type*) [Field K] [NumberField K] {p : ℕ} (hp : Nat.Prime p)
    {P : Ideal (𝓞 K)}
    (hP : P ∈ chapter03PrimeIdealsOverNatPrime (K := K) p) :
    Ideal.absNorm P = p ^ chapter03ResidueDegreeOverNatPrime p P := by
  let pI : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  exact
    (letI : P.LiesOver pI :=
        (chapter03_mem_prime_ideals_over_nat_prime_iff (P := P)).mp hP |>.2;
     by
       simpa [chapter03ResidueDegreeOverNatPrime, pI] using
         (Ideal.absNorm_eq_pow_inertiaDeg' P hp))

theorem chapter03_euler_factors_are_indexed_by_prime_ideals
    (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    chapter03EulerProduct K s =
      ∏' P : Chapter03PrimeIdeal K,
        (1 - (chapter03PrimeIdealNorm P : ℂ) ^ (-s))⁻¹ := by
  rfl

theorem chapter03_first_power_term_eq_log_derivative_zero_power
    (K : Type*) [Field K] [NumberField K]
    (P : Chapter03PrimeIdeal K) (s : ℂ) :
    chapter03FirstPowerPrimeIdealTerm P.asIdeal s =
      chapter03LogDerivativeTerm (P, 0) s := by
  simp [chapter03FirstPowerPrimeIdealTerm, chapter03LogDerivativeTerm,
    chapter03PrimeIdealNorm, chapter03AbsoluteIdealNorm]

def chapter03RationalFirstPowerTerm (p : Nat.Primes) (s : ℂ) : ℂ :=
  (Real.log (p : ℝ) : ℂ) * (p : ℂ) ^ (-s)

theorem chapter03_rational_example_log_derivative
    {s : ℂ} (hs : s ∈ chapter03EulerHalfPlane) :
    -(deriv (chapter03DedekindZeta ℚ) s) / chapter03DedekindZeta ℚ s =
      ∑' p : Nat.Primes, ∑' m : ℕ,
        (Real.log (p : ℝ) : ℂ) *
          (p : ℂ) ^ (-((m + 1 : ℕ) : ℂ) * s) := by
  calc
    -(deriv (chapter03DedekindZeta ℚ) s) / chapter03DedekindZeta ℚ s =
        ∑' P : Chapter03PrimeIdeal ℚ, ∑' m : ℕ,
          (Real.log (chapter03PrimeIdealNorm P : ℝ) : ℂ) *
            (chapter03PrimeIdealNorm P : ℂ) ^ (-((m + 1 : ℕ) : ℂ) * s) :=
      chapter03_log_derivative_formula_explicit ℚ hs
    _ = ∑' p : Nat.Primes, ∑' m : ℕ,
          (Real.log (p : ℝ) : ℂ) *
            (p : ℂ) ^ (-((m + 1 : ℕ) : ℂ) * s) := by
      rw [← (chapter03RationalPrimeIdealEquiv).tsum_eq]
      congr 1
      funext P
      congr 1
      funext m
      rw [chapter03_rational_prime_ideal_norm_eq_equiv]

theorem chapter03_rational_example_first_power_term
    (p : Nat.Primes) (s : ℂ) :
    chapter03RationalFirstPowerTerm p s =
      (Real.log (p : ℝ) : ℂ) * (p : ℂ) ^ (-s) := by
  rfl

theorem chapter03_log_norm_prime_square_eq_two_log_prime
    {p : ℕ} (hp : Nat.Prime p) :
    Real.log ((p ^ 2 : ℕ) : ℝ) = 2 * Real.log (p : ℝ) := by
  have _hp := hp
  rw [Nat.cast_pow, Real.log_pow]
  ring

theorem chapter03_gaussian_split_prime_ideals
    (K : Type*) [Field K] [NumberField K]
    (hK : chapter03IsGaussianField K) {p : ℕ} (hp : Nat.Prime p)
    (hmod : p % 4 = 1) :
    ∃ P Q : Ideal (𝓞 K),
      P ∈ chapter03PrimeIdealsOverNatPrime (K := K) p ∧
      Q ∈ chapter03PrimeIdealsOverNatPrime (K := K) p ∧
      P ≠ Q ∧
      Ideal.absNorm P = p ∧
      Ideal.absNorm Q = p ∧
      Ideal.map (algebraMap ℤ (𝓞 K))
          (Ideal.span ({(p : ℤ)} : Set ℤ)) = P * Q ∧
      ∀ R, R ∈ chapter03PrimeIdealsOverNatPrime (K := K) p →
        R = P ∨ R = Q := by
  rcases hK with ⟨ι, hιsq, hgen⟩
  have hι : IsPrimitiveRoot ι 4 := chapter03_gaussian_primitive_root K hιsq
  have : IsCyclotomicExtension {4} ℚ K :=
    chapter03_isCyclotomic_of_gaussian K hιsq hgen
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {4} ℚ K
  have hdegree : Module.finrank ℚ K = 2 := by
    convert IsCyclotomicExtension.Rat.finrank 4 K using 1
    decide
  let : Fact p.Prime := ⟨hp⟩
  let pI : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  have hpdvd : ¬ p ∣ 4 := by
    intro h
    have hp_le : p ≤ 4 := Nat.le_of_dvd (by norm_num) h
    interval_cases p
    · have := hp.one_lt
      omega
    · have := hp.one_lt
      omega
    · norm_num at hmod
    · norm_num at h
    · norm_num at hmod
  have hram : pI.ramificationIdxIn (𝓞 K) = 1 := by
    dsimp [pI]
    exact IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd p K hpdvd
  have hin : pI.inertiaDegIn (𝓞 K) = orderOf (p : ZMod 4) := by
    dsimp [pI]
    exact IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p K hpdvd
  have horder : orderOf (p : ZMod 4) = 1 := by
    rw [← ZMod.natCast_mod p 4, hmod]
    simp
  have hfund :=
    Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      pI (𝓞 K) (Gal(K / ℚ))
  have hcardGal : Nat.card (Gal(K / ℚ)) = 2 := by
    rw [IsGalois.card_aut_eq_finrank ℚ K, hdegree]
  have hcard : (pI.primesOver (𝓞 K)).ncard *
      (pI.ramificationIdxIn (𝓞 K) * pI.inertiaDegIn (𝓞 K)) = 2 := by
    rw [hcardGal] at hfund
    exact hfund
  have hncard : (pI.primesOver (𝓞 K)).ncard = 2 := by
    rw [hram, hin, horder] at hcard
    omega
  obtain ⟨P, Q, hPQ, hPset⟩ := Set.ncard_eq_two.mp hncard
  have hPmem : P ∈ chapter03PrimeIdealsOverNatPrime (K := K) p := by
    change P ∈ pI.primesOver (𝓞 K)
    rw [hPset]
    simp
  have hQmem : Q ∈ chapter03PrimeIdealsOverNatPrime (K := K) p := by
    change Q ∈ pI.primesOver (𝓞 K)
    rw [hPset]
    simp
  have hP' := (chapter03_mem_prime_ideals_over_nat_prime_iff P).mp hPmem
  have hQ' := (chapter03_mem_prime_ideals_over_nat_prime_iff Q).mp hQmem
  have hPnorm : Ideal.absNorm P = p := by
    let : P.IsPrime := hP'.1
    let : P.LiesOver pI := by simpa [pI] using hP'.2
    let : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P pI
    rw [Ideal.absNorm_eq_pow_inertiaDeg' P hp, Ideal.inertiaDeg'_eq_inertiaDeg]
    rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd p K P hpdvd, horder]
    simp
  have hQnorm : Ideal.absNorm Q = p := by
    let : Q.IsPrime := hQ'.1
    let : Q.LiesOver pI := by simpa [pI] using hQ'.2
    let : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q pI
    rw [Ideal.absNorm_eq_pow_inertiaDeg' Q hp, Ideal.inertiaDeg'_eq_inertiaDeg]
    rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd p K Q hpdvd, horder]
    simp
  have hmap : Ideal.map (algebraMap ℤ (𝓞 K)) pI = P * Q := by
    let : P.IsPrime := hP'.1
    let : P.LiesOver pI := by simpa [pI] using hP'.2
    let : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P pI
    let : Q.IsPrime := hQ'.1
    let : Q.LiesOver pI := by simpa [pI] using hQ'.2
    let : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q pI
    have hramP : P.ramificationIdx ℤ = 1 :=
      IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p K P hpdvd
    have hramQ : Q.ramificationIdx ℤ = 1 :=
      IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p K Q hpdvd
    have hfac :=
      Ideal.map_algebraMap_eq_finsetProd_pow (p := pI) (R := 𝓞 K) (S := ℤ) (by
        simpa [pI] using hp.ne_zero)
    have hPQfinset : (pI.primesOver (𝓞 K)).toFinset = {P, Q} := by
      ext R
      simp [hPset]
    rw [hPQfinset] at hfac
    have hnot : P ∉ ({Q} : Finset (Ideal (𝓞 K))) := by
      simpa using hPQ
    rw [Finset.prod_insert hnot, Finset.prod_singleton] at hfac
    rw [hramP, hramQ, pow_one, pow_one] at hfac
    exact hfac
  refine ⟨P, Q, hPmem, hQmem, hPQ, hPnorm, hQnorm, hmap, ?_⟩
  intro R hR
  change R ∈ pI.primesOver (𝓞 K) at hR
  rw [hPset] at hR
  simpa [hPQ] using hR

theorem chapter03_gaussian_inert_prime_ideal
    (K : Type*) [Field K] [NumberField K]
    (hK : chapter03IsGaussianField K) {p : ℕ} (hp : Nat.Prime p)
    (hmod : p % 4 = 3) :
    ∃ P : Ideal (𝓞 K),
      P ∈ chapter03PrimeIdealsOverNatPrime (K := K) p ∧
      Ideal.absNorm P = p ^ 2 ∧
      Ideal.map (algebraMap ℤ (𝓞 K))
          (Ideal.span ({(p : ℤ)} : Set ℤ)) = P ∧
      ∀ R, R ∈ chapter03PrimeIdealsOverNatPrime (K := K) p → R = P := by
  rcases hK with ⟨ι, hιsq, hgen⟩
  have hι : IsPrimitiveRoot ι 4 := chapter03_gaussian_primitive_root K hιsq
  have : IsCyclotomicExtension {4} ℚ K :=
    chapter03_isCyclotomic_of_gaussian K hιsq hgen
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {4} ℚ K
  have hdegree : Module.finrank ℚ K = 2 := by
    convert IsCyclotomicExtension.Rat.finrank 4 K using 1
    decide
  let : Fact p.Prime := ⟨hp⟩
  let pI : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  have hpdvd : ¬ p ∣ 4 := by
    intro h
    have hp_le : p ≤ 4 := Nat.le_of_dvd (by norm_num) h
    interval_cases p
    · have := hp.one_lt
      omega
    · have := hp.one_lt
      omega
    · norm_num at hmod
    · norm_num at h
    · norm_num at hmod
  have hram : pI.ramificationIdxIn (𝓞 K) = 1 := by
    dsimp [pI]
    exact IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd p K hpdvd
  have hin : pI.inertiaDegIn (𝓞 K) = orderOf (p : ZMod 4) := by
    dsimp [pI]
    exact IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p K hpdvd
  have horder : orderOf (p : ZMod 4) = 2 := by
    rw [← ZMod.natCast_mod p 4, hmod]
    rw [orderOf_eq_iff (by norm_num)]
    have hthree : (3 : ZMod 4) = -1 := by
      apply ZMod.val_injective 4
      rw [ZMod.val_neg_one, ZMod.val_ofNat]
    constructor
    · change (3 : ZMod 4) ^ 2 = 1
      rw [hthree]
      simp
    · intro m hm hmpos
      interval_cases m
      change (3 : ZMod 4) ^ 1 ≠ 1
      rw [hthree]
      let : Fact (2 < 4) := ⟨by norm_num⟩
      exact ZMod.neg_one_ne_one (n := 4)
  have hfund :=
    Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      pI (𝓞 K) (Gal(K / ℚ))
  have hcardGal : Nat.card (Gal(K / ℚ)) = 2 := by
    rw [IsGalois.card_aut_eq_finrank ℚ K, hdegree]
  have hcard : (pI.primesOver (𝓞 K)).ncard *
      (pI.ramificationIdxIn (𝓞 K) * pI.inertiaDegIn (𝓞 K)) = 2 := by
    rw [hcardGal] at hfund
    exact hfund
  have hncard : (pI.primesOver (𝓞 K)).ncard = 1 := by
    rw [hram, hin, horder] at hcard
    omega
  obtain ⟨P, hPset⟩ := Set.ncard_eq_one.mp hncard
  have hPmem : P ∈ chapter03PrimeIdealsOverNatPrime (K := K) p := by
    change P ∈ pI.primesOver (𝓞 K)
    rw [hPset]
    simp
  have hP' := (chapter03_mem_prime_ideals_over_nat_prime_iff P).mp hPmem
  have hPnorm : Ideal.absNorm P = p ^ 2 := by
    let : P.IsPrime := hP'.1
    let : P.LiesOver pI := by simpa [pI] using hP'.2
    let : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P pI
    rw [Ideal.absNorm_eq_pow_inertiaDeg' P hp, Ideal.inertiaDeg'_eq_inertiaDeg]
    rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd p K P hpdvd, horder]
  have hmap : Ideal.map (algebraMap ℤ (𝓞 K)) pI = P := by
    let : P.IsPrime := hP'.1
    let : P.LiesOver pI := by simpa [pI] using hP'.2
    let : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P pI
    have hramP : P.ramificationIdx ℤ = 1 :=
      IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p K P hpdvd
    have hfac :=
      Ideal.map_algebraMap_eq_finsetProd_pow (p := pI) (R := 𝓞 K) (S := ℤ) (by
        simpa [pI] using hp.ne_zero)
    have hPfinset : (pI.primesOver (𝓞 K)).toFinset = {P} := by
      ext R
      simp [hPset]
    rw [hPfinset] at hfac
    simpa [hramP] using hfac
  refine ⟨P, hPmem, hPnorm, hmap, ?_⟩
  intro R hR
  change R ∈ pI.primesOver (𝓞 K) at hR
  rw [hPset] at hR
  exact Set.mem_singleton_iff.mp hR

theorem chapter03_gaussian_ramified_prime_ideal_at_two
    (K : Type*) [Field K] [NumberField K]
    (hK : chapter03IsGaussianField K) :
    ∃ P : Ideal (𝓞 K),
      P ∈ chapter03PrimeIdealsOverNatPrime (K := K) 2 ∧
      Ideal.absNorm P = 2 ∧
      Ideal.map (algebraMap ℤ (𝓞 K))
          (Ideal.span ({(2 : ℤ)} : Set ℤ)) = P ^ 2 ∧
      ∀ R, R ∈ chapter03PrimeIdealsOverNatPrime (K := K) 2 → R = P := by
  rcases hK with ⟨ι, hιsq, hgen⟩
  have hι : IsPrimitiveRoot ι 4 := chapter03_gaussian_primitive_root K hιsq
  have : IsCyclotomicExtension {4} ℚ K :=
    chapter03_isCyclotomic_of_gaussian K hιsq hgen
  have hdegree : Module.finrank ℚ K = 2 := by
    convert IsCyclotomicExtension.Rat.finrank 4 K using 1
    decide
  let pI : Ideal ℤ := Ideal.span ({(2 : ℤ)} : Set ℤ)
  let P : Ideal (𝓞 K) := Ideal.span {hι.toInteger - 1}
  have hPprime : P.IsPrime := by
    dsimp [P]
    exact IsCyclotomicExtension.Rat.isPrime_span_zeta_sub_one 2 1 hι
  have hPlies : P.LiesOver pI := by
    dsimp [P, pI]
    exact IsCyclotomicExtension.Rat.liesOver_span_zeta_sub_one 2 1 hι
  have hPmem : P ∈ chapter03PrimeIdealsOverNatPrime (K := K) 2 := by
    exact (chapter03_mem_prime_ideals_over_nat_prime_iff P).2 ⟨hPprime, hPlies⟩
  have hPnorm : Ideal.absNorm P = 2 := by
    dsimp [P]
    exact IsCyclotomicExtension.Rat.absNorm_span_zeta_sub_one 2 1 hι
  have hmap : Ideal.map (algebraMap ℤ (𝓞 K)) pI = P ^ 2 := by
    dsimp [P, pI]
    simpa [hdegree] using
      (IsCyclotomicExtension.Rat.map_eq_span_zeta_sub_one_pow 2 1 hι)
  refine ⟨P, hPmem, hPnorm, hmap, ?_⟩
  intro R hR
  have hR' := (chapter03_mem_prime_ideals_over_nat_prime_iff R).mp hR
  let : R.IsPrime := hR'.1
  let : R.LiesOver pI := by simpa [pI] using hR'.2
  dsimp [P]
  exact IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver 2 1 K hι R

theorem chapter03_gaussian_split_first_power_contribution
    (K : Type*) [Field K] [NumberField K] {p : ℕ} (hp : Nat.Prime p)
    {P Q : Ideal (𝓞 K)} (hP : Ideal.absNorm P = p)
    (hQ : Ideal.absNorm Q = p) (s : ℂ) :
      chapter03FirstPowerPrimeIdealTerm P s +
        chapter03FirstPowerPrimeIdealTerm Q s =
      2 * (Real.log (p : ℝ) : ℂ) * (p : ℂ) ^ (-s) := by
  have _hp := hp
  simp [chapter03FirstPowerPrimeIdealTerm, hP, hQ]
  ring

theorem chapter03_gaussian_inert_first_power_contribution
    (K : Type*) [Field K] [NumberField K] {p : ℕ} (hp : Nat.Prime p)
    {P : Ideal (𝓞 K)} (hP : Ideal.absNorm P = p ^ 2) (s : ℂ) :
      chapter03FirstPowerPrimeIdealTerm P s =
      (2 * (Real.log (p : ℝ) : ℂ)) * (p : ℂ) ^ (-((2 : ℂ) * s)) := by
  unfold chapter03FirstPowerPrimeIdealTerm
  rw [hP]
  rw [chapter03_log_norm_prime_square_eq_two_log_prime hp]
  congr 1
  · norm_num
  · rw [show -((2 : ℂ) * s) = (2 : ℕ) * (-s) by ring]
    simpa only [Nat.cast_pow] using
      (Complex.natCast_cpow_natCast_mul p 2 (-s)).symm

theorem chapter03_gaussian_ramified_first_power_contribution
    (K : Type*) [Field K] [NumberField K] {P : Ideal (𝓞 K)}
    (hP : Ideal.absNorm P = 2) (s : ℂ) :
    chapter03FirstPowerPrimeIdealTerm P s =
      (Real.log (2 : ℝ) : ℂ) * (2 : ℂ) ^ (-s) := by
  simp [chapter03FirstPowerPrimeIdealTerm, hP]

theorem chapter03_weighted_prime_power_nonzero_implies_bound
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hF : chapter03SupportWithin F T)
    {q : Chapter03PrimePower K}
    (hq : chapter03WeightedPrimePowerTerm F q ≠ 0) :
    (((q.2 + 1 : ℕ) : ℝ) *
        Real.log (chapter03PrimeIdealNorm q.1 : ℝ)) ≤ T := by
  have _hT := hT
  have hlog : 0 < Real.log (chapter03PrimeIdealNorm q.1 : ℝ) :=
    chapter03_prime_ideal_log_norm_pos K q.1
  have hFq : F (((q.2 + 1 : ℕ) : ℝ) *
      Real.log (chapter03PrimeIdealNorm q.1 : ℝ)) ≠ 0 := by
    intro hzero
    have hzero' : F (((q.2 : ℝ) + 1) *
        Real.log (chapter03PrimeIdealNorm q.1 : ℝ)) = 0 := by
      simpa only [Nat.cast_add, Nat.cast_one] using hzero
    apply hq
    simp [chapter03WeightedPrimePowerTerm, hzero']
  have hmem : (((q.2 + 1 : ℕ) : ℝ) *
      Real.log (chapter03PrimeIdealNorm q.1 : ℝ)) ∈ Function.support F := hFq
  exact hF hmem |>.2

theorem chapter03_weighted_prime_power_support_finite
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hF : chapter03SupportWithin F T) :
    {q : Chapter03PrimePower K |
      chapter03WeightedPrimePowerTerm F q ≠ 0}.Finite := by
  let B : ℕ := Nat.ceil (Real.exp T)
  let M : ℕ := Nat.ceil (T / Real.log (2 : ℝ))
  let S : Set (Chapter03PrimeIdeal K) :=
    {P | chapter03PrimeIdealNorm P ≤ B}
  let U : Set ℕ := {m | m ≤ M}
  have hS : S.Finite := by
    simpa [S, B, chapter03PrimeIdealNorm, chapter03AbsoluteIdealNorm] using
      (Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le
        (R := 𝓞 K) B)
  have hU : U.Finite := by
    simpa [U] using Set.finite_le_nat M
  have hprod : (S ×ˢ U).Finite := hS.prod hU
  refine hprod.subset ?_
  intro q hq
  change q.1 ∈ S ∧ q.2 ∈ U
  have hbound :=
    chapter03_weighted_prime_power_nonzero_implies_bound K hT hF hq
  have hlog : 0 < Real.log (chapter03PrimeIdealNorm q.1 : ℝ) :=
    chapter03_prime_ideal_log_norm_pos K q.1
  have hlog_le : Real.log (chapter03PrimeIdealNorm q.1 : ℝ) ≤ T := by
    have hone : (1 : ℝ) ≤ ((q.2 + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le q.2))
    have hmul : Real.log (chapter03PrimeIdealNorm q.1 : ℝ) ≤
        ((q.2 + 1 : ℕ) : ℝ) *
          Real.log (chapter03PrimeIdealNorm q.1 : ℝ) := by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right hone (le_of_lt hlog))
    exact hmul.trans hbound
  have hNreal : (chapter03PrimeIdealNorm q.1 : ℝ) ≤ Real.exp T :=
    Real.le_exp_of_log_le hlog_le
  have hNnat : chapter03PrimeIdealNorm q.1 ≤ B := by
    have hceil : Real.exp T ≤ (B : ℝ) := by
      exact Nat.le_ceil _
    exact_mod_cast hNreal.trans hceil
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hN2 : (2 : ℝ) ≤ chapter03PrimeIdealNorm q.1 := by
    exact_mod_cast chapter03_prime_ideal_norm_ge_two K q.1
  have hlog2_le : Real.log (2 : ℝ) ≤
      Real.log (chapter03PrimeIdealNorm q.1 : ℝ) :=
    Real.log_le_log (by norm_num) hN2
  have hprod_bound :
      ((q.2 + 1 : ℕ) : ℝ) * Real.log (2 : ℝ) ≤ T := by
    calc
      ((q.2 + 1 : ℕ) : ℝ) * Real.log (2 : ℝ) ≤
          ((q.2 + 1 : ℕ) : ℝ) *
            Real.log (chapter03PrimeIdealNorm q.1 : ℝ) :=
        mul_le_mul_of_nonneg_left hlog2_le (by positivity)
      _ ≤ T := hbound
  have hdiv : ((q.2 + 1 : ℕ) : ℝ) ≤ T / Real.log (2 : ℝ) := by
    exact (le_div_iff₀ hlog2).2 hprod_bound
  have hsucc : q.2 + 1 ≤ M := by
    have hceil : T / Real.log (2 : ℝ) ≤ (M : ℝ) := by
      exact Nat.le_ceil _
    exact_mod_cast hdiv.trans hceil
  have hm : q.2 ≤ M := le_trans (Nat.le_succ q.2) hsucc
  exact ⟨hNnat, hm⟩

noncomputable def chapter03PrimePowerLedger
    (K : Type*) [Field K] [NumberField K] (F : ℝ → ℝ) (T : ℝ)
    (hT : 0 ≤ T) (hF : chapter03SupportWithin F T) :
    Finset (Chapter03PrimePower K) :=
  (chapter03_weighted_prime_power_support_finite (K := K) hT hF).toFinset

theorem chapter03_mem_prime_power_ledger_iff
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hF : chapter03SupportWithin F T)
    (q : Chapter03PrimePower K) :
      q ∈ chapter03PrimePowerLedger K F T hT hF ↔
      chapter03WeightedPrimePowerTerm F q ≠ 0 := by
  exact (chapter03_weighted_prime_power_support_finite (K := K) hT hF).mem_toFinset

theorem chapter03_weighted_prime_power_tsum_eq_ledger_sum
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hF : chapter03SupportWithin F T) :
    (∑' q : Chapter03PrimePower K, chapter03WeightedPrimePowerTerm F q) =
      ∑ q ∈ chapter03PrimePowerLedger K F T hT hF,
        chapter03WeightedPrimePowerTerm F q := by
  apply tsum_eq_sum
  intro q hq
  by_contra hq0
  apply hq
  exact (chapter03_mem_prime_power_ledger_iff (K := K) hT hF q).2 hq0

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03
