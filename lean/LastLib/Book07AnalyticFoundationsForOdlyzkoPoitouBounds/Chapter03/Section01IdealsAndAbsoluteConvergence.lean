import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03.Dependencies
import Mathlib.RingTheory.Ideal.Int
import Mathlib.Topology.Algebra.InfiniteSum.Order

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03

noncomputable section

open NumberField IsDedekindDomain
open scoped BigOperators nonZeroDivisors

/-! ### 3.1 Ideals and absolute convergence -/

theorem chapter03_prime_ideal_over_iff
    (K : Type*) [Field K] [NumberField K] {p : ℕ}
    (P : Chapter03PrimeIdeal K) :
    P.asIdeal ∈ chapter03PrimeIdealsOverNatPrime (K := K) p ↔
      P.asIdeal.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
  simp [chapter03_mem_prime_ideals_over_nat_prime_iff, P.isPrime]

theorem chapter03_prime_over_to_height_one
    (K : Type*) [Field K] [NumberField K] {p : ℕ} (hp : Nat.Prime p)
    {P : Ideal (𝓞 K)}
    (hP : P ∈ chapter03PrimeIdealsOverNatPrime (K := K) p) :
    ∃ v : Chapter03PrimeIdeal K, v.asIdeal = P := by
  have hP' := (chapter03_mem_prime_ideals_over_nat_prime_iff (P := P)).mp hP
  refine ⟨⟨P, hP'.1, ?_⟩, rfl⟩
  apply Ideal.ne_bot_of_mem_primesOver
    (p := Ideal.span ({(p : ℤ)} : Set ℤ)) (B := 𝓞 K)
  · simp [hp.ne_zero]
  · exact hP

theorem chapter03_integral_ideals_bounded_norm_finite
    (K : Type*) [Field K] [NumberField K] (B : ℕ) :
    {I : Ideal (𝓞 K) | Ideal.absNorm I ≤ B}.Finite := by
  exact Ideal.finite_setOfPred_absNorm_le B

theorem chapter03_nonzero_integral_ideals_bounded_norm_finite
    (K : Type*) [Field K] [NumberField K] (B : ℕ) :
    {I : Chapter03IntegralIdeal K | chapter03IdealNorm I ≤ B}.Finite := by
  exact Ideal.finite_setOfPred_absNorm_le₀ B

theorem chapter03_nonzero_ideal_factorization
    (K : Type*) [Field K] [NumberField K] {I : Ideal (𝓞 K)} (hI : I ≠ 0) :
    ∏ᶠ P : Chapter03PrimeIdeal K, P.maxPowDividing I = I := by
  exact Ideal.finprod_heightOneSpectrum_factorization hI

theorem chapter03_prime_ideals_over_rational_prime_finite
    (K : Type*) [Field K] [NumberField K] {p : ℕ} (hp : Nat.Prime p) :
    (chapter03PrimeIdealsOverNatPrime (K := K) p).Finite := by
  let pI : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  have hpI : pI ≠ (⊥ : Ideal ℤ) := by
    simp [pI, hp.ne_zero]
  have hpIprime : pI.IsPrime := by
    exact (Ideal.span_singleton_prime (α := ℤ) (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)
  have hpImax : pI.IsMaximal := Ideal.IsPrime.isMaximal hpIprime hpI
  simpa [chapter03PrimeIdealsOverNatPrime, pI] using
    (IsDedekindDomain.primesOver_finite (p := pI) (B := 𝓞 K) (hpm := hpImax))

theorem chapter03_prime_ideal_count_le_degree
    (K : Type*) [Field K] [NumberField K] {p : ℕ} (hp : Nat.Prime p) :
    (chapter03PrimeIdealsOverNatPrime (K := K) p).ncard ≤ chapter03Degree K := by
  let pI : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  have hpI : pI ≠ (⊥ : Ideal ℤ) := by simp [pI, hp.ne_zero]
  have hpIprime : pI.IsPrime := by
    exact (Ideal.span_singleton_prime (α := ℤ) (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)
  have hpImax : pI.IsMaximal := Ideal.IsPrime.isMaximal hpIprime hpI
  have hsum :=
    (letI : pI.IsPrime := hpIprime;
      letI : pI.IsMaximal := hpImax;
      Ideal.sum_ramification_inertia_eq_finrank (p := pI) (S := 𝓞 K))
  have hle :
      (pI.primesOver (𝓞 K)).ncard ≤
        ∑ q : pI.primesOver (𝓞 K),
          q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    rw [← Set.fintypeCard_eq_ncard]
    calc
      Fintype.card (pI.primesOver (𝓞 K)) =
          ∑ _ : pI.primesOver (𝓞 K), 1 := by simp
      _ ≤ ∑ q : pI.primesOver (𝓞 K),
          q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
        exact Finset.sum_le_sum fun q _ => by
          exact one_le_mul_of_one_le_of_one_le
            (Nat.one_le_iff_ne_zero.mpr
              (letI : q.1.IsPrime := q.2.1;
                Ideal.ramificationIdx_pos (R := ℤ) q.1).ne')
            (Nat.one_le_iff_ne_zero.mpr
              (letI : q.1.IsPrime := q.2.1;
                Ideal.inertiaDeg_pos (R := ℤ) q.1).ne')
  calc
    (chapter03PrimeIdealsOverNatPrime (K := K) p).ncard =
        (pI.primesOver (𝓞 K)).ncard := by rfl
    _ ≤ ∑ q : pI.primesOver (𝓞 K),
        q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := hle
    _ = Module.finrank ℤ (𝓞 K) := hsum
    _ = chapter03Degree K := by
      simpa [chapter03Degree] using
        (IsFractionRing.finrank_eq ℤ ℚ (𝓞 K) K).symm

theorem chapter03_prime_ideal_norm_ge_rational_prime
    (K : Type*) [Field K] [NumberField K] {p : ℕ} (hp : Nat.Prime p)
    {P : Ideal (𝓞 K)}
    (hP : P ∈ chapter03PrimeIdealsOverNatPrime (K := K) p) :
    p ≤ Ideal.absNorm P := by
  let pI : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  have hP' := (chapter03_mem_prime_ideals_over_nat_prime_iff (P := P)).mp hP
  exact
    (letI : P.IsPrime := hP'.1;
     letI : P.LiesOver pI := by simpa [pI] using hP'.2;
     by
       rw [Ideal.absNorm_eq_pow_inertiaDeg' P hp]
       have hf : 0 < pI.inertiaDeg' P := Ideal.inertiaDeg'_pos' pI P
       obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hf.ne'
       rw [hk, pow_succ]
       simpa [pI, Nat.sub_add_cancel hp.one_le] using
         Nat.mul_le_mul_right p (Nat.one_le_pow' k (p - 1)))

theorem chapter03_real_euler_product_bound
    (K : Type*) [Field K] [NumberField K] {σ : ℝ} (hσ : 1 < σ) :
    chapter03RealEulerProduct K σ ≤
      chapter03RationalPrimeEulerProduct σ ^ chapter03Degree K := by
  classical
  let e : Chapter03PrimeIdeal K → Nat.Primes := fun P =>
    ⟨Ideal.absNorm (Ideal.under ℤ P.asIdeal), by
      let hprime : P.asIdeal.IsPrime := P.isPrime
      let hne : NeZero P.asIdeal := ⟨P.ne_bot⟩
      exact @Nat.absNorm_under_prime (𝓞 K) _ _ _ P.asIdeal hprime hne⟩
  have he_mem (P : Chapter03PrimeIdeal K) :
      P.asIdeal ∈ chapter03PrimeIdealsOverNatPrime (K := K) (e P : ℕ) := by
    rw [chapter03_mem_prime_ideals_over_nat_prime_iff]
    refine ⟨P.isPrime, ?_⟩
    simpa [e] using (Int.liesOver_span_absNorm P.asIdeal)
  have he_norm (P : Chapter03PrimeIdeal K) :
      (e P : ℕ) ≤ chapter03PrimeIdealNorm P :=
    chapter03_prime_ideal_norm_ge_rational_prime K (e P).property (he_mem P)
  let f : Chapter03PrimeIdeal K → ℝ := fun P =>
    (1 - Real.rpow (chapter03PrimeIdealNorm P : ℝ) (-σ))⁻¹
  let g : Nat.Primes → ℝ := fun p =>
    (1 - Real.rpow (p : ℝ) (-σ))⁻¹
  have hpow_lt_one (x : ℝ) (hx : 1 < x) : Real.rpow x (-σ) < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg hx (by linarith)
  have hfactor_pos (P : Chapter03PrimeIdeal K) :
      0 < 1 - Real.rpow (chapter03PrimeIdealNorm P : ℝ) (-σ) := by
    have hP : (1 : ℝ) < chapter03PrimeIdealNorm P := by
      exact_mod_cast chapter03_prime_ideal_norm_gt_one P
    linarith [hpow_lt_one _ hP]
  have hfactor_one_le (P : Chapter03PrimeIdeal K) : 1 ≤ f P := by
    apply (one_le_inv₀ (hfactor_pos P)).2
    have hbase : (0 : ℝ) ≤ chapter03PrimeIdealNorm P := by positivity
    have hnonneg : 0 ≤ Real.rpow (chapter03PrimeIdealNorm P : ℝ) (-σ) :=
      Real.rpow_nonneg hbase _
    linarith
  have hfactor_le (P : Chapter03PrimeIdeal K) : f P ≤ g (e P) := by
    have hnorm : (e P : ℝ) ≤ chapter03PrimeIdealNorm P := by
      exact_mod_cast he_norm P
    have hpow : Real.rpow (chapter03PrimeIdealNorm P : ℝ) (-σ) ≤
        Real.rpow (e P : ℝ) (-σ) :=
      Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (e P).property.pos)
        hnorm (by linarith)
    have hposP := hfactor_pos P
    have hposp : 0 < 1 - Real.rpow (e P : ℝ) (-σ) := by
      have hp : (1 : ℝ) < (e P : ℕ) := by
        exact_mod_cast (e P).property.one_lt
      linarith [hpow_lt_one _ hp]
    dsimp [f, g]
    exact (inv_le_inv₀ hposP hposp).2 (by linarith)
  have hfactor_pos' (p : Nat.Primes) :
      0 < 1 - Real.rpow (p : ℝ) (-σ) := by
    have hp : (1 : ℝ) < (p : ℕ) := by
      exact_mod_cast p.property.one_lt
    linarith [hpow_lt_one _ hp]
  have hfactor_one_le' (p : Nat.Primes) : 1 ≤ g p := by
    apply (one_le_inv₀ (hfactor_pos' p)).2
    have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
    have hnonneg : 0 ≤ Real.rpow (p : ℝ) (-σ) := Real.rpow_nonneg hp0 _
    linarith
  have hg_nonneg (p : Nat.Primes) : 0 ≤ g p := by
    dsimp [g]
    exact (inv_pos.mpr (hfactor_pos' p)).le
  have hf_nonneg (P : Chapter03PrimeIdeal K) : 0 ≤ f P := by
    dsimp [f]
    exact (inv_pos.mpr (hfactor_pos P)).le
  let F : ℕ →*₀ ℝ :=
    { toFun := fun n => (n : ℝ) ^ (-σ)
      map_zero' := by
        simpa only [Nat.cast_zero] using
          (Real.zero_rpow (x := -σ) (by linarith))
      map_one' := by simp
      map_mul' := by
        intro m n
        rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)] }
  have hsum : Summable (fun n : ℕ => ‖F n‖) := by
    dsimp [F]
    convert (Real.summable_nat_rpow_inv.mpr hσ) using 1
    ext n
    rw [abs_of_nonneg (by positivity), Real.rpow_neg (by positivity)]
  have hG : Multipliable g := by
    have h := EulerProduct.eulerProduct_completely_multiplicative_hasProd hsum
    simpa [g, F] using h.multipliable
  have hfinite_prod (S : Finset (Chapter03PrimeIdeal K)) :
      (∏ P ∈ S, f P) ≤ (∏ p ∈ S.image e, g p ^ chapter03Degree K) := by
    have hgroup (p : Nat.Primes) :
        (∏ P ∈ S.filter (fun P => e P = p), f P) ≤
          g p ^ chapter03Degree K := by
      let U : Set (Ideal (𝓞 K)) :=
        chapter03PrimeIdealsOverNatPrime (K := K) (p : ℕ)
      have hU : U.Finite :=
        chapter03_prime_ideals_over_rational_prime_finite K p.property
      let φ : (S.filter (fun P => e P = p)) → {I : Ideal (𝓞 K) // I ∈ hU.toFinset} :=
        fun P => ⟨P.1.asIdeal, by
          have hEp : e P.1 = p := (Finset.mem_filter.mp P.2).2
          apply hU.mem_toFinset.mpr
          simpa [U, hEp] using he_mem P.1⟩
      have hφ : Function.Injective φ := by
        intro P Q hPQ
        apply Subtype.ext
        apply chapter03_prime_ideal_ext P.1 Q.1
        exact congrArg Subtype.val hPQ
      have hcard : (S.filter (fun P => e P = p)).card ≤ chapter03Degree K := by
        calc
          (S.filter (fun P => e P = p)).card =
              Fintype.card (S.filter (fun P => e P = p)) := by simp
          _ ≤ Fintype.card {I : Ideal (𝓞 K) // I ∈ hU.toFinset} :=
            Fintype.card_le_of_injective φ hφ
          _ = U.ncard := by
            simpa using (Set.ncard_eq_toFinset_card U hU).symm
          _ ≤ chapter03Degree K := chapter03_prime_ideal_count_le_degree K p.property
      calc
        (∏ P ∈ S.filter (fun P => e P = p), f P) ≤
            ∏ P ∈ S.filter (fun P => e P = p), g p := by
          apply Finset.prod_le_prod
          · intro P hP
            exact hf_nonneg P
          · intro P hP
            have hEp : e P = p := (Finset.mem_filter.mp hP).2
            simpa [hEp] using hfactor_le P
        _ = g p ^ (S.filter (fun P => e P = p)).card := by simp
        _ ≤ g p ^ chapter03Degree K :=
          pow_le_pow_right₀ (hfactor_one_le' p) hcard
    rw [← Finset.prod_fiberwise_of_maps_to
      (fun P hP => Finset.mem_image_of_mem e hP) f]
    apply Finset.prod_le_prod
    · intro p hp
      exact Finset.prod_nonneg (fun P hP => hf_nonneg P)
    · intro p hp
      exact hgroup p
  have hprod_bound : ∀ S : Finset (Chapter03PrimeIdeal K),
      (∏ P ∈ S, f P) ≤ (∏' p : Nat.Primes, g p) ^ chapter03Degree K := by
    intro S
    calc
      (∏ P ∈ S, f P) ≤ ∏ p ∈ S.image e, g p ^ chapter03Degree K :=
        hfinite_prod S
      _ = (∏ p ∈ S.image e, g p) ^ chapter03Degree K := by
        rw [Finset.prod_pow]
      _ ≤ (∏' p : Nat.Primes, g p) ^ chapter03Degree K := by
        have hprod_le_tprod (T : Finset Nat.Primes) :
            (∏ p ∈ T, g p) ≤ ∏' p : Nat.Primes, g p := by
          apply ge_of_tendsto hG.hasProd
          filter_upwards [Filter.eventually_atTop.2 ⟨T, fun U hTU => hTU⟩] with U hTU
          exact Finset.prod_le_prod_of_subset_of_one_le hTU
            (fun p hp => hg_nonneg p) (fun p hp hnot => hfactor_one_le' p)
        exact pow_le_pow_left₀
          (Finset.prod_nonneg (fun p hp => hg_nonneg p))
          (hprod_le_tprod (S.image e))
          (chapter03Degree K)
  have hone_tprod : (1 : ℝ) ≤ ∏' p : Nat.Primes, g p := by
    apply le_hasProd_of_le_prod hG.hasProd
    intro S
    exact Finset.one_le_prod (fun p hp => hfactor_one_le' p)
  have hone : (1 : ℝ) ≤ (∏' p : Nat.Primes, g p) ^ chapter03Degree K :=
    by simpa only [one_pow] using
      (pow_le_pow_left₀ (by positivity) hone_tprod (chapter03Degree K))
  change (∏' P : Chapter03PrimeIdeal K, f P) ≤
    (∏' p : Nat.Primes, g p) ^ chapter03Degree K
  exact tprod_le_of_prod_le' hone hprod_bound

theorem chapter03_rational_prime_euler_product_eq_riemann_zeta
    {σ : ℝ} (hσ : 1 < σ) :
    chapter03RationalPrimeEulerProduct σ = chapter03RiemannZetaOnReal σ := by
  let f : ℕ →*₀ ℝ :=
    { toFun := fun n => (n : ℝ) ^ (-σ)
      map_zero' := by
        simpa only [Nat.cast_zero] using
          (Real.zero_rpow (x := -σ) (by linarith))
      map_one' := by simp
      map_mul' := by
        intro m n
        rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)] }
  have hsum : Summable (fun n : ℕ => ‖f n‖) := by
    dsimp [f]
    convert (Real.summable_nat_rpow_inv.mpr hσ) using 1
    ext n
    rw [abs_of_nonneg (by positivity), Real.rpow_neg (by positivity)]
  have hprod := EulerProduct.eulerProduct_completely_multiplicative_tprod hsum
  change (∏' p : Nat.Primes, (1 - Real.rpow (p : ℝ) (-σ))⁻¹) =
    (riemannZeta (σ : ℂ)).re
  calc
    (∏' p : Nat.Primes, (1 - Real.rpow (p : ℝ) (-σ))⁻¹) =
        ∑' n : ℕ, f n := by simpa [f] using hprod
    _ = (riemannZeta (σ : ℂ)).re := by
      have hsc :
          Summable (fun n : ℕ => 1 / (n : ℂ) ^ (σ : ℂ)) :=
        (Complex.summable_one_div_nat_cpow (p := (σ : ℂ))).2 (by simpa using hσ)
      have hz := zeta_eq_tsum_one_div_nat_cpow
        (s := (σ : ℂ)) (by simpa using hσ)
      rw [hz, Complex.re_tsum hsc]
      apply tsum_congr
      intro n
      change (n : ℝ) ^ (-σ) = (1 / (n : ℂ) ^ (σ : ℂ)).re
      have hc := Complex.ofReal_cpow (x := (n : ℝ)) (by positivity) σ
      have hc' := hc
      simp only [Complex.ofReal_natCast] at hc'
      rw [← hc']
      simp [Real.rpow_neg (x := (n : ℝ)) (by positivity) σ]

theorem chapter03_rational_zeta_series_summable
    {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => Real.rpow ((n : ℝ) + 1) (-σ)) := by
  convert (Real.summable_one_div_nat_add_rpow (1 : ℝ) σ).2 hσ using 1
  ext n
  rw [abs_of_nonneg (by positivity), one_div]
  exact Real.rpow_neg (x := (n : ℝ) + 1) (by positivity) σ

private theorem chapter03_ideal_series_norm_summable_aux
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    Summable (fun I : Chapter03IntegralIdeal K => ‖chapter03IdealTerm s I‖) := by
  classical
  have hcard (n : ℕ) :
      Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} =
        ∑ k ∈ Finset.Icc 1 n,
          Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} := by
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by
        simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq
        (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  let A : ℕ → ℝ := fun n =>
    Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n}
  let f : ℕ → ℂ := fun n =>
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}
  have hpartial : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ‖f k‖) =
      fun n => A n := by
    funext n
    simp [f, A]
    rw [hcard, Nat.cast_sum]
  have hlim := (Ideal.tendsto_norm_le_div_atTop₀ K).comp
    (tendsto_natCast_atTop_atTop)
  have hO : A =O[Filter.atTop] (fun n : ℕ => (n : ℝ)) := by
    apply Asymptotics.isBigO_of_div_tendsto_nhds
    · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      intro hn0
      exact False.elim ((Nat.cast_ne_zero.mpr hn.ne') hn0)
    · change Filter.Tendsto (fun n : ℕ => A n / (n : ℝ)) Filter.atTop _
      simpa [A, Function.comp_def] using hlim
  have hsumO :
      (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ‖f k‖) =O[Filter.atTop]
        (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
    rw [hpartial]
    simpa [Real.rpow_one] using hO
  have hf : LSeriesSummable f s := by
    apply LSeriesSummable_of_sum_norm_bigO (r := 1) hsumO
    · norm_num
    · exact hs
  have hnormL : Summable (fun n : ℕ => ‖LSeries.term f s n‖) :=
    summable_norm_iff.mpr hf
  have hfiber (n : ℕ) :
      (∑' I : {I : Chapter03IntegralIdeal K | chapter03IdealNorm I = n},
        ‖chapter03IdealTerm s I.1‖) = ‖LSeries.term f s n‖ := by
    by_cases hn : n = 0
    · subst n
      let hEmpty : IsEmpty {I : Chapter03IntegralIdeal K | chapter03IdealNorm I = 0} :=
        ⟨fun I => by
          have hne := Ideal.absNorm_ne_zero_of_nonZeroDivisors I.1
          have hzero : Ideal.absNorm (I.1 : Ideal (𝓞 K)) = 0 := by
            change chapter03IdealNorm I.1 = 0
            exact I.2
          exact hne hzero⟩
      let e : Empty ≃ {I : Chapter03IntegralIdeal K | chapter03IdealNorm I = 0} :=
        (@Equiv.equivEmpty _ hEmpty).symm
      rw [← e.tsum_eq]
      simp [LSeries.term_zero]
    · have hfin : {I : Chapter03IntegralIdeal K | chapter03IdealNorm I = n}.Finite :=
        (chapter03_nonzero_integral_ideals_bounded_norm_finite K n).subset
          (fun I hI => le_of_eq hI)
      let hFintype : Fintype {I : Chapter03IntegralIdeal K | chapter03IdealNorm I = n} :=
        hfin.fintype
      have hconst (I : {I : Chapter03IntegralIdeal K | chapter03IdealNorm I = n}) :
          ‖chapter03IdealTerm s I.1‖ = ‖(n : ℂ) ^ (-s)‖ := by
        change ‖(chapter03IdealNorm I.1 : ℂ) ^ (-s)‖ = ‖(n : ℂ) ^ (-s)‖
        rw [I.2]
      have hI0 (I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}) :
          I.1 ∈ (Ideal (𝓞 K))⁰ := by
        rw [mem_nonZeroDivisors_iff_ne_zero]
        intro hzero
        apply hn
        simpa [hzero] using I.2.symm
      let e : {J : Chapter03IntegralIdeal K | chapter03IdealNorm J = n} ≃
          {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
        { toFun := fun J =>
            ⟨(J.1 : Ideal (𝓞 K)), by
              exact J.2⟩
          invFun := fun I =>
            ⟨⟨I.1, hI0 I⟩, by
              change chapter03IdealNorm ⟨I.1, hI0 I⟩ = n
              exact I.2⟩
          left_inv := by intro J; rfl
          right_inv := by intro I; rfl }
      have hcard' :
          (@Finset.univ {J : Chapter03IntegralIdeal K |
            chapter03IdealNorm J = n} hFintype).card =
            Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} := by
        change @Fintype.card _ hFintype = _
        simpa only [Nat.card_eq_fintype_card] using Nat.card_congr e
      rw [@tsum_fintype _ _ _ _ _ _ hFintype]
      simp_rw [hconst]
      rw [Finset.sum_const, nsmul_eq_mul]
      rw [LSeries.term_of_ne_zero hn]
      simp [f, hcard', Complex.cpow_neg]
      rw [div_eq_mul_inv]
  refine (summable_partition (f := fun I : Chapter03IntegralIdeal K =>
      ‖chapter03IdealTerm s I‖) (s := fun n : ℕ =>
        {I : Chapter03IntegralIdeal K | chapter03IdealNorm I = n}) ?_ ?_).2 ?_
  · intro I
    exact norm_nonneg _
  · intro I
    refine ⟨chapter03IdealNorm I, ?_, ?_⟩
    · rfl
    · intro j hj
      exact hj.symm
  · constructor
    · intro n
      have hfin : {I : Chapter03IntegralIdeal K | chapter03IdealNorm I = n}.Finite :=
        (chapter03_nonzero_integral_ideals_bounded_norm_finite K n).subset
          (fun I hI => le_of_eq hI)
      let hFintype : Fintype {I : Chapter03IntegralIdeal K | chapter03IdealNorm I = n} :=
        hfin.fintype
      exact @Summable.of_finite _ _ _ _ _ hfin _ _
    · simpa only [hfiber] using hnormL

theorem chapter03_ideal_series_eq_dedekind_zeta
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    chapter03DedekindZeta K s = chapter03IdealSeries K s := by
  classical
  have hsum : Summable (fun I : Chapter03IntegralIdeal K => chapter03IdealTerm s I) :=
    (chapter03_ideal_series_norm_summable_aux K hs).of_norm
  let f : ℕ → ℂ := fun n =>
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}
  have hfiber (n : ℕ) :
      (∑' I : {I : Chapter03IntegralIdeal K | chapter03IdealNorm I = n},
        chapter03IdealTerm s I.1) = LSeries.term f s n := by
    by_cases hn : n = 0
    · subst n
      let hEmpty : IsEmpty {I : Chapter03IntegralIdeal K | chapter03IdealNorm I = 0} :=
        ⟨fun I => by
          have hne := Ideal.absNorm_ne_zero_of_nonZeroDivisors I.1
          have hzero : Ideal.absNorm (I.1 : Ideal (𝓞 K)) = 0 := by
            change chapter03IdealNorm I.1 = 0
            exact I.2
          exact hne hzero⟩
      let e : Empty ≃ {I : Chapter03IntegralIdeal K | chapter03IdealNorm I = 0} :=
        (@Equiv.equivEmpty _ hEmpty).symm
      rw [← e.tsum_eq]
      simp [LSeries.term_zero]
    · have hfin : {I : Chapter03IntegralIdeal K | chapter03IdealNorm I = n}.Finite :=
        (chapter03_nonzero_integral_ideals_bounded_norm_finite K n).subset
          (fun I hI => le_of_eq hI)
      let hFintype : Fintype {I : Chapter03IntegralIdeal K | chapter03IdealNorm I = n} :=
        hfin.fintype
      have hconst (I : {I : Chapter03IntegralIdeal K | chapter03IdealNorm I = n}) :
          chapter03IdealTerm s I.1 = (n : ℂ) ^ (-s) := by
        change (chapter03IdealNorm I.1 : ℂ) ^ (-s) = (n : ℂ) ^ (-s)
        rw [I.2]
      have hI0 (I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}) :
          I.1 ∈ (Ideal (𝓞 K))⁰ := by
        rw [mem_nonZeroDivisors_iff_ne_zero]
        intro hzero
        apply hn
        simpa [hzero] using I.2.symm
      let e : {J : Chapter03IntegralIdeal K | chapter03IdealNorm J = n} ≃
          {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
        { toFun := fun J =>
            ⟨(J.1 : Ideal (𝓞 K)), by
              exact J.2⟩
          invFun := fun I =>
            ⟨⟨I.1, hI0 I⟩, by
              change chapter03IdealNorm ⟨I.1, hI0 I⟩ = n
              exact I.2⟩
          left_inv := by intro J; rfl
          right_inv := by intro I; rfl }
      have hcard' :
          (@Finset.univ {J : Chapter03IntegralIdeal K |
            chapter03IdealNorm J = n} hFintype).card =
            Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} := by
        change @Fintype.card _ hFintype = _
        simpa only [Nat.card_eq_fintype_card] using Nat.card_congr e
      rw [@tsum_fintype _ _ _ _ _ _ hFintype]
      simp_rw [hconst]
      rw [Finset.sum_const, nsmul_eq_mul]
      rw [LSeries.term_of_ne_zero hn]
      simp [f, hcard', Complex.cpow_neg]
      rw [div_eq_mul_inv]
  let S : ℕ → Set (Chapter03IntegralIdeal K) := fun n =>
    {I : Chapter03IntegralIdeal K | chapter03IdealNorm I = n}
  have hpart (I : Chapter03IntegralIdeal K) : ∃! n, I ∈ S n := by
    refine ⟨chapter03IdealNorm I, ?_, ?_⟩
    · rfl
    · intro j hj
      exact hj.symm
  let e : (Σ n, S n) ≃ Chapter03IntegralIdeal K := Set.sigmaEquiv S hpart
  have hsum_sigma :
      Summable (fun p : Σ n, S n => chapter03IdealTerm s p.2.1) := by
    convert e.summable_iff.mpr hsum using 1
    rfl
  have hsum_fiber (n : ℕ) :
      Summable (fun I : S n => chapter03IdealTerm s I.1) := by
    have hfin : (S n).Finite :=
      (chapter03_nonzero_integral_ideals_bounded_norm_finite K n).subset
        (fun I hI => le_of_eq hI)
    exact @Summable.of_finite _ _ _ _ _ hfin _ _
  calc
    chapter03DedekindZeta K s = LSeries f s := rfl
    _ = ∑' n : ℕ, LSeries.term f s n := rfl
    _ = ∑' n : ℕ, ∑' I : S n, chapter03IdealTerm s I.1 := by
      apply tsum_congr
      intro n
      exact (hfiber n).symm
    _ = ∑' p : Σ n, S n, chapter03IdealTerm s p.2.1 := by
      symm
      exact hsum_sigma.tsum_sigma' hsum_fiber
    _ = ∑' I : Chapter03IntegralIdeal K, chapter03IdealTerm s I := by
      exact e.tsum_eq _
    _ = chapter03IdealSeries K s := rfl

theorem chapter03_ideal_series_summable
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    Summable (fun I : Chapter03IntegralIdeal K => chapter03IdealTerm s I) := by
  exact (chapter03_ideal_series_norm_summable_aux K hs).of_norm

theorem chapter03_ideal_series_absolutely_summable
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    Summable (fun I : Chapter03IntegralIdeal K => ‖chapter03IdealTerm s I‖) := by
  exact chapter03_ideal_series_norm_summable_aux K hs

theorem chapter03_ideal_series_summable_uniformly_on
    (K : Type*) [Field K] [NumberField K] (ε : ℝ) (hε : 0 < ε) :
    SummableUniformlyOn
      (fun I : Chapter03IntegralIdeal K =>
        fun s : ℂ => chapter03IdealTerm s I)
      (chapter03EulerHalfPlaneClosed ε) := by
  let s₀ : ℂ := (1 + ε : ℝ)
  have hs₀ : s₀ ∈ chapter03EulerHalfPlane := by
    change (1 : ℝ) < 1 + ε
    linarith
  have hsum₀ :
      Summable (fun I : Chapter03IntegralIdeal K => ‖chapter03IdealTerm s₀ I‖) :=
    chapter03_ideal_series_norm_summable_aux K hs₀
  apply HasSumUniformlyOn.summableUniformlyOn
  rw [hasSumUniformlyOn_iff_tendstoUniformlyOn]
  apply tendstoUniformlyOn_tsum hsum₀
  intro I s hs
  have hI : 0 < chapter03IdealNorm I :=
    Nat.pos_of_ne_zero (Ideal.absNorm_ne_zero_of_nonZeroDivisors I)
  change ‖(chapter03IdealNorm I : ℂ) ^ (-s)‖ ≤
    ‖(chapter03IdealNorm I : ℂ) ^ (-s₀)‖
  apply Complex.norm_natCast_cpow_le_norm_natCast_cpow_of_pos hI
  change -s.re ≤ -s₀.re
  change -s.re ≤ -(1 + ε)
  exact neg_le_neg hs

theorem chapter03_ideal_series_norm_summable_uniformly_on
    (K : Type*) [Field K] [NumberField K] (ε : ℝ) (hε : 0 < ε) :
    SummableUniformlyOn
      (fun I : Chapter03IntegralIdeal K =>
        fun s : ℂ => ‖chapter03IdealTerm s I‖)
      (chapter03EulerHalfPlaneClosed ε) := by
  let s₀ : ℂ := (1 + ε : ℝ)
  have hs₀ : s₀ ∈ chapter03EulerHalfPlane := by
    change (1 : ℝ) < 1 + ε
    linarith
  have hsum₀ :
      Summable (fun I : Chapter03IntegralIdeal K => ‖chapter03IdealTerm s₀ I‖) :=
    chapter03_ideal_series_norm_summable_aux K hs₀
  apply HasSumUniformlyOn.summableUniformlyOn
  rw [hasSumUniformlyOn_iff_tendstoUniformlyOn]
  apply tendstoUniformlyOn_tsum hsum₀
  intro I s hs
  have hI : 0 < chapter03IdealNorm I :=
    Nat.pos_of_ne_zero (Ideal.absNorm_ne_zero_of_nonZeroDivisors I)
  have hbound :
      ‖(chapter03IdealNorm I : ℂ) ^ (-s)‖ ≤
        ‖(chapter03IdealNorm I : ℂ) ^ (-s₀)‖ := by
    apply Complex.norm_natCast_cpow_le_norm_natCast_cpow_of_pos hI
    change -s.re ≤ -s₀.re
    change -s.re ≤ -(1 + ε)
    exact neg_le_neg hs
  change ‖‖(chapter03IdealNorm I : ℂ) ^ (-s)‖‖ ≤
    ‖(chapter03IdealNorm I : ℂ) ^ (-s₀)‖
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hbound

theorem chapter03_ideal_series_derivative_summable_uniformly_on
    (K : Type*) [Field K] [NumberField K] (ε : ℝ) (hε : 0 < ε) :
    SummableUniformlyOn
      (fun I : Chapter03IntegralIdeal K =>
        fun s : ℂ => chapter03IdealTermDerivative s I)
      (chapter03EulerHalfPlaneClosed ε) := by
  let s₀ : ℂ := (1 + ε / 2 : ℝ)
  have hs₀ : s₀ ∈ chapter03EulerHalfPlane := by
    change (1 : ℝ) < 1 + ε / 2
    linarith
  let g : Chapter03IntegralIdeal K → ℝ := fun I =>
    (ε / 2)⁻¹ * ‖chapter03IdealTerm s₀ I‖
  have hlog (I : Chapter03IntegralIdeal K) :
      ‖(Real.log (chapter03IdealNorm I : ℝ) : ℂ)‖ ≤
        (chapter03IdealNorm I : ℝ) ^ (ε / 2) / (ε / 2) := by
    simpa only [Complex.norm_real,
      Real.norm_of_nonneg (Real.log_natCast_nonneg _)] using
      (Real.log_natCast_le_rpow_div (chapter03IdealNorm I) (by linarith [hε] : 0 < ε / 2))
  have hsumg : Summable g := by
    simpa [g] using
      (chapter03_ideal_series_norm_summable_aux K hs₀).mul_left (ε / 2)⁻¹
  apply HasSumUniformlyOn.summableUniformlyOn
  rw [hasSumUniformlyOn_iff_tendstoUniformlyOn]
  apply tendstoUniformlyOn_tsum hsumg
  intro I s hs
  change (1 : ℝ) + ε ≤ s.re at hs
  have hI : 0 < chapter03IdealNorm I :=
    Nat.pos_of_ne_zero (Ideal.absNorm_ne_zero_of_nonZeroDivisors I)
  have hpow :
      (chapter03IdealNorm I : ℝ) ^ (ε / 2) *
          ‖(chapter03IdealNorm I : ℂ) ^ (-s)‖ ≤
        ‖(chapter03IdealNorm I : ℂ) ^ (-s₀)‖ := by
    rw [Complex.norm_natCast_cpow_of_pos hI,
      Complex.norm_natCast_cpow_of_pos hI]
    rw [← Real.rpow_add (by positivity)]
    apply Real.rpow_le_rpow_of_exponent_le
    · exact_mod_cast (show 1 ≤ chapter03IdealNorm I from Nat.succ_le_iff.mp hI)
    · dsimp [s₀]
      linarith [hs]
  change ‖-(Real.log (chapter03IdealNorm I : ℝ) : ℂ) *
      (chapter03IdealNorm I : ℂ) ^ (-s)‖ ≤ g I
  rw [norm_mul, norm_neg]
  calc
    ‖(Real.log (chapter03IdealNorm I : ℝ) : ℂ)‖ *
          ‖(chapter03IdealNorm I : ℂ) ^ (-s)‖ ≤
        ((chapter03IdealNorm I : ℝ) ^ (ε / 2) / (ε / 2)) *
          ‖(chapter03IdealNorm I : ℂ) ^ (-s)‖ :=
      mul_le_mul_of_nonneg_right (hlog I) (norm_nonneg _)
    _ = (ε / 2)⁻¹ *
          ((chapter03IdealNorm I : ℝ) ^ (ε / 2) *
            ‖(chapter03IdealNorm I : ℂ) ^ (-s)‖) := by ring
    _ ≤ (ε / 2)⁻¹ * ‖(chapter03IdealTerm s₀ I)‖ := by
      apply mul_le_mul_of_nonneg_left hpow
      positivity
    _ = g I := by rfl

theorem chapter03_euler_half_plane_isOpen :
    IsOpen chapter03EulerHalfPlane := by
  exact isOpen_lt continuous_const Complex.continuous_re

theorem chapter03_euler_half_plane_closed_subset
    {ε : ℝ} (hε : 0 < ε) :
    chapter03EulerHalfPlaneClosed ε ⊆ chapter03EulerHalfPlane := by
  intro s hs
  exact lt_of_lt_of_le (show (1 : ℝ) < 1 + ε by linarith [hε]) hs

theorem chapter03_ideal_term_hasDerivAt
    (K : Type*) [Field K] [NumberField K]
    (I : Chapter03IntegralIdeal K) (s : ℂ) :
    HasDerivAt (fun z : ℂ => chapter03IdealTerm z I)
      (chapter03IdealTermDerivative s I) s := by
  change HasDerivAt (fun z : ℂ => (chapter03IdealNorm I : ℂ) ^ (-z))
    (-(Real.log (chapter03IdealNorm I : ℝ) : ℂ) *
      (chapter03IdealNorm I : ℂ) ^ (-s)) s
  have hI : chapter03IdealNorm I ≠ 0 := by
    exact Ideal.absNorm_ne_zero_of_nonZeroDivisors I
  simpa [Complex.cpow_neg, mul_comm, mul_left_comm, mul_assoc] using
    (hasDerivAt_neg s).const_cpow (c := (chapter03IdealNorm I : ℂ))
      (Or.inl (by exact_mod_cast hI))

private theorem chapter03_coefficient_lseries_summable_aux
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    LSeriesSummable
      (fun n : ℕ => Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}) s := by
  classical
  have hcard (n : ℕ) :
      Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} =
        ∑ k ∈ Finset.Icc 1 n,
          Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} := by
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by
        simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq
        (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  let A : ℕ → ℝ := fun n =>
    Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n}
  let f : ℕ → ℂ := fun n =>
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}
  have hpartial : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ‖f k‖) =
      fun n => A n := by
    funext n
    simp [f, A]
    rw [hcard, Nat.cast_sum]
  have hlim := (Ideal.tendsto_norm_le_div_atTop₀ K).comp
    (tendsto_natCast_atTop_atTop)
  have hO : A =O[Filter.atTop] (fun n : ℕ => (n : ℝ)) := by
    apply Asymptotics.isBigO_of_div_tendsto_nhds
    · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      intro hn0
      exact False.elim ((Nat.cast_ne_zero.mpr hn.ne') hn0)
    · change Filter.Tendsto (fun n : ℕ => A n / (n : ℝ)) Filter.atTop _
      simpa [A, Function.comp_def] using hlim
  have hsumO :
      (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ‖f k‖) =O[Filter.atTop]
        (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
    rw [hpartial]
    simpa [Real.rpow_one] using hO
  apply LSeriesSummable_of_sum_norm_bigO (r := 1) hsumO
  · norm_num
  · exact hs

theorem chapter03_dedekind_zeta_differentiableOn
    (K : Type*) [Field K] [NumberField K] :
    DifferentiableOn ℂ (chapter03DedekindZeta K) chapter03EulerHalfPlane := by
  let f : ℕ → ℂ := fun n =>
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}
  have ha : LSeries.abscissaOfAbsConv f ≤ (1 : ℝ) := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    intro y hy
    have hy' : (y : ℂ) ∈ chapter03EulerHalfPlane := by
      change (1 : ℝ) < y
      exact hy
    simpa [f] using chapter03_coefficient_lseries_summable_aux K hy'
  intro s hs
  change DifferentiableWithinAt ℂ (LSeries f) chapter03EulerHalfPlane s
  have hs' : (1 : ℝ) < s.re := hs
  have hs'' : (1 : EReal) < (s.re : EReal) := by exact_mod_cast hs'
  exact (LSeries_hasDerivAt (s := s) (ha.trans_lt hs'')).differentiableAt.differentiableWithinAt

theorem chapter03_dedekind_zeta_hasDerivAt_of_euler_half_plane
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    HasDerivAt (chapter03DedekindZeta K)
      (∑' I : Chapter03IntegralIdeal K, chapter03IdealTermDerivative s I) s := by
  classical
  let f : ℕ → ℂ := fun n =>
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}
  have ha : LSeries.abscissaOfAbsConv f ≤ (1 : ℝ) := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    intro y hy
    have hy' : (y : ℂ) ∈ chapter03EulerHalfPlane := by
      change (1 : ℝ) < y
      exact hy
    simpa [f] using chapter03_coefficient_lseries_summable_aux K hy'
  have hs' : (1 : ℝ) < s.re := hs
  have hε : 0 < (s.re - 1) / 2 := by linarith [hs']
  have hsclosed : s ∈ chapter03EulerHalfPlaneClosed ((s.re - 1) / 2) := by
    change (1 : ℝ) + (s.re - 1) / 2 ≤ s.re
    linarith
  have hsumD : Summable
      (fun I : Chapter03IntegralIdeal K => chapter03IdealTermDerivative s I) :=
    (chapter03_ideal_series_derivative_summable_uniformly_on K
      ((s.re - 1) / 2) hε).summable hsclosed
  let S : ℕ → Set (Chapter03IntegralIdeal K) := fun n =>
    {I : Chapter03IntegralIdeal K | chapter03IdealNorm I = n}
  have hpart (I : Chapter03IntegralIdeal K) : ∃! n, I ∈ S n := by
    refine ⟨chapter03IdealNorm I, ?_, ?_⟩
    · rfl
    · intro j hj
      exact hj.symm
  let e : (Σ n, S n) ≃ Chapter03IntegralIdeal K := Set.sigmaEquiv S hpart
  have hsum_sigma :
      Summable (fun p : Σ n, S n => chapter03IdealTermDerivative s p.2.1) := by
    convert e.summable_iff.mpr hsumD using 1
    rfl
  have hsum_fiber (n : ℕ) :
      Summable (fun I : S n => chapter03IdealTermDerivative s I.1) := by
    have hfin : (S n).Finite :=
      (chapter03_nonzero_integral_ideals_bounded_norm_finite K n).subset
        (fun I hI => le_of_eq hI)
    exact @Summable.of_finite _ _ _ _ _ hfin _ _
  have hfiber (n : ℕ) :
      (∑' I : S n, chapter03IdealTermDerivative s I.1) =
        -LSeries.term (LSeries.logMul f) s n := by
    by_cases hn : n = 0
    · subst n
      let hEmpty : IsEmpty (S 0) :=
        ⟨fun I => by
          have hne := Ideal.absNorm_ne_zero_of_nonZeroDivisors I.1
          exact hne I.2⟩
      let e₀ : Empty ≃ S 0 := (@Equiv.equivEmpty _ hEmpty).symm
      rw [← e₀.tsum_eq]
      simp [LSeries.term_zero]
    · have hfin : (S n).Finite :=
        (chapter03_nonzero_integral_ideals_bounded_norm_finite K n).subset
          (fun I hI => le_of_eq hI)
      let hFintype : Fintype (S n) := hfin.fintype
      have hconst (I : S n) :
          chapter03IdealTermDerivative s I.1 =
            -(Real.log (n : ℝ) : ℂ) * (n : ℂ) ^ (-s) := by
        change -(Real.log (chapter03IdealNorm I.1 : ℝ) : ℂ) *
          (chapter03IdealNorm I.1 : ℂ) ^ (-s) = _
        rw [I.2]
      have hI0 (I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}) :
          I.1 ∈ (Ideal (𝓞 K))⁰ := by
        rw [mem_nonZeroDivisors_iff_ne_zero]
        intro hzero
        apply hn
        simpa [hzero] using I.2.symm
      let e' : S n ≃ {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
        { toFun := fun J =>
            ⟨(J.1 : Ideal (𝓞 K)), by exact J.2⟩
          invFun := fun I =>
            ⟨⟨I.1, hI0 I⟩, by
              change chapter03IdealNorm ⟨I.1, hI0 I⟩ = n
              exact I.2⟩
          left_inv := by intro J; rfl
          right_inv := by intro I; rfl }
      have hcard' :
          (@Finset.univ (S n) hFintype).card =
            Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} := by
        change @Fintype.card _ hFintype = _
        simpa only [Nat.card_eq_fintype_card] using Nat.card_congr e'
      rw [@tsum_fintype _ _ _ _ _ _ hFintype]
      simp_rw [hconst]
      rw [Finset.sum_const, nsmul_eq_mul]
      rw [LSeries.term_of_ne_zero hn]
      simp [f, LSeries.logMul, hcard', Complex.cpow_neg, Complex.natCast_log]
      ring
  calc
    (∑' I : Chapter03IntegralIdeal K, chapter03IdealTermDerivative s I) =
        ∑' p : Σ n, S n, chapter03IdealTermDerivative s p.2.1 := by
      exact (e.tsum_eq _).symm
    _ = ∑' n : ℕ, ∑' I : S n, chapter03IdealTermDerivative s I.1 :=
      hsum_sigma.tsum_sigma' hsum_fiber
    _ = ∑' n : ℕ, -LSeries.term (LSeries.logMul f) s n := by
      apply tsum_congr
      exact hfiber
    _ = -LSeries (LSeries.logMul f) s := by
      rw [LSeries]
      rw [← tsum_neg]
  change HasDerivAt (LSeries f) _ s
  convert LSeries_hasDerivAt (s := s)
    (ha.trans_lt (by exact_mod_cast hs')) using 1

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03
