import LastLib.Book04AdelesAndIdeles.Chapter05.Dependencies
import LastLib.Book04AdelesAndIdeles.Chapter04.Section03NeighborhoodsAsLocalSpecifications

namespace LastLib.Book04AdelesAndIdeles.Chapter05

open LastLib.Book04AdelesAndIdeles.Chapter01
open LastLib.Book04AdelesAndIdeles.Chapter04

noncomputable section

open NumberField
open scoped Topology nonZeroDivisors

/-! ## 5.5. Weak approximation at arbitrary places -/

def chapter05SelectedFinitePlaces
    (K : Type*) [Field K] [NumberField K]
  (T : Finset (Chapter04Place K)) : Finset (Chapter04FinitePlace K) := by
  classical
  exact T.toLeft

def chapter05SelectedArchimedeanPlaces
    (K : Type*) [Field K] [NumberField K]
  (T : Finset (Chapter04Place K)) : Finset (Chapter04InfinitePlace K) := by
  classical
  exact T.toRight

def chapter05FiniteCorrectionSet
    (K : Type*) [Field K] [NumberField K]
    (S : Finset (Chapter04FinitePlace K))
    (m : ∀ _v : S, ℤ) : Set K :=
  chapter05FiniteDiagonal K ⁻¹'
    chapter04FinitePrecisionNeighborhood K S m

private theorem chapter05_fractionalIdeal_le_of_count_le
    (K : Type*) [Field K] [NumberField K]
    {A B : FractionalIdeal (𝓞 K)⁰ K}
    (hA : A ≠ 0) (hB : B ≠ 0)
    (hcount : ∀ v : Chapter04FinitePlace K,
      FractionalIdeal.count K v A ≤ FractionalIdeal.count K v B) :
    B ≤ A := by
  let L := B * A⁻¹
  have hL : L ≠ 0 := mul_ne_zero hB (inv_ne_zero hA)
  have hcountL : ∀ v : Chapter04FinitePlace K,
      FractionalIdeal.count K v L =
        FractionalIdeal.count K v B - FractionalIdeal.count K v A := by
    intro v
    dsimp [L]
    rw [FractionalIdeal.count_mul K v hB (inv_ne_zero hA),
      FractionalIdeal.count_inv]
    ring
  have hL_nonneg : ∀ v : Chapter04FinitePlace K,
      0 ≤ FractionalIdeal.count K v L := by
    intro v
    rw [hcountL]
    exact sub_nonneg.mpr (hcount v)
  have hfinite : Function.HasFiniteMulSupport
      (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
        FractionalIdeal.count K v L) := by
    rw [Function.HasFiniteMulSupport]
    refine (Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors L)).subset ?_
    intro v hv
    rw [Function.mem_mulSupport] at hv
    intro hzero
    apply hv
    simp [hzero]
  have hLle : L ≤ 1 := by
    rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hL]
    calc
      (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
          (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
            FractionalIdeal.count K v L) ≤
          ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
            (1 : FractionalIdeal (𝓞 K)⁰ K) := by
        refine finprod_le_finprod' hfinite ?_ ?_
        · simp [Function.HasFiniteMulSupport]
        · intro v
          exact zpow_le_one₀
            (bot_lt_iff_ne_bot.mpr (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot))
            FractionalIdeal.coeIdeal_le_one (hL_nonneg v)
      _ = 1 := finprod_one
  have hmul := mul_le_mul_left hLle A
  dsimp [L] at hmul
  simpa [mul_assoc, hA] using hmul

private theorem chapter05_finite_diagonal_preimage_fractional_ideal
    (K : Type*) [Field K] [NumberField K]
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) :
    chapter05FiniteDiagonal K ⁻¹'
        chapter04FractionalIdealCompletion K I = (I : Set K) := by
  ext c
  change chapter05FiniteDiagonal K c ∈ chapter04FractionalIdealCompletion K I ↔
    c ∈ (I : Set K)
  by_cases hc : c = 0
  · subst c
    constructor
    · intro _
      exact I.zero_mem
    · intro _
      change ∀ v : Chapter04FinitePlace K,
        Valued.v ((0 : K) : v.adicCompletion K) ≤
          WithZero.exp (-(FractionalIdeal.count K v I))
      intro v
      simp
  have hspan : FractionalIdeal.spanSingleton (𝓞 K)⁰ c ≠ 0 := by
    exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr hc
  constructor
  · intro hcI
    change ∀ v : Chapter04FinitePlace K,
      Valued.v (((c : K) : v.adicCompletion K)) ≤
        WithZero.exp (-(FractionalIdeal.count K v I)) at hcI
    have hcount : ∀ v : Chapter04FinitePlace K,
        FractionalIdeal.count K v I ≤ chapter01Order v c := by
      intro v
      have hv := hcI v
      rw [chapter01_completion_valuation_agrees_with_global] at hv
      have hval : v.valuation K c =
          WithZero.exp (-(chapter01Order v c)) := by
        simpa [chapter01Order,
          LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent] using
          (LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent_valuation
            v hc)
      rw [hval, WithZero.exp_le_exp] at hv
      exact (neg_le_neg_iff.mp hv)
    apply FractionalIdeal.spanSingleton_le_iff_mem.mp
      (chapter05_fractionalIdeal_le_of_count_le K hI hspan (by
        intro v
        exact hcount v))
  · intro hcI
    have hspan_le : FractionalIdeal.spanSingleton (𝓞 K)⁰ c ≤ I :=
      FractionalIdeal.spanSingleton_le_iff_mem.mpr hcI
    have hcount : ∀ v : Chapter04FinitePlace K,
        FractionalIdeal.count K v I ≤ chapter01Order v c := by
      intro v
      exact FractionalIdeal.count_mono K v hspan hspan_le
    change ∀ v : Chapter04FinitePlace K,
      Valued.v (((c : K) : v.adicCompletion K)) ≤
        WithZero.exp (-(FractionalIdeal.count K v I))
    intro v
    have hval : v.valuation K c =
        WithZero.exp (-(chapter01Order v c)) := by
      simpa [chapter01Order,
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent] using
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent_valuation
          v hc)
    rw [chapter01_completion_valuation_agrees_with_global, hval,
      WithZero.exp_le_exp]
    exact neg_le_neg (hcount v)

theorem chapter05_finite_correction_set_is_fractional_ideal
    (K : Type*) [Field K] [NumberField K]
    (S : Finset (Chapter04FinitePlace K)) (m : ∀ _v : S, ℤ) :
    ∃ I : FractionalIdeal (𝓞 K)⁰ K,
      I ≠ 0 ∧ chapter05FiniteCorrectionSet K S m = (I : Set K) := by
  classical
  let exps : Chapter04FinitePlace K → ℤ := fun v =>
    if hv : v ∈ S then m ⟨v, hv⟩ else 0
  have h_exps : ∀ᶠ v : Chapter04FinitePlace K in Filter.cofinite,
      exps v = 0 := by
    filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv
    have hv' : v ∉ S := by simpa using hv
    simp [exps, hv']
  let I : FractionalIdeal (𝓞 K)⁰ K :=
    ∏ᶠ v : Chapter04FinitePlace K,
      (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ exps v
  have hI : I ≠ 0 := by
    apply finprod_ne_zero
    intro v
    have hv0 : (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot
    exact zpow_ne_zero _ hv0
  have hcount : ∀ v : Chapter04FinitePlace K,
      FractionalIdeal.count K v I = exps v := by
    intro v
    simpa [I] using
      (FractionalIdeal.count_finprod (R := 𝓞 K) K v exps h_exps)
  have hcompletion :
      chapter04FinitePrecisionNeighborhood K S m =
        chapter04FractionalIdealCompletion K I := by
    ext x
    constructor
    · intro hx
      change (∀ v : S,
          x v.1 ∈ chapter01LocalNeighborhood v.1 (m v)) ∧
        (∀ v : Chapter04FinitePlace K, v ∉ S →
          x v ∈ chapter04FiniteLocalIntegerSet K v) at hx
      change ∀ v : Chapter04FinitePlace K,
        Valued.v (x v) ≤
          WithZero.exp (-(FractionalIdeal.count K v I))
      intro v
      by_cases hv : v ∈ S
      · rw [hcount v]
        have hxv := hx.1 ⟨v, hv⟩
        change Valued.v (x v) ≤ WithZero.exp (-m ⟨v, hv⟩) at hxv
        simpa [exps, hv] using hxv
      · rw [hcount v]
        simp only [exps, dif_neg hv, neg_zero, WithZero.exp_zero]
        exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
          (𝓞 K) K v).1 (hx.2 v hv)
    · intro hx
      change ∀ v : Chapter04FinitePlace K,
        Valued.v (x v) ≤
          WithZero.exp (-(FractionalIdeal.count K v I)) at hx
      change (∀ v : S,
          x v.1 ∈ chapter01LocalNeighborhood v.1 (m v)) ∧
        (∀ v : Chapter04FinitePlace K, v ∉ S →
          x v ∈ chapter04FiniteLocalIntegerSet K v)
      constructor
      · intro v
        have hxv := hx v.1
        rw [hcount v.1] at hxv
        change Valued.v (x v.1) ≤ WithZero.exp (-exps v.1) at hxv
        change Valued.v (x v.1) ≤ WithZero.exp (-m v)
        simpa [exps, v.2] using hxv
      · intro v hv
        have hxv := hx v
        rw [hcount v] at hxv
        apply (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
          (𝓞 K) K v).2
        change Valued.v (x v) ≤ 1
        simpa only [exps, dif_neg hv, neg_zero, WithZero.exp_zero] using hxv
  refine ⟨I, hI, ?_⟩
  change chapter05FiniteDiagonal K ⁻¹'
      chapter04FinitePrecisionNeighborhood K S m = (I : Set K)
  rw [hcompletion]
  exact chapter05_finite_diagonal_preimage_fractional_ideal K I hI

/-! An auxiliary rational prime is characterized canonically by vanishing
finite-place order at each selected prime. -/

def chapter05AuxiliaryPrimeAvoids
    (K : Type*) [Field K] [NumberField K]
    (S : Finset (Chapter04FinitePlace K)) (ell : ℕ) : Prop :=
  Nat.Prime ell ∧
    ∀ v : S,
      LastLib.Book04AdelesAndIdeles.Chapter01.chapter01Order v.1
        (ell : K) = 0

theorem chapter05_exists_auxiliary_prime
    (K : Type*) [Field K] [NumberField K]
    (S : Finset (Chapter04FinitePlace K)) :
    ∃ ell : ℕ, chapter05AuxiliaryPrimeAvoids K S ell := by
  classical
  let p : ∀ v : S, ℕ := fun v =>
    (v.1.asIdeal.under ℤ).absNorm
  have hp : ∀ v : S, Nat.Prime (p v) := by
    intro v
    have hprime : Prime (v.1.asIdeal.under ℤ) := by
      apply Ideal.prime_of_isPrime
      · exact Ideal.under_ne_bot ℤ v.1.ne_bot
      · infer_instance
    exact (Int.prime_absNorm _).2 hprime
  let N := (∑ v : S, p v) + 1
  obtain ⟨ell, hellN, hellprime⟩ := Nat.exists_infinite_primes N
  refine ⟨ell, hellprime, ?_⟩
  intro v
  have hp_le : p v ≤ ∑ w : S, p w := by
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
  have hp_lt : p v < ell := by
    exact lt_of_le_of_lt hp_le (lt_of_lt_of_le (Nat.lt_succ_self _) hellN)
  have hell_notmem : (ell : 𝓞 K) ∉ v.1.asIdeal := by
    intro hmem
    have hmem' : ((ell : ℤ) : 𝓞 K) ∈ v.1.asIdeal := by
      simpa using hmem
    have hdivZ : ((p v : ℕ) : ℤ) ∣ (ell : ℤ) := by
      exact (Int.cast_mem_ideal_iff).mp hmem'
    have hdiv : p v ∣ ell := by
      exact_mod_cast hdivZ
    have heq : ell = p v := (hellprime.dvd_iff_eq (hp v).ne_one).mp hdiv
    exact (Nat.ne_of_gt hp_lt) heq
  have hzero : chapter01Order v.1 (ell : K) = 0 := by
    simpa [chapter01Order,
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent] using
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent_primeCompl_eq_zero
        v.1 ⟨ell, hell_notmem⟩)
  exact hzero

def chapter05ScaledCorrectionSet
    (K : Type*) [Field K] [NumberField K]
    (S : Finset (Chapter04FinitePlace K)) (m : ∀ _v : S, ℤ)
    (ell s : ℕ) : Set K :=
  {c |
    ∃ d : K, d ∈ chapter05FiniteCorrectionSet K S m ∧
      c = ((ell : K)⁻¹) ^ s * d}

theorem chapter05_scaled_correction_preserves_finite_precision
    (K : Type*) [Field K] [NumberField K]
    (S : Finset (Chapter04FinitePlace K)) (m : ∀ _v : S, ℤ)
    (ell s : ℕ) (hℓ : chapter05AuxiliaryPrimeAvoids K S ell)
    {c : K} (hc : c ∈ chapter05ScaledCorrectionSet K S m ell s) :
    ∀ v : S,
      chapter05FiniteDiagonal K c v.1 ∈
        LastLib.Book04AdelesAndIdeles.Chapter01.chapter01LocalNeighborhood
          v.1 (m v) := by
  rcases hc with ⟨d, hd, rfl⟩
  intro v
  have hd' := (chapter04_mem_finitePrecisionNeighborhood_iff K S m
      (chapter05FiniteDiagonal K d)).mp hd
  have hdv := hd'.1 v
  change Valued.v (((((ell : K)⁻¹) ^ s * d : K) : v.1.adicCompletion K)) ≤
    WithZero.exp (-(m v))
  by_cases hd0 : d = 0
  · simp [hd0]
  have hell0 : (ell : K) ≠ 0 := by exact_mod_cast hℓ.1.ne_zero
  have hvalell :
      v.1.valuation K (ell : K) =
        WithZero.exp (-(chapter01Order v.1 (ell : K))) := by
    simpa [chapter01Order,
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent] using
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent_valuation
        v.1 hell0)
  have hellv : Valued.v (((ell : K) : v.1.adicCompletion K)) = 1 := by
    rw [chapter01_completion_valuation_agrees_with_global,
      hvalell, hℓ.2 v]
    simp
  have hcoe (z : K) : (z : v.1.adicCompletion K) =
      algebraMap K (v.1.adicCompletion K) z := by
    simp [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
  have hellv' :
      Valued.v (algebraMap K (v.1.adicCompletion K) (ell : K)) = 1 := by
    rw [← hcoe (ell : K)]
    exact hellv
  change Valued.v (algebraMap K (v.1.adicCompletion K)
      (((ell : K)⁻¹) ^ s * d)) ≤ WithZero.exp (-(m v))
  simp only [map_mul, map_pow, map_inv₀, hellv', inv_one, one_pow, one_mul]
  change Valued.v ((d : K) : v.1.adicCompletion K) ≤ WithZero.exp (-(m v)) at hdv
  rw [hcoe d] at hdv
  exact hdv

/-! The correction lattice is now the canonical mixed-space image of a
fractional ideal; its mesh statement is the scaled-lattice statement from the
source proof. -/

theorem chapter05_correction_lattice_mesh
    (K : Type*) [Field K] [NumberField K]
    (I : chapter01FractionalIdealGroup K) (ell : ℕ) (hℓ : 1 < ell)
    (x : chapter01MinkowskiSpace K)
    (U : Set (chapter01MinkowskiSpace K)) (hU : U ∈ 𝓝 x) :
    ∀ᶠ s : ℕ in Filter.atTop,
      ∃ c : K,
        c ∈ chapter05ScaledFractionalIdeal K I ell s ∧
          chapter01MinkowskiEmbedding K c ∈ U := by
  sorry

theorem chapter05_place_system_lattice_mesh
    (K : Type*) [Field K] [NumberField K]
    (I : chapter01FractionalIdealGroup K) (ell : ℕ) (hℓ : 1 < ell) :
    chapter05MinkowskiLatticeMesh K I ell := by
  sorry

/-!
**Theorem 5.3 (weak approximation).** For every finite list of distinct
canonical places, the diagonal map has dense image in the selected local
product.
-/
theorem chapter05_theorem_5_3_weak_approximation
    (K : Type*) [Field K] [NumberField K]
    (T : Finset (Chapter04Place K)) :
    chapter05WeakApproximationStatement K T := by
  sorry

theorem chapter05_theorem_5_3_weak_approximation_dense
    (K : Type*) [Field K] [NumberField K]
    (T : Finset (Chapter04Place K)) :
    DenseRange (chapter05DiagonalAtPlaces K T) := by
  sorry

theorem chapter05_weak_approximation_iff_dense_selected_diagonal
    (K : Type*) [Field K] [NumberField K]
    (T : Finset (Chapter04Place K)) :
    chapter05WeakApproximationStatement K T ↔
      DenseRange (chapter05DiagonalAtPlaces K T) := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter05
