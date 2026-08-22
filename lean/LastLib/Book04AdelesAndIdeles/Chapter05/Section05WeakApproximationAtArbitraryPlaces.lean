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
  exact chapter05_minkowski_correction_lattice_mesh K I ell hℓ hℓ x U hU

theorem chapter05_place_system_lattice_mesh
    (K : Type*) [Field K] [NumberField K]
    (I : chapter01FractionalIdealGroup K) (ell : ℕ) (hℓ : 1 < ell) :
    chapter05MinkowskiLatticeMesh K I ell := by
  exact chapter05_minkowski_correction_lattice_mesh K I ell hℓ

/-!
**Theorem 5.3 (weak approximation).** For every finite list of distinct
canonical places, the diagonal map has dense image in the selected local
product.
-/
theorem chapter05_theorem_5_3_weak_approximation
    (K : Type*) [Field K] [NumberField K]
    (T : Finset (Chapter04Place K)) :
    chapter05WeakApproximationStatement K T := by
  classical
  intro x W hW
  let S : Finset (Chapter04FinitePlace K) :=
    chapter05SelectedFinitePlaces K T
  let A : Finset (Chapter04InfinitePlace K) :=
    chapter05SelectedArchimedeanPlaces K T
  have hS_mem (v : Chapter04FinitePlace K) (hv : v ∈ S) :
      Sum.inl v ∈ T := by
    exact (Finset.mem_toLeft.mp hv)
  have hA_mem (w : Chapter04InfinitePlace K) (hw : w ∈ A) :
      Sum.inr w ∈ T := by
    exact (Finset.mem_toRight.mp hw)
  let xfin : ∀ v : Chapter04FinitePlace K, v ∈ S →
      Chapter04FiniteLocalField K v := fun v hv =>
    x ⟨Sum.inl v, hS_mem v hv⟩
  have hWlocal (v : Chapter04FinitePlace K) (hv : v ∈ S) :
      ∃ n : ℤ, ∀ z : Chapter04FiniteLocalField K v,
        chapter01LocallyClose v (xfin v hv) z n →
          z ∈ W ⟨Sum.inl v, hS_mem v hv⟩ := by
    have hmem : W ⟨Sum.inl v, hS_mem v hv⟩ ∈
        𝓝 (xfin v hv) := hW ⟨Sum.inl v, hS_mem v hv⟩
    rcases Valued.mem_nhds.mp hmem with ⟨γ, hγ⟩
    let γ' := MonoidWithZeroHom.ValueGroup₀.embedding γ.1
    refine ⟨-(WithZero.log γ' - 1), ?_⟩
    intro z hz
    apply hγ
    change Valued.v.restrict (z - xfin v hv) < γ.1
    rw [Valued.v.restrict_lt_iff_lt_embedding]
    have hz' : Valued.v (xfin v hv - z) ≤
        WithZero.exp (-(-(WithZero.log γ' - 1))) := by
      change Valued.v (xfin v hv - z) ≤
        WithZero.exp (-(-(WithZero.log γ' - 1))) at hz
      exact hz
    rw [Valuation.map_sub_swap] at hz'
    have hγ'ne : γ' ≠ 0 := by
      exact MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ
    change Valued.v (z - xfin v hv) < γ'
    rw [← WithZero.exp_log hγ'ne]
    apply lt_of_le_of_lt hz'
    rw [WithZero.exp_lt_exp]
    omega
  let mfin : ∀ v : Chapter04FinitePlace K, v ∈ S → ℤ := fun v hv =>
    Classical.choose (hWlocal v hv)
  let m : ∀ v : S, ℤ := fun v => mfin v.1 v.2
  have hm (v : Chapter04FinitePlace K) (hv : v ∈ S) :
      ∀ z : Chapter04FiniteLocalField K v,
        chapter01LocallyClose v (xfin v hv) z (mfin v hv) →
        z ∈ W ⟨Sum.inl v, hS_mem v hv⟩ := by
    exact Classical.choose_spec (hWlocal v hv)
  obtain ⟨a₀, ha₀, haout⟩ :=
    chapter01_finite_approximation K S xfin mfin
  obtain ⟨I, hI, hIset⟩ :=
    chapter05_finite_correction_set_is_fractional_ideal K S m
  have hIunit : IsUnit I := isUnit_iff_ne_zero.mpr hI
  let Iu : chapter01FractionalIdealGroup K := hIunit.unit
  have hIu : (Iu : FractionalIdeal (𝓞 K)⁰ K) = I :=
    hIunit.unit_spec
  obtain ⟨ell, hell⟩ := chapter05_exists_auxiliary_prime K S
  have hell' : 1 < ell := hell.1.one_lt
  let z : Chapter04InfiniteAdeleRing K := fun w =>
    if hw : Sum.inr w ∈ T then
      x ⟨Sum.inr w, hw⟩ - chapter05LocalEmbedding K (Sum.inr w) a₀
    else 0
  let B : ∀ w : Chapter04InfinitePlace K, Set w.Completion := fun w =>
    if hw : w ∈ A then
      {y | y + algebraMap K w.Completion a₀ ∈
        W ⟨Sum.inr w, hA_mem w hw⟩}
    else Set.univ
  let V : Set (Chapter04InfiniteAdeleRing K) :=
    Set.pi (A : Set (Chapter04InfinitePlace K)) B
  have hV : V ∈ 𝓝 z := by
    dsimp only [V]
    have hV' :
        (Set.pi (A : Set (Chapter04InfinitePlace K)) B :
          Set (∀ w : Chapter04InfinitePlace K, w.Completion)) ∈
        @nhds (∀ w : Chapter04InfinitePlace K, w.Completion)
          Pi.topologicalSpace (z : ∀ w : Chapter04InfinitePlace K, w.Completion) := by
      rw [nhds_pi, Filter.mem_pi']
      refine ⟨A, B, ?_, ?_⟩
      · intro w
        by_cases hw : w ∈ A
        · have hcont : ContinuousAt
              (fun y : w.Completion =>
                y + algebraMap K w.Completion a₀) (z w) :=
            continuousAt_id.add continuousAt_const
          have hz : z w + algebraMap K w.Completion a₀ =
              x ⟨Sum.inr w, hA_mem w hw⟩ := by
            simp [z, hA_mem w hw, chapter05LocalEmbedding]
            rw [← NumberField.InfinitePlace.Completion.algebraMap_apply w a₀]
            exact sub_add_cancel _ _
          have hW0 := hW ⟨Sum.inr w, hA_mem w hw⟩
          change (W ⟨Sum.inr w, hA_mem w hw⟩ : Set w.Completion) ∈
              @nhds w.Completion _
                (x ⟨Sum.inr w, hA_mem w hw⟩) at hW0
          have hW' :
              (W ⟨Sum.inr w, hA_mem w hw⟩ : Set w.Completion) ∈
                𝓝 (z w + algebraMap K w.Completion a₀) := by
            simpa only [hz] using hW0
          have hpre := hcont.preimage_mem_nhds hW'
          change {y : w.Completion |
              y + algebraMap K w.Completion a₀ ∈
                W ⟨Sum.inr w, hA_mem w hw⟩} ∈ 𝓝 (z w) at hpre
          simpa [B, z, hw, hA_mem w hw, chapter05LocalEmbedding,
            Set.preimage_ofPred_eq] using hpre
        · simp [B, hw]
      · exact Set.Subset.rfl
    exact hV'
  have hcont' : Continuous
      ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm :
        chapter01MinkowskiSpace K → Chapter04InfiniteAdeleRing K) := by
    let e : Chapter04InfiniteAdeleRing K ≃ₜ chapter01MinkowskiSpace K :=
      (Homeomorph.piEquivPiSubtypeProd
          (fun (v : NumberField.InfinitePlace K) =>
            NumberField.InfinitePlace.IsReal v)
          (fun (v : NumberField.InfinitePlace K) => v.Completion)).trans
        (Homeomorph.prodCongr
          (Homeomorph.piCongrRight
            (fun w : {w : NumberField.InfinitePlace K //
                NumberField.InfinitePlace.IsReal w} =>
              (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal
                w.2).toHomeomorph))
          ((Homeomorph.piCongrRight
              (fun w : {w : NumberField.InfinitePlace K //
                  ¬ NumberField.InfinitePlace.IsReal w} =>
                (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex
                  (NumberField.InfinitePlace.not_isReal_iff_isComplex.1 w.2)).toHomeomorph)).trans
            (Homeomorph.piCongrLeft
              (Y := fun _ : {w : NumberField.InfinitePlace K //
                  NumberField.InfinitePlace.IsComplex w} => ℂ)
              (Equiv.subtypeEquivRight
                (fun _ => NumberField.InfinitePlace.not_isReal_iff_isComplex)))))
    exact e.symm.continuous
  let U : Set (chapter01MinkowskiSpace K) :=
    (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm ⁻¹' V
  have hU : U ∈ 𝓝
      (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K z) := by
    have ht : Filter.Tendsto
        ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm :
          chapter01MinkowskiSpace K → Chapter04InfiniteAdeleRing K)
        (𝓝 (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K z))
        (𝓝 z) := by
      have ht0 := hcont'.continuousAt
        (x := NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K z)
      change Filter.Tendsto
        ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm :
          chapter01MinkowskiSpace K → Chapter04InfiniteAdeleRing K)
        (𝓝 (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K z))
        (𝓝 ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm
          (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K z))) at ht0
      simpa only [RingEquiv.symm_apply_apply] using ht0
    simpa [U] using ht hV
  obtain ⟨s, hs⟩ :=
    (chapter05_correction_lattice_mesh K Iu ell hell'
      (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K z) U hU).exists
  rcases hs with ⟨c, hc, hcU⟩
  have hcV :
      (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm
          (chapter01MinkowskiEmbedding K c) ∈ V := hcU
  have hpres : c ∈ chapter05ScaledCorrectionSet K S m ell s := by
    rcases hc with ⟨d, hd, rfl⟩
    refine ⟨d, ?_, rfl⟩
    have hdI : d ∈ (I : Set K) := by
      rw [← hIu]
      exact hd
    rw [hIset]
    exact hdI
  have hfinite :=
    chapter05_scaled_correction_preserves_finite_precision K S m ell s hell hpres
  refine ⟨a₀ + c, ?_⟩
  intro v
  rcases v with ⟨v, hvT⟩
  rcases v with w | w
  · have hv : w ∈ S := Finset.mem_toLeft.mpr hvT
    have hclose :
        chapter01LocallyClose w (xfin w hv)
          (chapter05FiniteDiagonal K (a₀ + c) w) (mfin w hv) := by
      change Valued.v (xfin w hv - ((a₀ + c : K) : w.adicCompletion K)) ≤
        WithZero.exp (-(mfin w hv))
      have ha := ha₀ w hv
      have hc' := hfinite ⟨w, hv⟩
      change Valued.v (xfin w hv - (a₀ : w.adicCompletion K)) ≤
        WithZero.exp (-(mfin w hv)) at ha
      change Valued.v ((c : K) : w.adicCompletion K) ≤
        WithZero.exp (-(mfin w hv)) at hc'
      have hdiff :
          xfin w hv - ((a₀ + c : K) : w.adicCompletion K) =
            (xfin w hv - (a₀ : w.adicCompletion K)) -
              ((c : K) : w.adicCompletion K) := by
        have hcoe (d : K) : (d : w.adicCompletion K) =
            algebraMap K (w.adicCompletion K) d := by
          simp [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
        rw [hcoe (a₀ + c), map_add, ← hcoe a₀, ← hcoe c]
        abel
      rw [hdiff]
      exact (Valued.v.map_sub _ _).trans
        (max_le ha hc')
    have hmem := hm w hv _ hclose
    have hdiag : chapter05FiniteDiagonal K (a₀ + c) w =
        chapter05LocalEmbedding K (Sum.inl w) (a₀ + c) := by
      change (algebraMap K (Chapter04FiniteAdeleRing K) (a₀ + c)) w =
        NumberField.FinitePlace.embedding w (a₀ + c)
      rw [map_add, chapter04_finiteAdele_add_apply]
      have hcoe0 :
          (algebraMap K (Chapter04FiniteAdeleRing K) a₀) w =
            (a₀ : w.adicCompletion K) := by
        exact IsDedekindDomain.FiniteAdeleRing.algebraMap_apply (𝓞 K) K a₀ w
      have hcoec :
          (algebraMap K (Chapter04FiniteAdeleRing K) c) w =
            (c : w.adicCompletion K) := by
        exact IsDedekindDomain.FiniteAdeleRing.algebraMap_apply (𝓞 K) K c w
      rw [hcoe0, hcoec, NumberField.FinitePlace.embedding_apply]
      have hcoe (d : K) : (d : w.adicCompletion K) =
          algebraMap K (w.adicCompletion K) d := by
        simp [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
      rw [hcoe a₀, hcoe c, hcoe (a₀ + c), map_add]
    rw [← hdiag]
    exact hmem
  · have hv : w ∈ A := Finset.mem_toRight.mpr hvT
    have hv' := hcV w hv
    simp only [B, dif_pos hv, Set.mem_ofPred_eq] at hv'
    have hmix :
        (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm
            (chapter01MinkowskiEmbedding K c) =
          algebraMap K (Chapter04InfiniteAdeleRing K) c := by
      rw [NumberField.InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
      exact (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm_apply_apply _
    rw [hmix, NumberField.InfiniteAdeleRing.algebraMap_apply] at hv'
    change algebraMap K w.Completion (a₀ + c) ∈ W ⟨Sum.inr w, hvT⟩
    rw [map_add]
    simpa [add_comm] using hv'

private theorem chapter05_weak_approximation_iff_dense_selected_diagonal_aux
    (K : Type*) [Field K] [NumberField K]
    (T : Finset (Chapter04Place K)) :
    chapter05WeakApproximationStatement K T ↔
      DenseRange (chapter05DiagonalAtPlaces K T) := by
  classical
  constructor
  · intro hweak
    rw [denseRange_iff_closure_range]
    apply Set.eq_univ_of_forall
    intro x
    rw [mem_closure_iff_nhds]
    intro U hU
    rw [nhds_pi] at hU
    rcases Filter.mem_pi'.mp hU with ⟨I, V, hV, hIU⟩
    obtain ⟨a, ha⟩ := hweak x V hV
    have haI : chapter05DiagonalAtPlaces K T a ∈
        Set.pi (I : Set T) V := by
      intro v hv
      exact ha v
    exact ⟨chapter05DiagonalAtPlaces K T a,
      hIU haI, ⟨a, rfl⟩⟩
  · intro hdense x W hW
    have hP : Set.pi (Set.univ : Set T) W ∈ 𝓝 x := by
      rw [nhds_pi, Filter.mem_pi']
      refine ⟨Finset.univ, W, hW, ?_⟩
      intro y hy v _
      exact hy v (Finset.mem_univ v)
    have hxcl : x ∈ closure
        (Set.range (chapter05DiagonalAtPlaces K T)) := by
      rw [hdense.closure_range]
      exact Set.mem_univ x
    rw [mem_closure_iff_nhds] at hxcl
    rcases hxcl (Set.pi (Set.univ : Set T) W) hP with
      ⟨y, hyP, ⟨a, rfl⟩⟩
    refine ⟨a, ?_⟩
    intro v
    exact hyP v (Set.mem_univ v)

theorem chapter05_theorem_5_3_weak_approximation_dense
    (K : Type*) [Field K] [NumberField K]
    (T : Finset (Chapter04Place K)) :
    DenseRange (chapter05DiagonalAtPlaces K T) := by
  exact (chapter05_weak_approximation_iff_dense_selected_diagonal_aux K T).mp
    (chapter05_theorem_5_3_weak_approximation K T)

theorem chapter05_weak_approximation_iff_dense_selected_diagonal
    (K : Type*) [Field K] [NumberField K]
    (T : Finset (Chapter04Place K)) :
    chapter05WeakApproximationStatement K T ↔
      DenseRange (chapter05DiagonalAtPlaces K T) := by
  exact chapter05_weak_approximation_iff_dense_selected_diagonal_aux K T

end

end LastLib.Book04AdelesAndIdeles.Chapter05
