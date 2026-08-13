import LastLib.Book04AdelesAndIdeles.Chapter01.Dependencies
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Localization.Integer

namespace LastLib.Book04AdelesAndIdeles.Chapter01

open NumberField IsDedekindDomain
open scoped nonZeroDivisors WithZero Topology

noncomputable section

/-! ## 1.4 Approximation in a Dedekind domain -/

/- The source extends the additive order to the completion, but the interfaces
below use the completion's canonical multiplicative valuation `Valued.v` for
local neighborhoods, and use the additive order only for global elements of
`K`.
-/

variable (K : Type*) [Field K] [NumberField K]

theorem chapter01_local_neighborhood_coe_iff
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : K) (m : ℤ) :
    (x : v.adicCompletion K) ∈ chapter01LocalNeighborhood v m ↔
      Valued.v (x : v.adicCompletion K) ≤ WithZero.exp (-m) := by
  rfl

theorem chapter01_completion_valuation_agrees_with_global
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : K) :
    Valued.v (x : v.adicCompletion K) = v.valuation K x := by
  exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x

theorem chapter01_finite_approximation
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (x : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), v ∈ S → v.adicCompletion K)
    (m : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), v ∈ S → ℤ) :
    ∃ a : K,
      (∀ v (hv : v ∈ S),
        chapter01LocallyClose v (x v hv) (a : v.adicCompletion K) (m v hv)) ∧
        ∀ q : IsDedekindDomain.HeightOneSpectrum (𝓞 K), q ∉ S →
          0 ≤ chapter01Order q a := by
  let S' := {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) // v ∈ S}
  have hlocal : ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (hv : v ∈ S),
      ∃ y : K,
        Valued.v ((x v hv) - (y : v.adicCompletion K)) <
          WithZero.exp (-(m v hv)) := by
    intro v hv
    let c := Classical.choose
      (v.valuedAdicCompletion_surjective K (WithZero.exp (-(m v hv))))
    let δ := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict c
    have hc : Valued.v c = WithZero.exp (-(m v hv)) := by
      exact Classical.choose_spec
        (v.valuedAdicCompletion_surjective K (WithZero.exp (-(m v hv))))
    have hδpos : 0 < δ := by
      apply (Valuation.restrict_pos_iff
        (v := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)) c).2
      rw [hc]
      exact WithZero.exp_pos
    let U : Set (v.adicCompletion K) := {z |
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict
          ((x v hv) - z) < δ}
    have hUopen : IsOpen U := by
      have hball := Valued.isOpen_ball (v.adicCompletion K) δ
      simpa [U] using hball.preimage (continuous_const.sub continuous_id)
    have hUmem : U ∈ 𝓝 (x v hv) := by
      apply hUopen.mem_nhds
      simp [U, hδpos]
    obtain ⟨y, hy⟩ := (v.denseRange_algebraMap (K := K)).mem_nhds hUmem
    refine ⟨y, ?_⟩
    have hrestrict := hy
    change (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict
        ((x v hv) - (y : v.adicCompletion K)) < δ at hrestrict
    have hlt := (Valuation.restrict_lt_iff_lt_embedding
      (v := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰))).mp hrestrict
    simpa [Valuation.embedding_restrict, δ, hc] using hlt
  choose y hy using hlocal
  obtain ⟨d, hd⟩ :=
    IsLocalization.exist_integer_multiples_of_finite
      (M := (𝓞 K)⁰) (S := K) (fun v : S' => y v.1 v.2)
  choose b hb using hd
  have hb' (v : S') : (b v : K) = ((d : 𝓞 K) : K) * y v.1 v.2 := by
    simpa [Algebra.smul_def] using hb v
  let e : S' → ℕ := fun v =>
    Int.toNat (m v.1 v.2 + chapter01Order v.1 ((d : 𝓞 K) : K))
  have he (v : S') :
      m v.1 v.2 + chapter01Order v.1 ((d : 𝓞 K) : K) ≤ (e v : ℤ) := by
    dsimp [e]
    omega
  classical
  have hdA : (d : 𝓞 K) ≠ 0 := nonZeroDivisors.ne_zero d.2
  let J : Ideal (𝓞 K) := Ideal.span ({(d : 𝓞 K)} : Set (𝓞 K))
  have hJ : J ≠ 0 := by
    simp [J, hdA]
  let Dset : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
    {q | q.asIdeal ∣ J}
  have hD : Dset.Finite := by
    exact Ideal.finite_factors hJ
  let Tset : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
    (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) ∪ Dset
  have hT : Tset.Finite := S.finite_toSet.union hD
  let t : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) := hT.toFinset
  let eT : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℕ := fun v =>
    if hv : v ∈ S then e ⟨v, hv⟩
    else Int.toNat (chapter01Order v ((d : 𝓞 K) : K))
  let bT : ∀ v : t, 𝓞 K := fun v =>
    if hv : v.1 ∈ S then b ⟨v.1, hv⟩ else 0
  obtain ⟨b₀, hb₀⟩ :=
    IsDedekindDomain.exists_forall_sub_mem_ideal
      (s := t) (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => v.asIdeal) eT
      (by
        intro v hv
        exact Ideal.prime_of_isPrime v.ne_bot v.isPrime)
      (by
        intro v hv w hw hvw hEq
        apply hvw
        exact IsDedekindDomain.HeightOneSpectrum.ext hEq)
      bT
  have hbmem (v : S') : b₀ - b v ∈ v.1.asIdeal ^ e v := by
    have hvT : v.1 ∈ Tset := by
      exact Set.mem_union_left Dset v.2
    have hvt : v.1 ∈ t := by
      exact hT.mem_toFinset.mpr hvT
    have h := hb₀ v.1 hvt
    simpa [bT, eT, v.2] using h
  have hbmem_out (q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
      (hqS : q ∉ S) (hqD : q.asIdeal ∣ J) :
      b₀ ∈ q.asIdeal ^ Int.toNat (chapter01Order q ((d : 𝓞 K) : K)) := by
    have hqT : q ∈ Tset := by
      exact Set.mem_union_right (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) hqD
    have hqt : q ∈ t := by
      exact hT.mem_toFinset.mpr hqT
    have h := hb₀ q hqt
    simpa [bT, eT, hqS] using h
  have horder_int (q : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) :
      0 ≤ chapter01Order q (r : K) := by
    rw [chapter01Order, ← FractionalIdeal.coeIdeal_span_singleton]
    exact FractionalIdeal.count_coe_nonneg K q (Ideal.span ({r} : Set (𝓞 K)))
  let a : K := (b₀ : K) / ((d : 𝓞 K) : K)
  have hdK : ((d : 𝓞 K) : K) ≠ 0 := by
    exact map_ne_zero_of_mem_nonZeroDivisors _
      (IsFractionRing.injective (𝓞 K) K) d.2
  have hglobal (v : S') :
      v.1.valuation K (a - y v.1 v.2) ≤
        WithZero.exp (-(m v.1 v.2)) := by
    have hquot : a - y v.1 v.2 =
        ((b₀ - b v : 𝓞 K) : K) / ((d : 𝓞 K) : K) := by
      dsimp [a]
      field_simp [hdK]
      rw [← hb' v]
      rfl
    have hnum : v.1.intValuation (b₀ - b v) ≤
        WithZero.exp (-(e v : ℤ)) :=
      (v.1.intValuation_le_pow_iff_mem (b₀ - b v) (e v)).2 (hbmem v)
    have hden : v.1.valuation K ((d : 𝓞 K) : K) =
        WithZero.exp (-(chapter01Order v.1 ((d : 𝓞 K) : K))) := by
      simpa [chapter01Order,
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent] using
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent_valuation
          v.1 hdK)
    have hden' : v.1.intValuation (d : 𝓞 K) =
        WithZero.exp (-(chapter01Order v.1 ((d : 𝓞 K) : K))) := by
      calc
        v.1.intValuation (d : 𝓞 K) =
            v.1.valuation K ((d : 𝓞 K) : K) :=
          (v.1.valuation_of_algebraMap (d : 𝓞 K)).symm
        _ = _ := hden
    rw [hquot, ← IsFractionRing.mk'_eq_div, v.1.valuation_of_mk']
    rw [hden', div_le_iff₀ WithZero.exp_pos]
    calc
      v.1.intValuation (b₀ - b v) ≤ WithZero.exp (-(e v : ℤ)) := hnum
      _ ≤ WithZero.exp (-(m v.1 v.2)) *
          WithZero.exp (-(chapter01Order v.1 ((d : 𝓞 K) : K))) := by
        rw [← WithZero.exp_add, WithZero.exp_le_exp]
        have hev := he v
        omega
  refine ⟨a, ?_, ?_⟩
  · intro v hv
    change Valued.v ((x v hv) - (a : v.adicCompletion K)) ≤
      WithZero.exp (-(m v hv))
    have hxy := hy v hv
    have hya : Valued.v (((y v hv : K) : v.adicCompletion K) - (a : v.adicCompletion K)) ≤
        WithZero.exp (-(m v hv)) := by
      have hcoe (z : K) : (z : v.adicCompletion K) =
          algebraMap K (v.adicCompletion K) z := by
        simp [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
      have hya' : Valued.v ((a : v.adicCompletion K) -
          (y v hv : v.adicCompletion K)) ≤ WithZero.exp (-(m v hv)) := by
        rw [hcoe a, hcoe (y v hv), ← map_sub, ← hcoe (a - y v hv)]
        rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v]
        exact hglobal ⟨v, hv⟩
      rw [Valuation.map_sub_swap]
      exact hya'
    calc
      Valued.v ((x v hv) - (a : v.adicCompletion K)) =
          Valued.v (((x v hv) - (y v hv : K)) +
            ((y v hv : K) - (a : v.adicCompletion K))) := by
        congr 1
        abel
      _ ≤ max (Valued.v ((x v hv) - (y v hv : K)))
          (Valued.v ((y v hv : K) - (a : v.adicCompletion K))) := by
        exact map_add_le_max (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) _ _
      _ ≤ WithZero.exp (-(m v hv)) := max_le (le_of_lt hxy) hya
  · intro q hqS
    by_cases hbzero : (b₀ : K) = 0
    · rw [chapter01Order, show a = 0 by simp [a, hbzero],
        FractionalIdeal.spanSingleton_zero, FractionalIdeal.count_zero]
    · have horder_a : chapter01Order q a =
          chapter01Order q (b₀ : K) - chapter01Order q ((d : 𝓞 K) : K) := by
        dsimp [a]
        change
          LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent q
              ((b₀ : K) / ((d : 𝓞 K) : K)) =
            LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent q
              (b₀ : K) -
              LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent q
                ((d : 𝓞 K) : K)
        rw [div_eq_mul_inv,
          LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent_mul
            q hbzero (inv_ne_zero hdK),
          LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent_inv
            q hdK]
        ring
      by_cases hqD : q.asIdeal ∣ J
      · have hbo := hbmem_out q hqS hqD
        let n : ℕ := (chapter01Order q ((d : 𝓞 K) : K)).toNat
        have hvalb := (q.intValuation_le_pow_iff_mem (b₀ : 𝓞 K) n).2 (by
          simpa [n] using hbo)
        have hvalb' : q.valuation K (b₀ : K) ≤ WithZero.exp (-(n : ℤ)) := by
          rw [q.valuation_of_algebraMap]
          exact hvalb
        have hvalb0 : q.valuation K (b₀ : K) =
            WithZero.exp (-(chapter01Order q (b₀ : K))) := by
          simpa [chapter01Order,
            LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent] using
            (LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent_valuation
              q hbzero)
        rw [hvalb0] at hvalb'
        rw [WithZero.exp_le_exp] at hvalb'
        have hnd : (n : ℤ) = chapter01Order q ((d : 𝓞 K) : K) := by
          dsimp [n]
          exact Int.toNat_of_nonneg (horder_int q d)
        rw [hnd] at hvalb'
        rw [horder_a]
        omega
      · have hd_notmem : (d : 𝓞 K) ∉ q.asIdeal := by
          intro h
          apply hqD
          exact Ideal.dvd_span_singleton.mpr h
        have horder_d_zero : chapter01Order q ((d : 𝓞 K) : K) = 0 := by
          simpa [chapter01Order,
            LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent] using
            (LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent_primeCompl_eq_zero
              q ⟨d, hd_notmem⟩)
        rw [horder_a, horder_d_zero]
        simpa using horder_int q b₀

theorem chapter01_finite_approximation_with_controlled_denominator
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (x : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), v ∈ S → v.adicCompletion K)
    (m : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), v ∈ S → ℤ) :
    ∃ I : (FractionalIdeal (𝓞 K)⁰ K),
      I ≠ 0 ∧
        chapter01FractionalIdealIntegralOutside S I ∧
          (∀ v (hv : v ∈ S),
            x v hv ∈ chapter01LocalFractionalIdealBall v I) ∧
          ∃ a : K, a ∈ I ∧
            (∀ v (hv : v ∈ S),
              chapter01LocallyClose v (x v hv) (a : v.adicCompletion K) (m v hv)) := by
  classical
  by_cases hS : S.Nonempty
  · have hsurj (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
        (γ : ℤᵐ⁰) : ∃ y : K, v.valuation K y = γ := by
      exact (IsDedekindDomain.HeightOneSpectrum.valuation_surjective K v) γ
    let r : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), v ∈ S → ℤ :=
      fun v hv => if hx : x v hv = 0 then max (m v hv) 0 + 1
        else -WithZero.log (Valued.v (x v hv))
    let z : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), v ∈ S →
        v.adicCompletion K := fun v hv =>
      if hx : x v hv = 0 then
        ((Classical.choose (hsurj v
          (WithZero.exp (r v hv))⁻¹) : K) : v.adicCompletion K)
      else x v hv
    let M : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), v ∈ S → ℤ :=
      fun v hv => max (m v hv) (r v hv + 1)
    have hzval (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (hv : v ∈ S) :
        Valued.v (z v hv) = WithZero.exp (-(r v hv)) := by
      by_cases hx : x v hv = 0
      · dsimp [z]
        rw [if_pos hx]
        rw [chapter01_completion_valuation_agrees_with_global]
        exact Classical.choose_spec (hsurj v
          (WithZero.exp (r v hv))⁻¹)
      · dsimp [z]
        rw [if_neg hx]
        have hxv : Valued.v (x v hv) ≠ 0 :=
          (Valuation.ne_zero_iff _).2 hx
        have hr : r v hv = -WithZero.log (Valued.v (x v hv)) := by
          simp [r, hx]
        rw [hr]
        simpa only [WithZero.exp_neg, inv_inv] using (WithZero.exp_log hxv).symm
    obtain ⟨a, haS, haout⟩ :=
      chapter01_finite_approximation K S z M
    have hclose_val (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (hv : v ∈ S) :
        Valued.v (a : v.adicCompletion K) = Valued.v (z v hv) := by
      have hclose := haS v hv
      change Valued.v ((z v hv) - (a : v.adicCompletion K)) ≤
        WithZero.exp (-(M v hv)) at hclose
      have hsmall : Valued.v ((z v hv) - (a : v.adicCompletion K)) <
          Valued.v (z v hv) := by
        calc
          Valued.v ((z v hv) - (a : v.adicCompletion K)) ≤
              WithZero.exp (-(M v hv)) := hclose
          _ ≤ WithZero.exp (-(r v hv + 1)) := by
            have hMr : r v hv + 1 ≤ M v hv := by
              dsimp [M]
              exact le_max_right _ _
            rw [WithZero.exp_le_exp]
            exact neg_le_neg hMr
          _ < WithZero.exp (-(r v hv)) := by
            rw [WithZero.exp_lt_exp]
            omega
          _ = Valued.v (z v hv) := (hzval v hv).symm
      apply Valuation.map_eq_of_sub_lt (Valued.v :
        Valuation (v.adicCompletion K) ℤᵐ⁰)
      rw [Valuation.map_sub_swap]
      exact hsmall
    have ha0 : a ≠ 0 := by
      obtain ⟨v, hv⟩ := hS
      have hval := hclose_val v hv
      have hne : Valued.v (a : v.adicCompletion K) ≠ 0 := by
        rw [hval, hzval]
        exact ne_of_gt WithZero.exp_pos
      intro ha
      apply hne
      simp [ha]
    let I : FractionalIdeal (𝓞 K)⁰ K :=
      FractionalIdeal.spanSingleton (𝓞 K)⁰ a
    have hI : I ≠ 0 := by
      dsimp [I]
      exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr ha0
    refine ⟨I, hI, ?_, ?_, ?_⟩
    · intro q hqS
      change 0 ≤ chapter01Order q a
      exact haout q hqS
    · intro v hv
      change Valued.v (x v hv) ≤ WithZero.exp (-(chapter01Order v a))
      by_cases hx : x v hv = 0
      · simp [hx]
      · have hvalx : Valued.v (x v hv) =
            WithZero.exp (-(chapter01Order v a)) := by
          calc
            Valued.v (x v hv) = Valued.v (z v hv) := by simp [z, hx]
            _ = Valued.v (a : v.adicCompletion K) := (hclose_val v hv).symm
            _ = v.valuation K a :=
              chapter01_completion_valuation_agrees_with_global K v a
            _ = WithZero.exp (-(chapter01Order v a)) := by
              simpa [chapter01Order,
                LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent] using
                (LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent_valuation
                  v ha0)
        exact hvalx.le
    · refine ⟨a, ?_, ?_⟩
      · simpa [I] using
          (FractionalIdeal.mem_spanSingleton_self (𝓞 K)⁰ a)
      · intro v hv
        change Valued.v ((x v hv) - (a : v.adicCompletion K)) ≤
          WithZero.exp (-(m v hv))
        by_cases hx : x v hv = 0
        · rw [hx, zero_sub, Valuation.map_neg, hclose_val v hv, hzval]
          rw [WithZero.exp_le_exp]
          simp only [r, dif_pos hx]
          omega
        · have hclose := haS v hv
          change Valued.v ((z v hv) - (a : v.adicCompletion K)) ≤
            WithZero.exp (-(M v hv)) at hclose
          have hM : m v hv ≤ M v hv := by
            dsimp [M]
            exact le_max_left _ _
          have hbound : WithZero.exp (-(M v hv)) ≤
              WithZero.exp (-(m v hv)) := by
            rw [WithZero.exp_le_exp]
            exact neg_le_neg hM
          simpa [z, hx] using hclose.trans hbound
  · let I : FractionalIdeal (𝓞 K)⁰ K := 1
    refine ⟨I, ?_, ?_, ?_, 0, ?_, ?_⟩
    · simp [I]
    · intro v hv
      change 0 ≤ FractionalIdeal.count K v (1 : FractionalIdeal (𝓞 K)⁰ K)
      rw [FractionalIdeal.count_one]
    · intro v hv
      exact (hS ⟨v, hv⟩).elim
    · simp [I]
    · intro v hv
      exact (hS ⟨v, hv⟩).elim

theorem chapter01_principal_parts_approximation
    (x : chapter01FiniteAdeleRing K) :
    ∃ a : K, ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      x v - (a : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
  classical
  have hfinite :
      {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) |
        ¬ x v ∈ v.adicCompletionIntegers K}.Finite := by
    exact Filter.eventually_cofinite.1 x.2
  let S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) := hfinite.toFinset
  have hS (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
      v ∈ S ↔ ¬ x v ∈ v.adicCompletionIntegers K := by
    dsimp [S]
    exact hfinite.mem_toFinset
  obtain ⟨a, haS, haout⟩ :=
    chapter01_finite_approximation K S
      (fun v _ => x v) (fun _ _ => 0)
  refine ⟨a, ?_⟩
  intro v
  by_cases hv : v ∈ S
  · apply (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
      (𝓞 K) K v).2
    have hclose := haS v hv
    change Valued.v ((x v) - (a : v.adicCompletion K)) ≤ 1
    change Valued.v ((x v) - (a : v.adicCompletion K)) ≤
        WithZero.exp (-(0 : ℤ)) at hclose
    simpa using hclose
  · have hxint : x v ∈ v.adicCompletionIntegers K := by
      by_contra hx
      exact hv ((hS v).2 hx)
    have ha_val : v.valuation K a ≤ 1 := by
      by_cases ha0 : a = 0
      · simp [ha0]
      · have hval : v.valuation K a =
            WithZero.exp (-(chapter01Order v a)) := by
          simpa [chapter01Order,
            LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent] using
            (LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent_valuation
              v ha0)
        rw [hval, ← WithZero.exp_zero, WithZero.exp_le_exp]
        exact neg_nonpos.mpr (haout v hv)
    have haint : (a : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
      apply (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
        (𝓞 K) K v).2
      rw [chapter01_completion_valuation_agrees_with_global]
      exact ha_val
    apply (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
      (𝓞 K) K v).2
    exact Valuation.map_sub_le (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
      ((IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
        (𝓞 K) K v).1 hxint)
      ((IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
        (𝓞 K) K v).1 haint)

theorem chapter01_finite_adele_nonintegral_support_finite
    (x : chapter01FiniteAdeleRing K) :
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) |
      x v ∉ v.adicCompletionIntegers K}.Finite := by
  exact (Filter.eventually_cofinite.1 x.2)

theorem chapter01_order_finite_support_for_nonzero_global (a : K) (ha : a ≠ 0) :
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) | chapter01Order v a ≠ 0}.Finite :=
  by
    simpa [chapter01Order,
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent] using
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent_finite_support
        (A := 𝓞 K) (K := K) ha)

theorem chapter01_no_nonzero_global_element_positive_at_every_prime :
    ¬∃ a : K, a ≠ 0 ∧
      ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), 0 < chapter01Order v a := by
  classical
  let V := IsDedekindDomain.HeightOneSpectrum (𝓞 K)
  let PType := {p : ℕ // p.Prime}
  let chooseOver : ∀ p : PType, (Ideal.span {(p.1 : ℤ)}).primesOver (𝓞 K) :=
    fun p => by
      letI : Fact (Nat.Prime p.1) := ⟨p.2⟩
      letI : (Ideal.span {(p.1 : ℤ)}).IsMaximal :=
        Int.ideal_span_isMaximal_of_prime p.1
      exact Classical.choice (Ideal.nonempty_primesOver _)
  let f : PType → V := fun p =>
    ⟨(chooseOver p).1, (chooseOver p).2.1, Ideal.ne_bot_of_mem_primesOver
      (by simp [p.2.ne_zero]) (chooseOver p).2⟩
  have hf : Function.Injective f := by
    intro p p' hpq
    have hP : Ideal.span {(p.1 : ℤ)} =
        Ideal.span {(p'.1 : ℤ)} := by
      calc
        Ideal.span {(p.1 : ℤ)} = (f p).asIdeal.under ℤ := by
          change _ = (chooseOver p).1.under ℤ
          exact (chooseOver p).2.2.over
        _ = (f p').asIdeal.under ℤ := by rw [hpq]
        _ = Ideal.span {(p'.1 : ℤ)} := by
          change (chooseOver p').1.under ℤ = _
          exact (chooseOver p').2.2.over.symm
    have hn := congrArg Ideal.absNorm hP
    have hn' : p.1 = p'.1 := by
      simpa [Ideal.absNorm_span_singleton] using hn
    exact Subtype.ext hn'
  have hPinf : Infinite PType := Nat.infinite_setOfPred_prime.to_subtype
  have hVinst : Infinite V := @Infinite.of_injective V PType hPinf f hf
  have hV : (Set.univ : Set V).Infinite := @Set.infinite_univ V hVinst
  intro h
  rcases h with ⟨a, ha, hpos⟩
  have hfin := chapter01_order_finite_support_for_nonzero_global K a ha
  apply hV
  apply hfin.subset
  intro v hv
  exact (ne_of_gt (hpos v))

end

end LastLib.Book04AdelesAndIdeles.Chapter01
