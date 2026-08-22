import LastLib.Book04AdelesAndIdeles.Chapter12.Core
import LastLib.Book04AdelesAndIdeles.Chapter09.Section04StructureOfIdeleClassGroup
import LastLib.Book04AdelesAndIdeles.Chapter09.Section05CompactKernelOverIdealClassGroup
import LastLib.Book04AdelesAndIdeles.Chapter11.Section07ComputingElementaryRayQuotients
import LastLib.Book04AdelesAndIdeles.Chapter07.Section03AdditiveAndMultiplicativeInformation

namespace LastLib.Book04AdelesAndIdeles.Chapter12

noncomputable section

open Filter Set NumberField Topology WithZeroTopology
open LastLib.Book04AdelesAndIdeles.Chapter09
open LastLib.Book04AdelesAndIdeles.Chapter11
open scoped BigOperators NNReal RestrictedProduct WithZero nonZeroDivisors

/-! # Book 4, Chapter 12, §12.1: The rational field -/

/-- The single real-place portrait of the rational infinite adele ring. -/
structure Chapter12RationalInfinitePortrait where
  equiv : chapter12InfiniteAdeleRing ℚ ≃+* ℝ
  one_real_place : NumberField.InfinitePlace.nrRealPlaces ℚ = 1
  no_complex_places : NumberField.InfinitePlace.nrComplexPlaces ℚ = 0

theorem chapter12_rational_has_one_real_place :
    Nonempty Chapter12RationalInfinitePortrait := by
  let e : chapter12InfiniteAdeleRing ℚ ≃+* ℝ :=
    (RingEquiv.piUnique (fun v : NumberField.InfinitePlace ℚ => v.Completion)).trans
      (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)
  exact ⟨{ equiv := e, one_real_place := NumberField.InfinitePlace.nrRealPlaces_eq_one_of_finrank_eq_one (by simp), no_complex_places := NumberField.InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one (by simp) }⟩

/-- The finite rational adeles written as the canonical restricted product over `ℤ`. -/
abbrev chapter12RationalFiniteRestrictedProduct :=
  Πʳ v : IsDedekindDomain.HeightOneSpectrum ℤ,
    [v.adicCompletion ℚ, v.adicCompletionIntegers ℚ]

theorem chapter12_rational_finite_adele_restricted_product :
    Nonempty (chapter12RationalFiniteAdeleRing ≃+*
      chapter12RationalFiniteRestrictedProduct) := by
  exact ⟨RingEquiv.refl _⟩

theorem chapter12_rational_finite_places_are_prime_indexed :
    Nonempty (IsDedekindDomain.HeightOneSpectrum ℤ ≃ Nat.Primes) := by
  exact ⟨Rat.HeightOneSpectrum.primesEquiv (R := ℤ)⟩

theorem chapter12_rational_ideles_split_into_infinite_and_finite_units :
    Nonempty (chapter12RationalIdeles ≃*
      (chapter12InfiniteAdeleRing ℚ)ˣ × chapter12RationalFiniteIdeles) := by
  exact ⟨MulEquiv.prodUnits⟩

/-- The displayed product portrait of the rational adele ring. -/
def chapter12RationalAdeleProductPortrait
    (P : Chapter12RationalInfinitePortrait) :
    chapter12RationalAdeleRing ≃+*
      ℝ × chapter12RationalFiniteRestrictedProduct :=
  RingEquiv.prodCongr P.equiv (RingEquiv.refl _)

theorem chapter12_rational_adele_ring_product_portrait :
    Nonempty (chapter12RationalAdeleRing ≃+*
      ℝ × chapter12RationalFiniteRestrictedProduct) := by
  obtain ⟨P⟩ := chapter12_rational_has_one_real_place
  exact ⟨chapter12RationalAdeleProductPortrait P⟩

/-- The rational profinite integral coordinates embedded in the finite adeles. -/
def chapter12RationalIntegralFiniteAdeleSet :
    Set chapter12RationalFiniteAdeleRing :=
  {x | ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
    x v ∈ v.adicCompletionIntegers ℚ}

theorem chapter12_rational_integral_finite_adele_iff
    (x : chapter12RationalFiniteAdeleRing) :
    x ∈ chapter12RationalIntegralFiniteAdeleSet ↔
      ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
        x v ∈ v.adicCompletionIntegers ℚ :=
  Iff.rfl

/-- The closed additive fundamental set `[0,1] × Ẑ` in the rational portrait. -/
def chapter12RationalAdditiveFundamentalSet
    (P : Chapter12RationalInfinitePortrait) :
    Set chapter12RationalAdeleRing :=
  {x | P.equiv x.1 ∈ Set.Icc (0 : ℝ) 1 ∧
    x.2 ∈ chapter12RationalIntegralFiniteAdeleSet}

private def chapter12RationalOrder
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) (a : ℚ) : ℤ :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent v a

private theorem chapter12_rational_finite_principal_parts
    (x : chapter12RationalFiniteAdeleRing) :
    ∃ a : ℚ, ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      x v - (a : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := by
  classical
  have hfinite :
      {v : IsDedekindDomain.HeightOneSpectrum ℤ |
        ¬ x v ∈ v.adicCompletionIntegers ℚ}.Finite := by
    exact Filter.eventually_cofinite.1 x.2
  let S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ) := hfinite.toFinset
  have hS (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
      v ∈ S ↔ ¬ x v ∈ v.adicCompletionIntegers ℚ := by
    dsimp [S]
    exact hfinite.mem_toFinset
  have hlocal (v : IsDedekindDomain.HeightOneSpectrum ℤ) (hv : v ∈ S) :
      ∃ y : ℚ,
        Valued.v ((x v) - (y : v.adicCompletion ℚ)) < 1 := by
    let U : Set (v.adicCompletion ℚ) :=
      {z | Valued.v ((x v) - z) < 1}
    have hUopen : IsOpen U := by
      change IsOpen ((fun z : v.adicCompletion ℚ =>
        Valued.v ((x v) - z)) ⁻¹' Set.Iio 1)
      apply (WithZeroTopology.isOpen_Iio : IsOpen (Set.Iio (1 : ℤᵐ⁰))).preimage
      exact (Valued.continuous_valuation_of_surjective
        (v.valuedAdicCompletion_surjective ℚ)).comp
        (continuous_const.sub continuous_id)
    have hxU : (x v) ∈ U := by
      simp [U]
    obtain ⟨y, hy⟩ :=
      (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap
        (v := v) (K := ℚ)).exists_mem_open hUopen ⟨x v, hxU⟩
    refine ⟨y, ?_⟩
    have hcoe (z : ℚ) : (z : v.adicCompletion ℚ) =
        algebraMap ℚ (v.adicCompletion ℚ) z := by
      simp
    simpa only [U, Set.mem_ofPred_eq, hcoe] using hy
  choose y hy using hlocal
  let S' := {v : IsDedekindDomain.HeightOneSpectrum ℤ // v ∈ S}
  obtain ⟨d, hd⟩ :=
    IsLocalization.exist_integer_multiples_of_finite
      (M := (ℤ)⁰) (S := ℚ) (fun v : S' => y v.1 v.2)
  choose b hb using hd
  have hb' (v : S') :
      (b v : ℚ) = ((d : ℤ) : ℚ) * y v.1 v.2 := by
    simpa [Algebra.smul_def] using hb v
  have horder_int (v : IsDedekindDomain.HeightOneSpectrum ℤ) (r : ℤ) :
      0 ≤ chapter12RationalOrder v (r : ℚ) := by
    change 0 ≤ FractionalIdeal.count ℚ v
      (FractionalIdeal.spanSingleton (ℤ)⁰ (algebraMap ℤ ℚ r))
    rw [← FractionalIdeal.coeIdeal_span_singleton]
    exact FractionalIdeal.count_coe_nonneg ℚ v (Ideal.span ({r} : Set ℤ))
  let J : Ideal ℤ := Ideal.span ({(d : ℤ)} : Set ℤ)
  have hdA : (d : ℤ) ≠ 0 := nonZeroDivisors.ne_zero d.2
  have hJ : J ≠ 0 := by
    simp [J, hdA]
  let Dset : Set (IsDedekindDomain.HeightOneSpectrum ℤ) :=
    {q | q.asIdeal ∣ J}
  have hD : Dset.Finite := by
    exact Ideal.finite_factors hJ
  let Tset : Set (IsDedekindDomain.HeightOneSpectrum ℤ) :=
    (S : Set (IsDedekindDomain.HeightOneSpectrum ℤ)) ∪ Dset
  have hT : Tset.Finite := S.finite_toSet.union hD
  let t : Finset (IsDedekindDomain.HeightOneSpectrum ℤ) := hT.toFinset
  let e : S' → ℕ := fun v =>
    Int.toNat (chapter12RationalOrder v.1 ((d : ℤ) : ℚ))
  let eT : IsDedekindDomain.HeightOneSpectrum ℤ → ℕ := fun v =>
    if hv : v ∈ S then e ⟨v, hv⟩
    else Int.toNat (chapter12RationalOrder v ((d : ℤ) : ℚ))
  let bT : ∀ v : t, ℤ := fun v =>
    if hv : v.1 ∈ S then b ⟨v.1, hv⟩ else 0
  obtain ⟨b₀, hb₀⟩ :=
    IsDedekindDomain.exists_forall_sub_mem_ideal
      (s := t) (fun v : IsDedekindDomain.HeightOneSpectrum ℤ => v.asIdeal) eT
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
    have hvt : v.1 ∈ t := hT.mem_toFinset.mpr hvT
    have h := hb₀ v.1 hvt
    simpa [bT, eT, v.2] using h
  have hbmem_out (q : IsDedekindDomain.HeightOneSpectrum ℤ)
      (hqS : q ∉ S) (hqD : q.asIdeal ∣ J) :
      b₀ ∈ q.asIdeal ^ Int.toNat (chapter12RationalOrder q ((d : ℤ) : ℚ)) := by
    have hqT : q ∈ Tset := by
      exact Set.mem_union_right (S : Set (IsDedekindDomain.HeightOneSpectrum ℤ)) hqD
    have hqt : q ∈ t := hT.mem_toFinset.mpr hqT
    have h := hb₀ q hqt
    simpa [bT, eT, hqS] using h
  have hdQ : ((d : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast hdA
  let a : ℚ := (b₀ : ℚ) / ((d : ℤ) : ℚ)
  have hglobal (v : S') :
      v.1.valuation ℚ (a - y v.1 v.2) ≤ 1 := by
    have hquot : a - y v.1 v.2 =
        ((b₀ - b v : ℤ) : ℚ) / ((d : ℤ) : ℚ) := by
      dsimp [a]
      field_simp [hdQ]
      rw [← hb' v]
      norm_cast
    have hnum : v.1.intValuation (b₀ - b v) ≤
        WithZero.exp (-(e v : ℤ)) :=
      (v.1.intValuation_le_pow_iff_mem (b₀ - b v) (e v)).2 (hbmem v)
    have hden : v.1.valuation ℚ ((d : ℤ) : ℚ) =
        WithZero.exp (-(chapter12RationalOrder v.1 ((d : ℤ) : ℚ))) := by
      simpa only [chapter12RationalOrder] using
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent_valuation
          (A := ℤ) (K := ℚ) v.1 hdQ
    rw [hquot, (v.1.valuation ℚ).map_div]
    have hnum' : v.1.valuation ℚ (b₀ - b v : ℤ) =
        v.1.intValuation (b₀ - b v) := by
      exact v.1.valuation_of_algebraMap (b₀ - b v)
    rw [hnum']
    rw [hden]
    rw [div_le_iff₀ WithZero.exp_pos]
    have he : chapter12RationalOrder v.1 ((d : ℤ) : ℚ) ≤ (e v : ℤ) := by
      dsimp [e]
      omega
    calc
      v.1.intValuation (b₀ - b v) ≤
          WithZero.exp (-(e v : ℤ)) := hnum
      _ ≤
          WithZero.exp (-(chapter12RationalOrder v.1 ((d : ℤ) : ℚ))) := by
        rw [WithZero.exp_le_exp]
        exact neg_le_neg he
      _ = 1 * WithZero.exp
          (-(chapter12RationalOrder v.1 ((d : ℤ) : ℚ))) := by simp
  have haout (q : IsDedekindDomain.HeightOneSpectrum ℤ) (hqS : q ∉ S) :
      0 ≤ chapter12RationalOrder q a := by
    by_cases hbzero : (b₀ : ℚ) = 0
    · have ha0 : a = 0 := by simp [a, hbzero]
      rw [ha0]
      change 0 ≤ FractionalIdeal.count ℚ q
        (FractionalIdeal.spanSingleton (ℤ)⁰ 0)
      rw [FractionalIdeal.spanSingleton_zero, FractionalIdeal.count_zero]
    · have horder_a : chapter12RationalOrder q a =
          chapter12RationalOrder q (b₀ : ℚ) -
            chapter12RationalOrder q ((d : ℤ) : ℚ) := by
        have horder_a' :
            LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent
                q a =
              LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent
                q (b₀ : ℚ) -
              LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent
                q ((d : ℤ) : ℚ) := by
          dsimp [a]
          rw [div_eq_mul_inv,
            LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent_mul
              q hbzero (inv_ne_zero hdQ),
            LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent_inv
              q hdQ]
          ring
        simpa only [chapter12RationalOrder] using horder_a'
      by_cases hqD : q.asIdeal ∣ J
      · have hbo := hbmem_out q hqS hqD
        let n : ℕ := (chapter12RationalOrder q ((d : ℤ) : ℚ)).toNat
        have hvalb := (q.intValuation_le_pow_iff_mem (b₀ : ℤ) n).2 (by
          simpa [n] using hbo)
        have hvalb' : q.valuation ℚ (b₀ : ℚ) ≤ WithZero.exp (-(n : ℤ)) := by
          have hcast : (b₀ : ℚ) = algebraMap ℤ ℚ b₀ := rfl
          rw [hcast, q.valuation_of_algebraMap]
          exact hvalb
        have hvalb0 : q.valuation ℚ (b₀ : ℚ) =
            WithZero.exp (-(chapter12RationalOrder q (b₀ : ℚ))) := by
          simpa only [chapter12RationalOrder] using
            LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent_valuation
              (A := ℤ) (K := ℚ) q hbzero
        rw [hvalb0] at hvalb'
        rw [WithZero.exp_le_exp] at hvalb'
        have hnd : (n : ℤ) = chapter12RationalOrder q ((d : ℤ) : ℚ) := by
          dsimp [n]
          exact Int.toNat_of_nonneg (horder_int q (d : ℤ))
        rw [hnd] at hvalb'
        rw [horder_a]
        omega
      · have hd_notmem : (d : ℤ) ∉ q.asIdeal := by
          intro h
          apply hqD
          exact Ideal.dvd_span_singleton.mpr h
        have horder_d_zero : chapter12RationalOrder q ((d : ℤ) : ℚ) = 0 := by
          have hzero :=
            LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent_primeCompl_eq_zero
              (A := ℤ) (K := ℚ) q ⟨d, hd_notmem⟩
          change LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent
            q ((d : ℤ) : ℚ) = 0
          rw [show ((d : ℤ) : ℚ) = algebraMap ℤ ℚ (d : ℤ) by rfl]
          exact hzero
        rw [horder_a, horder_d_zero]
        simpa using horder_int q b₀
  refine ⟨a, ?_⟩
  intro v
  by_cases hv : v ∈ S
  · apply (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
      ℤ ℚ v).2
    have hya : Valued.v ((y v hv : ℚ) - (a : v.adicCompletion ℚ)) ≤ 1 := by
      have hcoe (z : ℚ) : (z : v.adicCompletion ℚ) =
          algebraMap ℚ (v.adicCompletion ℚ) z := by
        simp
      have hya' : Valued.v ((a : v.adicCompletion ℚ) -
          (y v hv : v.adicCompletion ℚ)) ≤ 1 := by
        rw [hcoe a, hcoe (y v hv), ← map_sub,
          IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
        simp only [Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply]
        rw [v.valuedAdicCompletion_eq_valuation' (a - y v hv)]
        exact hglobal ⟨v, hv⟩
      rw [Valuation.map_sub_swap]
      exact hya'
    calc
      Valued.v ((x v) - (a : v.adicCompletion ℚ)) ≤
          max (Valued.v ((x v) - (y v hv : ℚ)))
            (Valued.v ((y v hv : ℚ) - (a : v.adicCompletion ℚ))) := by
        rw [show (x v) - (a : v.adicCompletion ℚ) =
            ((x v) - (y v hv : ℚ)) +
              ((y v hv : ℚ) - (a : v.adicCompletion ℚ)) by abel]
        exact map_add_le_max (Valued.v :
          Valuation (v.adicCompletion ℚ) ℤᵐ⁰) _ _
      _ ≤ 1 := max_le (le_of_lt (hy v hv)) hya
  · have hxint : x v ∈ v.adicCompletionIntegers ℚ := by
      by_contra hx
      exact hv ((hS v).2 hx)
    have ha_val : v.valuation ℚ a ≤ 1 := by
      by_cases ha0 : a = 0
      · simp [ha0]
      · rw [LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent_valuation
          v ha0]
        rw [← WithZero.exp_zero, WithZero.exp_le_exp]
        exact neg_nonpos.mpr (haout v hv)
    have haint : (a : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := by
      apply (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
        ℤ ℚ v).2
      have hcoe (z : ℚ) : (z : v.adicCompletion ℚ) =
          algebraMap ℚ (v.adicCompletion ℚ) z := by
        simp
      rw [hcoe a, IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
      simp only [Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply]
      rw [v.valuedAdicCompletion_eq_valuation' a]
      exact ha_val
    apply (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
      ℤ ℚ v).2
    exact Valuation.map_sub_le (Valued.v :
      Valuation (v.adicCompletion ℚ) ℤᵐ⁰)
      ((IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
        ℤ ℚ v).1 hxint)
      ((IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
        ℤ ℚ v).1 haint)

/-- Strong approximation gives the stated additive cover. -/
theorem chapter12_rational_additive_fundamental_set_covers
    (P : Chapter12RationalInfinitePortrait)
    (x : chapter12RationalAdeleRing) :
    ∃ q : ℚ, x - algebraMap ℚ chapter12RationalAdeleRing q ∈
      chapter12RationalAdditiveFundamentalSet P := by
  rcases chapter12_rational_finite_principal_parts x.2 with ⟨a, ha⟩
  let r : ℝ := P.equiv x.1 - (a : ℝ)
  let n : ℤ := Int.floor r
  let q : ℚ := a + n
  have hPq (z : ℚ) :
      P.equiv (algebraMap ℚ (chapter12InfiniteAdeleRing ℚ) z) = (z : ℝ) := by
    exact map_ratCast
      (P.equiv.toRingHom.comp (algebraMap ℚ (chapter12InfiniteAdeleRing ℚ))) z
  refine ⟨q, ?_⟩
  constructor
  · have hreal :
        P.equiv (x.1 - (algebraMap ℚ chapter12RationalAdeleRing q).1) =
          r - (n : ℝ) := by
      change P.equiv (x.1 - algebraMap ℚ
        (chapter12InfiniteAdeleRing ℚ) q) = r - (n : ℝ)
      rw [map_sub, hPq]
      simp [r, q]
      ring
    change P.equiv (x.1 - (algebraMap ℚ chapter12RationalAdeleRing q).1) ∈
      Set.Icc (0 : ℝ) 1
    rw [hreal]
    constructor
    · exact sub_nonneg.mpr (Int.floor_le r)
    · apply sub_le_iff_le_add.mpr
      simpa [add_comm] using (Int.lt_floor_add_one r).le
  · intro v
    have hxa : x.2 v - (a : v.adicCompletion ℚ) ∈
        v.adicCompletionIntegers ℚ := ha v
    have hn : (n : v.adicCompletion ℚ) ∈
        v.adicCompletionIntegers ℚ := by
      simp
    have hqv :
        (algebraMap ℚ chapter12RationalFiniteAdeleRing q) v =
          (a : v.adicCompletion ℚ) + (n : v.adicCompletion ℚ) := by
      rw [IsDedekindDomain.FiniteAdeleRing.algebraMap_apply]
      change algebraMap ℚ (v.adicCompletion ℚ) q = _
      have hcoe (z : ℚ) : (z : v.adicCompletion ℚ) =
          algebraMap ℚ (v.adicCompletion ℚ) z := by
        simp
      rw [show q = a + (n : ℚ) by rfl, map_add]
      rw [← hcoe a, ← hcoe (n : ℚ)]
      norm_cast
    change x.2 v - (algebraMap ℚ chapter12RationalFiniteAdeleRing q) v ∈
      v.adicCompletionIntegers ℚ
    rw [hqv]
    rw [show x.2 v - ((a : v.adicCompletion ℚ) + (n : v.adicCompletion ℚ)) =
      (x.2 v - (a : v.adicCompletion ℚ)) - (n : v.adicCompletion ℚ) by abel]
    apply (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
      ℤ ℚ v).2
    exact Valuation.map_sub_le (Valued.v :
      Valuation (v.adicCompletion ℚ) ℤᵐ⁰)
      ((IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
        ℤ ℚ v).1 hxa)
      ((IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
        ℤ ℚ v).1 hn)

/-- The rational additive quotient by diagonal principal adeles. -/
abbrev chapter12RationalAdditiveQuotient :=
  chapter12RationalAdeleRing ⧸ NumberField.AdeleRing.principalSubgroup ℤ ℚ

def chapter12RationalAdditiveQuotientMk :
    chapter12RationalAdeleRing →+ chapter12RationalAdditiveQuotient :=
  QuotientAddGroup.mk'
    (NumberField.AdeleRing.principalSubgroup ℤ ℚ)

theorem chapter12_rational_additive_quotient_is_covered
    (P : Chapter12RationalInfinitePortrait) :
    ∀ c : chapter12RationalAdditiveQuotient,
      ∃ x ∈ chapter12RationalAdditiveFundamentalSet P,
        chapter12RationalAdditiveQuotientMk x = c := by
  intro c
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective
    (NumberField.AdeleRing.principalSubgroup ℤ ℚ) c
  rcases chapter12_rational_additive_fundamental_set_covers P x with ⟨q, hq⟩
  refine ⟨x - algebraMap ℚ chapter12RationalAdeleRing q, hq, ?_⟩
  apply (QuotientAddGroup.eq_iff_sub_mem).2
  refine ⟨-q, ?_⟩
  simp [sub_eq_add_neg, add_comm]

/-! ## Valuation normalization of rational ideles -/

abbrev Chapter12RationalPrime := {p : ℕ // p.Prime}

/- The integer-valued exponent read from a finite rational-idele coordinate. -/
def chapter12RationalFiniteValuationExponent
    (x : chapter12RationalIdeles) (p : Chapter12RationalPrime) : ℤ :=
  let v := (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p
  let z := Valued.v (x.1.2 v)
  -- `Valued.v` uses `WithZero.exp (-ord)`; the book's ideal exponent is `ord`.
  if hz : z = 0 then 0 else -(WithZero.unzero hz).toAdd

private theorem chapter12_rational_height_one_span
    (p : Chapter12RationalPrime) :
    ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm
      (⟨p.1, p.2⟩ : Nat.Primes)).asIdeal =
      Ideal.span {(p.1 : ℤ)} := by
  have hi : Rat.IsIntegralClosure.intEquiv (R := ℤ) = RingEquiv.refl ℤ := by
    ext z
    simp
  have hmap : Ideal.map (RingEquiv.refl ℤ)
      ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm
        (⟨p.1, p.2⟩ : Nat.Primes)).asIdeal =
      ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm
        (⟨p.1, p.2⟩ : Nat.Primes)).asIdeal := by
    change Ideal.map (RingHom.id ℤ) _ = _
    simp
  have h := (Rat.HeightOneSpectrum.span_natGenerator (R := ℤ)
    ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm
      (⟨p.1, p.2⟩ : Nat.Primes))).symm
  rw [hi] at h
  rw [← hmap]
  rw [h]
  have hpgen := congrArg Subtype.val
    ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).apply_symm_apply
      (⟨p.1, p.2⟩ : Nat.Primes))
  change Rat.HeightOneSpectrum.natGenerator
      ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm
        (⟨p.1, p.2⟩ : Nat.Primes)) = p.1 at hpgen
  rw [hpgen]

private theorem chapter12_rational_height_one_valuation_is_padic
    (p : Chapter12RationalPrime)
    (V : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hV : V.asIdeal = Ideal.span {(p.1 : ℤ)}) :
    ∀ b : ℚ, V.valuation ℚ b =
      @Rat.padicValuation p.1 ⟨p.2⟩ b := by
  let _ : Fact p.1.Prime := ⟨p.2⟩
  have hVint {z : ℤ} (hz : z ≠ 0) :
      V.intValuation z = WithZero.exp (-(padicValInt p.1 z : ℤ)) := by
    rw [V.intValuation_if_neg hz, hV]
    have hcount : (Associates.mk (Ideal.span {(p.1 : ℤ)} : Ideal ℤ)).count
        (Associates.mk (Ideal.span ({z} : Set ℤ) : Ideal ℤ)).factors =
        padicValNat p.1 z.natAbs := by
      let n : ℕ := padicValNat p.1 z.natAbs
      have hle : (p.1 : ℤ) ^ n ∣ z := by
        rw [← Nat.cast_pow, Int.natCast_dvd]
        exact (Nat.pow_dvd_iff_le_padicValNat p.2.ne_one
          (Int.natAbs_ne_zero.mpr hz)).2 (le_rfl)
      have hlt : ¬(p.1 : ℤ) ^ (n + 1) ∣ z := by
        intro hdiv
        rw [← Nat.cast_pow, Int.natCast_dvd] at hdiv
        have hle' := (Nat.pow_dvd_iff_le_padicValNat p.2.ne_one
          (Int.natAbs_ne_zero.mpr hz)).1 hdiv
        simp at hle'
        exact (Nat.not_succ_le_self n) hle'
      have hpz : Prime (p.1 : ℤ) := Nat.prime_iff_prime_int.mp p.2
      exact Ideal.count_associates_eq' (R := ℤ) (x := (p.1 : ℤ)) (a := z)
        hpz hle hlt
    rw [hcount]
    simp [padicValInt]
  intro b
  obtain ⟨r, s, h⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors ℤ) b
  rw [← h, IsDedekindDomain.HeightOneSpectrum.valuation_of_mk']
  by_cases hr : r = 0
  · simp [hr]
  · have hs : (s : ℤ) ≠ 0 := nonZeroDivisors.ne_zero s.property
    rw [hVint hr, hVint hs]
    simp [Rat.padicValuation, padicValRat, padicValInt, hr]

private theorem chapter12_rational_exponent_eq_zero_of_valued_eq_one
    (x : chapter12RationalIdeles) (p : Chapter12RationalPrime)
    (hp : Valued.v (x.1.2
      ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm
        (⟨p.1, p.2⟩ : Nat.Primes))) = 1) :
    chapter12RationalFiniteValuationExponent x p = 0 := by
  unfold chapter12RationalFiniteValuationExponent
  have hne : Valued.v (x.1.2
      ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm
        (⟨p.1, p.2⟩ : Nat.Primes))) ≠ 0 := by
    rw [hp]
    exact one_ne_zero
  change (if hz : Valued.v (x.1.2
      ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm
        (⟨p.1, p.2⟩ : Nat.Primes))) = 0 then 0 else
      -(WithZero.unzero hz).toAdd) = 0
  rw [dif_neg hne]
  apply neg_eq_zero.mpr
  apply (WithZero.toAdd_unzero_eq_iff hne 0).2
  simpa using hp

/- A finite valuation profile is the precise finite-product datum in the text. -/
structure Chapter12RationalValuationProfile where
  exponent : Chapter12RationalPrime → ℤ
  support : Finset Chapter12RationalPrime
  support_spec : ∀ p, p ∉ support → exponent p = 0

namespace Chapter12RationalValuationProfile

/-- The positive rational number obtained from a finite valuation profile. -/
def q (a : Chapter12RationalValuationProfile) : ℚ :=
  Finset.prod a.support (fun p => (p.1 : ℚ) ^ a.exponent p)

theorem q_pos (a : Chapter12RationalValuationProfile) : 0 < a.q := by
  exact Finset.prod_pos (fun p hp => zpow_pos (by exact_mod_cast p.2.pos) _)

@[simp]
theorem q_def (a : Chapter12RationalValuationProfile) :
    a.q = Finset.prod a.support (fun p => (p.1 : ℚ) ^ a.exponent p) :=
  rfl

end Chapter12RationalValuationProfile

private theorem chapter12_rational_profile_padic_val_rat
    (a : Chapter12RationalValuationProfile) (p : Chapter12RationalPrime) :
    padicValRat p.1 a.q = a.exponent p := by
  let _ : Fact p.1.Prime := ⟨p.2⟩
  classical
  have haux : ∀ s : Finset Chapter12RationalPrime,
      ∀ p : Chapter12RationalPrime,
        padicValRat p.1 (∏ r ∈ s, (r.1 : ℚ) ^ a.exponent r) =
          ∑ r ∈ s, if r = p then a.exponent r else 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro p
        simp
    | @insert r s hrs ih =>
        intro p
        let _ : Fact p.1.Prime := ⟨p.2⟩
        have hr0 : (r.1 : ℚ) ≠ 0 := by
          exact_mod_cast r.2.ne_zero
        have hprod0 : (∏ q ∈ s, (q.1 : ℚ) ^ a.exponent q) ≠ 0 := by
          exact Finset.prod_ne_zero_iff.mpr (fun q hq =>
            zpow_ne_zero _ (by exact_mod_cast q.2.ne_zero))
        rw [Finset.prod_insert hrs, padicValRat.mul
          (zpow_ne_zero _ hr0) hprod0, ih p]
        by_cases h : r = p
        · subst r
          simp [hrs, padicValRat.zpow, padicValRat.self p.2.one_lt]
        · have hnot : ¬p.1 ∣ r.1 := by
            intro hdiv
            apply h
            apply Subtype.ext
            exact (prime_dvd_prime_iff_eq (Nat.prime_iff.mp p.2)
              (Nat.prime_iff.mp r.2)).mp hdiv |>.symm
          have hval : padicValRat p.1 (r.1 : ℚ) = 0 := by
            rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnot]
            rfl
          have h' : p ≠ r := by
            intro hpr
            exact h hpr.symm
          rw [padicValRat.zpow, hval]
          norm_num [h, h']
  rw [Chapter12RationalValuationProfile.q_def, haux a.support p]
  by_cases hp : p ∈ a.support
  · simp [hp]
  · simp [hp, a.support_spec p hp]

private theorem chapter12_rational_profile_valuation
    (a : Chapter12RationalValuationProfile)
    (p : Chapter12RationalPrime)
    (V : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hV : V.asIdeal = Ideal.span {(p.1 : ℤ)}) :
    V.valuation ℚ a.q = WithZero.exp (-(a.exponent p)) := by
  let _ : Fact p.1.Prime := ⟨p.2⟩
  rw [chapter12_rational_height_one_valuation_is_padic p V hV]
  change (if a.q = 0 then 0 else WithZero.exp (-padicValRat p.1 a.q)) = _
  rw [if_neg (ne_of_gt (Chapter12RationalValuationProfile.q_pos a))]
  rw [chapter12_rational_profile_padic_val_rat]

/-- The finite component of an idele after division by a rational scalar. -/
def chapter12RationalFinitePartAfterDivision
    (x : chapter12RationalIdeles) (q : ℚ) :
    chapter12RationalFiniteAdeleRing :=
  x.1.2 * algebraMap ℚ (chapter12FiniteAdeleRing ℤ ℚ) q⁻¹

/-- All finite coordinates are units after the indicated scalar division. -/
def chapter12RationalFinitePartIsUnit
    (x : chapter12RationalIdeles) (q : ℚ) : Prop :=
  ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
    ∃ u : (v.adicCompletionIntegers ℚ)ˣ,
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) u =
        chapter12RationalFinitePartAfterDivision x q v

private theorem chapter12_rational_finite_division_valued_eq_one
    (x : chapter12RationalIdeles)
    (a : Chapter12RationalValuationProfile)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (p : Chapter12RationalPrime)
    (hV : v.asIdeal = Ideal.span {(p.1 : ℤ)})
    (hplace : (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm
        (⟨p.1, p.2⟩ : Nat.Primes) = v)
    (hmatch : a.exponent p = chapter12RationalFiniteValuationExponent x p) :
    Valued.v (chapter12RationalFinitePartAfterDivision x a.q v) = 1 := by
  have hx0 : x.1.2 v ≠ 0 := by
    exact (LastLib.Book04AdelesAndIdeles.Chapter07.chapter07_idele_coordinates_are_nonzero
      ℤ ℚ x).2 v
  have hxv : Valued.v (x.1.2 v) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 hx0
  have hvalx : Valued.v (x.1.2 v) =
      WithZero.exp (-(chapter12RationalFiniteValuationExponent x p)) := by
    unfold chapter12RationalFiniteValuationExponent
    rw [hplace]
    rw [dif_neg hxv, WithZero.toAdd_unzero_eq_log hxv]
    simpa only [neg_neg] using (WithZero.exp_log hxv).symm
  have hqpos : 0 < a.q := Chapter12RationalValuationProfile.q_pos a
  have hq0 : a.q ≠ 0 := ne_of_gt hqpos
  have hqv : v.valuation ℚ a.q = WithZero.exp (-(a.exponent p)) :=
    chapter12_rational_profile_valuation a p v hV
  have hqbase : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) a.q) =
      v.valuation ℚ a.q := by
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
    simp only [Function.comp_apply]
    exact v.valuedAdicCompletion_eq_valuation' a.q
  have hqinv : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) a.q⁻¹) =
      (v.valuation ℚ a.q)⁻¹ := by
    simp only [map_inv₀, hqbase]
  rw [chapter12RationalFinitePartAfterDivision]
  have hcoord : (algebraMap ℚ (chapter12FiniteAdeleRing ℤ ℚ) a.q⁻¹) v =
      algebraMap ℚ (v.adicCompletion ℚ) a.q⁻¹ :=
    IsDedekindDomain.FiniteAdeleRing.algebraMap_apply ℤ ℚ a.q⁻¹ v
  have hmul : ((x.1.2 * algebraMap ℚ (chapter12FiniteAdeleRing ℤ ℚ)
      a.q⁻¹) v) = x.1.2 v * (algebraMap ℚ
        (chapter12FiniteAdeleRing ℤ ℚ) a.q⁻¹) v := by
    rfl
  rw [hmul, hcoord, map_mul, hvalx, hqinv, hqv]
  rw [hmatch]
  exact mul_inv_cancel₀ (by simp)

/-- The real coordinate of a rational idele in a chosen one-place portrait. -/
def chapter12RationalRealCoordinate
    (P : Chapter12RationalInfinitePortrait)
    (x : chapter12RationalIdeles) : ℝ :=
  P.equiv x.1.1

structure Chapter12RationalIdeleNormalization
    (x : chapter12RationalIdeles) where
  profile : Chapter12RationalValuationProfile
  profile_matches_idele :
    ∀ p, profile.exponent p = chapter12RationalFiniteValuationExponent x p
  finite_unit_after_division :
    chapter12RationalFinitePartIsUnit x profile.q
  real_coordinate_ne_zero :
    ∀ P : Chapter12RationalInfinitePortrait,
      chapter12RationalRealCoordinate P x ≠ 0

theorem chapter12_rational_idele_has_finite_valuation_normalization
    (x : chapter12RationalIdeles) :
    Nonempty (Chapter12RationalIdeleNormalization x) := by
  classical
  let e : IsDedekindDomain.HeightOneSpectrum ℤ ≃ Nat.Primes :=
    Rat.HeightOneSpectrum.primesEquiv (R := ℤ)
  let f : Nat.Primes ≃ Chapter12RationalPrime :=
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun p => ⟨p.1, p.2⟩
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  have hunit_v :=
    LastLib.Book04AdelesAndIdeles.Chapter07.chapter07_idele_has_integral_units_at_almost_all_finite_places
      ℤ ℚ x
  have hzeroNat : ∀ᶠ p : Nat.Primes in cofinite,
      chapter12RationalFiniteValuationExponent x (f p) = 0 := by
    have hpull := e.symm.injective.tendsto_cofinite hunit_v
    filter_upwards [hpull] with p hp
    have heq : (⟨(f p).1, (f p).2⟩ : Nat.Primes) = p := by
      rfl
    apply chapter12_rational_exponent_eq_zero_of_valued_eq_one x (f p)
    rw [heq]
    exact hp
  have hzero : ∀ᶠ p : Chapter12RationalPrime in cofinite,
      chapter12RationalFiniteValuationExponent x p = 0 := by
    have hpull := f.symm.injective.tendsto_cofinite hzeroNat
    filter_upwards [hpull] with p hp
    have hp' : chapter12RationalFiniteValuationExponent x (f (f.symm p)) = 0 := hp
    rw [f.apply_symm_apply p] at hp'
    exact hp'
  let profile : Chapter12RationalValuationProfile :=
    { exponent := chapter12RationalFiniteValuationExponent x
      support := hzero.toFinset
      support_spec := by
        intro p hp
        apply not_not.mp
        intro hnot
        have hmem := (hzero.mem_toFinset).2 hnot
        exact hp (by simpa only [Set.mem_ofPred_eq] using hmem) }
  refine ⟨{
    profile := profile
    profile_matches_idele := by
      intro p
      rfl
    finite_unit_after_division := by
      intro v
      let p : Chapter12RationalPrime := f (e v)
      have hpNat : (⟨p.1, p.2⟩ : Nat.Primes) = e v := by
        rfl
      have hplace : (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm
          (⟨p.1, p.2⟩ : Nat.Primes) = v := by
        change e.symm (⟨p.1, p.2⟩ : Nat.Primes) = v
        rw [hpNat, e.symm_apply_apply]
      have hspan : v.asIdeal = Ideal.span {(p.1 : ℤ)} := by
        rw [← hplace]
        exact chapter12_rational_height_one_span p
      have hmatch : profile.exponent p =
          chapter12RationalFiniteValuationExponent x p := by
        rfl
      have hyval : Valued.v
          (chapter12RationalFinitePartAfterDivision x profile.q v) = 1 :=
        chapter12_rational_finite_division_valued_eq_one x profile v p
          hspan hplace hmatch
      have hyint : chapter12RationalFinitePartAfterDivision x profile.q v ∈
          v.adicCompletionIntegers ℚ := by
        apply (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
          ℤ ℚ v).2
        rw [hyval]
      let z : v.adicCompletionIntegers ℚ :=
        ⟨chapter12RationalFinitePartAfterDivision x profile.q v, hyint⟩
      have hzunit : IsUnit z := by
        apply (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
          (K := ℚ) (v := v)).2
        simpa [z] using hyval
      let u : (v.adicCompletionIntegers ℚ)ˣ := hzunit.unit
      refine ⟨u, ?_⟩
      change (u : v.adicCompletion ℚ) =
        chapter12RationalFinitePartAfterDivision x profile.q v
      have hu : (u : v.adicCompletionIntegers ℚ) = z := by
        exact hzunit.unit_spec
      rw [hu]
    real_coordinate_ne_zero := by
      intro P
      have hxi :=
        (LastLib.Book04AdelesAndIdeles.Chapter07.chapter07_idele_coordinates_are_nonzero
          ℤ ℚ x).1
      have hnonzero : x.1.1 ≠ 0 := by
        intro hx
        let v : NumberField.InfinitePlace ℚ := Classical.choice inferInstance
        apply hxi v
        rw [hx]
        rfl
      intro hz
      apply hnonzero
      apply P.equiv.injective
      change P.equiv x.1.1 = 0 at hz
      simpa using hz
  }⟩

theorem chapter12_rational_normalization_scalar_is_positive
    {x : chapter12RationalIdeles}
    (N : Chapter12RationalIdeleNormalization x) :
    0 < N.profile.q :=
  Chapter12RationalValuationProfile.q_pos N.profile

/-- The positive real coordinate after removing the finite valuation profile. -/
def chapter12RationalNormalizedRealCoordinate
    (P : Chapter12RationalInfinitePortrait)
    (x : chapter12RationalIdeles) (q : ℚ) : ℝ :=
  |chapter12RationalRealCoordinate P x| / (q : ℝ)

/-- The extra principal sign correction used to make the real coordinate positive. -/
def chapter12RationalSignCorrectedNormalizer (P : Chapter12RationalInfinitePortrait)
    (x : chapter12RationalIdeles) (q : ℚ) : ℚ :=
  if 0 ≤ chapter12RationalRealCoordinate P x / (q : ℝ) then q else -q

theorem chapter12_rational_normalized_real_coordinate_pos
    (P : Chapter12RationalInfinitePortrait)
    (x : chapter12RationalIdeles) (q : ℚ) (hq : 0 < q)
    (hx : chapter12RationalRealCoordinate P x ≠ 0) :
    0 < chapter12RationalNormalizedRealCoordinate P x q := by
  exact div_pos (abs_pos.mpr hx) (Rat.cast_pos.mpr hq)

/-! ## The rational idele class portraits -/

/-- A finite-place unit coordinate in the rational finite ideles. -/
def chapter12RationalFiniteUnitCoordinates :
    Set chapter12RationalFiniteIdeles :=
  {x | ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
    ∃ u : (v.adicCompletionIntegers ℚ)ˣ,
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) u = x.1 v}

theorem chapter12_rational_finite_unit_coordinates_iff
    (x : chapter12RationalFiniteIdeles) :
    x ∈ chapter12RationalFiniteUnitCoordinates ↔
      ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
        ∃ u : (v.adicCompletionIntegers ℚ)ˣ,
          algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) u = x.1 v :=
  Iff.rfl

/- The class portrait uses Mathlib's canonical `𝓞 ℚ` model.  The explicit
   finite-place portraits above retain the more convenient `ℤ` model; the
   equivalence between those two models is not definitionally transparent. -/
abbrev chapter12RationalClassTarget :=
  ℝ≥0ˣ × chapter12CanonicalFiniteUnitIdeles ℚ

structure Chapter12RationalClassPortrait
    (M : Chapter12IdeleModuleData (𝓞 ℚ) ℚ) where
  equivalence : chapter12IdeleClassGroup (𝓞 ℚ) ℚ ≃* chapter12RationalClassTarget
  first_coordinate_is_module :
    ∀ x : chapter12Ideles (𝓞 ℚ) ℚ,
      (equivalence (chapter12IdeleClassMk (𝓞 ℚ) ℚ x)).1 =
        chapter12IdeleModuleUnit M x

theorem chapter12_rational_idele_class_group_portrait :
    Nonempty (Chapter12RationalClassPortrait
      (chapter12CanonicalIdeleModuleData ℚ)) := by
  have harch_surj :
      Function.Surjective (chapter09ArchimedeanUnitEmbedding ℚ) := by
    intro x
    let xi : (∀ v : InfinitePlace ℚ, v.Completion)ˣ := x.1
    let c : (Rat.infinitePlace.Completion)ˣ :=
      (MulEquiv.piUnits xi) Rat.infinitePlace
    let r : ℝˣ := Units.map
      (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
        Rat.isReal_infinitePlace).toMonoidHom c
    have hxmod : chapter09InfiniteIdeleModule x.1 = 1 :=
      (chapter09KInfinityOne_mem_iff).1 x.2
    have hprod : chapter09InfiniteIdeleModule x.1 = chapter09NormUnit c := by
      change chapter09InfiniteIdeleModule xi = chapter09NormUnit c
      unfold chapter09InfiniteIdeleModule
      simpa [c] using
        (Fintype.prod_subsingleton
          (fun v : InfinitePlace ℚ =>
            chapter09NormUnit ((MulEquiv.piUnits xi) v)) Rat.infinitePlace)
    have hunit : chapter09NormUnit c = 1 := by
      rw [← hprod, hxmod]
    have hunit' : (chapter09NormUnit c : ℝ≥0) = 1 :=
      congrArg Units.val hunit
    have hc_norm : ‖(c : Rat.infinitePlace.Completion)‖ = 1 := by
      have hc' : ‖(c : Rat.infinitePlace.Completion)‖₊ = 1 := by
        simpa [chapter09NormUnit] using hunit'
      have := congrArg (fun y : ℝ≥0 => (y : ℝ)) hc'
      simpa using this
    have hr_norm : ‖(r : ℝ)‖ = 1 := by
      have hr_nn : ‖(r : ℝ)‖₊ = ‖(c : Rat.infinitePlace.Completion)‖₊ := by
        have hzero :
            (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal
              Rat.isReal_infinitePlace) 0 = 0 := by
          change (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
            Rat.isReal_infinitePlace) 0 = 0
          exact (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
            Rat.isReal_infinitePlace).map_zero
        have hnorm :=
          (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal
            Rat.isReal_infinitePlace).isometry.nnnorm_map_of_map_zero hzero
            (c : Rat.infinitePlace.Completion)
        change ‖(NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
          Rat.isReal_infinitePlace) (c : Rat.infinitePlace.Completion)‖₊ =
          ‖(c : Rat.infinitePlace.Completion)‖₊
        exact hnorm
      have := congrArg (fun y : ℝ≥0 => (y : ℝ)) hr_nn
      simpa [hc_norm] using this
    have hr_abs : |(r : ℝ)| = 1 := by
      simpa [Real.norm_eq_abs] using hr_norm
    rcases (abs_eq (by norm_num)).1 hr_abs with hr | hr
    · refine ⟨1, ?_⟩
      apply Subtype.ext
      change chapter09InfiniteUnitEmbedding ℚ (1 : (𝓞 ℚ)ˣ) = xi
      apply (MulEquiv.piUnits).injective
      funext v
      have hv : v = Rat.infinitePlace := Subsingleton.elim _ _
      subst v
      change (MulEquiv.piUnits
          (chapter09InfiniteUnitEmbedding ℚ (1 : (𝓞 ℚ)ˣ))) Rat.infinitePlace = c
      have hc : c = 1 := by
        apply Units.ext
        apply (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
          Rat.isReal_infinitePlace).injective
        simpa [r] using hr
      rw [hc]
      exact congrArg (fun f : ∀ v : InfinitePlace ℚ, v.Completionˣ =>
        f Rat.infinitePlace)
        ((MulEquiv.piUnits :
          (∀ v : InfinitePlace ℚ, v.Completion)ˣ ≃*
            (∀ v : InfinitePlace ℚ, v.Completionˣ)).map_one)
    · refine ⟨-1, ?_⟩
      apply Subtype.ext
      change chapter09InfiniteUnitEmbedding ℚ (-1 : (𝓞 ℚ)ˣ) = xi
      apply (MulEquiv.piUnits).injective
      funext v
      have hv : v = Rat.infinitePlace := Subsingleton.elim _ _
      subst v
      change (MulEquiv.piUnits
          (chapter09InfiniteUnitEmbedding ℚ (-1 : (𝓞 ℚ)ˣ))) Rat.infinitePlace = c
      have hc : c = (MulEquiv.piUnits
          (chapter09InfiniteUnitEmbedding ℚ (-1 : (𝓞 ℚ)ˣ))) Rat.infinitePlace := by
        apply Units.ext
        apply (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
          Rat.isReal_infinitePlace).injective
        have hneg :
            (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
              Rat.isReal_infinitePlace)
                ((MulEquiv.piUnits
                  (chapter09InfiniteUnitEmbedding ℚ (-1 : (𝓞 ℚ)ˣ))) Rat.infinitePlace :
                  Rat.infinitePlace.Completion) = -1 := by
          have hcoord :
              ((MulEquiv.piUnits
                (chapter09InfiniteUnitEmbedding ℚ (-1 : (𝓞 ℚ)ˣ))) Rat.infinitePlace :
                Rat.infinitePlace.Completion) =
                ((-1 : ℚ) : Rat.infinitePlace.Completion) := by
            change algebraMap ℚ Rat.infinitePlace.Completion (-1 : ℚ) =
              ((-1 : ℚ) : Rat.infinitePlace.Completion)
            simp
          rw [hcoord]
          simp
        simpa [r, hneg] using hr
      rw [hc]
  have harch_inj :
      Function.Injective (chapter09ArchimedeanUnitEmbedding ℚ) := by
    have hring : Function.Injective
        ((algebraMap ℚ (Chapter09InfiniteAdele ℚ)).comp
          (algebraMap (𝓞 ℚ) ℚ)) := by
      intro a b hab
      apply (IsFractionRing.injective (𝓞 ℚ) ℚ)
      apply RingHom.injective (algebraMap ℚ (Chapter09InfiniteAdele ℚ))
      exact hab
    intro a b hab
    apply Units.map_injective hring
    simpa [chapter09ArchimedeanUnitEmbedding, chapter09InfiniteUnitEmbedding] using
      congrArg Subtype.val hab
  let s₀ : chapter09FiniteUnitIdeles ℚ →*
      Chapter09ArchFiniteUnitNumerator ℚ := {
    toFun := fun u => (1, u)
    map_one' := by simp
    map_mul' := by intro u v; simp }
  let s : chapter09FiniteUnitIdeles ℚ →*
      Chapter09ArchFiniteUnitKernel ℚ :=
    (QuotientGroup.mk' (chapter09GlobalUnitDiagonal ℚ).range).comp s₀
  have hs_inj : Function.Injective s := by
    intro u v huv
    apply Subtype.ext
    change QuotientGroup.mk' (chapter09GlobalUnitDiagonal ℚ).range
        (s₀ u) = QuotientGroup.mk' (chapter09GlobalUnitDiagonal ℚ).range (s₀ v) at huv
    have huv' := (QuotientGroup.eq_iff_div_mem).1 huv
    rcases huv' with ⟨a, ha⟩
    have hfirst := congrArg Prod.fst ha
    have harch : chapter09ArchimedeanUnitEmbedding ℚ a = 1 := by
      apply Subtype.ext
      simpa [s₀, chapter09GlobalUnitDiagonal] using hfirst
    have ha1 : a = 1 := harch_inj (by simpa using harch)
    have hsecond := congrArg Prod.snd ha
    have huv : u = v := by
      have hmul := congrArg (fun z : chapter09FiniteUnitIdeles ℚ => z * v) hsecond
      simpa [s₀, chapter09GlobalUnitDiagonal, ha1, div_eq_mul_inv, mul_assoc] using
        hmul.symm
    exact congrArg Subtype.val huv
  have hs_surj : Function.Surjective s := by
    intro z
    obtain ⟨w, rfl⟩ :=
      QuotientGroup.mk'_surjective (chapter09GlobalUnitDiagonal ℚ).range z
    rcases harch_surj w.1 with ⟨a, ha⟩
    let u : chapter09FiniteUnitIdeles ℚ :=
      (chapter09FiniteUnitSubtypeEmbedding ℚ a)⁻¹ * w.2
    refine ⟨u, ?_⟩
    change QuotientGroup.mk' (chapter09GlobalUnitDiagonal ℚ).range
        (s₀ u) = QuotientGroup.mk' (chapter09GlobalUnitDiagonal ℚ).range w
    apply (QuotientGroup.eq_iff_div_mem).2
    refine ⟨a⁻¹, ?_⟩
    apply Prod.ext <;>
      simp [s₀, u, chapter09GlobalUnitDiagonal, ha, div_eq_mul_inv, mul_assoc]
  let eAF : Chapter09ArchFiniteUnitKernel ℚ ≃*
      chapter09FiniteUnitIdeles ℚ :=
    (MulEquiv.ofBijective s ⟨hs_inj, hs_surj⟩).symm
  let _ : IsPrincipalIdealRing (𝓞 ℚ) :=
    IsPrincipalIdealRing.of_surjective
      (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm.toRingHom
      (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm.surjective
  have hclass_sub : Subsingleton (ClassGroup (𝓞 ℚ)) := by
    refine ⟨fun x y => ?_⟩
    have htriv : ∀ z : ClassGroup (𝓞 ℚ), z = 1 := by
      intro z
      refine ClassGroup.induction ℚ ?_ z
      intro I
      exact ClassGroup.mk_eq_one_iff.mpr
        (I : FractionalIdeal (𝓞 ℚ)⁰ ℚ).isPrincipal
    exact (htriv x).trans (htriv y).symm
  let fclass : Chapter09ArchFiniteUnitKernel ℚ →*
      chapter09ClassNormOne ℚ := chapter09ArchFiniteToClassNormOne ℚ
  have fclass_inj : Function.Injective fclass :=
    (chapter09CompactKernel_short_exact ℚ).left_injective
  have fclass_surj : Function.Surjective fclass := by
    intro z
    have hz : chapter09NormOneClassIdealClassMap ℚ z = 1 :=
      @Subsingleton.elim _ hclass_sub _ _
    exact ((chapter09CompactKernel_short_exact ℚ).exact z).mp hz
  let eClass : Chapter09ArchFiniteUnitKernel ℚ ≃*
      chapter09ClassNormOne ℚ :=
    MulEquiv.ofBijective fclass ⟨fclass_inj, fclass_surj⟩
  let eNormF : chapter09ClassNormOne ℚ ≃*
      chapter09FiniteUnitIdeles ℚ := eClass.symm.trans eAF
  obtain ⟨t, _ht, ht_right⟩ :=
    chapter09_exists_class_module_section ℚ Rat.infinitePlace
  have ht_apply (q : Chapter09PositiveReal) :
      chapter09IdeleClassModule ℚ (t q) = q := by
    have h := congrArg
      (fun f : Chapter09PositiveReal →* Chapter09PositiveReal => f q) ht_right
    simpa using h
  let p : Chapter09IdeleClassGroup ℚ →*
      chapter09ClassNormOne ℚ := {
    toFun := fun x =>
      ⟨x * (t (chapter09IdeleClassModule ℚ x))⁻¹, by
        apply (chapter09ClassNormOne_mem_iff).2
        simpa only [map_mul, map_inv, ht_apply] using
          mul_inv_cancel (chapter09IdeleClassModule ℚ x)⟩
    map_one' := by
      apply Subtype.ext
      simp
    map_mul' := by
      intro x y
      apply Subtype.ext
      change x * y * (t (chapter09IdeleClassModule ℚ (x * y)))⁻¹ =
        (x * (t (chapter09IdeleClassModule ℚ x))⁻¹) *
          (y * (t (chapter09IdeleClassModule ℚ y))⁻¹)
      rw [(chapter09IdeleClassModule ℚ).map_mul, t.map_mul, mul_inv_rev]
      ac_rfl }
  let eSplit : Chapter09IdeleClassGroup ℚ ≃*
      chapter09ClassNormOne ℚ × Chapter09PositiveReal := {
    toFun := fun x => (p x, chapter09IdeleClassModule ℚ x)
    invFun := fun z => (z.1 : Chapter09IdeleClassGroup ℚ) * t z.2
    left_inv := by
      intro x
      change (p x : Chapter09IdeleClassGroup ℚ) *
        t (chapter09IdeleClassModule ℚ x) = x
      change (x * (t (chapter09IdeleClassModule ℚ x))⁻¹) *
        t (chapter09IdeleClassModule ℚ x) = x
      rw [mul_assoc, inv_mul_cancel, mul_one]
    right_inv := by
      intro z
      have hz : chapter09IdeleClassModule ℚ
          (z.1 : Chapter09IdeleClassGroup ℚ) = 1 :=
        (chapter09ClassNormOne_mem_iff).1 z.1.property
      apply Prod.ext
      · apply Subtype.ext
        change (z.1 : Chapter09IdeleClassGroup ℚ) * t z.2 *
            (t (chapter09IdeleClassModule ℚ
              ((z.1 : Chapter09IdeleClassGroup ℚ) * t z.2)))⁻¹ = z.1
        rw [map_mul, hz, one_mul, ht_apply]
        simp
      · change chapter09IdeleClassModule ℚ
          ((z.1 : Chapter09IdeleClassGroup ℚ) * t z.2) = z.2
        rw [map_mul, hz, one_mul, ht_apply]
    map_mul' := by
      intro x y
      exact p.map_mul x y |> fun h => by
        simp [p, t.map_mul, mul_inv_rev]
        ac_rfl }
  let eFinal : chapter12IdeleClassGroup (𝓞 ℚ) ℚ ≃*
      chapter12RationalClassTarget :=
    (eSplit.trans (MulEquiv.prodCongr eNormF (MulEquiv.refl _))).trans
      MulEquiv.prodComm
  refine ⟨{ equivalence := eFinal, first_coordinate_is_module := ?_ }⟩
  intro x
  apply Units.ext
  change ((eFinal (chapter12IdeleClassMk (𝓞 ℚ) ℚ x)).1 : ℝ≥0) =
    (chapter09IdeleModuleNNRealHom ℚ x : ℝ≥0)
  change ((chapter09IdeleClassModule ℚ
      (QuotientGroup.mk (x : Chapter09Idele ℚ)) : Chapter09PositiveReal) : ℝ≥0) =
    (chapter09IdeleModuleNNRealHom ℚ x : ℝ≥0)
  rfl

abbrev chapter12RationalNormOneClassCarrier
    (M : Chapter12IdeleModuleData (𝓞 ℚ) ℚ) :=
  chapter12NormOneIdeleClassCarrier M

theorem chapter12_rational_norm_one_class_group_portrait :
    Nonempty (chapter12RationalNormOneClassCarrier
      (chapter12CanonicalIdeleModuleData ℚ) ≃*
      chapter12CanonicalFiniteUnitIdeles ℚ) := by
  obtain ⟨P⟩ := chapter12_rational_idele_class_group_portrait
  let M := chapter12CanonicalIdeleModuleData ℚ
  let C := chapter12IdeleClassGroup (𝓞 ℚ) ℚ
  let N := chapter12RationalNormOneClassCarrier M
  let F := chapter12CanonicalFiniteUnitIdeles ℚ
  have hfirst (c : N) : (P.equivalence c.1).1 = 1 := by
    obtain ⟨x, hx⟩ :=
      QuotientGroup.mk'_surjective (chapter12PrincipalIdeleSubgroup (𝓞 ℚ) ℚ) c.1
    have hmodule : M.module x = 1 := by
      have hc : chapter12IdeleClassModule M c.1 = 1 := c.2
      rw [← hx] at hc
      change chapter12IdeleClassModule M (chapter12IdeleClassMk (𝓞 ℚ) ℚ x) = 1 at hc
      rw [chapter12IdeleClassModule_apply] at hc
      exact hc
    have hcoord := P.first_coordinate_is_module x
    have hcoord' : (P.equivalence c.1).1 = chapter12IdeleModuleUnit M x := by
      rw [← hx]
      exact hcoord
    rw [hcoord']
    apply Units.ext
    change M.module x = (1 : ℝ≥0)
    exact hmodule
  have hkernel (c : C) (hc : (P.equivalence c).1 = 1) :
      c ∈ chapter12NormOneIdeleClassSubgroup M := by
    obtain ⟨x, hx⟩ :=
      QuotientGroup.mk'_surjective (chapter12PrincipalIdeleSubgroup (𝓞 ℚ) ℚ) c
    have hcoord := P.first_coordinate_is_module x
    have hcoord' : (P.equivalence c).1 = chapter12IdeleModuleUnit M x := by
      rw [← hx]
      exact hcoord
    have hu : chapter12IdeleModuleUnit M x = 1 := by
      rw [← hcoord']
      exact hc
    have hmodule : M.module x = 1 := by
      have hval := congrArg Units.val hu
      change M.module x = (1 : ℝ≥0) at hval
      exact hval
    change c ∈ chapter12NormOneIdeleClassSubgroup M
    change chapter12IdeleClassModule M c = 1
    rw [← hx]
    change chapter12IdeleClassModule M (chapter12IdeleClassMk (𝓞 ℚ) ℚ x) = 1
    rw [chapter12IdeleClassModule_apply]
    exact hmodule
  let e : N ≃* F := {
    toFun := fun c => (P.equivalence c.1).2
    invFun := fun f =>
      ⟨P.equivalence.symm (1, f), hkernel _ (by
        exact congrArg Prod.fst (P.equivalence.apply_symm_apply (1, f)))⟩
    left_inv := by
      intro c
      apply Subtype.ext
      apply P.equivalence.injective
      rw [P.equivalence.apply_symm_apply]
      apply Prod.ext
      · exact (hfirst c).symm
      · rfl
    right_inv := by
      intro f
      change (P.equivalence (P.equivalence.symm (1, f))).2 = f
      exact congrArg Prod.snd (P.equivalence.apply_symm_apply (1, f))
    map_mul' := by
      intro c d
      change (P.equivalence (c.1 * d.1)).2 =
        (P.equivalence c.1).2 * (P.equivalence d.1).2
      rw [P.equivalence.map_mul]
      rfl }
  exact ⟨e⟩

def chapter12RationalGlobalUnitValues : Set ℤ :=
  {1, -1}

theorem chapter12_rational_global_units_are_signs :
    Set.range (fun u : ℤˣ => (u : ℤ)) = chapter12RationalGlobalUnitValues := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    rcases Int.units_eq_one_or u with rfl | rfl <;>
      simp [chapter12RationalGlobalUnitValues]
  · intro hx
    rcases hx with rfl | rfl
    · exact ⟨1, by simp⟩
    · exact ⟨-1, by simp⟩

/-! ## Rational ray class quotients -/

abbrev chapter12RationalRaySignSubgroup (N : ℕ) : Subgroup (ZMod N)ˣ :=
  chapter11ResidueSignSubgroup N

abbrev chapter12RationalRayClassWithInfinity (N : ℕ) (hN : 0 < N) :=
  chapter11RationalRayClassGroup N hN .included

abbrev chapter12RationalRayClassWithoutInfinity (N : ℕ) (hN : 0 < N) :=
  chapter11RationalRayClassGroup N hN .omitted

theorem chapter12_rational_ray_class_group_with_infinity
    (N : ℕ) (hN : 0 < N) :
    Nonempty (chapter12RationalRayClassWithInfinity N hN ≃*
      (ZMod N)ˣ) :=
  chapter11_rational_infinite_ray_class_group_equiv_residue_units N hN

theorem chapter12_rational_ray_class_group_without_infinity
    (N : ℕ) (hN : 0 < N) :
    Nonempty (chapter12RationalRayClassWithoutInfinity N hN ≃*
      (ZMod N)ˣ ⧸ chapter12RationalRaySignSubgroup N) :=
  chapter11_rational_omitting_infinity_quotients_by_signs N hN

end
end LastLib.Book04AdelesAndIdeles.Chapter12
