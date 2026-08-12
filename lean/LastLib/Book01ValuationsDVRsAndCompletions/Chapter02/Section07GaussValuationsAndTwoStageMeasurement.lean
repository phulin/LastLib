import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter02.Section01WhyTheValuesFormAGroup
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter02.Section03TheDecisiveEquality

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter02

/-!
# Chapter 2: Valuations

This file is a statement-generation pass for Chapter 2 of *Valuations, DVRs,
and Completions*.  The declarations are deliberately self-contained: they
use Mathlib's `AddValuation` where it has the required interface and introduce
chapter-local names for the constructions that are specific to the exposition.
-/

noncomputable section

open Set Function
open scoped BigOperators LaurentSeries
open HahnSeries Polynomial

/-! # Book 1, Chapter 2, Section 2.7: Gauss Valuations and Two-Stage Measurement
-/

/-! ## 2.7. Gauss valuations and two-stage examples -/

def Chapter02WeightedCoefficientValue
    {K Γ Λ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (v : AddValuation K (WithTop Γ)) (e : Γ →+o Λ) (α : Λ)
    (a : K) (i : ℕ) : WithTop Λ :=
  if ha : v a = ⊤ then ⊤
  else (e ((v a).untop ha) + i • α : Λ)

def Chapter02GaussValuationFunction
    {K Γ Λ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (v : AddValuation K (WithTop Γ)) (e : Γ →+o Λ) (α : Λ)
    (f : Polynomial K) : WithTop Λ :=
  if hf : f.support.Nonempty then
    f.support.inf' hf (fun i => Chapter02WeightedCoefficientValue v e α (f.coeff i) i)
  else ⊤

theorem chapter02_gauss_valuation_sum_inequality
    {K Γ Λ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (v : AddValuation K (WithTop Γ)) (e : Γ →+o Λ) (α : Λ)
    (f g : Polynomial K) :
    min (Chapter02GaussValuationFunction v e α f)
        (Chapter02GaussValuationFunction v e α g) ≤
      Chapter02GaussValuationFunction v e α (f + g) := by
  classical
  let W : Polynomial K → ℕ → WithTop Λ :=
    fun p i => Chapter02WeightedCoefficientValue v e α (p.coeff i) i
  have hG (p : Polynomial K) (i : ℕ) :
      Chapter02GaussValuationFunction v e α p ≤ W p i := by
    by_cases hp : p.support.Nonempty
    · by_cases hi : i ∈ p.support
      · simp only [W, Chapter02GaussValuationFunction, dif_pos hp]
        exact Finset.inf'_le _ hi
      · have hzero : p.coeff i = 0 := Polynomial.notMem_support_iff.mp hi
        have hp' : p.support.Nonempty := hp
        obtain ⟨b, hb⟩ := hp'
        simp only [W, Chapter02GaussValuationFunction, dif_pos hp]
        exact (Finset.inf'_le _ hb).trans (by
          simp [Chapter02WeightedCoefficientValue, hzero])
    · have hp0 : p = 0 := by
        by_contra hp0
        exact hp (Polynomial.support_nonempty.mpr hp0)
      subst p
      simp [W, Chapter02GaussValuationFunction, Chapter02WeightedCoefficientValue]
  have hW (i : ℕ) : min (W f i) (W g i) ≤ W (f + g) i := by
    by_cases hfi : f.coeff i = 0
    · simp [W, Chapter02WeightedCoefficientValue, hfi]
    by_cases hgi : g.coeff i = 0
    · simp [W, Chapter02WeightedCoefficientValue, hgi]
    by_cases hsum : f.coeff i + g.coeff i = 0
    · simp [W, Chapter02WeightedCoefficientValue, hsum]
    have hfv : v (f.coeff i) ≠ (⊤ : WithTop Γ) :=
      (AddValuation.ne_top_iff v).2 hfi
    have hgv : v (g.coeff i) ≠ (⊤ : WithTop Γ) :=
      (AddValuation.ne_top_iff v).2 hgi
    have hsv : v (f.coeff i + g.coeff i) ≠ (⊤ : WithTop Γ) :=
      (AddValuation.ne_top_iff v).2 hsum
    rcases le_total (v (f.coeff i)) (v (g.coeff i)) with hfg | hgf
    · have hmin : W f i ≤ W g i := by
        simp only [W, Chapter02WeightedCoefficientValue, dif_neg hfv, dif_neg hgv]
        have hfg' :
            ((v (f.coeff i)).untop hfv : WithTop Γ) ≤
              (v (g.coeff i)).untop hgv := by
          simpa only [WithTop.coe_untop] using hfg
        exact WithTop.coe_le_coe.mpr
          (add_le_add_left ((OrderHomClass.monotone e)
            (WithTop.coe_le_coe.mp hfg')) (i • α))
      have hsumv : v (f.coeff i) ≤ v (f.coeff i + g.coeff i) := by
        have h := v.map_add (f.coeff i) (g.coeff i)
        simpa [min_eq_left hfg] using h
      have hsumv' : (v (f.coeff i)).untop hfv ≤
          (v (f.coeff i + g.coeff i)).untop hsv :=
        WithTop.coe_le_coe.mp (by
          simpa only [WithTop.coe_untop] using hsumv)
      have hweighted := add_le_add_left ((OrderHomClass.monotone e) hsumv') (i • α)
      rw [min_eq_left hmin]
      simp only [W, Polynomial.coeff_add, Chapter02WeightedCoefficientValue,
        dif_neg hfv, dif_neg hsv]
      exact WithTop.coe_le_coe.mpr hweighted
    · have hmin : W g i ≤ W f i := by
        simp only [W, Chapter02WeightedCoefficientValue, dif_neg hgv, dif_neg hfv]
        have hgf' :
            ((v (g.coeff i)).untop hgv : WithTop Γ) ≤
              (v (f.coeff i)).untop hfv := by
          simpa only [WithTop.coe_untop] using hgf
        exact WithTop.coe_le_coe.mpr
          (add_le_add_left ((OrderHomClass.monotone e)
            (WithTop.coe_le_coe.mp hgf')) (i • α))
      have hsumv : v (g.coeff i) ≤ v (f.coeff i + g.coeff i) := by
        have h := v.map_add (f.coeff i) (g.coeff i)
        simpa [min_eq_right hgf] using h
      have hsumv' : (v (g.coeff i)).untop hgv ≤
          (v (f.coeff i + g.coeff i)).untop hsv :=
        WithTop.coe_le_coe.mp (by
          simpa only [WithTop.coe_untop] using hsumv)
      have hweighted := add_le_add_left ((OrderHomClass.monotone e) hsumv') (i • α)
      rw [min_eq_right hmin]
      simp only [W, Polynomial.coeff_add, Chapter02WeightedCoefficientValue,
        dif_neg hgv, dif_neg hsv]
      exact WithTop.coe_le_coe.mpr hweighted
  by_cases hf : f.support.Nonempty
  · by_cases hg : g.support.Nonempty
    · by_cases hsum : (f + g).support.Nonempty
      · simp only [Chapter02GaussValuationFunction, dif_pos hf, dif_pos hg, dif_pos hsum]
        rw [Finset.le_inf'_iff]
        intro i hi
        simpa only [W, Chapter02GaussValuationFunction, dif_pos hf, dif_pos hg] using
          ((min_le_min (hG f i) (hG g i)).trans (hW i))
      · have hzero : f + g = 0 := by
            by_contra hzero
            exact hsum (Polynomial.support_nonempty.mpr hzero)
        simp [Chapter02GaussValuationFunction, hzero]
    · have hg0 : g = 0 := by
        by_contra hg0
        exact hg (Polynomial.support_nonempty.mpr hg0)
      subst g
      simp [Chapter02GaussValuationFunction]
  · have hf0 : f = 0 := by
      by_contra hf0
      exact hf (Polynomial.support_nonempty.mpr hf0)
    subst f
    simp [Chapter02GaussValuationFunction]

theorem chapter02_gauss_valuation_is_multiplicative
    {K Γ Λ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (v : AddValuation K (WithTop Γ)) (e : Γ →+o Λ) (α : Λ)
    (f g : Polynomial K) :
    Chapter02GaussValuationFunction v e α (f * g) =
      Chapter02GaussValuationFunction v e α f +
        Chapter02GaussValuationFunction v e α g := by
  classical
  let W : Polynomial K → ℕ → WithTop Λ :=
    fun p i => Chapter02WeightedCoefficientValue v e α (p.coeff i) i
  have hG (p : Polynomial K) (i : ℕ) :
      Chapter02GaussValuationFunction v e α p ≤ W p i := by
    by_cases hp : p.support.Nonempty
    · by_cases hi : i ∈ p.support
      · simp only [W, Chapter02GaussValuationFunction, dif_pos hp]
        exact Finset.inf'_le _ hi
      · have hzero : p.coeff i = 0 := Polynomial.notMem_support_iff.mp hi
        have hp' : p.support.Nonempty := hp
        obtain ⟨b, hb⟩ := hp'
        simp only [W, Chapter02GaussValuationFunction, dif_pos hp]
        exact (Finset.inf'_le _ hb).trans (by
          simp [Chapter02WeightedCoefficientValue, hzero])
    · have hp0 : p = 0 := by
        by_contra hp0
        exact hp (Polynomial.support_nonempty.mpr hp0)
      subst p
      simp [W, Chapter02GaussValuationFunction, Chapter02WeightedCoefficientValue]
  have hterm (k l : ℕ) :
      Chapter02GaussValuationFunction v e α f +
          Chapter02GaussValuationFunction v e α g ≤
        Chapter02WeightedCoefficientValue v e α
          (f.coeff k * g.coeff l) (k + l) := by
    by_cases hfk : f.coeff k = 0
    · simp [Chapter02WeightedCoefficientValue, hfk]
    by_cases hgl : g.coeff l = 0
    · simp [Chapter02WeightedCoefficientValue, hgl]
    have hprod : f.coeff k * g.coeff l ≠ 0 := mul_ne_zero hfk hgl
    have hfk_top : v (f.coeff k) ≠ (⊤ : WithTop Γ) :=
      (AddValuation.ne_top_iff v).2 hfk
    have hgl_top : v (g.coeff l) ≠ (⊤ : WithTop Γ) :=
      (AddValuation.ne_top_iff v).2 hgl
    have hprod_top : v (f.coeff k * g.coeff l) ≠ (⊤ : WithTop Γ) :=
      (AddValuation.ne_top_iff v).2 hprod
    have hsum := add_le_add (hG f k) (hG g l)
    have heq :
        W f k + W g l =
          Chapter02WeightedCoefficientValue v e α
            (f.coeff k * g.coeff l) (k + l) := by
      have hvsum :
          (v (f.coeff k * g.coeff l)).untop hprod_top =
            (v (f.coeff k)).untop hfk_top + (v (g.coeff l)).untop hgl_top := by
        apply WithTop.coe_injective
        simp only [WithTop.coe_untop, v.map_mul, WithTop.coe_add]
      apply WithTop.coe_injective
      simp only [W, Chapter02WeightedCoefficientValue, dif_neg hfk_top,
        dif_neg hgl_top, dif_neg hprod_top, WithTop.coe_add]
      rw [hvsum]
      simp [add_nsmul, add_assoc, add_left_comm, add_comm]
    exact heq ▸ hsum
  have hprod_weight (n : ℕ) (hn : (f * g).coeff n ≠ 0) :
      Chapter02GaussValuationFunction v e α f +
          Chapter02GaussValuationFunction v e α g ≤ W (f * g) n := by
    let s : Finset (ℕ × ℕ) :=
      Finset.HasAntidiagonal.antidiagonal (A := ℕ) n
    have hs : s.Nonempty := by
      refine ⟨(n, 0), ?_⟩
      simp [s]
    have hex : ∃ p ∈ s, f.coeff p.1 * g.coeff p.2 ≠ 0 := by
      by_contra h
      push Not at h
      apply hn
      rw [Polynomial.coeff_mul]
      apply Finset.sum_eq_zero
      intro r hr
      exact h r (by simpa [s] using hr)
    obtain ⟨p, hp, hp0⟩ := hex
    obtain ⟨q, hq, hqmin⟩ :=
      Finset.exists_min_image s
        (fun r => v (f.coeff r.1 * g.coeff r.2)) hs
    have hqtop : v (f.coeff q.1 * g.coeff q.2) ≠ (⊤ : WithTop Γ) :=
      ne_of_lt ((hqmin p hp).trans_lt
        (lt_top_iff_ne_top.mpr ((AddValuation.ne_top_iff v).2 hp0)))
    have hval :
        v (f.coeff q.1 * g.coeff q.2) ≤ v ((f * g).coeff n) := by
      rw [Polynomial.coeff_mul]
      exact v.map_le_sum (by
        intro r hr
        exact hqmin r (by simpa [s] using hr))
    have hval' :
        (v (f.coeff q.1 * g.coeff q.2)).untop hqtop ≤
          (v ((f * g).coeff n)).untop
            ((AddValuation.ne_top_iff v).2 hn) :=
      WithTop.coe_le_coe.mp (by
        simpa only [WithTop.coe_untop] using hval)
    have heval := (OrderHomClass.monotone e) hval'
    have hweighted :
        (e ((v (f.coeff q.1 * g.coeff q.2)).untop hqtop) +
            n • α : Λ) ≤
          e ((v ((f * g).coeff n)).untop
            ((AddValuation.ne_top_iff v).2 hn)) + n • α := by
      exact add_le_add_left heval (n • α)
    have hqsum : q.1 + q.2 = n := by simpa [s] using hq
    have hqterm := hterm q.1 q.2
    rw [hqsum] at hqterm
    have hqprod : f.coeff q.1 * g.coeff q.2 ≠ 0 :=
      (AddValuation.ne_top_iff v).1 hqtop
    have hqf : f.coeff q.1 ≠ 0 := by
      intro hqf
      exact hqprod (by simp [hqf])
    have hqg : g.coeff q.2 ≠ 0 := by
      intro hqg
      exact hqprod (by simp [hqg])
    have hqterm' :
        Chapter02GaussValuationFunction v e α f +
            Chapter02GaussValuationFunction v e α g ≤
          (e ((v (f.coeff q.1 * g.coeff q.2)).untop hqtop) +
            n • α : Λ) := by
      simpa [Chapter02WeightedCoefficientValue, hqf, hqg, hqtop] using hqterm
    have hWn : W (f * g) n =
        (e ((v ((f * g).coeff n)).untop
          ((AddValuation.ne_top_iff v).2 hn)) + n • α : Λ) := by
      simp only [W, Chapter02WeightedCoefficientValue,
        dif_neg ((AddValuation.ne_top_iff v).2 hn)]
    exact hqterm'.trans (by
      rw [hWn]
      exact WithTop.coe_le_coe.mpr hweighted)
  by_cases hf : f = 0
  · simp [hf, Chapter02GaussValuationFunction]
  by_cases hg : g = 0
  · simp [hg, Chapter02GaussValuationFunction]
  have hfS : f.support.Nonempty := Polynomial.support_nonempty.mpr hf
  have hgS : g.support.Nonempty := Polynomial.support_nonempty.mpr hg
  let Sf : Finset ℕ :=
    f.support.filter
      (fun i => W f i = Chapter02GaussValuationFunction v e α f)
  let Sg : Finset ℕ :=
    g.support.filter
      (fun i => W g i = Chapter02GaussValuationFunction v e α g)
  have hSf : Sf.Nonempty := by
    obtain ⟨i, hi, hi_eq⟩ :=
      Finset.exists_mem_eq_inf' (s := f.support) hfS
        (fun j => Chapter02WeightedCoefficientValue v e α (f.coeff j) j)
    refine ⟨i, ?_⟩
    exact Finset.mem_filter.mpr ⟨hi, by
      simpa only [W, Chapter02GaussValuationFunction, dif_pos hfS] using hi_eq.symm⟩
  have hSg : Sg.Nonempty := by
    obtain ⟨i, hi, hi_eq⟩ :=
      Finset.exists_mem_eq_inf' (s := g.support) hgS
        (fun j => Chapter02WeightedCoefficientValue v e α (g.coeff j) j)
    refine ⟨i, ?_⟩
    exact Finset.mem_filter.mpr ⟨hi, by
      simpa only [W, Chapter02GaussValuationFunction, dif_pos hgS] using hi_eq.symm⟩
  let i : ℕ := Sf.max' hSf
  let j : ℕ := Sg.max' hSg
  have hiS : i ∈ Sf := by
    exact Finset.max'_mem Sf hSf
  have hjS : j ∈ Sg := by
    exact Finset.max'_mem Sg hSg
  have hiF : i ∈ f.support := (Finset.mem_filter.mp hiS).1
  have hjG : j ∈ g.support := (Finset.mem_filter.mp hjS).1
  have hi_eq :
      W f i = Chapter02GaussValuationFunction v e α f :=
    (Finset.mem_filter.mp hiS).2
  have hj_eq :
      W g j = Chapter02GaussValuationFunction v e α g :=
    (Finset.mem_filter.mp hjS).2
  have hmaxF {k : ℕ} (hk : k ∈ Sf) : k ≤ i :=
    Finset.le_max' Sf k hk
  have hmaxG {l : ℕ} (hl : l ∈ Sg) : l ≤ j :=
    Finset.le_max' Sg l hl
  have hstrictF {k : ℕ} (hk : k ∈ f.support) (hik : i < k) :
      W f i < W f k := by
    have hle : W f i ≤ W f k := by
      rw [hi_eq]
      exact hG f k
    apply lt_of_le_of_ne hle
    intro heq
    have hkS : k ∈ Sf := Finset.mem_filter.mpr ⟨hk, heq.symm.trans hi_eq⟩
    exact (not_le_of_gt hik) (hmaxF hkS)
  have hstrictG {l : ℕ} (hl : l ∈ g.support) (hjl : j < l) :
      W g j < W g l := by
    have hle : W g j ≤ W g l := by
      rw [hj_eq]
      exact hG g l
    apply lt_of_le_of_ne hle
    intro heq
    have hlS : l ∈ Sg := Finset.mem_filter.mpr ⟨hl, heq.symm.trans hj_eq⟩
    exact (not_le_of_gt hjl) (hmaxG hlS)
  have hpair_lt {k l : ℕ} (hk : k ∈ f.support) (hl : l ∈ g.support)
      (hkl : k + l = i + j) (hne : (k, l) ≠ (i, j)) :
      v (f.coeff i * g.coeff j) < v (f.coeff k * g.coeff l) := by
    have hif : f.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hiF
    have hjg : g.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hjG
    have hklf : f.coeff k ≠ 0 := Polynomial.mem_support_iff.mp hk
    have hklg : g.coeff l ≠ 0 := Polynomial.mem_support_iff.mp hl
    have hsel : v (f.coeff i * g.coeff j) ≠ (⊤ : WithTop Γ) :=
      (AddValuation.ne_top_iff v).2 (mul_ne_zero hif hjg)
    by_contra hnot
    have hval : v (f.coeff k * g.coeff l) ≤
        v (f.coeff i * g.coeff j) := le_of_not_gt hnot
    have hval' :
        (v (f.coeff k * g.coeff l)).untop
            ((AddValuation.ne_top_iff v).2 (mul_ne_zero hklf hklg)) ≤
          (v (f.coeff i * g.coeff j)).untop hsel :=
      WithTop.coe_le_coe.mp (by
        simpa only [WithTop.coe_untop] using hval)
    have hsumW :
        W f k + W g l ≤ W f i + W g j := by
      have htotal :
          e ((v (f.coeff k * g.coeff l)).untop
              ((AddValuation.ne_top_iff v).2 (mul_ne_zero hklf hklg))) +
              (k + l) • α ≤
            e ((v (f.coeff i * g.coeff j)).untop hsel) +
              (i + j) • α := by
        have := add_le_add_left ((OrderHomClass.monotone e) hval') ((k + l) • α)
        simpa only [hkl] using this
      have hvkl :
          (v (f.coeff k * g.coeff l)).untop
              ((AddValuation.ne_top_iff v).2 (mul_ne_zero hklf hklg)) =
            (v (f.coeff k)).untop
                ((AddValuation.ne_top_iff v).2 hklf) +
              (v (g.coeff l)).untop
                ((AddValuation.ne_top_iff v).2 hklg) := by
        apply WithTop.coe_injective
        simp only [WithTop.coe_untop, v.map_mul, WithTop.coe_add]
      have hvij :
          (v (f.coeff i * g.coeff j)).untop hsel =
            (v (f.coeff i)).untop
                ((AddValuation.ne_top_iff v).2 hif) +
              (v (g.coeff j)).untop
                ((AddValuation.ne_top_iff v).2 hjg) := by
        apply WithTop.coe_injective
        simp only [WithTop.coe_untop, v.map_mul, WithTop.coe_add]
      have htotal' :
          (e ((v (f.coeff k * g.coeff l)).untop
              ((AddValuation.ne_top_iff v).2 (mul_ne_zero hklf hklg))) +
            (k + l) • α : WithTop Λ) ≤
          (e ((v (f.coeff i * g.coeff j)).untop hsel) +
            (i + j) • α : WithTop Λ) :=
        WithTop.coe_le_coe.mpr htotal
      have hWfkval : W f k =
          (e ((v (f.coeff k)).untop
            ((AddValuation.ne_top_iff v).2 hklf)) + k • α : Λ) := by
        simp only [W, Chapter02WeightedCoefficientValue,
          dif_neg ((AddValuation.ne_top_iff v).2 hklf)]
      have hWglval : W g l =
          (e ((v (g.coeff l)).untop
            ((AddValuation.ne_top_iff v).2 hklg)) + l • α : Λ) := by
        simp only [W, Chapter02WeightedCoefficientValue,
          dif_neg ((AddValuation.ne_top_iff v).2 hklg)]
      have hWfival : W f i =
          (e ((v (f.coeff i)).untop
            ((AddValuation.ne_top_iff v).2 hif)) + i • α : Λ) := by
        simp only [W, Chapter02WeightedCoefficientValue,
          dif_neg ((AddValuation.ne_top_iff v).2 hif)]
      have hWgjval : W g j =
          (e ((v (g.coeff j)).untop
            ((AddValuation.ne_top_iff v).2 hjg)) + j • α : Λ) := by
        simp only [W, Chapter02WeightedCoefficientValue,
          dif_neg ((AddValuation.ne_top_iff v).2 hjg)]
      calc
        W f k + W g l =
            ((e ((v (f.coeff k)).untop
                ((AddValuation.ne_top_iff v).2 hklf)) + k • α : Λ) :
              WithTop Λ) +
              ((e ((v (g.coeff l)).untop
                ((AddValuation.ne_top_iff v).2 hklg)) + l • α : Λ) :
                WithTop Λ) := by rw [hWfkval, hWglval]
        _ = (e ((v (f.coeff k * g.coeff l)).untop
              ((AddValuation.ne_top_iff v).2 (mul_ne_zero hklf hklg))) +
            (k + l) • α : Λ) := by
          rw [← WithTop.coe_add]
          apply WithTop.coe_injective
          rw [hvkl, map_add]
          simp only [add_nsmul]
          abel_nf
        _ ≤ (e ((v (f.coeff i * g.coeff j)).untop hsel) +
            (i + j) • α : Λ) := htotal'
        _ = W f i + W g j := by
          rw [hWfival, hWgjval]
          rw [← WithTop.coe_add]
          apply WithTop.coe_injective
          rw [hvij, map_add]
          simp only [add_nsmul]
          abel_nf
    have hsumW' : W f i + W g j ≤ W f k + W g l := by
      exact add_le_add
        (by rw [hi_eq]; exact hG f k)
        (by rw [hj_eq]; exact hG g l)
    have hsumEq : W f k + W g l = W f i + W g j :=
      le_antisymm hsumW hsumW'
    have hWgl : W g j ≠ (⊤ : WithTop Λ) := by
      simp only [W, Chapter02WeightedCoefficientValue,
        dif_neg ((AddValuation.ne_top_iff v).2 (Polynomial.mem_support_iff.mp hjG))]
      exact WithTop.coe_ne_top
    have hWfi : W f i ≠ (⊤ : WithTop Λ) := by
      simp only [W, Chapter02WeightedCoefficientValue,
        dif_neg ((AddValuation.ne_top_iff v).2 (Polynomial.mem_support_iff.mp hiF))]
      exact WithTop.coe_ne_top
    have hfkEq : W f k = W f i := by
      have hgjle : W g j ≤ W g l := by
        rw [hj_eq]
        exact hG g l
      apply le_antisymm
      · apply (add_le_add_iff_left_of_ne_top hWgl).mp
        calc
          W f k + W g j ≤ W f k + W g l := by
            simpa [add_comm] using (add_le_add_left hgjle (W f k))
          _ = W f i + W g j := hsumEq
      · exact le_of_not_gt (by
          intro h
          exact (not_le_of_gt h)
            (by rw [hi_eq]; exact hG f k))
    have hglEq : W g l = W g j := by
      have hfkle : W f i ≤ W f k := by
        rw [hi_eq]
        exact hG f k
      apply le_antisymm
      · apply (add_le_add_iff_right_of_ne_top hWfi).mp
        calc
          W f i + W g l ≤ W f k + W g l := by
            simpa [add_comm] using (add_le_add_right hfkle (W g l))
          _ = W f i + W g j := hsumEq
      · exact le_of_not_gt (by
          intro h
          exact (not_le_of_gt h)
            (by rw [hj_eq]; exact hG g l))
    have hkS : k ∈ Sf := Finset.mem_filter.mpr ⟨hk, hfkEq.trans hi_eq⟩
    have hlS : l ∈ Sg := Finset.mem_filter.mpr ⟨hl, hglEq.trans hj_eq⟩
    have hk_le : k ≤ i := hmaxF hkS
    have hl_le : l ≤ j := hmaxG hlS
    have : k = i ∧ l = j := by omega
    exact hne (by exact Prod.ext this.1 this.2)
  have hsum_coeff :
      v ((f * g).coeff (i + j)) = v (f.coeff i * g.coeff j) := by
    rw [Polynomial.coeff_mul]
    exact chapter02_strictly_smallest_term_controls_finite_sum v
      (Finset.HasAntidiagonal.antidiagonal (A := ℕ) (i + j))
      (fun p : ℕ × ℕ => f.coeff p.1 * g.coeff p.2) (i, j) (by simp)
      (by
        intro p hp hne
        have hsel_ne : v (f.coeff i * g.coeff j) ≠ (⊤ : WithTop Γ) :=
          (AddValuation.ne_top_iff v).2
            (mul_ne_zero (Polynomial.mem_support_iff.mp hiF)
              (Polynomial.mem_support_iff.mp hjG))
        by_cases hpf : p.1 ∈ f.support
        · by_cases hpg : p.2 ∈ g.support
          · exact hpair_lt hpf hpg (by simpa using hp) hne
          · have hpzero : g.coeff p.2 = 0 :=
              Polynomial.notMem_support_iff.mp hpg
            simpa [hpzero] using (lt_top_iff_ne_top.mpr hsel_ne)
        · have hpzero : f.coeff p.1 = 0 :=
            Polynomial.notMem_support_iff.mp hpf
          simpa [hpzero] using (lt_top_iff_ne_top.mpr hsel_ne))
  have hsel_coeff : (f * g).coeff (i + j) ≠ 0 := by
    have hterm_ne : v (f.coeff i * g.coeff j) ≠ (⊤ : WithTop Γ) :=
      (AddValuation.ne_top_iff v).2
        (mul_ne_zero (Polynomial.mem_support_iff.mp hiF)
          (Polynomial.mem_support_iff.mp hjG))
    intro hzero
    apply hterm_ne
    calc
      v (f.coeff i * g.coeff j) = v ((f * g).coeff (i + j)) := hsum_coeff.symm
      _ = ⊤ := by simp [hzero]
  have hprodS : (f * g).support.Nonempty :=
    Polynomial.support_nonempty.mpr (by
      intro hzero
      exact hsel_coeff (by simp [hzero]))
  have hlower : Chapter02GaussValuationFunction v e α f +
      Chapter02GaussValuationFunction v e α g ≤
        Chapter02GaussValuationFunction v e α (f * g) := by
    simp only [Chapter02GaussValuationFunction, dif_pos hfS, dif_pos hgS, dif_pos hprodS]
    rw [Finset.le_inf'_iff]
    intro n hn
    simpa only [W, Chapter02GaussValuationFunction,
      dif_pos hfS, dif_pos hgS, dif_pos hprodS] using
      hprod_weight n (Polynomial.mem_support_iff.mp hn)
  have hselected :
      W (f * g) (i + j) =
        Chapter02GaussValuationFunction v e α f +
          Chapter02GaussValuationFunction v e α g := by
    have heq :
        W f i + W g j = W (f * g) (i + j) := by
      have hif : f.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hiF
      have hjg : g.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hjG
      have hpij : f.coeff i * g.coeff j ≠ 0 := mul_ne_zero hif hjg
      have hvi : v (f.coeff i) ≠ (⊤ : WithTop Γ) :=
        (AddValuation.ne_top_iff v).2 hif
      have hvj : v (g.coeff j) ≠ (⊤ : WithTop Γ) :=
        (AddValuation.ne_top_iff v).2 hjg
      have hvp : v (f.coeff i * g.coeff j) ≠ (⊤ : WithTop Γ) :=
        (AddValuation.ne_top_iff v).2 hpij
      have hvij :
          (v (f.coeff i * g.coeff j)).untop hvp =
            (v (f.coeff i)).untop hvi + (v (g.coeff j)).untop hvj := by
        apply WithTop.coe_injective
        simp only [WithTop.coe_untop, v.map_mul, WithTop.coe_add]
      have hWfi : W f i =
          (e ((v (f.coeff i)).untop hvi) + i • α : Λ) := by
        simp only [W, Chapter02WeightedCoefficientValue, dif_neg hvi]
      have hWgj : W g j =
          (e ((v (g.coeff j)).untop hvj) + j • α : Λ) := by
        simp only [W, Chapter02WeightedCoefficientValue, dif_neg hvj]
      have hWprod : W (f * g) (i + j) =
          (e ((v ((f * g).coeff (i + j))).untop
            ((AddValuation.ne_top_iff v).2 hsel_coeff)) +
            (i + j) • α : Λ) := by
        simp only [W, Chapter02WeightedCoefficientValue,
          dif_neg ((AddValuation.ne_top_iff v).2 hsel_coeff)]
      have huv :
          (v ((f * g).coeff (i + j))).untop
              ((AddValuation.ne_top_iff v).2 hsel_coeff) =
            (v (f.coeff i * g.coeff j)).untop hvp := by
        apply WithTop.coe_injective
        simpa only [WithTop.coe_untop] using hsum_coeff
      calc
        W f i + W g j =
            ((e ((v (f.coeff i)).untop hvi) + i • α : Λ) : WithTop Λ) +
              ((e ((v (g.coeff j)).untop hvj) + j • α : Λ) : WithTop Λ) := by
          rw [hWfi, hWgj]
        _ = (e ((v (f.coeff i * g.coeff j)).untop hvp) +
            (i + j) • α : Λ) := by
          rw [← WithTop.coe_add]
          apply WithTop.coe_injective
          rw [hvij, map_add]
          simp only [add_nsmul]
          abel_nf
        _ = W (f * g) (i + j) := by
          rw [hWprod]
          apply WithTop.coe_injective
          rw [huv]
    calc
      W (f * g) (i + j) = W f i + W g j := heq.symm
      _ = Chapter02GaussValuationFunction v e α f +
          Chapter02GaussValuationFunction v e α g := by
        rw [hi_eq, hj_eq]
  have hupper : Chapter02GaussValuationFunction v e α (f * g) ≤
      Chapter02GaussValuationFunction v e α f +
        Chapter02GaussValuationFunction v e α g := by
    simp only [Chapter02GaussValuationFunction, dif_pos hprodS]
    exact (Finset.inf'_le _ (by
      exact Polynomial.mem_support_iff.mpr hsel_coeff)).trans_eq hselected
  exact le_antisymm hupper hlower

noncomputable def Chapter02GaussValuationOnRationalFunctions
    {K Γ Λ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (v : AddValuation K (WithTop Γ)) (e : Γ →+o Λ) (α : Λ) :
    RatFunc K → WithTop Λ := by
  classical
  exact fun x => if hx : x = 0 then ⊤ else
    Chapter02GaussValuationFunction v e α x.num -
      Chapter02GaussValuationFunction v e α x.denom

theorem chapter02_gauss_valuation_on_quotients
    {K Γ Λ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (v : AddValuation K (WithTop Γ)) (e : Γ →+o Λ) (α : Λ)
    (f g : Polynomial K) (hg : g ≠ 0) :
    Chapter02GaussValuationOnRationalFunctions v e α
        (algebraMap (Polynomial K) (RatFunc K) f /
          algebraMap (Polynomial K) (RatFunc K) g) =
      Chapter02GaussValuationFunction v e α f -
        Chapter02GaussValuationFunction v e α g := by
  classical
  let G : Polynomial K → WithTop Λ :=
    Chapter02GaussValuationFunction v e α
  have hcancel (a b c : WithTop Λ) (ha : a ≠ ⊤) :
      a + b - (a + c) = b - c := by
    obtain rfl | hb := eq_or_ne b ⊤
    · simp
    obtain rfl | hc := eq_or_ne c ⊤
    · simp
    cases a with
    | top => exact (ha rfl).elim
    | coe a =>
      cases b with
      | top => exact (hb rfl).elim
      | coe b =>
        cases c with
        | top => exact (hc rfl).elim
        | coe c =>
          change ((a + b - (a + c) : Λ) : WithTop Λ) =
            ((b - c : Λ) : WithTop Λ)
          exact congrArg (fun z : Λ => (z : WithTop Λ))
            (show a + b - (a + c) = b - c by abel_nf)
  have hG_ne_top {p : Polynomial K} (hp : p ≠ 0) : G p ≠ ⊤ := by
    have hs : p.support.Nonempty := Polynomial.support_nonempty.mpr hp
    obtain ⟨i, hi⟩ := hs
    have hpi : p.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
    have hWi :
        Chapter02WeightedCoefficientValue v e α (p.coeff i) i ≠
          (⊤ : WithTop Λ) := by
      simp only [Chapter02WeightedCoefficientValue,
        dif_neg ((AddValuation.ne_top_iff v).2 hpi)]
      exact WithTop.coe_ne_top
    have hle : G p ≤
        Chapter02WeightedCoefficientValue v e α (p.coeff i) i := by
      simp only [G, Chapter02GaussValuationFunction, dif_pos
        (Polynomial.support_nonempty.mpr hp)]
      exact Finset.inf'_le _ hi
    exact ne_of_lt (hle.trans_lt (lt_top_iff_ne_top.mpr hWi))
  by_cases hf0 : f = 0
  · subst f
    simp [Chapter02GaussValuationOnRationalFunctions,
      Chapter02GaussValuationFunction, hg]
  let x : RatFunc K :=
    algebraMap (Polynomial K) (RatFunc K) f /
      algebraMap (Polynomial K) (RatFunc K) g
  have hx : x ≠ 0 := by
    dsimp [x]
    exact div_ne_zero (RatFunc.algebraMap_ne_zero hf0)
      (RatFunc.algebraMap_ne_zero hg)
  let d : Polynomial K := gcd f g
  let f' : Polynomial K := f / d
  let g' : Polynomial K := g / d
  let c : Polynomial K := Polynomial.C (g'.leadingCoeff⁻¹)
  have hd0 : d ≠ 0 := by
    intro hd
    apply hg
    have hzero := (gcd_eq_zero_iff f g).mp (by simpa [d] using hd)
    exact hzero.2
  have hfd : d * f' = f := by
    dsimp [f', d]
    exact EuclideanDomain.mul_div_cancel' hd0
      (gcd_dvd_left f g)
  have hgd : d * g' = g := by
    dsimp [g', d]
    exact EuclideanDomain.mul_div_cancel' hd0
      (gcd_dvd_right f g)
  have hf'0 : f' ≠ 0 := by
    intro hf'
    apply hf0
    calc
      f = d * f' := hfd.symm
      _ = 0 := by simp [hf']
  have hg'0 : g' ≠ 0 := by
    intro hg'
    apply hg
    calc
      g = d * g' := hgd.symm
      _ = 0 := by simp [hg']
  have hc0 : c ≠ 0 := by
    dsimp [c]
    exact C_ne_zero.mpr (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hg'0))
  have hGc : G c ≠ ⊤ := hG_ne_top hc0
  have hGd : G d ≠ ⊤ := hG_ne_top hd0
  have hmul (p q : Polynomial K) :
      G (p * q) = G p + G q := by
    change Chapter02GaussValuationFunction v e α (p * q) =
      Chapter02GaussValuationFunction v e α p +
        Chapter02GaussValuationFunction v e α q
    exact chapter02_gauss_valuation_is_multiplicative v e α p q
  have hcf : G (c * f') = G c + G f' := by
    exact hmul c f'
  have hcg : G (c * g') = G c + G g' := by
    exact hmul c g'
  have hdf : G f = G d + G f' := by
    simpa only [hfd] using hmul d f'
  have hdg : G g = G d + G g' := by
    simpa only [hgd] using hmul d g'
  change (if h : x = 0 then ⊤ else G x.num - G x.denom) = G f - G g
  rw [dif_neg hx]
  dsimp [x]
  rw [RatFunc.num_div, RatFunc.denom_div _ hg]
  have hmain : G (c * f') - G (c * g') = G f - G g := by
    calc
      G (c * f') - G (c * g') =
          (G c + G f') - (G c + G g') := by rw [hcf, hcg]
      _ = G f' - G g' := hcancel (G c) (G f') (G g') hGc
      _ = (G d + G f') - (G d + G g') :=
        (hcancel (G d) (G f') (G g') hGd).symm
      _ = G f - G g := by rw [hdf, hdg]
  have hnum :
      Polynomial.C (g / gcd f g).leadingCoeff⁻¹ *
          (f / gcd f g) = c * f' := by
    rfl
  have hden :
      Polynomial.C (g / gcd f g).leadingCoeff⁻¹ *
          (g / gcd f g) = c * g' := by
    rfl
  rw [hnum, hden]
  exact hmain

theorem chapter02_gauss_at_zero_is_coefficient_minimum
    {K Γ Λ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (v : AddValuation K (WithTop Γ)) (e : Γ →+o Λ) (f : Polynomial K) :
    Chapter02GaussValuationFunction v e 0 f =
      if hf : f.support.Nonempty then
        f.support.inf' hf (fun i =>
          if ha : v (f.coeff i) = ⊤ then ⊤
          else (e ((v (f.coeff i)).untop ha) : WithTop Λ))
        else ⊤ := by
  simp [Chapter02GaussValuationFunction, Chapter02WeightedCoefficientValue]

theorem chapter02_gauss_variable_has_prescribed_value
    {K Γ Λ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (v : AddValuation K (WithTop Γ)) (e : Γ →+o Λ) (α : Λ) :
    Chapter02GaussValuationFunction v e α Polynomial.X = (α : WithTop Λ) := by
  simp [Chapter02GaussValuationFunction, Chapter02WeightedCoefficientValue]

theorem chapter02_gauss_positive_parameter_makes_the_variable_small
    {K Γ Λ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (v : AddValuation K (WithTop Γ)) (e : Γ →+o Λ) {α : Λ} (hα : 0 < α) :
    0 < Chapter02GaussValuationFunction v e α Polynomial.X := by
  rw [chapter02_gauss_variable_has_prescribed_value]
  exact WithTop.coe_pos.mpr hα

def Chapter02GaussMinimalIndices
    {K Γ Λ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (v : AddValuation K (WithTop Γ)) (e : Γ →+o Λ) (α : Λ)
    (f : Polynomial K) : Set ℕ :=
  {i | i ∈ f.support ∧
    Chapter02WeightedCoefficientValue v e α (f.coeff i) i =
      Chapter02GaussValuationFunction v e α f}

theorem chapter02_gauss_minimum_is_attained
    {K Γ Λ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (v : AddValuation K (WithTop Γ)) (e : Γ →+o Λ) (α : Λ)
    {f : Polynomial K} (hf : f ≠ 0) :
    (Chapter02GaussMinimalIndices v e α f).Nonempty := by
  classical
  have hsupport : f.support.Nonempty := Polynomial.support_nonempty.mpr hf
  obtain ⟨i, hi, hi_eq⟩ :=
    Finset.exists_mem_eq_inf' (s := f.support) hsupport
      (fun j => Chapter02WeightedCoefficientValue v e α (f.coeff j) j)
  refine ⟨i, ?_⟩
  exact ⟨hi, by
    simpa [Chapter02GaussValuationFunction, hf] using hi_eq.symm⟩

abbrev Chapter02ValuationSubring
    {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ]
    (v : AddValuation K (WithTop Γ)) : Subring K :=
  (AddValuation.toValuation v).integer

def Chapter02ValuationMaximalIdeal
    {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ]
    (v : AddValuation K (WithTop Γ)) :
    Ideal (Chapter02ValuationSubring v) :=
  IsLocalRing.maximalIdeal (Chapter02ValuationSubring v)

abbrev Chapter02ResidueField
    {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ]
    (v : AddValuation K (WithTop Γ)) :=
  (Chapter02ValuationSubring v) ⧸ Chapter02ValuationMaximalIdeal v

noncomputable def Chapter02ResidueOfIntegral
    {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ]
    (v : AddValuation K (WithTop Γ)) (x : K) (hx : 0 ≤ v x) :
    Chapter02ResidueField v :=
  Ideal.Quotient.mk _ ⟨x, hx⟩

theorem chapter02_withTop_sub_nonneg_of_le
    {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    {a b : WithTop Γ} (ha : a ≠ ⊤) (hb : b ≠ ⊤) (h : b ≤ a) :
    0 ≤ a - b := by
  have h' : b.untop hb ≤ a.untop ha :=
    WithTop.coe_le_coe.mp (by
      simpa only [WithTop.coe_untop] using h)
  have hco : ((0 : Γ) : WithTop Γ) ≤
      ((a.untop ha - b.untop hb : Γ) : WithTop Γ) :=
    WithTop.coe_le_coe.mpr (sub_nonneg.mpr h')
  rw [← WithTop.coe_untop a ha, ← WithTop.coe_untop b hb]
  change ((0 : Γ) : WithTop Γ) ≤
    ((a.untop ha - b.untop hb : Γ) : WithTop Γ)
  exact hco

theorem chapter02_gauss_residue_remembers_scaled_polynomial
    {K Γ Λ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (v : AddValuation K (WithTop Γ)) (e : Γ →+o Λ)
    {f : Polynomial K} (hf : f ≠ 0) :
    ∃ i : ℕ, ∃ hi : i ∈ f.support,
      ∃ hmin : ∀ j : ℕ, j ∈ f.support →
        v (f.coeff i) ≤ v (f.coeff j),
      Chapter02WeightedCoefficientValue v e 0 (f.coeff i) i =
        Chapter02GaussValuationFunction v e 0 f ∧
      ∃ g : Polynomial (Chapter02ResidueField v),
        g.coeff i = 1 ∧
        g.support ⊆ f.support ∧
        ∀ j : ℕ, (hj : j ∈ f.support) →
          g.coeff j = Chapter02ResidueOfIntegral v
            ((f.coeff j) / (f.coeff i)) (by
              by_cases hzero : f.coeff j = 0
              · simp [hzero]
              have hij : v (f.coeff i) ≤ v (f.coeff j) :=
                hmin j hj
              rw [v.map_div]
              exact chapter02_withTop_sub_nonneg_of_le
                ((AddValuation.ne_top_iff v).2 (Polynomial.mem_support_iff.mp hj))
                ((AddValuation.ne_top_iff v).2
                  (Polynomial.mem_support_iff.mp hi)) hij) := by
  classical
  have hsupport : f.support.Nonempty := Polynomial.support_nonempty.mpr hf
  obtain ⟨i, hi, hmin⟩ :=
    Finset.exists_min_image f.support (fun j => v (f.coeff j)) hsupport
  have hfi : f.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
  have hweight (j : ℕ) (hj : j ∈ f.support) :
      Chapter02WeightedCoefficientValue v e 0 (f.coeff i) i ≤
        Chapter02WeightedCoefficientValue v e 0 (f.coeff j) j := by
    have hfj : f.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
    have hvi : v (f.coeff i) ≠ (⊤ : WithTop Γ) :=
      (AddValuation.ne_top_iff v).2 hfi
    have hvj : v (f.coeff j) ≠ (⊤ : WithTop Γ) :=
      (AddValuation.ne_top_iff v).2 hfj
    simp only [Chapter02WeightedCoefficientValue, dif_neg hvi, dif_neg hvj,
      nsmul_zero, add_zero]
    have hmin' :
        (v (f.coeff i)).untop
            ((AddValuation.ne_top_iff v).2 hfi) ≤
          (v (f.coeff j)).untop
            ((AddValuation.ne_top_iff v).2 hfj) :=
      WithTop.coe_le_coe.mp (by
        simpa only [WithTop.coe_untop] using hmin j hj)
    exact WithTop.coe_le_coe.mpr
      ((OrderHomClass.monotone e) hmin')
  have hGauss :
      Chapter02WeightedCoefficientValue v e 0 (f.coeff i) i =
        Chapter02GaussValuationFunction v e 0 f := by
    apply le_antisymm
    · simp only [Chapter02GaussValuationFunction, dif_pos hsupport]
      rw [Finset.le_inf'_iff]
      intro j hj
      exact hweight j hj
    · simp only [Chapter02GaussValuationFunction, dif_pos hsupport]
      exact Finset.inf'_le _ hi
  have hint (j : ℕ) (hj : j ∈ f.support) :
      0 ≤ v ((f.coeff j) / (f.coeff i)) := by
    have hfj : f.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
    rw [v.map_div]
    exact chapter02_withTop_sub_nonneg_of_le
      ((AddValuation.ne_top_iff v).2 hfj)
      ((AddValuation.ne_top_iff v).2 hfi) (hmin j hj)
  let r : ℕ → Chapter02ResidueField v := fun j =>
    if hj : j ∈ f.support then
      Chapter02ResidueOfIntegral v ((f.coeff j) / (f.coeff i)) (hint j hj)
    else 0
  have hr : ∀ j : ℕ, r j ≠ 0 → j ∈ f.support := by
    intro j hj
    by_cases hmem : j ∈ f.support
    · exact hmem
    · have hrzero : r j = 0 := by
        dsimp [r]
        rw [dif_neg hmem]
      exact (hj hrzero).elim
  let F : ℕ →₀ Chapter02ResidueField v :=
    Finsupp.onFinset f.support r hr
  let g : Polynomial (Chapter02ResidueField v) := Polynomial.ofFinsupp ⟨F⟩
  have hgcoeff (j : ℕ) : g.coeff j = r j := by
    simp [g, F]
  have hgsup : g.support ⊆ f.support := by
    intro j hj
    rw [Polynomial.support_ofFinsupp] at hj
    exact (Finsupp.support_onFinset_subset (s := f.support) (f := r)
      (hf := hr)) hj
  have hri : r i = 1 := by
    simp only [r, dif_pos hi]
    have hunit : Chapter02ResidueOfIntegral v (1 : K) (by simp) =
        (1 : Chapter02ResidueField v) := by
      change Ideal.Quotient.mk _ ⟨(1 : K), _⟩ = (1 : Chapter02ResidueField v)
      have hone : (⟨(1 : K), (by simp : 0 ≤ v (1 : K))⟩ :
          Chapter02ValuationSubring v) = 1 := by
        ext
        simp
      rw [hone]
      exact map_one _
    simpa only [div_self hfi] using hunit
  refine ⟨i, hi, hmin, hGauss, g, ?_, hgsup, ?_⟩
  · rw [hgcoeff, hri]
  · intro j hj
    rw [hgcoeff]
    have hfj : f.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
    simp [r, hfj]

theorem chapter02_gauss_residue_construction_requires_a_unit_coefficient
    {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ]
    (v : AddValuation K (WithTop Γ)) {a : K} (ha : a ≠ 0) :
    ∃ s : K, s ≠ 0 ∧ v (s * a) = 0 ∧ v s + v a = 0 := by
  refine ⟨a⁻¹, inv_ne_zero ha, ?_, ?_⟩
  · simp [ha]
  · rw [v.map_inv]
    exact LinearOrderedAddCommGroupWithTop.neg_add_cancel_of_ne_top
      ((AddValuation.ne_top_iff v).2 ha)

/-! ### Two-stage valuation on Laurent series -/

abbrev Chapter02TwoStageValueGroup (Γ : Type*) := ℤ ×ₗ Γ

def Chapter02TwoStageLaurentValuation
    {K Γ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Nontrivial Γ]
    (v : AddValuation K (WithTop Γ)) :
    LaurentSeries K → WithTop (Chapter02TwoStageValueGroup Γ) := by
  classical
  exact fun f => if hf : f = 0 then ⊤ else
    ((toLex
      (f.order, (v f.leadingCoeff).untop (by
        exact (AddValuation.ne_top_iff v).2
          (HahnSeries.leadingCoeff_ne_zero.mpr hf))) :
      Chapter02TwoStageValueGroup Γ) :
      WithTop (Chapter02TwoStageValueGroup Γ))

theorem chapter02_two_stage_value_of_zero
    {K Γ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Nontrivial Γ] (v : AddValuation K (WithTop Γ)) :
    Chapter02TwoStageLaurentValuation v 0 = ⊤ := by
  simp [Chapter02TwoStageLaurentValuation]

theorem chapter02_two_stage_value_of_one
    {K Γ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Nontrivial Γ] (v : AddValuation K (WithTop Γ)) :
    Chapter02TwoStageLaurentValuation v 1 =
      (0 : WithTop (Chapter02TwoStageValueGroup Γ)) := by
  simp [Chapter02TwoStageLaurentValuation]

theorem chapter02_two_stage_value_is_multiplicative
    {K Γ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Nontrivial Γ] (v : AddValuation K (WithTop Γ))
    (f g : LaurentSeries K) :
    Chapter02TwoStageLaurentValuation v (f * g) =
      Chapter02TwoStageLaurentValuation v f +
        Chapter02TwoStageLaurentValuation v g := by
  by_cases hf : f = 0
  · subst f
    simp [Chapter02TwoStageLaurentValuation]
  by_cases hg : g = 0
  · subst g
    simp [Chapter02TwoStageLaurentValuation]
  have hfg : f * g ≠ 0 := mul_ne_zero hf hg
  have hflead : f.leadingCoeff ≠ 0 :=
    HahnSeries.leadingCoeff_ne_zero.mpr hf
  have hglead : g.leadingCoeff ≠ 0 :=
    HahnSeries.leadingCoeff_ne_zero.mpr hg
  have hvf : v f.leadingCoeff ≠ (⊤ : WithTop Γ) :=
    (AddValuation.ne_top_iff v).2 hflead
  have hvg : v g.leadingCoeff ≠ (⊤ : WithTop Γ) :=
    (AddValuation.ne_top_iff v).2 hglead
  have hvfg : v f.leadingCoeff + v g.leadingCoeff ≠ (⊤ : WithTop Γ) := by
    rw [← v.map_mul]
    exact (AddValuation.ne_top_iff v).2 (mul_ne_zero hflead hglead)
  have hlead : (f * g).leadingCoeff = f.leadingCoeff * g.leadingCoeff :=
    HahnSeries.leadingCoeff_mul_of_ne_zero
      (mul_ne_zero hflead hglead)
  simp only [Chapter02TwoStageLaurentValuation, dif_neg hf, dif_neg hg,
    dif_neg hfg, HahnSeries.order_mul hf hg, hlead, v.map_mul]
  rw [← WithTop.coe_add]
  have hlex :
      (toLex (order f + order g,
        (v f.leadingCoeff + v g.leadingCoeff).untop hvfg) :
        Chapter02TwoStageValueGroup Γ) =
        toLex (order f, (v f.leadingCoeff).untop hvf) +
          toLex (order g, (v g.leadingCoeff).untop hvg) := by
    change toLex (order f + order g,
        (v f.leadingCoeff + v g.leadingCoeff).untop hvfg) =
      toLex ((order f, (v f.leadingCoeff).untop hvf) +
        (order g, (v g.leadingCoeff).untop hvg))
    apply toLex_inj.mp
    apply Prod.ext
    · rfl
    · apply WithTop.coe_injective
      change
        (↑((v f.leadingCoeff + v g.leadingCoeff).untop hvfg) : WithTop Γ) =
          ↑((v f.leadingCoeff).untop hvf + (v g.leadingCoeff).untop hvg)
      simp only [WithTop.coe_untop, WithTop.coe_add]
  exact congrArg (fun x : Chapter02TwoStageValueGroup Γ =>
    (x : WithTop (Chapter02TwoStageValueGroup Γ))) hlex

theorem chapter02_two_stage_value_satisfies_sum_inequality
    {K Γ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Nontrivial Γ] (v : AddValuation K (WithTop Γ))
    (f g : LaurentSeries K) :
    min (Chapter02TwoStageLaurentValuation v f)
        (Chapter02TwoStageLaurentValuation v g) ≤
      Chapter02TwoStageLaurentValuation v (f + g) := by
  by_cases hf : f = 0
  · subst f
    rw [zero_add]
    simp [Chapter02TwoStageLaurentValuation]
  by_cases hg : g = 0
  · subst g
    rw [add_zero]
    simp [Chapter02TwoStageLaurentValuation]
  by_cases hfg : f + g = 0
  · simp [hfg, Chapter02TwoStageLaurentValuation]
  have hfo : f.orderTop = (f.order : WithTop ℤ) :=
    (HahnSeries.order_eq_orderTop_of_ne_zero hf).symm
  have hgo : g.orderTop = (g.order : WithTop ℤ) :=
    (HahnSeries.order_eq_orderTop_of_ne_zero hg).symm
  have hsumorder : min f.orderTop g.orderTop ≤ (f + g).orderTop :=
    HahnSeries.min_orderTop_le_orderTop_add
  have hvalue_le_of_order_lt {p q : LaurentSeries K} (hp : p ≠ 0)
      (hq : q ≠ 0) (hpq : p.order < q.order) :
      Chapter02TwoStageLaurentValuation v p ≤
        Chapter02TwoStageLaurentValuation v q := by
    simp only [Chapter02TwoStageLaurentValuation, dif_neg hp, dif_neg hq]
    exact WithTop.coe_le_coe.mpr
      (Prod.Lex.toLex_le_toLex.mpr (Or.inl hpq))
  have hvalue_le_of_order_eq {p q : LaurentSeries K} (hp : p ≠ 0)
      (hq : q ≠ 0) (hpq : p.order = q.order)
      (hpqv : v p.leadingCoeff ≤ v q.leadingCoeff) :
      Chapter02TwoStageLaurentValuation v p ≤
        Chapter02TwoStageLaurentValuation v q := by
    have hpv : v p.leadingCoeff ≠ (⊤ : WithTop Γ) :=
      (AddValuation.ne_top_iff v).2 (HahnSeries.leadingCoeff_ne_zero.mpr hp)
    have hqv : v q.leadingCoeff ≠ (⊤ : WithTop Γ) :=
      (AddValuation.ne_top_iff v).2 (HahnSeries.leadingCoeff_ne_zero.mpr hq)
    have hpqv' : (v p.leadingCoeff).untop hpv ≤
        (v q.leadingCoeff).untop hqv :=
      WithTop.coe_le_coe.mp (by
        simpa only [WithTop.coe_untop] using hpqv)
    simp only [Chapter02TwoStageLaurentValuation, dif_neg hp, dif_neg hq]
    exact WithTop.coe_le_coe.mpr
      (Prod.Lex.toLex_le_toLex.mpr
        (Or.inr ⟨hpq, hpqv'⟩))
  by_cases hlt : f.order < g.order
  · have ho : (f + g).order = f.order := by
      have horderlt : f.orderTop < g.orderTop := by
        rw [hfo, hgo]
        exact WithTop.coe_lt_coe.mpr hlt
      have htop := HahnSeries.orderTop_add_eq_left horderlt
      apply WithTop.coe_injective
      rw [HahnSeries.order_eq_orderTop_of_ne_zero hfg,
        HahnSeries.order_eq_orderTop_of_ne_zero hf,
        htop]
    have hc := HahnSeries.leadingCoeff_add_eq_left
      (show f.orderTop < g.orderTop by
        rw [hfo, hgo]
        exact WithTop.coe_lt_coe.mpr hlt)
    have hfgval := hvalue_le_of_order_lt hf hg hlt
    have hfsumval :
        Chapter02TwoStageLaurentValuation v f ≤
          Chapter02TwoStageLaurentValuation v (f + g) :=
      hvalue_le_of_order_eq hf hfg ho.symm (by rw [hc])
    rw [min_eq_left hfgval]
    exact hfsumval
  · by_cases hgt : g.order < f.order
    · have ho : (f + g).order = g.order := by
        have horderlt : g.orderTop < f.orderTop := by
          rw [hfo, hgo]
          exact WithTop.coe_lt_coe.mpr hgt
        have htop := HahnSeries.orderTop_add_eq_right horderlt
        apply WithTop.coe_injective
        rw [HahnSeries.order_eq_orderTop_of_ne_zero hfg,
          HahnSeries.order_eq_orderTop_of_ne_zero hg,
          htop]
      have hc := HahnSeries.leadingCoeff_add_eq_right
        (show g.orderTop < f.orderTop by
          rw [hfo, hgo]
          exact WithTop.coe_lt_coe.mpr hgt)
      have hgval := hvalue_le_of_order_lt hg hf hgt
      have hgsumval :
          Chapter02TwoStageLaurentValuation v g ≤
            Chapter02TwoStageLaurentValuation v (f + g) :=
        hvalue_le_of_order_eq hg hfg ho.symm (by rw [hc])
      rw [min_eq_right hgval]
      exact hgsumval
    · have heq : f.order = g.order := le_antisymm (le_of_not_gt hgt)
        (le_of_not_gt hlt)
      have hfirst : f.order ≤ (f + g).order := by
        have h := hsumorder
        rw [hfo, hgo, ← heq, min_self] at h
        rw [← HahnSeries.order_eq_orderTop_of_ne_zero hfg] at h
        exact WithTop.coe_le_coe.mp h
      by_cases hsumord : (f + g).order = f.order
      · have hcoeff : (f + g).leadingCoeff = f.leadingCoeff + g.leadingCoeff := by
          rw [HahnSeries.leadingCoeff_eq, hsumord, HahnSeries.leadingCoeff_eq,
            HahnSeries.leadingCoeff_eq, heq, HahnSeries.coeff_add]
        rcases le_total (v f.leadingCoeff) (v g.leadingCoeff) with hvfg | hvgf
        · have hvadd : v f.leadingCoeff ≤
              v (f.leadingCoeff + g.leadingCoeff) := by
            simpa [min_eq_left hvfg] using v.map_add f.leadingCoeff g.leadingCoeff
          have hvsum : v f.leadingCoeff ≤ v (f + g).leadingCoeff := by
            simpa [hcoeff] using hvadd
          have hfsumval :
              Chapter02TwoStageLaurentValuation v f ≤
                Chapter02TwoStageLaurentValuation v (f + g) :=
            hvalue_le_of_order_eq hf hfg hsumord.symm hvsum
          exact (min_le_left _ _).trans hfsumval
        · have hvadd : v g.leadingCoeff ≤
              v (f.leadingCoeff + g.leadingCoeff) := by
            simpa [min_eq_right hvgf] using v.map_add f.leadingCoeff g.leadingCoeff
          have hvsum : v g.leadingCoeff ≤ v (f + g).leadingCoeff := by
            simpa [hcoeff] using hvadd
          have hgsumval :
              Chapter02TwoStageLaurentValuation v g ≤
                Chapter02TwoStageLaurentValuation v (f + g) :=
            hvalue_le_of_order_eq hg hfg (hsumord.trans heq).symm hvsum
          exact (min_le_right _ _).trans hgsumval
      · have hstrict : f.order < (f + g).order :=
          lt_of_le_of_ne hfirst (Ne.symm hsumord)
        have hfsumval := hvalue_le_of_order_lt hf hfg hstrict
        exact (min_le_left _ _).trans hfsumval

noncomputable def Chapter02TwoStageAdditiveValuation
    {K Γ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Nontrivial Γ] (v : AddValuation K (WithTop Γ)) :
    AddValuation (LaurentSeries K) (WithTop (Chapter02TwoStageValueGroup Γ)) :=
  AddValuation.of (Chapter02TwoStageLaurentValuation v)
    (chapter02_two_stage_value_of_zero v)
    (chapter02_two_stage_value_of_one v)
    (chapter02_two_stage_value_satisfies_sum_inequality v)
    (chapter02_two_stage_value_is_multiplicative v)

theorem chapter02_positive_T_order_outweighs_every_coefficient_value
    {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    {n : ℤ} (hn : 0 < n) (γ : Γ) :
    toLex (0, γ) < toLex (n, 0) := by
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hn)

theorem chapter02_two_stage_order_is_lexicographic
    {K Γ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Nontrivial Γ] (v : AddValuation K (WithTop Γ))
    {f : LaurentSeries K} (hf : f ≠ 0) :
    ∃ n : ℤ, ∃ a : K, ∃ ha : a ≠ 0, n = f.order ∧ a = f.leadingCoeff ∧
      Chapter02TwoStageLaurentValuation v f =
        ((toLex (n, (v a).untop (by
          exact (AddValuation.ne_top_iff v).2 ha)) :
          Chapter02TwoStageValueGroup Γ) :
          WithTop (Chapter02TwoStageValueGroup Γ)) := by
  refine ⟨f.order, f.leadingCoeff, HahnSeries.leadingCoeff_ne_zero.mpr hf, rfl, rfl, ?_⟩
  simp [Chapter02TwoStageLaurentValuation, hf]

def Chapter02LaurentTAdicOrder {K : Type*} [Zero K]
    (f : LaurentSeries K) : WithTop ℤ := by
  classical
  exact if hf : f = 0 then ⊤ else (f.order : WithTop ℤ)

theorem chapter02_two_stage_coarsening_is_T_adic_order
    {K Γ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Nontrivial Γ] (v : AddValuation K (WithTop Γ))
    {f : LaurentSeries K} (hf : f ≠ 0) :
    (ofLex
      ((Chapter02TwoStageLaurentValuation v f).untop
        (by simp [Chapter02TwoStageLaurentValuation, hf]))).1 = f.order := by
  simp [Chapter02TwoStageLaurentValuation, hf]

def Chapter02ConstantLaurentSeries {K : Type*} [Zero K] (a : K) : LaurentSeries K :=
  HahnSeries.single 0 a

theorem chapter02_two_stage_constant_series_recovers_coefficient_value
    {K Γ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Nontrivial Γ] (v : AddValuation K (WithTop Γ)) {a : K} (ha : a ≠ 0) :
    (ofLex
      ((Chapter02TwoStageLaurentValuation v (Chapter02ConstantLaurentSeries a)).untop
        (by simp [Chapter02TwoStageLaurentValuation, Chapter02ConstantLaurentSeries, ha]))).2 =
      (v a).untop ((AddValuation.ne_top_iff v).2 ha) := by
  simp [Chapter02ConstantLaurentSeries, Chapter02TwoStageLaurentValuation, ha]

theorem chapter02_two_stage_is_a_higher_rank_value_group
    {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Nontrivial Γ] :
    ¬ ∃ f : Chapter02TwoStageValueGroup Γ →+o ℝ, Function.Injective f := by
  rintro ⟨f, hf⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : Γ, 0 < γ := by
    by_cases h : ∃ γ : Γ, 0 < γ
    · exact h
    · push Not at h
      have hneg : ∀ γ : Γ, γ ≤ 0 := fun γ => h γ
      obtain ⟨a, b, hab⟩ := exists_pair_ne Γ
      let γ : Γ := a - b
      have hγ0 : γ ≠ 0 := sub_ne_zero.mpr hab
      by_cases hpos : 0 < γ
      · exact ⟨γ, hpos⟩
      · have hneg' : 0 < -γ := by
          exact neg_pos.mpr (lt_of_le_of_ne (hneg γ) hγ0)
        exact ⟨-γ, hneg'⟩
  have hmono : Monotone f := OrderHomClass.monotone f
  have hnonneg : 0 ≤ f (toLex ((0 : ℤ), γ)) := by
    have hle : f (toLex ((0 : ℤ), 0)) ≤ f (toLex ((0 : ℤ), γ)) :=
      hmono (show toLex ((0 : ℤ), 0) ≤ toLex ((0 : ℤ), γ) by
      exact Prod.Lex.toLex_le_toLex.mpr (Or.inr ⟨rfl, hγ.le⟩))
    have hzero : f (toLex ((0 : ℤ), (0 : Γ))) = 0 := by
      change f 0 = 0
      exact f.toAddMonoidHom.map_zero
    rw [← hzero]
    exact hle
  have hpos : 0 < f (toLex ((0 : ℤ), γ)) := by
    have hne : f (toLex ((0 : ℤ), γ)) ≠ 0 := by
      intro hz
      have hz0 : f (toLex ((0 : ℤ), 0)) =
          f (toLex ((0 : ℤ), γ)) := by
        rw [show f (toLex ((0 : ℤ), (0 : Γ))) = 0 by
          change f 0 = 0
          exact f.toAddMonoidHom.map_zero, hz]
      have hdom : toLex ((0 : ℤ), 0) = toLex ((0 : ℤ), γ) := hf hz0
      have hdom' : ((0 : ℤ), (0 : Γ)) = ((0 : ℤ), γ) :=
        toLex_inj.mp hdom
      exact hγ.ne (congrArg Prod.snd hdom')
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  obtain ⟨n, hn⟩ := Archimedean.arch (f (toLex ((1 : ℤ), 0))) hpos
  have hltlex : toLex ((0 : ℤ), n • γ) < toLex ((1 : ℤ), 0) :=
    Prod.Lex.toLex_lt_toLex.mpr (Or.inl (by omega))
  have hlt : f (toLex ((0 : ℤ), n • γ)) < f (toLex ((1 : ℤ), 0)) :=
    (hmono.strictMono_of_injective hf) hltlex
  have hmap : f (toLex ((0 : ℤ), n • γ)) =
      n • f (toLex ((0 : ℤ), γ)) := by
    change f (n • toLex ((0 : ℤ), γ)) =
      n • f (toLex ((0 : ℤ), γ))
    exact map_nsmul f n (toLex ((0 : ℤ), γ))
  rw [hmap] at hlt
  exact (not_lt_of_ge hn) hlt

end
end LastLib.Book01ValuationsDVRsAndCompletions.Chapter02
