import LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.Section02TheValuationForm

namespace LastLib.Book01ValuationsDVRsAndCompletions
namespace Chapter09

universe u uK uL uΓ uA uH uC uI

open scoped BigOperators Polynomial WithZeroTopology
open Ideal IsLocalRing Polynomial

noncomputable section

local instance chapter09Section03FactPrime7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
local instance chapter09Section03FactPrime2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩

/-! # Chapter 9: Hensel lifting

This file is a statement-generation pass for Chapter 9 of Book 1.  The
declarations deliberately keep the hypotheses visible: in particular, a
complete DVR means adic completeness, while the valuation form is stated for
an arbitrary additive valuation.
-/

/-! # Book 1, Chapter 9, Section 9.3: Lifting Factorizations
-/

/-! ## 9.3 Lifting factorizations -/

/-- Approximate factorization modulo a power of the maximal ideal. -/
def ApproximateFactorization {A : Type*} [CommRing A] [IsLocalRing A]
    (f g h : A[X]) (n : ℕ) : Prop :=
  PolynomialCoefficientsInIdeal ((IsLocalRing.maximalIdeal A) ^ n) (f - g * h)

/-- The linear correction map `(r,s) ↦ r h + s g`. -/
def factorizationCorrectionMap {R : Type*} [CommRing R]
    (g h : R[X]) (rs : R[X] × R[X]) : R[X] :=
  rs.1 * h + rs.2 * g

/-- The bounded-degree coprime correction property used in Hensel factor lifting. -/
def CoprimeCorrectionProperty {R : Type*} [CommRing R]
    (g h : R[X]) : Prop :=
  ∀ t : R[X], t.degree < (g * h).degree →
    ∃! rs : R[X] × R[X],
      rs.1.degree < g.degree ∧ rs.2.degree < h.degree ∧
        factorizationCorrectionMap g h rs = t

/-- Coprimality gives the unique bounded-degree solution to the linear correction equation. -/
theorem coprime_correction_property {k : Type*} [Field k]
    {g h : k[X]} (hg : g.Monic) (hh : h.Monic) (hcop : IsCoprime g h) :
    CoprimeCorrectionProperty g h := by
  let G : Bool → k[X] := Bool.rec h g
  have hG : ∀ i ∈ (Finset.univ : Finset Bool), (G i).Monic := by
    intro i hi
    cases i <;> simp [G, hg, hh]
  have hGcop : Set.Pairwise (Finset.univ : Finset Bool)
      (fun i j => IsCoprime (G i) (G j)) := by
    simp [G, Set.pairwise_insert, hcop, hcop.symm]
  intro t ht
  obtain ⟨q, r, hr, htq⟩ :=
    eq_quo_mul_prod_add_sum_rem_mul_prod
      (f := t) (s := (Finset.univ : Finset Bool)) hG hGcop
  have huniv : (Finset.univ : Finset Bool) = {false, true} := by decide
  rw [huniv] at htq
  have htq2 : t = q * (g * h) + r true * h + r false * g := by
    simpa [G, Finset.erase_insert_of_ne, Finset.erase_insert_eq_erase,
      add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using htq
  have hrt : (r true * h).degree < (g * h).degree := by
    calc
      (r true * h).degree ≤ (r true).degree + h.degree := degree_mul_le _ _
      _ < g.degree + h.degree := by
        rw [WithBot.add_lt_add_iff_right (degree_ne_bot.mpr hh.ne_zero)]
        simpa [G] using hr true (Finset.mem_univ true)
      _ = (g * h).degree := (degree_mul).symm
  have hrf : (r false * g).degree < (g * h).degree := by
    calc
      (r false * g).degree ≤ (r false).degree + g.degree := degree_mul_le _ _
      _ < h.degree + g.degree := by
        rw [WithBot.add_lt_add_iff_right (degree_ne_bot.mpr hg.ne_zero)]
        simpa [G] using hr false (Finset.mem_univ false)
      _ = (g * h).degree := by rw [degree_mul]; ac_rfl
  have hR : (r true * h + r false * g).degree < (g * h).degree :=
    (degree_add_le _ _).trans_lt (max_lt hrt hrf)
  have hq : q = 0 := by
    by_contra hq0
    have hprod : (g * h).degree ≤ (q * (g * h)).degree := by
      rw [mul_comm q (g * h)]
      exact degree_le_mul_left (g * h) hq0
    have hRlt : (r true * h + r false * g).degree < (q * (g * h)).degree :=
      lt_of_lt_of_le hR hprod
    have htd : t.degree = (q * (g * h)).degree := by
      rw [htq2, add_assoc, degree_add_eq_left_of_degree_lt hRlt]
    exact (not_lt_of_ge hprod) (htd ▸ ht)
  refine ⟨(r true, r false), ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · simpa [G] using hr true (Finset.mem_univ true)
    · simpa [G] using hr false (Finset.mem_univ false)
    · simpa [factorizationCorrectionMap, hq] using htq2.symm
  · rintro ⟨r₁, s₁⟩ ⟨hr₁, hs₁, hcorr₁⟩
    let R : Bool → k[X] := Bool.rec s₁ r₁
    have hRdeg : ∀ i ∈ (Finset.univ : Finset Bool),
        (R i).degree < (G i).degree := by
      intro i hi
      cases i
      · simpa [R, G] using hs₁
      · simpa [R, G] using hr₁
    have hrepr₁ : (0 : k[X]) * (g * h) + r true * h + r false * g = t := by
      simpa [hq] using htq2.symm
    have hrepr₂ : (0 : k[X]) * (g * h) + r₁ * h + s₁ * g = t := by
      simpa [factorizationCorrectionMap] using hcorr₁
    have hEq :
        (0 : k[X]) * (∏ i ∈ (Finset.univ : Finset Bool), G i) +
          ∑ i ∈ (Finset.univ : Finset Bool),
            r i * ∏ j ∈ (Finset.univ : Finset Bool).erase i, G j =
        0 * (∏ i ∈ (Finset.univ : Finset Bool), G i) +
          ∑ i ∈ (Finset.univ : Finset Bool),
            R i * ∏ j ∈ (Finset.univ : Finset Bool).erase i, G j := by
      simpa [huniv, G, R, Finset.erase_insert_of_ne, Finset.erase_insert_eq_erase,
        add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
        hrepr₁.trans hrepr₂.symm
    obtain ⟨_, hreq⟩ : (0 : k[X]) = 0 ∧
        ∀ i ∈ (Finset.univ : Finset Bool), r i = R i :=
      quo_mul_prod_add_sum_rem_mul_prod_unique
        (s := (Finset.univ : Finset Bool)) hG hGcop hr hRdeg hEq
    apply Prod.ext
    · simpa using (hreq true (Finset.mem_univ true)).symm
    · simpa [R] using (hreq false (Finset.mem_univ false)).symm

/-- One coefficientwise Hensel correction step, modulo `π^(n+1)`. -/
theorem hensel_factorization_step {A : Type*} [CommRing A] [IsDomain A]
    [CompleteDVR A] (f g h : A[X]) (g₀ h₀ : Polynomial (ResidueRing A))
    (π : A) (hπ : IsUniformizer π) (n : ℕ)
    (hf : f.Monic) (hg : g.Monic) (hh : h.Monic)
    (hgdeg : 0 < g.natDegree) (hhdeg : 0 < h.natDegree)
    (happrox : ApproximateFactorization f g h n)
    (hredg : residuePolynomial g = g₀) (hredh : residuePolynomial h = h₀)
    (hcop : IsCoprime g₀ h₀)
    (hred : residuePolynomial f = g₀ * h₀)
    (hn : 1 ≤ n) :
    ∃ r s : A[X],
      r.natDegree < g.natDegree ∧ s.natDegree < h.natDegree ∧
        ApproximateFactorization f
          (g + C (π ^ n) * r) (h + C (π ^ n) * s) (n + 1) := by
  let m : Ideal A := IsLocalRing.maximalIdeal A
  let hfield : Field (ResidueRing A) :=
    Ideal.Quotient.field (IsLocalRing.maximalIdeal A)
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hm : m = Ideal.span ({π} : Set A) := by
    exact hπ.maximalIdeal_eq
  have hm_pow (k : ℕ) : m ^ k = Ideal.span ({π ^ k} : Set A) := by
    rw [hm, Ideal.span_singleton_pow]
  have hc_mem : π ^ n ∈ m ^ n := by
    rw [hm_pow]
    exact Ideal.mem_span_singleton.mpr (dvd_refl _)
  have hcoeff_mem : ∀ i : ℕ, (f - g * h).coeff i ∈ m ^ n := by
    intro i
    exact happrox i
  let qcoeff : ℕ → A := fun i =>
    Classical.choose (Ideal.mem_span_singleton.mp (hm_pow n ▸ hcoeff_mem i))
  have hqcoeff : ∀ i : ℕ, (f - g * h).coeff i = π ^ n * qcoeff i := by
    intro i
    have hi := Classical.choose_spec (Ideal.mem_span_singleton.mp
      (hm_pow n ▸ hcoeff_mem i))
    dsimp [qcoeff]
    exact hi
  have hq_support : ∀ i : ℕ, qcoeff i ≠ 0 → i ∈ (f - g * h).support := by
    intro i hi
    apply Polynomial.mem_support_iff.mpr
    intro hzero
    apply hi
    have hmul : π ^ n * qcoeff i = 0 := by simpa [hzero] using hqcoeff i
    exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero n hπ0)
  let q : ℕ →₀ A := Finsupp.onFinset (f - g * h).support qcoeff hq_support
  let t : A[X] := Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff q)
  have htcoeff : ∀ i : ℕ, t.coeff i = qcoeff i := by
    intro i
    change (AddMonoidAlgebra.ofCoeff q).coeff i = qcoeff i
    simp [q, Finsupp.onFinset_apply]
  have hEt : f - g * h = C (π ^ n) * t := by
    ext i
    rw [Polynomial.coeff_C_mul, htcoeff, hqcoeff]
  have hdeg_f : (residuePolynomial f).natDegree = f.natDegree :=
    hf.natDegree_map (residueMap A)
  have hdeg_g : (residuePolynomial g).natDegree = g.natDegree :=
    hg.natDegree_map (residueMap A)
  have hdeg_h : (residuePolynomial h).natDegree = h.natDegree :=
    hh.natDegree_map (residueMap A)
  have hprod_monic : (g * h).Monic := hg.mul hh
  have hdeg_prod : (g₀ * h₀).natDegree = (g * h).natDegree := by
    calc
      (g₀ * h₀).natDegree = (residuePolynomial g * residuePolynomial h).natDegree := by
        rw [hredg, hredh]
      _ = (residuePolynomial (g * h)).natDegree := by
        simp [residuePolynomial, Polynomial.map_mul]
      _ = (g * h).natDegree := hprod_monic.natDegree_map (residueMap A)
  have hdeg_fprod : f.natDegree = (g * h).natDegree := by
    calc
      f.natDegree = (residuePolynomial f).natDegree := hdeg_f.symm
      _ = (g₀ * h₀).natDegree := by rw [hred]
      _ = (g * h).natDegree := hdeg_prod
  have hg₀ : g₀.Monic := by
    rw [← hredg]
    exact hg.map (residueMap A)
  have hh₀ : h₀.Monic := by
    rw [← hredh]
    exact hh.map (residueMap A)
  have hEdeg : (f - g * h).degree < (g * h).degree := by
    apply Polynomial.degree_sub_lt_right
    · calc
        f.degree = (f.natDegree : WithBot ℕ) := Polynomial.degree_eq_natDegree hf.ne_zero
        _ = ((g * h).natDegree : WithBot ℕ) := by rw [hdeg_fprod]
        _ = (g * h).degree := (Polynomial.degree_eq_natDegree hprod_monic.ne_zero).symm
    · exact hprod_monic.ne_zero
    · rw [hf.leadingCoeff, hprod_monic.leadingCoeff]
  have htdeg : t.degree = (f - g * h).degree := by
    rw [hEt, Polynomial.degree_C_mul (pow_ne_zero n hπ0)]
  have htdeg_lt : t.degree < (g₀ * h₀).degree := by
    rw [htdeg]
    calc
      (f - g * h).degree < (g * h).degree := hEdeg
      _ = (g₀ * h₀).degree := by
        rw [Polynomial.degree_eq_natDegree hprod_monic.ne_zero,
          Polynomial.degree_eq_natDegree (hg₀.mul hh₀).ne_zero,
          hdeg_prod]
  let tbar : Polynomial (ResidueRing A) := t.map (residueMap A)
  have hcorrprop : CoprimeCorrectionProperty g₀ h₀ :=
    @coprime_correction_property (ResidueRing A) hfield g₀ h₀ hg₀ hh₀ hcop
  have htbar_deg : tbar.degree < (g₀ * h₀).degree := by
    exact (Polynomial.degree_map_le.trans_lt htdeg_lt)
  obtain ⟨⟨rbar, sbar⟩, hrsdeg, hrsEq⟩ := hcorrprop tbar htbar_deg
  have hrbar_deg : rbar.degree < g₀.degree := hrsdeg.1
  have hsbar_deg : sbar.degree < h₀.degree := hrsdeg.2.1
  obtain ⟨r₀, hr₀⟩ := Polynomial.map_surjective
    (residueMap A)
    (Ideal.Quotient.mk_surjective : Function.Surjective (residueMap A)) rbar
  obtain ⟨r, hrmap, hrd⟩ :=
    Polynomial.exists_natDegree_eq_of_mem_lifts
      ((Polynomial.mem_lifts rbar).mpr ⟨r₀, hr₀⟩)
  obtain ⟨s₀, hs₀⟩ := Polynomial.map_surjective
    (residueMap A)
    (Ideal.Quotient.mk_surjective : Function.Surjective (residueMap A)) sbar
  obtain ⟨s, hsmap, hsd⟩ :=
    Polynomial.exists_natDegree_eq_of_mem_lifts
      ((Polynomial.mem_lifts sbar).mpr ⟨s₀, hs₀⟩)
  have hrdeg : r.natDegree < g.natDegree := by
    by_cases hrbar0 : rbar = 0
    · rw [hrd, hrbar0]
      exact hgdeg
    · calc
        r.natDegree = rbar.natDegree := hrd
        _ < g₀.natDegree := Polynomial.natDegree_lt_natDegree hrbar0 hrbar_deg
        _ = g.natDegree := by rw [← hredg, hdeg_g]
  have hsdeg : s.natDegree < h.natDegree := by
    by_cases hsbar0 : sbar = 0
    · rw [hsd, hsbar0]
      exact hhdeg
    · calc
        s.natDegree = sbar.natDegree := hsd
        _ < h₀.natDegree := Polynomial.natDegree_lt_natDegree hsbar0 hsbar_deg
        _ = h.natDegree := by rw [← hredh, hdeg_h]
  let u : A[X] := t - (r * h + s * g)
  have hu_res : residuePolynomial u = 0 := by
    calc
      residuePolynomial u = tbar - (rbar * h₀ + sbar * g₀) := by
        rw [residuePolynomial]
        simp only [u, tbar, Polynomial.map_sub, Polynomial.map_add,
          Polynomial.map_mul]
        have hredh' : Polynomial.map (residueMap A) h = h₀ := hredh
        have hredg' : Polynomial.map (residueMap A) g = g₀ := hredg
        rw [hrmap, hsmap, hredh', hredg']
      _ = 0 := by
        have hcorrEq : rbar * h₀ + sbar * g₀ = tbar := by
          simpa [factorizationCorrectionMap] using hrsdeg.2.2
        rw [← hcorrEq]
        simp
  have hu_mem : ∀ i : ℕ, u.coeff i ∈ m := by
    intro i
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change residueMap A (u.coeff i) = 0
    have hi := congrArg (fun P : Polynomial (ResidueRing A) => P.coeff i) hu_res
    simpa [residuePolynomial] using hi
  let J : Ideal A := m ^ (n + 1)
  have hfirst : PolynomialCoefficientsInIdeal J (C (π ^ n) * u) := by
    intro i
    rw [Polynomial.coeff_C_mul]
    have hi := Ideal.mul_mem_mul hc_mem (hu_mem i)
    simpa [J, pow_succ] using hi
  have hc2 : (π ^ n) ^ 2 ∈ J := by
    have hcc : (π ^ n) ^ 2 ∈ m ^ (n + n) := by
      have hcc' : (π ^ n) * (π ^ n) ∈ m ^ n * m ^ n :=
        Ideal.mul_mem_mul hc_mem hc_mem
      rw [← pow_add] at hcc'
      simpa [pow_two] using hcc'
    have hle : n + 1 ≤ n + n := by omega
    exact (Ideal.pow_le_pow_right hle) hcc
  have hsecond : PolynomialCoefficientsInIdeal J (C ((π ^ n) ^ 2) * (r * s)) := by
    intro i
    rw [Polynomial.coeff_C_mul]
    exact Ideal.mul_mem_right _ J hc2
  have hexpand : f - (g + C (π ^ n) * r) * (h + C (π ^ n) * s) =
      C (π ^ n) * u - C ((π ^ n) ^ 2) * (r * s) := by
    have hf_eq : f = C (π ^ n) * t + g * h := eq_add_of_sub_eq hEt
    rw [hf_eq]
    dsimp [u]
    simp [pow_two]
    ring
  refine ⟨r, s, hrdeg, hsdeg, ?_⟩
  unfold ApproximateFactorization PolynomialCoefficientsInIdeal
  intro i
  rw [hexpand]
  simpa only [Polynomial.coeff_sub] using J.sub_mem (hfirst i) (hsecond i)

/-- A pair of lifted factors with the prescribed reductions and degrees. -/
def IsFactorizationLift {A : Type*} [CommRing A] [IsLocalRing A]
    (f : A[X]) (g₀ h₀ : Polynomial (ResidueRing A)) (g h : A[X]) : Prop :=
  g.Monic ∧ h.Monic ∧
    g.natDegree = g₀.natDegree ∧ h.natDegree = h₀.natDegree ∧
    residuePolynomial g = g₀ ∧ residuePolynomial h = h₀ ∧ f = g * h

set_option maxHeartbeats 3000000 in
/-- Factorization-form Hensel lifting: the exact assertion of Theorem 9.3. -/
lemma hensel_factorization {A : Type*} [CommRing A] [IsDomain A]
    [CompleteDVR A] (f : A[X]) (g₀ h₀ : Polynomial (ResidueRing A))
    (hf : f.Monic) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcop : IsCoprime g₀ h₀)
    (hred : residuePolynomial f = g₀ * h₀) :
    ∃! gh : A[X] × A[X], IsFactorizationLift f g₀ h₀ gh.1 gh.2 := by
  by_cases hg0deg : g₀.natDegree = 0
  · have hg01 : g₀ = 1 := hg₀.natDegree_eq_zero.mp hg0deg
    have hredh : residuePolynomial f = h₀ := by simpa [hg01] using hred
    have hfdeg : f.natDegree = h₀.natDegree := by
      calc
        f.natDegree = (residuePolynomial f).natDegree :=
          (hf.natDegree_map (residueMap A)).symm
        _ = h₀.natDegree := congrArg Polynomial.natDegree hredh
    refine ⟨(1, f), ?_, ?_⟩
    · refine ⟨by simp, hf, by simp [hg01], hfdeg, ?_, hredh, by simp⟩
      simp [residuePolynomial, hg01]
    · intro gh hgh
      rcases hgh with ⟨hg, hh, hgd, hhd, hrg, hrh, hfac⟩
      apply Prod.ext
      · exact hg.natDegree_eq_zero.mp (by simpa [hg01] using hgd)
      · rw [show gh.1 = 1 by exact hg.natDegree_eq_zero.mp (by simpa [hg01] using hgd)] at hfac
        simp [hfac]
  · by_cases hh0deg : h₀.natDegree = 0
    · have hh01 : h₀ = 1 := hh₀.natDegree_eq_zero.mp hh0deg
      have hredg : residuePolynomial f = g₀ := by simpa [hh01] using hred
      have hfdeg : f.natDegree = g₀.natDegree := by
        calc
          f.natDegree = (residuePolynomial f).natDegree :=
            (hf.natDegree_map (residueMap A)).symm
          _ = g₀.natDegree := congrArg Polynomial.natDegree hredg
      refine ⟨(f, 1), ?_, ?_⟩
      · refine ⟨hf, by simp, hfdeg, by simp [hh01], hredg, ?_, by simp⟩
        simp [residuePolynomial, hh01]
      · intro gh hgh
        rcases hgh with ⟨hg, hh, hgd, hhd, hrg, hrh, hfac⟩
        apply Prod.ext
        · rw [show gh.2 = 1 by exact hh.natDegree_eq_zero.mp (by simpa [hh01] using hhd)] at hfac
          simp [hfac]
        · exact hh.natDegree_eq_zero.mp (by simpa [hh01] using hhd)
    · have hg0pos : 0 < g₀.natDegree := Nat.pos_of_ne_zero hg0deg
      have hh0pos : 0 < h₀.natDegree := Nat.pos_of_ne_zero hh0deg
      have hg0_lifts : g₀ ∈ Polynomial.lifts (residueMap A) := by
        rw [Polynomial.lifts_iff_coeff_lifts]
        intro n
        exact Ideal.Quotient.mk_surjective (g₀.coeff n)
      have hh0_lifts : h₀ ∈ Polynomial.lifts (residueMap A) := by
        rw [Polynomial.lifts_iff_coeff_lifts]
        intro n
        exact Ideal.Quotient.mk_surjective (h₀.coeff n)
      obtain ⟨g₁, hmapg₁, hdeg₁, hg₁⟩ :=
        Polynomial.lifts_and_natDegree_eq_and_monic hg0_lifts hg₀
      obtain ⟨h₁, hmaph₁, hdeh₁, hh₁⟩ :=
        Polynomial.lifts_and_natDegree_eq_and_monic hh0_lifts hh₀
      have hredg₁ : residuePolynomial g₁ = g₀ := hmapg₁
      have hredh₁ : residuePolynomial h₁ = h₀ := hmaph₁
      have happrox₁ : ApproximateFactorization f g₁ h₁ 1 := by
        unfold ApproximateFactorization PolynomialCoefficientsInIdeal
        intro n
        rw [pow_one]
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        change residueMap A ((f - g₁ * h₁).coeff n) = 0
        have hzero : residuePolynomial f - residuePolynomial (g₁ * h₁) = 0 := by
          rw [hred, ← hredg₁, ← hredh₁]
          simp [residuePolynomial, Polynomial.map_mul]
        simpa only [residuePolynomial, Polynomial.coeff_sub, Polynomial.coeff_map,
          map_zero, coeff_zero, map_sub] using congrArg (fun p => p.coeff n) hzero
      have hpositive_g : 0 < g₁.natDegree := by simpa [hdeg₁] using hg0pos
      have hpositive_h : 0 < h₁.natDegree := by simpa [hdeh₁] using hh0pos
      have hπ : ∃ π : A, IsUniformizer π := IsDiscreteValuationRing.exists_irreducible A
      obtain ⟨π, hπ⟩ := hπ
      let LiftAt : ℕ → (A[X] × A[X]) → Prop := fun n gh =>
        gh.1.Monic ∧ gh.2.Monic ∧
          gh.1.natDegree = g₀.natDegree ∧ gh.2.natDegree = h₀.natDegree ∧
          residuePolynomial gh.1 = g₀ ∧ residuePolynomial gh.2 = h₀ ∧
          ApproximateFactorization f gh.1 gh.2 (n + 1)
      let Q : ℕ → Type _ := fun n => {gh : A[X] × A[X] // LiftAt n gh}
      have hQ0 : Q 0 := by
        refine ⟨(g₁, h₁), hg₁, hh₁, hdeg₁, hdeh₁, hredg₁, hredh₁, happrox₁⟩
      let factorChoice : ∀ n (qn : Q n), ∃ r s : A[X],
          r.natDegree < qn.1.1.natDegree ∧
            s.natDegree < qn.1.2.natDegree ∧
            ApproximateFactorization f
              (qn.1.1 + C (π ^ (n + 1)) * r)
              (qn.1.2 + C (π ^ (n + 1)) * s) (n + 1 + 1) := by
        intro n qn
        rcases qn.property with ⟨hg, hh, hgd, hhd, hrg, hrh, happrox⟩
        exact hensel_factorization_step f qn.1.1 qn.1.2 g₀ h₀ π hπ
          (n + 1) hf hg hh (by simpa [hgd] using hg0pos)
          (by simpa [hhd] using hh0pos) happrox hrg hrh hcop hred (by omega)
      let StepData : ∀ n, Q n → Type _ := fun n qn =>
        {z : Q (n + 1) × (A[X] × A[X]) //
          z.1.1.1 = qn.1.1 + C (π ^ (n + 1)) * z.2.1 ∧
            z.1.1.2 = qn.1.2 + C (π ^ (n + 1)) * z.2.2}
      let stepData : ∀ n (qn : Q n), StepData n qn := fun n qn => by
        rcases qn.property with ⟨hg, hh, hgd, hhd, hrg, hrh, happrox⟩
        have hex := factorChoice n qn
        let r : A[X] := hex.choose
        let s : A[X] := hex.choose_spec.choose
        have hrs : r.natDegree < qn.1.1.natDegree := hex.choose_spec.choose_spec.1
        have hss : s.natDegree < qn.1.2.natDegree := hex.choose_spec.choose_spec.2.1
        have hnext : ApproximateFactorization f
            (qn.1.1 + C (π ^ (n + 1)) * r)
            (qn.1.2 + C (π ^ (n + 1)) * s) (n + 1 + 1) :=
          hex.choose_spec.choose_spec.2.2
        have htermg : (C (π ^ (n + 1)) * r).natDegree < qn.1.1.natDegree :=
          (natDegree_C_mul_le _ _).trans_lt hrs
        have htermh : (C (π ^ (n + 1)) * s).natDegree < qn.1.2.natDegree :=
          (natDegree_C_mul_le _ _).trans_lt hss
        have hg' : (qn.1.1 + C (π ^ (n + 1)) * r).Monic :=
          hg.add_of_left (degree_lt_degree htermg)
        have hh' : (qn.1.2 + C (π ^ (n + 1)) * s).Monic :=
          hh.add_of_left (degree_lt_degree htermh)
        have hgd' : (qn.1.1 + C (π ^ (n + 1)) * r).natDegree = g₀.natDegree :=
          (natDegree_add_eq_left_of_natDegree_lt htermg).trans hgd
        have hhd' : (qn.1.2 + C (π ^ (n + 1)) * s).natDegree = h₀.natDegree :=
          (natDegree_add_eq_left_of_natDegree_lt htermh).trans hhd
        have hπmem : π ∈ IsLocalRing.maximalIdeal A := by
          rw [hπ.maximalIdeal_eq]
          exact Submodule.mem_span_singleton_self π
        have hπpowmem : π ^ (n + 1) ∈ IsLocalRing.maximalIdeal A := by
          simpa [pow_succ, mul_comm] using
            (IsLocalRing.maximalIdeal A).mul_mem_left (π ^ n) hπmem
        have hπpowzero : residueMap A (π ^ (n + 1)) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr hπpowmem
        have hπzero : residueMap A π = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr hπmem
        have hrg' : residuePolynomial
            (qn.1.1 + C (π ^ (n + 1)) * r) = g₀ := by
          calc
            residuePolynomial (qn.1.1 + C (π ^ (n + 1)) * r) =
                residuePolynomial qn.1.1 + residuePolynomial (C (π ^ (n + 1)) * r) := by
                  simp [residuePolynomial]
            _ = g₀ := by rw [hrg]; simp [residuePolynomial, hπzero]
        have hrh' : residuePolynomial
            (qn.1.2 + C (π ^ (n + 1)) * s) = h₀ := by
          calc
            residuePolynomial (qn.1.2 + C (π ^ (n + 1)) * s) =
                residuePolynomial qn.1.2 + residuePolynomial (C (π ^ (n + 1)) * s) := by
                  simp [residuePolynomial]
            _ = h₀ := by rw [hrh]; simp [residuePolynomial, hπzero]
        refine ⟨(⟨(qn.1.1 + C (π ^ (n + 1)) * r,
          qn.1.2 + C (π ^ (n + 1)) * s),
          ⟨hg', hh', hgd', hhd', hrg', hrh', hnext⟩⟩, (r, s)), ?_⟩
        exact ⟨rfl, rfl⟩
      let q : ∀ n, Q n := fun n => Nat.rec hQ0 (fun n qn => (stepData n qn).1.1) n
      have hqsucc (n : ℕ) : q (n + 1) = (stepData n (q n)).1.1 := by
        simp [q]
      have hqsucc_factor (n : ℕ) :
          ∃ r : A[X], (q (n + 1)).1.1 = (q n).1.1 + C (π ^ (n + 1)) * r := by
        rw [hqsucc]
        exact ⟨(stepData n (q n)).1.2.1, (stepData n (q n)).2.1⟩
      have hπpow_mem (k : ℕ) : π ^ (k + 1) ∈
          (IsLocalRing.maximalIdeal A) ^ (k + 1) := by
        exact Ideal.pow_mem_pow
          (by
            rw [hπ.maximalIdeal_eq]
            exact Submodule.mem_span_singleton_self π) _
      have hcoeff_step (k d : ℕ) :
          (q (k + 1)).1.1.coeff d - (q k).1.1.coeff d ∈
            (IsLocalRing.maximalIdeal A) ^ (k + 1) := by
        obtain ⟨r, hr⟩ := hqsucc_factor k
        rw [hr]
        simp only [Polynomial.coeff_add,
          Polynomial.coeff_C_mul]
        simpa [sub_eq_add_neg, add_assoc] using
          Ideal.mul_mem_right (r.coeff d)
            ((IsLocalRing.maximalIdeal A) ^ (k + 1)) (hπpow_mem k)
      have hcoeff_diff (d m n : ℕ) (hmn : m ≤ n) :
          (q m).1.1.coeff d - (q n).1.1.coeff d ∈
            (IsLocalRing.maximalIdeal A) ^ m := by
        induction n, hmn using Nat.le_induction with
        | base => simp
        | succ n hmn ih =>
            have hs := hcoeff_step n d
            have hle : m ≤ n + 1 := hmn.trans (Nat.le_succ n)
            have hs' : (q (n + 1)).1.1.coeff d - (q n).1.1.coeff d ∈
                (IsLocalRing.maximalIdeal A) ^ m :=
              (Ideal.pow_le_pow_right hle) hs
            have hsneg : (q n).1.1.coeff d - (q (n + 1)).1.1.coeff d ∈
                (IsLocalRing.maximalIdeal A) ^ m := by
              simpa [sub_eq_add_neg] using
                (IsLocalRing.maximalIdeal A ^ m).neg_mem hs'
            convert (IsLocalRing.maximalIdeal A ^ m).add_mem ih hsneg using 1 ;
              ring
      have hgCauchy (d : ℕ) :
          AdicCompletion.IsAdicCauchy (IsLocalRing.maximalIdeal A) A
            (fun n => (q n).1.1.coeff d) := by
        intro m n hmn
        rw [SModEq.sub_mem]
        simpa [smul_eq_mul, Ideal.mul_top] using hcoeff_diff d m n hmn
      have hgLimit (d : ℕ) : ∃ L : A, ∀ n : ℕ,
          (q n).1.1.coeff d - L ∈ (IsLocalRing.maximalIdeal A) ^ n := by
        obtain ⟨L, hL⟩ := IsPrecomplete.prec
          (inferInstance : IsPrecomplete (IsLocalRing.maximalIdeal A) A)
          (hgCauchy d)
        refine ⟨L, ?_⟩
        intro n
        have hn := hL n
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hn
        exact hn
      let glim : ℕ → A := fun d => (hgLimit d).choose
      have hglim_spec (d n : ℕ) :
          (q n).1.1.coeff d - glim d ∈ (IsLocalRing.maximalIdeal A) ^ n :=
        (hgLimit d).choose_spec n
      have hcoeff_zero_high (d n : ℕ) (hd : g₀.natDegree < d) :
          (q n).1.1.coeff d = 0 := by
        rcases (q n).property with ⟨hg, hh, hgd, hhd, hrg, hrh, happrox⟩
        apply coeff_eq_zero_of_natDegree_lt
        rw [hgd]
        exact hd
      have hcoeff_lead_one (n : ℕ) :
          (q n).1.1.coeff g₀.natDegree = 1 := by
        rcases (q n).property with ⟨hg, hh, hgd, hhd, hrg, hrh, happrox⟩
        simpa [← hgd] using hg.coeff_natDegree
      have hglim_eq_zero (d : ℕ) (hd : g₀.natDegree < d) : glim d = 0 := by
        apply (IsHausdorff.eq_iff_smodEq (I := IsLocalRing.maximalIdeal A)
          (M := A)).mpr
        intro n
        have hn := hglim_spec d n
        rw [hcoeff_zero_high d n hd] at hn
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
        simpa using (IsLocalRing.maximalIdeal A ^ n).neg_mem hn
      have hglim_eq_one : glim g₀.natDegree = 1 := by
        apply (IsHausdorff.eq_iff_smodEq (I := IsLocalRing.maximalIdeal A)
          (M := A)).mpr
        intro n
        have hn := hglim_spec g₀.natDegree n
        rw [hcoeff_lead_one n] at hn
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
        simpa using (IsLocalRing.maximalIdeal A ^ n).neg_mem hn
      let g : A[X] := X ^ g₀.natDegree +
        ∑ i ∈ Finset.range g₀.natDegree, C (glim i) * X ^ i
      have hg : g.Monic := by
        dsimp [g]
        apply monic_X_pow_add
        simp_rw [← Fin.sum_univ_eq_sum_range, degree_sum_fin_lt]
      have hgcoeff_low (i : ℕ) (hi : i < g₀.natDegree) :
          g.coeff i = glim i := by
        simp [g, hi, Nat.ne_of_lt hi]
      have hgcoeff_lead : g.coeff g₀.natDegree = 1 := by
        simp [g]
      have hgcoeff_high (i : ℕ) (hi : g₀.natDegree < i) :
          g.coeff i = 0 := by
        simp [g, Nat.ne_of_gt hi, Nat.not_lt_of_ge (Nat.le_of_lt hi)]
      have hqsucc_factor_h (n : ℕ) :
          ∃ s : A[X], (q (n + 1)).1.2 = (q n).1.2 + C (π ^ (n + 1)) * s := by
        rw [hqsucc]
        exact ⟨(stepData n (q n)).1.2.2, (stepData n (q n)).2.2⟩
      have hcoeff_step_h (k d : ℕ) :
          (q (k + 1)).1.2.coeff d - (q k).1.2.coeff d ∈
            (IsLocalRing.maximalIdeal A) ^ (k + 1) := by
        obtain ⟨s, hs⟩ := hqsucc_factor_h k
        rw [hs]
        simp only [Polynomial.coeff_add,
          Polynomial.coeff_C_mul]
        simpa [sub_eq_add_neg, add_assoc] using
          Ideal.mul_mem_right (s.coeff d)
            ((IsLocalRing.maximalIdeal A) ^ (k + 1)) (hπpow_mem k)
      have hcoeff_diff_h (d m n : ℕ) (hmn : m ≤ n) :
          (q m).1.2.coeff d - (q n).1.2.coeff d ∈
            (IsLocalRing.maximalIdeal A) ^ m := by
        induction n, hmn using Nat.le_induction with
        | base => simp
        | succ n hmn ih =>
            have hs := hcoeff_step_h n d
            have hle : m ≤ n + 1 := hmn.trans (Nat.le_succ n)
            have hs' : (q (n + 1)).1.2.coeff d - (q n).1.2.coeff d ∈
                (IsLocalRing.maximalIdeal A) ^ m :=
              (Ideal.pow_le_pow_right hle) hs
            have hsneg : (q n).1.2.coeff d - (q (n + 1)).1.2.coeff d ∈
                (IsLocalRing.maximalIdeal A) ^ m := by
              simpa [sub_eq_add_neg] using
                (IsLocalRing.maximalIdeal A ^ m).neg_mem hs'
            convert (IsLocalRing.maximalIdeal A ^ m).add_mem ih hsneg using 1 ;
              ring
      have hhCauchy (d : ℕ) :
          AdicCompletion.IsAdicCauchy (IsLocalRing.maximalIdeal A) A
            (fun n => (q n).1.2.coeff d) := by
        intro m n hmn
        rw [SModEq.sub_mem]
        simpa [smul_eq_mul, Ideal.mul_top] using hcoeff_diff_h d m n hmn
      have hhLimit (d : ℕ) : ∃ L : A, ∀ n : ℕ,
          (q n).1.2.coeff d - L ∈ (IsLocalRing.maximalIdeal A) ^ n := by
        obtain ⟨L, hL⟩ := IsPrecomplete.prec
          (inferInstance : IsPrecomplete (IsLocalRing.maximalIdeal A) A)
          (hhCauchy d)
        refine ⟨L, ?_⟩
        intro n
        have hn := hL n
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hn
        exact hn
      let hlim : ℕ → A := fun d => (hhLimit d).choose
      have hhlim_spec (d n : ℕ) :
          (q n).1.2.coeff d - hlim d ∈ (IsLocalRing.maximalIdeal A) ^ n :=
        (hhLimit d).choose_spec n
      have hcoeff_h_zero_high (d n : ℕ) (hd : h₀.natDegree < d) :
          (q n).1.2.coeff d = 0 := by
        rcases (q n).property with ⟨hg, hh, hgd, hhd, hrg, hrh, happrox⟩
        apply coeff_eq_zero_of_natDegree_lt
        rw [hhd]
        exact hd
      have hcoeff_h_lead_one (n : ℕ) :
          (q n).1.2.coeff h₀.natDegree = 1 := by
        rcases (q n).property with ⟨hg, hh, hgd, hhd, hrg, hrh, happrox⟩
        simpa [← hhd] using hh.coeff_natDegree
      have hhlim_eq_zero (d : ℕ) (hd : h₀.natDegree < d) : hlim d = 0 := by
        apply (IsHausdorff.eq_iff_smodEq (I := IsLocalRing.maximalIdeal A)
          (M := A)).mpr
        intro n
        have hn := hhlim_spec d n
        rw [hcoeff_h_zero_high d n hd] at hn
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
        simpa using (IsLocalRing.maximalIdeal A ^ n).neg_mem hn
      have hhlim_eq_one : hlim h₀.natDegree = 1 := by
        apply (IsHausdorff.eq_iff_smodEq (I := IsLocalRing.maximalIdeal A)
          (M := A)).mpr
        intro n
        have hn := hhlim_spec h₀.natDegree n
        rw [hcoeff_h_lead_one n] at hn
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
        simpa using (IsLocalRing.maximalIdeal A ^ n).neg_mem hn
      let h : A[X] := X ^ h₀.natDegree +
        ∑ i ∈ Finset.range h₀.natDegree, C (hlim i) * X ^ i
      have hh : h.Monic := by
        dsimp [h]
        apply monic_X_pow_add
        simp_rw [← Fin.sum_univ_eq_sum_range, degree_sum_fin_lt]
      have hhcoeff_low (i : ℕ) (hi : i < h₀.natDegree) :
          h.coeff i = hlim i := by
        simp [h, hi, Nat.ne_of_lt hi]
      have hhcoeff_lead : h.coeff h₀.natDegree = 1 := by
        simp [h]
      have hhcoeff_high (i : ℕ) (hi : h₀.natDegree < i) :
          h.coeff i = 0 := by
        simp [h, Nat.ne_of_gt hi,
          Nat.not_lt_of_ge (Nat.le_of_lt hi)]
      have hgcoeff_eq (i : ℕ) : g.coeff i = glim i := by
        by_cases hi : i < g₀.natDegree
        · exact hgcoeff_low i hi
        by_cases hieq : i = g₀.natDegree
        · subst i
          simpa [hglim_eq_one] using hgcoeff_lead
        have hig : g₀.natDegree < i := lt_of_le_of_ne
          (Nat.le_of_not_gt hi) (Ne.symm hieq)
        rw [hgcoeff_high i hig, hglim_eq_zero i hig]
      have hhcoeff_eq (i : ℕ) : h.coeff i = hlim i := by
        by_cases hi : i < h₀.natDegree
        · exact hhcoeff_low i hi
        by_cases hieq : i = h₀.natDegree
        · subst i
          simpa [hhlim_eq_one] using hhcoeff_lead
        have hig : h₀.natDegree < i := lt_of_le_of_ne
          (Nat.le_of_not_gt hi) (Ne.symm hieq)
        rw [hhcoeff_high i hig, hhlim_eq_zero i hig]
      have hprod_coeff (n d : ℕ) :
          ((q n).1.1 * (q n).1.2).coeff d - (g * h).coeff d ∈
            (IsLocalRing.maximalIdeal A) ^ n := by
        rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
        rw [← Finset.sum_sub_distrib]
        apply (IsLocalRing.maximalIdeal A ^ n).sum_mem
        intro x hx
        have hga : (q n).1.1.coeff x.1 - g.coeff x.1 ∈
            (IsLocalRing.maximalIdeal A) ^ n := by
          rw [hgcoeff_eq x.1]
          exact hglim_spec x.1 n
        have hhb : (q n).1.2.coeff x.2 - h.coeff x.2 ∈
            (IsLocalRing.maximalIdeal A) ^ n := by
          rw [hhcoeff_eq x.2]
          exact hhlim_spec x.2 n
        have hterm :
            (q n).1.1.coeff x.1 * (q n).1.2.coeff x.2 -
                g.coeff x.1 * h.coeff x.2 ∈
              (IsLocalRing.maximalIdeal A) ^ n := by
          rw [show (q n).1.1.coeff x.1 * (q n).1.2.coeff x.2 -
                g.coeff x.1 * h.coeff x.2 =
              ((q n).1.1.coeff x.1 - g.coeff x.1) *
                  (q n).1.2.coeff x.2 +
                g.coeff x.1 *
                  ((q n).1.2.coeff x.2 - h.coeff x.2) by ring]
          have h1 := Ideal.mul_mem_left (IsLocalRing.maximalIdeal A ^ n)
            ((q n).1.2.coeff x.2) hga
          have h2 := Ideal.mul_mem_left (IsLocalRing.maximalIdeal A ^ n)
            (g.coeff x.1) hhb
          exact (IsLocalRing.maximalIdeal A ^ n).add_mem
            (by rw [mul_comm]; exact h1) h2
        exact hterm
      have hfactor_coeff (n d : ℕ) :
          (f - g * h).coeff d ∈ (IsLocalRing.maximalIdeal A) ^ n := by
        rcases (q n).property with ⟨hgq, hhq, hgdq, hhdq, hrgq, hrhq, happrox⟩
        unfold ApproximateFactorization PolynomialCoefficientsInIdeal at happrox
        have ha := happrox d
        have ha' : (f - (q n).1.1 * (q n).1.2).coeff d ∈
            (IsLocalRing.maximalIdeal A) ^ n := by
          exact (Ideal.pow_le_pow_right (Nat.le_succ n)) ha
        have hp := hprod_coeff n d
        have hadd := (IsLocalRing.maximalIdeal A ^ n).add_mem ha' hp
        simpa [sub_eq_add_neg, add_assoc] using hadd
      have hfactor : f = g * h := by
        apply sub_eq_zero.mp
        apply Polynomial.ext
        intro d
        apply (IsHausdorff.haus (I := IsLocalRing.maximalIdeal A) (M := A)
          (inferInstance : IsHausdorff (IsLocalRing.maximalIdeal A) A))
        intro n
        rw [SModEq.sub_mem]
        simpa [smul_eq_mul, Ideal.mul_top] using hfactor_coeff n d
      have hqred_g (i : ℕ) :
          residueMap A ((q 1).1.1.coeff i) = g₀.coeff i := by
        rcases (q 1).property with ⟨hgq, hhq, hgdq, hhdq, hrgq, hrhq, happrox⟩
        have hi := congrArg (fun p : Polynomial (ResidueRing A) => p.coeff i) hrgq
        simpa [residuePolynomial] using hi
      have hqred_h (i : ℕ) :
          residueMap A ((q 1).1.2.coeff i) = h₀.coeff i := by
        rcases (q 1).property with ⟨hgq, hhq, hgdq, hhdq, hrgq, hrhq, happrox⟩
        have hi := congrArg (fun p : Polynomial (ResidueRing A) => p.coeff i) hrhq
        simpa [residuePolynomial] using hi
      have hglim_map (i : ℕ) : residueMap A (glim i) = g₀.coeff i := by
        have hi := hglim_spec i 1
        have hi' : residueMap A ((q 1).1.1.coeff i - glim i) = 0 := by
          apply Ideal.Quotient.eq_zero_iff_mem.mpr
          simpa [pow_one] using hi
        rw [map_sub] at hi'
        exact (sub_eq_zero.mp hi').symm.trans (hqred_g i)
      have hlim_map (i : ℕ) : residueMap A (hlim i) = h₀.coeff i := by
        have hi := hhlim_spec i 1
        have hi' : residueMap A ((q 1).1.2.coeff i - hlim i) = 0 := by
          apply Ideal.Quotient.eq_zero_iff_mem.mpr
          simpa [pow_one] using hi
        rw [map_sub] at hi'
        exact (sub_eq_zero.mp hi').symm.trans (hqred_h i)
      have hdeg_g : g.natDegree = g₀.natDegree := by
        have hsum : (∑ i ∈ Finset.range g₀.natDegree,
            C (glim i) * X ^ i).degree < (g₀.natDegree : WithBot ℕ) := by
          simp_rw [← Fin.sum_univ_eq_sum_range, degree_sum_fin_lt]
        dsimp [g]
        rw [Polynomial.natDegree_add_eq_left_of_degree_lt]
        · simp
        · simpa [degree_X_pow] using hsum
      have hdeg_h : h.natDegree = h₀.natDegree := by
        have hsum : (∑ i ∈ Finset.range h₀.natDegree,
            C (hlim i) * X ^ i).degree < (h₀.natDegree : WithBot ℕ) := by
          simp_rw [← Fin.sum_univ_eq_sum_range, degree_sum_fin_lt]
        dsimp [h]
        rw [Polynomial.natDegree_add_eq_left_of_degree_lt]
        · simp
        · simpa [degree_X_pow] using hsum
      have hredg : residuePolynomial g = g₀ := by
        apply Polynomial.ext
        intro i
        by_cases hi : i < g₀.natDegree
        · have hi' : residueMap A (g.coeff i) = g₀.coeff i := by
            rw [hgcoeff_low i hi, hglim_map i]
          simpa only [residuePolynomial, Polynomial.coeff_map] using hi'
        · by_cases hieq : i = g₀.natDegree
          · subst i
            have hi' : residueMap A (g.coeff g₀.natDegree) =
                g₀.coeff g₀.natDegree := by
              rw [hgcoeff_lead, hg₀.coeff_natDegree]
              simp
            simpa only [residuePolynomial, Polynomial.coeff_map] using hi'
          · have hig : g₀.natDegree < i := lt_of_le_of_ne
              (Nat.le_of_not_gt hi) (Ne.symm hieq)
            have hi' : residueMap A (g.coeff i) = g₀.coeff i := by
              rw [hgcoeff_high i hig]
              have hzero : g₀.coeff i = 0 := coeff_eq_zero_of_natDegree_lt hig
              simp [hzero]
            simpa only [residuePolynomial, Polynomial.coeff_map] using hi'
      have hredh : residuePolynomial h = h₀ := by
        apply Polynomial.ext
        intro i
        by_cases hi : i < h₀.natDegree
        · have hi' : residueMap A (h.coeff i) = h₀.coeff i := by
            rw [hhcoeff_low i hi, hlim_map i]
          simpa only [residuePolynomial, Polynomial.coeff_map] using hi'
        · by_cases hieq : i = h₀.natDegree
          · subst i
            have hi' : residueMap A (h.coeff h₀.natDegree) =
                h₀.coeff h₀.natDegree := by
              rw [hhcoeff_lead, hh₀.coeff_natDegree]
              simp
            simpa only [residuePolynomial, Polynomial.coeff_map] using hi'
          · have hig : h₀.natDegree < i := lt_of_le_of_ne
              (Nat.le_of_not_gt hi) (Ne.symm hieq)
            have hi' : residueMap A (h.coeff i) = h₀.coeff i := by
              rw [hhcoeff_high i hig]
              have hzero : h₀.coeff i = 0 := coeff_eq_zero_of_natDegree_lt hig
              simp [hzero]
            simpa only [residuePolynomial, Polynomial.coeff_map] using hi'
      let m : Ideal A := IsLocalRing.maximalIdeal A
      have hm : m = Ideal.span ({π} : Set A) := by
        exact hπ.maximalIdeal_eq
      have hm_pow (n : ℕ) : m ^ n = Ideal.span ({π ^ n} : Set A) := by
        rw [hm, Ideal.span_singleton_pow]
      have hdivide (p : A[X]) (n : ℕ) (hp : ∀ i : ℕ, p.coeff i ∈ m ^ n) :
          ∃ t : A[X], p = C (π ^ n) * t ∧ t.degree ≤ p.degree := by
        let qcoeff : ℕ → A := fun i =>
          Classical.choose (Ideal.mem_span_singleton.mp (hm_pow n ▸ hp i))
        have hqcoeff : ∀ i : ℕ, p.coeff i = π ^ n * qcoeff i := by
          intro i
          have hi := Classical.choose_spec (Ideal.mem_span_singleton.mp
            (hm_pow n ▸ hp i))
          dsimp [qcoeff]
          exact hi
        have hq_support : ∀ i : ℕ, qcoeff i ≠ 0 → i ∈ p.support := by
          intro i hi
          apply Polynomial.mem_support_iff.mpr
          intro hzero
          apply hi
          have hmul : π ^ n * qcoeff i = 0 := by simpa [hzero] using hqcoeff i
          exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero n hπ.ne_zero)
        let q : ℕ →₀ A := Finsupp.onFinset p.support qcoeff hq_support
        let t : A[X] := Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff q)
        have htcoeff : ∀ i : ℕ, t.coeff i = qcoeff i := by
          intro i
          change (AddMonoidAlgebra.ofCoeff q).coeff i = qcoeff i
          simp [q, Finsupp.onFinset_apply]
        have hpt : p = C (π ^ n) * t := by
          ext i
          rw [Polynomial.coeff_C_mul, htcoeff, hqcoeff]
        refine ⟨t, hpt, ?_⟩
        apply Polynomial.degree_mono
        intro i hi
        apply hq_support i
        rw [← htcoeff i]
        exact Polynomial.mem_support_iff.mp hi
      refine ⟨(g, h), ?_, ?_⟩
      · exact ⟨hg, hh, hdeg_g, hdeg_h, hredg, hredh, hfactor⟩
      · intro gh hgh
        rcases hgh with ⟨hg', hh', hgd', hhd', hredg', hredh', hfac'⟩
        have hprod_eq : gh.1 * gh.2 = g * h := by
          rw [← hfac', hfactor]
        have hbase (i : ℕ) :
            (gh.1 - g).coeff i ∈ m ∧ (gh.2 - h).coeff i ∈ m := by
          constructor
          · change (gh.1 - g).coeff i ∈ IsLocalRing.maximalIdeal A
            have hi0 : residueMap A ((gh.1 - g).coeff i) = 0 := by
              have hi := congrArg (fun P : Polynomial (ResidueRing A) => P.coeff i)
                (hredg'.trans hredg.symm)
              have hi' : residueMap A (gh.1.coeff i) = residueMap A (g.coeff i) := by
                simpa only [residuePolynomial, Polynomial.coeff_map] using hi
              rw [Polynomial.coeff_sub, map_sub]
              exact sub_eq_zero.mpr hi'
            exact Ideal.Quotient.eq_zero_iff_mem.mp hi0
          · change (gh.2 - h).coeff i ∈ IsLocalRing.maximalIdeal A
            have hi0 : residueMap A ((gh.2 - h).coeff i) = 0 := by
              have hi := congrArg (fun P : Polynomial (ResidueRing A) => P.coeff i)
                (hredh'.trans hredh.symm)
              have hi' : residueMap A (gh.2.coeff i) = residueMap A (h.coeff i) := by
                simpa only [residuePolynomial, Polynomial.coeff_map] using hi
              rw [Polynomial.coeff_sub, map_sub]
              exact sub_eq_zero.mpr hi'
            exact Ideal.Quotient.eq_zero_iff_mem.mp hi0
        let hfield : Field (ResidueRing A) :=
          Ideal.Quotient.field (IsLocalRing.maximalIdeal A)
        have hstep_unique (n : ℕ) (hn : 1 ≤ n)
            (hgn : ∀ i : ℕ, (gh.1 - g).coeff i ∈ m ^ n)
            (hhn : ∀ i : ℕ, (gh.2 - h).coeff i ∈ m ^ n) :
            ∀ i : ℕ,
              (gh.1 - g).coeff i ∈ m ^ (n + 1) ∧
                (gh.2 - h).coeff i ∈ m ^ (n + 1) := by
          obtain ⟨rg, hrg_eq, hrgdeg⟩ := hdivide (gh.1 - g) n hgn
          obtain ⟨rh, hrh_eq, hrhdeg⟩ := hdivide (gh.2 - h) n hhn
          have hδgdeg : (gh.1 - g).degree < g.degree := by
            apply Polynomial.degree_sub_lt_right
            · rw [Polynomial.degree_eq_natDegree hg'.ne_zero,
                Polynomial.degree_eq_natDegree hg.ne_zero, hgd', hdeg_g]
            · exact hg.ne_zero
            · rw [hg'.leadingCoeff, hg.leadingCoeff]
          have hδhdeg : (gh.2 - h).degree < h.degree := by
            apply Polynomial.degree_sub_lt_right
            · rw [Polynomial.degree_eq_natDegree hh'.ne_zero,
                Polynomial.degree_eq_natDegree hh.ne_zero, hhd', hdeg_h]
            · exact hh.ne_zero
            · rw [hh'.leadingCoeff, hh.leadingCoeff]
          have hrgdeg' : rg.degree < g.degree := hrgdeg.trans_lt hδgdeg
          have hrhdeg' : rh.degree < h.degree := hrhdeg.trans_lt hδhdeg
          have hrelg : gh.1 = g + C (π ^ n) * rg := by
            simpa [add_comm] using (eq_add_of_sub_eq hrg_eq)
          have hrelh : gh.2 = h + C (π ^ n) * rh := by
            simpa [add_comm] using (eq_add_of_sub_eq hrh_eq)
          have hexpand :
              C (π ^ n) * (rg * h + rh * g) +
                  C ((π ^ n) ^ 2) * (rg * rh) = 0 := by
            calc
              C (π ^ n) * (rg * h + rh * g) +
                    C ((π ^ n) ^ 2) * (rg * rh) =
                  (g + C (π ^ n) * rg) * (h + C (π ^ n) * rh) - g * h := by
                    have hC : C ((π ^ n) ^ 2) =
                        C (π ^ n) * C (π ^ n) := by
                      rw [pow_two]
                      exact Polynomial.C_mul (a := π ^ n) (b := π ^ n)
                    simp only [mul_add, add_mul]
                    rw [hC]
                    ring
              _ = gh.1 * gh.2 - g * h := by rw [hrelg, hrelh]
              _ = 0 := sub_eq_zero.mpr hprod_eq
          have hp_mem : π ^ n ∈ m ^ n := by
            rw [hm_pow n]
            exact Ideal.mem_span_singleton.mpr (dvd_refl _)
          have hp2_mem' : (π ^ n) ^ 2 ∈ m ^ (n + n) := by
            have hmul := Ideal.mul_mem_mul hp_mem hp_mem
            rw [← pow_add] at hmul
            simpa [pow_two] using hmul
          have hp2_mem : (π ^ n) ^ 2 ∈ m ^ (n + 1) := by
            exact (Ideal.pow_le_pow_right (by omega)) hp2_mem'
          have hquad (d : ℕ) :
              (C ((π ^ n) ^ 2) * (rg * rh)).coeff d ∈ m ^ (n + 1) := by
            rw [Polynomial.coeff_C_mul]
            exact Ideal.mul_mem_right _ (m ^ (n + 1)) hp2_mem
          have hcancel_mem (x : A) (hx : π ^ n * x ∈ m ^ (n + 1)) :
              x ∈ m := by
            rw [hm]
            obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp
              (hm_pow (n + 1) ▸ hx)
            apply Ideal.mem_span_singleton.mpr
            refine ⟨c, ?_⟩
            apply (mul_left_cancel₀ (pow_ne_zero n hπ.ne_zero))
            calc
              π ^ n * x = π ^ (n + 1) * c := hc
              _ = π ^ n * (π * c) := by rw [pow_succ]; ring
          have hlin_mem (d : ℕ) :
              (rg * h + rh * g).coeff d ∈ m := by
            have he := congrArg (fun P : A[X] => P.coeff d) hexpand
            rw [Polynomial.coeff_add, Polynomial.coeff_C_mul,
              Polynomial.coeff_C_mul] at he
            apply hcancel_mem
            have hneg := (m ^ (n + 1)).neg_mem (hquad d)
            rw [eq_neg_of_add_eq_zero_left he]
            simpa only [Polynomial.coeff_C_mul] using hneg
          have hlin_res : residuePolynomial (rg * h + rh * g) = 0 := by
            apply Polynomial.ext
            intro d
            have hd : residueMap A ((rg * h + rh * g).coeff d) = 0 :=
              Ideal.Quotient.eq_zero_iff_mem.mpr (hlin_mem d)
            simpa only [residuePolynomial, Polynomial.coeff_map, coeff_zero] using hd
          have hcorrprop : CoprimeCorrectionProperty g₀ h₀ :=
            @coprime_correction_property (ResidueRing A) hfield g₀ h₀ hg₀ hh₀ hcop
          have hrgbar_deg : (residuePolynomial rg).degree < g₀.degree := by
            calc
              (residuePolynomial rg).degree ≤ rg.degree := Polynomial.degree_map_le
              _ < g.degree := hrgdeg'
              _ = g₀.degree := by
                rw [Polynomial.degree_eq_natDegree hg.ne_zero,
                  Polynomial.degree_eq_natDegree hg₀.ne_zero, hdeg_g]
          have hrhbar_deg : (residuePolynomial rh).degree < h₀.degree := by
            calc
              (residuePolynomial rh).degree ≤ rh.degree := Polynomial.degree_map_le
              _ < h.degree := hrhdeg'
              _ = h₀.degree := by
                rw [Polynomial.degree_eq_natDegree hh.ne_zero,
                  Polynomial.degree_eq_natDegree hh₀.ne_zero, hdeg_h]
          have hlin_corr :
              factorizationCorrectionMap g₀ h₀
                (residuePolynomial rg, residuePolynomial rh) = 0 := by
            dsimp [factorizationCorrectionMap]
            rw [← hredh, ← hredg]
            simpa [residuePolynomial, Polynomial.map_add, Polynomial.map_mul] using
              hlin_res
          have hg₀deg : g₀.degree ≠ (⊥ : WithBot ℕ) :=
            Polynomial.degree_ne_bot.mpr hg₀.ne_zero
          have hh₀deg : h₀.degree ≠ (⊥ : WithBot ℕ) :=
            Polynomial.degree_ne_bot.mpr hh₀.ne_zero
          have hzero_deg :
              (0 : Polynomial (ResidueRing A)).degree < (g₀ * h₀).degree := by
            rw [Polynomial.degree_zero, Polynomial.degree_mul]
            exact WithBot.bot_lt_iff_ne_bot.mpr
              (WithBot.add_ne_bot.mpr ⟨hg₀deg, hh₀deg⟩)
          obtain ⟨rs₀, hrs₀, hrsuniq⟩ := hcorrprop 0 hzero_deg
          have hzero_prop :
              (0 : Polynomial (ResidueRing A)).degree < g₀.degree ∧
                (0 : Polynomial (ResidueRing A)).degree < h₀.degree ∧
                factorizationCorrectionMap g₀ h₀ (0, 0) = 0 := by
            refine ⟨WithBot.bot_lt_iff_ne_bot.mpr hg₀deg,
              WithBot.bot_lt_iff_ne_bot.mpr hh₀deg, ?_⟩
            simp [factorizationCorrectionMap]
          have hpair :
              (residuePolynomial rg, residuePolynomial rh) = (0, 0) := by
            exact (hrsuniq _ ⟨hrgbar_deg, hrhbar_deg, hlin_corr⟩).trans
              (hrsuniq _ hzero_prop).symm
          have hrg_res : residuePolynomial rg = 0 := congrArg Prod.fst hpair
          have hrh_res : residuePolynomial rh = 0 := congrArg Prod.snd hpair
          have hrg_mem (d : ℕ) : rg.coeff d ∈ m := by
            change rg.coeff d ∈ IsLocalRing.maximalIdeal A
            have hd := congrArg (fun P : Polynomial (ResidueRing A) => P.coeff d)
              hrg_res
            have hd0 : residueMap A (rg.coeff d) = 0 := by
              simpa only [residuePolynomial, Polynomial.coeff_map, coeff_zero] using hd
            exact Ideal.Quotient.eq_zero_iff_mem.mp hd0
          have hrh_mem (d : ℕ) : rh.coeff d ∈ m := by
            change rh.coeff d ∈ IsLocalRing.maximalIdeal A
            have hd := congrArg (fun P : Polynomial (ResidueRing A) => P.coeff d)
              hrh_res
            have hd0 : residueMap A (rh.coeff d) = 0 := by
              simpa only [residuePolynomial, Polynomial.coeff_map, coeff_zero] using hd
            exact Ideal.Quotient.eq_zero_iff_mem.mp hd0
          intro d
          constructor
          · rw [hrg_eq, Polynomial.coeff_C_mul]
            simpa [pow_succ] using Ideal.mul_mem_mul hp_mem (hrg_mem d)
          · rw [hrh_eq, Polynomial.coeff_C_mul]
            simpa [pow_succ] using Ideal.mul_mem_mul hp_mem (hrh_mem d)
        have hdiff_succ : ∀ k : ℕ, ∀ i : ℕ,
            (gh.1 - g).coeff i ∈ m ^ (k + 1) ∧
              (gh.2 - h).coeff i ∈ m ^ (k + 1) := by
          intro k
          induction k with
          | zero => intro i; simpa [pow_one] using hbase i
          | succ k ih =>
              exact hstep_unique (k + 1) (by omega)
                (fun i => (ih i).1) (fun i => (ih i).2)
        have hdiff_all (n i : ℕ) :
            (gh.1 - g).coeff i ∈ m ^ n ∧
              (gh.2 - h).coeff i ∈ m ^ n := by
          cases n with
          | zero => simp
          | succ k => exact hdiff_succ k i
        have hzero_g : gh.1 - g = 0 := by
          apply Polynomial.ext
          intro i
          apply (IsHausdorff.haus (I := IsLocalRing.maximalIdeal A) (M := A)
            (inferInstance : IsHausdorff (IsLocalRing.maximalIdeal A) A))
          intro n
          rw [SModEq.sub_mem]
          simpa [smul_eq_mul, Ideal.mul_top] using (hdiff_all n i).1
        have hzero_h : gh.2 - h = 0 := by
          apply Polynomial.ext
          intro i
          apply (IsHausdorff.haus (I := IsLocalRing.maximalIdeal A) (M := A)
            (inferInstance : IsHausdorff (IsLocalRing.maximalIdeal A) A))
          intro n
          rw [SModEq.sub_mem]
          simpa [smul_eq_mul, Ideal.mul_top] using (hdiff_all n i).2
        apply Prod.ext
        · exact sub_eq_zero.mp hzero_g
        · exact sub_eq_zero.mp hzero_h

/-- The homogeneous first-precision correction equation proves uniqueness of factor lifts. -/
theorem hensel_factorization_unique_at_first_nonzero_precision
    {A : Type*} [CommRing A] [IsDomain A] [CompleteDVR A]
    {f : A[X]} {g₀ h₀ : Polynomial (ResidueRing A)}
    (hf : f.Monic) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcop : IsCoprime g₀ h₀) :
    ∀ gh₁ gh₂ : A[X] × A[X],
      IsFactorizationLift f g₀ h₀ gh₁.1 gh₁.2 →
      IsFactorizationLift f g₀ h₀ gh₂.1 gh₂.2 → gh₁ = gh₂ := by
  intro gh₁ gh₂ h₁ h₂
  rcases h₁ with ⟨hg₁, hh₁, hng₁, hnh₁, hrg₁, hrh₁, hfac₁⟩
  have hred : residuePolynomial f = g₀ * h₀ := by
    calc
      residuePolynomial f = residuePolynomial (gh₁.1 * gh₁.2) := by rw [hfac₁]
      _ = residuePolynomial gh₁.1 * residuePolynomial gh₁.2 := by
        simp [residuePolynomial]
      _ = g₀ * h₀ := by rw [hrg₁, hrh₁]
  obtain ⟨gh, hgh, huniq⟩ :=
    hensel_factorization f g₀ h₀ hf hg₀ hh₀ hcop hred
  have h₁' : IsFactorizationLift f g₀ h₀ gh₁.1 gh₁.2 :=
    ⟨hg₁, hh₁, hng₁, hnh₁, hrg₁, hrh₁, hfac₁⟩
  exact (huniq gh₁ h₁').trans (huniq gh₂ h₂).symm

/-- A simple residue root is a linear factor and therefore lifts uniquely. -/
theorem monic_simple_residue_root_lifts {A : Type*} [CommRing A] [IsDomain A]
    [CompleteDVR A] (f : A[X]) (a₀ : ResidueRing A)
    (hf : f.Monic)
    (hroot : (residuePolynomial f).eval a₀ = 0)
    (hsimple : IsUnit ((residuePolynomial f).derivative.eval a₀)) :
    ∃! a : A, f.eval a = 0 ∧ residueClass a = a₀ := by
  have _hf := hf
  obtain ⟨a₀', ha₀'⟩ := Ideal.Quotient.mk_surjective a₀
  have hfa : f.eval a₀' ∈ IsLocalRing.maximalIdeal A := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change residueMap A (f.eval a₀') = 0
    have hroot' := hroot
    rw [← ha₀'] at hroot'
    change (f.map (residueMap A)).eval (residueMap A a₀') = 0 at hroot'
    rw [Polynomial.eval_map_apply] at hroot'
    exact hroot'
  have hunit : IsUnit (f.derivative.eval a₀') := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    change residueMap A (f.derivative.eval a₀') ≠ 0
    have hsimple' : (residuePolynomial f).derivative.eval a₀ ≠ 0 :=
      hsimple.ne_zero
    rw [← ha₀'] at hsimple'
    change ((f.map (residueMap A)).derivative).eval (residueMap A a₀') ≠ 0 at hsimple'
    rw [Polynomial.derivative_map, Polynomial.eval_map_apply] at hsimple'
    exact hsimple'
  obtain ⟨a, ha, huniq⟩ := hensel_simple_root f a₀' hfa hunit
  refine ⟨a, ?_, ?_⟩
  · refine ⟨ha.1, ?_⟩
    unfold residueClass residueMap
    rw [← ha₀']
    rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact ha.2
  · intro b hb
    have hbc : CongruentModIdeal (IsLocalRing.maximalIdeal A) b a₀' := by
      unfold CongruentModIdeal
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      change residueMap A (b - a₀') = 0
      have hres : residueMap A b = residueMap A a₀' := by
        calc
          residueMap A b = a₀ := by simpa [residueClass, residueMap] using hb.2
          _ = residueMap A a₀' := ha₀'.symm
      rw [map_sub, hres]
      simp
    exact huniq b ⟨hb.1, hbc⟩

/-- Pairwise coprime residue factors lift simultaneously. -/
def PairwiseCoprimeFamily {ι R : Type*} [CommRing R]
    (f : ι → R[X]) : Prop :=
  ∀ ⦃i j : ι⦄, i ≠ j → IsCoprime (f i) (f j)

set_option maxHeartbeats 3000000 in
/-- The simultaneous pairwise-coprime factor lifting consequence. -/
theorem hensel_lift_pairwise_coprime_factors {A : Type*} {ι : Type uI}
    [CommRing A] [IsDomain A]
    [CompleteDVR A] [Fintype ι] (f : A[X])
    (f₀ : ι → Polynomial (ResidueRing A))
    (hf : f.Monic) (hmonic : ∀ i, (f₀ i).Monic)
    (hpair : PairwiseCoprimeFamily f₀)
    (hred : residuePolynomial f = ∏ i, f₀ i) :
    ∃ lifts : ι → A[X],
      (∀ i, (lifts i).Monic ∧ (lifts i).natDegree = (f₀ i).natDegree ∧
        residuePolynomial (lifts i) = f₀ i) ∧
      f = ∏ i, lifts i := by
  classical
  let P : ∀ (ι : Type uI) [Fintype ι], Prop := fun ι _ =>
    ∀ (f : A[X]) (f₀ : ι → Polynomial (ResidueRing A)),
      f.Monic → (∀ i, (f₀ i).Monic) →
      PairwiseCoprimeFamily f₀ → residuePolynomial f = ∏ i, f₀ i →
      ∃ lifts : ι → A[X],
        (∀ i, (lifts i).Monic ∧ (lifts i).natDegree = (f₀ i).natDegree ∧
          residuePolynomial (lifts i) = f₀ i) ∧
        f = ∏ i, lifts i
  have hP : P ι := by
    apply Fintype.induction_empty_option (P := fun ι _ => P ι)
    · intro α β inst e IH
      let : Fintype α := Fintype.ofEquiv β e.symm
      intro f f₀ hf hmonic hpair hred
      let f₀' : α → Polynomial (ResidueRing A) := fun a => f₀ (e a)
      have hmonic' : ∀ a, (f₀' a).Monic := by
        intro a
        exact hmonic (e a)
      have hpair' : PairwiseCoprimeFamily f₀' := by
        intro a b hab
        apply hpair
        intro heq
        apply hab
        exact e.injective heq
      have hred' : residuePolynomial f = ∏ a, f₀' a := by
        rw [hred]
        exact (e.prod_comp f₀).symm
      obtain ⟨lifts, hlifts, hprod⟩ := IH f f₀' hf hmonic' hpair' hred'
      let lifts' : β → A[X] := fun b => lifts (e.symm b)
      refine ⟨lifts', ?_, ?_⟩
      · intro b
        simpa [lifts', f₀'] using hlifts (e.symm b)
      · calc
          f = ∏ a, lifts a := hprod
          _ = ∏ b, lifts' b := by
            rw [← e.prod_comp lifts']
            simp [lifts']
    · intro f f₀ hf hmonic hpair hred
      have hred1 : residuePolynomial f = 1 := by
        simpa using hred
      have hfd : f.natDegree = 0 := by
        calc
          f.natDegree = (residuePolynomial f).natDegree :=
            (hf.natDegree_map (residueMap A)).symm
          _ = (1 : Polynomial (ResidueRing A)).natDegree :=
            congrArg Polynomial.natDegree hred1
          _ = 0 := by simp
      have hf1 : f = 1 := hf.natDegree_eq_zero.mp hfd
      refine ⟨fun i => PEmpty.elim i, ?_, ?_⟩
      · intro i
        exact PEmpty.elim i
      · simp [hf1]
    · intro α inst IH f f₀ hf hmonic hpair hred
      let g₀ : Polynomial (ResidueRing A) := f₀ none
      let h₀ : Polynomial (ResidueRing A) := ∏ a, f₀ (some a)
      have hg₀ : g₀.Monic := hmonic none
      have hh₀ : h₀.Monic := by
        dsimp [h₀]
        exact monic_prod_of_monic Finset.univ _ (by
          intro a ha
          exact hmonic (some a))
      have hcop : IsCoprime g₀ h₀ := by
        dsimp [g₀, h₀]
        apply IsCoprime.prod_right
        intro a ha
        exact hpair (by simp)
      have hred' : residuePolynomial f = g₀ * h₀ := by
        dsimp [g₀, h₀]
        rw [hred, Fintype.prod_option]
      obtain ⟨gh, hgh, _⟩ :=
        hensel_factorization f g₀ h₀ hf hg₀ hh₀ hcop hred'
      rcases hgh with ⟨hg, hh, hgd, hhd, hrg, hrh, hfac⟩
      have hpair' : PairwiseCoprimeFamily (fun a : α => f₀ (some a)) := by
        intro a b hab
        apply hpair
        intro heq
        apply hab
        exact Option.some.inj heq
      obtain ⟨rest, hrest, hrestprod⟩ :=
        IH gh.2 (fun a : α => f₀ (some a)) hh
          (fun a => hmonic (some a)) hpair' hrh
      let lifts : Option α → A[X] := fun o =>
        match o with
        | none => gh.1
        | some a => rest a
      refine ⟨lifts, ?_, ?_⟩
      · intro o
        cases o with
        | none => simpa [lifts, g₀] using And.intro hg (And.intro hgd hrg)
        | some a => simpa [lifts] using hrest a
      · calc
          f = gh.1 * gh.2 := hfac
          _ = gh.1 * ∏ a, rest a := by rw [hrestprod]
          _ = ∏ o, lifts o := by
            rw [Fintype.prod_option]
  simpa [P] using hP f f₀ hf hmonic hpair hred

/-- Residue-field factorization predicts a corresponding factorization upstairs. -/
theorem residue_factorization_predicts_complete_factorization
    {A : Type*} [CommRing A] [IsDomain A] [CompleteDVR A]
    (f : A[X]) (g₀ h₀ : Polynomial (ResidueRing A))
    (hf : f.Monic) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcop : IsCoprime g₀ h₀) (hred : residuePolynomial f = g₀ * h₀) :
    ∃ g h : A[X], IsFactorizationLift f g₀ h₀ g h := by
  obtain ⟨gh, hgh, _⟩ := hensel_factorization f g₀ h₀ hf hg₀ hh₀ hcop hred
  exact ⟨gh.1, gh.2, hgh⟩

end
end Chapter09
end LastLib.Book01ValuationsDVRsAndCompletions
