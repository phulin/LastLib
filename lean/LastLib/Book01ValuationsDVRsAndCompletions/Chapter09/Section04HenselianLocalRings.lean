import LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.Section03LiftingFactorizations
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Topology.Algebra.WithZeroTopology
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace LastLib.Book01ValuationsDVRsAndCompletions
namespace Chapter09

universe u uK uL uΓ uA uH uC uI

open scoped BigOperators Polynomial WithZeroTopology
open Ideal IsLocalRing Polynomial

noncomputable section

local instance chapter09Section04FactPrime7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
local instance chapter09Section04FactPrime2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩

/-! # Chapter 9: Hensel lifting

This file is a statement-generation pass for Chapter 9 of Book 1.  The
declarations deliberately keep the hypotheses visible: in particular, a
complete DVR means adic completeness, while the valuation form is stated for
an arbitrary additive valuation.
-/

/-! # Book 1, Chapter 9, Section 9.4: Henselian Local Rings
-/

/-! ## 9.4 Henselian local rings -/

/-- The simple-residue-root lifting property. -/
def SimpleResidueRootLiftingProperty (A : Type*) [CommRing A] [IsLocalRing A] : Prop :=
  ∀ (f : A[X]) (a₀ : ResidueRing A), f.Monic →
    (residuePolynomial f).eval a₀ = 0 →
    IsUnit ((residuePolynomial f).derivative.eval a₀) →
    ∃! a : A, f.eval a = 0 ∧ residueClass a = a₀

/-- The coprime-factorization lifting property used as the book's primary
definition of henselianity. -/
def HenselianFactorizationProperty (A : Type*) [CommRing A] [IsLocalRing A] : Prop :=
  ∀ (f : A[X]) (g₀ h₀ : Polynomial (ResidueRing A)), f.Monic →
    g₀.Monic → h₀.Monic → IsCoprime g₀ h₀ → residuePolynomial f = g₀ * h₀ →
    ∃! gh : A[X] × A[X], IsFactorizationLift f g₀ h₀ gh.1 gh.2

/-- The chapter's book-facing henselian predicate. -/
abbrev IsHenselianLocalRingChapter09 (A : Type*) [CommRing A] [IsLocalRing A] : Prop :=
  HenselianFactorizationProperty A

/-- Complete and separated maximal-ideal-adic local rings. -/
def IsMaximalIdealAdicallyCompleteSeparated (A : Type*) [CommRing A] [IsLocalRing A] : Prop :=
  IsAdicComplete (IsLocalRing.maximalIdeal A) A

/-! The bounded correction argument only needs a commutative ring once the
resultant is a unit.  The field-specific version in Section 9.3 is retained
for the DVR construction; this version is used for the general adic proof. -/
theorem coprime_correction_property_of_isCoprime {R : Type*} [CommRing R]
    [Nontrivial R] {g h : R[X]} (hg : g.Monic) (hh : h.Monic)
    (hcop : IsCoprime g h) : CoprimeCorrectionProperty g h := by
  let G : Bool → R[X] := Bool.rec h g
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
      _ = (g * h).degree := (hh.degree_mul (p := g)).symm
  have hrf : (r false * g).degree < (g * h).degree := by
    calc
      (r false * g).degree ≤ (r false).degree + g.degree := degree_mul_le _ _
      _ < h.degree + g.degree := by
        rw [WithBot.add_lt_add_iff_right (degree_ne_bot.mpr hg.ne_zero)]
        simpa [G] using hr false (Finset.mem_univ false)
      _ = (h * g).degree := (hg.degree_mul (p := h)).symm
      _ = (g * h).degree := by rw [mul_comm]
  have hR : (r true * h + r false * g).degree < (g * h).degree :=
    (degree_add_le _ _).trans_lt (max_lt hrt hrf)
  have hq : q = 0 := by
    by_contra hq0
    have hprod : (g * h).degree ≤ (q * (g * h)).degree := by
      rw [(hg.mul hh).degree_mul, degree_eq_natDegree hq0]
      simpa only [zero_add] using
        (add_le_add_left (show (0 : WithBot ℕ) ≤ (q.natDegree : WithBot ℕ) by simp)
          (g * h).degree)
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
    let Rfun : Bool → R[X] := Bool.rec s₁ r₁
    have hRdeg : ∀ i ∈ (Finset.univ : Finset Bool),
        (Rfun i).degree < (G i).degree := by
      intro i hi
      cases i
      · simpa [Rfun, G] using hs₁
      · simpa [Rfun, G] using hr₁
    have hrepr₁ : (0 : R[X]) * (g * h) + r true * h + r false * g = t := by
      simpa [hq] using htq2.symm
    have hrepr₂ : (0 : R[X]) * (g * h) + r₁ * h + s₁ * g = t := by
      simpa [factorizationCorrectionMap] using hcorr₁
    have hEq :
        (0 : R[X]) * (∏ i ∈ (Finset.univ : Finset Bool), G i) +
          ∑ i ∈ (Finset.univ : Finset Bool),
            r i * ∏ j ∈ (Finset.univ : Finset Bool).erase i, G j =
        0 * (∏ i ∈ (Finset.univ : Finset Bool), G i) +
          ∑ i ∈ (Finset.univ : Finset Bool),
            Rfun i * ∏ j ∈ (Finset.univ : Finset Bool).erase i, G j := by
      simpa [huniv, G, Rfun, Finset.erase_insert_of_ne, Finset.erase_insert_eq_erase,
        add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
        hrepr₁.trans hrepr₂.symm
    obtain ⟨_, hreq⟩ : (0 : R[X]) = 0 ∧
        ∀ i ∈ (Finset.univ : Finset Bool), r i = Rfun i :=
      quo_mul_prod_add_sum_rem_mul_prod_unique
        (s := (Finset.univ : Finset Bool)) hG hGcop hr hRdeg hEq
    apply Prod.ext
    · simpa using (hreq true (Finset.mem_univ true)).symm
    · simpa [Rfun] using (hreq false (Finset.mem_univ false)).symm

theorem coprime_lifts_are_coprime {A : Type*} [CommRing A] [IsLocalRing A]
    {g h : A[X]} {g₀ h₀ : Polynomial (ResidueRing A)}
    (hg : g.Monic) (hh : h.Monic)
    (hredg : residuePolynomial g = g₀) (hredh : residuePolynomial h = h₀)
    (hcop : IsCoprime g₀ h₀) : IsCoprime g h := by
  have hg₀ : g₀.Monic := by
    rw [← hredg]
    exact hg.map (residueMap A)
  have hh₀ : h₀.Monic := by
    rw [← hredh]
    exact hh.map (residueMap A)
  apply (Polynomial.isUnit_resultant_iff_isCoprime hg).mp
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  change residueMap A (Polynomial.resultant g h) ≠ 0
  have hdeg_g : g₀.natDegree = g.natDegree := by
    rw [← hredg]
    exact hg.natDegree_map (residueMap A)
  have hdeg_h : h₀.natDegree = h.natDegree := by
    rw [← hredh]
    exact hh.natDegree_map (residueMap A)
  have hres : IsUnit (Polynomial.resultant g₀ h₀) :=
    (Polynomial.isUnit_resultant_iff_isCoprime hg₀).mpr hcop
  rw [← Polynomial.resultant_map_map]
  have hredg' : Polynomial.map (residueMap A) g = g₀ := hredg
  have hredh' : Polynomial.map (residueMap A) h = h₀ := hredh
  rw [hredg', hredh']
  rw [← hdeg_g, ← hdeg_h]
  exact hres.ne_zero

theorem correction_terms_mem_of_coprime {A : Type*} [CommRing A] [IsLocalRing A]
    (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A)
    {n : ℕ} (hn : n ≠ 0) {g h r s t : A[X]}
    (hg : g.Monic) (hh : h.Monic) (hcop : IsCoprime g h)
    (hrdeg : r.degree < g.degree) (hsdeg : s.degree < h.degree)
    (heq : factorizationCorrectionMap g h (r, s) = t)
    (ht : PolynomialCoefficientsInIdeal (I ^ n) t) :
    PolynomialCoefficientsInIdeal (I ^ n) r ∧
      PolynomialCoefficientsInIdeal (I ^ n) s := by
  have hI_ne_top : I ^ n ≠ ⊤ := by
    exact ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      ((Ideal.pow_le_self hn).trans hI)
  let φ : A →+* (A ⧸ I ^ n) := Ideal.Quotient.mk (I ^ n)
  have hquot_nontrivial : Nontrivial (A ⧸ I ^ n) :=
    Ideal.Quotient.nontrivial_iff.mpr hI_ne_top
  have hgmap : (g.map φ).Monic := hg.map φ
  have hhmap : (h.map φ).Monic := hh.map φ
  have hcopmap : IsCoprime (g.map φ) (h.map φ) :=
    hcop.map (Polynomial.mapRingHom φ)
  have hdeg_g : (g.map φ).degree = g.degree := by
    rw [degree_eq_natDegree hg.ne_zero, degree_eq_natDegree (hg.map φ).ne_zero,
      hg.natDegree_map φ]
  have hdeg_h : (h.map φ).degree = h.degree := by
    rw [degree_eq_natDegree hh.ne_zero, degree_eq_natDegree (hh.map φ).ne_zero,
      hh.natDegree_map φ]
  have hrmapdeg : (r.map φ).degree < (g.map φ).degree := by
    simpa [hdeg_g] using (Polynomial.degree_map_le.trans_lt hrdeg)
  have hsmapdeg : (s.map φ).degree < (h.map φ).degree := by
    simpa [hdeg_h] using (Polynomial.degree_map_le.trans_lt hsdeg)
  have htmap : t.map φ = 0 := by
    ext i
    simp only [Polynomial.coeff_map, coeff_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (ht i)
  have hcorrmap :
      factorizationCorrectionMap (g.map φ) (h.map φ) (r.map φ, s.map φ) = t.map φ := by
    simpa [factorizationCorrectionMap, Polynomial.map_add, Polynomial.map_mul] using
      congrArg (Polynomial.map φ) heq
  have hcorrzero : CoprimeCorrectionProperty (g.map φ) (h.map φ) :=
    coprime_correction_property_of_isCoprime hgmap hhmap hcopmap
  obtain ⟨rs, hrs, hrsuniq⟩ := hcorrzero 0 (by
    change (⊥ : WithBot ℕ) < (g.map φ * h.map φ).degree
    exact bot_lt_iff_ne_bot.mpr (degree_ne_bot.mpr (hgmap.mul hhmap).ne_zero))
  have hrs_map : (r.map φ, s.map φ) = rs := by
    apply hrsuniq
    refine ⟨hrmapdeg, hsmapdeg, ?_⟩
    rw [hcorrmap, htmap]
  have hrs_zero : rs = (0, 0) := by
    symm
    apply hrsuniq
    refine ⟨?_, ?_, ?_⟩
    · change (⊥ : WithBot ℕ) < (g.map φ).degree
      exact bot_lt_iff_ne_bot.mpr (degree_ne_bot.mpr hgmap.ne_zero)
    · change (⊥ : WithBot ℕ) < (h.map φ).degree
      exact bot_lt_iff_ne_bot.mpr (degree_ne_bot.mpr hhmap.ne_zero)
    · simp [factorizationCorrectionMap]
  have hrmap_zero : r.map φ = 0 := by
    simpa using congrArg Prod.fst (hrs_map.trans hrs_zero)
  have hsmap_zero : s.map φ = 0 := by
    simpa using congrArg Prod.snd (hrs_map.trans hrs_zero)
  constructor
  · intro i
    have hi := congrArg (fun P : Polynomial (A ⧸ I ^ n) => P.coeff i) hrmap_zero
    have hi' : φ (r.coeff i) = 0 := by
      simpa only [Polynomial.coeff_map, coeff_zero] using hi
    exact Ideal.Quotient.eq_zero_iff_mem.mp hi'
  · intro i
    have hi := congrArg (fun P : Polynomial (A ⧸ I ^ n) => P.coeff i) hsmap_zero
    have hi' : φ (s.coeff i) = 0 := by
      simpa only [Polynomial.coeff_map, coeff_zero] using hi
    exact Ideal.Quotient.eq_zero_iff_mem.mp hi'

/-- A residue root is the linear factor `X-ā`. -/
theorem simple_residue_root_iff_linear_factor {A : Type*} [CommRing A] [IsLocalRing A]
    (f : A[X]) (a₀ : ResidueRing A) :
    (residuePolynomial f).eval a₀ = 0 ↔
      ∃ q : Polynomial (ResidueRing A),
        residuePolynomial f = (X - C a₀) * q := by
  constructor
  · intro hroot
    have hdvd : X - C a₀ ∣ residuePolynomial f := by
      rw [Polynomial.dvd_iff_isRoot]
      simpa [Polynomial.IsRoot] using hroot
    rcases hdvd with ⟨q, hq⟩
    exact ⟨q, hq⟩
  · rintro ⟨q, hq⟩
    have hdvd : X - C a₀ ∣ residuePolynomial f := ⟨q, hq⟩
    have hroot := (Polynomial.dvd_iff_isRoot.mp hdvd)
    simpa [Polynomial.IsRoot] using hroot

/-- A factorization lift applied to `X-ā` gives simple-root lifting. -/
theorem simple_root_lifting_by_linear_factorization
    {A : Type*} [CommRing A] [IsLocalRing A]
    (hfactor : HenselianFactorizationProperty A) :
    SimpleResidueRootLiftingProperty A := by
  intro f a₀ hf hroot hsimple
  let g₀ : Polynomial (ResidueRing A) := X - C a₀
  let h₀ : Polynomial (ResidueRing A) := residuePolynomial f /ₘ g₀
  have hg₀ : g₀.Monic := by
    simpa [g₀] using monic_X_sub_C a₀
  have hred : residuePolynomial f = g₀ * h₀ := by
    simpa [g₀, h₀, modByMonic_X_sub_C_eq_C_eval, hroot] using
      (X_sub_C_mul_divByMonic_eq_sub_modByMonic (residuePolynomial f) a₀).symm
  have hcop : IsCoprime g₀ h₀ := by
    change IsCoprime (X - C a₀) (residuePolynomial f /ₘ (X - C a₀))
    have hsimple_ne : (residuePolynomial f).derivative.eval a₀ ≠ 0 :=
      hsimple.ne_zero
    exact isCoprime_of_is_root_of_eval_derivative_ne_zero
      (K := IsLocalRing.ResidueField A) (residuePolynomial f) a₀ hsimple_ne
  have hprodmonic : (g₀ * h₀).Monic := by
    rw [← hred]
    exact hf.map (residueMap A)
  have hh₀ : h₀.Monic := hg₀.of_mul_monic_left hprodmonic
  obtain ⟨gh, hgh, _⟩ := hfactor f g₀ h₀ hf hg₀ hh₀ hcop hred
  rcases hgh with ⟨hg, hh, hng, hnh, hrg, hrh, hfac⟩
  have hng' : gh.1.natDegree = 1 := by
    simpa [g₀] using hng
  let a : A := -gh.1.coeff 0
  have hpoly : gh.1 = X - C a := by
    rw [hg.eq_X_add_C hng']
    simp [a, sub_neg_eq_add]
  have hfa : f.eval a = 0 := by
    rw [hfac, eval_mul, hpoly]
    simp
  have hresa : residueClass a = a₀ := by
    have hcoeff := congrArg (fun P : Polynomial (ResidueRing A) => P.coeff 0) hrg
    simp [residuePolynomial, g₀] at hcoeff
    change residueMap A (-gh.1.coeff 0) = a₀
    rw [map_neg, hcoeff]
    simp
  obtain ⟨a₀', ha₀'⟩ := Ideal.Quotient.mk_surjective a₀
  have hunit : IsUnit (f.derivative.eval a₀') := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    change residueMap A (f.derivative.eval a₀') ≠ 0
    have hsimple' : (residuePolynomial f).derivative.eval a₀ ≠ 0 :=
      hsimple.ne_zero
    rw [← ha₀'] at hsimple'
    change ((f.map (residueMap A)).derivative).eval (residueMap A a₀') ≠ 0 at hsimple'
    rw [Polynomial.derivative_map, Polynomial.eval_map_apply] at hsimple'
    exact hsimple'
  have hca : CongruentModIdeal (IsLocalRing.maximalIdeal A) a a₀' := by
    unfold CongruentModIdeal
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change residueMap A (a - a₀') = 0
    have hres : residueMap A a = residueMap A a₀' := by
      calc
        residueMap A a = a₀ := by simpa [residueClass, residueMap] using hresa
        _ = residueMap A a₀' := ha₀'.symm
    rw [map_sub, hres]
    simp
  refine ⟨a, ⟨hfa, hresa⟩, ?_⟩
  intro b hb
  have hcb : CongruentModIdeal (IsLocalRing.maximalIdeal A) b a₀' := by
    unfold CongruentModIdeal
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change residueMap A (b - a₀') = 0
    have hres : residueMap A b = residueMap A a₀' := by
      calc
        residueMap A b = a₀ := by simpa [residueClass, residueMap] using hb.2
        _ = residueMap A a₀' := ha₀'.symm
    rw [map_sub, hres]
    simp
  have hunit_a : IsUnit (f.derivative.eval a) :=
    derivative_unit_on_residue_class f hca hunit
  have habmem : a - b ∈ IsLocalRing.maximalIdeal A := by
    unfold CongruentModIdeal at hca hcb
    have h := (IsLocalRing.maximalIdeal A).sub_mem hca hcb
    simpa [sub_eq_add_neg, add_assoc] using h
  have habunit : ¬ IsUnit (a - b) := by
    intro hab
    exact (notMem_maximalIdeal.mpr hab) habmem
  exact (IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub
    (f := f) (a := a) (b := b) hfa hb.1 habunit hunit_a).symm

/-- Mathlib's henselian local-ring class is equivalent to simple-root lifting. -/
theorem mathlib_henselian_iff_simple_residue_root_lifting {A : Type*} [CommRing A]
    [IsLocalRing A] :
  HenselianLocalRing A ↔ SimpleResidueRootLiftingProperty A := by
  constructor
  · intro hH f a₀ hf hroot hsimple
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
    obtain ⟨a, ha, hres⟩ := hH.is_henselian f hf a₀' hfa hunit
    have hares : residueClass a = a₀ := by
      unfold residueClass residueMap
      rw [← ha₀']
      rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact hres
    refine ⟨a, ⟨ha, hares⟩, ?_⟩
    intro b hb
    have hbc : CongruentModIdeal (IsLocalRing.maximalIdeal A) b a₀' := by
      unfold CongruentModIdeal
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      change residueMap A (b - a₀') = 0
      have hresb : residueMap A b = residueMap A a₀' := by
        calc
          residueMap A b = a₀ := by simpa [residueClass, residueMap] using hb.2
          _ = residueMap A a₀' := ha₀'.symm
      rw [map_sub, hresb]
      simp
    have hca : CongruentModIdeal (IsLocalRing.maximalIdeal A) a a₀' := hres
    have hunit_a : IsUnit (f.derivative.eval a) :=
      derivative_unit_on_residue_class f hca hunit
    have habmem : a - b ∈ IsLocalRing.maximalIdeal A := by
      unfold CongruentModIdeal at hca hbc
      have h := (IsLocalRing.maximalIdeal A).sub_mem hca hbc
      simpa [sub_eq_add_neg, add_assoc] using h
    have habunit : ¬ IsUnit (a - b) := by
      intro hab
      exact (notMem_maximalIdeal.mpr hab) habmem
    exact (IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub
      (f := f) (a := a) (b := b) ha hb.1 habunit hunit_a).symm
  · intro hroot
    refine { toIsLocalRing := inferInstance, is_henselian := ?_ }
    intro f hf a₀ hfa hunit
    have hroot' : (residuePolynomial f).eval (residueClass a₀) = 0 := by
      change (f.map (residueMap A)).eval (residueMap A a₀) = 0
      rw [Polynomial.eval_map_apply]
      change (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) (f.eval a₀) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hfa
    have hsimple : IsUnit ((residuePolynomial f).derivative.eval (residueClass a₀)) := by
      simpa only [residueClass, residuePolynomial, Polynomial.derivative_map,
        Polynomial.eval_map_apply] using hunit.map (residueMap A)
    obtain ⟨a, ha, _⟩ := hroot f (residueClass a₀) hf hroot' hsimple
    refine ⟨a, ha.1, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change residueMap A (a - a₀) = 0
    have hres : residueMap A a = residueMap A a₀ := by
      simpa only [residueClass] using ha.2
    rw [map_sub, hres]
    simp

/-- Book-henselian rings satisfy Mathlib's simple-root interface. -/
theorem factorization_henselian_implies_mathlib_henselian
    {A : Type*} [CommRing A] [IsLocalRing A]
    (hfactor : IsHenselianLocalRingChapter09 A) :
    HenselianLocalRing A :=
  (mathlib_henselian_iff_simple_residue_root_lifting (A := A)).mpr
    (simple_root_lifting_by_linear_factorization hfactor)

/-- Mathlib's simple-root henselianity implies the coprime factorization
lifting property used by this chapter. -/
theorem mathlib_henselian_implies_factorization
    {A : Type*} [CommRing A]
    [HenselianLocalRing A] :
    HenselianFactorizationProperty A := by
  sorry

/-- The Mathlib-to-Chapter-9 bridge for the valuation subring attached to a
valuation ring and its fraction field. -/
theorem mathlib_henselian_valuation_ring_implies_factorization
    {A K : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [HenselianLocalRing ((ValuationRing.valuation A K).valuationSubring)] :
    HenselianFactorizationProperty
      ((ValuationRing.valuation A K).valuationSubring) := by
  exact mathlib_henselian_implies_factorization

/-- The chapter-specific henselian predicate is definitionally the
factorization-lifting property. -/
theorem henselian_iff_factorization_lifting {A : Type*} [CommRing A]
    [IsLocalRing A] :
    IsHenselianLocalRingChapter09 A ↔ HenselianFactorizationProperty A := by
  rfl

/-- Adic completeness supplies Mathlib's simple-root henselian class. -/
theorem complete_separated_local_ring_has_simple_root_henselianity
    {A : Type*} [CommRing A]
    [IsLocalRing A] (hA : IsMaximalIdealAdicallyCompleteSeparated A) :
    HenselianLocalRing A := by
  unfold IsMaximalIdealAdicallyCompleteSeparated at hA
  have hring : HenselianRing A (IsLocalRing.maximalIdeal A) :=
    @IsAdicComplete.henselianRing A _ (IsLocalRing.maximalIdeal A) hA
  let hH : HenselianLocalRing A :=
    { is_henselian := by
        intro f hf a₀ hfa hunit
        have hmap : IsUnit
            (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)
              (f.derivative.eval a₀)) :=
          IsUnit.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) hunit
        obtain ⟨a, ha, hres⟩ := hring.is_henselian f hf a₀ hfa hmap
        exact ⟨a, ha, hres⟩ }
  exact hH

theorem adic_factorization_correction_step
    {A : Type*} [CommRing A] [IsLocalRing A]
    (f g h : A[X]) (g₀ h₀ : Polynomial (ResidueRing A)) (n : ℕ)
    (hf : f.Monic) (hg : g.Monic) (hh : h.Monic)
    (hdeg : f.natDegree = (g * h).natDegree)
    (hredg : residuePolynomial g = g₀) (hredh : residuePolynomial h = h₀)
    (hcop : IsCoprime g₀ h₀)
    (happrox : ApproximateFactorization f g h n) (hn : 1 ≤ n) :
    ∃ r s : A[X],
      r.degree < g.degree ∧ s.degree < h.degree ∧
        PolynomialCoefficientsInIdeal ((IsLocalRing.maximalIdeal A) ^ n) r ∧
        PolynomialCoefficientsInIdeal ((IsLocalRing.maximalIdeal A) ^ n) s ∧
        ApproximateFactorization f (g + r) (h + s) (2 * n) := by
  have hcopA : IsCoprime g h :=
    coprime_lifts_are_coprime hg hh hredg hredh hcop
  have hprodmonic : (g * h).Monic := hg.mul hh
  have hEdeg : (f - g * h).degree < (g * h).degree := by
    apply Polynomial.degree_sub_lt_right
    · calc
        f.degree = (f.natDegree : WithBot ℕ) :=
          Polynomial.degree_eq_natDegree hf.ne_zero
        _ = ((g * h).natDegree : WithBot ℕ) := by rw [hdeg]
        _ = (g * h).degree :=
          (Polynomial.degree_eq_natDegree hprodmonic.ne_zero).symm
    · exact hprodmonic.ne_zero
    · rw [hf.leadingCoeff, hprodmonic.leadingCoeff]
  obtain ⟨⟨r, s⟩, hprop, _⟩ :=
    (coprime_correction_property_of_isCoprime hg hh hcopA)
      (f - g * h) hEdeg
  rcases hprop with ⟨hrdeg, hsdeg, hcorr⟩
  change r.degree < g.degree at hrdeg
  change s.degree < h.degree at hsdeg
  have hterms := correction_terms_mem_of_coprime
    (I := IsLocalRing.maximalIdeal A) (le_rfl) (by omega)
    hg hh hcopA hrdeg hsdeg hcorr happrox
  change PolynomialCoefficientsInIdeal ((IsLocalRing.maximalIdeal A) ^ n) r ∧
    PolynomialCoefficientsInIdeal ((IsLocalRing.maximalIdeal A) ^ n) s at hterms
  dsimp [factorizationCorrectionMap] at hcorr
  have hnewerr : f - (g + r) * (h + s) = -(r * s) := by
    have hf_eq : f = (r * h + s * g) + g * h := eq_add_of_sub_eq hcorr.symm
    rw [hf_eq]
    ring
  have hprod :
      PolynomialCoefficientsInIdeal ((IsLocalRing.maximalIdeal A) ^ (n + n)) (r * s) := by
    intro i
    rw [Polynomial.coeff_mul]
    refine Submodule.sum_mem _ ?_
    intro x hx
    have hmem : r.coeff x.1 * s.coeff x.2 ∈
        (IsLocalRing.maximalIdeal A) ^ n * (IsLocalRing.maximalIdeal A) ^ n :=
      Ideal.mul_mem_mul (hterms.1 x.1) (hterms.2 x.2)
    rw [← pow_add] at hmem
    exact hmem
  refine ⟨r, s, hrdeg, hsdeg, hterms.1, hterms.2, ?_⟩
  unfold ApproximateFactorization PolynomialCoefficientsInIdeal
  intro i
  rw [hnewerr]
  simpa only [Polynomial.coeff_neg, two_mul] using
    ((IsLocalRing.maximalIdeal A) ^ (n + n)).neg_mem (hprod i)

/-- Complete separated local rings satisfy the book's factorization form of
Hensel's lemma by the coefficientwise correction argument in the adic topology;
this proof does not depend on a generic simple-root-to-factorization bridge. -/
theorem complete_separated_local_ring_is_henselian
    {A : Type*} [CommRing A] [IsLocalRing A]
    (hA : IsMaximalIdealAdicallyCompleteSeparated A) :
    IsHenselianLocalRingChapter09 A := by
  intro f g₀ h₀ hf hg₀ hh₀ hcop hred
  unfold IsMaximalIdealAdicallyCompleteSeparated at hA
  let _ : IsAdicComplete (IsLocalRing.maximalIdeal A) A := hA
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
      · have hgh1 : gh.1 = 1 := hg.natDegree_eq_zero.mp
          (by simpa [hg01] using hgd)
        rw [hgh1] at hfac
        simpa using hfac.symm
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
        · have hgh2 : gh.2 = 1 := hh.natDegree_eq_zero.mp
            (by simpa [hh01] using hhd)
          rw [hgh2] at hfac
          simpa using hfac.symm
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
      have hpow_ge_succ : ∀ n : ℕ, n + 1 ≤ 2 ^ n := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
            rw [pow_succ]
            omega
      have hpow_ge (n : ℕ) : n ≤ 2 ^ n :=
        (Nat.le_succ n).trans (hpow_ge_succ n)
      let LiftAt : ℕ → (A[X] × A[X]) → Prop := fun n gh =>
        gh.1.Monic ∧ gh.2.Monic ∧
          gh.1.natDegree = g₀.natDegree ∧ gh.2.natDegree = h₀.natDegree ∧
          residuePolynomial gh.1 = g₀ ∧ residuePolynomial gh.2 = h₀ ∧
          ApproximateFactorization f gh.1 gh.2 (2 ^ n)
      let Q : ℕ → Type _ := fun n => {gh : A[X] × A[X] // LiftAt n gh}
      have hQ0 : Q 0 := by
        refine ⟨(g₁, h₁), hg₁, hh₁, hdeg₁, hdeh₁, hredg₁, hredh₁, ?_⟩
        simpa using happrox₁
      let factorChoice : ∀ n (qn : Q n), ∃ r s : A[X],
          r.degree < qn.1.1.degree ∧
            s.degree < qn.1.2.degree ∧
            PolynomialCoefficientsInIdeal
              ((IsLocalRing.maximalIdeal A) ^ (2 ^ n)) r ∧
            PolynomialCoefficientsInIdeal
              ((IsLocalRing.maximalIdeal A) ^ (2 ^ n)) s ∧
            ApproximateFactorization f (qn.1.1 + r) (qn.1.2 + s) (2 ^ (n + 1)) := by
        intro n qn
        rcases qn.property with ⟨hg, hh, hgd, hhd, hrg, hrh, happrox⟩
        obtain ⟨r, s, hrdeg, hsdeg, hrmem, hsmem, hnext⟩ :=
          adic_factorization_correction_step f qn.1.1 qn.1.2 g₀ h₀
            (2 ^ n) hf hg hh (by
              calc
                f.natDegree = (residuePolynomial f).natDegree :=
                  (hf.natDegree_map (residueMap A)).symm
                _ = (g₀ * h₀).natDegree := congrArg Polynomial.natDegree hred
                _ = (qn.1.1 * qn.1.2).natDegree := by
                  rw [hg₀.natDegree_mul hh₀, hg.natDegree_mul hh]
                  rw [hgd, hhd]) hrg hrh hcop happrox
            (Nat.one_le_pow' n 1)
        refine ⟨r, s, hrdeg, hsdeg, hrmem, hsmem, ?_⟩
        simpa [pow_succ, Nat.mul_comm] using hnext
      let StepData : ∀ n, Q n → Type _ := fun n qn =>
        {z : Q (n + 1) × (A[X] × A[X]) //
          z.1.1.1 = qn.1.1 + z.2.1 ∧
            z.1.1.2 = qn.1.2 + z.2.2 ∧
            PolynomialCoefficientsInIdeal
              ((IsLocalRing.maximalIdeal A) ^ (2 ^ n)) z.2.1 ∧
            PolynomialCoefficientsInIdeal
              ((IsLocalRing.maximalIdeal A) ^ (2 ^ n)) z.2.2}
      let stepData : ∀ n (qn : Q n), StepData n qn := fun n qn => by
        rcases qn.property with ⟨hg, hh, hgd, hhd, hrg, hrh, happrox⟩
        let hex := factorChoice n qn
        let r : A[X] := hex.choose
        let s : A[X] := hex.choose_spec.choose
        have hrdeg : r.degree < qn.1.1.degree := hex.choose_spec.choose_spec.1
        have hsdeg : s.degree < qn.1.2.degree := hex.choose_spec.choose_spec.2.1
        have hrmem : PolynomialCoefficientsInIdeal
            ((IsLocalRing.maximalIdeal A) ^ (2 ^ n)) r :=
          hex.choose_spec.choose_spec.2.2.1
        have hsmem : PolynomialCoefficientsInIdeal
            ((IsLocalRing.maximalIdeal A) ^ (2 ^ n)) s :=
          hex.choose_spec.choose_spec.2.2.2.1
        have hnext : ApproximateFactorization f (qn.1.1 + r) (qn.1.2 + s)
            (2 ^ (n + 1)) := hex.choose_spec.choose_spec.2.2.2.2
        have hg' : (qn.1.1 + r).Monic := hg.add_of_left hrdeg
        have hh' : (qn.1.2 + s).Monic := hh.add_of_left hsdeg
        have hgd' : (qn.1.1 + r).natDegree = g₀.natDegree :=
          (natDegree_add_eq_left_of_degree_lt hrdeg).trans hgd
        have hhd' : (qn.1.2 + s).natDegree = h₀.natDegree :=
          (natDegree_add_eq_left_of_degree_lt hsdeg).trans hhd
        have hrzero : residuePolynomial r = 0 := by
          apply Polynomial.ext
          intro i
          have hi : r.coeff i ∈ IsLocalRing.maximalIdeal A :=
            (Ideal.pow_le_self (by positivity : 2 ^ n ≠ 0)) (hrmem i)
          have hi' : residueMap A (r.coeff i) = 0 :=
            Ideal.Quotient.eq_zero_iff_mem.mpr hi
          simpa only [residuePolynomial, Polynomial.coeff_map, coeff_zero] using hi'
        have hszero : residuePolynomial s = 0 := by
          apply Polynomial.ext
          intro i
          have hi : s.coeff i ∈ IsLocalRing.maximalIdeal A :=
            (Ideal.pow_le_self (by positivity : 2 ^ n ≠ 0)) (hsmem i)
          have hi' : residueMap A (s.coeff i) = 0 :=
            Ideal.Quotient.eq_zero_iff_mem.mpr hi
          simpa only [residuePolynomial, Polynomial.coeff_map, coeff_zero] using hi'
        have hrg' : residuePolynomial (qn.1.1 + r) = g₀ := by
          rw [show residuePolynomial (qn.1.1 + r) =
            residuePolynomial qn.1.1 + residuePolynomial r by
              simp [residuePolynomial], hrg, hrzero]
          simp
        have hrh' : residuePolynomial (qn.1.2 + s) = h₀ := by
          rw [show residuePolynomial (qn.1.2 + s) =
            residuePolynomial qn.1.2 + residuePolynomial s by
              simp [residuePolynomial], hrh, hszero]
          simp
        refine ⟨(⟨(qn.1.1 + r, qn.1.2 + s),
          ⟨hg', hh', hgd', hhd', hrg', hrh', hnext⟩⟩, (r, s)), ?_⟩
        exact ⟨rfl, rfl, hrmem, hsmem⟩
      let q : ∀ n, Q n := fun n =>
        Nat.rec hQ0 (fun n qn => (stepData n qn).1.1) n
      have hqsucc (n : ℕ) : q (n + 1) = (stepData n (q n)).1.1 := by
        simp [q]
      have hqsucc_factor (n : ℕ) :
          ∃ r : A[X], (q (n + 1)).1.1 = (q n).1.1 + r ∧
            PolynomialCoefficientsInIdeal
              ((IsLocalRing.maximalIdeal A) ^ (2 ^ n)) r := by
        rw [hqsucc]
        exact ⟨(stepData n (q n)).1.2.1,
          (stepData n (q n)).2.1, (stepData n (q n)).2.2.2.1⟩
      have hqsucc_factor_h (n : ℕ) :
          ∃ s : A[X], (q (n + 1)).1.2 = (q n).1.2 + s ∧
            PolynomialCoefficientsInIdeal
              ((IsLocalRing.maximalIdeal A) ^ (2 ^ n)) s := by
        rw [hqsucc]
        exact ⟨(stepData n (q n)).1.2.2,
          (stepData n (q n)).2.2.1, (stepData n (q n)).2.2.2.2⟩
      have hcoeff_step (k d : ℕ) :
          (q (k + 1)).1.1.coeff d - (q k).1.1.coeff d ∈
            (IsLocalRing.maximalIdeal A) ^ (k + 1) := by
        obtain ⟨r, hr, hmem⟩ := hqsucc_factor k
        rw [hr]
        have hmem' := (Ideal.pow_le_pow_right (hpow_ge_succ k)) (hmem d)
        simpa [Polynomial.coeff_add, sub_eq_add_neg, add_assoc] using hmem'
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
      have hcoeff_step_h (k d : ℕ) :
          (q (k + 1)).1.2.coeff d - (q k).1.2.coeff d ∈
            (IsLocalRing.maximalIdeal A) ^ (k + 1) := by
        obtain ⟨s, hs, hmem⟩ := hqsucc_factor_h k
        rw [hs]
        have hmem' := (Ideal.pow_le_pow_right (hpow_ge_succ k)) (hmem d)
        simpa [Polynomial.coeff_add, sub_eq_add_neg, add_assoc] using hmem'
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
        simp [h, Nat.ne_of_gt hi, Nat.not_lt_of_ge (Nat.le_of_lt hi)]
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
          exact (Ideal.pow_le_pow_right (hpow_ge n)) ha
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
      refine ⟨(g, h), ?_, ?_⟩
      · exact ⟨hg, hh, hdeg_g, hdeg_h, hredg, hredh, hfactor⟩
      · intro gh hgh
        rcases hgh with ⟨hg', hh', hgd', hhd', hredg', hredh', hfac'⟩
        have hprod_eq : gh.1 * gh.2 = g * h := by
          rw [← hfac', hfactor]
        have hcopA : IsCoprime g h :=
          coprime_lifts_are_coprime hg hh hredg hredh hcop
        let m : Ideal A := IsLocalRing.maximalIdeal A
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
        have hstep_unique (n : ℕ) (hn : 1 ≤ n)
            (hgn : ∀ i : ℕ, (gh.1 - g).coeff i ∈ m ^ n)
            (hhn : ∀ i : ℕ, (gh.2 - h).coeff i ∈ m ^ n) :
            ∀ i : ℕ,
              (gh.1 - g).coeff i ∈ m ^ (2 * n) ∧
                (gh.2 - h).coeff i ∈ m ^ (2 * n) := by
          have hlin :
              (gh.1 - g) * h + (gh.2 - h) * g =
                -((gh.1 - g) * (gh.2 - h)) := by
            have hrelg : gh.1 = g + (gh.1 - g) := by ring
            have hrelh : gh.2 = h + (gh.2 - h) := by ring
            have hexpand :
                (g + (gh.1 - g)) * (h + (gh.2 - h)) = g * h := by
              rw [← hrelg, ← hrelh]
              exact hprod_eq
            calc
              (gh.1 - g) * h + (gh.2 - h) * g =
                  (g + (gh.1 - g)) * (h + (gh.2 - h)) - g * h -
                    (gh.1 - g) * (gh.2 - h) := by ring
              _ = -((gh.1 - g) * (gh.2 - h)) := by rw [hexpand]; ring
          have hquad (d : ℕ) :
              ((gh.1 - g) * (gh.2 - h)).coeff d ∈ m ^ (n + n) := by
            rw [Polynomial.coeff_mul]
            refine Submodule.sum_mem _ ?_
            intro x hx
            have hmem := Ideal.mul_mem_mul (hgn x.1) (hhn x.2)
            rw [← pow_add] at hmem
            exact hmem
          have ht : PolynomialCoefficientsInIdeal (m ^ (2 * n))
              (-((gh.1 - g) * (gh.2 - h))) := by
            intro d
            rw [Polynomial.coeff_neg]
            apply (m ^ (2 * n)).neg_mem
            simpa [two_mul] using hquad d
          have hcorr : factorizationCorrectionMap g h
              (gh.1 - g, gh.2 - h) =
                -((gh.1 - g) * (gh.2 - h)) := by
            simpa [factorizationCorrectionMap] using hlin
          have hterms := correction_terms_mem_of_coprime
            (I := IsLocalRing.maximalIdeal A) (le_rfl) (by omega)
            hg hh hcopA hδgdeg hδhdeg hcorr ht
          intro i
          constructor
          · exact hterms.1 i
          · exact hterms.2 i
        have hdiff_pow : ∀ k : ℕ, ∀ i : ℕ,
            (gh.1 - g).coeff i ∈ m ^ (2 ^ k) ∧
              (gh.2 - h).coeff i ∈ m ^ (2 ^ k) := by
          intro k
          induction k with
          | zero =>
              intro i
              simpa [pow_one] using hbase i
          | succ k ih =>
              intro i
              have hs := hstep_unique (2 ^ k) (Nat.one_le_pow' k 1)
                (fun j => (ih j).1) (fun j => (ih j).2) i
              constructor
              · simpa [pow_succ, Nat.mul_comm] using hs.1
              · simpa [pow_succ, Nat.mul_comm] using hs.2
        have hdiff_all (n i : ℕ) :
            (gh.1 - g).coeff i ∈ m ^ n ∧
              (gh.2 - h).coeff i ∈ m ^ n := by
          have hle : n ≤ 2 ^ (n + 1) :=
            (Nat.le_succ n).trans (hpow_ge (n + 1))
          have hs := hdiff_pow (n + 1) i
          exact ⟨(Ideal.pow_le_pow_right hle) hs.1,
            (Ideal.pow_le_pow_right hle) hs.2⟩
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

/-- Complete DVRs satisfy the book's factorization-form definition directly
by the successive-precision theorem of Section 9.3. -/
theorem complete_DVR_is_henselian {A : Type*} [CommRing A] [IsDomain A]
    [CompleteDVR A] : IsHenselianLocalRingChapter09 A := by
  intro f g₀ h₀ hf hg₀ hh₀ hcop hred
  exact hensel_factorization f g₀ h₀ hf hg₀ hh₀ hcop hred

end
end Chapter09
end LastLib.Book01ValuationsDVRsAndCompletions
