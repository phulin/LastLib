import LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.Section02TheValuationForm
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.Section04HenselianLocalRings
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Valuation.Integers
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Topology.Algebra.Valued.WithVal
import Mathlib.Topology.Algebra.WithZeroTopology
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

namespace LastLib.Book01ValuationsDVRsAndCompletions
namespace Chapter09

universe u uK uL uΓ uA uH uC uI

open scoped BigOperators Polynomial WithZeroTopology
open Ideal IsLocalRing Polynomial

noncomputable section

local instance chapter09Section06FactPrime7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
local instance chapter09Section06FactPrime2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩

/-! # Chapter 9: Hensel lifting

This file is a statement-generation pass for Chapter 9 of Book 1.  The
declarations deliberately keep the hypotheses visible: in particular, a
complete DVR means adic completeness, while the valuation form is stated for
an arbitrary additive valuation.
-/

/-! # Book 1, Chapter 9, Section 9.6: Algebraic Consequences
-/

/-! ## 9.6 Algebraic consequences -/

/-- A polynomial has a repeated residue root when it and its derivative vanish there. -/
def HasRepeatedResidueRoot {R : Type*} [CommRing R] (f : R[X]) : Prop :=
  ∃ a : R, f.eval a = 0 ∧ f.derivative.eval a = 0

/-- Coefficients of a polynomial are integral over a base ring. -/
def PolynomialCoefficientsIntegralOver {A K : Type*} [CommRing A] [CommRing K]
    [Algebra A K] (f : K[X]) : Prop :=
  ∀ n : ℕ, IsIntegral A (f.coeff n)

/-- A monic factor of a monic polynomial over a field extension has integral coefficients. -/
theorem monic_factor_coefficients_are_integral {A K : Type*} [CommRing A]
    [Field K] [Algebra A K]
    (f : A[X]) (g h : K[X]) (hf : f.Monic) (hg : g.Monic) (hh : h.Monic)
    (hfac : Polynomial.map (algebraMap A K) f = g * h) :
    PolynomialCoefficientsIntegralOver (A := A) (K := K) g ∧ PolynomialCoefficientsIntegralOver (A := A) (K := K) h := by
  constructor
  · intro n
    apply Polynomial.isIntegral_coeff_of_dvd f g hf hg
    exact ⟨h, hfac⟩
  · intro n
    apply Polynomial.isIntegral_coeff_of_dvd f h hf hh
    refine ⟨g, ?_⟩
    rw [mul_comm]
    exact hfac

/-- Integral closedness descends a monic factorization from the fraction field to the DVR. -/
theorem monic_factorization_descends_to_integrally_closed_domain
    {A K : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (f : A[X]) (g h : K[X]) (hf : f.Monic) (hg : g.Monic) (hh : h.Monic)
    (hfac : Polynomial.map (algebraMap A K) f = g * h) :
    ∃ gA hA : A[X],
      gA.Monic ∧ hA.Monic ∧
        Polynomial.map (algebraMap A K) gA = g ∧
        Polynomial.map (algebraMap A K) hA = h ∧ f = gA * hA := by
  have hgdiv : g ∣ Polynomial.map (algebraMap A K) f := ⟨h, hfac⟩
  have hhdiv : h ∣ Polynomial.map (algebraMap A K) f := by
    refine ⟨g, ?_⟩
    rw [mul_comm]
    exact hfac
  obtain ⟨gA, hgA⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K hf hgdiv
  obtain ⟨hA, hhA⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K hf hhdiv
  have hmapg : Polynomial.map (algebraMap A K) gA = g := by
    simpa [hg.leadingCoeff] using hgA
  have hmaph : Polynomial.map (algebraMap A K) hA = h := by
    simpa [hh.leadingCoeff] using hhA
  have hmonicg : gA.Monic := by
    apply Polynomial.monic_of_injective (IsFractionRing.injective A K)
    simpa [hmapg] using hg
  have hmonich : hA.Monic := by
    apply Polynomial.monic_of_injective (IsFractionRing.injective A K)
    simpa [hmaph] using hh
  refine ⟨gA, hA, hmonicg, hmonich, hmapg, hmaph, ?_⟩
  apply Polynomial.map_injective (algebraMap A K) (IsFractionRing.injective A K)
  simpa [Polynomial.map_mul, hmapg, hmaph] using hfac

/-- A monic polynomial with irreducible reduction is irreducible over the fraction field. -/
theorem irreducible_of_irreducible_residue_reduction
    {A K : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K]
    (f : A[X]) (hf : f.Monic)
    (hred : Irreducible (residuePolynomial f)) :
    Irreducible (Polynomial.map (algebraMap A K) f) := by
  have hfa : Irreducible f := by
    apply Polynomial.Monic.irreducible_of_irreducible_map
      (residueMap A) f hf
    simpa [residuePolynomial] using hred
  exact (hf.irreducible_iff_irreducible_map_fraction_map).mp hfa

/-- The converse fails: an irreducible polynomial can acquire a repeated reduction. -/
theorem padic_x_sq_sub_p_irreducible_but_reduction_repeated (p : ℕ) [Fact p.Prime] :
    Irreducible
        (Polynomial.map (algebraMap (ℤ_[p]) (ℚ_[p]))
          (quadraticPolynomial (p : ℤ_[p]))) ∧
      HasRepeatedResidueRoot (quadraticPolynomial (p : ZMod p)) := by
  constructor
  · apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
      (p := Polynomial.map (algebraMap (ℤ_[p]) (ℚ_[p]))
        (quadraticPolynomial (p : ℤ_[p])))
      (by
        have hnd :
            (Polynomial.map (algebraMap (ℤ_[p]) (ℚ_[p]))
              (quadraticPolynomial (p : ℤ_[p]))).natDegree = 2 := by
          simp only [quadraticPolynomial, Polynomial.map_sub, Polynomial.map_pow,
            Polynomial.map_C, Polynomial.map_X]
          rw [natDegree_sub_C, natDegree_X_pow]
        rw [hnd]
        norm_num)
    intro x hx
    apply padic_x_sq_sub_p_has_no_root p
    refine ⟨x, ?_⟩
    have hx' : x ^ 2 = (p : ℚ_[p]) := by
      apply sub_eq_zero.mp
      simpa [quadraticPolynomial] using hx
    exact hx'
  · refine ⟨0, ?_, ?_⟩
    · simp [quadraticPolynomial]
    · simp [quadraticPolynomial]

/-- Henselianity is the hypothesis needed to lift a coprime residue factorization. -/
theorem henselianity_lifts_coprime_residue_factorization
    {A : Type*} [CommRing A] [IsLocalRing A]
    (hH : HenselianFactorizationProperty A)
    (f : A[X]) (g₀ h₀ : Polynomial (ResidueRing A))
    (hf : f.Monic) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcop : IsCoprime g₀ h₀) (hred : residuePolynomial f = g₀ * h₀) :
    ∃! gh : A[X] × A[X], IsFactorizationLift f g₀ h₀ gh.1 gh.2 := by
  exact hH f g₀ h₀ hf hg₀ hh₀ hcop hred

/-- A complete rank-one valued field satisfies Mathlib's simple-root
henselianity.  The factorization-form theorem is stated separately below. -/
theorem complete_valued_field_has_simple_root_henselianity
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ)
    [Valuation.RankOne vK]
    (hcomplete : @CompleteSpace K (Valued.mk' vK).toUniformSpace) :
    HenselianLocalRing vK.valuationSubring := by
  let v : AddValuation K (Additive Γ)ᵒᵈ := Valuation.toAddValuation vK
  have hv_equiv : vK.IsEquiv v.toValuation := by
    rw [Valuation.isEquiv_iff_val_le_one]
    intro x
    rfl
  let hrank : Valuation.RankOne v.toValuation :=
    { hom' := (Valuation.RankOne.hom vK).comp
        hv_equiv.orderMonoidIso.symm.toMonoidWithZeroHom
      strictMono' := (Valuation.RankOne.strictMono vK).comp
        hv_equiv.orderMonoidIso.symm.strictMono
      exists_val_nontrivial := by
        obtain ⟨r, hr0, hr1⟩ := Valuation.RankOne.nontrivial vK
        refine ⟨r, ?_, ?_⟩
        · intro hr
          exact hr0 ((hv_equiv.eq_zero).mpr hr)
        · intro hr
          exact hr1 ((hv_equiv.eq_one_iff_eq_one).mpr hr) }
  have hA : IsValuationSubring vK.valuationSubring.toSubring v := by
    intro x
    change x ∈ vK.valuationSubring ↔ v x ≥ 0
    rw [Valuation.mem_valuationSubring_iff]
    rfl
  have hcomplete' : Chapter09NonarchimedeanComplete v := by
    have hforward : @UniformContinuous K K
        (Valued.mk' vK).toUniformSpace (Valued.mk' v.toValuation).toUniformSpace
        (id : K → K) := hv_equiv.symm.uniformContinuous
    have hback : @UniformContinuous K K
        (Valued.mk' v.toValuation).toUniformSpace (Valued.mk' vK).toUniformSpace
        (id : K → K) := hv_equiv.uniformContinuous
    have hind : @IsUniformInducing K K
        (Valued.mk' vK).toUniformSpace (Valued.mk' v.toValuation).toUniformSpace
        (id : K → K) :=
      @IsUniformInducing.of_comp K K K
        (Valued.mk' vK).toUniformSpace
        (Valued.mk' v.toValuation).toUniformSpace
        (Valued.mk' vK).toUniformSpace
        (id : K → K) (id : K → K) hforward hback
        (@IsUniformInducing.id K (Valued.mk' vK).toUniformSpace)
    have hc : @CompleteSpace K (Valued.mk' v.toValuation).toUniformSpace :=
      (@IsUniformInducing.completeSpace_congr K K
        (Valued.mk' vK).toUniformSpace (Valued.mk' v.toValuation).toUniformSpace
        (id : K → K) hind (Function.surjective_id)).mp hcomplete
    exact hc
  refine { is_henselian := ?_ }
  intro f hf a₀ hfa hunit
  let fK : K[X] := f.map (Subring.subtype vK.valuationSubring.toSubring)
  have hfK : fK.Monic := by
    exact hf.map (Subring.subtype vK.valuationSubring.toSubring)
  have hfcoeff : PolynomialCoefficientsInSubring
      vK.valuationSubring.toSubring fK := by
    intro n
    change (f.map (Subring.subtype vK.valuationSubring.toSubring)).coeff n ∈
      vK.valuationSubring.toSubring
    rw [Polynomial.coeff_map]
    exact (f.coeff n).property
  have hfa_eval : fK.eval (a₀ : K) = ((f.eval a₀ : vK.valuationSubring) : K) := by
    change (f.map (Subring.subtype vK.valuationSubring.toSubring)).eval
        ((Subring.subtype vK.valuationSubring.toSubring) a₀) =
      (Subring.subtype vK.valuationSubring.toSubring) (f.eval a₀)
    exact Polynomial.eval_map_apply
      (Subring.subtype vK.valuationSubring.toSubring) a₀
  have hderiv_eval : fK.derivative.eval (a₀ : K) =
      ((f.derivative.eval a₀ : vK.valuationSubring) : K) := by
    rw [show fK.derivative =
        f.derivative.map (Subring.subtype vK.valuationSubring.toSubring) by
      simp [fK]]
    change (f.derivative.map (Subring.subtype vK.valuationSubring.toSubring)).eval
        ((Subring.subtype vK.valuationSubring.toSubring) a₀) =
      (Subring.subtype vK.valuationSubring.toSubring) (f.derivative.eval a₀)
    exact Polynomial.eval_map_apply
      (Subring.subtype vK.valuationSubring.toSubring) a₀
  have hfa_val : v (fK.eval (a₀ : K)) > 0 := by
    have hlt : vK ((f.eval a₀ : vK.valuationSubring) : K) < 1 :=
      (Valuation.mem_maximalIdeal_iff (v := vK)).mp hfa
    rw [hfa_eval]
    change 0 < OrderDual.toDual
      (Additive.ofMul (vK ((f.eval a₀ : vK.valuationSubring) : K)))
    exact hlt
  have hderiv_val : v ((f.derivative.eval a₀ : vK.valuationSubring) : K) = 0 := by
    obtain ⟨u, hu⟩ := isUnit_iff_exists_inv.mp hunit
    have hmul : ((f.derivative.eval a₀ : vK.valuationSubring) : K) * (u : K) = 1 := by
      exact congrArg (fun z : vK.valuationSubring => (z : K)) hu
    have hnonneg : 0 ≤ v ((f.derivative.eval a₀ : vK.valuationSubring) : K) :=
      (hA _).mp (f.derivative.eval a₀).property
    have hunonneg : 0 ≤ v (u : K) := (hA _).mp u.property
    have hsum : v ((f.derivative.eval a₀ : vK.valuationSubring) : K) + v (u : K) = 0 := by
      rw [← v.map_mul, hmul, v.map_one]
    apply le_antisymm
    · calc
        v ((f.derivative.eval a₀ : vK.valuationSubring) : K) =
            v ((f.derivative.eval a₀ : vK.valuationSubring) : K) + 0 := by simp
        _ ≤ v ((f.derivative.eval a₀ : vK.valuationSubring) : K) + v (u : K) :=
          add_le_add (le_refl _) hunonneg
        _ = 0 := hsum
    · exact hnonneg
  have hineq : v (fK.eval (a₀ : K)) >
      v (fK.derivative.eval (a₀ : K)) + v (fK.derivative.eval (a₀ : K)) := by
    have hderivK_val : v (fK.derivative.eval (a₀ : K)) = 0 := by
      rw [hderiv_eval, hderiv_val]
    rw [hfa_eval, hderivK_val]
    have hfa_val' := hfa_val
    rw [hfa_eval] at hfa_val'
    simpa only [add_zero] using hfa_val'
  obtain ⟨huniq, _hexact⟩ := @hensel_newton_form K (Additive Γ)ᵒᵈ _ _ v hrank
    vK.valuationSubring.toSubring hA fK hfcoeff (a₀ : K) a₀.property hineq hcomplete'
  obtain ⟨a, ha, _ha_unique⟩ := huniq
  have hroot := ha.2.1
  have hstrict := ha.2.2
  have hderivK_val : v (fK.derivative.eval (a₀ : K)) = 0 := by
    rw [hderiv_eval, hderiv_val]
  have ha_val : v a ≥ 0 := by
    have hdiff : v (a - (a₀ : K)) ≥ 0 :=
      le_of_lt (by simpa [hderivK_val] using hstrict)
    have hsum := valuation_strong_triangle v (a - (a₀ : K)) (a₀ : K)
    have hmin : 0 ≤ min (v (a - (a₀ : K))) (v (a₀ : K)) :=
      le_min hdiff ((hA _).mp a₀.property)
    exact hmin.trans (by simpa [sub_add_cancel] using hsum)
  let a' : vK.valuationSubring := ⟨a, (hA _).mpr ha_val⟩
  refine ⟨a', ?_, ?_⟩
  · apply Subtype.ext
    change ((f.eval a' : vK.valuationSubring) : K) = 0
    have heval : fK.eval (a : K) =
        ((f.eval a' : vK.valuationSubring) : K) := by
      change (f.map (Subring.subtype vK.valuationSubring.toSubring)).eval
          ((Subring.subtype vK.valuationSubring.toSubring) a') =
        (Subring.subtype vK.valuationSubring.toSubring) (f.eval a')
      exact Polynomial.eval_map_apply
        (Subring.subtype vK.valuationSubring.toSubring) a'
    rw [← heval]
    exact hroot
  · rw [Valuation.mem_maximalIdeal_iff]
    have hdiff : v (a - (a₀ : K)) > 0 := by
      simpa [hderivK_val] using hstrict
    have hdiffK : vK (a - (a₀ : K)) < 1 := by
      change 0 < OrderDual.toDual (Additive.ofMul (vK (a - (a₀ : K)))) at hdiff
      exact hdiff
    simpa [a'] using hdiffK

/-- Rank-one values are cofinal under repeated doubling. -/
private theorem section06_rank_one_image_doubling_cofinal {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ)
    [Valuation.RankOne v.toValuation] (q : Γ) (hq : 0 < q)
    (hqimage : q ≠ ⊤ → ∃ z : K, z ≠ 0 ∧ v z = q) :
    ∀ γ : Γ, (∃ x : K, x ≠ 0 ∧ v x = γ) →
      ∃ n : ℕ, γ ≤ (2 ^ n) • q := by
  let G := MonoidWithZeroHom.ValueGroup₀ (.ofClass v.toValuation)
  intro γ hγ
  rcases hγ with ⟨x, hx0, rfl⟩
  by_cases hqtop : q = ⊤
  · exact ⟨0, by simp [hqtop]⟩
  obtain ⟨z, hz0, hzq⟩ := hqimage hqtop
  let hxv : G := v.toValuation.restrict x
  let hzv : G := v.toValuation.restrict z
  have hxv0 : hxv ≠ 0 := by
    dsimp [hxv]
    exact v.toValuation.restrict.ne_zero_iff.mpr hx0
  have hzv0 : hzv ≠ 0 := by
    dsimp [hzv]
    exact v.toValuation.restrict.ne_zero_iff.mpr hz0
  let ξ : Gˣ := Units.mk0 hxv hxv0
  let η : Gˣ := Units.mk0 hzv hzv0
  have hηlt : η < 1 := by
    change hzv < (1 : G)
    dsimp [hzv]
    rw [Valuation.restrict_lt_iff_lt_embedding]
    change Multiplicative.ofAdd (OrderDual.toDual (v z)) <
      Multiplicative.ofAdd (OrderDual.toDual (0 : Γ))
    rw [hzq]
    change OrderDual.toDual q < OrderDual.toDual (0 : Γ)
    change (0 : Γ) < q
    exact hq
  obtain ⟨m, hm⟩ := exists_pow_lt hηlt ξ
  have hm' : hzv ^ m < hxv := by
    change (η : G) ^ m < (ξ : G) at hm
    simpa [η, ξ] using hm
  have hmval : v.toValuation (z ^ m) < v.toValuation x := by
    calc
      v.toValuation (z ^ m) =
          MonoidWithZeroHom.ValueGroup₀.embedding (hzv ^ m) := by
        rw [show hzv ^ m = (v.toValuation.restrict z) ^ m by rfl]
        rw [← map_pow, Valuation.embedding_restrict]
      _ < MonoidWithZeroHom.ValueGroup₀.embedding hxv :=
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono hm'
      _ = v.toValuation x := by
        rw [show hxv = v.toValuation.restrict x by rfl,
          Valuation.embedding_restrict]
  have hmadd : v x < m • q := by
    change Multiplicative.ofAdd (OrderDual.toDual (v (z ^ m))) <
      Multiplicative.ofAdd (OrderDual.toDual (v x)) at hmval
    have hmdual : OrderDual.toDual (v (z ^ m)) <
        OrderDual.toDual (v x) := by simpa using hmval
    have hmadd' : v x < v (z ^ m) := (OrderDual.toDual_lt).mp hmdual
    simpa [hzq, v.map_pow] using hmadd'
  have hmle : m ≤ 2 ^ m := Nat.lt_two_pow_self.le
  exact ⟨m, hmadd.le.trans (nsmul_le_nsmul_left hq.le hmle)⟩

private theorem section06_hensel_cauchy_of_top {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ)
    (hcomplete : Chapter09NonarchimedeanComplete v)
    (u : ℕ → K) (q₀ : Γ) (hq₀ : 0 < q₀)
    (htop : ∀ γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass v.toValuation))ˣ,
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (OrderDual.ofDual (Multiplicative.toAdd
          (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)) + q₀) ≤
          v (u (n + 1) - u n)) :
      @CauchySeq K ℕ (Chapter09ValuationUniformSpace v) inferInstance u := by
  have _hcomplete := hcomplete
  let hvalued : Valued K (Multiplicative Γᵒᵈ) := Valued.mk' v.toValuation
  let hfoo (γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass v.toValuation))ˣ) : Γ :=
    OrderDual.ofDual (Multiplicative.toAdd
      (MonoidWithZeroHom.ValueGroup₀.embedding γ.1))
  have hval_lt_iff (x : K)
      (γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass v.toValuation))ˣ) :
      (v.toValuation.restrict x < γ.1) ↔ hfoo γ < v x := by
    rw [Valuation.restrict_lt_iff_lt_embedding]
    change Multiplicative.ofAdd (OrderDual.toDual (v x)) <
      MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ↔ _
    change OrderDual.toDual (v x) < Multiplicative.toAdd
      (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) ↔ _
    change _ ↔ OrderDual.ofDual (Multiplicative.toAdd
      (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)) < v x
    exact OrderDual.toDual_lt
  have hpair : ∀ (b : Γ) {m n : ℕ}, m ≤ n →
      (∀ i : ℕ, m ≤ i → i < n → b ≤ v (u (i + 1) - u i)) →
      b ≤ v (u n - u m) := by
    intro b m n hmn
    induction n, hmn using Nat.le_induction with
    | base =>
        intro hinc
        simp
    | succ n hmn ih =>
        intro hinc
        have hi := hinc n hmn (by omega)
        have ih' := ih (fun i hi' hlt =>
          hinc i hi' (lt_trans hlt (Nat.lt_succ_self n)))
        have hsum : u (n + 1) - u m =
            (u (n + 1) - u n) + (u n - u m) := by ring
        rw [hsum]
        exact (le_min hi ih').trans (valuation_strong_triangle v _ _)
  have htest : ∀ (γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass v.toValuation))ˣ),
      ∃ M ∈ (Filter.map u Filter.atTop),
        ∀ᵉ (x ∈ M) (y ∈ M), v.toValuation.restrict (y - x) < γ.1 := by
    intro γ
    let t : Γ := hfoo γ
    obtain ⟨N, hN⟩ := htop γ
    refine ⟨u '' Set.Ici N, ?_, ?_⟩
    · rw [Filter.mem_map']
      exact Filter.mem_of_superset (Filter.eventually_ge_atTop N)
        (fun n hn => ⟨n, hn, rfl⟩)
    · intro x hx y hy
      rcases hx with ⟨m, hm, rfl⟩
      rcases hy with ⟨n, hn, rfl⟩
      rcases le_total m n with hmn | hnm
      · have hinc : ∀ i : ℕ, m ≤ i → i < n →
            t + q₀ ≤ v (u (i + 1) - u i) := by
          intro i hi _
          exact hN i (le_trans hm hi)
        have hdiff := hpair (t + q₀) hmn hinc
        have ht_top : t ≠ ⊤ := by
          intro htop
          change OrderDual.ofDual (Multiplicative.toAdd
            (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)) = (⊤ : Γ) at htop
          have hdual : Multiplicative.toAdd
              (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) = (⊥ : Γᵒᵈ) :=
            (OrderDual.ofDual_eq_top Γ).mp htop
          have heq : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 = 0 :=
            congrArg Multiplicative.ofAdd hdual
          have hγzero : (γ.1 : MonoidWithZeroHom.ValueGroup₀ (.ofClass v.toValuation)) = 0 := by
            apply MonoidWithZeroHom.ValueGroup₀.embedding_injective
            exact heq
          exact (Units.ne_zero γ) hγzero
        have ht : t < t + q₀ := by
          simpa using (add_lt_add_iff_right_of_ne_top ht_top).2 hq₀
        apply hval_lt_iff _ γ |>.mpr
        exact lt_of_lt_of_le ht hdiff
      · have hinc : ∀ i : ℕ, n ≤ i → i < m →
            t + q₀ ≤ v (u (i + 1) - u i) := by
          intro i hi _
          exact hN i (le_trans hn hi)
        have hdiff := hpair (t + q₀) hnm hinc
        have ht_top : t ≠ ⊤ := by
          intro htop
          change OrderDual.ofDual (Multiplicative.toAdd
            (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)) = (⊤ : Γ) at htop
          have hdual : Multiplicative.toAdd
              (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) = (⊥ : Γᵒᵈ) :=
            (OrderDual.ofDual_eq_top Γ).mp htop
          have heq : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 = 0 :=
            congrArg Multiplicative.ofAdd hdual
          have hγzero : (γ.1 : MonoidWithZeroHom.ValueGroup₀ (.ofClass v.toValuation)) = 0 := by
            apply MonoidWithZeroHom.ValueGroup₀.embedding_injective
            exact heq
          exact (Units.ne_zero γ) hγzero
        have ht : t < t + q₀ := by
          simpa using (add_lt_add_iff_right_of_ne_top ht_top).2 hq₀
        apply hval_lt_iff _ γ |>.mpr
        have hneg : v (u n - u m) = v (u m - u n) := by
          rw [show u n - u m = -(u m - u n) by ring, v.map_neg]
        exact lt_of_lt_of_le ht (hneg ▸ hdiff)
  change Cauchy (Filter.map u Filter.atTop)
  rw [@Valued.cauchy_iff K _ (Multiplicative Γᵒᵈ) _ hvalued]
  refine ⟨inferInstance, ?_⟩
  intro γ
  exact htest γ

private theorem section06_coprime_correction_property {R : Type*} [CommRing R]
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

private theorem section06_correction_terms_mem_of_ideal
    {A : Type*} [CommRing A] [IsLocalRing A]
    (J : Ideal A) (hJ : J ≤ IsLocalRing.maximalIdeal A)
    {g h r s t : A[X]} (hg : g.Monic) (hh : h.Monic)
    (hcop : IsCoprime g h) (hrdeg : r.degree < g.degree)
    (hsdeg : s.degree < h.degree)
    (heq : factorizationCorrectionMap g h (r, s) = t)
    (ht : PolynomialCoefficientsInIdeal J t) :
    PolynomialCoefficientsInIdeal J r ∧
      PolynomialCoefficientsInIdeal J s := by
  have hJ_ne_top : J ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal A).ne_top hJ
  let φ : A →+* (A ⧸ J) := Ideal.Quotient.mk J
  have hquot_nontrivial : Nontrivial (A ⧸ J) :=
    Ideal.Quotient.nontrivial_iff.mpr hJ_ne_top
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
    section06_coprime_correction_property hgmap hhmap hcopmap
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
    have hi := congrArg (fun P : Polynomial (A ⧸ J) => P.coeff i) hrmap_zero
    have hi' : φ (r.coeff i) = 0 := by
      simpa only [Polynomial.coeff_map, coeff_zero] using hi
    exact Ideal.Quotient.eq_zero_iff_mem.mp hi'
  · intro i
    have hi := congrArg (fun P : Polynomial (A ⧸ J) => P.coeff i) hsmap_zero
    have hi' : φ (s.coeff i) = 0 := by
      simpa only [Polynomial.coeff_map, coeff_zero] using hi
    exact Ideal.Quotient.eq_zero_iff_mem.mp hi'

/-- A complete rank-one valued field has the book's factorization-form
henselianity.  This is the remaining metric factorization theorem for Chapter
9; unlike the former generic simple-root-to-factorization stub, its proof can
be developed entirely from the approximation machinery of this chapter. -/
theorem complete_valued_field_is_henselian
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ)
    [Valuation.RankOne vK]
    (hcomplete : @CompleteSpace K (Valued.mk' vK).toUniformSpace) :
    IsHenselianLocalRingChapter09 vK.valuationSubring := by
  intro f g₀ h₀ hf hg₀ hh₀ hcop hred
  let v : AddValuation K (Additive Γ)ᵒᵈ := Valuation.toAddValuation vK
  have hv_equiv : vK.IsEquiv v.toValuation := by
    rw [Valuation.isEquiv_iff_val_le_one]
    intro x
    rfl
  let hrank : Valuation.RankOne v.toValuation :=
    { hom' := (Valuation.RankOne.hom vK).comp
        hv_equiv.orderMonoidIso.symm.toMonoidWithZeroHom
      strictMono' := (Valuation.RankOne.strictMono vK).comp
        hv_equiv.orderMonoidIso.symm.strictMono
      exists_val_nontrivial := by
        obtain ⟨r, hr0, hr1⟩ := Valuation.RankOne.nontrivial vK
        refine ⟨r, ?_, ?_⟩
        · intro hr
          exact hr0 ((hv_equiv.eq_zero).mpr hr)
        · intro hr
          exact hr1 ((hv_equiv.eq_one_iff_eq_one).mpr hr) }
  let _ : Valuation.RankOne v.toValuation := hrank
  have hA : IsValuationSubring vK.valuationSubring.toSubring v := by
    intro x
    change x ∈ vK.valuationSubring ↔ v x ≥ 0
    rw [Valuation.mem_valuationSubring_iff]
    rfl
  have hcomplete' : Chapter09NonarchimedeanComplete v := by
    have hforward : @UniformContinuous K K
        (Valued.mk' vK).toUniformSpace (Valued.mk' v.toValuation).toUniformSpace
        (id : K → K) := hv_equiv.symm.uniformContinuous
    have hback : @UniformContinuous K K
        (Valued.mk' v.toValuation).toUniformSpace (Valued.mk' vK).toUniformSpace
        (id : K → K) := hv_equiv.uniformContinuous
    have hind : @IsUniformInducing K K
        (Valued.mk' vK).toUniformSpace (Valued.mk' v.toValuation).toUniformSpace
        (id : K → K) :=
      @IsUniformInducing.of_comp K K K
        (Valued.mk' vK).toUniformSpace
        (Valued.mk' v.toValuation).toUniformSpace
        (Valued.mk' vK).toUniformSpace
        (id : K → K) (id : K → K) hforward hback
        (@IsUniformInducing.id K (Valued.mk' vK).toUniformSpace)
    have hc : @CompleteSpace K (Valued.mk' v.toValuation).toUniformSpace :=
      (@IsUniformInducing.completeSpace_congr K K
        (Valued.mk' vK).toUniformSpace (Valued.mk' v.toValuation).toUniformSpace
        (id : K → K) hind (Function.surjective_id)).mp hcomplete
    exact hc
  have hg0_lifts : g₀ ∈ Polynomial.lifts (residueMap vK.valuationSubring) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact Ideal.Quotient.mk_surjective (g₀.coeff n)
  have hh0_lifts : h₀ ∈ Polynomial.lifts (residueMap vK.valuationSubring) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact Ideal.Quotient.mk_surjective (h₀.coeff n)
  by_cases hg0deg : g₀.natDegree = 0
  · have hg01 : g₀ = 1 := hg₀.natDegree_eq_zero.mp hg0deg
    have hredh : residuePolynomial f = h₀ := by simpa [hg01] using hred
    have hfdeg : f.natDegree = h₀.natDegree := by
      calc
        f.natDegree = (residuePolynomial f).natDegree :=
          (hf.natDegree_map (residueMap vK.valuationSubring)).symm
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
            (hf.natDegree_map (residueMap vK.valuationSubring)).symm
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
    · obtain ⟨g₁, hmapg₁, hdeg₁, hg₁⟩ :=
        Polynomial.lifts_and_natDegree_eq_and_monic hg0_lifts hg₀
      obtain ⟨h₁, hmaph₁, hdeh₁, hh₁⟩ :=
        Polynomial.lifts_and_natDegree_eq_and_monic hh0_lifts hh₀
      have hredg₁ : residuePolynomial g₁ = g₀ := hmapg₁
      have hredh₁ : residuePolynomial h₁ = h₀ := hmaph₁
      have hdeg_f : f.natDegree = (g₁ * h₁).natDegree := by
        calc
          f.natDegree = (residuePolynomial f).natDegree :=
            (hf.natDegree_map (residueMap vK.valuationSubring)).symm
          _ = (g₀ * h₀).natDegree := congrArg Polynomial.natDegree hred
          _ = (g₁ * h₁).natDegree := by
            rw [hg₀.natDegree_mul hh₀, hg₁.natDegree_mul hh₁, hdeg₁, hdeh₁]
      have hcop₁ : IsCoprime g₁ h₁ := by
        have hg₀' : g₀.Monic := by
          rw [← hredg₁]
          exact hg₁.map (residueMap vK.valuationSubring)
        have hh₀' : h₀.Monic := by
          rw [← hredh₁]
          exact hh₁.map (residueMap vK.valuationSubring)
        apply (Polynomial.isUnit_resultant_iff_isCoprime hg₁).mp
        apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
        change residueMap vK.valuationSubring (Polynomial.resultant g₁ h₁) ≠ 0
        have hdeg_g : g₀.natDegree = g₁.natDegree := by
          rw [← hredg₁]
          exact hg₁.natDegree_map (residueMap vK.valuationSubring)
        have hdeg_h : h₀.natDegree = h₁.natDegree := by
          rw [← hredh₁]
          exact hh₁.natDegree_map (residueMap vK.valuationSubring)
        have hres : IsUnit (Polynomial.resultant g₀ h₀) :=
          (Polynomial.isUnit_resultant_iff_isCoprime hg₀').mpr hcop
        rw [← Polynomial.resultant_map_map]
        have hredg₁' : Polynomial.map (residueMap vK.valuationSubring) g₁ = g₀ :=
          hredg₁
        have hredh₁' : Polynomial.map (residueMap vK.valuationSubring) h₁ = h₀ :=
          hredh₁
        rw [hredg₁', hredh₁', ← hdeg_g, ← hdeg_h]
        exact hres.ne_zero
      have hcop_lift : ∀ (G H : vK.valuationSubring[X]), G.Monic → H.Monic →
          residuePolynomial G = g₀ → residuePolynomial H = h₀ → IsCoprime G H := by
        intro G H hG hH hGred hHred
        have hG₀ : g₀.Monic := by
          rw [← hGred]
          exact hG.map (residueMap vK.valuationSubring)
        have hH₀ : h₀.Monic := by
          rw [← hHred]
          exact hH.map (residueMap vK.valuationSubring)
        apply (Polynomial.isUnit_resultant_iff_isCoprime hG).mp
        apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
        change residueMap vK.valuationSubring (Polynomial.resultant G H) ≠ 0
        have hdeg_G : g₀.natDegree = G.natDegree := by
          rw [← hGred]
          exact hG.natDegree_map (residueMap vK.valuationSubring)
        have hdeg_H : h₀.natDegree = H.natDegree := by
          rw [← hHred]
          exact hH.natDegree_map (residueMap vK.valuationSubring)
        have hres : IsUnit (Polynomial.resultant g₀ h₀) :=
          (Polynomial.isUnit_resultant_iff_isCoprime hG₀).mpr hcop
        rw [← Polynomial.resultant_map_map]
        have hGred' : Polynomial.map (residueMap vK.valuationSubring) G = g₀ := hGred
        have hHred' : Polynomial.map (residueMap vK.valuationSubring) H = h₀ := hHred
        rw [hGred', hHred', ← hdeg_G, ← hdeg_H]
        exact hres.ne_zero
      let hv_approx (g h : vK.valuationSubring[X])
          (q : (Additive Γ)ᵒᵈ) : Prop :=
        ∀ i : ℕ, q ≤ v ((f - g * h).coeff i : K)
      let hvalue_ideal (q : (Additive Γ)ᵒᵈ) (hq : 0 < q) :
          Ideal vK.valuationSubring := by
        refine {
          carrier := {a : vK.valuationSubring | q ≤ v (a : K)}
          add_mem' := ?_
          zero_mem' := ?_
          smul_mem' := ?_ }
        · intro a b ha hb
          have hmin : q ≤ min (v (a : K)) (v (b : K)) := le_min ha hb
          have hsum : min (v (a : K)) (v (b : K)) ≤
              v ((a : K) + (b : K)) := valuation_strong_triangle v (a : K) (b : K)
          exact hmin.trans hsum
        · simp
        · intro a b hb
          have ha : 0 ≤ v (a : K) := (hA _).mp a.property
          rw [show (a • b : vK.valuationSubring) = a * b by rfl]
          change q ≤ v ((a : K) * (b : K))
          rw [v.map_mul]
          have hmul : v (b : K) ≤ v (b : K) + v (a : K) := by
            simpa using add_le_add_right ha (v (b : K))
          calc
            q ≤ v (b : K) := hb
            _ ≤ v (a : K) + v (b : K) := by simpa [add_comm] using hmul
      have hlower_bound (p : vK.valuationSubring[X])
          (hp : ∀ i : ℕ, p.coeff i ∈ IsLocalRing.maximalIdeal vK.valuationSubring)
          (hp0 : p ≠ 0) :
          ∃ q : (Additive Γ)ᵒᵈ, 0 < q ∧
            (∃ z : K, z ≠ 0 ∧ v z = q) ∧
            ∀ i : ℕ, q ≤ v ((p.coeff i : K)) := by
        let S : Finset ((Additive Γ)ᵒᵈ) :=
          p.support.image (fun i => v ((p.coeff i : vK.valuationSubring) : K))
        have hS : S.Nonempty := by
          exact (Polynomial.support_nonempty.mpr hp0).image _
        let q : (Additive Γ)ᵒᵈ := S.min' hS
        have hqmem : q ∈ S := Finset.min'_mem S hS
        obtain ⟨j, hj, hqj⟩ := Finset.mem_image.mp hqmem
        refine ⟨q, ?_, ?_, ?_⟩
        · rw [← hqj]
          have hj0 : p.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
          have hjlt : vK ((p.coeff j : vK.valuationSubring) : K) < 1 :=
            (Valuation.mem_maximalIdeal_iff (v := vK)).mp (hp j)
          change 0 < OrderDual.toDual (Additive.ofMul
            (vK ((p.coeff j : vK.valuationSubring) : K)))
          exact hjlt
        · refine ⟨(p.coeff j : K), ?_, hqj⟩
          have hj0 : p.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
          exact_mod_cast hj0
        · intro i
          by_cases hi : i ∈ p.support
          · exact Finset.min'_le S _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
          · have hi0 : p.coeff i = 0 := by
              apply Classical.byContradiction
              intro hi0
              exact hi (Polynomial.mem_support_iff.mpr hi0)
            rw [hi0]
            simp
      have hsum_lower : ∀ (b : (Additive Γ)ᵒᵈ) (s : Finset (ℕ × ℕ))
          (a : (ℕ × ℕ) → K), (∀ i ∈ s, b ≤ v (a i)) →
          b ≤ v (∑ i ∈ s, a i) := by
        intro b s
        induction s using Finset.induction_on with
        | empty =>
            intro a ha
            simp
        | @insert i s hi ih =>
            intro a ha
            rw [Finset.sum_insert hi]
            have hfirst : b ≤ v (a i) := ha i (Finset.mem_insert_self i s)
            have hrest : b ≤ v (∑ x ∈ s, a x) := by
              apply ih
              intro j hj
              exact ha j (Finset.mem_insert_of_mem hj)
            exact (le_min hfirst hrest).trans (valuation_strong_triangle v _ _)
      have hmaximal_le (q : (Additive Γ)ᵒᵈ) (hq : 0 < q)
          (J : Ideal vK.valuationSubring) (hJ : J = hvalue_ideal q hq) :
          J ≤ IsLocalRing.maximalIdeal vK.valuationSubring := by
        intro a ha
        have haq : q ≤ v (a : K) := by
          rw [hJ] at ha
          simpa [hvalue_ideal] using ha
        by_cases ha0 : a = 0
        · simp [ha0]
        · rw [Valuation.mem_maximalIdeal_iff]
          change 0 < OrderDual.toDual (Additive.ofMul
            (vK (a : K)))
          exact lt_of_lt_of_le hq haq
      have herror_mem_max : ∀ i : ℕ,
          (f - g₁ * h₁).coeff i ∈ IsLocalRing.maximalIdeal vK.valuationSubring := by
        intro i
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        change residueMap vK.valuationSubring ((f - g₁ * h₁).coeff i) = 0
        have hzero : residuePolynomial f - residuePolynomial (g₁ * h₁) = 0 := by
          rw [hred, ← hredg₁, ← hredh₁]
          simp [residuePolynomial, Polynomial.map_mul]
        simpa only [residuePolynomial, Polynomial.coeff_sub, Polynomial.coeff_map,
          map_zero, coeff_zero, map_sub] using congrArg (fun p => p.coeff i) hzero
      have hExists : ∃ gh : vK.valuationSubring[X] × vK.valuationSubring[X],
          IsFactorizationLift f g₀ h₀ gh.1 gh.2 := by
        by_cases hzero : f - g₁ * h₁ = 0
        · refine ⟨(g₁, h₁), ?_⟩
          exact ⟨hg₁, hh₁, hdeg₁, hdeh₁, hredg₁, hredh₁,
            sub_eq_zero.mp hzero⟩
        · obtain ⟨q₀, hq₀, hq₀rep, hq₀coeff⟩ :=
            hlower_bound (f - g₁ * h₁) herror_mem_max hzero
          have hq₀image : q₀ ≠ ⊤ → ∃ z : K, z ≠ 0 ∧ v z = q₀ :=
            fun _ => hq₀rep
          have hcofinal := section06_rank_one_image_doubling_cofinal v q₀ hq₀ hq₀image
          let LiftAt : ℕ →
              (vK.valuationSubring[X] × vK.valuationSubring[X]) → Prop :=
            fun n gh => gh.1.Monic ∧ gh.2.Monic ∧
              gh.1.natDegree = g₀.natDegree ∧ gh.2.natDegree = h₀.natDegree ∧
              residuePolynomial gh.1 = g₀ ∧ residuePolynomial gh.2 = h₀ ∧
              hv_approx gh.1 gh.2 ((2 ^ n) • q₀)
          let Q : ℕ → Type _ := fun n =>
            {gh : vK.valuationSubring[X] × vK.valuationSubring[X] // LiftAt n gh}
          have hQ0 : Q 0 := by
            refine ⟨(g₁, h₁), hg₁, hh₁, hdeg₁, hdeh₁, hredg₁, hredh₁, ?_⟩
            simpa [hv_approx] using hq₀coeff
          have hfactorChoice : ∀ n (qn : Q n), ∃ r s : vK.valuationSubring[X],
              r.degree < qn.1.1.degree ∧ s.degree < qn.1.2.degree ∧
              (∀ i : ℕ, ((2 ^ n) • q₀) ≤ v ((r.coeff i : K))) ∧
              (∀ i : ℕ, ((2 ^ n) • q₀) ≤ v ((s.coeff i : K))) ∧
              hv_approx (qn.1.1 + r) (qn.1.2 + s) ((2 ^ (n + 1)) • q₀) := by
            intro n qn
            rcases qn.property with ⟨hg, hh, hgd, hhd, hrg, hrh, happrox⟩
            let qnval : (Additive Γ)ᵒᵈ := (2 ^ n) • q₀
            have hqnpos : 0 < qnval := by
              dsimp [qnval]
              exact nsmul_pos hq₀ (by positivity)
            let J : Ideal vK.valuationSubring := hvalue_ideal qnval hqnpos
            have hJle : J ≤ IsLocalRing.maximalIdeal vK.valuationSubring :=
              hmaximal_le qnval hqnpos J rfl
            have hEdeg : (f - qn.1.1 * qn.1.2).degree <
                (qn.1.1 * qn.1.2).degree := by
              apply Polynomial.degree_sub_lt_right
              · calc
                  f.degree = (f.natDegree : WithBot ℕ) :=
                    Polynomial.degree_eq_natDegree hf.ne_zero
                  _ = ((qn.1.1 * qn.1.2).natDegree : WithBot ℕ) := by
                    rw [hdeg_f, hg₁.natDegree_mul hh₁, hg.natDegree_mul hh,
                      hdeg₁, hdeh₁, hgd, hhd]
                  _ = (qn.1.1 * qn.1.2).degree :=
                    (Polynomial.degree_eq_natDegree (hg.mul hh).ne_zero).symm
              · exact (hg.mul hh).ne_zero
              · rw [hf.leadingCoeff, (hg.mul hh).leadingCoeff]
            obtain ⟨⟨r, s⟩, hprop, _⟩ :=
              section06_coprime_correction_property hg hh
                (hcop_lift qn.1.1 qn.1.2 hg hh hrg hrh)
                (f - qn.1.1 * qn.1.2) hEdeg
            rcases hprop with ⟨hrdeg, hsdeg, hcorr⟩
            change r.degree < qn.1.1.degree at hrdeg
            change s.degree < qn.1.2.degree at hsdeg
            have hT : PolynomialCoefficientsInIdeal J
                (f - qn.1.1 * qn.1.2) := by
              intro i
              simpa [J, hvalue_ideal, qnval] using happrox i
            have hterms := section06_correction_terms_mem_of_ideal J hJle
              hg hh (hcop_lift qn.1.1 qn.1.2 hg hh hrg hrh)
                hrdeg hsdeg hcorr hT
            have hrval : ∀ i : ℕ, qnval ≤ v ((r.coeff i : K)) := by
              intro i
              simpa [J, hvalue_ideal] using hterms.1 i
            have hsval : ∀ i : ℕ, qnval ≤ v ((s.coeff i : K)) := by
              intro i
              simpa [J, hvalue_ideal] using hterms.2 i
            have hnewerr : f - (qn.1.1 + r) * (qn.1.2 + s) = -(r * s) := by
              have hf_eq : f = (r * qn.1.2 + s * qn.1.1) + qn.1.1 * qn.1.2 :=
                eq_add_of_sub_eq hcorr.symm
              rw [hf_eq]
              ring
            have hprod (i : ℕ) : qnval + qnval ≤
                v (((r * s).coeff i : vK.valuationSubring) : K) := by
              rw [Polynomial.coeff_mul]
              have hsum := hsum_lower (b := qnval + qnval)
                (s := Finset.antidiagonal i)
                (a := fun x : ℕ × ℕ =>
                  ((r.coeff x.1 : vK.valuationSubring) : K) *
                    ((s.coeff x.2 : vK.valuationSubring) : K)) (by
                  intro x hx
                  rw [v.map_mul]
                  exact add_le_add (hrval x.1) (hsval x.2))
              norm_cast at hsum
            have hnext : hv_approx (qn.1.1 + r) (qn.1.2 + s)
                ((2 ^ (n + 1)) • q₀) := by
              intro i
              rw [hnewerr, Polynomial.coeff_neg]
              have hi := hprod i
              have hpow : (2 ^ (n + 1)) • q₀ =
                  (2 ^ n) • q₀ + (2 ^ n) • q₀ := by
                have htwo : 2 ^ n * 2 = 2 ^ n + 2 ^ n := by omega
                rw [pow_succ, htwo, add_nsmul]
              rw [hpow]
              simpa [map_neg, v.map_neg, qnval] using hi
            refine ⟨r, s, hrdeg, hsdeg, hrval, hsval, hnext⟩
          let StepData : ∀ n, Q n → Type _ := fun n qn =>
            {z : Q (n + 1) ×
                (vK.valuationSubring[X] × vK.valuationSubring[X]) //
              z.1.1.1 = qn.1.1 + z.2.1 ∧
                z.1.1.2 = qn.1.2 + z.2.2 ∧
                (∀ i : ℕ, ((2 ^ n) • q₀) ≤ v ((z.2.1.coeff i : K))) ∧
                (∀ i : ℕ, ((2 ^ n) • q₀) ≤ v ((z.2.2.coeff i : K)))}
          let stepData : ∀ n (qn : Q n), StepData n qn := fun n qn => by
            rcases qn.property with ⟨hg, hh, hgd, hhd, hrg, hrh, happrox⟩
            let hex := hfactorChoice n qn
            let r : vK.valuationSubring[X] := hex.choose
            let s : vK.valuationSubring[X] := hex.choose_spec.choose
            have hrdeg : r.degree < qn.1.1.degree :=
              hex.choose_spec.choose_spec.1
            have hsdeg : s.degree < qn.1.2.degree :=
              hex.choose_spec.choose_spec.2.1
            have hrval : ∀ i : ℕ, ((2 ^ n) • q₀) ≤ v ((r.coeff i : K)) :=
              hex.choose_spec.choose_spec.2.2.1
            have hsval : ∀ i : ℕ, ((2 ^ n) • q₀) ≤ v ((s.coeff i : K)) :=
              hex.choose_spec.choose_spec.2.2.2.1
            have hnext : hv_approx (qn.1.1 + r) (qn.1.2 + s)
                ((2 ^ (n + 1)) • q₀) :=
              hex.choose_spec.choose_spec.2.2.2.2
            have hg' : (qn.1.1 + r).Monic := hg.add_of_left hrdeg
            have hh' : (qn.1.2 + s).Monic := hh.add_of_left hsdeg
            have hgd' : (qn.1.1 + r).natDegree = g₀.natDegree :=
              (natDegree_add_eq_left_of_degree_lt hrdeg).trans hgd
            have hhd' : (qn.1.2 + s).natDegree = h₀.natDegree :=
              (natDegree_add_eq_left_of_degree_lt hsdeg).trans hhd
            have hqnpos : 0 < (2 ^ n) • q₀ := by
              exact nsmul_pos hq₀ (by positivity)
            let J : Ideal vK.valuationSubring :=
              hvalue_ideal ((2 ^ n) • q₀) hqnpos
            have hJle : J ≤ IsLocalRing.maximalIdeal vK.valuationSubring :=
              hmaximal_le ((2 ^ n) • q₀) hqnpos J rfl
            have hrzero : residuePolynomial r = 0 := by
              apply Polynomial.ext
              intro i
              have hi : r.coeff i ∈ IsLocalRing.maximalIdeal vK.valuationSubring :=
                hJle (by simpa [J, hvalue_ideal] using hrval i)
              have hi' : residueMap vK.valuationSubring (r.coeff i) = 0 :=
                Ideal.Quotient.eq_zero_iff_mem.mpr hi
              simpa only [residuePolynomial, Polynomial.coeff_map, coeff_zero] using hi'
            have hszero : residuePolynomial s = 0 := by
              apply Polynomial.ext
              intro i
              have hi : s.coeff i ∈ IsLocalRing.maximalIdeal vK.valuationSubring :=
                hJle (by simpa [J, hvalue_ideal] using hsval i)
              have hi' : residueMap vK.valuationSubring (s.coeff i) = 0 :=
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
            exact ⟨rfl, rfl, hrval, hsval⟩
          let q : ∀ n, Q n := fun n =>
            Nat.rec hQ0 (fun n qn => (stepData n qn).1.1) n
          have hqsucc (n : ℕ) : q (n + 1) = (stepData n (q n)).1.1 := by
            simp [q]
          have hqsucc_factor (n : ℕ) :
              ∃ r : vK.valuationSubring[X],
                (q (n + 1)).1.1 = (q n).1.1 + r ∧
                (∀ i : ℕ, ((2 ^ n) • q₀) ≤ v ((r.coeff i : K))) := by
            rw [hqsucc]
            exact ⟨(stepData n (q n)).1.2.1,
              (stepData n (q n)).2.1, (stepData n (q n)).2.2.2.1⟩
          have hqsucc_factor_h (n : ℕ) :
              ∃ s : vK.valuationSubring[X],
                (q (n + 1)).1.2 = (q n).1.2 + s ∧
                (∀ i : ℕ, ((2 ^ n) • q₀) ≤ v ((s.coeff i : K))) := by
            rw [hqsucc]
            exact ⟨(stepData n (q n)).1.2.2,
              (stepData n (q n)).2.2.1, (stepData n (q n)).2.2.2.2⟩
          have himage_add_sub : ∀ {r₁ r₂ r₃ : (Additive Γ)ᵒᵈ},
              (∃ x : K, x ≠ 0 ∧ v x = r₁) →
              (∃ y : K, y ≠ 0 ∧ v y = r₂) →
              (∃ z : K, z ≠ 0 ∧ v z = r₃) →
              ∃ w : K, w ≠ 0 ∧ v w = r₁ + r₂ - r₃ := by
            intro r₁ r₂ r₃ hx hy hz
            rcases hx with ⟨x, hx0, hxr⟩
            rcases hy with ⟨y, hy0, hyr⟩
            rcases hz with ⟨z, hz0, hzr⟩
            refine ⟨x * y * z⁻¹, by simp [hx0, hy0, hz0], ?_⟩
            rw [v.map_mul, v.map_mul, v.map_inv, hxr, hyr, hzr]
            simp [sub_eq_add_neg, add_assoc]
          let G := MonoidWithZeroHom.ValueGroup₀ (.ofClass v.toValuation)
          let hfoo (γ : Gˣ) : (Additive Γ)ᵒᵈ :=
            OrderDual.ofDual (Multiplicative.toAdd
              (MonoidWithZeroHom.ValueGroup₀.embedding γ.1))
          have hval_lt_iff (x : K) (γ : Gˣ) :
              (v.toValuation.restrict x < γ.1) ↔ hfoo γ < v x := by
            rw [Valuation.restrict_lt_iff_lt_embedding]
            change Multiplicative.ofAdd (OrderDual.toDual (v x)) <
              MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ↔ _
            change OrderDual.toDual (v x) < Multiplicative.toAdd
              (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) ↔ _
            change _ ↔ OrderDual.ofDual (Multiplicative.toAdd
              (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)) < v x
            exact OrderDual.toDual_lt
          have hfoo_image (γ : Gˣ) :
              ∃ x : K, x ≠ 0 ∧ v x = hfoo γ := by
            obtain ⟨x, hx⟩ :=
              MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective
                (.ofClass v.toValuation) γ.1
            have hx0 : x ≠ 0 := by
              intro hx0
              have hzero :
                  (γ.1 : MonoidWithZeroHom.ValueGroup₀ (.ofClass v.toValuation)) = 0 := by
                simpa [hx0] using hx.symm
              exact (Units.ne_zero γ) hzero
            refine ⟨x, hx0, ?_⟩
            have hxeq : v.toValuation x =
                MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
              calc
                v.toValuation x =
                    MonoidWithZeroHom.ValueGroup₀.embedding
                      (v.toValuation.restrict x) :=
                  (Valuation.embedding_restrict v.toValuation x).symm
                _ = MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
                  rw [Valuation.restrict_def, hx]
            simpa [hfoo, AddValuation.toValuation_apply] using congrArg
              (fun z : Multiplicative ((Additive Γ)ᵒᵈ)ᵒᵈ =>
                OrderDual.ofDual (Multiplicative.toAdd z)) hxeq
          have hpair : ∀ (u : ℕ → K) (b : (Additive Γ)ᵒᵈ)
              {m n : ℕ}, m ≤ n →
              (∀ i : ℕ, m ≤ i → i < n → b ≤ v (u (i + 1) - u i)) →
              b ≤ v (u n - u m) := by
            intro u b m n hmn
            induction n, hmn using Nat.le_induction with
            | base =>
                intro hinc
                simp
            | succ n hmn ih =>
                intro hinc
                have hi := hinc n hmn (by omega)
                have ih' := ih (fun i hi' hlt =>
                  hinc i hi' (lt_trans hlt (Nat.lt_succ_self n)))
                have hsum : u (n + 1) - u m =
                    (u (n + 1) - u n) + (u n - u m) := by ring
                rw [hsum]
                exact (le_min hi ih').trans (valuation_strong_triangle v _ _)
          let _ : UniformSpace K := Chapter09ValuationUniformSpace v
          have hlimit_of_steps : ∀ (u : ℕ → K),
              (∀ n : ℕ, ((2 ^ n) • q₀) ≤ v (u (n + 1) - u n)) →
              ∃ L : K, Filter.Tendsto u Filter.atTop (nhds L) ∧
                (∀ n : ℕ, ((2 ^ n) • q₀) ≤ v (u n - L)) := by
            intro u hstep
            let hvalued : Valued K (Multiplicative ((Additive Γ)ᵒᵈ)ᵒᵈ) :=
              Valued.mk' v.toValuation
            have htop : ∀ γ : Gˣ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
                hfoo γ + q₀ ≤ v (u (n + 1) - u n) := by
              intro γ
              obtain ⟨N, hN⟩ := hcofinal (hfoo γ + q₀) (by
                simpa using (himage_add_sub (r₃ := 0) (hfoo_image γ) hq₀rep
                  ⟨1, one_ne_zero, by simp⟩))
              refine ⟨N, fun n hn => ?_⟩
              have hpow : 2 ^ N ≤ 2 ^ n :=
                Nat.pow_le_pow_right (by norm_num) hn
              have hsmul : (2 ^ N) • q₀ ≤ (2 ^ n) • q₀ :=
                nsmul_le_nsmul_left hq₀.le hpow
              exact hN.trans (hsmul.trans (hstep n))
            have hCauchy : @CauchySeq K ℕ
                (Chapter09ValuationUniformSpace v) inferInstance u :=
              section06_hensel_cauchy_of_top v hcomplete' u q₀ hq₀ htop
            obtain ⟨L, hlim⟩ := @cauchySeq_tendsto_of_complete K ℕ
              (Chapter09ValuationUniformSpace v) inferInstance hcomplete'
              (u := u) hCauchy
            have hdiff_lim : Filter.Tendsto (fun m : ℕ => u m - L)
                Filter.atTop (nhds (0 : K)) := by
              have h := hlim.sub (tendsto_const_nhds :
                Filter.Tendsto (fun _ : ℕ => L) Filter.atTop (nhds L))
              simpa using h
            have hpowtop : ∀ j : ℕ,
                (2 ^ j) • (⊤ : (Additive Γ)ᵒᵈ) = ⊤ := by
              intro j
              induction j with
              | zero => simp
              | succ j ih =>
                  rw [pow_succ, show 2 ^ j * 2 = 2 ^ j + 2 ^ j by omega,
                    add_nsmul, ih]
                  simp
            have hbound : ∀ n : ℕ, ((2 ^ n) • q₀) ≤ v (u n - L) := by
              by_cases hqtop : q₀ = (⊤ : (Additive Γ)ᵒᵈ)
              · have huconst : ∀ n : ℕ, u n = u 0 := by
                  intro n
                  induction n with
                  | zero => rfl
                  | succ n ih =>
                      have hn := hstep n
                      have hzero : u (n + 1) - u n = 0 := by
                        apply (AddValuation.top_iff v).mp
                        apply top_unique
                        rw [hqtop, hpowtop n] at hn
                        exact hn
                      rw [sub_eq_zero] at hzero
                      exact hzero.trans ih
                have hL : L = u 0 := by
                  have hlim' : Filter.Tendsto (fun _ : ℕ => u 0)
                      Filter.atTop (nhds L) := by
                    have hu : u = (fun _ : ℕ => u 0) := funext huconst
                    rw [← hu]
                    exact hlim
                  exact tendsto_nhds_unique hlim' tendsto_const_nhds
                intro n
                rw [hqtop, huconst n, hL]
                simp
              · intro n
                obtain ⟨z₀, hz₀, hzq₀⟩ := hq₀rep
                let z : K := z₀ ^ (2 ^ n)
                have hz : z ≠ 0 := pow_ne_zero _ hz₀
                have hzval : v z = (2 ^ n) • q₀ := by
                  rw [v.map_pow, hzq₀]
                let ξ : Gˣ := Units.mk0 (v.toValuation.restrict z)
                  (v.toValuation.restrict.ne_zero_iff.mpr hz)
                have hξ : hfoo ξ = (2 ^ n) • q₀ := by
                  have hxeq : v.toValuation z =
                      MonoidWithZeroHom.ValueGroup₀.embedding ξ.1 := by
                    exact (Valuation.embedding_restrict v.toValuation z).symm
                  have hh := congrArg
                    (fun w : Multiplicative ((Additive Γ)ᵒᵈ)ᵒᵈ =>
                      OrderDual.ofDual (Multiplicative.toAdd w)) hxeq
                  simpa [hfoo, hzval, AddValuation.toValuation_apply] using hh.symm
                have hev : ∀ᶠ m : ℕ in Filter.atTop,
                    v.toValuation.restrict (u m - L) < ξ.1 := by
                  have hdiff_lim' := hdiff_lim
                  rw [(@Valued.hasBasis_nhds_zero K _
                    (Multiplicative ((Additive Γ)ᵒᵈ)ᵒᵈ) _ hvalued).tendsto_right_iff]
                    at hdiff_lim'
                  exact hdiff_lim' ξ trivial
                have hev' : ∀ᶠ m : ℕ in Filter.atTop,
                    ((2 ^ n) • q₀) < v (u m - L) := by
                  filter_upwards [hev] with m hm
                  rw [← hξ]
                  exact (hval_lt_iff (u m - L) ξ).mp hm
                obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hev'
                let k := max n M
                have hnk : n ≤ k := le_max_left _ _
                have hMk : M ≤ k := le_max_right _ _
                have hinc : ∀ i : ℕ, n ≤ i → i < k →
                    ((2 ^ n) • q₀) ≤ v (u (i + 1) - u i) := by
                  intro i hi _
                  have hpow : 2 ^ n ≤ 2 ^ i :=
                    Nat.pow_le_pow_right (by norm_num) hi
                  exact (nsmul_le_nsmul_left hq₀.le hpow).trans (hstep i)
                have hdiff := hpair u ((2 ^ n) • q₀) hnk hinc
                have htail : ((2 ^ n) • q₀) ≤ v (u k - L) :=
                  le_of_lt (hM k hMk)
                have hsum : u n - L = (u n - u k) + (u k - L) := by ring
                rw [hsum]
                have hdiff' : ((2 ^ n) • q₀) ≤ v (u n - u k) := by
                  rw [show u n - u k = -(u k - u n) by ring, v.map_neg]
                  exact hdiff
                exact (le_min hdiff' htail).trans
                  (valuation_strong_triangle v _ _)
            exact ⟨L, hlim, hbound⟩
          have hlimit_mem (u : ℕ → K) (hu : ∀ n : ℕ,
              u n ∈ vK.valuationSubring) (L : K)
              (hlim : Filter.Tendsto u Filter.atTop (nhds L)) :
              L ∈ vK.valuationSubring := by
            apply (hA _).mpr
            by_contra hnot
            have hneg : v L < 0 := lt_of_not_ge hnot
            let hvalued : Valued K (Multiplicative ((Additive Γ)ᵒᵈ)ᵒᵈ) :=
              Valued.mk' v.toValuation
            have hLval : v.toValuation L ≠ 0 := by
              intro hz
              have hz' : v L = ⊤ := by
                change Multiplicative.ofAdd (OrderDual.toDual (v L)) = 0 at hz
                have hzdual : OrderDual.toDual (v L) =
                    (⊥ : ((Additive Γ)ᵒᵈ)ᵒᵈ) := by
                  exact congrArg Multiplicative.toAdd hz
                exact (OrderDual.toDual_eq_bot ((Additive Γ)ᵒᵈ)).mp hzdual
              exact (not_lt_of_ge (le_top : (0 : (Additive Γ)ᵒᵈ) ≤ ⊤))
                (hz' ▸ hneg)
            have hloc := @Valued.locally_const K _
              (Multiplicative ((Additive Γ)ᵒᵈ)ᵒᵈ) _ hvalued L hLval
            have hev : ∀ᶠ n : ℕ in Filter.atTop,
                v.toValuation (u n) = v.toValuation L := hlim.eventually hloc
            obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
            have hEq := hN N (le_rfl)
            have hEq' : v (u N) = v L := by
              have hh := congrArg
                (fun z : Multiplicative ((Additive Γ)ᵒᵈ)ᵒᵈ =>
                  OrderDual.ofDual (Multiplicative.toAdd z)) hEq
              simpa [AddValuation.toValuation_apply] using hh
            have hnonneg : 0 ≤ v (u N) := (hA _).mp (hu N)
            exact (not_lt_of_ge (hEq' ▸ hnonneg)) hneg
          have hstep_g (d n : ℕ) :
              ((2 ^ n) • q₀) ≤
                v (((q (n + 1)).1.1.coeff d : K) -
                  ((q n).1.1.coeff d : K)) := by
            obtain ⟨r, hr, hrval⟩ := hqsucc_factor n
            rw [hr]
            simp only [Polynomial.coeff_add]
            simpa [sub_eq_add_neg, add_assoc] using hrval d
          have hstep_h (d n : ℕ) :
              ((2 ^ n) • q₀) ≤
                v (((q (n + 1)).1.2.coeff d : K) -
                  ((q n).1.2.coeff d : K)) := by
            obtain ⟨s, hs, hsval⟩ := hqsucc_factor_h n
            rw [hs]
            simp only [Polynomial.coeff_add]
            simpa [sub_eq_add_neg, add_assoc] using hsval d
          have hgLimit (d : ℕ) : ∃ L : K,
              Filter.Tendsto
                  (fun n : ℕ => ((q n).1.1.coeff d : K))
                  Filter.atTop (nhds L) ∧
                ∀ n : ℕ, ((2 ^ n) • q₀) ≤
                  v (((q n).1.1.coeff d : K) - L) := by
            exact hlimit_of_steps
              (fun n : ℕ => ((q n).1.1.coeff d : K))
              (hstep_g d)
          have hhLimit (d : ℕ) : ∃ L : K,
              Filter.Tendsto
                  (fun n : ℕ => ((q n).1.2.coeff d : K))
                  Filter.atTop (nhds L) ∧
                ∀ n : ℕ, ((2 ^ n) • q₀) ≤
                  v (((q n).1.2.coeff d : K) - L) := by
            exact hlimit_of_steps
              (fun n : ℕ => ((q n).1.2.coeff d : K))
              (hstep_h d)
          let glim : ℕ → vK.valuationSubring := fun d =>
            ⟨(hgLimit d).choose, hlimit_mem
              (fun n : ℕ => ((q n).1.1.coeff d : K))
              (fun n => ((q n).1.1.coeff d).property)
              (hgLimit d).choose ((hgLimit d).choose_spec.1)⟩
          let hlim : ℕ → vK.valuationSubring := fun d =>
            ⟨(hhLimit d).choose, hlimit_mem
              (fun n : ℕ => ((q n).1.2.coeff d : K))
              (fun n => ((q n).1.2.coeff d).property)
              (hhLimit d).choose ((hhLimit d).choose_spec.1)⟩
          have hglim_spec (d n : ℕ) :
              ((2 ^ n) • q₀) ≤
                v (((q n).1.1.coeff d : K) - (glim d : K)) :=
            (hgLimit d).choose_spec.2 n
          have hlim_spec (d n : ℕ) :
              ((2 ^ n) • q₀) ≤
                v (((q n).1.2.coeff d : K) - (hlim d : K)) :=
            (hhLimit d).choose_spec.2 n
          have hglim_tendsto (d : ℕ) :
              Filter.Tendsto (fun n : ℕ => ((q n).1.1.coeff d : K))
                Filter.atTop (nhds (glim d : K)) :=
            (hgLimit d).choose_spec.1
          have hlim_tendsto (d : ℕ) :
              Filter.Tendsto (fun n : ℕ => ((q n).1.2.coeff d : K))
                Filter.atTop (nhds (hlim d : K)) :=
            (hhLimit d).choose_spec.1
          have hcoeff_zero_high_g (d n : ℕ)
              (hd : g₀.natDegree < d) : (q n).1.1.coeff d = 0 := by
            rcases (q n).property with ⟨hg, hh, hgd, hhd, hrg, hrh, happrox⟩
            apply coeff_eq_zero_of_natDegree_lt
            rw [hgd]
            exact hd
          have hcoeff_lead_one_g (n : ℕ) :
              (q n).1.1.coeff g₀.natDegree = 1 := by
            rcases (q n).property with ⟨hg, hh, hgd, hhd, hrg, hrh, happrox⟩
            simpa [← hgd] using hg.coeff_natDegree
          have hglim_eq_zero (d : ℕ) (hd : g₀.natDegree < d) :
              glim d = 0 := by
            have hseq : (fun n : ℕ => ((q n).1.1.coeff d : K)) =
                (fun _ : ℕ => (0 : K)) := by
              funext n
              simpa using congrArg (fun z : vK.valuationSubring => (z : K)
                ) (hcoeff_zero_high_g d n hd)
            have hzero : (glim d : K) = 0 := by
              have hlim' : Filter.Tendsto (fun _ : ℕ => (0 : K))
                  Filter.atTop (nhds (glim d : K)) := by
                rw [← hseq]
                exact hglim_tendsto d
              exact tendsto_nhds_unique hlim' tendsto_const_nhds
            exact Subtype.ext hzero
          have hglim_eq_one : glim g₀.natDegree = 1 := by
            have hseq : (fun n : ℕ =>
                ((q n).1.1.coeff g₀.natDegree : K)) =
                (fun _ : ℕ => (1 : K)) := by
              funext n
              simpa using congrArg (fun z : vK.valuationSubring => (z : K)
                ) (hcoeff_lead_one_g n)
            have hone : (glim g₀.natDegree : K) = 1 := by
              have hlim' : Filter.Tendsto (fun _ : ℕ => (1 : K))
                  Filter.atTop (nhds (glim g₀.natDegree : K)) := by
                rw [← hseq]
                exact hglim_tendsto g₀.natDegree
              exact tendsto_nhds_unique hlim' tendsto_const_nhds
            exact Subtype.ext hone
          have hcoeff_zero_high_h (d n : ℕ)
              (hd : h₀.natDegree < d) : (q n).1.2.coeff d = 0 := by
            rcases (q n).property with ⟨hg, hh, hgd, hhd, hrg, hrh, happrox⟩
            apply coeff_eq_zero_of_natDegree_lt
            rw [hhd]
            exact hd
          have hcoeff_lead_one_h (n : ℕ) :
              (q n).1.2.coeff h₀.natDegree = 1 := by
            rcases (q n).property with ⟨hg, hh, hgd, hhd, hrg, hrh, happrox⟩
            simpa [← hhd] using hh.coeff_natDegree
          have hlim_eq_zero (d : ℕ) (hd : h₀.natDegree < d) :
              hlim d = 0 := by
            have hseq : (fun n : ℕ => ((q n).1.2.coeff d : K)) =
                (fun _ : ℕ => (0 : K)) := by
              funext n
              simpa using congrArg (fun z : vK.valuationSubring => (z : K)
                ) (hcoeff_zero_high_h d n hd)
            have hzero : (hlim d : K) = 0 := by
              have hlim' : Filter.Tendsto (fun _ : ℕ => (0 : K))
                  Filter.atTop (nhds (hlim d : K)) := by
                rw [← hseq]
                exact hlim_tendsto d
              exact tendsto_nhds_unique hlim' tendsto_const_nhds
            exact Subtype.ext hzero
          have hlim_eq_one : hlim h₀.natDegree = 1 := by
            have hseq : (fun n : ℕ =>
                ((q n).1.2.coeff h₀.natDegree : K)) =
                (fun _ : ℕ => (1 : K)) := by
              funext n
              simpa using congrArg (fun z : vK.valuationSubring => (z : K)
                ) (hcoeff_lead_one_h n)
            have hone : (hlim h₀.natDegree : K) = 1 := by
              have hlim' : Filter.Tendsto (fun _ : ℕ => (1 : K))
                  Filter.atTop (nhds (hlim h₀.natDegree : K)) := by
                rw [← hseq]
                exact hlim_tendsto h₀.natDegree
              exact tendsto_nhds_unique hlim' tendsto_const_nhds
            exact Subtype.ext hone
          let g : vK.valuationSubring[X] := X ^ g₀.natDegree +
            ∑ i ∈ Finset.range g₀.natDegree,
              C (glim i) * X ^ i
          let h : vK.valuationSubring[X] := X ^ h₀.natDegree +
            ∑ i ∈ Finset.range h₀.natDegree,
              C (hlim i) * X ^ i
          have hg : g.Monic := by
            dsimp [g]
            apply monic_X_pow_add
            simp_rw [← Fin.sum_univ_eq_sum_range, degree_sum_fin_lt]
          have hh : h.Monic := by
            dsimp [h]
            apply monic_X_pow_add
            simp_rw [← Fin.sum_univ_eq_sum_range, degree_sum_fin_lt]
          have hgcoeff_low (i : ℕ) (hi : i < g₀.natDegree) :
              g.coeff i = glim i := by
            simp [g, hi, Nat.ne_of_lt hi]
          have hgcoeff_lead : g.coeff g₀.natDegree = 1 := by
            simp [g]
          have hgcoeff_high (i : ℕ) (hi : g₀.natDegree < i) :
              g.coeff i = 0 := by
            simp [g, Nat.ne_of_gt hi,
              Nat.not_lt_of_ge (Nat.le_of_lt hi)]
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
              simpa [hlim_eq_one] using hhcoeff_lead
            have hig : h₀.natDegree < i := lt_of_le_of_ne
              (Nat.le_of_not_gt hi) (Ne.symm hieq)
            rw [hhcoeff_high i hig, hlim_eq_zero i hig]
          have hprod_coeff (n d : ℕ) :
              ((2 ^ n) • q₀) ≤
                v ((((q n).1.1 * (q n).1.2).coeff d : K) -
                  ((g * h).coeff d : K)) := by
            rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
            have hcast_prod :
                (((∑ x ∈ Finset.antidiagonal d,
                  (q n).1.1.coeff x.1 * (q n).1.2.coeff x.2) :
                    vK.valuationSubring) : K) =
                  ∑ x ∈ Finset.antidiagonal d,
                    ((q n).1.1.coeff x.1 : K) *
                      ((q n).1.2.coeff x.2 : K) := by
              norm_cast
            have hcast_gh :
                (((∑ x ∈ Finset.antidiagonal d,
                  g.coeff x.1 * h.coeff x.2) : vK.valuationSubring) : K) =
                  ∑ x ∈ Finset.antidiagonal d,
                    (g.coeff x.1 : K) * (h.coeff x.2 : K) := by
              norm_cast
            rw [hcast_prod, hcast_gh]
            rw [← Finset.sum_sub_distrib]
            apply hsum_lower (b := (2 ^ n) • q₀)
            intro x hx
            have hga : ((2 ^ n) • q₀) ≤
                v (((q n).1.1.coeff x.1 : K) - (g.coeff x.1 : K)) := by
              rw [hgcoeff_eq x.1]
              exact hglim_spec x.1 n
            have hhb : ((2 ^ n) • q₀) ≤
                v (((q n).1.2.coeff x.2 : K) - (h.coeff x.2 : K)) := by
              rw [hhcoeff_eq x.2]
              exact hlim_spec x.2 n
            have hterm : ((2 ^ n) • q₀) ≤
                v (((q n).1.1.coeff x.1 : K) *
                    ((q n).1.2.coeff x.2 : K) -
                  (g.coeff x.1 : K) * (h.coeff x.2 : K)) := by
              rw [show ((q n).1.1.coeff x.1 : K) *
                    ((q n).1.2.coeff x.2 : K) -
                    (g.coeff x.1 : K) * (h.coeff x.2 : K) =
                  (((q n).1.1.coeff x.1 : K) - (g.coeff x.1 : K)) *
                      ((q n).1.2.coeff x.2 : K) +
                    (g.coeff x.1 : K) *
                      (((q n).1.2.coeff x.2 : K) - (h.coeff x.2 : K)) by ring]
              have hfirst : ((2 ^ n) • q₀) ≤
                  v ((((q n).1.1.coeff x.1 : K) - (g.coeff x.1 : K)) *
                    ((q n).1.2.coeff x.2 : K)) := by
                rw [v.map_mul]
                exact hga.trans (le_add_of_nonneg_right
                  ((hA _).mp ((q n).1.2.coeff x.2).property))
              have hsecond : ((2 ^ n) • q₀) ≤
                  v (((g.coeff x.1 : K) *
                    (((q n).1.2.coeff x.2 : K) - (h.coeff x.2 : K)))) := by
                rw [v.map_mul]
                exact hhb.trans (le_add_of_nonneg_left
                  ((hA _).mp (g.coeff x.1).property))
              exact (le_min hfirst hsecond).trans
                (valuation_strong_triangle v _ _)
            exact hterm
          have hfactor_coeff (n d : ℕ) :
              ((2 ^ n) • q₀) ≤ v (((f - g * h).coeff d : K)) := by
            rcases (q n).property with ⟨hgq, hhq, hgdq, hhdq, hrgq, hrhq, happrox⟩
            have ha : ((2 ^ n) • q₀) ≤
                v (((f - (q n).1.1 * (q n).1.2).coeff d : K)) := happrox d
            have hp := hprod_coeff n d
            have hp' : ((2 ^ n) • q₀) ≤
                v ((((q n).1.1 * (q n).1.2 - g * h).coeff d : K)) := by
              rw [Polynomial.coeff_sub]
              simpa using hp
            have heq : ((f - g * h).coeff d : K) =
                ((f - (q n).1.1 * (q n).1.2).coeff d : K) +
                  (((q n).1.1 * (q n).1.2 - g * h).coeff d : K) := by
              simp only [Polynomial.coeff_sub]
              norm_cast
              ring
            rw [heq]
            exact (le_min ha hp').trans
              (valuation_strong_triangle v
                ((f - (q n).1.1 * (q n).1.2).coeff d : K)
                (((q n).1.1 * (q n).1.2 - g * h).coeff d : K))
          have hzero_of_doubling (q' : (Additive Γ)ᵒᵈ) (hq' : 0 < q')
              (hq'rep : ∃ z : K, z ≠ 0 ∧ v z = q') (x : K)
              (hx : ∀ n : ℕ, (2 ^ n) • q' ≤ v x) : x = 0 := by
            by_cases hx0 : x = 0
            · exact hx0
            have hq'top : q' ≠ ⊤ := by
              intro htop
              rcases hq'rep with ⟨z, hz, hzval⟩
              exact (AddValuation.ne_top_iff v).mpr hz
                (hzval.trans htop)
            have hvalx : v x ≠ ⊤ := (AddValuation.ne_top_iff v).mpr hx0
            have hcofinal' :=
              section06_rank_one_image_doubling_cofinal v q' hq'
                (fun _ => hq'rep)
            have hrep : ∃ w : K, w ≠ 0 ∧ v w = v x + q' := by
              rcases himage_add_sub (r₁ := v x) (r₂ := q') (r₃ := 0)
                  ⟨x, hx0, rfl⟩ hq'rep
                  ⟨1, one_ne_zero, by simp⟩ with ⟨w, hw, hwval⟩
              exact ⟨w, hw, by simpa using hwval⟩
            obtain ⟨N, hN⟩ := hcofinal' (v x + q') hrep
            have hlt : v x < v x + q' := by
              simpa using (add_lt_add_iff_right_of_ne_top hvalx).2 hq'
            have hcontra : v x + q' ≤ v x := (hN).trans (hx N)
            exact False.elim ((not_le_of_gt hlt) hcontra)
          have hfactor : f = g * h := by
            have hzero : f - g * h = 0 := by
              apply Polynomial.ext
              intro d
              apply Subtype.ext
              apply hzero_of_doubling q₀ hq₀ hq₀rep
              intro n
              exact hfactor_coeff n d
            exact sub_eq_zero.mp hzero
          have hqred_g (i : ℕ) :
              residueMap vK.valuationSubring ((q 0).1.1.coeff i) = g₀.coeff i := by
            rcases (q 0).property with ⟨hgq, hhq, hgdq, hhdq, hrgq, hrhq, happrox⟩
            have hi := congrArg (fun p : Polynomial (ResidueRing vK.valuationSubring) =>
              p.coeff i) hrgq
            simpa [residuePolynomial] using hi
          have hqred_h (i : ℕ) :
              residueMap vK.valuationSubring ((q 0).1.2.coeff i) = h₀.coeff i := by
            rcases (q 0).property with ⟨hgq, hhq, hgdq, hhdq, hrgq, hrhq, happrox⟩
            have hi := congrArg (fun p : Polynomial (ResidueRing vK.valuationSubring) =>
              p.coeff i) hrhq
            simpa [residuePolynomial] using hi
          have hglim_map (i : ℕ) :
              residueMap vK.valuationSubring (glim i) = g₀.coeff i := by
            have hi : (q 0).1.1.coeff i - glim i ∈
                hvalue_ideal q₀ hq₀ := by
              simpa [hvalue_ideal, pow_zero] using hglim_spec i 0
            have hmem : (q 0).1.1.coeff i - glim i ∈
                IsLocalRing.maximalIdeal vK.valuationSubring := by
              exact hmaximal_le q₀ hq₀ (hvalue_ideal q₀ hq₀) rfl hi
            have hi' : residueMap vK.valuationSubring
                ((q 0).1.1.coeff i - glim i) = 0 :=
              Ideal.Quotient.eq_zero_iff_mem.mpr hmem
            rw [map_sub] at hi'
            exact (sub_eq_zero.mp hi').symm.trans (hqred_g i)
          have hlim_map (i : ℕ) :
              residueMap vK.valuationSubring (hlim i) = h₀.coeff i := by
            have hi : (q 0).1.2.coeff i - hlim i ∈
                hvalue_ideal q₀ hq₀ := by
              simpa [hvalue_ideal, pow_zero] using hlim_spec i 0
            have hmem : (q 0).1.2.coeff i - hlim i ∈
                IsLocalRing.maximalIdeal vK.valuationSubring := by
              exact hmaximal_le q₀ hq₀ (hvalue_ideal q₀ hq₀) rfl hi
            have hi' : residueMap vK.valuationSubring
                ((q 0).1.2.coeff i - hlim i) = 0 :=
              Ideal.Quotient.eq_zero_iff_mem.mpr hmem
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
            have hi : residueMap vK.valuationSubring (g.coeff i) = g₀.coeff i := by
              rw [hgcoeff_eq i, hglim_map i]
            simpa only [residuePolynomial, Polynomial.coeff_map] using hi
          have hredh : residuePolynomial h = h₀ := by
            apply Polynomial.ext
            intro i
            have hi : residueMap vK.valuationSubring (h.coeff i) = h₀.coeff i := by
              rw [hhcoeff_eq i, hlim_map i]
            simpa only [residuePolynomial, Polynomial.coeff_map] using hi
          refine ⟨(g, h), ?_⟩
          exact ⟨hg, hh, hdeg_g, hdeg_h, hredg, hredh, hfactor⟩
      rcases hExists with ⟨gh₁, hgh₁⟩
      refine ⟨gh₁, hgh₁, ?_⟩
      intro gh₂ hgh₂
      rcases hgh₁ with ⟨hg₁, hh₁, hgd₁, hhd₁, hredg₁, hredh₁, hfac₁⟩
      rcases hgh₂ with ⟨hg₂, hh₂, hgd₂, hhd₂, hredg₂, hredh₂, hfac₂⟩
      let dg : vK.valuationSubring[X] := gh₂.1 - gh₁.1
      let dh : vK.valuationSubring[X] := gh₂.2 - gh₁.2
      have hbase (i : ℕ) :
          dg.coeff i ∈ IsLocalRing.maximalIdeal vK.valuationSubring ∧
            dh.coeff i ∈ IsLocalRing.maximalIdeal vK.valuationSubring := by
        constructor
        · change (gh₂.1 - gh₁.1).coeff i ∈
            IsLocalRing.maximalIdeal vK.valuationSubring
          have hi := congrArg
            (fun P : Polynomial (ResidueRing vK.valuationSubring) => P.coeff i)
            (hredg₂.trans hredg₁.symm)
          have hi' : residueMap vK.valuationSubring (gh₂.1.coeff i) =
              residueMap vK.valuationSubring (gh₁.1.coeff i) := by
            simpa only [residuePolynomial, Polynomial.coeff_map] using hi
          have hi0 : residueMap vK.valuationSubring
              ((gh₂.1 - gh₁.1).coeff i) = 0 := by
            rw [Polynomial.coeff_sub, map_sub]
            exact sub_eq_zero.mpr hi'
          exact Ideal.Quotient.eq_zero_iff_mem.mp hi0
        · change (gh₂.2 - gh₁.2).coeff i ∈
            IsLocalRing.maximalIdeal vK.valuationSubring
          have hi := congrArg
            (fun P : Polynomial (ResidueRing vK.valuationSubring) => P.coeff i)
            (hredh₂.trans hredh₁.symm)
          have hi' : residueMap vK.valuationSubring (gh₂.2.coeff i) =
              residueMap vK.valuationSubring (gh₁.2.coeff i) := by
            simpa only [residuePolynomial, Polynomial.coeff_map] using hi
          have hi0 : residueMap vK.valuationSubring
              ((gh₂.2 - gh₁.2).coeff i) = 0 := by
            rw [Polynomial.coeff_sub, map_sub]
            exact sub_eq_zero.mpr hi'
          exact Ideal.Quotient.eq_zero_iff_mem.mp hi0
      have hprod_eq : gh₂.1 * gh₂.2 = gh₁.1 * gh₁.2 := by
        rw [← hfac₂, hfac₁]
      have hdgdeg : dg.degree < gh₁.1.degree := by
        dsimp [dg]
        apply Polynomial.degree_sub_lt_right
        · rw [Polynomial.degree_eq_natDegree hg₂.ne_zero,
            Polynomial.degree_eq_natDegree hg₁.ne_zero, hgd₂, hgd₁]
        · exact hg₁.ne_zero
        · rw [hg₂.leadingCoeff, hg₁.leadingCoeff]
      have dhdeg : dh.degree < gh₁.2.degree := by
        dsimp [dh]
        apply Polynomial.degree_sub_lt_right
        · rw [Polynomial.degree_eq_natDegree hh₂.ne_zero,
            Polynomial.degree_eq_natDegree hh₁.ne_zero, hhd₂, hhd₁]
        · exact hh₁.ne_zero
        · rw [hh₂.leadingCoeff, hh₁.leadingCoeff]
      have himage_add_sub_unique {r₁ r₂ r₃ : (Additive Γ)ᵒᵈ}
          (hr₁ : ∃ x : K, x ≠ 0 ∧ v x = r₁)
          (hr₂ : ∃ y : K, y ≠ 0 ∧ v y = r₂)
          (hr₃ : ∃ z : K, z ≠ 0 ∧ v z = r₃) :
          ∃ w : K, w ≠ 0 ∧ v w = r₁ + r₂ - r₃ := by
        rcases hr₁ with ⟨x, hx, hxv⟩
        rcases hr₂ with ⟨y, hy, hyv⟩
        rcases hr₃ with ⟨z, hz, hzv⟩
        refine ⟨x * y * z⁻¹,
          mul_ne_zero (mul_ne_zero hx hy) (inv_ne_zero hz), ?_⟩
        rw [v.map_mul, v.map_mul, v.map_inv, hxv, hyv, hzv]
        simp [sub_eq_add_neg]
      have hpositive_image : ∃ q : (Additive Γ)ᵒᵈ, 0 < q ∧
          (∃ z : K, z ≠ 0 ∧ v z = q) := by
        obtain ⟨z, hz, hzv⟩ := Valuation.RankOne.nontrivial v.toValuation
        have hzfield : z ≠ 0 := by
          intro hz0
          subst z
          exact hz (by simp only [map_zero])
        rcases lt_or_gt_of_ne hzv with hzlt | hzgt
        · have hqpos : 0 < v z := by
            change Multiplicative.ofAdd (OrderDual.toDual (v z)) <
              Multiplicative.ofAdd (OrderDual.toDual
                (0 : (Additive Γ)ᵒᵈ))
            exact hzlt
          exact ⟨v z, hqpos, z, hzfield, rfl⟩
        · have hinv : v.toValuation (z⁻¹) < 1 := by
            rw [v.toValuation.map_inv]
            exact inv_lt_one_of_one_lt₀ hzgt
          have hqpos : 0 < v (z⁻¹) := by
            change Multiplicative.ofAdd (OrderDual.toDual (v (z⁻¹))) <
              Multiplicative.ofAdd (OrderDual.toDual
                (0 : (Additive Γ)ᵒᵈ))
            exact hinv
          exact ⟨v (z⁻¹), hqpos, z⁻¹, inv_ne_zero hzfield, by
            rw [v.map_inv]⟩
      have hzero_of_doubling_unique (q' : (Additive Γ)ᵒᵈ) (hq' : 0 < q')
          (hq'rep : ∃ z : K, z ≠ 0 ∧ v z = q') (x : K)
          (hx : ∀ n : ℕ, (2 ^ n) • q' ≤ v x) : x = 0 := by
        by_cases hx0 : x = 0
        · exact hx0
        have hq'top : q' ≠ ⊤ := by
          intro htop
          rcases hq'rep with ⟨z, hz, hzval⟩
          exact (AddValuation.ne_top_iff v).mpr hz
            (hzval.trans htop)
        have hvalx : v x ≠ ⊤ := (AddValuation.ne_top_iff v).mpr hx0
        have hcofinal' :=
          section06_rank_one_image_doubling_cofinal v q' hq'
            (fun _ => hq'rep)
        have hrep : ∃ w : K, w ≠ 0 ∧ v w = v x + q' := by
          rcases himage_add_sub_unique (r₁ := v x) (r₂ := q') (r₃ := 0)
              ⟨x, hx0, rfl⟩ hq'rep
              ⟨1, one_ne_zero, by simp⟩ with ⟨w, hw, hwval⟩
          exact ⟨w, hw, by simpa using hwval⟩
        obtain ⟨N, hN⟩ := hcofinal' (v x + q') hrep
        have hlt : v x < v x + q' := by
          simpa using (add_lt_add_iff_right_of_ne_top hvalx).2 hq'
        have hcontra : v x + q' ≤ v x := (hN).trans (hx N)
        exact False.elim ((not_le_of_gt hlt) hcontra)
      have hcommon : ∃ q : (Additive Γ)ᵒᵈ, 0 < q ∧
          (∃ z : K, z ≠ 0 ∧ v z = q) ∧
          (∀ i : ℕ, q ≤ v (dg.coeff i : K)) ∧
          (∀ i : ℕ, q ≤ v (dh.coeff i : K)) := by
        by_cases hdg0 : dg = 0
        · by_cases dh0 : dh = 0
          · obtain ⟨q, hq, hqrep⟩ := hpositive_image
            exact ⟨q, hq, hqrep, by simp [hdg0], by simp [dh0]⟩
          · obtain ⟨q, hq, hqrep, hqbound⟩ :=
              hlower_bound dh (fun i => (hbase i).2) dh0
            refine ⟨q, hq, hqrep, ?_, hqbound⟩
            intro i
            simp [hdg0]
        · obtain ⟨qg, hqg, hqgrep, hqgbound⟩ :=
            hlower_bound dg (fun i => (hbase i).1) hdg0
          by_cases dh0 : dh = 0
          · refine ⟨qg, hqg, hqgrep, hqgbound, ?_⟩
            intro i
            simp [dh0]
          · obtain ⟨qh, hqh, hqhrep, hqhbound⟩ :=
              hlower_bound dh (fun i => (hbase i).2) dh0
            rcases le_total qg qh with hqle | hqle
            · refine ⟨qg, hqg, hqgrep, hqgbound, ?_⟩
              intro i
              exact hqle.trans (hqhbound i)
            · refine ⟨qh, hqh, hqhrep, ?_, hqhbound⟩
              intro i
              exact hqle.trans (hqgbound i)
      obtain ⟨q, hq, hqrep, hqg, hqh⟩ := hcommon
      have hdelta_prod (r : (Additive Γ)ᵒᵈ)
          (hgr : ∀ i : ℕ, r ≤ v (dg.coeff i : K))
          (hhr : ∀ i : ℕ, r ≤ v (dh.coeff i : K)) (d : ℕ) :
          r + r ≤ v (((dg * dh).coeff d : K)) := by
        rw [Polynomial.coeff_mul]
        have hcast :
            (((∑ x ∈ Finset.antidiagonal d,
              dg.coeff x.1 * dh.coeff x.2) : vK.valuationSubring) : K) =
              ∑ x ∈ Finset.antidiagonal d,
                (dg.coeff x.1 : K) * (dh.coeff x.2 : K) := by
          norm_cast
        rw [hcast]
        apply hsum_lower (b := r + r)
        intro x hx
        rw [v.map_mul]
        exact add_le_add (hgr x.1) (hhr x.2)
      have hstep_unique (r : (Additive Γ)ᵒᵈ) (hr : 0 < r)
          (hgr : ∀ i : ℕ, r ≤ v (dg.coeff i : K))
          (hhr : ∀ i : ℕ, r ≤ v (dh.coeff i : K)) :
          ∀ i : ℕ, (r + r) ≤ v (dg.coeff i : K) ∧
            (r + r) ≤ v (dh.coeff i : K) := by
        have hrr : 0 < r + r := by
          simpa [two_nsmul] using (nsmul_pos hr (by norm_num : (2 : ℕ) ≠ 0))
        let J : Ideal vK.valuationSubring := hvalue_ideal (r + r) hrr
        have hJle : J ≤ IsLocalRing.maximalIdeal vK.valuationSubring :=
          hmaximal_le (r + r) hrr J rfl
        have hrelg : gh₂.1 = gh₁.1 + dg := by
          dsimp [dg]
          ring
        have hrelh : gh₂.2 = gh₁.2 + dh := by
          dsimp [dh]
          ring
        have hexpand : (gh₁.1 + dg) * (gh₁.2 + dh) = gh₁.1 * gh₁.2 := by
          rw [← hrelg, ← hrelh]
          exact hprod_eq
        have hlin :
            factorizationCorrectionMap gh₁.1 gh₁.2 (dg, dh) =
              -(dg * dh) := by
          dsimp [factorizationCorrectionMap]
          calc
            dg * gh₁.2 + dh * gh₁.1 =
                (gh₁.1 + dg) * (gh₁.2 + dh) - gh₁.1 * gh₁.2 -
                  dg * dh := by ring
            _ = -(dg * dh) := by rw [hexpand]; ring
        have ht : PolynomialCoefficientsInIdeal J (-(dg * dh)) := by
          intro i
          change r + r ≤ v (((-(dg * dh)).coeff i : K))
          simpa [Polynomial.coeff_neg, v.map_neg] using
            hdelta_prod r hgr hhr i
        have hterms := section06_correction_terms_mem_of_ideal J hJle
          hg₁ hh₁ (hcop_lift gh₁.1 gh₁.2 hg₁ hh₁ hredg₁ hredh₁)
          hdgdeg dhdeg hlin ht
        intro i
        constructor
        · simpa [J, hvalue_ideal] using hterms.1 i
        · simpa [J, hvalue_ideal] using hterms.2 i
      have hdiff_bound (n : ℕ) : ∀ i : ℕ,
          (2 ^ n) • q ≤ v (dg.coeff i : K) ∧
            (2 ^ n) • q ≤ v (dh.coeff i : K) := by
        induction n with
        | zero =>
            intro i
            simpa using And.intro (hqg i) (hqh i)
        | succ n ih =>
            intro i
            have hstep := hstep_unique ((2 ^ n) • q)
              (nsmul_pos hq (by positivity))
              (fun j => (ih j).1) (fun j => (ih j).2) i
            have hpow : (2 ^ n) • q + (2 ^ n) • q = (2 ^ (n + 1)) • q := by
              have htwo : 2 ^ n * 2 = 2 ^ n + 2 ^ n := by omega
              rw [pow_succ, htwo, add_nsmul]
            rw [hpow] at hstep
            exact hstep
      have hdgz : dg = 0 := by
        apply Polynomial.ext
        intro i
        apply Subtype.ext
        apply hzero_of_doubling_unique q hq hqrep
        intro n
        exact (hdiff_bound n i).1
      have dhz : dh = 0 := by
        apply Polynomial.ext
        intro i
        apply Subtype.ext
        apply hzero_of_doubling_unique q hq hqrep
        intro n
        exact (hdiff_bound n i).2
      have hdgz' : gh₂.1 - gh₁.1 = 0 := by
        simpa [dg] using hdgz
      have dhz' : gh₂.2 - gh₁.2 = 0 := by
        simpa [dh] using dhz
      apply Prod.ext
      · exact sub_eq_zero.mp hdgz'
      · exact sub_eq_zero.mp dhz'

end
end Chapter09
end LastLib.Book01ValuationsDVRsAndCompletions
