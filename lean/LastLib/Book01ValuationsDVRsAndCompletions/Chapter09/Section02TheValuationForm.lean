import LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.Section01CorrectingAnApproximateRoot

namespace LastLib.Book01ValuationsDVRsAndCompletions
namespace Chapter09

universe u uK uL uΓ uA uH uC uI

open scoped BigOperators Polynomial WithZeroTopology
open Ideal IsLocalRing Polynomial

noncomputable section

local instance chapter09Section02FactPrime7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
local instance chapter09Section02FactPrime2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩

/-! # Chapter 9: Hensel lifting

This file is a statement-generation pass for Chapter 9 of Book 1.  The
declarations deliberately keep the hypotheses visible: in particular, a
complete DVR means adic completeness, while the valuation form is stated for
an arbitrary additive valuation.
-/

/-! # Book 1, Chapter 9, Section 9.2: The Valuation Form
-/

/-! ## 9.2 The valuation form -/

/-- The excess of a valuation error beyond twice a fixed derivative value. -/
def valuationExcess {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ)
    (f : K[X]) (s : Γ) (a : K) : Γ :=
  v (f.eval a) - (s + s)

/- The uniformity canonically induced by an additive valuation. -/
@[instance_reducible]
noncomputable def Chapter09ValuationUniformSpace
    {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ) : UniformSpace K :=
  (Valued.mk' v.toValuation).toUniformSpace

/- Completeness for the nonarchimedean uniformity attached to `v`. -/
def Chapter09NonarchimedeanComplete
    {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ) : Prop :=
  @CompleteSpace K (Chapter09ValuationUniformSpace v)

/-- A sequence of values tends to infinity in the ordered-value sense. -/
def TendsToTop {Γ : Type*} [Preorder Γ] (s : ℕ → Γ) : Prop :=
  ∀ γ : Γ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → γ ≤ s n

/- Cofinality needed to turn valuation doubling into convergence to the top. -/
def Chapter09DoublingCofinal {Γ : Type*}
    [LinearOrderedAddCommGroupWithTop Γ] (q : Γ) : Prop :=
  ∀ γ : Γ, ∃ n : ℕ, γ ≤ (2 ^ n) • q

/- Cofinality restricted to values represented by nonzero field elements. -/
private def Chapter09ImageDoublingCofinal {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ) (q : Γ) : Prop :=
  ∀ γ : Γ, (∃ x : K, x ≠ 0 ∧ v x = γ) → ∃ n : ℕ, γ ≤ (2 ^ n) • q

/-- The strong triangle inequality for an additive valuation. -/
theorem valuation_strong_triangle {K Γ : Type*} [Ring K]
    [LinearOrderedAddCommMonoidWithTop Γ] (v : AddValuation K Γ) (x y : K) :
    min (v x) (v y) ≤ v (x + y) := by
  exact v.map_add x y

/-- Unequal valuation terms cannot cancel. -/
theorem valuation_unequal_value_rigidity {K Γ : Type*} [Ring K]
    [LinearOrderedAddCommMonoidWithTop Γ] (v : AddValuation K Γ) {x y : K}
    (hxy : v x ≠ v y) :
    v (x + y) = min (v x) (v y) := by
  exact v.map_add_of_distinct_val hxy

/-- The Newton correction and derivative invariants in the proof of Theorem 9.2. -/
theorem valuation_newton_induction {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ)
    (A : Subring K) (hA : IsValuationSubring A v) (f : K[X])
    (hf : PolynomialCoefficientsInSubring A f) (a₀ : K) (ha₀ : a₀ ∈ A)
    (hineq : v (f.eval a₀) > v (f.derivative.eval a₀) + v (f.derivative.eval a₀))
    (hderiv : v (f.derivative.eval a₀) ≠ ⊤) :
    let s := v (f.derivative.eval a₀)
    let q₀ := v (f.eval a₀) - (s + s)
    ∀ n : ℕ,
      v (f.derivative.eval (newtonIterate f a₀ n)) = s ∧
        valuationExcess v f s (newtonIterate f a₀ n) ≥ (2 ^ n) • q₀ ∧
        v (newtonIterate f a₀ (n + 1) - newtonIterate f a₀ n) =
          s + valuationExcess v f s (newtonIterate f a₀ n) := by
  dsimp
  let s : Γ := v (f.derivative.eval a₀)
  let q₀ : Γ := v (f.eval a₀) - (s + s)
  have hs : s ≠ ⊤ := by
    simpa [s] using hderiv
  have hs_nonneg : 0 ≤ s := by
    apply (hA _).mp
    have hfd : PolynomialCoefficientsInSubring A f.derivative := by
      intro n
      rw [coeff_derivative]
      exact A.mul_mem (hf (n + 1)) (by simpa using intCast_mem A (n + 1 : ℤ))
    rw [eval_eq_sum_range]
    apply A.sum_mem
    intro n hn
    exact A.mul_mem (hfd n) (A.pow_mem ha₀ n)
  have hq₀pos : 0 < q₀ := by
    dsimp [q₀, s]
    exact LinearOrderedAddCommGroupWithTop.sub_pos.mpr (Or.inl hineq)
  have hEvalMem : ∀ (p : K[X]), PolynomialCoefficientsInSubring A p →
      ∀ {x : K}, x ∈ A → p.eval x ∈ A := by
    intro p hp x hx
    rw [eval_eq_sum_range]
    apply A.sum_mem
    intro n hn
    exact A.mul_mem (hp n) (A.pow_mem hx n)
  have hDerivativeCoeffs : PolynomialCoefficientsInSubring A f.derivative := by
    intro n
    rw [coeff_derivative]
    exact A.mul_mem (hf (n + 1)) (by simpa using intCast_mem A (n + 1 : ℤ))
  have hDerivativeDerivativeCoeffs :
      PolynomialCoefficientsInSubring A f.derivative.derivative := by
    intro n
    rw [coeff_derivative]
    exact A.mul_mem (hDerivativeCoeffs (n + 1))
      (by simpa using intCast_mem A (n + 1 : ℤ))
  have hTaylorIntegral : ∀ (p : K[X]), PolynomialCoefficientsInSubring A p →
      ∀ (x y : K), x ∈ A → y ∈ A → ∃ g : A,
        p.eval (x + y) = p.eval x + y * p.derivative.eval x + y ^ 2 * (g : K) := by
    intro p hp x y hx hy
    let hpcoeff : (p.coeffs : Set K) ⊆ A := by
      intro c hc
      rcases (Polynomial.mem_coeffs_iff.mp hc) with ⟨n, hn, rfl⟩
      exact hp n
    let pA : A[X] := p.toSubring A hpcoeff
    obtain ⟨g, hg⟩ := taylor_second_order pA ⟨x, hx⟩ ⟨y, hy⟩
    refine ⟨g, ?_⟩
    have hmap := congrArg (fun z : A => (z : K)) hg
    have hpmap : pA.map (Subring.subtype A) = p := by
      exact Polynomial.map_toSubring p A hpcoeff
    have heval (z : A) : ((pA.eval z : A) : K) = p.eval (z : K) := by
      have h := Polynomial.eval_map_apply (p := pA) (Subring.subtype A) z
      rw [hpmap] at h
      exact h.symm
    have hdermap : pA.derivative.map (Subring.subtype A) = p.derivative := by
      rw [← Polynomial.derivative_map, hpmap]
    have hderval (z : A) : ((pA.derivative.eval z : A) : K) = p.derivative.eval (z : K) := by
      have h := Polynomial.eval_map_apply (p := pA.derivative) (Subring.subtype A) z
      rw [hdermap] at h
      exact h.symm
    calc
      p.eval (x + y) = ((pA.eval (⟨x, hx⟩ + ⟨y, hy⟩) : A) : K) := by
        simpa using (heval (⟨x, hx⟩ + ⟨y, hy⟩)).symm
      _ = ((pA.eval ⟨x, hx⟩ + ⟨y, hy⟩ *
          pA.derivative.eval ⟨x, hx⟩ +
          ⟨y, hy⟩ ^ 2 * g : A) : K) := hmap
      _ = p.eval x + y * p.derivative.eval x + y ^ 2 * (g : K) := by
        simp [heval, hderval, Subring.coe_add, Subring.coe_mul]
  have hStep : ∀ n : ℕ,
      newtonIterate f a₀ n ∈ A ∧
        v (f.derivative.eval (newtonIterate f a₀ n)) = s ∧
        valuationExcess v f s (newtonIterate f a₀ n) ≥ (2 ^ n) • q₀ := by
    intro n
    induction n with
    | zero =>
        have hfe : f.eval a₀ ∈ A := hEvalMem f hf ha₀
        have hfde : f.derivative.eval a₀ ∈ A := hEvalMem f.derivative hDerivativeCoeffs ha₀
        refine ⟨ha₀, ?_, ?_⟩
        · rfl
        · simp [newtonIterate, valuationExcess, s, q₀]
    | succ n ih =>
        let an : K := newtonIterate f a₀ n
        let d : K := f.derivative.eval an
        let e : K := f.eval an
        let qn : Γ := valuationExcess v f s an
        have han : an ∈ A := by simpa [an] using ih.1
        have hdn : v d = s := by simpa [d] using ih.2.1
        have hqn : qn ≥ (2 ^ n) • q₀ := by simpa [qn] using ih.2.2
        have hqnpos : 0 < qn := lt_of_lt_of_le
          (nsmul_pos hq₀pos (by positivity : 2 ^ n ≠ 0)) hqn
        have hene : s + s ≤ v e := by
          have hqnonneg : 0 ≤ qn :=
            (le_of_lt (nsmul_pos hq₀pos (by positivity : 2 ^ n ≠ 0))).trans hqn
          have hcancel : s + s + (v e - (s + s)) = v e := by
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
              (LinearOrderedAddCommGroupWithTop.add_neg_cancel_left_of_ne_top
                (show s + s ≠ ⊤ by simp [hs]) (v e))
          rw [show qn = v e - (s + s) by rfl] at hqnonneg
          rw [← hcancel]
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hqnonneg (s + s)
        have hs_le_ve : s ≤ v e := by
          exact (le_add_of_nonneg_right hs_nonneg).trans hene
        have hcorrmem : e * Ring.inverse d ∈ A := by
          apply (hA _).mpr
          rw [Ring.inverse_eq_inv, v.map_mul, AddValuation.map_inv, hdn]
          have h := add_le_add_right hs_le_ve (-s)
          simpa [sub_eq_add_neg, add_comm,
            LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top hs] using h
        have han1 : newtonIterate f a₀ (n + 1) ∈ A := by
          have hrec : newtonIterate f a₀ (n + 1) = an - e * Ring.inverse d := by
            simp [an, d, e, newtonIterate, newtonCorrection]
          rw [hrec]
          exact A.sub_mem han hcorrmem
        have hdelta : newtonIterate f a₀ (n + 1) - an =
            -(e * Ring.inverse d) := by
          have hrec : newtonIterate f a₀ (n + 1) = an - e * Ring.inverse d := by
            simp [an, d, e, newtonIterate, newtonCorrection]
          rw [hrec]
          ring
        obtain ⟨g, hg⟩ := hTaylorIntegral f hf an
          (newtonIterate f a₀ (n + 1) - an) han (by
            rw [hdelta]
            exact A.neg_mem hcorrmem)
        have hdneq : d ≠ 0 := by
          intro hd0
          have : v d = ⊤ := by simp [hd0]
          exact hs ((by simpa [hdn] using this) : s = ⊤)
        have hdu : IsUnit d := isUnit_iff_ne_zero.mpr hdneq
        have hcancel : e + (newtonIterate f a₀ (n + 1) - an) * d = 0 := by
          rw [hdelta, Ring.inverse_eq_inv, neg_mul, mul_assoc,
            inv_mul_cancel₀ hdneq, mul_one]
          ring
        have hdeltaVal0 : v (newtonIterate f a₀ (n + 1) - an) = s + qn := by
          rw [hdelta, Ring.inverse_eq_inv, v.map_neg, v.map_mul,
            AddValuation.map_inv, hdn]
          by_cases hev : v e = ⊤
          · dsimp [qn, valuationExcess]
            have hev' : v (f.eval an) = ⊤ := by simpa [e] using hev
            rw [hev]
            simp [sub_eq_add_neg]
          · dsimp [qn, valuationExcess]
            have hval_formula : v e + -s = s + (v e + -(s + s)) := by
              rw [neg_add_rev]
              calc
                v e + -s = 0 + (v e + -s) := by simp
                _ = (s + -s) + (v e + -s) := by
                  simp [LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top hs]
                _ = s + (v e + (-s + -s)) := by ac_rfl
            simpa [e, an, sub_eq_add_neg] using hval_formula
        have hdn1 : v (f.derivative.eval (newtonIterate f a₀ (n + 1))) = s := by
          obtain ⟨gd, hgd⟩ := hTaylorIntegral f.derivative hDerivativeCoeffs an
            (newtonIterate f a₀ (n + 1) - an) han (by
              rw [hdelta]
              exact A.neg_mem hcorrmem)
          let delta : K := newtonIterate f a₀ (n + 1) - an
          let u : K := f.derivative.derivative.eval an + delta * (gd : K)
          have hdeltaVal : v delta = s + qn := by
            simpa [delta] using hdeltaVal0
          have hdelta_gt : s < v delta := by
            rw [hdeltaVal]
            have := (add_lt_add_iff_right_of_ne_top hs).mpr hqnpos
            simpa using this
          have hgdmem : (f.derivative.derivative.eval an) ∈ A :=
            hEvalMem f.derivative.derivative hDerivativeDerivativeCoeffs han
          have hgm : (gd : K) ∈ A := gd.property
          have hdelta_mem : delta ∈ A := by
            dsimp [delta]
            rw [hdelta]
            exact A.neg_mem hcorrmem
          have huv : 0 ≤ v u := by
            apply (le_trans (le_min (hA _ |>.mp hgdmem)
              (by
                apply (hA _).mp
                exact A.mul_mem hdelta_mem hgm))
              (v.map_add _ _))
          have hduval : s < v (delta * u) := by
            rw [v.map_mul]
            exact lt_of_lt_of_le hdelta_gt (le_add_of_nonneg_right huv)
          have hdercalc : f.derivative.eval (newtonIterate f a₀ (n + 1)) =
              d + delta * u := by
            rw [show newtonIterate f a₀ (n + 1) = an + delta by
              dsimp [delta]
              ring]
            rw [hgd]
            dsimp [u]
            ring
          calc
            v (f.derivative.eval (newtonIterate f a₀ (n + 1))) =
                v (d + delta * u) := congrArg v hdercalc
            _ = min (v d) (v (delta * u)) :=
              v.map_add_of_distinct_val (by
                rw [hdn]
                exact ne_of_lt hduval)
            _ = s := by rw [hdn, min_eq_left (le_of_lt hduval)]
        have hqn1 : valuationExcess v f s
              (newtonIterate f a₀ (n + 1)) ≥ (2 ^ (n + 1)) • q₀ := by
          let en : K := f.eval (newtonIterate f a₀ (n + 1))
          have hneval : en =
              (newtonIterate f a₀ (n + 1) - an) ^ 2 * (g : K) := by
            dsimp [en]
            calc
              f.eval (newtonIterate f a₀ (n + 1)) =
                  f.eval (an + (newtonIterate f a₀ (n + 1) - an)) := by
                    congr 1
                    ring
              _ = f.eval an +
                  (newtonIterate f a₀ (n + 1) - an) * f.derivative.eval an +
                  (newtonIterate f a₀ (n + 1) - an) ^ 2 * (g : K) := hg
              _ = (newtonIterate f a₀ (n + 1) - an) ^ 2 * (g : K) := by
                have hcancel' : f.eval an +
                    (newtonIterate f a₀ (n + 1) - an) * f.derivative.eval an = 0 := by
                  simpa [e, d] using hcancel
                rw [hcancel', zero_add]
          have hvg : 0 ≤ v (g : K) := (hA _).mp g.property
          have hvn : (s + s) + (2 • qn) ≤ v en := by
            rw [hneval, v.map_mul, v.map_pow, hdeltaVal0]
            have hbase : 2 • (s + qn) = (s + s) + (2 • qn) := by
              simp [two_nsmul, add_assoc]
            rw [hbase]
            exact le_add_of_nonneg_right hvg
          have hsub : 2 • qn ≤ v en - (s + s) := by
            have hss : s + s ≠ ⊤ := by simp [hs]
            have hsub' :
                ((s + s) + (2 • qn)) - (s + s) ≤ v en - (s + s) :=
              (LinearOrderedAddCommGroupWithTop.sub_le_sub_iff_left_of_ne_top hss).mpr hvn
            calc
              2 • qn = ((s + s) + (2 • qn)) - (s + s) := by
                rw [sub_eq_add_neg]
                calc
                  2 • qn = 0 + (2 • qn) := by simp
                  _ = ((s + s) + -(s + s)) + (2 • qn) := by
                    rw [LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top hss]
                  _ = (s + s) + (2 • qn) + -(s + s) := by ac_rfl
              _ ≤ v en - (s + s) := hsub'
          have hdouble : (2 ^ n) • q₀ + (2 ^ n) • q₀ ≤ qn + qn :=
            add_le_add hqn hqn
          have hpow : (2 ^ (n + 1)) • q₀ =
              (2 ^ n) • q₀ + (2 ^ n) • q₀ := by
            have htwo : 2 ^ n * 2 = 2 ^ n + 2 ^ n := by omega
            rw [pow_succ, htwo, add_nsmul]
          dsimp [valuationExcess] at hsub ⊢
          rw [hpow]
          exact hdouble.trans (by simpa [two_nsmul] using hsub)
        exact ⟨han1, hdn1, hqn1⟩
  intro n
  have hn := hStep n
  refine ⟨hn.2.1, hn.2.2, ?_⟩
  let an : K := newtonIterate f a₀ n
  let d : K := f.derivative.eval an
  let e : K := f.eval an
  let qn : Γ := valuationExcess v f s an
  have hdelta : newtonIterate f a₀ (n + 1) - an =
      -(e * Ring.inverse d) := by
    simp [an, d, e, newtonIterate, newtonCorrection]
  have hdn : v d = s := by simpa [d] using hn.2.1
  rw [hdelta, Ring.inverse_eq_inv, v.map_neg, v.map_mul, AddValuation.map_inv, hdn]
  by_cases hev : v e = ⊤
  · have hev' : v (f.eval (newtonIterate f a₀ n)) = ⊤ := by simpa [e, an] using hev
    dsimp [qn, valuationExcess, s]
    rw [hev]
    simp [sub_eq_add_neg]
  · dsimp [qn, valuationExcess]
    have hval_formula : v e + -s = s + (v e + -(s + s)) := by
      rw [neg_add_rev]
      calc
        v e + -s = 0 + (v e + -s) := by simp
        _ = (s + -s) + (v e + -s) := by
          simp [LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top hs]
        _ = s + (v e + (-s + -s)) := by ac_rfl
    simpa [e, an, sub_eq_add_neg] using hval_formula

/-- The valuation Newton form of Hensel's lemma, including the integral root condition. -/
private theorem hensel_cauchy_of_top {K Γ : Type*} [Field K]
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
      have hmn : m ≤ n ∨ n ≤ m := le_total m n
      rcases hmn with hmn | hnm
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
          have heq : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 = 0 := by
            exact congrArg Multiplicative.ofAdd hdual
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
          have heq : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 = 0 := by
            exact congrArg Multiplicative.ofAdd hdual
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


set_option maxHeartbeats 2000000 in
private theorem hensel_newton_data {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ)
    (A : Subring K) (hA : IsValuationSubring A v) (f : K[X])
    (hf : PolynomialCoefficientsInSubring A f) (a₀ : K) (ha₀ : a₀ ∈ A)
    (hineq : v (f.eval a₀) > v (f.derivative.eval a₀) + v (f.derivative.eval a₀))
    (hderiv : v (f.derivative.eval a₀) ≠ ⊤)
    (hcomplete : Chapter09NonarchimedeanComplete v)
    (hcofinal : Chapter09ImageDoublingCofinal v
      (valuationExcess v f (v (f.derivative.eval a₀)) a₀)) :
    ∃ a : K, a ∈ A ∧ f.eval a = 0 ∧
      v (a - a₀) = v (f.derivative.eval a₀) +
        (v (f.eval a₀) -
          (v (f.derivative.eval a₀) + v (f.derivative.eval a₀))) ∧
      v (f.derivative.eval a) = v (f.derivative.eval a₀) := by
  let hvalued : Valued K (Multiplicative Γᵒᵈ) := Valued.mk' v.toValuation
  let s : Γ := v (f.derivative.eval a₀)
  let q₀ : Γ := v (f.eval a₀) - (s + s)
  have hs : s ≠ ⊤ := by simpa [s] using hderiv
  have hq₀pos : 0 < q₀ := by
    dsimp [q₀, s]
    exact LinearOrderedAddCommGroupWithTop.sub_pos.mpr (Or.inl hineq)
  have hfd : PolynomialCoefficientsInSubring A f.derivative := by
    intro n
    rw [coeff_derivative]
    exact A.mul_mem (hf (n + 1))
      (by simpa using intCast_mem A (n + 1 : ℤ))
  have hs_nonneg : 0 ≤ s := by
    apply (hA _).mp
    rw [eval_eq_sum_range]
    apply A.sum_mem
    intro n hn
    exact A.mul_mem (hfd n) (A.pow_mem ha₀ n)
  have hmem : ∀ n : ℕ, newtonIterate f a₀ n ∈ A := by
    intro n
    induction n with
    | zero => exact ha₀
    | succ n ih =>
        let an : K := newtonIterate f a₀ n
        let d : K := f.derivative.eval an
        let e : K := f.eval an
        let qn : Γ := valuationExcess v f s an
        have hn := valuation_newton_induction v A hA f hf a₀ ha₀ hineq hderiv n
        have hdn : v d = s := by simpa [d] using hn.1
        have hqn : (2 ^ n) • q₀ ≤ qn := by simpa [qn] using hn.2.1
        have hqnonneg : 0 ≤ qn :=
          (nsmul_nonneg hq₀pos.le _).trans hqn
        have hve : s + s ≤ v e := by
          have hsub : 0 ≤ v e - (s + s) := by
            simpa [qn, valuationExcess, e] using hqnonneg
          have hss : s + s ≠ ⊤ := by simp [hs]
          calc
            s + s = (s + s) + 0 := by simp
            _ ≤ (s + s) + (v e - (s + s)) := add_le_add_right hsub _
            _ = v e := by
              rw [sub_eq_add_neg]
              rw [show s + s + (v e + -(s + s)) =
                  (s + s + -(s + s)) + v e by ac_rfl]
              rw [LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top hss,
                zero_add]
        have hse : s ≤ v e :=
          (le_add_of_nonneg_right hs_nonneg).trans hve
        have hcorrmem : e * Ring.inverse d ∈ A := by
          apply (hA _).mpr
          rw [Ring.inverse_eq_inv, v.map_mul, AddValuation.map_inv, hdn]
          have hsub : 0 ≤ v e - s := by
            apply (add_le_add_iff_right_of_ne_top hs).mp
            calc
              s + 0 = s := by simp
              _ ≤ v e := hse
              _ = s + (v e - s) := by
                rw [sub_eq_add_neg]
                symm
                calc
                  s + (v e + -s) = (s + -s) + v e := by ac_rfl
                  _ = v e := by
                    rw [LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top hs,
                      zero_add]
          simpa [sub_eq_add_neg] using hsub
        have hrec : newtonIterate f a₀ (n + 1) =
            an - e * Ring.inverse d := by
          simp [an, d, e, newtonIterate, newtonCorrection]
        rw [hrec]
        exact A.sub_mem ih hcorrmem
  let u : ℕ → K := newtonIterate f a₀
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
  have himage_add_sub : ∀ {r₁ r₂ r₃ : Γ},
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
  have hfoo_image (γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass v.toValuation))ˣ) :
      ∃ x : K, x ≠ 0 ∧ v x = hfoo γ := by
    obtain ⟨x, hx⟩ :=
      MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective
        (.ofClass v.toValuation) γ.1
    have hx0 : x ≠ 0 := by
      intro hx0
      have hzero : (γ.1 : MonoidWithZeroHom.ValueGroup₀ (.ofClass v.toValuation)) = 0 := by
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
      (fun z : Multiplicative Γᵒᵈ =>
        OrderDual.ofDual (Multiplicative.toAdd z)) hxeq
  have hqimage : q₀ ≠ ⊤ →
      ∃ z : K, z ≠ 0 ∧ v z = q₀ := by
    intro hqtop
    have heval_top : v (f.eval a₀) ≠ ⊤ := by
      intro heval_top
      apply hqtop
      dsimp [q₀]
      rw [sub_eq_add_neg, heval_top, top_add]
    have heval0 : f.eval a₀ ≠ 0 := (AddValuation.ne_top_iff v).mp heval_top
    have hderiv0 : f.derivative.eval a₀ ≠ 0 :=
      (AddValuation.ne_top_iff v).mp hderiv
    refine ⟨f.eval a₀ * (f.derivative.eval a₀)⁻¹ *
      (f.derivative.eval a₀)⁻¹, by simp [heval0, hderiv0], ?_⟩
    rw [v.map_mul, v.map_mul, AddValuation.map_inv]
    simp [q₀, s, sub_eq_add_neg, add_assoc]
  have hpowtop : ∀ j : ℕ, (2 ^ j) • (⊤ : Γ) = ⊤ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [pow_succ, show 2 ^ j * 2 = 2 ^ j + 2 ^ j by omega,
          add_nsmul, ih]
        simp
  have htop : ∀ γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass v.toValuation))ˣ,
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        hfoo γ + q₀ ≤ v (u (n + 1) - u n) := by
    intro γ
    let t : Γ := hfoo γ
    have hqtop : q₀ = ⊤ ∨ q₀ ≠ ⊤ := eq_or_ne q₀ ⊤
    rcases hqtop with hqtop | hqtop
    · refine ⟨0, fun n _ => ?_⟩
      have hnstep := valuation_newton_induction v A hA f hf a₀ ha₀ hineq hderiv n
      have hqn : valuationExcess v f s (u n) = ⊤ := by
        apply top_unique
        have hnineq := hnstep.2.1
        rw [show (2 ^ n) • q₀ = ⊤ by rw [hqtop, hpowtop n]] at hnineq
        simpa [u, s, q₀] using hnineq
      have hcorr : v (u (n + 1) - u n) = ⊤ := by
        rw [hnstep.2.2, hqn]
        simp
      rw [hqtop, add_top, hcorr]
    · obtain ⟨N, hN⟩ := hcofinal (t + q₀ - s) (by
        obtain ⟨x, hx0, hxt⟩ := hfoo_image γ
        exact (himage_add_sub ⟨x, hx0, hxt⟩ (hqimage hqtop)
          ⟨f.derivative.eval a₀, (AddValuation.ne_top_iff v).mp hderiv, rfl⟩))
      refine ⟨N, fun n hn => ?_⟩
      have hpow : 2 ^ N ≤ 2 ^ n := by
        exact Nat.pow_le_pow_right (by norm_num) hn
      have hsmul : (2 ^ N) • q₀ ≤ (2 ^ n) • q₀ :=
        nsmul_le_nsmul_left hq₀pos.le hpow
      have hγ : t + q₀ ≤ s + (2 ^ n) • q₀ := by
        calc
          t + q₀ = s + (t + q₀ - s) := by
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
              (LinearOrderedAddCommGroupWithTop.add_neg_cancel_left_of_ne_top hs
                (t + q₀)).symm
          _ ≤ s + (2 ^ N) • q₀ := by
            simpa [valuationExcess, add_comm] using add_le_add_left hN s
          _ ≤ s + (2 ^ n) • q₀ := by
            simpa [add_comm] using add_le_add_left hsmul s
      have hnstep := valuation_newton_induction v A hA f hf a₀ ha₀ hineq hderiv n
      rw [hnstep.2.2]
      apply hγ.trans
      simpa [s, q₀, valuationExcess, add_comm] using add_le_add_left hnstep.2.1 s
  have hCauchy : @CauchySeq K ℕ (Chapter09ValuationUniformSpace v) inferInstance u :=
    hensel_cauchy_of_top v hcomplete u q₀ hq₀pos htop
  obtain ⟨a, ha_lim⟩ := @cauchySeq_tendsto_of_complete K ℕ
    (Chapter09ValuationUniformSpace v) inferInstance hcomplete (u := u) hCauchy
  have hmemA : a ∈ A := by
    apply (hA _).mpr
    by_contra hnot
    have hneg : v a < 0 := lt_of_not_ge hnot
    have haVal : v.toValuation a ≠ 0 := by
      intro hz
      have hz' : v a = ⊤ := by
        change Multiplicative.ofAdd (OrderDual.toDual (v a)) = 0 at hz
        have hzdual : OrderDual.toDual (v a) = (⊥ : Γᵒᵈ) := by
          have hh := congrArg Multiplicative.toAdd hz
          exact hh
        exact (OrderDual.toDual_eq_bot Γ).mp hzdual
      exact (not_lt_of_ge (le_top : (0 : Γ) ≤ ⊤)) (hz' ▸ hneg)
    have hloc := @Valued.locally_const K _ (Multiplicative Γᵒᵈ) _ hvalued a haVal
    have hev : ∀ᶠ n : ℕ in Filter.atTop,
        v.toValuation (u n) = v.toValuation a := ha_lim.eventually hloc
    obtain ⟨N, hN⟩ := (Filter.eventually_atTop.1 hev)
    have hEq := hN N (le_rfl)
    have hEq' : v (u N) = v a := by
      have hh := congrArg (fun z : Multiplicative Γᵒᵈ =>
          OrderDual.ofDual (Multiplicative.toAdd z)) hEq
      simpa [AddValuation.toValuation_apply] using hh
    have hnonneg : 0 ≤ v (u N) := (hA _).mp (hmem N)
    exact (not_lt_of_ge (hEq' ▸ hnonneg)) hneg
  have hbound : ∀ n : ℕ,
      s + s + (2 ^ n) • q₀ ≤ v (f.eval (u n)) := by
    intro n
    have hn := valuation_newton_induction v A hA f hf a₀ ha₀ hineq hderiv n
    let e : K := f.eval (u n)
    let qn : Γ := valuationExcess v f s (u n)
    have hqn : (2 ^ n) • q₀ ≤ qn := by simpa [qn] using hn.2.1
    have hss : s + s ≠ ⊤ := by simp [hs]
    calc
      s + s + (2 ^ n) • q₀ ≤ s + s + qn := add_le_add_right hqn _
      _ = v e := by
        rw [show qn = v e - (s + s) by rfl, sub_eq_add_neg]
        rw [show s + s + (v e + -(s + s)) =
            (s + s + -(s + s)) + v e by ac_rfl]
        rw [LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top hss,
          zero_add]
  have hEval : Filter.Tendsto (fun n : ℕ => f.eval (u n)) Filter.atTop (nhds (0 : K)) := by
    rw [(@Valued.hasBasis_nhds_zero K _ (Multiplicative Γᵒᵈ) _ hvalued).tendsto_right_iff]
    intro γ _
    by_cases hqtop : q₀ = ⊤
    · filter_upwards [] with n
      have hnstep := valuation_newton_induction v A hA f hf a₀ ha₀ hineq hderiv n
      have hqn : valuationExcess v f s (u n) = ⊤ := by
        apply top_unique
        have hnineq := hnstep.2.1
        rw [show (2 ^ n) • q₀ = ⊤ by rw [hqtop, hpowtop n]] at hnineq
        simpa [u, s, q₀] using hnineq
      have hve : v (f.eval (u n)) = ⊤ := by
        by_contra hve
        have hqne : valuationExcess v f s (u n) ≠ ⊤ := by
          intro hqne
          have hss : s + s ≠ ⊤ := by simp [hs]
          have hcancel : valuationExcess v f s (u n) + (s + s) =
              v (f.eval (u n)) := by
            dsimp [valuationExcess]
            rw [sub_eq_add_neg]
            calc
              (v (f.eval (u n)) + -(s + s)) + (s + s) =
                  v (f.eval (u n)) + (-(s + s) + (s + s)) := by ac_rfl
              _ = v (f.eval (u n)) := by
                rw [LinearOrderedAddCommGroupWithTop.neg_add_cancel_of_ne_top hss,
                  add_zero]
          rw [hqne] at hcancel
          have hve' : v (f.eval (u n)) = ⊤ := by
            simpa using hcancel.symm
          exact hve hve'
        exact hqne hqn
      rw [(AddValuation.top_iff v).mp hve]
      simp
    · let t : Γ := hfoo γ
      have ht_top : t ≠ ⊤ := by
        intro htop
        change OrderDual.ofDual (Multiplicative.toAdd
          (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)) = (⊤ : Γ) at htop
        have hdual : Multiplicative.toAdd
            (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) = (⊥ : Γᵒᵈ) :=
          (OrderDual.ofDual_eq_top Γ).mp htop
        have heq : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 = 0 := by
          exact congrArg Multiplicative.ofAdd hdual
        have hγzero : (γ.1 : MonoidWithZeroHom.ValueGroup₀ (.ofClass v.toValuation)) = 0 := by
          apply MonoidWithZeroHom.ValueGroup₀.embedding_injective
          exact heq
        exact (Units.ne_zero γ) hγzero
      have hss : s + s ≠ ⊤ := by simp [hs]
      let ss : Γ := s + s
      have hss : ss ≠ ⊤ := by simp [ss, hs]
      let r : Γ := t - ss
      have hr_top : r ≠ ⊤ := by
        dsimp [r]
        intro hr
        apply ht_top
        calc
          t = ss + (t - ss) := by
            rw [sub_eq_add_neg]
            symm
            calc
              ss + (t + -ss) = (ss + -ss) + t := by
                calc
                  ss + (t + -ss) = (ss + t) + -ss :=
                    (add_assoc ss t (-ss)).symm
                  _ = ss + (t + -ss) :=
                    add_assoc ss t (-ss)
                  _ = ss + (-ss + t) :=
                    congrArg (fun z : Γ => ss + z) (add_comm t (-ss))
                  _ = (ss + -ss) + t :=
                    (add_assoc ss (-ss) t).symm
              _ = t := by
                rw [LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top hss,
                  zero_add]
          _ = ⊤ := by rw [hr]; simp
      obtain ⟨N, hN⟩ := hcofinal (r + q₀) (by
        obtain ⟨x, hx0, hxt⟩ := hfoo_image γ
        have hss_image : ∃ z : K, z ≠ 0 ∧ v z = ss := by
          refine ⟨f.derivative.eval a₀ * f.derivative.eval a₀,
            mul_ne_zero ((AddValuation.ne_top_iff v).mp hderiv)
              ((AddValuation.ne_top_iff v).mp hderiv), ?_⟩
          rw [v.map_mul]
        simpa [r, ss, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
          himage_add_sub ⟨x, hx0, hxt⟩ (hqimage hqtop) hss_image)
      refine Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩
      have hpow : 2 ^ N ≤ 2 ^ n := by
        exact Nat.pow_le_pow_right (by norm_num) hn
      have hsmul : (2 ^ N) • q₀ ≤ (2 ^ n) • q₀ :=
        nsmul_le_nsmul_left hq₀pos.le hpow
      have hrpow : r + q₀ ≤ (2 ^ n) • q₀ :=
        hN.trans hsmul
      have hrstrict : r < r + q₀ := by
        simpa only [add_zero] using (add_lt_add_iff_right_of_ne_top hr_top).2 hq₀pos
      have hstrict : t < ss + (2 ^ n) • q₀ := by
        calc
          t = ss + (t - ss) := by
            rw [sub_eq_add_neg]
            symm
            calc
              ss + (t + -ss) = (ss + -ss) + t := by
                calc
                  ss + (t + -ss) = (ss + t) + -ss :=
                    (add_assoc ss t (-ss)).symm
                  _ = ss + (t + -ss) :=
                    add_assoc ss t (-ss)
                  _ = ss + (-ss + t) :=
                    congrArg (fun z : Γ => ss + z) (add_comm t (-ss))
                  _ = (ss + -ss) + t :=
                    (add_assoc ss (-ss) t).symm
              _ = t := by
                rw [LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top hss,
                  zero_add]
          _ < ss + ((t - ss) + q₀) := by
            exact (add_lt_add_iff_right_of_ne_top hss).2 hrstrict
          _ ≤ ss + (2 ^ n) • q₀ := add_le_add_right hrpow _
      apply hval_lt_iff _ γ |>.mpr
      have hb : ss + (2 ^ n) • q₀ ≤ v (f.eval (u n)) := by
        dsimp [ss]
        exact hbound n
      exact lt_of_lt_of_le hstrict hb
  have hbase : v (u 1 - u 0) = s + q₀ := by
    have hn0 := valuation_newton_induction v A hA f hf a₀ ha₀ hineq hderiv 0
    have hh := hn0.2.2
    dsimp [u, s, q₀, valuationExcess] at hh ⊢
    simpa [newtonIterate] using hh
  have hdisp_seq : ∀ n : ℕ, 1 ≤ n → v (u n - a₀) = s + q₀ := by
    intro n hn
    by_cases hqtop : q₀ = ⊤
    · have hiter : ∀ k : ℕ, u k = a₀ := by
        intro k
        induction k with
        | zero => simp [u, newtonIterate]
        | succ k ih =>
            have hk := valuation_newton_induction v A hA f hf a₀ ha₀ hineq hderiv k
            have hqk : (2 ^ k) • q₀ ≤ valuationExcess v f s (u k) := by
              simpa [u, s] using hk.2.1
            have hqk_top : valuationExcess v f s (u k) = ⊤ := by
              apply top_unique
              have hpowtop : ∀ j : ℕ, (2 ^ j) • (⊤ : Γ) = ⊤ := by
                intro j
                induction j with
                | zero => simp
                | succ j ih =>
                    rw [pow_succ, show 2 ^ j * 2 = 2 ^ j + 2 ^ j by omega,
                      add_nsmul, ih]
                    simp
              calc
                (⊤ : Γ) = (2 ^ k) • q₀ := by rw [hqtop, hpowtop k]
                _ ≤ valuationExcess v f s (u k) := hqk
            have hinc_top : v (u (k + 1) - u k) = ⊤ := by
              have hinc := hk.2.2
              simpa [s, u, hqk_top] using hinc
            have hinc_zero : u (k + 1) - u k = 0 := by
              by_contra hne
              exact (v.ne_top_iff.mpr hne) hinc_top
            have hinc_eq : u (k + 1) = u k := sub_eq_zero.mp hinc_zero
            rw [hinc_eq, ih]
      rw [hiter n, sub_self, hqtop]
      simp
    · induction n, hn using Nat.le_induction with
      | base =>
          simpa [u, newtonIterate] using hbase
      | succ n hn ih =>
          have hnstep := valuation_newton_induction v A hA f hf a₀ ha₀ hineq hderiv n
          have hqn : (2 ^ n) • q₀ ≤ valuationExcess v f s (u n) := by
            simpa [u] using hnstep.2.1
          have hqgt : q₀ < (2 ^ n) • q₀ := by
            have hp : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
            have hcoef : 2 ^ n - 1 ≠ 0 := by omega
            have hpos : 0 < (2 ^ n - 1) • q₀ := nsmul_pos hq₀pos hcoef
            calc
              q₀ = 0 + q₀ := by simp
              _ < (2 ^ n - 1) • q₀ + q₀ := by
                exact (add_lt_add_iff_left_of_ne_top hqtop).2 hpos
              _ = (2 ^ n) • q₀ := by
                rw [← succ_nsmul]
                congr 1 ; omega
          have hincgt : s + q₀ < v (u (n + 1) - u n) := by
            have hsq : s + q₀ < s + valuationExcess v f s (u n) := by
              exact (add_lt_add_iff_right_of_ne_top hs).2 (hqgt.trans_le hqn)
            have hinc_eq : s + valuationExcess v f s (u n) =
                v (u (n + 1) - u n) := by
              simpa [s, u] using hnstep.2.2.symm
            exact hsq.trans_eq hinc_eq
          have hsum : u (n + 1) - a₀ =
              (u (n + 1) - u n) + (u n - a₀) := by ring
          rw [hsum]
          have hne : v (u (n + 1) - u n) ≠ v (u n - a₀) := by
            rw [ih]
            exact ne_of_gt hincgt
          rw [valuation_unequal_value_rigidity v hne, ih,
            min_eq_right (le_of_lt hincgt)]
  have hdisp : v (a - a₀) = s + q₀ := by
    have hsub_lim : Filter.Tendsto (fun n : ℕ => u n - a₀) Filter.atTop
        (nhds (a - a₀)) := by
      exact (continuous_id.sub continuous_const).continuousAt.tendsto.comp ha_lim
    have hval_lim : Filter.Tendsto
        (fun n : ℕ => v.toValuation.restrict (u n - a₀)) Filter.atTop
        (nhds (v.toValuation.restrict (a - a₀))) := by
      have hcont : Continuous
          (v.toValuation.restrict : K →
            MonoidWithZeroHom.ValueGroup₀ (.ofClass v.toValuation)) := by
        exact @Valued.continuous_valuation K _ (Multiplicative Γᵒᵈ) _ hvalued
      apply Filter.Tendsto.congr' (Filter.Eventually.of_forall (fun n => rfl))
      exact (hcont.continuousAt (x := a - a₀)).tendsto.comp hsub_lim
    have hval_event : ∀ᶠ n : ℕ in Filter.atTop,
        v.toValuation.restrict (u n - a₀) =
          v.toValuation.restrict (u 1 - u 0) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      apply MonoidWithZeroHom.ValueGroup₀.embedding_injective
      rw [Valuation.embedding_restrict, Valuation.embedding_restrict]
      have hh := hdisp_seq n hn
      have hh0 := hbase
      have hadd : v (u n - a₀) = v (u 1 - u 0) := hh.trans hh0.symm
      exact congrArg (fun z : Γ => Multiplicative.ofAdd (OrderDual.toDual z)) hadd
    have hval_const : Filter.Tendsto
        (fun n : ℕ => v.toValuation.restrict (u n - a₀)) Filter.atTop
        (nhds (v.toValuation.restrict (u 1 - u 0))) :=
      Filter.Tendsto.congr' (Filter.EventuallyEq.symm hval_event)
        tendsto_const_nhds
    have hval_eq := tendsto_nhds_unique hval_lim hval_const
    have hval_eq' := congrArg MonoidWithZeroHom.ValueGroup₀.embedding hval_eq
    rw [Valuation.embedding_restrict, Valuation.embedding_restrict] at hval_eq'
    have hadd := congrArg (fun z : Multiplicative Γᵒᵈ =>
        OrderDual.ofDual (Multiplicative.toAdd z)) hval_eq'
    have hEqAdd : v (a - a₀) = v (u 1 - u 0) := by
      simpa [AddValuation.toValuation_apply] using hadd
    exact hEqAdd.trans hbase
  have hzero : f.eval a = 0 := by
    have hEval' : Filter.Tendsto (fun n : ℕ => f.eval (u n)) Filter.atTop
        (nhds (f.eval a)) :=
      (Polynomial.continuousAt f (a := a)).tendsto.comp ha_lim
    have heq : (0 : K) = f.eval a := tendsto_nhds_unique hEval hEval'
    exact heq.symm
  have hderivA : v (f.derivative.eval a) = s := by
    have hder_lim : Filter.Tendsto
        (fun n : ℕ => f.derivative.eval (u n)) Filter.atTop
        (nhds (f.derivative.eval a)) :=
      (Polynomial.continuousAt f.derivative (a := a)).tendsto.comp ha_lim
    have hval_lim : Filter.Tendsto
        (fun n : ℕ => v.toValuation.restrict (f.derivative.eval (u n)))
          Filter.atTop
        (nhds (v.toValuation.restrict (f.derivative.eval a))) := by
      have hcont : Continuous
          (v.toValuation.restrict : K →
            MonoidWithZeroHom.ValueGroup₀ (.ofClass v.toValuation)) := by
        exact @Valued.continuous_valuation K _ (Multiplicative Γᵒᵈ) _ hvalued
      apply Filter.Tendsto.congr' (Filter.Eventually.of_forall (fun n => rfl))
      exact (hcont.continuousAt (x := f.derivative.eval a)).tendsto.comp hder_lim
    have hval_event : ∀ᶠ n : ℕ in Filter.atTop,
        v.toValuation.restrict (f.derivative.eval (u n)) =
          v.toValuation.restrict (f.derivative.eval a₀) := by
      filter_upwards [] with n
      apply MonoidWithZeroHom.ValueGroup₀.embedding_injective
      rw [Valuation.embedding_restrict, Valuation.embedding_restrict]
      have hn := valuation_newton_induction v A hA f hf a₀ ha₀ hineq hderiv n
      have hh : v (f.derivative.eval (u n)) =
          v (f.derivative.eval a₀) := by
        simpa [u] using hn.1
      exact congrArg (fun z : Γ => Multiplicative.ofAdd (OrderDual.toDual z)) hh
    have hval_const : Filter.Tendsto
        (fun n : ℕ => v.toValuation.restrict (f.derivative.eval (u n)))
          Filter.atTop
        (nhds (v.toValuation.restrict (f.derivative.eval a₀))) :=
      Filter.Tendsto.congr' (Filter.EventuallyEq.symm hval_event)
        tendsto_const_nhds
    have hval_eq := tendsto_nhds_unique hval_lim hval_const
    have hval_eq' := congrArg MonoidWithZeroHom.ValueGroup₀.embedding hval_eq
    rw [Valuation.embedding_restrict, Valuation.embedding_restrict] at hval_eq'
    have hadd := congrArg (fun z : Multiplicative Γᵒᵈ =>
        OrderDual.ofDual (Multiplicative.toAdd z)) hval_eq'
    have hEqAdd : v (f.derivative.eval a) =
        v (f.derivative.eval a₀) := by
      simpa [AddValuation.toValuation_apply] using hadd
    exact hEqAdd.trans (by rfl)
  exact ⟨a, hmemA, hzero, (by simpa [s, q₀] using hdisp), hderivA⟩



theorem hensel_newton_form_of_doubling_cofinal {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ)
    (A : Subring K) (hA : IsValuationSubring A v) (f : K[X])
    (hf : PolynomialCoefficientsInSubring A f) (a₀ : K) (ha₀ : a₀ ∈ A)
    (hineq : v (f.eval a₀) > v (f.derivative.eval a₀) + v (f.derivative.eval a₀))
    (hderiv : v (f.derivative.eval a₀) ≠ ⊤)
    (hcomplete : Chapter09NonarchimedeanComplete v)
    (hcofinal : Chapter09DoublingCofinal
      (valuationExcess v f (v (f.derivative.eval a₀)) a₀)) :
    ∃! a : K,
      a ∈ A ∧ f.eval a = 0 ∧
      v (a - a₀) > v (f.derivative.eval a₀) ∧
          v (a - a₀) = v (f.eval a₀) - v (f.derivative.eval a₀) := by
  let s : Γ := v (f.derivative.eval a₀)
  let q₀ : Γ := v (f.eval a₀) - (s + s)
  have hs : s ≠ ⊤ := by simpa [s] using hderiv
  have hq₀pos : 0 < q₀ := by
    dsimp [q₀, s]
    exact LinearOrderedAddCommGroupWithTop.sub_pos.mpr (Or.inl hineq)
  obtain ⟨a, haA, hfa, hdisp, hderivA⟩ :=
    hensel_newton_data v A hA f hf a₀ ha₀ hineq hderiv hcomplete
      (fun γ _ => hcofinal γ)
  have hdisp' : v (a - a₀) = s + q₀ := by
    simpa [s, q₀] using hdisp
  have hstrict : s < v (a - a₀) := by
    rw [hdisp']
    simpa using (add_lt_add_iff_right_of_ne_top hs).2 hq₀pos
  have hexact : v (a - a₀) = v (f.eval a₀) - s := by
    rw [hdisp']
    have hval_formula : v (f.eval a₀) + -s =
        s + (v (f.eval a₀) + -(s + s)) := by
      rw [neg_add_rev]
      calc
        v (f.eval a₀) + -s = 0 + (v (f.eval a₀) + -s) := by simp
        _ = (s + -s) + (v (f.eval a₀) + -s) := by
          simp [LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top hs]
        _ = s + (v (f.eval a₀) + (-s + -s)) := by ac_rfl
    simpa [s, q₀, sub_eq_add_neg] using hval_formula.symm
  refine ⟨a, ⟨haA, hfa, hstrict, hexact⟩, ?_⟩
  intro b hb
  by_contra hab
  have hne : b - a ≠ 0 := sub_ne_zero.mpr hab
  have hba_val : s < v (b - a) := by
    have h1 : s < v (b - a₀) := hb.2.2.1
    have h2 : s < v (-(a - a₀)) := by
      rw [v.map_neg]
      exact hstrict
    calc
      s < min (v (b - a₀)) (v (-(a - a₀))) := (lt_min_iff).2 ⟨h1, h2⟩
      _ ≤ v ((b - a₀) + (-(a - a₀))) :=
        valuation_strong_triangle v (b - a₀) (-(a - a₀))
      _ = v (b - a) := by congr 1 ; ring
  have hTaylorIntegral : ∀ (p : K[X]), PolynomialCoefficientsInSubring A p →
      ∀ (x y : K), x ∈ A → y ∈ A → ∃ g : A,
        p.eval (x + y) = p.eval x + y * p.derivative.eval x + y ^ 2 * (g : K) := by
    intro p hp x y hx hy
    let hpcoeff : (p.coeffs : Set K) ⊆ A := by
      intro c hc
      rcases (Polynomial.mem_coeffs_iff.mp hc) with ⟨n, hn, rfl⟩
      exact hp n
    let pA : A[X] := p.toSubring A hpcoeff
    obtain ⟨g, hg⟩ := taylor_second_order pA ⟨x, hx⟩ ⟨y, hy⟩
    refine ⟨g, ?_⟩
    have hmap := congrArg (fun z : A => (z : K)) hg
    have hpmap : pA.map (Subring.subtype A) = p := by
      exact Polynomial.map_toSubring p A hpcoeff
    have heval (z : A) : ((pA.eval z : A) : K) = p.eval (z : K) := by
      have h := Polynomial.eval_map_apply (p := pA) (Subring.subtype A) z
      rw [hpmap] at h
      exact h.symm
    have hdermap : pA.derivative.map (Subring.subtype A) = p.derivative := by
      rw [← Polynomial.derivative_map, hpmap]
    have hderval (z : A) : ((pA.derivative.eval z : A) : K) =
        p.derivative.eval (z : K) := by
      have h := Polynomial.eval_map_apply (p := pA.derivative) (Subring.subtype A) z
      rw [hdermap] at h
      exact h.symm
    calc
      p.eval (x + y) = ((pA.eval (⟨x, hx⟩ + ⟨y, hy⟩) : A) : K) := by
        simpa using (heval (⟨x, hx⟩ + ⟨y, hy⟩)).symm
      _ = ((pA.eval ⟨x, hx⟩ + ⟨y, hy⟩ *
          pA.derivative.eval ⟨x, hx⟩ +
          ⟨y, hy⟩ ^ 2 * g : A) : K) := hmap
      _ = p.eval x + y * p.derivative.eval x + y ^ 2 * (g : K) := by
        simp [heval, hderval, Subring.coe_add, Subring.coe_mul]
  have hmem_h : b - a ∈ A := A.sub_mem hb.1 haA
  obtain ⟨g, hg⟩ := hTaylorIntegral f hf a (b - a) haA hmem_h
  have hrootrel : 0 = (b - a) * f.derivative.eval a +
      (b - a) ^ 2 * (g : K) := by
    calc
      0 = f.eval b := hb.2.1.symm
      _ = f.eval (a + (b - a)) := by rw [show a + (b - a) = b by ring]
      _ = f.eval a + (b - a) * f.derivative.eval a +
          (b - a) ^ 2 * (g : K) := hg
      _ = (b - a) * f.derivative.eval a + (b - a) ^ 2 * (g : K) := by
        rw [hfa]
        simp
  have hfactor : (b - a) *
      (f.derivative.eval a + (b - a) * (g : K)) = 0 := by
    calc
      (b - a) * (f.derivative.eval a + (b - a) * (g : K)) =
          (b - a) * f.derivative.eval a + (b - a) ^ 2 * (g : K) := by ring
      _ = 0 := hrootrel.symm
  have hsumzero : f.derivative.eval a + (b - a) * (g : K) = 0 := by
    rcases (mul_eq_zero.mp hfactor) with hzero | hsum
    · exact (hne hzero).elim
    · exact hsum
  have hg_nonneg : 0 ≤ v (g : K) := (hA _).mp g.property
  have hprodgt : s < v ((b - a) * (g : K)) := by
    rw [v.map_mul]
    exact hba_val.trans_le (le_add_of_nonneg_right hg_nonneg)
  have hneval : v (f.derivative.eval a) ≠ v ((b - a) * (g : K)) := by
    rw [hderivA]
    exact ne_of_lt hprodgt
  have hsumval : v (f.derivative.eval a + (b - a) * (g : K)) = s := by
    calc
      v (f.derivative.eval a + (b - a) * (g : K)) =
          min (v (f.derivative.eval a)) (v ((b - a) * (g : K))) :=
        valuation_unequal_value_rigidity v hneval
      _ = s := by rw [hderivA, min_eq_left (le_of_lt hprodgt)]
  have hstop : s = ⊤ := by
    calc
      s = v (f.derivative.eval a + (b - a) * (g : K)) := hsumval.symm
      _ = ⊤ := by rw [hsumzero, v.map_zero]
  exact hs hstop


/-- The valuation form of Hensel's lemma for a complete rank-one valuation. -/
theorem hensel_newton_form {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ)
    [Valuation.RankOne v.toValuation]
    (A : Subring K) (hA : IsValuationSubring A v) (f : K[X])
    (hf : PolynomialCoefficientsInSubring A f) (a₀ : K) (ha₀ : a₀ ∈ A)
    (hineq : v (f.eval a₀) > v (f.derivative.eval a₀) + v (f.derivative.eval a₀))
    (hcomplete : Chapter09NonarchimedeanComplete v) :
    ∃! a : K,
      f.eval a = 0 ∧
        v (a - a₀) > v (f.derivative.eval a₀) ∧
        v (a - a₀) = v (f.eval a₀) - v (f.derivative.eval a₀) := by
  sorry

/-- The exact displacement in the valuation Newton form under explicit cofinality. -/
theorem hensel_newton_exact_displacement_of_doubling_cofinal {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ)
    (A : Subring K) (hA : IsValuationSubring A v) (f : K[X])
    (hf : PolynomialCoefficientsInSubring A f) (a₀ : K) (ha₀ : a₀ ∈ A)
    (hineq : v (f.eval a₀) > v (f.derivative.eval a₀) + v (f.derivative.eval a₀))
    (hderiv : v (f.derivative.eval a₀) ≠ ⊤)
    (hcomplete : Chapter09NonarchimedeanComplete v)
    (hcofinal : Chapter09DoublingCofinal
      (valuationExcess v f (v (f.derivative.eval a₀)) a₀)) :
    ∃ a : K,
      a ∈ A ∧ f.eval a = 0 ∧
        v (a - a₀) = v (f.eval a₀) - v (f.derivative.eval a₀) := by
  obtain ⟨a, ha, _⟩ :=
    hensel_newton_form_of_doubling_cofinal v A hA f hf a₀ ha₀ hineq hderiv hcomplete hcofinal
  exact ⟨a, ha.1, ha.2.1, ha.2.2.2⟩

/-- The exact displacement supplied by the rank-one Newton form. -/
theorem hensel_newton_exact_displacement {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ)
    [Valuation.RankOne v.toValuation]
    (A : Subring K) (hA : IsValuationSubring A v) (f : K[X])
    (hf : PolynomialCoefficientsInSubring A f) (a₀ : K) (ha₀ : a₀ ∈ A)
    (hineq : v (f.eval a₀) > v (f.derivative.eval a₀) + v (f.derivative.eval a₀))
    (hcomplete : Chapter09NonarchimedeanComplete v) :
    ∃ a : K,
      f.eval a = 0 ∧
        v (a - a₀) = v (f.eval a₀) - v (f.derivative.eval a₀) := by
  obtain ⟨a, ha, _⟩ :=
    hensel_newton_form v A hA f hf a₀ ha₀ hineq hcomplete
  exact ⟨a, ha.1, ha.2.2⟩

/-- The Newton corrections tend to the top of the value group. -/
theorem valuation_newton_corrections_tend_to_top_of_doubling_cofinal {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ)
    (A : Subring K) (hA : IsValuationSubring A v) (f : K[X])
    (hf : PolynomialCoefficientsInSubring A f) (a₀ : K) (ha₀ : a₀ ∈ A)
    (hineq : v (f.eval a₀) > v (f.derivative.eval a₀) + v (f.derivative.eval a₀))
    (hderiv : v (f.derivative.eval a₀) ≠ ⊤)
    (hcomplete : Chapter09NonarchimedeanComplete v)
    (hcofinal : Chapter09DoublingCofinal
      (valuationExcess v f (v (f.derivative.eval a₀)) a₀)) :
    TendsToTop (fun n => v (newtonIterate f a₀ (n + 1) - newtonIterate f a₀ n)) := by
  have _hcomplete := hcomplete
  dsimp [TendsToTop]
  let s : Γ := v (f.derivative.eval a₀)
  let q₀ : Γ := v (f.eval a₀) - (s + s)
  have hs : s ≠ ⊤ := by
    simpa [s] using hderiv
  have hq₀ : 0 < q₀ := by
    dsimp [q₀, s]
    exact LinearOrderedAddCommGroupWithTop.sub_pos.mpr (Or.inl hineq)
  intro γ
  obtain ⟨N, hN⟩ := hcofinal (γ - s)
  refine ⟨N, fun n hn => ?_⟩
  have hpow : 2 ^ N ≤ 2 ^ n := by
    exact Nat.pow_le_pow_right (by norm_num) hn
  have hsmul : (2 ^ N) • q₀ ≤ (2 ^ n) • q₀ :=
    nsmul_le_nsmul_left hq₀.le hpow
  have hγ : γ ≤ s + (2 ^ n) • q₀ := by
    calc
      γ = s + (γ - s) := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          (LinearOrderedAddCommGroupWithTop.add_neg_cancel_left_of_ne_top hs γ).symm
      _ ≤ s + (2 ^ N) • q₀ := by
        simpa [valuationExcess, add_comm] using add_le_add_left hN s
      _ ≤ s + (2 ^ n) • q₀ := by
        simpa [add_comm] using add_le_add_left hsmul s
  have hnstep := valuation_newton_induction v A hA f hf a₀ ha₀ hineq hderiv n
  rw [hnstep.2.2]
  apply hγ.trans
  simpa [s, q₀, valuationExcess, add_comm] using add_le_add_left hnstep.2.1 s

/-- The Newton corrections tend to the top in the rank-one case. -/
-- STATEMENT_NEEDS_UPDATE: `Valuation.RankOne v.toValuation` controls only the ordered value-group image of `v`, not the ambient codomain `Γ`; that image can lie in a proper non-cofinal convex subgroup. Moreover, `TendsToTop` quantifies over `⊤`, while a generic Newton correction has finite value, so the displayed sequence need not tend to the top even in the value-group image. The minimal correction is to quantify only over finite values in the value-group image (or to add an appropriate finite-value cofinality hypothesis and exclude `⊤`).
theorem valuation_newton_corrections_tend_to_top {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ)
    [Valuation.RankOne v.toValuation]
    (A : Subring K) (hA : IsValuationSubring A v) (f : K[X])
    (hf : PolynomialCoefficientsInSubring A f) (a₀ : K) (ha₀ : a₀ ∈ A)
    (hineq : v (f.eval a₀) > v (f.derivative.eval a₀) + v (f.derivative.eval a₀))
    (hcomplete : Chapter09NonarchimedeanComplete v) :
    TendsToTop (fun n => v (newtonIterate f a₀ (n + 1) - newtonIterate f a₀ n)) := by
  sorry

/-- The strict Newton inequality is the error being smaller than the square of the derivative. -/
def StrictNewtonCondition {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ)
    (f : K[X]) (a₀ : K) : Prop :=
  v (f.eval a₀) > v (f.derivative.eval a₀) + v (f.derivative.eval a₀)

/-- A residue approximation at which both the polynomial and derivative vanish. -/
def IsMultipleResidueApproximation {A : Type*} [CommRing A] [IsLocalRing A]
    (f : A[X]) (a₀ : A) : Prop :=
  f.eval a₀ ∈ IsLocalRing.maximalIdeal A ∧
    f.derivative.eval a₀ ∈ IsLocalRing.maximalIdeal A

/-- A multiple approximation can split into two distinct exact roots. -/
theorem quadratic_multiple_approximation_can_split {K : Type*} [Field K]
    (c : K) (hc : c ≠ 0) (hcneg : c ≠ -c) :
    quadraticPolynomial (c ^ 2) = (X - C c) * (X + C c) ∧
      (quadraticPolynomial (c ^ 2)).eval c = 0 ∧
      (quadraticPolynomial (c ^ 2)).eval (-c) = 0 ∧ c ≠ -c := by
  have _hc := hc
  refine ⟨?_, ?_, ?_, hcneg⟩
  · simp [quadraticPolynomial]
    ring
  · simp [quadraticPolynomial]
  · simp [quadraticPolynomial]

/-- The strict inequality in Theorem 9.2 cannot be dropped in general. -/
theorem strict_newton_condition_is_essential :
    ¬ StrictNewtonCondition (Padic.addValuation (p := 2))
        (quadraticPolynomial (2 : ℚ_[2])) 0 ∧
      ¬ ∃ x : ℚ_[2], x ^ 2 = (2 : ℚ_[2]) := by
  constructor
  · intro h
    have h' := h
    simp [StrictNewtonCondition, quadraticPolynomial] at h'
  · exact padic_x_sq_sub_p_has_no_root 2

end
end Chapter09
end LastLib.Book01ValuationsDVRsAndCompletions
