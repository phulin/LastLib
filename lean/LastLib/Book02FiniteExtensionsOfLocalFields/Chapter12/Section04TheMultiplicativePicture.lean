import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12.Section03TheGaloisPicture
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.Section02TheValuationForm
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Valued.WithVal
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.RingTheory.Polynomial.ScaleRoots

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12

noncomputable section

open Polynomial
open scoped BigOperators

/-! ## 12.4. Stability of simple roots -/

/-- The monic degree-`d` polynomial with coefficient vector `a`, where
`a i` is the coefficient of `T^i`. -/
def chapter12MonicPolynomial
    {K : Type*} [Semiring K] (d : ℕ) (a : Fin d → K) : K[X] :=
  (X : K[X]) ^ d + ∑ i : Fin d, C (a i) * X ^ (i : ℕ)

/-- The lower-coefficient vector of a polynomial in the fixed degree-parameter
space. -/
def chapter12CoefficientVector
    {K : Type*} [Semiring K] (d : ℕ) (f : K[X]) : Fin d → K :=
  fun i => f.coeff (i : ℕ)

/-- A monic polynomial of degree `d` is recovered from its lower
coefficients. -/
theorem chapter12_monic_polynomial_recovered_from_coefficients
    {K : Type*} [Field K] (f : K[X]) (d : ℕ)
    (hf_monic : f.Monic) (hf_degree : f.natDegree = d) :
    chapter12MonicPolynomial d (chapter12CoefficientVector d f) = f := by
  change X ^ d + ∑ i : Fin d, C (f.coeff (i : ℕ)) * X ^ (i : ℕ) = f
  have hsum :
      (∑ i : Fin d, C (f.coeff (i : ℕ)) * X ^ (i : ℕ)) =
        ∑ i ∈ Finset.range d, C (f.coeff i) * X ^ i := by
    apply Finset.sum_bij (s := (Finset.univ : Finset (Fin d)))
      (t := Finset.range d) (fun i _ => (i : ℕ))
    · intro i hi
      exact Finset.mem_range.mpr i.isLt
    · intro i hi j hj hij
      exact Fin.ext hij
    · intro b hb
      refine ⟨⟨b, Finset.mem_range.mp hb⟩, Finset.mem_univ _, rfl⟩
    · intro i hi
      rfl
  rw [hsum]
  simpa [hf_degree] using hf_monic.as_sum.symm

/-- Separability is exactly the nonvanishing derivative condition at a root. -/
theorem chapter12_simple_root_has_nonzero_derivative
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (f : K[X]) (hf_separable : f.Separable) (z : L)
    (hz : aeval z f = 0) :
    aeval z f.derivative ≠ 0 := by
  rcases hf_separable with ⟨u, v, huv⟩
  intro hzero
  have heval := congrArg (aeval z) huv
  simp [hz, hzero] at heval

private theorem chapter12_monic_polynomial_coeff_of_lt
    {K : Type*} [Semiring K] (d : ℕ) (a : Fin d → K)
    {n : ℕ} (hn : n < d) :
    (chapter12MonicPolynomial d a).coeff n = a ⟨n, hn⟩ := by
  classical
  change coeff (X ^ d +
      ∑ i ∈ (Finset.univ : Finset (Fin d)), C (a i) * X ^ (i : ℕ)) n =
    a ⟨n, hn⟩
  rw [coeff_add, finsetSum_coeff, coeff_X_pow]
  rw [Finset.sum_eq_single ⟨n, hn⟩]
  · rw [coeff_C_mul_X_pow]
    simp [Nat.ne_of_lt hn]
  · intro i hi hne
    have hni : n ≠ (i : ℕ) := by
      intro h
      apply hne
      exact Fin.ext h.symm
    rw [coeff_C_mul_X_pow]
    simp [hni]
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

private theorem chapter12_monic_polynomial_monic
    {K : Type*} [Semiring K] (d : ℕ) (a : Fin d → K) :
    (chapter12MonicPolynomial d a).Monic := by
  change (X ^ d + ∑ i : Fin d, C (a i) * X ^ (i : ℕ)).Monic
  apply monic_X_pow_add
  exact degree_sum_fin_lt _

private theorem chapter12_monic_polynomial_natDegree
    {K : Type*} [Semiring K] [Nontrivial K] (d : ℕ) (a : Fin d → K) (hd : 0 < d) :
    (chapter12MonicPolynomial d a).natDegree = d := by
  have _ := hd
  change (X ^ d + ∑ i : Fin d, C (a i) * X ^ (i : ℕ)).natDegree = d
  have hdeg : (∑ i : Fin d, C (a i) * X ^ (i : ℕ)).degree <
      (X ^ d : K[X]).degree := by
    rw [degree_X_pow]
    exact degree_sum_fin_lt a
  rw [natDegree_add_eq_left_of_degree_lt hdeg]
  simp

private theorem chapter12_complete_norm_valuation
    {M : Type*} [NontriviallyNormedField M]
    [IsUltrametricDist M] [CompleteSpace M] :
    @CompleteSpace M
      (Valued.mk' (Valuation.toAddValuation
        (NormedField.valuation (K := M))).toValuation).toUniformSpace := by
  let vM : Valuation M NNReal := NormedField.valuation
  let v : AddValuation M (Additive NNReal)ᵒᵈ := Valuation.toAddValuation vM
  have hv_equiv : vM.IsEquiv v.toValuation := by
    rw [Valuation.isEquiv_iff_val_le_one]
    intro x
    rfl
  let : Valued M NNReal := NormedField.toValued
  have hcompleteM : @CompleteSpace M (Valued.mk' vM).toUniformSpace := by
    have hU : (Valued.mk' vM).toUniformSpace = (inferInstance : UniformSpace M) := by
      change @IsTopologicalAddGroup.rightUniformSpace M _ vM.subgroups_basis.topology _ = _
      exact (Valued.toUniformSpace_eq M NNReal).symm
    rw [hU]
    infer_instance
  have hforward : @UniformContinuous M M
      (Valued.mk' vM).toUniformSpace (Valued.mk' v.toValuation).toUniformSpace
      (id : M → M) := hv_equiv.symm.uniformContinuous
  have hback : @UniformContinuous M M
      (Valued.mk' v.toValuation).toUniformSpace (Valued.mk' vM).toUniformSpace
      (id : M → M) := hv_equiv.uniformContinuous
  have hind : @IsUniformInducing M M
      (Valued.mk' vM).toUniformSpace (Valued.mk' v.toValuation).toUniformSpace
      (id : M → M) :=
    @IsUniformInducing.of_comp M M M
      (Valued.mk' vM).toUniformSpace
      (Valued.mk' v.toValuation).toUniformSpace
      (Valued.mk' vM).toUniformSpace
      (id : M → M) (id : M → M) hforward hback
      (@IsUniformInducing.id M (Valued.mk' vM).toUniformSpace)
  exact (@IsUniformInducing.completeSpace_congr M M
    (Valued.mk' vM).toUniformSpace (Valued.mk' v.toValuation).toUniformSpace
    (id : M → M) hind (Function.surjective_id)).mp hcompleteM

private theorem chapter12_hensel_root_of_norm
    {M : Type*} [NontriviallyNormedField M]
    [IsUltrametricDist M] [CompleteSpace M]
    (p : M[X]) (a₀ : M) (hp : p.Monic)
    (hcoeff : ∀ n, ‖p.coeff n‖ ≤ 1) (ha₀ : ‖a₀‖ ≤ 1)
    (hderiv : p.derivative.eval a₀ ≠ 0)
    (hineq : ‖p.eval a₀‖ < ‖p.derivative.eval a₀‖ ^ 2) :
    ∃ a : M, p.eval a = 0 ∧ ‖a - a₀‖ < ‖p.derivative.eval a₀‖ := by
  have _ := hp
  have _ := hderiv
  let vM : Valuation M NNReal := NormedField.valuation
  let : Valuation.RankOne vM :=
    { hom' := MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
      exists_val_nontrivial := by
        obtain ⟨x, hx⟩ := NormedField.exists_one_lt_norm M
        have hx0 : x ≠ 0 := by
          intro hx0
          subst x
          have hx' : (1 : ℝ) < 0 := by simpa only [norm_zero] using hx
          linarith
        refine ⟨x, ?_, ?_⟩
        · simp [vM, NormedField.valuation_apply, hx0]
        · intro h
          have h' : ‖x‖₊ = (1 : NNReal) := by
            simpa [vM, NormedField.valuation_apply] using h
          have hreal : ‖x‖ = (1 : ℝ) := by
            simpa using congrArg (fun t : NNReal => (t : ℝ)) h'
          exact (ne_of_gt hx) hreal }
  let v : AddValuation M (Additive NNReal)ᵒᵈ := Valuation.toAddValuation vM
  let : Valuation.RankOne v.toValuation := by
    let hv_equiv : vM.IsEquiv v.toValuation := by
      rw [Valuation.isEquiv_iff_val_le_one]
      intro x
      rfl
    exact
      { hom' := (Valuation.RankOne.hom vM).comp
          hv_equiv.orderMonoidIso.symm.toMonoidWithZeroHom
        strictMono' := (Valuation.RankOne.strictMono vM).comp
          hv_equiv.orderMonoidIso.symm.strictMono
        exists_val_nontrivial := by
          obtain ⟨r, hr0, hr1⟩ := Valuation.RankOne.nontrivial vM
          refine ⟨r, ?_, ?_⟩
          · intro hr
            exact hr0 ((hv_equiv.eq_zero).mpr hr)
          · intro hr
            exact hr1 ((hv_equiv.eq_one_iff_eq_one).mpr hr) }
  let A : Subring M := v.toValuation.valuationSubring.toSubring
  have hA :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.IsValuationSubring A v := by
    intro x
    change x ∈ v.toValuation.valuationSubring ↔ v x ≥ 0
    rw [Valuation.mem_valuationSubring_iff]
    rfl
  have hcoeff' :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.PolynomialCoefficientsInSubring A p := by
    intro n
    apply (hA _).mpr
    change ‖p.coeff n‖₊ ≤ 1
    exact_mod_cast hcoeff n
  have ha₀' : a₀ ∈ A := by
    apply (hA _).mpr
    change ‖a₀‖₊ ≤ 1
    exact_mod_cast ha₀
  have hineq' : v (p.eval a₀) >
      v (p.derivative.eval a₀) + v (p.derivative.eval a₀) := by
    dsimp [v, vM]
    change ‖p.eval a₀‖₊ < ‖p.derivative.eval a₀‖₊ * ‖p.derivative.eval a₀‖₊
    rw [← NNReal.coe_lt_coe]
    simpa [pow_two] using hineq
  have huniq :=
    (LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.hensel_newton_form
      v A hA p hcoeff' a₀ ha₀' hineq'
      (chapter12_complete_norm_valuation (M := M))).1
  obtain ⟨a, ha, hunique⟩ := huniq
  obtain ⟨haA, hroot, hstrict⟩ := ha
  refine ⟨a, hroot, ?_⟩
  dsimp [v, vM] at hstrict
  change ‖a - a₀‖₊ < ‖p.derivative.eval a₀‖₊ at hstrict
  rw [← NNReal.coe_lt_coe] at hstrict
  simpa using hstrict

private theorem chapter12_hensel_root_of_norm_exact
    {M : Type*} [NontriviallyNormedField M]
    [IsUltrametricDist M] [CompleteSpace M]
    (p : M[X]) (a₀ : M) (hcoeff : ∀ n, ‖p.coeff n‖ ≤ 1) (ha₀ : ‖a₀‖ ≤ 1)
    (hineq : ‖p.eval a₀‖ < ‖p.derivative.eval a₀‖ ^ 2) :
    ∃ a : M, p.eval a = 0 ∧
      ‖a - a₀‖ = ‖p.eval a₀‖ / ‖p.derivative.eval a₀‖ := by
  let vM : Valuation M NNReal := NormedField.valuation
  let : Valuation.RankOne vM :=
    { hom' := MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
      exists_val_nontrivial := by
        obtain ⟨x, hx⟩ := NormedField.exists_one_lt_norm M
        have hx0 : x ≠ 0 := by
          intro hx0
          subst x
          have hx' : (1 : ℝ) < 0 := by simpa only [norm_zero] using hx
          linarith
        refine ⟨x, ?_, ?_⟩
        · simp [vM, NormedField.valuation_apply, hx0]
        · intro h
          have h' : ‖x‖₊ = (1 : NNReal) := by
            simpa [vM, NormedField.valuation_apply] using h
          have hreal : ‖x‖ = (1 : ℝ) := by
            simpa using congrArg (fun t : NNReal => (t : ℝ)) h'
          exact (ne_of_gt hx) hreal }
  let v : AddValuation M (Additive NNReal)ᵒᵈ := Valuation.toAddValuation vM
  let : Valuation.RankOne v.toValuation := by
    let hv_equiv : vM.IsEquiv v.toValuation := by
      rw [Valuation.isEquiv_iff_val_le_one]
      intro x
      rfl
    exact
      { hom' := (Valuation.RankOne.hom vM).comp
          hv_equiv.orderMonoidIso.symm.toMonoidWithZeroHom
        strictMono' := (Valuation.RankOne.strictMono vM).comp
          hv_equiv.orderMonoidIso.symm.strictMono
        exists_val_nontrivial := by
          obtain ⟨r, hr0, hr1⟩ := Valuation.RankOne.nontrivial vM
          refine ⟨r, ?_, ?_⟩
          · intro hr
            exact hr0 ((hv_equiv.eq_zero).mpr hr)
          · intro hr
            exact hr1 ((hv_equiv.eq_one_iff_eq_one).mpr hr) }
  let A : Subring M := v.toValuation.valuationSubring.toSubring
  have hA :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.IsValuationSubring A v := by
    intro x
    change x ∈ v.toValuation.valuationSubring ↔ v x ≥ 0
    rw [Valuation.mem_valuationSubring_iff]
    rfl
  have hcoeff' :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.PolynomialCoefficientsInSubring A p := by
    intro n
    apply (hA _).mpr
    change ‖p.coeff n‖₊ ≤ 1
    exact_mod_cast hcoeff n
  have ha₀' : a₀ ∈ A := by
    apply (hA _).mpr
    change ‖a₀‖₊ ≤ 1
    exact_mod_cast ha₀
  have hineq' : v (p.eval a₀) >
      v (p.derivative.eval a₀) + v (p.derivative.eval a₀) := by
    dsimp [v, vM]
    change ‖p.eval a₀‖₊ < ‖p.derivative.eval a₀‖₊ * ‖p.derivative.eval a₀‖₊
    rw [← NNReal.coe_lt_coe]
    simpa [pow_two] using hineq
  obtain ⟨a, haA, hroot, hexact⟩ :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.hensel_newton_exact_displacement
      v A hA p hcoeff' a₀ ha₀' hineq'
      (chapter12_complete_norm_valuation (M := M))
  refine ⟨a, hroot, ?_⟩
  dsimp [v, vM] at hexact
  change ‖a - a₀‖₊ = ‖p.eval a₀‖₊ / ‖p.derivative.eval a₀‖₊ at hexact
  rw [← NNReal.coe_inj] at hexact
  simpa using hexact

private theorem chapter12_exists_small_scale
    {K M : Type*} [NontriviallyNormedField K] [NormedField M]
    [NormedAlgebra K M]
    (p : M[X]) (d : ℕ) (hp_monic : p.Monic) (hp_degree : p.natDegree = d)
    (roots : Fin d → M) :
    ∃ c : K, c ≠ 0 ∧
      (∀ n, n < d → ‖(p.scaleRoots (algebraMap K M c)).coeff n‖ < 1) ∧
      (∀ n, ‖(p.scaleRoots (algebraMap K M c)).coeff n‖ ≤ 1) ∧
      (∀ i, ‖algebraMap K M c * roots i‖ ≤ 1) := by
  let B : ℝ := 1 + (∑ n ∈ Finset.range d, ‖p.coeff n‖) +
    ∑ i : Fin d, ‖roots i‖
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  have hBone : 1 ≤ B := by
    dsimp [B]
    have h₁ : 0 ≤ ∑ n ∈ Finset.range d, ‖p.coeff n‖ := by positivity
    have h₂ : 0 ≤ ∑ i : Fin d, ‖roots i‖ := by positivity
    linarith
  obtain ⟨c, hcpos, hc⟩ :=
    NormedField.exists_norm_lt K (one_div_pos.mpr hBpos)
  have hc0 : c ≠ 0 := norm_pos_iff.mp hcpos
  have hc_le_one : ‖c‖ ≤ 1 := by
    have hdiv : 1 / B ≤ 1 := by
      exact (div_le_iff₀ hBpos).2 (by linarith)
    exact hc.le.trans hdiv
  have hpow_le : ∀ n : ℕ, 1 ≤ n → ‖c‖ ^ n ≤ ‖c‖ := by
    intro n hn
    induction n with
    | zero => omega
    | succ n ih =>
        cases n with
        | zero => simp
        | succ n =>
            rw [pow_succ]
            exact (mul_le_of_le_one_right (pow_nonneg (norm_nonneg c) _) hc_le_one).trans
              (ih (by omega))
  have hcoeff_le : ∀ n : ℕ, n < d → ‖p.coeff n‖ ≤ B := by
    intro n hn
    have hsum : ‖p.coeff n‖ ≤ ∑ m ∈ Finset.range d, ‖p.coeff m‖ := by
      apply Finset.single_le_sum (f := fun m => ‖p.coeff m‖)
      · intro m hm
        exact norm_nonneg _
      · exact Finset.mem_range.mpr hn
    dsimp [B]
    have h₂ : 0 ≤ ∑ i : Fin d, ‖roots i‖ := by positivity
    linarith
  have hroot_le : ∀ i : Fin d, ‖roots i‖ ≤ B := by
    intro i
    have hsum : ‖roots i‖ ≤ ∑ j : Fin d, ‖roots j‖ := by
      apply Finset.single_le_sum (f := fun j => ‖roots j‖)
      · intro j hj
        exact norm_nonneg _
      · exact Finset.mem_univ i
    dsimp [B]
    have h₁ : 0 ≤ ∑ n ∈ Finset.range d, ‖p.coeff n‖ := by positivity
    linarith
  have hcoeff_lt :
      ∀ n, n < d → ‖(p.scaleRoots (algebraMap K M c)).coeff n‖ < 1 := by
    intro n hlt
    rw [coeff_scaleRoots, hp_degree, norm_mul, norm_pow, norm_algebraMap']
    have hpow : ‖c‖ ^ (d - n) ≤ ‖c‖ :=
      hpow_le _ (Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_of_lt hlt))
    have hprod : ‖p.coeff n‖ * ‖c‖ < 1 := by
      calc
        ‖p.coeff n‖ * ‖c‖ ≤ B * ‖c‖ :=
          mul_le_mul_of_nonneg_right (hcoeff_le n hlt) (norm_nonneg c)
        _ < B * (1 / B) := mul_lt_mul_of_pos_left hc hBpos
        _ = 1 := by field_simp
    exact (mul_le_mul_of_nonneg_left hpow (norm_nonneg (p.coeff n))).trans_lt hprod
  refine ⟨c, hc0, hcoeff_lt, ?_, ?_⟩
  · intro n
    by_cases hlt : n < d
    · exact (hcoeff_lt n hlt).le
    · by_cases heq : n = d
      · subst n
        have hnd :
            (p.scaleRoots (algebraMap K M c)).coeff d = p.leadingCoeff := by
          rw [← hp_degree]
          exact coeff_scaleRoots_natDegree p _
        rw [hnd, hp_monic.leadingCoeff]
        simp
      · have hdn : d < n := lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm heq)
        rw [coeff_scaleRoots, coeff_eq_zero_of_natDegree_lt (hp_degree ▸ hdn)]
        simp
  · intro i
    rw [norm_mul, norm_algebraMap']
    exact (show ‖c‖ * ‖roots i‖ < 1 by
      calc
        ‖c‖ * ‖roots i‖ ≤ ‖c‖ * B :=
          mul_le_mul_of_nonneg_left (hroot_le i) (norm_nonneg c)
        _ < (1 / B) * B := mul_lt_mul_of_pos_right hc hBpos
        _ = 1 := by field_simp).le

private theorem chapter12_scaled_monic_polynomial_eq
    {K M : Type*} [NontriviallyNormedField K] [NormedField M] [NormedAlgebra K M]
    (d : ℕ) (hd : 0 < d) (c : M) (b : Fin d → K) :
    ((chapter12MonicPolynomial d b).map (algebraMap K M)).scaleRoots c =
      (X : M[X]) ^ d +
        ∑ i : Fin d,
          C (algebraMap K M (b i) * c ^ (d - (i : ℕ))) * X ^ (i : ℕ) := by
  classical
  have hmonic := chapter12_monic_polynomial_monic d b
  have hdegree := chapter12_monic_polynomial_natDegree d b hd
  have hmapdegree :
      ((chapter12MonicPolynomial d b).map (algebraMap K M)).natDegree = d := by
    rw [natDegree_map_of_leadingCoeff_ne_zero]
    · exact hdegree
    · simp [hmonic.leadingCoeff]
  ext n
  by_cases hlt : n < d
  · rw [coeff_scaleRoots, hmapdegree, coeff_map,
      chapter12_monic_polynomial_coeff_of_lt d b hlt]
    rw [coeff_add, coeff_X_pow, if_neg (Nat.ne_of_lt hlt)]
    rw [finsetSum_coeff]
    rw [Finset.sum_eq_single ⟨n, hlt⟩]
    · rw [coeff_C_mul_X_pow]
      simp
    · intro i hi hne
      rw [coeff_C_mul_X_pow]
      have hni : n ≠ (i : ℕ) := by
        intro h
        apply hne
        exact Fin.ext h.symm
      simp [hni]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  · by_cases heq : n = d
    · subst n
      have hqcoeff : (chapter12MonicPolynomial d b).coeff d = 1 := by
        rw [← hmonic.leadingCoeff, leadingCoeff]
        simp [hdegree]
      have hleft :
          (((chapter12MonicPolynomial d b).map (algebraMap K M)).scaleRoots c).coeff d =
            1 := by
        simpa [coeff_scaleRoots, hmapdegree, coeff_map] using
          congrArg (algebraMap K M) hqcoeff
      have hsum :
          (∑ i : Fin d,
            C (algebraMap K M (b i) * c ^ (d - (i : ℕ))) * X ^ (i : ℕ)).coeff d =
            0 := by
        rw [finsetSum_coeff]
        apply Finset.sum_eq_zero
        intro i hi
        rw [coeff_C_mul_X_pow]
        have hdi : d ≠ (i : ℕ) := Nat.ne_of_gt i.isLt
        simp [hdi]
      rw [hleft, coeff_add, coeff_X_pow, if_pos rfl, hsum]
      simp
    · have hdn : d < n := lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm heq)
      have hmn :
          ((chapter12MonicPolynomial d b).map (algebraMap K M)).natDegree < n := by
        simpa [hmapdegree] using hdn
      have hleft :
          (((chapter12MonicPolynomial d b).map (algebraMap K M)).scaleRoots c).coeff n = 0 := by
        rw [coeff_scaleRoots, coeff_eq_zero_of_natDegree_lt hmn]
        simp
      rw [hleft, coeff_add, coeff_X_pow]
      simp only [if_neg heq, zero_add]
      rw [finsetSum_coeff]
      symm
      apply Finset.sum_eq_zero
      intro i hi
      rw [coeff_C_mul_X_pow]
      have hni : n ≠ (i : ℕ) := by omega
      simp [hni]

private theorem chapter12_continuous_scaled_eval
    {K M : Type*} [NontriviallyNormedField K] [NormedField M]
    [NormedAlgebra K M]
    (d : ℕ) (hd : 0 < d) (c z : M) :
    Continuous (fun b : Fin d → K =>
      (((chapter12MonicPolynomial d b).map (algebraMap K M)).scaleRoots c).eval z) := by
  simp_rw [chapter12_scaled_monic_polynomial_eq d hd c]
  simp only [eval_add, eval_finsetSum, eval_mul, eval_C, eval_X_pow]
  fun_prop

private theorem chapter12_scaled_monic_polynomial_coeff_lt
    {K M : Type*} [NontriviallyNormedField K] [NormedField M]
    [NormedAlgebra K M]
    (d : ℕ) (hd : 0 < d) (c : M) (b : Fin d → K) (i : Fin d) :
    (((chapter12MonicPolynomial d b).map (algebraMap K M)).scaleRoots c).coeff (i : ℕ) =
      algebraMap K M (b i) * c ^ (d - (i : ℕ)) := by
  rw [chapter12_scaled_monic_polynomial_eq d hd c b]
  rw [coeff_add, coeff_X_pow, if_neg (Nat.ne_of_lt i.isLt), finsetSum_coeff]
  rw [Finset.sum_eq_single i]
  · rw [coeff_C_mul_X_pow]
    simp
  · intro j hj hne
    rw [coeff_C_mul_X_pow]
    have hji : (i : ℕ) ≠ (j : ℕ) := by
      intro h
      apply hne
      exact Fin.ext h.symm
    simp [hji]
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

private theorem chapter12_continuous_scaled_derivative_eval
    {K M : Type*} [NontriviallyNormedField K] [NormedField M]
    [NormedAlgebra K M]
    (d : ℕ) (hd : 0 < d) (c z : M) :
    Continuous (fun b : Fin d → K =>
      (((chapter12MonicPolynomial d b).map (algebraMap K M)).scaleRoots c).derivative.eval z) := by
  simp_rw [chapter12_scaled_monic_polynomial_eq d hd c]
  simp only [derivative_add, derivative_X_pow, derivative_sum, derivative_C_mul,
    eval_add, eval_finsetSum, eval_mul, eval_C, eval_X_pow]
  fun_prop

private theorem chapter12_norm_eq_of_norm_sub_lt
    {M : Type*} [NormedField M] [IsUltrametricDist M]
    (x y : M) (h : ‖x - y‖ < ‖y‖) : ‖x‖ = ‖y‖ := by
  apply le_antisymm
  · calc
      ‖x‖ = ‖(x - y) + y‖ := by congr 1; ring
      _ ≤ max ‖x - y‖ ‖y‖ := IsUltrametricDist.norm_add_le_max _ _
      _ = ‖y‖ := max_eq_right h.le
  · by_contra hnot
    have hyx : ‖x‖ < ‖y‖ := lt_of_not_ge hnot
    have hle : ‖y‖ ≤ max ‖y - x‖ ‖x‖ := by
      calc
        ‖y‖ = ‖(y - x) + x‖ := by congr 1; ring
        _ ≤ max ‖y - x‖ ‖x‖ := IsUltrametricDist.norm_add_le_max _ _
    have hmax : max ‖y - x‖ ‖x‖ < ‖y‖ := by
      apply max_lt
      · simpa [norm_sub_rev] using h
      · exact hyx
    exact (not_lt_of_ge hle) hmax

/--
Simultaneous stability of all simple roots.  `M` is a finite splitting field
and the supplied root list records its distinct roots.  The conclusion keeps
the coefficient neighborhood in `K^d`, returns one root in each prescribed
ball, asserts uniqueness in that ball, and records that all roots factor in
`M`.
-/
theorem chapter12_simultaneous_stability_of_simple_roots
    {K M : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] [NormedField M] [NormedAlgebra K M]
    [FiniteDimensional K M]
    (f : K[X]) (d : ℕ)
    (hf_monic : f.Monic) (hf_degree : f.natDegree = d)
    (hf_separable : f.Separable)
    (hsplits : (f.map (algebraMap K M)).Splits)
    (roots : Fin d → M)
    (hroot : ∀ i, aeval (roots i) f = 0)
    (hexhaustive : ∀ z : M, aeval z f = 0 → ∃ i, z = roots i)
    (hinjective : Function.Injective roots)
    (r : Fin d → ℝ) (hr : ∀ i, 0 < r i)
    (hballs : ∀ i j, i ≠ j →
      Disjoint (Metric.ball (roots i) (r i)) (Metric.ball (roots j) (r j))) :
    ∃ U : Set (Fin d → K), IsOpen U ∧
      chapter12CoefficientVector d f ∈ U ∧
      ∀ b : Fin d → K, b ∈ U →
        ∃ β : Fin d → M,
          (∀ i, aeval (β i) (chapter12MonicPolynomial d b) = 0 ∧
            β i ∈ Metric.ball (roots i) (r i)) ∧
          (∀ (i : Fin d) (z : M), aeval z (chapter12MonicPolynomial d b) = 0 →
            z ∈ Metric.ball (roots i) (r i) → z = β i) ∧
          Polynomial.map (algebraMap K M) (chapter12MonicPolynomial d b) =
            ∏ i : Fin d, ((X : M[X]) - C (β i)) := by
  classical
  by_cases hd : d = 0
  · cases hd
    refine ⟨Set.univ, isOpen_univ, by simp, ?_⟩
    intro b hb
    let β : Fin 0 → M := Fin.elim0
    refine ⟨β, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp [chapter12MonicPolynomial]
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    let : NontriviallyNormedField M :=
      NontriviallyNormedField.ofNormNeOne (by
        obtain ⟨x, hx⟩ := NormedField.exists_one_lt_norm K
        have hxM0 : algebraMap K M x ≠ 0 := by
          intro h
          have hx0 : x = 0 :=
            (FaithfulSMul.algebraMap_injective K M) (by simpa using h)
          subst x
          norm_num at hx
        refine ⟨algebraMap K M x, hxM0, ?_⟩
        rw [norm_algebraMap']
        exact ne_of_gt hx)
    let : IsUltrametricDist M := IsUltrametricDist.of_normedAlgebra K
    let : CompleteSpace M := FiniteDimensional.complete K M
    let p : M[X] := f.map (algebraMap K M)
    have hp_monic : p.Monic := by
      dsimp [p]
      exact hf_monic.map _
    have hp_degree : p.natDegree = d := by
      dsimp [p]
      rw [natDegree_map_of_leadingCoeff_ne_zero]
      · exact hf_degree
      · simp [hf_monic.leadingCoeff]
    have hp_separable : p.Separable := by
      dsimp [p]
      exact hf_separable.map
    have hp_splits : p.Splits := by
      exact hsplits
    obtain ⟨c, hc0, hcoeff_lt, hcoeff_le, hroot_le⟩ :=
      chapter12_exists_small_scale (K := K) (M := M) p d hp_monic hp_degree roots
    let cM : M := algebraMap K M c
    let F : M[X] := p.scaleRoots cM
    let z : Fin d → M := fun i => cM * roots i
    have hcM0 : cM ≠ 0 := by
      intro h
      apply hc0
      apply (FaithfulSMul.algebraMap_injective K M)
      simpa [cM] using h
    have hF_monic : F.Monic := by
      dsimp [F]
      exact (monic_scaleRoots_iff cM).2 hp_monic
    have hF_ne : F ≠ 0 := hF_monic.ne_zero
    have hF_splits : F.Splits := by
      dsimp [F]
      exact hp_splits.scaleRoots cM
    have hproots_nodup : p.roots.Nodup := nodup_roots hp_separable
    have hF_roots : F.roots = p.roots.map (cM * ·) := by
      dsimp [F]
      exact roots_scaleRoots p (isUnit_iff_ne_zero.mpr hcM0)
    have hmul_injective : Function.Injective (cM * ·) := by
      intro x y hxy
      exact mul_left_cancel₀ hcM0 hxy
    have hF_nodup : F.roots.Nodup := by
      rw [hF_roots]
      exact hproots_nodup.map hmul_injective
    have hF_separable : F.Separable :=
      (nodup_roots_iff_of_splits hF_ne hF_splits).1 hF_nodup
    have hzroot : ∀ i, F.eval (z i) = 0 := by
      intro i
      have hrootp : p.eval (roots i) = 0 := by
        dsimp [p]
        rw [eval_map_algebraMap]
        exact hroot i
      dsimp [F, z]
      rw [scaleRoots_eval_mul, hrootp, mul_zero]
    have hFderiv : ∀ i, F.derivative.eval (z i) ≠ 0 := by
      intro i
      have hzroot' : aeval (z i) F = 0 := by
        simpa [aeval_def] using hzroot i
      have h := hF_separable.aeval_derivative_ne_zero hzroot'
      simpa [aeval_def] using h
    let D : Fin d → ℝ := fun i => ‖F.derivative.eval (z i)‖
    have hDpos : ∀ i, 0 < D i := by
      intro i
      exact norm_pos_iff.mpr (hFderiv i)
    let s : Fin d → ℝ := fun i => ‖cM‖ * r i
    have hspos : ∀ i, 0 < s i := by
      intro i
      dsimp [s]
      exact mul_pos (norm_pos_iff.mpr hcM0) (hr i)
    let e : Fin d → ℝ := fun i => min (D i ^ 2) (D i * s i)
    have hepos : ∀ i, 0 < e i := by
      intro i
      dsimp [e]
      exact lt_min (sq_pos_of_pos (hDpos i)) (mul_pos (hDpos i) (hspos i))
    let G : (Fin d → K) → M[X] := fun b =>
      ((chapter12MonicPolynomial d b).map (algebraMap K M)).scaleRoots cM
    have hG_center : G (chapter12CoefficientVector d f) = F := by
      dsimp [G, F, p]
      rw [chapter12_monic_polynomial_recovered_from_coefficients f d hf_monic hf_degree]
    let U : Set (Fin d → K) :=
      (⋂ i : Fin d, {b | ‖(G b).coeff (i : ℕ)‖ < 1}) ∩
        (⋂ i : Fin d, {b | ‖(G b).eval (z i)‖ < e i}) ∩
          ⋂ i : Fin d, {b |
            ‖(G b).derivative.eval (z i) - F.derivative.eval (z i)‖ < D i}
    have hcont_coeff : ∀ i : Fin d, Continuous (fun b : Fin d → K =>
        ‖(G b).coeff (i : ℕ)‖) := by
      intro i
      have hEq :
          (fun b : Fin d → K => ‖(G b).coeff (i : ℕ)‖) =
            (fun b => ‖algebraMap K M (b i) * cM ^ (d - (i : ℕ))‖) := by
        funext b
        dsimp [G]
        rw [chapter12_scaled_monic_polynomial_coeff_lt d hdpos cM b i]
      rw [hEq]
      fun_prop
    have hcont_eval : ∀ i : Fin d, Continuous (fun b : Fin d → K =>
        ‖(G b).eval (z i)‖) := by
      intro i
      simpa [G] using
        (chapter12_continuous_scaled_eval (K := K) (M := M) d hdpos cM (z i)).norm
    have hcont_deriv : ∀ i : Fin d, Continuous (fun b : Fin d → K =>
        ‖(G b).derivative.eval (z i) - F.derivative.eval (z i)‖) := by
      intro i
      simpa [G] using
        ((chapter12_continuous_scaled_derivative_eval
          (K := K) (M := M) d hdpos cM (z i)).sub continuous_const).norm
    have hUopen : IsOpen U := by
      dsimp [U]
      have h₁ : IsOpen (⋂ i : Fin d, {b | ‖(G b).coeff (i : ℕ)‖ < 1}) :=
        isOpen_iInter_of_finite fun i =>
          (hcont_coeff i).isOpen_preimage _ isOpen_Iio
      have h₂ : IsOpen (⋂ i : Fin d, {b | ‖(G b).eval (z i)‖ < e i}) :=
        isOpen_iInter_of_finite fun i =>
          (hcont_eval i).isOpen_preimage _ isOpen_Iio
      have h₃ : IsOpen (⋂ i : Fin d, {b |
          ‖(G b).derivative.eval (z i) - F.derivative.eval (z i)‖ < D i}) :=
        isOpen_iInter_of_finite fun i =>
          (hcont_deriv i).isOpen_preimage _ isOpen_Iio
      exact (h₁.inter h₂).inter h₃
    have hUcenter : chapter12CoefficientVector d f ∈ U := by
      dsimp [U]
      constructor
      · constructor
        · rw [Set.mem_iInter]
          intro i
          change ‖(G (chapter12CoefficientVector d f)).coeff (i : ℕ)‖ < 1
          rw [hG_center]
          have h := hcoeff_lt (i : ℕ) i.isLt
          simpa [F, p, cM] using h
        · rw [Set.mem_iInter]
          intro i
          change ‖(G (chapter12CoefficientVector d f)).eval (z i)‖ < e i
          rw [hG_center]
          have hzero : F.eval (z i) = 0 := hzroot i
          simpa [hzero] using hepos i
      · rw [Set.mem_iInter]
        intro i
        change ‖(G (chapter12CoefficientVector d f)).derivative.eval (z i) -
          F.derivative.eval (z i)‖ < D i
        rw [hG_center]
        simpa using hDpos i
    refine ⟨U, hUopen, hUcenter, ?_⟩
    intro b hb
    dsimp [U] at hb
    have hb_coeff_lt : ∀ i : Fin d, ‖(G b).coeff (i : ℕ)‖ < 1 := by
      intro i
      exact Set.mem_iInter.mp hb.1.1 i
    have hb_eval : ∀ i : Fin d, ‖(G b).eval (z i)‖ < e i := by
      intro i
      exact Set.mem_iInter.mp hb.1.2 i
    have hb_deriv : ∀ i : Fin d,
        ‖(G b).derivative.eval (z i) - F.derivative.eval (z i)‖ < D i := by
      intro i
      exact Set.mem_iInter.mp hb.2 i
    have hGb_monic : (G b).Monic := by
      dsimp [G]
      have hqmonic := chapter12_monic_polynomial_monic d b
      exact (monic_scaleRoots_iff cM).2 (hqmonic.map (algebraMap K M))
    have hGb_degree : (G b).natDegree = d := by
      dsimp [G]
      rw [natDegree_scaleRoots, natDegree_map_of_leadingCoeff_ne_zero]
      · exact chapter12_monic_polynomial_natDegree d b hdpos
      · simp [chapter12_monic_polynomial_monic d b |>.leadingCoeff]
    have hGb_coeff : ∀ n, ‖(G b).coeff n‖ ≤ 1 := by
      intro n
      by_cases hlt : n < d
      · exact (hb_coeff_lt ⟨n, hlt⟩).le
      · by_cases heq : n = d
        · have hcoeff : (G b).coeff d = 1 := by
            simpa [leadingCoeff, hGb_degree] using hGb_monic.leadingCoeff
          rw [heq, hcoeff]
          simp
        · have hdn : d < n := lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm heq)
          rw [coeff_eq_zero_of_natDegree_lt (hGb_degree ▸ hdn)]
          simp
    have hGb_deriv_norm : ∀ i : Fin d,
        ‖(G b).derivative.eval (z i)‖ = D i := by
      intro i
      simpa [D] using
        chapter12_norm_eq_of_norm_sub_lt
          ((G b).derivative.eval (z i)) (F.derivative.eval (z i)) (hb_deriv i)
    have hGb_ineq : ∀ i : Fin d,
        ‖(G b).eval (z i)‖ < ‖(G b).derivative.eval (z i)‖ ^ 2 := by
      intro i
      calc
        ‖(G b).eval (z i)‖ < e i := hb_eval i
        _ ≤ D i ^ 2 := min_le_left _ _
        _ = ‖(G b).derivative.eval (z i)‖ ^ 2 := by rw [hGb_deriv_norm]
    have hz_integral : ∀ i : Fin d, ‖z i‖ ≤ 1 := by
      intro i
      simpa [z, cM] using hroot_le i
    have hscaled : ∀ i : Fin d, ∃ w : M,
        (G b).eval w = 0 ∧
          ‖w - z i‖ = ‖(G b).eval (z i)‖ /
            ‖(G b).derivative.eval (z i)‖ := by
      intro i
      exact chapter12_hensel_root_of_norm_exact
        (M := M) (G b) (z i) hGb_coeff (hz_integral i) (hGb_ineq i)
    choose w hwroot hwdisp using hscaled
    have hwclose : ∀ i : Fin d, ‖w i - z i‖ < s i := by
      intro i
      have hratio :
          ‖(G b).eval (z i)‖ /
              ‖(G b).derivative.eval (z i)‖ < s i := by
        rw [hGb_deriv_norm]
        apply (div_lt_iff₀ (hDpos i)).2
        have he : e i ≤ s i * D i := by
          dsimp [e]
          exact (min_le_right _ _).trans_eq (mul_comm _ _)
        exact (hb_eval i).trans_le he
      rw [hwdisp i]
      exact hratio
    let β : Fin d → M := fun i => w i / cM
    have hβroot : ∀ i, aeval (β i) (chapter12MonicPolynomial d b) = 0 := by
      intro i
      have hscale := scaleRoots_eval_mul
        ((chapter12MonicPolynomial d b).map (algebraMap K M)) (β i) cM
      have hwrel : cM * β i = w i := by
        dsimp [β]
        field_simp
      have hzero : cM ^
          ((chapter12MonicPolynomial d b).map (algebraMap K M)).natDegree *
          ((chapter12MonicPolynomial d b).map (algebraMap K M)).eval (β i) = 0 := by
        rw [← hscale, show cM * β i = w i by exact hwrel]
        exact hwroot i
      have hmaproot :
          ((chapter12MonicPolynomial d b).map (algebraMap K M)).eval (β i) = 0 := by
        exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero _ hcM0)
      rw [eval_map_algebraMap] at hmaproot
      exact hmaproot
    have hβball : ∀ i, β i ∈ Metric.ball (roots i) (r i) := by
      intro i
      rw [Metric.mem_ball, dist_eq_norm]
      have hdiff : β i - roots i = (w i - z i) / cM := by
        dsimp [β, z]
        field_simp
      rw [hdiff, norm_div]
      calc
        ‖w i - z i‖ / ‖cM‖ < s i / ‖cM‖ :=
          div_lt_div_of_pos_right (hwclose i) (norm_pos_iff.mpr hcM0)
        _ = r i := by dsimp [s]; field_simp
    have hβ_injective : Function.Injective β := by
      intro i j hij
      by_contra hne
      have hzi : β j ∈ Metric.ball (roots i) (r i) := by
        rw [← hij]
        exact hβball i
      have hzj : β j ∈ Metric.ball (roots j) (r j) := hβball j
      exact (Set.disjoint_left.1 (hballs i j hne)) hzi hzj
    let g₀ : M[X] :=
      (chapter12MonicPolynomial d b).map (algebraMap K M)
    have hg₀_monic : g₀.Monic := by
      dsimp [g₀]
      exact (chapter12_monic_polynomial_monic d b).map _
    have hg₀_ne : g₀ ≠ 0 := hg₀_monic.ne_zero
    have hg₀_degree : g₀.natDegree = d := by
      dsimp [g₀]
      rw [natDegree_map_of_leadingCoeff_ne_zero]
      · exact chapter12_monic_polynomial_natDegree d b hdpos
      · simp [chapter12_monic_polynomial_monic d b |>.leadingCoeff]
    have hβroot₀ : ∀ i, g₀.eval (β i) = 0 := by
      intro i
      dsimp [g₀]
      rw [eval_map_algebraMap]
      exact hβroot i
    let S : Finset M := (Finset.univ : Finset (Fin d)).image β
    have hS_card : S.card = d := by
      dsimp [S]
      rw [Finset.card_image_of_injective _ hβ_injective, Finset.card_univ,
        Fintype.card_fin]
    have hSroot : ∀ x ∈ S, g₀.eval x = 0 := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
      exact hβroot₀ i
    have hroots_eq : g₀.roots = S.val := by
      apply roots_eq_of_natDegree_le_card_of_ne_zero hSroot
      · rw [hg₀_degree, hS_card]
      · exact hg₀_ne
    have hg₀_splits : g₀.Splits := by
      rw [splits_iff_card_roots]
      rw [hroots_eq, hg₀_degree]
      change S.card = d
      exact hS_card
    have hfactor : g₀ = (g₀.roots.map (X - C ·)).prod :=
      hg₀_splits.eq_prod_roots_of_monic hg₀_monic
    have hprod_finset :
        ∏ x ∈ S, ((X : M[X]) - C x) =
          ∏ i : Fin d, ((X : M[X]) - C (β i)) := by
      dsimp [S]
      rw [Finset.prod_image hβ_injective.injOn]
    have hfactor' :
        (chapter12MonicPolynomial d b).map (algebraMap K M) =
          ∏ i : Fin d, ((X : M[X]) - C (β i)) := by
      change g₀ = ∏ i : Fin d, ((X : M[X]) - C (β i))
      rw [hfactor, hroots_eq]
      change (∏ x ∈ S, ((X : M[X]) - C x)) =
        ∏ i : Fin d, ((X : M[X]) - C (β i))
      exact hprod_finset
    refine ⟨β, ?_, ?_, hfactor'⟩
    · intro i
      exact ⟨hβroot i, hβball i⟩
    intro i z hz hzi
    have hz₀ : g₀.eval z = 0 := by
      dsimp [g₀]
      rw [eval_map_algebraMap]
      exact hz
    have hzmem : z ∈ g₀.roots := (mem_roots hg₀_ne).2 hz₀
    rw [hroots_eq] at hzmem
    have hzS : z ∈ S := by simpa using hzmem
    rcases Finset.mem_image.mp hzS with ⟨j, hj, hzj⟩
    have hji : j = i := by
      by_contra hne
      subst z
      exact (Set.disjoint_left.1 (hballs i j (Ne.symm hne))) hzi (hβball j)
    subst z
    simp [hji]

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12
