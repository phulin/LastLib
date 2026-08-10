import Mathlib.Algebra.Module.PID
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.AbsoluteValue
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter07

open Filter Set Function MonoidWithZeroHom
open scoped BigOperators Topology PowerSeries LaurentSeries RatFunc WithZero
  WithZeroTopology Multiplicative

noncomputable section

/-!
  Chapter 7 develops completion from the metric point of view and compares it with
  valuation rings and ideal-adic completion. Proofs are deferred to a later pass.
-/

/-! # Book 1, Chapter 7, Section 7.1: Filling the Missing Limits
-/

/-! ### 7.1. Finite approximations and digit strings -/

/-- The infinite base-p digit strings used to describe compatible approximations. -/
def chapter07DigitString (p : ℕ) : Type _ :=
  ℕ → Fin p

/-- The finite truncation of a p-adic digit string. -/
def chapter07DigitTruncation (p n : ℕ) (a : chapter07DigitString p) : ℕ :=
  ∑ i ∈ Finset.range n, (a i).val * p ^ i

/-! The localization at p and the finite rings ZMod powers. -/

abbrev chapter07LocalizedIntegers (p : ℕ) [Fact p.Prime] : Type _ :=
  Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))

abbrev chapter07FinitePAdicApproximation (p n : ℕ) : Type _ :=
  ZMod (p ^ n)

-- Section 7.1: every finite base-p approximation is represented by digits.
theorem chapter07_digits_surject_onto_finite_approximations
    (p n : ℕ) [Fact p.Prime] :
    Function.Surjective
      (fun a : chapter07DigitString p =>
        (chapter07DigitTruncation p n a : chapter07FinitePAdicApproximation p n)) := by
  intro z
  obtain ⟨m, rfl⟩ := ZMod.natCast_zmod_surjective z
  have hp : 2 ≤ p := Nat.Prime.two_le Fact.out
  let a : chapter07DigitString p := fun i =>
    ⟨(Nat.digits p m).getD i 0, by
      by_cases hi : i < (Nat.digits p m).length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
        exact Nat.digits_lt_base hp (List.getElem_mem hi)
      · have hzero : 0 < p := by omega
        rw [List.getD_eq_getElem?_getD]
        simpa [hi] using hzero⟩
  refine ⟨a, ?_⟩
  have hsum : ∀ j : ℕ,
      (∑ i ∈ Finset.range j, (Nat.digits p m).getD i 0 * p ^ i) =
        (List.mapIdx (fun i a => a * p ^ i) ((Nat.digits p m).take j)).sum := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      by_cases h : j < (Nat.digits p m).length
      · rw [Finset.sum_range_succ, ih]
        rw [← List.take_append_getElem h]
        rw [List.mapIdx_append, List.sum_append]
        simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt h)]
        simp [List.getElem?_eq_getElem h]
      · have hle : (Nat.digits p m).length ≤ j := Nat.le_of_not_gt h
        rw [Finset.sum_range_succ, ih]
        have htake : (Nat.digits p m).take (j + 1) =
            (Nat.digits p m).take j := by
          apply (List.take_eq_take_iff).2
          simp [Nat.min_eq_right hle,
            Nat.min_eq_right (le_trans hle (Nat.le_succ j))]
        rw [htake]
        simp [List.getD_eq_getElem?_getD, h]
  simp only [chapter07DigitTruncation, a]
  rw [hsum n, ← Nat.ofDigits_eq_sum_mapIdx,
    ← Nat.self_mod_pow_eq_ofDigits_take n m hp]
  simp

-- Section 7.1: localization at (p) realizes every finite p-adic approximation.
theorem chapter07_localized_integers_realize_finite_approximations
    (p n : ℕ) [Fact p.Prime] :
    ∃ φ : chapter07LocalizedIntegers p →+*
        chapter07FinitePAdicApproximation p n,
      Function.Surjective φ := by
  let P : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  let e := IsLocalization.AtPrime.equivQuotMaximalIdealPow P
    (chapter07LocalizedIntegers p) n
  let q : chapter07LocalizedIntegers p →+*
      chapter07LocalizedIntegers p ⧸
        IsLocalRing.maximalIdeal (chapter07LocalizedIntegers p) ^ n :=
    Ideal.Quotient.mk _
  have hP : P ^ n = Ideal.span ({(p ^ n : ℤ)} : Set ℤ) := by
    rw [show P = Ideal.span ({(p : ℤ)} : Set ℤ) by rfl]
    rw [Ideal.span_singleton_pow]
  let z : ℤ ⧸ P ^ n ≃+* ZMod (p ^ n) :=
    hP ▸ Int.quotientSpanNatEquivZMod (p ^ n)
  let φ : chapter07LocalizedIntegers p →+* ZMod (p ^ n) :=
    z.toRingHom.comp (e.symm.toRingHom.comp q)
  refine ⟨φ, ?_⟩
  intro a
  obtain ⟨m, rfl⟩ := ZMod.natCast_zmod_surjective a
  refine ⟨algebraMap ℤ (chapter07LocalizedIntegers p) m, ?_⟩
  simp [φ, q, z, e]

/-! ### 7.1. Completion data and uniqueness -/

/-- A complete valued-field completion package, with its dense field embedding. -/
structure Chapter07CompletionData
    (K F Γ₀ : Type*) [Field K] [Field F]
    [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [Valued F Γ₀] where
  embedding : K →+* F
  complete : CompleteSpace F
  hausdorff : T0Space F
  injective : Function.Injective embedding
  isometric : ∀ x : K,
    Valued.v (R := F) (embedding x) = Valued.v (R := K) x
  dense : DenseRange embedding

/-- The property that a field equivalence is isometric and commutes with the embeddings. -/
def chapter07IsometricFieldEquiv
    {K F G Γ₀ : Type*} [Field K] [Field F] [Field G]
    [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [Valued F Γ₀] [Valued G Γ₀]
    (A : Chapter07CompletionData K F Γ₀) (B : Chapter07CompletionData K G Γ₀)
    (e : F ≃+* G) : Prop :=
  (∀ y : F, Valued.v (R := G) (e y) = Valued.v (R := F) y) ∧
    ∀ x : K, e (A.embedding x) = B.embedding x

-- Section 7.1: a completion is unique up to a unique isometric field isomorphism.
theorem chapter07_completion_unique_up_to_unique_isometric_field_equiv
    {K F G Γ₀ : Type*} [Field K] [Field F] [Field G]
    [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] [Valued F Γ₀] [Valued G Γ₀]
    (A : Chapter07CompletionData K F Γ₀) (B : Chapter07CompletionData K G Γ₀) :
    ∃! e : F ≃+* G, chapter07IsometricFieldEquiv A B e := by
  have hAui : IsUniformInducing A.embedding := by
    rw [Filter.HasBasis.isUniformInducing_iff
      (Valued.hasBasis_uniformity K Γ₀) (Valued.hasBasis_uniformity F Γ₀)]
    constructor
    · intro γ _
      obtain ⟨y, hy⟩ :=
        MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective
          (.ofClass (Valued.v (R := F))) γ.1
      have hy0 : y ≠ 0 := by
        intro hyzero
        have hzero : (0 : MonoidWithZeroHom.ValueGroup₀
            (.ofClass (Valued.v (R := F)))) = γ.1 := by
          simpa [hyzero] using hy
        exact γ.ne_zero hzero.symm
      have hvaly0 : Valued.v (R := F) y ≠ 0 :=
        (Valuation.ne_zero_iff (Valued.v (R := F))).2 hy0
      obtain ⟨x, hxy⟩ := A.dense.mem_nhds (Valued.locally_const hvaly0)
      have hvalx : Valued.v (R := K) x = Valued.v (R := F) y := by
        calc
          Valued.v (R := K) x = Valued.v (R := F) (A.embedding x) :=
            (A.isometric x).symm
          _ = Valued.v (R := F) y := hxy
      have hvalx0 : Valued.v (R := K) x ≠ 0 := by
        intro hzero
        exact hvaly0 (hvalx.symm.trans hzero)
      have hx0 : x ≠ 0 :=
        (Valuation.ne_zero_iff (Valued.v (R := K))).mp hvalx0
      have hrestrictx0 : (Valued.v (R := K)).restrict x ≠ 0 :=
        (Valued.v (R := K)).restrict.ne_zero_iff.mpr hx0
      let δ : (MonoidWithZeroHom.ValueGroup₀
          (.ofClass (Valued.v (R := K))))ˣ :=
        Units.mk0 ((Valued.v (R := K)).restrict x) hrestrictx0
      have hyemb : Valued.v (R := F) y =
          MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
        simpa using congrArg MonoidWithZeroHom.ValueGroup₀.embedding hy
      have hbound : MonoidWithZeroHom.ValueGroup₀.embedding δ.1 =
          MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
        calc
          MonoidWithZeroHom.ValueGroup₀.embedding δ.1 = Valued.v (R := K) x := by
            simp [δ]
          _ = Valued.v (R := F) (A.embedding x) := (A.isometric x).symm
          _ = Valued.v (R := F) y := hxy
          _ = MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := hyemb
      refine ⟨δ, trivial, ?_⟩
      intro x₁ x₂ h₁₂
      simp only [Set.mem_ofPred_eq] at h₁₂ ⊢
      rw [Valuation.restrict_lt_iff_lt_embedding] at h₁₂ ⊢
      have hmap : Valued.v (R := F) (A.embedding x₂ - A.embedding x₁) =
          Valued.v (R := K) (x₂ - x₁) := by
        rw [← A.embedding.map_sub, A.isometric]
      calc
        Valued.v (R := F) (A.embedding x₂ - A.embedding x₁) =
            Valued.v (R := K) (x₂ - x₁) := hmap
        _ < MonoidWithZeroHom.ValueGroup₀.embedding δ.1 := h₁₂
        _ = MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := hbound
    · intro δ _
      obtain ⟨x, hx⟩ :=
        MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective
          (.ofClass (Valued.v (R := K))) δ.1
      have hrestrictx0 : (Valued.v (R := K)).restrict x ≠ 0 := by
        simpa [Valuation.restrict_def] using
          (show MonoidWithZeroHom.ValueGroup₀.restrict₀
              (.ofClass (Valued.v (R := K))) x ≠ 0 by
            rw [hx]
            exact δ.ne_zero)
      have hx0 : x ≠ 0 :=
        (Valuation.ne_zero_iff (Valued.v (R := K))).mp (by
          intro hzero
          apply hrestrictx0
          exact (Valuation.restrict_eq_zero_iff (Valued.v (R := K))).2 hzero)
      have hAx0 : A.embedding x ≠ 0 := by
        intro hzero
        apply hx0
        exact A.injective (by simpa using hzero)
      have hrestrictAx0 : (Valued.v (R := F)).restrict (A.embedding x) ≠ 0 :=
        (Valued.v (R := F)).restrict.ne_zero_iff.mpr hAx0
      let γ : (MonoidWithZeroHom.ValueGroup₀
          (.ofClass (Valued.v (R := F))))ˣ :=
        Units.mk0 ((Valued.v (R := F)).restrict (A.embedding x)) hrestrictAx0
      have hbound : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 =
          MonoidWithZeroHom.ValueGroup₀.embedding δ.1 := by
        calc
          MonoidWithZeroHom.ValueGroup₀.embedding γ.1 =
              Valued.v (R := F) (A.embedding x) := by simp [γ]
          _ = Valued.v (R := K) x := A.isometric x
          _ = MonoidWithZeroHom.ValueGroup₀.embedding δ.1 := by
            simpa using congrArg MonoidWithZeroHom.ValueGroup₀.embedding hx
      refine ⟨γ, trivial, ?_⟩
      intro x₁ x₂ h₁₂
      simp only [Set.mem_ofPred_eq] at h₁₂ ⊢
      rw [Valuation.restrict_lt_iff_lt_embedding] at h₁₂ ⊢
      have hmap : Valued.v (R := F) (A.embedding x₂ - A.embedding x₁) =
          Valued.v (R := K) (x₂ - x₁) := by
        rw [← A.embedding.map_sub, A.isometric]
      calc
        Valued.v (R := K) (x₂ - x₁) =
            Valued.v (R := F) (A.embedding x₂ - A.embedding x₁) := hmap.symm
        _ < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := h₁₂
        _ = MonoidWithZeroHom.ValueGroup₀.embedding δ.1 := hbound
  have hBui : IsUniformInducing B.embedding := by
    rw [Filter.HasBasis.isUniformInducing_iff
      (Valued.hasBasis_uniformity K Γ₀) (Valued.hasBasis_uniformity G Γ₀)]
    constructor
    · intro γ _
      obtain ⟨y, hy⟩ :=
        MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective
          (.ofClass (Valued.v (R := G))) γ.1
      have hy0 : y ≠ 0 := by
        intro hyzero
        have hzero : (0 : MonoidWithZeroHom.ValueGroup₀
            (.ofClass (Valued.v (R := G)))) = γ.1 := by
          simpa [hyzero] using hy
        exact γ.ne_zero hzero.symm
      have hvaly0 : Valued.v (R := G) y ≠ 0 :=
        (Valuation.ne_zero_iff (Valued.v (R := G))).2 hy0
      obtain ⟨x, hxy⟩ := B.dense.mem_nhds (Valued.locally_const hvaly0)
      have hvalx : Valued.v (R := K) x = Valued.v (R := G) y := by
        calc
          Valued.v (R := K) x = Valued.v (R := G) (B.embedding x) :=
            (B.isometric x).symm
          _ = Valued.v (R := G) y := hxy
      have hvalx0 : Valued.v (R := K) x ≠ 0 := by
        intro hzero
        exact hvaly0 (hvalx.symm.trans hzero)
      have hx0 : x ≠ 0 :=
        (Valuation.ne_zero_iff (Valued.v (R := K))).mp hvalx0
      have hrestrictx0 : (Valued.v (R := K)).restrict x ≠ 0 :=
        (Valued.v (R := K)).restrict.ne_zero_iff.mpr hx0
      let δ : (MonoidWithZeroHom.ValueGroup₀
          (.ofClass (Valued.v (R := K))))ˣ :=
        Units.mk0 ((Valued.v (R := K)).restrict x) hrestrictx0
      have hyemb : Valued.v (R := G) y =
          MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
        simpa using congrArg MonoidWithZeroHom.ValueGroup₀.embedding hy
      have hbound : MonoidWithZeroHom.ValueGroup₀.embedding δ.1 =
          MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
        calc
          MonoidWithZeroHom.ValueGroup₀.embedding δ.1 = Valued.v (R := K) x := by
            simp [δ]
          _ = Valued.v (R := G) (B.embedding x) := (B.isometric x).symm
          _ = Valued.v (R := G) y := hxy
          _ = MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := hyemb
      refine ⟨δ, trivial, ?_⟩
      intro x₁ x₂ h₁₂
      simp only [Set.mem_ofPred_eq] at h₁₂ ⊢
      rw [Valuation.restrict_lt_iff_lt_embedding] at h₁₂ ⊢
      have hmap : Valued.v (R := G) (B.embedding x₂ - B.embedding x₁) =
          Valued.v (R := K) (x₂ - x₁) := by
        rw [← B.embedding.map_sub, B.isometric]
      calc
        Valued.v (R := G) (B.embedding x₂ - B.embedding x₁) =
            Valued.v (R := K) (x₂ - x₁) := hmap
        _ < MonoidWithZeroHom.ValueGroup₀.embedding δ.1 := h₁₂
        _ = MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := hbound
    · intro δ _
      obtain ⟨x, hx⟩ :=
        MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective
          (.ofClass (Valued.v (R := K))) δ.1
      have hrestrictx0 : (Valued.v (R := K)).restrict x ≠ 0 := by
        simpa [Valuation.restrict_def] using
          (show MonoidWithZeroHom.ValueGroup₀.restrict₀
              (.ofClass (Valued.v (R := K))) x ≠ 0 by
            rw [hx]
            exact δ.ne_zero)
      have hx0 : x ≠ 0 :=
        (Valuation.ne_zero_iff (Valued.v (R := K))).mp (by
          intro hzero
          apply hrestrictx0
          exact (Valuation.restrict_eq_zero_iff (Valued.v (R := K))).2 hzero)
      have hBx0 : B.embedding x ≠ 0 := by
        intro hzero
        apply hx0
        exact B.injective (by simpa using hzero)
      have hrestrictBx0 : (Valued.v (R := G)).restrict (B.embedding x) ≠ 0 :=
        (Valued.v (R := G)).restrict.ne_zero_iff.mpr hBx0
      let γ : (MonoidWithZeroHom.ValueGroup₀
          (.ofClass (Valued.v (R := G))))ˣ :=
        Units.mk0 ((Valued.v (R := G)).restrict (B.embedding x)) hrestrictBx0
      have hbound : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 =
          MonoidWithZeroHom.ValueGroup₀.embedding δ.1 := by
        calc
          MonoidWithZeroHom.ValueGroup₀.embedding γ.1 =
              Valued.v (R := G) (B.embedding x) := by simp [γ]
          _ = Valued.v (R := K) x := B.isometric x
          _ = MonoidWithZeroHom.ValueGroup₀.embedding δ.1 := by
            simpa using congrArg MonoidWithZeroHom.ValueGroup₀.embedding hx
      refine ⟨γ, trivial, ?_⟩
      intro x₁ x₂ h₁₂
      simp only [Set.mem_ofPred_eq] at h₁₂ ⊢
      rw [Valuation.restrict_lt_iff_lt_embedding] at h₁₂ ⊢
      have hmap : Valued.v (R := G) (B.embedding x₂ - B.embedding x₁) =
          Valued.v (R := K) (x₂ - x₁) := by
        rw [← B.embedding.map_sub, B.isometric]
      calc
        Valued.v (R := K) (x₂ - x₁) =
            Valued.v (R := G) (B.embedding x₂ - B.embedding x₁) := hmap.symm
        _ < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := h₁₂
        _ = MonoidWithZeroHom.ValueGroup₀.embedding δ.1 := hbound
  let : CompleteSpace F := A.complete
  let : CompleteSpace G := B.complete
  let pF := AbstractCompletion.mk F A.embedding (inferInstance : UniformSpace F)
    A.complete A.hausdorff hAui A.dense
  let pG := AbstractCompletion.mk G B.embedding (inferInstance : UniformSpace G)
    B.complete B.hausdorff hBui B.dense
  let eFG : F → G := pF.extend B.embedding
  let eGF : G → F := pG.extend A.embedding
  have hBuc : UniformContinuous B.embedding := hBui.uniformContinuous
  have hAuc : UniformContinuous A.embedding := hAui.uniformContinuous
  have hFGcont : Continuous eFG := by
    exact pF.continuous_extend
  have hGFcont : Continuous eGF := by
    exact pG.continuous_extend
  have hFG_coe : ∀ x : K, eFG (A.embedding x) = B.embedding x := by
    intro x
    exact pF.extend_coe hBuc x
  have hGF_coe : ∀ x : K, eGF (B.embedding x) = A.embedding x := by
    intro x
    exact pG.extend_coe hAuc x
  have hprodA : DenseRange (Prod.map A.embedding A.embedding) :=
    A.dense.prodMap A.dense
  have heq_add :
      (fun z : F × F => eFG (z.1 + z.2)) =
        (fun z : F × F => eFG z.1 + eFG z.2) := by
    apply DenseRange.equalizer hprodA
    · exact hFGcont.comp (continuous_fst.add continuous_snd)
    · exact (hFGcont.comp continuous_fst).add (hFGcont.comp continuous_snd)
    · funext z
      rcases z with ⟨x, y⟩
      change eFG (A.embedding x + A.embedding y) =
        eFG (A.embedding x) + eFG (A.embedding y)
      rw [← A.embedding.map_add]
      change pF.extend B.embedding (A.embedding (x + y)) =
        pF.extend B.embedding (A.embedding x) + pF.extend B.embedding (A.embedding y)
      rw [pF.extend_coe hBuc, pF.extend_coe hBuc, pF.extend_coe hBuc]
      exact B.embedding.map_add x y
  have heq_mul :
      (fun z : F × F => eFG (z.1 * z.2)) =
        (fun z : F × F => eFG z.1 * eFG z.2) := by
    apply DenseRange.equalizer hprodA
    · exact hFGcont.comp (continuous_fst.mul continuous_snd)
    · exact (hFGcont.comp continuous_fst).mul (hFGcont.comp continuous_snd)
    · funext z
      rcases z with ⟨x, y⟩
      change eFG (A.embedding x * A.embedding y) =
        eFG (A.embedding x) * eFG (A.embedding y)
      rw [← A.embedding.map_mul]
      change pF.extend B.embedding (A.embedding (x * y)) =
        pF.extend B.embedding (A.embedding x) * pF.extend B.embedding (A.embedding y)
      rw [pF.extend_coe hBuc, pF.extend_coe hBuc, pF.extend_coe hBuc]
      exact B.embedding.map_mul x y
  have hFG_one : eFG 1 = 1 := by
    calc
      eFG 1 = eFG (A.embedding 1) := by rw [A.embedding.map_one]
      _ = B.embedding 1 := hFG_coe 1
      _ = 1 := B.embedding.map_one
  have hGF_one : eGF 1 = 1 := by
    calc
      eGF 1 = eGF (B.embedding 1) := by rw [B.embedding.map_one]
      _ = A.embedding 1 := hGF_coe 1
      _ = 1 := A.embedding.map_one
  have hleft : Function.LeftInverse eGF eFG := by
    intro x
    simpa [eFG, eGF, AbstractCompletion.compare, Function.comp_def] using
      congrFun (pG.inverse_compare pF) x
  have hright : Function.RightInverse eGF eFG := by
    intro x
    simpa [eFG, eGF, AbstractCompletion.compare, Function.comp_def] using
      congrFun (pF.inverse_compare pG) x
  let e : F ≃+* G :=
    { toFun := eFG
      invFun := eGF
      left_inv := hleft
      right_inv := hright
      map_mul' := fun x y => congrFun heq_mul (x, y)
      map_add' := fun x y => congrFun heq_add (x, y) }
  have he_isometric : ∀ y : F, Valued.v (R := G) (e y) = Valued.v (R := F) y := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    · have hey : e y ≠ 0 := by
        intro hey
        exact hy (e.injective (by simpa using hey))
      have hyval0 : Valued.v (R := F) y ≠ 0 :=
        (Valuation.ne_zero_iff (Valued.v (R := F))).2 hy
      have heval0 : Valued.v (R := G) (e y) ≠ 0 :=
        (Valuation.ne_zero_iff (Valued.v (R := G))).2 hey
      have hFset : {z : F | Valued.v (R := F) z = Valued.v (R := F) y} ∈ 𝓝 y :=
        Valued.locally_const hyval0
      have hGset : {z : G | Valued.v (R := G) z = Valued.v (R := G) (e y)} ∈
          𝓝 (e y) := Valued.locally_const heval0
      have hepre : e ⁻¹' {z : G |
          Valued.v (R := G) z = Valued.v (R := G) (e y)} ∈ 𝓝 y :=
        hFGcont.continuousAt.preimage_mem_nhds hGset
      obtain ⟨x, hxF, hxG⟩ := A.dense.mem_nhds (inter_mem hFset hepre)
      calc
        Valued.v (R := G) (e y) = Valued.v (R := G) (e (A.embedding x)) := hxG.symm
        _ = Valued.v (R := G) (B.embedding x) := by
          simpa [e] using congrArg (Valued.v (R := G)) (hFG_coe x)
        _ = Valued.v (R := K) x := B.isometric x
        _ = Valued.v (R := F) (A.embedding x) := (A.isometric x).symm
        _ = Valued.v (R := F) y := hxF
  refine ⟨e, ?_, ?_⟩
  · exact ⟨he_isometric, hFG_coe⟩
  · intro e' he'
    have he'uc : UniformContinuous (e' : F → G) := by
      rw [Filter.HasBasis.uniformContinuous_iff
        (Valued.hasBasis_uniformity F Γ₀) (Valued.hasBasis_uniformity G Γ₀)]
      intro γ _
      obtain ⟨y, hy⟩ :=
        MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective
          (.ofClass (Valued.v (R := G))) γ.1
      have hy0 : y ≠ 0 := by
        intro hyzero
        have hzero : (0 : MonoidWithZeroHom.ValueGroup₀
            (.ofClass (Valued.v (R := G)))) = γ.1 := by
          simpa [hyzero] using hy
        exact γ.ne_zero hzero.symm
      have hyinv0 : (e'.symm y : F) ≠ 0 := by
        simpa using hy0
      have hδ0 : (Valued.v (R := F)).restrict (e'.symm y) ≠ 0 :=
        (Valued.v (R := F)).restrict.ne_zero_iff.mpr hyinv0
      let δ : (MonoidWithZeroHom.ValueGroup₀
          (.ofClass (Valued.v (R := F))))ˣ :=
        Units.mk0 ((Valued.v (R := F)).restrict (e'.symm y)) hδ0
      have hyemb : Valued.v (R := G) y =
          MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
        simpa using congrArg MonoidWithZeroHom.ValueGroup₀.embedding hy
      have hbound : MonoidWithZeroHom.ValueGroup₀.embedding δ.1 =
          MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
        calc
          MonoidWithZeroHom.ValueGroup₀.embedding δ.1 =
              Valued.v (R := F) (e'.symm y) := by simp [δ]
          _ = Valued.v (R := G) (e' (e'.symm y)) := (he'.1 (e'.symm y)).symm
          _ = Valued.v (R := G) y := by simp
          _ = MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := hyemb
      refine ⟨δ, trivial, ?_⟩
      intro x₁ x₂ h₁₂
      simp only [Set.mem_ofPred_eq] at h₁₂ ⊢
      rw [Valuation.restrict_lt_iff_lt_embedding] at h₁₂ ⊢
      calc
        Valued.v (R := G) (e' x₂ - e' x₁) =
            Valued.v (R := F) (x₂ - x₁) := by
          rw [← e'.map_sub, he'.1]
        _ < MonoidWithZeroHom.ValueGroup₀.embedding δ.1 := h₁₂
        _ = MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := hbound
    have he'cont : Continuous (e' : F → G) := he'uc.continuous
    have hfun : eFG = (e' : F → G) := by
      apply DenseRange.equalizer A.dense hFGcont he'cont
      funext x
      exact (hFG_coe x).trans (he'.2 x).symm
    apply RingEquiv.ext
    intro y
    change e' y = eFG y
    exact congrFun hfun.symm y

-- The standard Mathlib completion package for a valued field.
noncomputable def chapter07StandardValuedCompletionData
    (K Γ₀ : Type*) [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] :
    Chapter07CompletionData K (UniformSpace.Completion K) Γ₀ where
  embedding := UniformSpace.Completion.coeRingHom
  complete := inferInstance
  hausdorff := inferInstance
  injective := by
    exact UniformSpace.Completion.coe_injective K
  isometric := by
    intro x
    exact Valued.extensionValuation_apply_coe x
  dense := UniformSpace.Completion.denseRange_coe

/-! ### 7.1. The Cauchy-sequence construction -/

/-- Cauchy sequences in a uniform space, packaged as a subtype. -/
abbrev chapter07CauchySequence (K : Type*) [UniformSpace K] : Type _ :=
  {u : ℕ → K // CauchySeq u}

/-- Equivalence of Cauchy sequences: their difference tends to zero. -/
def chapter07CauchyEquivalent
    (K : Type*) [AddGroup K] [UniformSpace K] [IsUniformAddGroup K]
    (u v : chapter07CauchySequence K) : Prop :=
  Tendsto (fun n => u.1 n - v.1 n) (atTop : Filter ℕ) (𝓝 0)

/-- The setoid used for the Cauchy-sequence model of completion. -/
def chapter07CauchySetoid
    (K : Type*) [AddGroup K] [UniformSpace K] [IsUniformAddGroup K] :
    Setoid (chapter07CauchySequence K) where
  r := chapter07CauchyEquivalent K
  iseqv := by
    constructor
    · intro u
      change Tendsto (fun n => u.1 n - u.1 n) atTop (𝓝 0)
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : K)) atTop (𝓝 0))
    · intro u v h
      change Tendsto (fun n => u.1 n - v.1 n) atTop (𝓝 0) at h
      change Tendsto (fun n => v.1 n - u.1 n) atTop (𝓝 0)
      simpa [sub_eq_add_neg, add_comm] using h.neg
    · intro u v w huv hvw
      change Tendsto (fun n => u.1 n - v.1 n) atTop (𝓝 0) at huv
      change Tendsto (fun n => v.1 n - w.1 n) atTop (𝓝 0) at hvw
      change Tendsto (fun n => u.1 n - w.1 n) atTop (𝓝 0)
      simpa [sub_eq_add_neg, add_assoc] using huv.add hvw

/-- The quotient of Cauchy sequences by sequences tending to zero. -/
abbrev chapter07CauchyCompletion
    (K : Type*) [AddGroup K] [UniformSpace K] [IsUniformAddGroup K] : Type _ :=
  Quotient (chapter07CauchySetoid K)

-- The class of a Cauchy sequence in the quotient model.
def chapter07CauchyClass
    {K : Type*} [AddGroup K] [UniformSpace K] [IsUniformAddGroup K]
    (u : chapter07CauchySequence K) : chapter07CauchyCompletion K :=
  Quotient.mk (chapter07CauchySetoid K) u

-- Termwise addition of Cauchy sequences.
def chapter07CauchySequenceAdd
    {K : Type*} [AddGroup K] [UniformSpace K] [IsUniformAddGroup K]
    (u v : chapter07CauchySequence K) : chapter07CauchySequence K :=
  ⟨fun n => u.1 n + v.1 n, u.2.add v.2⟩

-- Products of Cauchy sequences remain Cauchy in a topological ring.  We use
-- the canonical completion only as a proof device; the uniform inducing
-- property of the completion embedding reflects the result back to K.
set_option maxHeartbeats 800000 in
lemma chapter07_cauchy_sequence_mul
    {K : Type*} [Ring K] [UniformSpace K] [IsUniformAddGroup K]
    [IsTopologicalRing K] {u v : ℕ → K}
    (hu : CauchySeq u) (hv : CauchySeq v) :
    CauchySeq (fun n => u n * v n) := by
  change Cauchy (atTop.map (fun n => u n * v n))
  rw [← (UniformSpace.Completion.isUniformInducing_coe K).cauchy_map_iff]
  have hu' : CauchySeq (fun n => (u n : UniformSpace.Completion K)) :=
    (UniformSpace.Completion.isUniformInducing_coe K).uniformContinuous.comp_cauchySeq hu
  have hv' : CauchySeq (fun n => (v n : UniformSpace.Completion K)) :=
    (UniformSpace.Completion.isUniformInducing_coe K).uniformContinuous.comp_cauchySeq hv
  have hprod : Tendsto
      (fun n => ((u n : K) : UniformSpace.Completion K) *
        (v n : UniformSpace.Completion K))
      atTop (𝓝 (limUnder atTop (fun n => (u n : UniformSpace.Completion K)) *
        limUnder atTop (fun n => (v n : UniformSpace.Completion K)))) := by
    have hmul : Continuous
        (fun z : UniformSpace.Completion K × UniformSpace.Completion K => z.1 * z.2) :=
      continuous_mul
    change Tendsto
      ((fun z : UniformSpace.Completion K × UniformSpace.Completion K => z.1 * z.2) ∘
        (fun n => (((u n : K) : UniformSpace.Completion K),
          ((v n : K) : UniformSpace.Completion K))))
      atTop (𝓝 (limUnder atTop (fun n => (u n : UniformSpace.Completion K)) *
        limUnder atTop (fun n => (v n : UniformSpace.Completion K))))
    exact (hmul.tendsto _).comp
      (hu'.tendsto_limUnder.prodMk_nhds hv'.tendsto_limUnder)
  have hprod' : CauchySeq
      (fun n => ((u n : K) : UniformSpace.Completion K) *
        (v n : UniformSpace.Completion K)) := hprod.cauchySeq
  simpa only [CauchySeq, Filter.map_map, Function.comp_def,
    UniformSpace.Completion.coe_mul] using hprod'

-- Termwise multiplication of Cauchy sequences.
def chapter07CauchySequenceMul
    {K : Type*} [Ring K] [UniformSpace K] [IsUniformAddGroup K]
    [IsTopologicalRing K]
    (u v : chapter07CauchySequence K) : chapter07CauchySequence K :=
  ⟨fun n => u.1 n * v.1 n, chapter07_cauchy_sequence_mul u.2 v.2⟩

set_option maxHeartbeats 800000 in
lemma chapter07_cauchy_mul_respects_equivalence_aux
    {K : Type*} [Ring K] [UniformSpace K] [IsUniformAddGroup K]
    [IsTopologicalRing K]
    (u₁ u₂ v₁ v₂ : ℕ → K)
    (hu : Tendsto (fun n => u₁ n - u₂ n) atTop (𝓝 (0 : K)))
    (hv : Tendsto (fun n => v₁ n - v₂ n) atTop (𝓝 (0 : K)))
    (hu₁ : CauchySeq u₁) (hu₂ : CauchySeq u₂)
    (hv₁ : CauchySeq v₁) (hv₂ : CauchySeq v₂) :
    Tendsto (fun n => u₁ n * v₁ n - u₂ n * v₂ n) atTop (𝓝 (0 : K)) := by
  have hu₁' : CauchySeq
      (fun n => (u₁ n : UniformSpace.Completion K)) :=
    (UniformSpace.Completion.isUniformInducing_coe K).uniformContinuous.comp_cauchySeq hu₁
  have hv₂' : CauchySeq
      (fun n => (v₂ n : UniformSpace.Completion K)) :=
    (UniformSpace.Completion.isUniformInducing_coe K).uniformContinuous.comp_cauchySeq hv₂
  have hu₂' : CauchySeq
      (fun n => (u₂ n : UniformSpace.Completion K)) :=
    (UniformSpace.Completion.isUniformInducing_coe K).uniformContinuous.comp_cauchySeq hu₂
  have hv₁' : CauchySeq
      (fun n => (v₁ n : UniformSpace.Completion K)) :=
    (UniformSpace.Completion.isUniformInducing_coe K).uniformContinuous.comp_cauchySeq hv₁
  have hdu : Tendsto
      (fun n => ((u₁ n - u₂ n : K) : UniformSpace.Completion K)) atTop
      (𝓝 (0 : UniformSpace.Completion K)) := by
    have h := ((UniformSpace.Completion.continuous_coe (α := K)).tendsto (0 : K)).comp hu
    have h' : Tendsto (fun n => ((u₁ n - u₂ n : K) : UniformSpace.Completion K)) atTop
        (𝓝 ((0 : K) : UniformSpace.Completion K)) :=
      h.congr' (Filter.Eventually.of_forall (fun _ => rfl))
    simpa only [UniformSpace.Completion.coe_zero] using h'
  have hdv : Tendsto
      (fun n => ((v₁ n - v₂ n : K) : UniformSpace.Completion K)) atTop
      (𝓝 (0 : UniformSpace.Completion K)) := by
    have h := ((UniformSpace.Completion.continuous_coe (α := K)).tendsto (0 : K)).comp hv
    have h' : Tendsto (fun n => ((v₁ n - v₂ n : K) : UniformSpace.Completion K)) atTop
        (𝓝 ((0 : K) : UniformSpace.Completion K)) :=
      h.congr' (Filter.Eventually.of_forall (fun _ => rfl))
    simpa only [UniformSpace.Completion.coe_zero] using h'
  have hterm₁ : Tendsto
      (fun n => ((u₁ n - u₂ n : K) : UniformSpace.Completion K) *
        (v₂ n : UniformSpace.Completion K)) atTop
      (𝓝 (0 : UniformSpace.Completion K)) := by
    have h := (continuous_mul.tendsto
      ((0 : UniformSpace.Completion K),
        limUnder atTop (fun n => (v₂ n : UniformSpace.Completion K)))).comp
      (hdu.prodMk_nhds hv₂'.tendsto_limUnder)
    simpa only [Function.comp_def, zero_mul] using h
  have hterm₂ : Tendsto
      (fun n => (u₁ n : UniformSpace.Completion K) *
        ((v₁ n - v₂ n : K) : UniformSpace.Completion K)) atTop
      (𝓝 (0 : UniformSpace.Completion K)) := by
    have h := (continuous_mul.tendsto
      (limUnder atTop (fun n => (u₁ n : UniformSpace.Completion K)),
        (0 : UniformSpace.Completion K))).comp
      (hu₁'.tendsto_limUnder.prodMk_nhds hdv)
    simpa only [Function.comp_def, mul_zero] using h
  have hterm₃ : Tendsto
      (fun n => ((u₁ n - u₂ n : K) : UniformSpace.Completion K) *
        (v₁ n : UniformSpace.Completion K)) atTop
      (𝓝 (0 : UniformSpace.Completion K)) := by
    have h := (continuous_mul.tendsto
      ((0 : UniformSpace.Completion K),
        limUnder atTop (fun n => (v₁ n : UniformSpace.Completion K)))).comp
      (hdu.prodMk_nhds hv₁'.tendsto_limUnder)
    simpa only [Function.comp_def, zero_mul] using h
  have hterm₄ : Tendsto
      (fun n => (u₂ n : UniformSpace.Completion K) *
        ((v₁ n - v₂ n : K) : UniformSpace.Completion K)) atTop
      (𝓝 (0 : UniformSpace.Completion K)) := by
    have h := (continuous_mul.tendsto
      (limUnder atTop (fun n => (u₂ n : UniformSpace.Completion K)),
        (0 : UniformSpace.Completion K))).comp
      (hu₂'.tendsto_limUnder.prodMk_nhds hdv)
    simpa only [Function.comp_def, mul_zero] using h
  have hzero : Tendsto
      (fun n =>
        ((((u₁ n - u₂ n : K) : UniformSpace.Completion K) *
            (v₁ n : UniformSpace.Completion K)) +
          ((u₂ n : UniformSpace.Completion K) *
            ((v₁ n - v₂ n : K) : UniformSpace.Completion K))) -
        ((((u₁ n - u₂ n : K) : UniformSpace.Completion K) *
            (v₁ n : UniformSpace.Completion K)) +
          ((u₂ n : UniformSpace.Completion K) *
            ((v₁ n - v₂ n : K) : UniformSpace.Completion K)))) atTop
      (𝓝 (0 : UniformSpace.Completion K)) := by
    have h := (hterm₃.add hterm₄).sub (hterm₃.add hterm₄)
    simpa only [Function.comp_def, sub_self] using h
  apply ((UniformSpace.Completion.isUniformInducing_coe K).isInducing.tendsto_nhds_iff).2
  have hsum := (hterm₁.add hterm₂).add hzero
  convert hsum using 1
  · funext n
    simp only [Function.comp_apply, UniformSpace.Completion.coe_sub,
      UniformSpace.Completion.coe_mul]
    noncomm_ring
  · simp only [UniformSpace.Completion.coe_zero, add_zero]

-- Constant Cauchy sequences embed the original field in the quotient model.
def chapter07CauchyConstant
    {K : Type*} [AddGroup K] [UniformSpace K] [IsUniformAddGroup K]
    (x : K) : chapter07CauchySequence K :=
  ⟨fun _ => x, cauchySeq_const x⟩

-- The constant-sequence map into the Cauchy quotient.
def chapter07CauchyConstantEmbedding
    {K : Type*} [AddGroup K] [UniformSpace K] [IsUniformAddGroup K] :
    K → chapter07CauchyCompletion K :=
  fun x => chapter07CauchyClass (chapter07CauchyConstant x)

-- Termwise addition descends to equivalence classes.
def chapter07CauchyCompletionAdd
    {K : Type*} [AddCommGroup K] [UniformSpace K] [IsUniformAddGroup K]
    (x y : chapter07CauchyCompletion K) : chapter07CauchyCompletion K :=
  Quotient.liftOn₂ x y
    (fun u v => chapter07CauchyClass (chapter07CauchySequenceAdd u v))
    (by
      intro u₁ v₁ u₂ v₂ hu hv
      apply Quotient.sound
      change Tendsto (fun n => u₁.1 n - u₂.1 n) atTop (𝓝 0) at hu
      change Tendsto (fun n => v₁.1 n - v₂.1 n) atTop (𝓝 0) at hv
      change Tendsto
        (fun n => (u₁.1 n + v₁.1 n) - (u₂.1 n + v₂.1 n)) atTop (𝓝 0)
      have hfun : (fun n => (u₁.1 n + v₁.1 n) - (u₂.1 n + v₂.1 n)) =
          (fun n => (u₁.1 n - u₂.1 n) + (v₁.1 n - v₂.1 n)) := by
        funext n
        simp only [sub_eq_add_neg, neg_add_rev]
        abel
      rw [hfun]
      simpa only [add_zero] using hu.add hv)

-- Termwise multiplication descends to equivalence classes.
def chapter07CauchyCompletionMul
    {K : Type*} [Ring K] [UniformSpace K] [IsUniformAddGroup K]
    [IsTopologicalRing K]
    (x y : chapter07CauchyCompletion K) : chapter07CauchyCompletion K :=
  Quotient.liftOn₂ x y
    (fun u v => chapter07CauchyClass (chapter07CauchySequenceMul u v))
    (by
      intro u₁ v₁ u₂ v₂ hu hv
      apply Quotient.sound
      change Tendsto (fun n => u₁.1 n - u₂.1 n) atTop (𝓝 0) at hu
      change Tendsto (fun n => v₁.1 n - v₂.1 n) atTop (𝓝 0) at hv
      change Tendsto
        (fun n => u₁.1 n * v₁.1 n - u₂.1 n * v₂.1 n) atTop (𝓝 0)
      exact chapter07_cauchy_mul_respects_equivalence_aux
        u₁.1 u₂.1 v₁.1 v₂.1 hu hv u₁.2 u₂.2 v₁.2 v₂.2)

-- The quotient zero and one represented by constant sequences.
def chapter07CauchyCompletionZero
    {K : Type*} [AddGroup K] [UniformSpace K] [IsUniformAddGroup K] :
    chapter07CauchyCompletion K :=
  chapter07CauchyConstantEmbedding 0

def chapter07CauchyCompletionOne
    {K : Type*} [Ring K] [UniformSpace K] [IsUniformAddGroup K] :
    chapter07CauchyCompletion K :=
  chapter07CauchyConstantEmbedding 1

-- Section 7.1: termwise addition is independent of representatives.
theorem chapter07_cauchy_add_respects_equivalence
    {K : Type*} [AddCommGroup K] [UniformSpace K] [IsUniformAddGroup K]
    (u₁ u₂ v₁ v₂ : chapter07CauchySequence K)
    (hu : chapter07CauchyEquivalent K u₁ u₂)
    (hv : chapter07CauchyEquivalent K v₁ v₂) :
    chapter07CauchyEquivalent K
      (chapter07CauchySequenceAdd u₁ v₁)
      (chapter07CauchySequenceAdd u₂ v₂) := by
  change Tendsto (fun n => u₁.1 n - u₂.1 n) atTop (𝓝 0) at hu
  change Tendsto (fun n => v₁.1 n - v₂.1 n) atTop (𝓝 0) at hv
  change Tendsto
    (fun n => (u₁.1 n + v₁.1 n) - (u₂.1 n + v₂.1 n)) atTop (𝓝 0)
  have hfun : (fun n => (u₁.1 n + v₁.1 n) - (u₂.1 n + v₂.1 n)) =
      (fun n => (u₁.1 n - u₂.1 n) + (v₁.1 n - v₂.1 n)) := by
    funext n
    simp only [sub_eq_add_neg, neg_add_rev]
    abel
  rw [hfun]
  simpa only [add_zero] using hu.add hv

-- Section 7.1: termwise multiplication is independent of representatives.
theorem chapter07_cauchy_mul_respects_equivalence
    {K : Type*} [Ring K] [UniformSpace K] [IsUniformAddGroup K]
    [IsTopologicalRing K]
    (u₁ u₂ v₁ v₂ : chapter07CauchySequence K)
    (hu : chapter07CauchyEquivalent K u₁ u₂)
    (hv : chapter07CauchyEquivalent K v₁ v₂) :
    chapter07CauchyEquivalent K
      (chapter07CauchySequenceMul u₁ v₁)
      (chapter07CauchySequenceMul u₂ v₂) := by
  change Tendsto (fun n => u₁.1 n - u₂.1 n) atTop (𝓝 0) at hu
  change Tendsto (fun n => v₁.1 n - v₂.1 n) atTop (𝓝 0) at hv
  change Tendsto
    (fun n => u₁.1 n * v₁.1 n - u₂.1 n * v₂.1 n) atTop (𝓝 0)
  exact chapter07_cauchy_mul_respects_equivalence_aux
    u₁.1 u₂.1 v₁.1 v₂.1 hu hv u₁.2 u₂.2 v₁.2 v₂.2

-- The constant-sequence map is injective.
theorem chapter07_cauchy_constant_embedding_injective
    {K : Type*} [AddGroup K] [UniformSpace K] [IsUniformAddGroup K] [T0Space K] :
    Function.Injective (@chapter07CauchyConstantEmbedding K _ _ _) := by
  intro x y hxy
  apply sub_eq_zero.mp
  have h : chapter07CauchyEquivalent K
      (chapter07CauchyConstant x) (chapter07CauchyConstant y) := by
    exact Quotient.exact hxy
  have hlim : Tendsto (fun _ : ℕ => x - y) atTop (𝓝 (0 : K)) := by
    simpa [chapter07CauchyConstant, chapter07CauchyEquivalent] using h
  exact (tendsto_nhds_unique hlim tendsto_const_nhds).symm

/- A discrete nonarchimedean absolute value compatible with the given uniformity. -/
class Chapter07NonarchimedeanStationarity
    (K : Type*) [Field K] [UniformSpace K] [IsUniformAddGroup K]
    (abv : AbsoluteValue K ℝ) : Prop where
  nonarchimedean : ∀ x y : K, abv (x + y) ≤ max (abv x) (abv y)
  discrete : ∃ q : ℝ, 0 < q ∧ q < 1 ∧
    ∀ {x : K}, x ≠ 0 → ∃ z : ℤ, abv x = q ^ z
  compatible : Continuous (abv : K → ℝ)
  uniformSpace_eq : (inferInstance : UniformSpace K) = abv.uniformSpace

lemma chapter07_absolute_value_uniformContinuous
    {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K]
    (abv : AbsoluteValue K ℝ)
    [Chapter07NonarchimedeanStationarity K abv] :
    UniformContinuous (abv : K → ℝ) := by
  have h' : @UniformContinuous K ℝ abv.uniformSpace _ abv := by
    let : UniformSpace K := abv.uniformSpace
    refine (AbsoluteValue.hasBasis_uniformity abv).uniformContinuous_iff
      Metric.uniformity_basis_dist |>.2 ?_
    intro ε hε
    refine ⟨ε, hε, ?_⟩
    intro x y hxy
    change dist (abv x) (abv y) < ε
    rw [Real.dist_eq]
    exact (abv.abs_abv_sub_le_abv_sub x y).trans_lt
      (by
        rw [← abv.map_neg]
        simpa [Set.mem_ofPred_eq, sub_eq_add_neg, add_comm] using hxy)
  have heq := Chapter07NonarchimedeanStationarity.uniformSpace_eq
    (K := K) (abv := abv)
  rw [← heq] at h'
  exact h'

-- A representative formula for the extended absolute value.
def chapter07CauchyAbsoluteValue
    {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K]
    (abv : AbsoluteValue K ℝ)
    [Chapter07NonarchimedeanStationarity K abv] :
    chapter07CauchyCompletion K → ℝ := by
  refine Quotient.lift
    (fun u : chapter07CauchySequence K =>
      limUnder (atTop : Filter ℕ) (fun n => abv (u.1 n))) ?_
  intro u v huv
  have habv_uc := chapter07_absolute_value_uniformContinuous abv
  have hu' : CauchySeq (fun n => abv (u.1 n)) :=
    habv_uc.comp_cauchySeq u.2
  have hv' : CauchySeq (fun n => abv (v.1 n)) :=
    habv_uc.comp_cauchySeq v.2
  have hlu := hu'.tendsto_limUnder
  have hlv := hv'.tendsto_limUnder
  change Tendsto (fun n => u.1 n - v.1 n) atTop (𝓝 0) at huv
  have hdiff : Tendsto (fun n => abv (u.1 n - v.1 n)) atTop (𝓝 0) := by
    have h := ((Chapter07NonarchimedeanStationarity.compatible
      (K := K) (abv := abv)).tendsto (0 : K)).comp huv
    have h' : Tendsto (fun n => abv (u.1 n - v.1 n)) atTop
        (𝓝 (abv 0)) :=
      h.congr' (Filter.Eventually.of_forall (fun _ => rfl))
    simpa only [abv.map_zero] using h'
  have hnorm : Tendsto (fun n => |abv (u.1 n) - abv (v.1 n)|)
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hdiff
      (Filter.Eventually.of_forall (fun n => abs_nonneg _))
      (Filter.Eventually.of_forall (fun n =>
        (abv.abs_abv_sub_le_abv_sub (u.1 n) (v.1 n))))
  have hsub : Tendsto (fun n => abv (u.1 n) - abv (v.1 n)) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa using hnorm
  exact sub_eq_zero.mp (tendsto_nhds_unique (hlu.sub hlv) hsub)

-- Section 7.1: the extension has the displayed representative formula.
theorem chapter07_cauchy_absolute_value_formula
    {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K]
    (abv : AbsoluteValue K ℝ) [Chapter07NonarchimedeanStationarity K abv]
    (u : chapter07CauchySequence K) :
    chapter07CauchyAbsoluteValue abv (chapter07CauchyClass u) =
      limUnder (atTop : Filter ℕ) (fun n => abv (u.1 n)) := by
  rfl

-- If a representative tends to zero, its extended absolute value is zero.
theorem chapter07_cauchy_absolute_value_limit_zero
    {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K]
    (abv : AbsoluteValue K ℝ) (u : chapter07CauchySequence K)
    (hu : Tendsto u.1 (atTop : Filter ℕ) (𝓝 0))
    (habv : Continuous (abv : K → ℝ)) :
    Tendsto (fun n => abv (u.1 n)) (atTop : Filter ℕ) (𝓝 0) := by
  have h := (habv.tendsto (0 : K)).comp hu
  have h' : Tendsto (fun n => abv (u.1 n)) atTop (𝓝 (abv 0)) :=
    h.congr' (Filter.Eventually.of_forall (fun _ => rfl))
  simpa only [abv.map_zero] using h'

-- The absolute value of a zero-limit representative is zero in the quotient.
theorem chapter07_cauchy_absolute_value_of_zero_limit
    {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K]
    (abv : AbsoluteValue K ℝ) [Chapter07NonarchimedeanStationarity K abv]
    (u : chapter07CauchySequence K)
    (hu : Tendsto u.1 (atTop : Filter ℕ) (𝓝 0))
    (habv : Continuous (abv : K → ℝ)) :
    chapter07CauchyAbsoluteValue abv (chapter07CauchyClass u) = 0 := by
  rw [chapter07_cauchy_absolute_value_formula]
  have hlim :=
    (chapter07_absolute_value_uniformContinuous abv).comp_cauchySeq u.2 |>.tendsto_limUnder
  exact tendsto_nhds_unique hlim (chapter07_cauchy_absolute_value_limit_zero abv u hu habv)

-- A nonzero norm sequence that is eventually constant.
def chapter07EventuallyConstantAbsoluteValue
    {K : Type*} [Field K] [UniformSpace K]
    (abv : AbsoluteValue K ℝ) (u : chapter07CauchySequence K) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in (atTop : Filter ℕ), abv (u.1 n) = c


-- Section 7.1: a nonzero Cauchy class has eventually constant positive absolute value.
theorem chapter07_nonzero_cauchy_absolute_value_eventually_constant
    {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K]
    (abv : AbsoluteValue K ℝ)
    [Chapter07NonarchimedeanStationarity K abv]
    (u : chapter07CauchySequence K)
    (hu : ¬ Tendsto u.1 (atTop : Filter ℕ) (𝓝 0)) :
    chapter07EventuallyConstantAbsoluteValue abv u := by
  have habs : ¬ Tendsto (fun n => abv (u.1 n)) atTop (𝓝 (0 : ℝ)) := by
    intro habs
    apply hu
    have heq := Chapter07NonarchimedeanStationarity.uniformSpace_eq
      (K := K) (abv := abv)
    have hconv : @Tendsto ℕ K u.1 atTop
        (@nhds K abv.uniformSpace.toTopologicalSpace (0 : K)) := by
      let : UniformSpace K := abv.uniformSpace
      refine Uniform.tendsto_nhds_right.2 ?_
      intro V hV
      obtain ⟨ε, hε, hsub⟩ :=
        (AbsoluteValue.hasBasis_uniformity abv).mem_iff.1 hV
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 habs) ε hε
      rw [mem_map]
      filter_upwards [eventually_ge_atTop N] with n hn
      apply hsub
      simpa [abv.map_zero, Real.dist_eq, abs_of_nonneg (abv.nonneg _)] using hN n hn
    have htop := congrArg (fun u : UniformSpace K => u.toTopologicalSpace) heq
    change @Tendsto ℕ K u.1 atTop
      (@nhds K (inferInstance : TopologicalSpace K) (0 : K))
    exact htop.symm ▸ hconv
  have hnotall : ¬ ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, abv (u.1 n) < ε := by
    intro h
    apply habs
    refine Metric.tendsto_atTop.2 ?_
    intro ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨N, ?_⟩
    intro n hn
    simpa [Real.dist_eq, abs_of_nonneg (abv.nonneg _)] using hN n hn
  push Not at hnotall
  obtain ⟨ε, hε, hεfreq⟩ := hnotall
  have hεfreq' : ∀ N : ℕ, ∃ n ≥ N, ε ≤ abv (u.1 n) := by
    intro N
    obtain ⟨n, hn, h⟩ := hεfreq N
    exact ⟨n, hn, h⟩
  have hrel' : {p : K × K | abv (p.2 - p.1) < ε} ∈
      @uniformity K abv.uniformSpace :=
    (AbsoluteValue.hasBasis_uniformity abv).mem_iff.2 ⟨ε, hε, subset_rfl⟩
  have heq := Chapter07NonarchimedeanStationarity.uniformSpace_eq
    (K := K) (abv := abv)
  have hrel : {p : K × K | abv (p.2 - p.1) < ε} ∈
      @uniformity K (inferInstance : UniformSpace K) := heq.symm ▸ hrel'
  obtain ⟨N₁, hN₁⟩ := u.2.mem_entourage hrel
  obtain ⟨N₀, hN₀, hN₀val⟩ := hεfreq' N₁
  let c : ℝ := abv (u.1 N₀)
  have hc : 0 < c := lt_of_lt_of_le hε hN₀val
  refine ⟨c, hc, ?_⟩
  filter_upwards [eventually_ge_atTop N₀] with n hn
  have hn₁ : N₁ ≤ n := le_trans hN₀ hn
  have hsmall : abv (u.1 n - u.1 N₀) < c := by
    have h := hN₁ n N₀ hn₁ hN₀
    have h' : abv (u.1 N₀ - u.1 n) < ε := by
      simpa using h
    rw [show u.1 n - u.1 N₀ = -(u.1 N₀ - u.1 n) by ring,
      abv.map_neg]
    exact lt_of_lt_of_le h' (by simpa [c] using hN₀val)
  have hle : abv (u.1 n) ≤ c := by
    calc
      abv (u.1 n) = abv ((u.1 n - u.1 N₀) + u.1 N₀) := by ring_nf
      _ ≤ max (abv (u.1 n - u.1 N₀)) c :=
        Chapter07NonarchimedeanStationarity.nonarchimedean
          (K := K) (abv := abv) _ _
      _ = c := max_eq_right hsmall.le
  have hge : c ≤ abv (u.1 n) := by
    have hsmall' : abv (u.1 N₀ - u.1 n) < c := by
      have h := hN₁ n N₀ hn₁ hN₀
      exact lt_of_lt_of_le h (by simpa [c] using hN₀val)
    have hmax : c ≤ max (abv (u.1 N₀ - u.1 n)) (abv (u.1 n)) := by
      calc
        c = abv (u.1 N₀) := rfl
        _ = abv ((u.1 N₀ - u.1 n) + u.1 n) := by ring_nf
        _ ≤ max (abv (u.1 N₀ - u.1 n)) (abv (u.1 n)) :=
          Chapter07NonarchimedeanStationarity.nonarchimedean
            (K := K) (abv := abv) _ _
    by_contra h
    have hlt : abv (u.1 n) < c := lt_of_not_ge h
    exact (not_lt_of_ge hmax) (max_lt hsmall' hlt)
  exact le_antisymm hle hge

-- The extended absolute value is independent of the representative.
theorem chapter07_cauchy_absolute_value_representative_independent
    {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K]
    (abv : AbsoluteValue K ℝ) [Chapter07NonarchimedeanStationarity K abv]
    (u v : chapter07CauchySequence K)
    (h : chapter07CauchyEquivalent K u v) :
    chapter07CauchyAbsoluteValue abv (chapter07CauchyClass u) =
      chapter07CauchyAbsoluteValue abv (chapter07CauchyClass v) := by
  exact congrArg (chapter07CauchyAbsoluteValue abv) (Quotient.sound h)

/- The quotient model carries the uniformity transported from Mathlib's canonical completion. -/
structure Chapter07CauchyCompletionModel
    (K : Type*) [Field K] [UniformSpace K] [IsUniformAddGroup K] where
  uniformSpace : UniformSpace (chapter07CauchyCompletion K)
  complete : @CompleteSpace (chapter07CauchyCompletion K) uniformSpace
  equivalent : chapter07CauchyCompletion K ≃ UniformSpace.Completion K
  equivalent_coe : ∀ x : K,
    equivalent (chapter07CauchyConstantEmbedding x) =
      (x : UniformSpace.Completion K)
  uniform_to_completion :
    @UniformContinuous (chapter07CauchyCompletion K) (UniformSpace.Completion K)
      uniformSpace inferInstance equivalent
  uniform_from_completion :
    @UniformContinuous (UniformSpace.Completion K) (chapter07CauchyCompletion K)
      inferInstance uniformSpace equivalent.symm

-- Section 7.1: a diagonal argument makes the Cauchy quotient complete.
theorem chapter07_cauchy_quotient_complete
    {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K]
    (abv : AbsoluteValue K ℝ)
    [Chapter07NonarchimedeanStationarity K abv] :
    Nonempty (Chapter07CauchyCompletionModel K) := by
  obtain ⟨q, hqpos, hqone, hqrepr⟩ :=
    Chapter07NonarchimedeanStationarity.discrete (K := K) (abv := abv)
  let S : ℕ → SetRel K K := fun n =>
    {p | abv (p.2 - p.1) < q ^ n}
  have hS_basis_abv : (@uniformity K abv.uniformSpace).HasBasis
      (fun _ : ℕ => True) S := by
    refine ⟨fun U => ?_⟩
    constructor
    · intro hU
      obtain ⟨ε, hε, hsub⟩ :=
        (AbsoluteValue.hasBasis_uniformity abv).mem_iff.mp hU
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hqone
      exact ⟨n, trivial, fun x hx => hsub (lt_of_lt_of_le hx hn.le)⟩
    · rintro ⟨n, -, hsub⟩
      exact mem_of_superset
        ((AbsoluteValue.hasBasis_uniformity abv).mem_iff.mpr ⟨q ^ n,
          pow_pos hqpos n, subset_rfl⟩) hsub
  have habv_eq : (@uniformity K (inferInstance : UniformSpace K)) =
      @uniformity K abv.uniformSpace := by
    exact congrArg (fun u : UniformSpace K => u.uniformity)
      (Chapter07NonarchimedeanStationarity.uniformSpace_eq (K := K) (abv := abv))
  have hS_basis : (@uniformity K (inferInstance : UniformSpace K)).HasBasis
      (fun _ : ℕ => True) S := by
    rw [habv_eq]
    exact hS_basis_abv
  let : IsCountablyGenerated (@uniformity K (inferInstance : UniformSpace K)) :=
    hS_basis.isCountablyGenerated
  let : IsCountablyGenerated (@uniformity (CauchyFilter K)
      (inferInstance : UniformSpace (CauchyFilter K))) := by
    exact (CauchyFilter.basis_uniformity hS_basis).isCountablyGenerated
  let : IsCountablyGenerated (@uniformity (UniformSpace.Completion K)
      (inferInstance : UniformSpace (UniformSpace.Completion K))) := by
    change IsCountablyGenerated (@uniformity
      (SeparationQuotient (CauchyFilter K)) _)
    rw [SeparationQuotient.uniformity_eq]
    infer_instance
  let toComp : chapter07CauchyCompletion K → UniformSpace.Completion K :=
    Quotient.lift
      (fun u : chapter07CauchySequence K =>
        limUnder (atTop : Filter ℕ)
          (fun n => ((u.1 n : K) : UniformSpace.Completion K)))
      (by
        intro u v huv
        have hu' : CauchySeq
            (fun n => ((u.1 n : K) : UniformSpace.Completion K)) :=
          (UniformSpace.Completion.isUniformInducing_coe K).uniformContinuous.comp_cauchySeq u.2
        have hv' : CauchySeq
            (fun n => ((v.1 n : K) : UniformSpace.Completion K)) :=
          (UniformSpace.Completion.isUniformInducing_coe K).uniformContinuous.comp_cauchySeq v.2
        have hu_lim := hu'.tendsto_limUnder
        have hv_lim := hv'.tendsto_limUnder
        have hdiff : Tendsto
            (fun n => ((u.1 n - v.1 n : K) : UniformSpace.Completion K))
            atTop (𝓝 (0 : UniformSpace.Completion K)) := by
          have h := ((UniformSpace.Completion.continuous_coe (α := K)).tendsto (0 : K)).comp huv
          convert h using 1
          · funext n
            simp
          · rfl
        have hdiff' : Tendsto
            (fun n => ((u.1 n : UniformSpace.Completion K) -
              (v.1 n : UniformSpace.Completion K))) atTop
              (𝓝 (0 : UniformSpace.Completion K)) := by
          simpa only [UniformSpace.Completion.coe_sub] using hdiff
        have heq := tendsto_nhds_unique (hu_lim.sub hv_lim) hdiff'
        exact sub_eq_zero.mp heq)
  have toComp_surj : Function.Surjective toComp := by
    intro x
    have hcluster : MapClusterPt x (𝓟 (Set.univ : Set K))
        (fun r : K => (r : UniformSpace.Completion K)) := by
      rw [MapClusterPt, Filter.map_principal, image_univ]
      exact (mem_closure_iff_clusterPt).mp
        ((UniformSpace.Completion.denseRange_coe (α := K) :
          DenseRange ((↑) : K → UniformSpace.Completion K)) x)
    obtain ⟨u, hu, _huuniv⟩ := hcluster.exists_seq_tendsto
    have hu' : CauchySeq
        (fun n => ((u n : K) : UniformSpace.Completion K)) := hu.cauchySeq
    have huK : CauchySeq u :=
      (UniformSpace.Completion.isUniformInducing_coe K).cauchy_map_iff.mp hu'
    let cu : chapter07CauchySequence K := ⟨u, huK⟩
    refine ⟨chapter07CauchyClass cu, ?_⟩
    change limUnder atTop (fun n => ((u n : K) : UniformSpace.Completion K)) = x
    have hu_point : Tendsto
        (fun n => ((u n : K) : UniformSpace.Completion K)) atTop (𝓝 x) := by
      exact hu.congr' (Filter.Eventually.of_forall (fun n => rfl))
    exact tendsto_nhds_unique hu'.tendsto_limUnder hu_point
  have toComp_inj : Function.Injective toComp := by
    intro x y hxy
    obtain ⟨u, rfl⟩ := Quotient.exists_rep x
    obtain ⟨v, rfl⟩ := Quotient.exists_rep y
    apply Quotient.sound
    have hu' : CauchySeq
        (fun n => ((u.1 n : K) : UniformSpace.Completion K)) :=
      (UniformSpace.Completion.isUniformInducing_coe K).uniformContinuous.comp_cauchySeq u.2
    have hv' : CauchySeq
        (fun n => ((v.1 n : K) : UniformSpace.Completion K)) :=
      (UniformSpace.Completion.isUniformInducing_coe K).uniformContinuous.comp_cauchySeq v.2
    have hlimu := hu'.tendsto_limUnder
    have hlimv := hv'.tendsto_limUnder
    have hdiff : Tendsto
        (fun n => ((u.1 n : UniformSpace.Completion K) -
          (v.1 n : UniformSpace.Completion K))) atTop
          (𝓝 (0 : UniformSpace.Completion K)) := by
      have h := hlimu.sub hlimv
      change limUnder atTop (fun n => ((u.1 n : K) : UniformSpace.Completion K)) =
        limUnder atTop (fun n => ((v.1 n : K) : UniformSpace.Completion K)) at hxy
      rw [hxy, sub_self] at h
      exact h
    have hdiffK : Tendsto (fun n => u.1 n - v.1 n) atTop (𝓝 (0 : K)) := by
      apply ((UniformSpace.Completion.isUniformInducing_coe K).isInducing.tendsto_nhds_iff).2
      simpa only [Function.comp_def, UniformSpace.Completion.coe_sub,
        UniformSpace.Completion.coe_zero] using hdiff
    exact hdiffK
  let e : chapter07CauchyCompletion K ≃ UniformSpace.Completion K :=
    Equiv.ofBijective toComp ⟨toComp_inj, toComp_surj⟩
  let uq : UniformSpace (chapter07CauchyCompletion K) :=
    UniformSpace.comap e inferInstance
  let : UniformSpace (chapter07CauchyCompletion K) := uq
  have heui : IsUniformInducing (e : chapter07CauchyCompletion K →
      UniformSpace.Completion K) := by
    exact (isUniformInducing_iff_uniformSpace).2 rfl
  have hecomplete : @CompleteSpace (chapter07CauchyCompletion K) uq := by
    apply (_root_.completeSpace_congr
      (e := e) ⟨heui, e.injective⟩).2
    infer_instance
  refine ⟨{
    uniformSpace := uq
    complete := hecomplete
    equivalent := e
    equivalent_coe := by
      intro x
      change limUnder atTop (fun _ : ℕ => ((x : K) : UniformSpace.Completion K)) =
        ((x : K) : UniformSpace.Completion K)
      exact (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => ((x : K) : UniformSpace.Completion K))
          atTop (𝓝 ((x : K) : UniformSpace.Completion K))).limUnder_eq
    uniform_to_completion := heui.uniformContinuous
    uniform_from_completion := ?_ }⟩
  apply (heui.uniformContinuous_iff).2
  simpa using (uniformContinuous_id :
    UniformContinuous (id : UniformSpace.Completion K → UniformSpace.Completion K))

-- The diagonal representative assertion used to prove completeness.
theorem chapter07_cauchy_diagonal_representative
    {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K]
    (x : chapter07CauchyCompletion K) :
    ∃ u : chapter07CauchySequence K,
      x = chapter07CauchyClass u := by
  obtain ⟨u, rfl⟩ := Quotient.exists_rep x
  exact ⟨u, rfl⟩

end
end LastLib.Book01ValuationsDVRsAndCompletions.Chapter07
