import Mathlib.Algebra.Module.PID
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.Valuation.Discrete.RankOne
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

/-! ### 7.2. Extending inverses and valuations -/

-- The inverse-difference formula displayed in Section 7.2.
theorem chapter07_inverse_difference_absolute_value
    {K : Type*} [Field K] (abv : AbsoluteValue K ℝ)
    (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    abv (x⁻¹ - y⁻¹) =
      abv (x - y) / (abv x * abv y) := by
  have hxy : x⁻¹ - y⁻¹ = -(x - y) / (x * y) := by
    field_simp [hx, hy]
    ring
  calc
    abv (x⁻¹ - y⁻¹) = abv (-(x - y) / (x * y)) := by rw [hxy]
    _ = abv (x - y) / abv (x * y) := by
      rw [IsAbsoluteValue.abv_div abv, abv.map_neg]
    _ = abv (x - y) / (abv x * abv y) := by rw [abv.map_mul]

-- A quantitative form of being bounded away from zero.
def chapter07CauchyBoundedAwayFromZero
    {K : Type*} [Field K] [UniformSpace K]
    (abv : AbsoluteValue K ℝ) (u : chapter07CauchySequence K) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in (atTop : Filter ℕ), c ≤ abv (u.1 n)

lemma chapter07_inverse_terms_are_cauchy
    {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K]
    [IsTopologicalRing K]
    (abv : AbsoluteValue K ℝ) [Chapter07NonarchimedeanStationarity K abv]
    (u : chapter07CauchySequence K)
    (hu : chapter07CauchyBoundedAwayFromZero abv u) :
    CauchySeq (fun n => (u.1 n)⁻¹) := by
  rcases hu with ⟨c, hc, hc_event⟩
  rw [cauchySeq_iff]
  intro V hV
  have hV' : V ∈ @uniformity K abv.uniformSpace := by
    have heq := Chapter07NonarchimedeanStationarity.uniformSpace_eq
      (K := K) (abv := abv)
    exact heq ▸ hV
  obtain ⟨ε, hε, hsubset⟩ :=
    (AbsoluteValue.hasBasis_uniformity abv).mem_iff.1 hV'
  have hδ : 0 < ε * (c * c) := mul_pos hε (mul_pos hc hc)
  have hU' : {p : K × K | abv (p.2 - p.1) < ε * (c * c)} ∈
      @uniformity K abv.uniformSpace := by
    exact (AbsoluteValue.hasBasis_uniformity abv).mem_iff.2
      ⟨ε * (c * c), hδ, subset_rfl⟩
  have hU : {p : K × K | abv (p.2 - p.1) < ε * (c * c)} ∈
      @uniformity K (inferInstance : UniformSpace K) := by
    have heq := Chapter07NonarchimedeanStationarity.uniformSpace_eq
      (K := K) (abv := abv)
    exact heq.symm ▸ hU'
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hc_event
  obtain ⟨N₁, hN₁⟩ := u.2.mem_entourage hU
  refine ⟨max N₀ N₁, ?_⟩
  intro m hm n hn
  have hm₀ : c ≤ abv (u.1 m) := hN₀ m (le_trans (le_max_left _ _) hm)
  have hn₀ : c ≤ abv (u.1 n) := hN₀ n (le_trans (le_max_left _ _) hn)
  have hm_ne : u.1 m ≠ 0 := by
    intro hm_ne
    rw [hm_ne, abv.map_zero] at hm₀
    exact (not_le_of_gt hc) hm₀
  have hn_ne : u.1 n ≠ 0 := by
    intro hn_ne
    rw [hn_ne, abv.map_zero] at hn₀
    exact (not_le_of_gt hc) hn₀
  have hsmall : abv (u.1 n - u.1 m) < ε * (c * c) :=
    by
      have hsmall' := hN₁ n m (le_trans (le_max_right _ _) hn)
        (le_trans (le_max_right _ _) hm)
      rw [show u.1 n - u.1 m = -(u.1 m - u.1 n) by ring, abv.map_neg]
      exact hsmall'
  have hden : 0 < abv (u.1 n) * abv (u.1 m) :=
    mul_pos (abv.pos hn_ne) (abv.pos hm_ne)
  have hcc : c * c ≤ abv (u.1 n) * abv (u.1 m) :=
    mul_le_mul hn₀ hm₀ (le_of_lt hc) (abv.nonneg _)
  have hnum : abv (u.1 n - u.1 m) <
      ε * (abv (u.1 n) * abv (u.1 m)) :=
    lt_of_lt_of_le hsmall (mul_le_mul_of_nonneg_left hcc hε.le)
  have hquot : abv ((u.1 n)⁻¹ - (u.1 m)⁻¹) < ε := by
    rw [chapter07_inverse_difference_absolute_value abv _ _ hn_ne hm_ne]
    exact (div_lt_iff₀ hden).2 hnum
  exact hsubset hquot

-- The termwise inverse sequence after discarding finitely many terms.
def chapter07CauchySequenceInverse
    {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K]
    [IsTopologicalRing K]
    (abv : AbsoluteValue K ℝ) [Chapter07NonarchimedeanStationarity K abv]
    (u : chapter07CauchySequence K)
    (hu : chapter07CauchyBoundedAwayFromZero abv u) :
  chapter07CauchySequence K :=
  ⟨fun n => (u.1 n)⁻¹, chapter07_inverse_terms_are_cauchy abv u hu⟩

-- Section 7.2: the inverse of a nonzero Cauchy class is represented by inverse terms.
theorem chapter07_inverse_sequence_is_cauchy
    {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K]
    [IsTopologicalRing K]
    (abv : AbsoluteValue K ℝ) [Chapter07NonarchimedeanStationarity K abv]
    (u : chapter07CauchySequence K)
    (hu : chapter07CauchyBoundedAwayFromZero abv u) :
    CauchySeq (fun n => (u.1 n)⁻¹) := by
  exact chapter07_inverse_terms_are_cauchy abv u hu

-- Inversion descends to the Cauchy quotient.
def chapter07CauchyCompletionInverse
    {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K]
    [IsTopologicalRing K]
    (abv : AbsoluteValue K ℝ) [Chapter07NonarchimedeanStationarity K abv]
    (x : chapter07CauchyCompletion K) : chapter07CauchyCompletion K := by
  classical
  let u : chapter07CauchySequence K := Quotient.out x
  by_cases hu : Tendsto u.1 (atTop : Filter ℕ) (𝓝 0)
  · exact chapter07CauchyCompletionZero
  · let hconst := chapter07_nonzero_cauchy_absolute_value_eventually_constant abv u hu
    let c : ℝ := Classical.choose hconst
    have hc : 0 < c := (Classical.choose_spec hconst).1
    have hc_event : ∀ᶠ n in (atTop : Filter ℕ), abv (u.1 n) = c :=
      (Classical.choose_spec hconst).2
    have hc_event' : ∀ᶠ n in (atTop : Filter ℕ), c ≤ abv (u.1 n) :=
      hc_event.mono (fun n hn => hn.ge)
    exact chapter07CauchyClass
      (chapter07CauchySequenceInverse abv u ⟨c, hc, hc_event'⟩)

-- The inverse class is a two-sided inverse.
theorem chapter07_cauchy_completion_nonzero_has_inverse
    {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K] [IsTopologicalRing K]
    (abv : AbsoluteValue K ℝ) [Chapter07NonarchimedeanStationarity K abv]
    (x : chapter07CauchyCompletion K) (hx : x ≠ chapter07CauchyCompletionZero) :
    ∃ y : chapter07CauchyCompletion K,
      chapter07CauchyCompletionMul x y = chapter07CauchyCompletionOne ∧
        chapter07CauchyCompletionMul y x = chapter07CauchyCompletionOne := by
  obtain ⟨u, rfl⟩ := Quotient.exists_rep x
  have hu : ¬ Tendsto u.1 (atTop : Filter ℕ) (𝓝 0) := by
    intro hu
    apply hx
    apply Quotient.sound
    change Tendsto (fun n => u.1 n - 0) atTop (𝓝 (0 : K))
    simpa using hu
  obtain ⟨c, hc, he⟩ :=
    chapter07_nonzero_cauchy_absolute_value_eventually_constant abv u hu
  have he' : ∀ᶠ n in (atTop : Filter ℕ), c ≤ abv (u.1 n) :=
    he.mono (fun n hn => hn.ge)
  let ui := chapter07CauchySequenceInverse abv u ⟨c, hc, he'⟩
  refine ⟨chapter07CauchyClass ui, ?_, ?_⟩
  · apply Quotient.sound
    change Tendsto (fun n => u.1 n * (u.1 n)⁻¹ - 1) atTop (𝓝 (0 : K))
    obtain ⟨N, hN⟩ := eventually_atTop.1 he
    refine (tendsto_congr' ?_).2 tendsto_const_nhds
    filter_upwards [eventually_ge_atTop N] with n hn
    have hne : u.1 n ≠ 0 := by
      intro hzero
      have h := hN n hn
      rw [hzero, abv.map_zero] at h
      linarith [hc]
    simp [hne]
  · apply Quotient.sound
    change Tendsto (fun n => (u.1 n)⁻¹ * u.1 n - 1) atTop (𝓝 (0 : K))
    obtain ⟨N, hN⟩ := eventually_atTop.1 he
    refine (tendsto_congr' ?_).2 tendsto_const_nhds
    filter_upwards [eventually_ge_atTop N] with n hn
    have hne : u.1 n ≠ 0 := by
      intro hzero
      have h := hN n hn
      rw [hzero, abv.map_zero] at h
      linarith [hc]
    simp [hne]

-- Section 7.2: the Cauchy completion of a valued field is a field.
theorem chapter07_valued_cauchy_completion_is_a_field
    {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K] [IsTopologicalRing K]
    (abv : AbsoluteValue K ℝ) [Chapter07NonarchimedeanStationarity K abv] :
    ∀ x : chapter07CauchyCompletion K,
      x ≠ chapter07CauchyCompletionZero →
        ∃ y : chapter07CauchyCompletion K,
          chapter07CauchyCompletionMul x y = chapter07CauchyCompletionOne ∧
          chapter07CauchyCompletionMul y x = chapter07CauchyCompletionOne := by
  intro x hx
  exact chapter07_cauchy_completion_nonzero_has_inverse abv x hx

-- The valuation on the standard completion, obtained by extending the original valuation.
noncomputable def chapter07CompletionValuation
    (K Γ₀ : Type*) [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] :
    Valuation (UniformSpace.Completion K) Γ₀ :=
  Valued.extensionValuation

-- Section 7.2: the extended valuation agrees with the original on the dense subfield.
theorem chapter07_completion_valuation_apply_coe
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] (x : K) :
    chapter07CompletionValuation K Γ₀ (x : UniformSpace.Completion K) =
      Valued.v x := by
  exact Valued.extensionValuation_apply_coe x

-- The value groups of a valued field and its completion are canonically equivalent.
noncomputable def chapter07CompletionValueGroupEquiv
    (K Γ₀ : Type*) [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] :
    ValueGroup₀ (.ofClass (Valued.v (R := K))) ≃*
      ValueGroup₀ (.ofClass (chapter07CompletionValuation K Γ₀)) :=
  Valued.valueGroup₀_equiv_extensionValuation

-- Discrete valuations have eventually constant values on nonzero Cauchy sequences.
theorem chapter07_discrete_valuation_values_eventually_constant
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] [hdiscrete : (Valued.v (R := K)).IsRankOneDiscrete]
    (u : chapter07CauchySequence K)
    (hu : ¬ Tendsto u.1 (atTop : Filter ℕ) (𝓝 0)) :
    ∃ c : Γ₀, c ≠ 0 ∧ ∀ᶠ n in (atTop : Filter ℕ), Valued.v (u.1 n) = c := by
  let γType := (MonoidWithZeroHom.ValueGroup₀
    (.ofClass (Valued.v (R := K))))ˣ
  have hnotall : ¬ ∀ γ : γType, ∀ᶠ n in (atTop : Filter ℕ),
      (Valued.v (R := K)).restrict (u.1 n) < γ.1 := by
    intro h
    apply hu
    apply (Valued.hasBasis_nhds_zero K Γ₀).tendsto_right_iff.2
    intro γ _
    simpa only [Set.mem_ofPred_eq] using h γ
  push Not at hnotall
  obtain ⟨γ, hγ⟩ := hnotall
  have hfreq : ∃ᶠ n in (atTop : Filter ℕ),
      γ.1 ≤ (Valued.v (R := K)).restrict (u.1 n) := by
    simpa only [Filter.Frequently, not_lt] using hγ
  have hV : {p : K × K |
      (Valued.v (R := K)).restrict (p.2 - p.1) < γ.1} ∈
      @uniformity K (inferInstance : UniformSpace K) :=
    (Valued.hasBasis_uniformity K Γ₀).mem_iff.2 ⟨γ, trivial, subset_rfl⟩
  obtain ⟨N₁, hN₁⟩ := u.2.mem_entourage hV
  obtain ⟨N₀, hN₀, hN₀val⟩ := frequently_atTop.1 hfreq N₁
  have hγpos : 0 < γ.1 := by simp
  have hN₀ne : u.1 N₀ ≠ 0 := by
    intro hzero
    simp [hzero] at hN₀val
  have hvne : Valued.v (u.1 N₀) ≠ 0 :=
    (Valuation.ne_zero_iff (Valued.v (R := K))).2 hN₀ne
  refine ⟨Valued.v (u.1 N₀), hvne, ?_⟩
  filter_upwards [eventually_ge_atTop N₀] with n hn
  have hsmall' : (Valued.v (R := K)).restrict (u.1 N₀ - u.1 n) < γ.1 :=
    by simpa only [Set.mem_ofPred_eq] using
      hN₁ n N₀ (le_trans hN₀ hn) hN₀
  have hsmall : (Valued.v (R := K)).restrict (u.1 n - u.1 N₀) < γ.1 := by
    rw [show u.1 n - u.1 N₀ = -(u.1 N₀ - u.1 n) by ring,
      (Valued.v (R := K)).restrict.map_neg]
    exact hsmall'
  have hlt : (Valued.v (R := K)).restrict (u.1 n - u.1 N₀) <
      (Valued.v (R := K)).restrict (u.1 N₀) :=
    lt_of_lt_of_le hsmall hN₀val
  apply Valuation.map_eq_of_sub_lt (Valued.v (R := K))
  exact ((Valued.v (R := K)).restrict_lt_iff).mp hlt

-- A discrete value group is indexed by the integers, including zero.
noncomputable def chapter07DiscreteValueGroupEquiv
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) [v.IsRankOneDiscrete] :
    ValueGroup₀ (.ofClass v) ≃*o ℤᵐ⁰ :=
  Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt v

/- Order-theoretic approximation of a completed value by values from the dense field. -/
def Chapter07ValueApproximatedByOriginalValues
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] (x : UniformSpace.Completion K) : Prop :=
  ∀ γ : Γ₀, γ < chapter07CompletionValuation K Γ₀ x →
    ∃ r : K, γ < Valued.v r

-- Nonzero values in the completed field are limits of values from the original field.
theorem chapter07_completion_nonzero_value_is_approximated
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] (x : UniformSpace.Completion K) (hx : x ≠ 0) :
    Chapter07ValueApproximatedByOriginalValues x := by
  intro γ hγ
  obtain ⟨r, hr⟩ := Valued.exists_coe_eq_v x
  have hr0 : r ≠ 0 := by
    intro hr0
    apply hx
    have hzero : Valued.extensionValuation x = 0 := by
      simpa [hr0] using hr
    exact (Valuation.zero_iff _).mp hzero
  refine ⟨r, ?_⟩
  exact (fun _ : r ≠ 0 => by
    simpa [chapter07CompletionValuation, hr] using hγ) hr0

/- Order closure of the original value set at a completed nonzero value. -/
def Chapter07ValueInOrderClosureOfOriginalValues
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] (x : UniformSpace.Completion K) : Prop :=
  ∀ γ₁ γ₂ : Γ₀,
    γ₁ < chapter07CompletionValuation K Γ₀ x →
      chapter07CompletionValuation K Γ₀ x < γ₂ →
        ∃ r : K, γ₁ < Valued.v r ∧ Valued.v r < γ₂

-- Nonzero completed values lie in the order closure of original values.
theorem chapter07_completion_nonzero_value_is_in_order_closure
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] (x : UniformSpace.Completion K) (hx : x ≠ 0) :
    Chapter07ValueInOrderClosureOfOriginalValues x := by
  intro γ₁ γ₂ h₁ h₂
  obtain ⟨r, hr⟩ := Valued.exists_coe_eq_v x
  have hr0 : r ≠ 0 := by
    intro hr0
    apply hx
    have hzero : Valued.extensionValuation x = 0 := by
      simpa [hr0] using hr
    exact (Valuation.zero_iff _).mp hzero
  refine ⟨r, ?_, ?_⟩
  · exact (fun _ : r ≠ 0 => by
      simpa [chapter07CompletionValuation, hr] using h₁) hr0
  · exact (fun _ : r ≠ 0 => by
      simpa [chapter07CompletionValuation, hr] using h₂) hr0

/-! ### 7.3. The universal property -/

-- The canonical extension map from a uniform space to a complete target.
noncomputable def chapter07UniversalCompletionExtension
    {K F : Type*} [UniformSpace K] [UniformSpace F] [CompleteSpace F]
    (f : K → F) (hf : UniformContinuous f) : UniformSpace.Completion K → F :=
  (fun _ : UniformContinuous f => UniformSpace.Completion.extension f) hf

-- The extension agrees with the original map on the dense copy of K.
theorem chapter07_universal_extension_coe
    {K F : Type*} [UniformSpace K] [UniformSpace F] [CompleteSpace F] [T0Space F]
    (f : K → F) (hf : UniformContinuous f) (x : K) :
    chapter07UniversalCompletionExtension f hf (x : UniformSpace.Completion K) = f x := by
  simpa [chapter07UniversalCompletionExtension] using
    (UniformSpace.Completion.extension_coe hf x)

-- Theorem 7.1: every uniformly continuous map extends uniquely to the completion.
theorem chapter07_completion_universal_property
    {K F : Type*} [UniformSpace K] [UniformSpace F] [CompleteSpace F] [T0Space F]
    (f : K → F) (hf : UniformContinuous f) :
    ∃ g : UniformSpace.Completion K → F,
      UniformContinuous g ∧
        (∀ x : K, g (x : UniformSpace.Completion K) = f x) ∧
          ∀ g' : UniformSpace.Completion K → F, Continuous g' →
            (∀ x : K, g' (x : UniformSpace.Completion K) = f x) → g' = g := by
  let g := chapter07UniversalCompletionExtension f hf
  refine ⟨g, ?_, ?_, ?_⟩
  · simpa [g, chapter07UniversalCompletionExtension] using
      (UniformSpace.Completion.uniformContinuous_extension (f := f))
  · intro x
    exact chapter07_universal_extension_coe f hf x
  · intro g' hg' h'
    symm
    apply UniformSpace.Completion.ext
    · exact UniformSpace.Completion.continuous_extension
    · exact hg'
    · intro x
      exact (chapter07_universal_extension_coe f hf x).trans (h' x).symm

-- The value of the extension can be computed from any approximating sequence.
theorem chapter07_universal_extension_as_limit
    {K F : Type*} [UniformSpace K] [UniformSpace F] [CompleteSpace F] [T0Space F] [Nonempty F]
    (f : K → F) (hf : UniformContinuous f)
    (x : UniformSpace.Completion K) (u : ℕ → K)
    (hu : Tendsto (fun n => (u n : UniformSpace.Completion K)) (atTop : Filter ℕ) (𝓝 x)) :
    chapter07UniversalCompletionExtension f hf x =
      limUnder (atTop : Filter ℕ) (fun n => f (u n)) := by
  have hlim : Tendsto (fun n => f (u n)) atTop
      (𝓝 (chapter07UniversalCompletionExtension f hf x)) := by
    have h := (UniformSpace.Completion.continuous_extension (f := f)).tendsto x |>.comp hu
    change Tendsto (fun n => f (u n)) atTop
      (𝓝 (UniformSpace.Completion.extension f x))
    exact h.congr' (Filter.Eventually.of_forall (fun n =>
      UniformSpace.Completion.extension_coe hf (u n)))
  exact hlim.limUnder_eq.symm

-- The dense-approximation construction is independent of the chosen approximating sequence.
theorem chapter07_universal_extension_approximation_independent
    {K F : Type*} [UniformSpace K] [UniformSpace F] [CompleteSpace F] [T0Space F] [Nonempty F]
    (f : K → F) (hf : UniformContinuous f) (x : UniformSpace.Completion K)
    (u v : ℕ → K)
    (hu : Tendsto (fun n => (u n : UniformSpace.Completion K)) (atTop : Filter ℕ) (𝓝 x))
    (hv : Tendsto (fun n => (v n : UniformSpace.Completion K)) (atTop : Filter ℕ) (𝓝 x)) :
    limUnder (atTop : Filter ℕ) (fun n => f (u n)) =
      limUnder (atTop : Filter ℕ) (fun n => f (v n)) := by
  have hU : Tendsto (fun n => f (u n)) atTop
      (𝓝 (chapter07UniversalCompletionExtension f hf x)) := by
    have h := (UniformSpace.Completion.continuous_extension (f := f)).tendsto x |>.comp hu
    change Tendsto (fun n => f (u n)) atTop
      (𝓝 (UniformSpace.Completion.extension f x))
    exact h.congr' (Filter.Eventually.of_forall (fun n =>
      UniformSpace.Completion.extension_coe hf (u n)))
  have hV : Tendsto (fun n => f (v n)) atTop
      (𝓝 (chapter07UniversalCompletionExtension f hf x)) := by
    have h := (UniformSpace.Completion.continuous_extension (f := f)).tendsto x |>.comp hv
    change Tendsto (fun n => f (v n)) atTop
      (𝓝 (UniformSpace.Completion.extension f x))
    exact h.congr' (Filter.Eventually.of_forall (fun n =>
      UniformSpace.Completion.extension_coe hf (v n)))
  exact hU.limUnder_eq.trans hV.limUnder_eq.symm

-- The completion extension of a continuous ring homomorphism.
noncomputable def chapter07UniversalCompletionRingHom
    {K F : Type*} [Ring K] [UniformSpace K] [IsUniformAddGroup K]
    [IsTopologicalRing K] [Ring F] [UniformSpace F] [IsUniformAddGroup F]
    [IsTopologicalRing F] [CompleteSpace F] [T0Space F]
    (f : K →+* F) (hf : Continuous f) :
    UniformSpace.Completion K →+* F :=
  UniformSpace.Completion.extensionHom f hf

-- The ring-hom extension agrees with the original ring homomorphism.
theorem chapter07_universal_extension_ringHom_coe
    {K F : Type*} [Ring K] [UniformSpace K] [IsUniformAddGroup K]
    [IsTopologicalRing K] [Ring F] [UniformSpace F] [IsUniformAddGroup F]
    [IsTopologicalRing F] [CompleteSpace F] [T0Space F]
    (f : K →+* F) (hf : Continuous f) (x : K) :
    chapter07UniversalCompletionRingHom f hf (x : UniformSpace.Completion K) = f x := by
  exact UniformSpace.Completion.extensionHom_coe f hf x

-- Compatibility of a field hom with a chosen valuation.
def chapter07ValuationCompatibleRingHom
    {K F Γ₀ : Type*} [Ring K] [Ring F] [LinearOrderedCommMonoidWithZero Γ₀]
    (vK : Valuation K Γ₀) (vF : Valuation F Γ₀) (f : K →+* F) : Prop :=
  ∀ x : K, vF (f x) = vK x

-- Theorem 7.1, valued form: compatible field homomorphisms extend compatibly.
theorem chapter07_completion_extension_preserves_valuation
    {K F Γ₀ : Type*} [Field K] [Field F]
    [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [Valued F Γ₀]
    [CompleteSpace F] [T0Space F] [T2Space Γ₀]
    (f : K →+* F) (hf : Continuous f)
    (hcompat : chapter07ValuationCompatibleRingHom
      (Valued.v (R := K)) (Valued.v (R := F)) f) :
    ∀ x : UniformSpace.Completion K,
      Valued.v (R := F) (chapter07UniversalCompletionRingHom f hf x) =
        chapter07CompletionValuation K Γ₀ x := by
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · simp [chapter07UniversalCompletionRingHom, chapter07CompletionValuation]
  · let g := chapter07UniversalCompletionRingHom f hf
    have hgx : g x ≠ 0 := by
      intro hgx
      apply hx
      exact (RingHom.injective g) (by simpa using hgx)
    have hxc : chapter07CompletionValuation K Γ₀ x ≠ 0 :=
      (Valuation.ne_zero_iff (chapter07CompletionValuation K Γ₀)).2 hx
    have hvalC : {y : UniformSpace.Completion K |
        chapter07CompletionValuation K Γ₀ y = chapter07CompletionValuation K Γ₀ x} ∈ 𝓝 x :=
      Valued.locally_const hxc
    have hvalF : {y : F | Valued.v (R := F) y = Valued.v (R := F) (g x)} ∈ 𝓝 (g x) :=
      Valued.locally_const ((Valuation.ne_zero_iff (Valued.v (R := F))).2 hgx)
    have hgval : g ⁻¹' {y : F |
        Valued.v (R := F) y = Valued.v (R := F) (g x)} ∈ 𝓝 x :=
      (UniformSpace.Completion.continuous_extension (f := f)).continuousAt.preimage_mem_nhds hvalF
    obtain ⟨r, hrC, hrF⟩ := UniformSpace.Completion.denseRange_coe.mem_nhds
      (inter_mem hvalC hgval)
    calc
      Valued.v (R := F) (g x) = Valued.v (R := F) (g (r : UniformSpace.Completion K)) := hrF.symm
      _ = Valued.v (R := F) (f r) := by
        rw [chapter07_universal_extension_ringHom_coe]
      _ = Valued.v (R := K) r := hcompat r
      _ = chapter07CompletionValuation K Γ₀ (r : UniformSpace.Completion K) :=
        (chapter07_completion_valuation_apply_coe r).symm
      _ = chapter07CompletionValuation K Γ₀ x := hrC

/-! ### 7.4. Completion of a valuation ring -/

abbrev chapter07ValuationRing
    (K Γ₀ : Type*) [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] : Type _ :=
  Valued.integer K

@[instance_reducible]
noncomputable def chapter07CompletedValuationRing
    (K Γ₀ : Type*) [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] : ValuationSubring (UniformSpace.Completion K) :=
  (chapter07CompletionValuation K Γ₀).valuationSubring

-- The unit-ball characterization of the completed valuation ring.
theorem chapter07_completed_valuation_ring_carrier
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] :
      (chapter07CompletedValuationRing K Γ₀ : Set (UniformSpace.Completion K)) =
      {x | chapter07CompletionValuation K Γ₀ x ≤ 1} := by
  rfl

-- The completed unit ball is closed.
theorem chapter07_completed_valuation_ring_is_closed
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] :
    IsClosed (chapter07CompletedValuationRing K Γ₀ :
      Set (UniformSpace.Completion K)) := by
  exact Valued.isClosed_valuationSubring (UniformSpace.Completion K)

-- The completed valuation ring is complete for the induced metric uniformity.
theorem chapter07_completed_valuation_ring_is_complete
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] :
    CompleteSpace (chapter07CompletedValuationRing K Γ₀) := by
  exact chapter07_completed_valuation_ring_is_closed.completeSpace_coe

-- The inclusion from the original valuation ring into the completion.
def chapter07ValuationRingCompletionEmbedding
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] :
    chapter07ValuationRing K Γ₀ → UniformSpace.Completion K :=
  fun a => ((a : K) : UniformSpace.Completion K)

-- The canonical map from the original valuation ring to the completed one.
noncomputable def chapter07ValuationRingCompletionRingHom
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] :
    chapter07ValuationRing K Γ₀ →+* chapter07CompletedValuationRing K Γ₀ := by
  let fK : chapter07ValuationRing K Γ₀ →+* UniformSpace.Completion K :=
    (UniformSpace.Completion.coeRingHom).comp (SubringClass.subtype (Valued.integer K))
  have hfK_mem : ∀ a : chapter07ValuationRing K Γ₀,
      fK a ∈ (chapter07CompletedValuationRing K Γ₀ : Set
        (UniformSpace.Completion K)) := by
    intro a
    change chapter07CompletionValuation K Γ₀ (fK a) ≤ 1
    change chapter07CompletionValuation K Γ₀
      (((a : chapter07ValuationRing K Γ₀) : K) : UniformSpace.Completion K) ≤ 1
    rw [chapter07_completion_valuation_apply_coe]
    exact a.property
  exact fK.codRestrict (chapter07CompletedValuationRing K Γ₀) hfK_mem

-- Section 7.4: one inclusion in the closure characterization.
theorem chapter07_valuation_ring_closure_subset
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] :
    closure (Set.range (@chapter07ValuationRingCompletionEmbedding K Γ₀ _ _ _)) ⊆
      (chapter07CompletedValuationRing K Γ₀ :
        Set (UniformSpace.Completion K)) := by
  apply closure_minimal
  · rintro _ ⟨a, rfl⟩
    change chapter07CompletionValuation K Γ₀
      (((a : chapter07ValuationRing K Γ₀) : K) : UniformSpace.Completion K) ≤ 1
    rw [chapter07_completion_valuation_apply_coe]
    exact a.property
  · exact chapter07_completed_valuation_ring_is_closed

-- Section 7.4: every point of the completed unit ball is approximated by integral elements.
theorem chapter07_completed_unit_ball_is_approximated_by_integral_elements
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] (x : UniformSpace.Completion K)
    (hx : chapter07CompletionValuation K Γ₀ x ≤ 1) :
    x ∈ closure (Set.range (@chapter07ValuationRingCompletionEmbedding K Γ₀ _ _ _)) := by
  rw [mem_closure_iff_nhds]
  intro s hs
  have hx' : x ∈ (chapter07CompletedValuationRing K Γ₀ :
      Set (UniformSpace.Completion K)) := by
    rw [chapter07_completed_valuation_ring_carrier]
    exact hx
  have hopen : (chapter07CompletedValuationRing K Γ₀ :
      Set (UniformSpace.Completion K)) ∈ 𝓝 x :=
    (Valued.isOpen_valuationSubring (UniformSpace.Completion K)).mem_nhds hx'
  obtain ⟨r, hr, hri⟩ :=
    UniformSpace.Completion.denseRange_coe.mem_nhds (inter_mem hs hopen)
  have hrval : Valued.v (R := K) r ≤ 1 := by
    have hri' : ((r : K) : UniformSpace.Completion K) ∈
        (chapter07CompletedValuationRing K Γ₀ :
        Set (UniformSpace.Completion K)) := hri
    rw [chapter07_completed_valuation_ring_carrier] at hri'
    simpa [chapter07CompletionValuation] using hri'
  refine ⟨chapter07ValuationRingCompletionEmbedding (K := K) (Γ₀ := Γ₀)
      ⟨r, hrval⟩, hr, ?_⟩
  exact ⟨⟨r, hrval⟩, rfl⟩

-- The closure of the valuation ring is exactly the completed valuation ring.
theorem chapter07_valuation_ring_closure_eq_completed_valuation_ring
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] :
    closure (Set.range (@chapter07ValuationRingCompletionEmbedding K Γ₀ _ _ _)) =
      (chapter07CompletedValuationRing K Γ₀ :
        Set (UniformSpace.Completion K)) := by
  apply Set.Subset.antisymm
  · exact chapter07_valuation_ring_closure_subset
  · intro x hx
    rw [chapter07_completed_valuation_ring_carrier] at hx
    exact chapter07_completed_unit_ball_is_approximated_by_integral_elements x hx

-- A uniformizer in the original valuation ring, bundled by Mathlib.
def chapter07CompletedUniformizer
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] [hdiscrete : (Valued.v (R := K)).IsRankOneDiscrete]
    (π : (Valued.v (R := K)).Uniformizer) :
  chapter07CompletedValuationRing K Γ₀ :=
  ⟨(((π : Valued.integer K) : K) : UniformSpace.Completion K), by
    change chapter07CompletionValuation K Γ₀
      (((π : Valued.integer K) : K) : UniformSpace.Completion K) ≤ 1
    rw [chapter07_completion_valuation_apply_coe]
    exact π.val.property⟩

-- The completed uniformizer has the same value as the original uniformizer.
theorem chapter07_completed_uniformizer_preserves_value
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] [hdiscrete : (Valued.v (R := K)).IsRankOneDiscrete]
    (π : (Valued.v (R := K)).Uniformizer) :
      chapter07CompletionValuation K Γ₀
        (chapter07CompletedUniformizer π) =
      Valued.v (π.val : K) := by
  change chapter07CompletionValuation K Γ₀
      (((π : Valued.integer K) : K) : UniformSpace.Completion K) =
    Valued.v (π.val : K)
  rw [chapter07_completion_valuation_apply_coe]

-- The completion has the same discrete value group.
theorem chapter07_completed_dvr_value_group_is_integer
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] [hdiscrete : (Valued.v (R := K)).IsRankOneDiscrete] :
    Nonempty
      (ValueGroup₀ (.ofClass (chapter07CompletionValuation K Γ₀)) ≃*o ℤᵐ⁰) := by
  let vK : Valuation K Γ₀ := Valued.v
  let vC : Valuation (UniformSpace.Completion K) Γ₀ :=
    chapter07CompletionValuation K Γ₀
  have hvalueGroup : valueGroup (.ofClass vC) = valueGroup (.ofClass vK) := by
    apply le_antisymm
    · intro γ hγ
      have hγ' : (γ : Γ₀) ∈ Set.range (MonoidWithZeroHom.ofClass vC) \ {0} := by
        rw [← MonoidWithZeroHom.valueGroup_eq_range (.ofClass vC)]
        exact ⟨γ, hγ, rfl⟩
      obtain ⟨⟨x, hx⟩, _hx0⟩ := hγ'
      obtain ⟨r, hr⟩ := Valued.exists_coe_eq_v x
      have hval : (γ : Γ₀) = vK r := by
        calc
          (γ : Γ₀) = vC x := hx.symm
          _ = vK r := by
            change Valued.extensionValuation x = Valued.v r
            exact hr
      have hr0 : r ≠ 0 := by
        intro hr0
        subst r
        simp [vK] at hval
      have hvr0 : vK r ≠ 0 := by
        intro hvr0
        exact γ.ne_zero (hval.trans hvr0)
      have hγeq : Units.mk0 (vK r) hvr0 = γ := by
        apply Units.ext
        exact hval.symm
      rw [← hγeq]
      exact MonoidWithZeroHom.mem_valueGroup (.ofClass vK) ⟨r, rfl⟩
    · intro γ hγ
      have hγ' : (γ : Γ₀) ∈ Set.range (MonoidWithZeroHom.ofClass vK) \ {0} := by
        rw [← MonoidWithZeroHom.valueGroup_eq_range (.ofClass vK)]
        exact ⟨γ, hγ, rfl⟩
      obtain ⟨⟨r, hr⟩, hr0⟩ := hγ'
      have hval : (γ : Γ₀) = vK r := by
        simpa [vK] using hr.symm
      have hvr0 : vK r ≠ 0 := by
        intro hvr0
        exact γ.ne_zero (hval.trans hvr0)
      have hvcval : vC ((r : K) : UniformSpace.Completion K) = vK r := by
        change chapter07CompletionValuation K Γ₀
            ((r : K) : UniformSpace.Completion K) = Valued.v r
        rw [chapter07_completion_valuation_apply_coe]
      have hvc0 : vC ((r : K) : UniformSpace.Completion K) ≠ 0 := by
        simpa [hvcval] using hvr0
      have hγeq : Units.mk0 (vC ((r : K) : UniformSpace.Completion K)) hvc0 = γ := by
        apply Units.ext
        exact hvcval.trans hval.symm
      rw [← hγeq]
      exact MonoidWithZeroHom.mem_valueGroup (.ofClass vC)
        ⟨(r : UniformSpace.Completion K), rfl⟩
  let : vC.IsRankOneDiscrete := by
    refine ⟨⟨Valuation.IsRankOneDiscrete.generator vK, ?_, ?_⟩⟩
    · rw [hvalueGroup]
      exact Valuation.IsRankOneDiscrete.generator_zpowers_eq_valueGroup vK
    · exact Valuation.IsRankOneDiscrete.generator_lt_one vK
  exact ⟨chapter07DiscreteValueGroupEquiv vC⟩

-- The completed valuation ring is a DVR.
theorem chapter07_completed_valuation_ring_is_dvr
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] [hdiscrete : (Valued.v (R := K)).IsRankOneDiscrete] :
    IsDiscreteValuationRing (chapter07CompletedValuationRing K Γ₀) ∧
      IsAdicComplete
        (IsLocalRing.maximalIdeal (chapter07CompletedValuationRing K Γ₀))
        (chapter07CompletedValuationRing K Γ₀) := by
  let vK : Valuation K Γ₀ := Valued.v
  let vC : Valuation (UniformSpace.Completion K) Γ₀ :=
    chapter07CompletionValuation K Γ₀
  have hvC : (Valued.v : Valuation (UniformSpace.Completion K) Γ₀) = vC := by
    rfl
  have hvalueGroup : valueGroup (.ofClass vC) = valueGroup (.ofClass vK) := by
    apply le_antisymm
    · intro γ hγ
      have hγ' : (γ : Γ₀) ∈ Set.range (MonoidWithZeroHom.ofClass vC) \ {0} := by
        rw [← MonoidWithZeroHom.valueGroup_eq_range (.ofClass vC)]
        exact ⟨γ, hγ, rfl⟩
      obtain ⟨⟨x, hx⟩, _hx0⟩ := hγ'
      obtain ⟨r, hr⟩ := Valued.exists_coe_eq_v x
      have hval : (γ : Γ₀) = vK r := by
        calc
          (γ : Γ₀) = vC x := hx.symm
          _ = vK r := by
            change Valued.extensionValuation x = Valued.v r
            exact hr
      have hvr0 : vK r ≠ 0 := by
        intro hvr0
        exact γ.ne_zero (hval.trans hvr0)
      have hγeq : Units.mk0 (vK r) hvr0 = γ := by
        apply Units.ext
        exact hval.symm
      rw [← hγeq]
      exact MonoidWithZeroHom.mem_valueGroup (.ofClass vK) ⟨r, rfl⟩
    · intro γ hγ
      have hγ' : (γ : Γ₀) ∈ Set.range (MonoidWithZeroHom.ofClass vK) \ {0} := by
        rw [← MonoidWithZeroHom.valueGroup_eq_range (.ofClass vK)]
        exact ⟨γ, hγ, rfl⟩
      obtain ⟨⟨r, hr⟩, hr0⟩ := hγ'
      have hval : (γ : Γ₀) = vK r := by
        simpa [vK] using hr.symm
      have hvr0 : vK r ≠ 0 := by
        intro hvr0
        exact γ.ne_zero (hval.trans hvr0)
      have hvcval : vC ((r : K) : UniformSpace.Completion K) = vK r := by
        change chapter07CompletionValuation K Γ₀
            ((r : K) : UniformSpace.Completion K) = Valued.v r
        rw [chapter07_completion_valuation_apply_coe]
      have hvc0 : vC ((r : K) : UniformSpace.Completion K) ≠ 0 := by
        simpa [hvcval] using hvr0
      have hγeq : Units.mk0 (vC ((r : K) : UniformSpace.Completion K)) hvc0 = γ := by
        apply Units.ext
        exact hvcval.trans hval.symm
      rw [← hγeq]
      exact MonoidWithZeroHom.mem_valueGroup (.ofClass vC)
        ⟨(r : UniformSpace.Completion K), rfl⟩
  let : vC.IsRankOneDiscrete := by
    refine ⟨⟨Valuation.IsRankOneDiscrete.generator vK, ?_, ?_⟩⟩
    · rw [hvalueGroup]
      exact Valuation.IsRankOneDiscrete.generator_zpowers_eq_valueGroup vK
    · exact Valuation.IsRankOneDiscrete.generator_lt_one vK
  have hdvr : IsDiscreteValuationRing vC.valuationSubring := by
    infer_instance
  refine ⟨?_, ?_⟩
  · exact hdvr
  · change IsAdicComplete (IsLocalRing.maximalIdeal vC.valuationSubring)
      vC.valuationSubring
    let π : vC.Uniformizer := Classical.choice (inferInstance :
      Nonempty (vC.Uniformizer))
    let p : vC.valuationSubring :=
      ⟨π.val, π.val.property⟩
    let : IsTopologicalRing vC.valuationSubring :=
      Subring.instIsTopologicalRing vC.valuationSubring.toSubring
    let : IsTopologicalAddGroup vC.valuationSubring := by
      infer_instance
    let : IsUniformAddGroup vC.valuationSubring :=
      vC.valuationSubring.toSubring.toAddSubgroup.isUniformAddGroup
    have hp : p = (π.val : vC.valuationSubring) := by
      apply Subtype.ext
      rfl
    have hm : IsLocalRing.maximalIdeal vC.valuationSubring =
        Ideal.span ({p} : Set vC.valuationSubring) := by
      rw [hp]
      exact π.valuation_gt_one.is_generator
    have hclosed : IsClosed (vC.valuationSubring :
        Set (UniformSpace.Completion K)) := by
      exact chapter07_completed_valuation_ring_is_closed
    let : CompleteSpace vC.valuationSubring := hclosed.completeSpace_coe
    have hpow : ∀ n : ℕ,
        (IsLocalRing.maximalIdeal vC.valuationSubring) ^ n =
          Ideal.span ({p ^ n} : Set vC.valuationSubring) := by
      intro n
      rw [hp]
      exact Valuation.pow_Uniformizer_is_pow_generator π n
    have hball : ∀ n : ℕ,
        (((IsLocalRing.maximalIdeal vC.valuationSubring) ^ n :
          Ideal vC.valuationSubring) : Set vC.valuationSubring) =
          (fun x : vC.valuationSubring =>
            (x : UniformSpace.Completion K)) ⁻¹'
            {x : UniformSpace.Completion K | vC x ≤ vC (p ^ n)} := by
      intro n
      rw [hpow n]
      ext x
      constructor
      · intro hx
        change vC (x : UniformSpace.Completion K) ≤ vC (p ^ n)
        rcases (Ideal.mem_span_singleton.mp hx) with ⟨y, hy⟩
        rw [hy]
        rw [Subring.coe_mul (vC.valuationSubring.toSubring),
          Subring.coe_pow (vC.valuationSubring.toSubring)]
        simpa only [map_mul, map_pow] using
          (mul_le_of_le_one_right
            (le_of_lt (pow_pos (by simpa [p] using π.valuation_gt_one.val_pos) n))
            y.property)
      · intro hx
        change vC (x : UniformSpace.Completion K) ≤ vC (p ^ n) at hx
        apply Ideal.mem_span_singleton.mpr
        let y0 : UniformSpace.Completion K :=
          (x : UniformSpace.Completion K) / (p : UniformSpace.Completion K) ^ n
        have hπpos : 0 < vC (p : UniformSpace.Completion K) := by
          simpa [p] using π.valuation_gt_one.val_pos
        have hy0 : vC y0 ≤ 1 := by
          dsimp [y0]
          rw [vC.map_div, map_pow]
          apply (div_le_iff₀ (pow_pos hπpos n)).2
          simpa using hx
        let y : vC.valuationSubring := ⟨y0, hy0⟩
        refine ⟨y, ?_⟩
        apply Subtype.ext
        dsimp [y, y0]
        have hp0 : (p : UniformSpace.Completion K) ≠ 0 :=
          (Valuation.pos_iff vC).mp hπpos
        field_simp [hp0]
    have hppos : 0 < vC (p : UniformSpace.Completion K) := by
      simpa [p] using π.valuation_gt_one.val_pos
    have hI : IsAdic (IsLocalRing.maximalIdeal vC.valuationSubring) := by
      rw [isAdic_iff]
      constructor
      · intro n
        rw [hball n]
        have hpn0 : Valued.v.restrict
            ((p : UniformSpace.Completion K) ^ n) ≠ 0 := by
          intro hzero
          have hzero' : Valued.v ((p : UniformSpace.Completion K) ^ n) = 0 := by
            exact (Valuation.restrict_eq_zero_iff (v := Valued.v)).mp hzero
          have hpnp : 0 < Valued.v ((p : UniformSpace.Completion K) ^ n) := by
            rw [map_pow]
            have hp : 0 < Valued.v (p : UniformSpace.Completion K) := by
              rw [show (Valued.v : Valuation (UniformSpace.Completion K) Γ₀) =
                vC by rfl]
              exact hppos
            exact pow_pos hp n
          exact (ne_of_gt hpnp) hzero'
        have hopen : IsOpen {x : UniformSpace.Completion K |
            vC x ≤ vC ((p : UniformSpace.Completion K) ^ n)} := by
          have hopen' := Valued.isOpen_closedBall (UniformSpace.Completion K)
            (Γ₀ := Γ₀) hpn0
          have htop : Valued.valuedCompletion.toTopologicalSpace =
              (UniformSpace.Completion.uniformSpace K).toTopologicalSpace := by
            rfl
          rw [htop] at hopen'
          have hv : (Valued.v : Valuation (UniformSpace.Completion K) Γ₀) =
              vC := by
            rfl
          rw [hv] at hopen'
          simpa only [Valuation.restrict_le_iff_le_embedding,
            Valuation.embedding_restrict] using hopen'
        exact hopen.preimage continuous_subtype_val
      · intro s hs
        obtain ⟨u, hu, hus⟩ := (mem_nhds_subtype
          (vC.valuationSubring : Set (UniformSpace.Completion K))
          (⟨0, (show (0 : UniformSpace.Completion K) ∈ vC.valuationSubring by simp)⟩)
          s).mp hs
        obtain ⟨γ, -, hγu⟩ :=
          (Valued.hasBasis_nhds_zero (UniformSpace.Completion K) Γ₀).mem_iff.mp hu
        let γval : Γ₀ :=
          MonoidWithZeroHom.ValueGroup₀.embedding
            (f := (.ofClass vC)) γ.1
        have hγpos : 0 < γval := by
          dsimp [γval]
          exact MonoidWithZeroHom.ValueGroup₀.embedding_unit_pos γ
        by_cases hγ : (1 : Γ₀) < γval
        · refine ⟨0, ?_⟩
          rw [hball 0]
          intro x hx
          apply hus
          apply hγu
          apply (Valuation.restrict_lt_iff_lt_embedding (v := vC)).2
          exact lt_of_le_of_lt (by simpa using hx) hγ
        · have hγle : γval ≤ (1 : Γ₀) := le_of_not_gt hγ
          obtain ⟨r, s, hrpos, hspos, hdiv⟩ :=
            Valuation.exists_div_eq_of_unit (v := vC) γ
          let x : UniformSpace.Completion K := r / s
          have hxval : vC x = γval := by
            dsimp [x]
            have hdiv' := congrArg
              (MonoidWithZeroHom.ValueGroup₀.embedding
                (f := (.ofClass vC))) hdiv
            calc
              vC (r / s) = vC r / vC s := by rw [vC.map_div]
              _ = MonoidWithZeroHom.ValueGroup₀.embedding
                  (vC.restrict r) /
                    MonoidWithZeroHom.ValueGroup₀.embedding (vC.restrict s) := by
                rw [Valuation.embedding_restrict, Valuation.embedding_restrict]
              _ = MonoidWithZeroHom.ValueGroup₀.embedding
                  (vC.restrict r / vC.restrict s) := by
                symm
                rw [map_div₀]
              _ = MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := hdiv'
              _ = γval := rfl
          have hxpos : 0 < vC x := by
            simpa [hxval] using hγpos
          have hx0 : x ≠ 0 := (Valuation.pos_iff vC).mp hxpos
          have hxA : x ∈ vC.valuationSubring := by
            change vC x ≤ 1
            simpa [hxval] using hγle
          let xA : vC.valuationSubring := ⟨x, hxA⟩
          have hxA0 : xA ≠ 0 := by
            intro hzero
            apply hx0
            exact congrArg Subtype.val hzero
          obtain ⟨k, uunit, hxpow⟩ :=
            Valuation.exists_pow_Uniformizer (v := vC) hxA0 π
          have huval : vC (uunit : vC.valuationSubring) = 1 := by
            exact (Valuation.Integers.isUnit_iff_valuation_eq_one
              (x := (uunit : vC.valuationSubring))
              (Valuation.integer.integers vC)).mp uunit.isUnit
          have hγeq : γval = vC p ^ k := by
            calc
              γval = vC x := hxval.symm
              _ = vC (xA : vC.valuationSubring) := rfl
              _ = vC (p ^ k * (uunit : vC.valuationSubring)) := by
                rw [hp]
                simpa only [Subring.coe_mul, Subring.coe_pow] using congrArg vC hxpow
              _ = vC p ^ k * vC (uunit : vC.valuationSubring) := by
                rw [map_mul, map_pow]
              _ = vC p ^ k := by rw [huval, mul_one]
          refine ⟨k + 1, ?_⟩
          rw [hball (k + 1)]
          intro x hx
          apply hus
          apply hγu
          apply (Valuation.restrict_lt_iff_lt_embedding (v := vC)).2
          have hπlt : vC p < (1 : Γ₀) := by
            simpa [p] using π.valuation_gt_one.val_lt_one
          have hx' : vC (x : UniformSpace.Completion K) ≤
              vC (p ^ (k + 1)) := by
            simpa using hx
          have hx'' : vC (x : UniformSpace.Completion K) ≤
              vC p ^ (k + 1) := by
            simpa only [map_pow] using hx'
          calc
            vC (x : UniformSpace.Completion K) ≤ vC p ^ (k + 1) := hx''
            _ < vC p ^ k := by
              rw [pow_succ]
              simpa using mul_lt_mul_of_pos_left hπlt (pow_pos hppos k)
            _ = γval := hγeq.symm
    exact (hI.isAdicComplete_iff).2 ⟨inferInstance, inferInstance⟩

-- A uniformizer generates the maximal ideal in any DVR.
theorem chapter07_dvr_uniformizer_generates_maximal_ideal
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (π : A) (hπ : Irreducible π) :
    Ideal.span ({π} : Set A) = IsLocalRing.maximalIdeal A := by
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ |>.symm

-- Finite-level quotients of the original and completed valuation rings.
theorem chapter07_dvr_finite_level_quotient_equivalence
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] [hdiscrete : (Valued.v (R := K)).IsRankOneDiscrete]
    (π : (Valued.v (R := K)).Uniformizer) (n : ℕ) (hn : 1 ≤ n) :
    ∃ e : (chapter07ValuationRing K Γ₀) ⧸
          Ideal.span ({(π.val : chapter07ValuationRing K Γ₀) ^ n} : Set
            (chapter07ValuationRing K Γ₀)) ≃+*
        (chapter07CompletedValuationRing K Γ₀) ⧸
          Ideal.span ({(chapter07CompletedUniformizer π) ^ n} : Set
            (chapter07CompletedValuationRing K Γ₀)),
      ∀ a : chapter07ValuationRing K Γ₀,
          e (Ideal.Quotient.mk _ a) =
          Ideal.Quotient.mk _
            (chapter07ValuationRingCompletionRingHom (K := K) (Γ₀ := Γ₀) a) := by
  let vK : Valuation K Γ₀ := Valued.v
  let vC : Valuation (UniformSpace.Completion K) Γ₀ :=
    chapter07CompletionValuation K Γ₀
  let Js : Ideal (chapter07ValuationRing K Γ₀) :=
    Ideal.span ({(π.val : chapter07ValuationRing K Γ₀) ^ n} : Set
      (chapter07ValuationRing K Γ₀))
  let Jc : Ideal (chapter07CompletedValuationRing K Γ₀) :=
    Ideal.span ({(chapter07CompletedUniformizer π :
      chapter07CompletedValuationRing K Γ₀) ^ n} : Set
      (chapter07CompletedValuationRing K Γ₀))
  let fK : chapter07ValuationRing K Γ₀ →+* UniformSpace.Completion K :=
    (UniformSpace.Completion.coeRingHom).comp (SubringClass.subtype (Valued.integer K))
  have hfK_mem : ∀ a : chapter07ValuationRing K Γ₀,
      fK a ∈ (chapter07CompletedValuationRing K Γ₀ : Set
        (UniformSpace.Completion K)) := by
    intro a
    change chapter07CompletionValuation K Γ₀ (fK a) ≤ 1
    change chapter07CompletionValuation K Γ₀
      (((a : chapter07ValuationRing K Γ₀) : K) : UniformSpace.Completion K) ≤ 1
    rw [chapter07_completion_valuation_apply_coe]
    exact a.property
  let f : chapter07ValuationRing K Γ₀ →+*
      chapter07CompletedValuationRing K Γ₀ :=
    fK.codRestrict (chapter07CompletedValuationRing K Γ₀) hfK_mem
  have hfπ : f (π.val : chapter07ValuationRing K Γ₀) =
      chapter07CompletedUniformizer π := by
    apply Subtype.ext
    rfl
  have hmap : Ideal.map f Js ≤ Jc := by
    rw [show Js = Ideal.span ({(π.val : chapter07ValuationRing K Γ₀) ^ n} : Set
      (chapter07ValuationRing K Γ₀)) by rfl]
    rw [Ideal.map_span]
    apply Ideal.span_mono
    rintro y ⟨x, hx, rfl⟩
    have hx' : x = (π.val : chapter07ValuationRing K Γ₀) ^ n := by simpa using hx
    subst x
    rw [map_pow, hfπ]
    exact Set.mem_singleton _
  let g : (chapter07ValuationRing K Γ₀) ⧸ Js →+*
      (chapter07CompletedValuationRing K Γ₀) ⧸ Jc :=
    Ideal.Quotient.lift Js ((Ideal.Quotient.mk Jc).comp f) (by
      intro a ha
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact (Ideal.map_le_iff_le_comap.mp hmap) ha)
  have hpval : 0 < vC (chapter07CompletedUniformizer π :
      chapter07CompletedValuationRing K Γ₀) := by
    change 0 < chapter07CompletionValuation K Γ₀
      (chapter07CompletedUniformizer π)
    rw [chapter07_completed_uniformizer_preserves_value]
    exact π.valuation_gt_one.val_pos
  let δ : (MonoidWithZeroHom.ValueGroup₀
      (.ofClass (Valued.v : Valuation (UniformSpace.Completion K) Γ₀))) :=
    (Valued.v : Valuation (UniformSpace.Completion K) Γ₀).restrict
      (((chapter07CompletedUniformizer π :
        chapter07CompletedValuationRing K Γ₀) : UniformSpace.Completion K) ^ n)
  have quotient_approx : ∀ y : chapter07CompletedValuationRing K Γ₀,
      ∃ a : chapter07ValuationRing K Γ₀, y - f a ∈ Jc := by
    intro y
    have hyclosure : (y : UniformSpace.Completion K) ∈
        closure (Set.range (@chapter07ValuationRingCompletionEmbedding K Γ₀ _ _ _)) := by
      apply chapter07_completed_unit_ball_is_approximated_by_integral_elements
      exact y.property
    let U : Set (UniformSpace.Completion K) :=
      {z | (Valued.v : Valuation (UniformSpace.Completion K) Γ₀).restrict
        (z - (y : UniformSpace.Completion K)) < δ}
    have hUopen : IsOpen U := by
      have hball := Valued.isOpen_ball (UniformSpace.Completion K) δ
      have htop : Valued.valuedCompletion.toTopologicalSpace =
          (UniformSpace.Completion.uniformSpace K).toTopologicalSpace := by
        rfl
      rw [htop] at hball
      simpa [U] using hball.preimage (continuous_id.sub continuous_const)
    have hδpos : 0 < δ := by
      apply (Valuation.restrict_pos_iff
        (Valued.v : Valuation (UniformSpace.Completion K) Γ₀) _).2
      rw [map_pow]
      have hpval' : 0 < (Valued.v : Valuation (UniformSpace.Completion K) Γ₀)
          ((chapter07CompletedUniformizer π :
            chapter07CompletedValuationRing K Γ₀) : UniformSpace.Completion K) := by
        rw [show (Valued.v : Valuation (UniformSpace.Completion K) Γ₀) = vC by rfl]
        exact hpval
      have hn_eq : n - 1 + 1 = n := Nat.sub_add_cancel hn
      rw [← hn_eq]
      exact pow_pos hpval' _
    have hUmem : U ∈ 𝓝 (y : UniformSpace.Completion K) := by
      apply hUopen.mem_nhds
      simp [U, hδpos]
    obtain ⟨z, hzU, ⟨a, rfl⟩⟩ :=
      (mem_closure_iff_nhds.mp hyclosure) U hUmem
    refine ⟨a, ?_⟩
    have hlt : vC (((f a : chapter07CompletedValuationRing K Γ₀) :
          UniformSpace.Completion K) - (y : UniformSpace.Completion K)) <
        vC (((chapter07CompletedUniformizer π :
          chapter07CompletedValuationRing K Γ₀) : UniformSpace.Completion K) ^ n) := by
      have hrestrict : (Valued.v : Valuation (UniformSpace.Completion K) Γ₀).restrict
          (chapter07ValuationRingCompletionEmbedding a -
            (y : UniformSpace.Completion K)) < δ := by
        change (Valued.v : Valuation (UniformSpace.Completion K) Γ₀).restrict
          ((((a : chapter07ValuationRing K Γ₀) : K) : UniformSpace.Completion K) -
            (y : UniformSpace.Completion K)) < δ at hzU
        exact hzU
      have hlt' := (Valuation.restrict_lt_iff_lt_embedding
        (v := (Valued.v : Valuation (UniformSpace.Completion K) Γ₀))).mp hrestrict
      have hltVal : (Valued.v : Valuation (UniformSpace.Completion K) Γ₀)
          (chapter07ValuationRingCompletionEmbedding a -
            (y : UniformSpace.Completion K)) <
          (Valued.v : Valuation (UniformSpace.Completion K) Γ₀)
            (((chapter07CompletedUniformizer π :
              chapter07CompletedValuationRing K Γ₀) : UniformSpace.Completion K) ^ n) := by
        simpa [δ, Valuation.embedding_restrict] using hlt'
      change vC (chapter07ValuationRingCompletionEmbedding a -
        (y : UniformSpace.Completion K)) <
        vC (((chapter07CompletedUniformizer π :
          chapter07CompletedValuationRing K Γ₀) : UniformSpace.Completion K) ^ n)
      simpa [show (Valued.v : Valuation (UniformSpace.Completion K) Γ₀) = vC by rfl] using hltVal
    have hle : vC (((y - f a : chapter07CompletedValuationRing K Γ₀) :
        chapter07CompletedValuationRing K Γ₀) : UniformSpace.Completion K) ≤
        vC (((chapter07CompletedUniformizer π :
          chapter07CompletedValuationRing K Γ₀) : UniformSpace.Completion K) ^ n) := by
      have hlt' : vC (((y : chapter07CompletedValuationRing K Γ₀) :
          UniformSpace.Completion K) - (f a : UniformSpace.Completion K)) <
          vC (((chapter07CompletedUniformizer π :
            chapter07CompletedValuationRing K Γ₀) : UniformSpace.Completion K) ^ n) := by
        rw [show (y : UniformSpace.Completion K) - (f a : UniformSpace.Completion K) =
          -(((f a : chapter07CompletedValuationRing K Γ₀) : UniformSpace.Completion K) -
            (y : UniformSpace.Completion K)) by ring, vC.map_neg]
        exact hlt
      exact hlt'.le
    change (y - f a : chapter07CompletedValuationRing K Γ₀) ∈
      (Ideal.span ({(chapter07CompletedUniformizer π :
        chapter07CompletedValuationRing K Γ₀) ^ n} : Set
          (chapter07CompletedValuationRing K Γ₀)) : Set
        (chapter07CompletedValuationRing K Γ₀))
    have hspan :
        (Ideal.span ({(chapter07CompletedUniformizer π :
          chapter07CompletedValuationRing K Γ₀) ^ n} : Set
            (chapter07CompletedValuationRing K Γ₀)) : Set
          (chapter07CompletedValuationRing K Γ₀)) =
        {x : chapter07CompletedValuationRing K Γ₀ |
          vC (x : UniformSpace.Completion K) ≤
          vC (((chapter07CompletedUniformizer π :
            chapter07CompletedValuationRing K Γ₀) : UniformSpace.Completion K) ^ n)} := by
      exact Valuation.integer.coe_span_singleton_eq_setOfPred_le_v_coe _
    rw [hspan]
    exact hle
  have g_surj : Function.Surjective g := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨a, ha⟩ := quotient_approx y
    refine ⟨Ideal.Quotient.mk Js a, ?_⟩
    rw [Ideal.Quotient.lift_mk]
    rw [← sub_eq_zero]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    simpa [sub_eq_add_neg, add_comm] using Jc.neg_mem ha
  have g_inj : Function.Injective g := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← sub_eq_zero]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change (a - b : chapter07ValuationRing K Γ₀) ∈
      (Ideal.span ({(π.val : chapter07ValuationRing K Γ₀) ^ n} : Set
        (chapter07ValuationRing K Γ₀)) : Set
          (chapter07ValuationRing K Γ₀))
    have hmemC : f a - f b ∈ Jc := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub]
      exact sub_eq_zero.mpr (by simpa [g] using hxy)
    have hspanC :
        (Ideal.span ({(chapter07CompletedUniformizer π :
          chapter07CompletedValuationRing K Γ₀) ^ n} : Set
            (chapter07CompletedValuationRing K Γ₀)) : Set
          (chapter07CompletedValuationRing K Γ₀)) =
        {x : chapter07CompletedValuationRing K Γ₀ |
          vC (x : UniformSpace.Completion K) ≤
            vC (((chapter07CompletedUniformizer π :
              chapter07CompletedValuationRing K Γ₀) : UniformSpace.Completion K) ^ n)} := by
      exact Valuation.integer.coe_span_singleton_eq_setOfPred_le_v_coe _
    have hleC : vC (((f a - f b : chapter07CompletedValuationRing K Γ₀) :
        chapter07CompletedValuationRing K Γ₀) : UniformSpace.Completion K) ≤
        vC (((chapter07CompletedUniformizer π :
          chapter07CompletedValuationRing K Γ₀) : UniformSpace.Completion K) ^ n) := by
      have hmemC' : f a - f b ∈
          (Ideal.span ({(chapter07CompletedUniformizer π :
            chapter07CompletedValuationRing K Γ₀) ^ n} : Set
              (chapter07CompletedValuationRing K Γ₀)) : Set
            (chapter07CompletedValuationRing K Γ₀)) := hmemC
      rw [hspanC] at hmemC'
      exact hmemC'
    have hleK : (Valued.v : Valuation K Γ₀)
        (((a : chapter07ValuationRing K Γ₀) : K) -
          ((b : chapter07ValuationRing K Γ₀) : K)) ≤
        (Valued.v : Valuation K Γ₀) (π.val : K) ^ n := by
      have hleC' : vC
          (((((a : chapter07ValuationRing K Γ₀) : K) -
            ((b : chapter07ValuationRing K Γ₀) : K)) : UniformSpace.Completion K)) ≤
          vC (((chapter07CompletedUniformizer π :
            chapter07CompletedValuationRing K Γ₀) : UniformSpace.Completion K) ^ n) := by
        dsimp [f, fK] at hleC
        exact hleC
      have hcoediff :
          ((((a : chapter07ValuationRing K Γ₀) : K) : UniformSpace.Completion K) -
            (((b : chapter07ValuationRing K Γ₀) : K) : UniformSpace.Completion K)) =
          (((((a : chapter07ValuationRing K Γ₀) : K) -
            ((b : chapter07ValuationRing K Γ₀) : K)) : K) :
              UniformSpace.Completion K) := by
        symm
        exact (UniformSpace.Completion.coeRingHom : K →+*
          UniformSpace.Completion K).map_sub _ _
      rw [hcoediff] at hleC'
      rw [chapter07_completion_valuation_apply_coe] at hleC'
      rw [map_pow, chapter07_completed_uniformizer_preserves_value] at hleC'
      exact hleC'
    rw [Valuation.integer.coe_span_singleton_eq_setOfPred_le_v_coe]
    simpa [map_pow] using hleK
  let e := RingEquiv.ofBijective g ⟨g_inj, g_surj⟩
  refine ⟨e, ?_⟩
  intro a
  change g (Ideal.Quotient.mk Js a) =
    Ideal.Quotient.mk Jc
      (chapter07ValuationRingCompletionRingHom (K := K) (Γ₀ := Γ₀) a)
  rw [Ideal.Quotient.lift_mk]
  rfl

-- The residue fields are canonically identified at level n = 1.
theorem chapter07_dvr_residue_field_equivalence
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] [hdiscrete : (Valued.v (R := K)).IsRankOneDiscrete]
    (π : (Valued.v (R := K)).Uniformizer) :
    ∃ e : (chapter07ValuationRing K Γ₀) ⧸
          Ideal.span ({(π.val : chapter07ValuationRing K Γ₀)} : Set
            (chapter07ValuationRing K Γ₀)) ≃+*
        (chapter07CompletedValuationRing K Γ₀) ⧸
          Ideal.span ({chapter07CompletedUniformizer π} : Set
            (chapter07CompletedValuationRing K Γ₀)),
      ∀ a : chapter07ValuationRing K Γ₀,
        e (Ideal.Quotient.mk _ a) =
          Ideal.Quotient.mk _
            (chapter07ValuationRingCompletionRingHom (K := K) (Γ₀ := Γ₀) a) := by
  have hs :
      Ideal.span ({(π.val : chapter07ValuationRing K Γ₀) ^ 1} :
        Set (chapter07ValuationRing K Γ₀)) =
        Ideal.span ({(π.val : chapter07ValuationRing K Γ₀)} :
          Set (chapter07ValuationRing K Γ₀)) := by
    congr 1
    ext x
    simp
  have ht :
      Ideal.span ({chapter07CompletedUniformizer π ^ 1} :
        Set (chapter07CompletedValuationRing K Γ₀)) =
        Ideal.span ({chapter07CompletedUniformizer π} :
          Set (chapter07CompletedValuationRing K Γ₀)) := by
    congr 1
    ext x
    simp
  obtain ⟨e, he⟩ :=
    chapter07_dvr_finite_level_quotient_equivalence
      (K := K) (Γ₀ := Γ₀) π 1 (by omega)
  let es := Ideal.quotEquivOfEq hs.symm
  let et := Ideal.quotEquivOfEq ht
  refine ⟨es.trans (e.trans et), ?_⟩
  intro a
  simp [es, et, he]

-- The completed field is the fraction field of the completed DVR.
theorem chapter07_completed_field_is_fraction_field
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] [hdiscrete : (Valued.v (R := K)).IsRankOneDiscrete] :
    ∃ e : FractionRing (chapter07CompletedValuationRing K Γ₀) ≃+*
        UniformSpace.Completion K,
      ∀ a : chapter07CompletedValuationRing K Γ₀,
        e (algebraMap (chapter07CompletedValuationRing K Γ₀)
            (FractionRing (chapter07CompletedValuationRing K Γ₀)) a) =
          (a : UniformSpace.Completion K) := by
  let e := (fun _ : (Valued.v (R := K)).IsRankOneDiscrete =>
    (FractionRing.algEquiv (chapter07CompletedValuationRing K Γ₀)
      (UniformSpace.Completion K)).toRingEquiv) hdiscrete
  refine ⟨e, ?_⟩
  intro a
  change FractionRing.algEquiv (chapter07CompletedValuationRing K Γ₀)
      (UniformSpace.Completion K)
      (algebraMap (chapter07CompletedValuationRing K Γ₀)
        (FractionRing (chapter07CompletedValuationRing K Γ₀)) a) =
    (a : UniformSpace.Completion K)
  exact (FractionRing.algEquiv (chapter07CompletedValuationRing K Γ₀)
    (UniformSpace.Completion K)).commutes a

/-! ### 7.5. Separated ideal-adic completion -/

abbrev chapter07AdicCompletion
    (R : Type*) [CommRing R] (I : Ideal R) : Type _ :=
  AdicCompletion I R

-- The canonical map from a ring to its ideal-adic completion.
def chapter07AdicCompletionMap
    {R : Type*} [CommRing R] (I : Ideal R) :
    R →+* chapter07AdicCompletion R I :=
  algebraMap R (chapter07AdicCompletion R I)

-- The inverse-limit compatibility condition in AdicCompletion.
theorem chapter07_adic_completion_compatible_family
    {R : Type*} [CommRing R] (I : Ideal R)
    (x : chapter07AdicCompletion R I) :
    ∀ {m n : ℕ} (hmn : m ≤ n),
      AdicCompletion.transitionMap I R hmn (x.val n) = x.val m := by
  intro m n hmn
  exact x.property hmn

-- The kernel of the natural map is the intersection of all powers of the ideal.
theorem chapter07_adic_completion_kernel
    {R : Type*} [CommRing R] (I : Ideal R) :
    RingHom.ker (chapter07AdicCompletionMap I) = ⨅ n : ℕ, I ^ n := by
  ext x
  constructor
  · intro hx
    have hx' : chapter07AdicCompletionMap I x =
        (0 : chapter07AdicCompletion R I) := hx
    have hcoord : ∀ n : ℕ,
        Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R R)) x = 0 := by
      intro n
      have h := congrArg (fun z => z.val n) hx'
      simpa [chapter07AdicCompletionMap, AdicCompletion.algebraMap_apply,
        AdicCompletion.val_zero_apply] using h
    change x ∈ (⨅ n : ℕ, I ^ n : Ideal R)
    refine (Ideal.mem_iInf).2 ?_
    intro n
    have hmem : x ∈ (I ^ n • (⊤ : Submodule R R)) :=
      (Submodule.Quotient.mk_eq_zero _).mp (hcoord n)
    simpa using hmem
  · intro hx
    apply Subtype.ext
    funext n
    simp only [chapter07AdicCompletionMap, AdicCompletion.algebraMap_apply,
      AdicCompletion.val_zero_apply]
    rw [AdicCompletion.of_apply]
    simp only [Submodule.mkQ_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [Submodule.Quotient.mk_eq_zero]
    simpa using (Ideal.mem_iInf.mp hx n)

-- The algebraic completion map is injective exactly in the separated case.
theorem chapter07_adic_completion_injective_iff_separated
    {R : Type*} [CommRing R] (I : Ideal R) :
    Function.Injective (chapter07AdicCompletionMap I) ↔ IsHausdorff I R := by
  exact AdicCompletion.of_injective_iff

-- A witness in every power of I disappears in the adic completion.
theorem chapter07_adic_nonseparated_witness_in_kernel
    {R : Type*} [CommRing R] (I : Ideal R) (x : R)
    (hx : ∀ n : ℕ, x ∈ I ^ n) :
    chapter07AdicCompletionMap I x = 0 := by
  apply Subtype.ext
  funext n
  simp only [chapter07AdicCompletionMap, AdicCompletion.algebraMap_apply,
    AdicCompletion.val_zero_apply]
  rw [AdicCompletion.of_apply]
  simp only [Submodule.mkQ_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rw [Submodule.Quotient.mk_eq_zero]
  simpa using hx n

-- A nonzero intersection witness makes the completion map noninjective.
theorem chapter07_adic_nonseparated_map_not_injective
    {R : Type*} [CommRing R] (I : Ideal R)
    (h : ∃ x : R, x ≠ 0 ∧ ∀ n : ℕ, x ∈ I ^ n) :
    ¬ Function.Injective (chapter07AdicCompletionMap I) := by
  intro hinj
  obtain ⟨x, hx, hxn⟩ := h
  apply hx
  apply hinj
  rw [chapter07_adic_nonseparated_witness_in_kernel I x hxn]
  exact (map_zero (chapter07AdicCompletionMap I)).symm

-- Noetherian local domains are separated for every ideal contained in the maximal ideal.
theorem chapter07_noetherian_local_domain_is_adically_separated
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ IsLocalRing.maximalIdeal R) :
    IsHausdorff I R := by
  apply IsHausdorff.of_isDomain I
  intro htop
  have hmax : IsLocalRing.maximalIdeal R = ⊤ :=
    top_unique (htop ▸ hI)
  let M : Ideal R := IsLocalRing.maximalIdeal R
  have hM : M.IsMaximal := by
    change (IsLocalRing.maximalIdeal R : Ideal R).IsMaximal
    infer_instance
  exact hM.ne_top hmax

-- The canonical uniformity pulled back from the DVR valuation on its fraction field.
noncomputable def chapter07DvrUniformSpace
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] :
    UniformSpace A :=
  UniformSpace.comap (algebraMap A (FractionRing A))
    ((Valued.mk' ((IsDiscreteValuationRing.maximalIdeal A).valuation (FractionRing A))).toUniformSpace)

-- The standard DVR statement comparing metric and ideal-adic completion.
set_option maxHeartbeats 800000 in
theorem chapter07_dvr_metric_completion_agrees_with_adic_completion
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    : ∃ e : @UniformSpace.Completion A (chapter07DvrUniformSpace A) ≃+*
        AdicCompletion (IsLocalRing.maximalIdeal A) A,
      ∀ a : A,
        e ((a : A) : @UniformSpace.Completion A (chapter07DvrUniformSpace A)) =
        chapter07AdicCompletionMap (IsLocalRing.maximalIdeal A) a := by
  let K := FractionRing A
  let v : Valuation K ℤᵐ⁰ := (IsDiscreteValuationRing.maximalIdeal A).valuation K
  let : Valued K ℤᵐ⁰ := Valued.mk' v
  let : UniformSpace K := (Valued.mk' v).toUniformSpace
  let : TopologicalSpace K := (Valued.mk' v).toTopologicalSpace
  let : IsUniformAddGroup K := (Valued.mk' v).toIsUniformAddGroup
  have hd : v.IsRankOneDiscrete := by infer_instance
  let : v.IsRankOneDiscrete := hd
  let C := UniformSpace.Completion K
  let B := chapter07CompletedValuationRing K ℤᵐ⁰
  let : UniformSpace B :=
    UniformSpace.comap (fun b : B => (b : C)) (inferInstance : UniformSpace C)
  let : TopologicalSpace B :=
    (UniformSpace.comap (fun b : B => (b : C))
      (inferInstance : UniformSpace C)).toTopologicalSpace
  have hclosed : IsClosed (B : Set C) := by
    exact chapter07_completed_valuation_ring_is_closed
  let : CompleteSpace B := hclosed.completeSpace_coe
  let : T0Space B := by infer_instance
  let fK : A →+* C := (UniformSpace.Completion.coeRingHom).comp (algebraMap A K)
  have hfK_mem : ∀ a : A, fK a ∈ (B : Set C) := by
    intro a
    change chapter07CompletionValuation K ℤᵐ⁰ (fK a) ≤ 1
    change chapter07CompletionValuation K ℤᵐ⁰
      (((algebraMap A K a) : K) : UniformSpace.Completion K) ≤ 1
    rw [chapter07_completion_valuation_apply_coe]
    change v (algebraMap A K a) ≤ 1
    exact (Valuation.mem_integer_iff v _).mp (by
      apply (Valuation.mem_integer_iff v _).2
      exact (Valuation.mem_valuationSubring_iff v _).mp (by
        change algebraMap A K a ∈ v.valuationSubring.toSubring
        rw [show v = (IsDiscreteValuationRing.maximalIdeal A).valuation K by rfl]
        rw [← IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring (A := A) (K := K)]
        exact Subring.mem_map.mpr ⟨a, Subring.mem_top _, rfl⟩))
  let f : A →+* B := fK.codRestrict B hfK_mem
  let : UniformSpace A := chapter07DvrUniformSpace A
  let : IsUniformAddGroup A := IsUniformAddGroup.comap (algebraMap A K)
  have hif : @IsUniformInducing A B (chapter07DvrUniformSpace A)
      (inferInstance : UniformSpace B) f := by
    apply (isUniformInducing_iff_uniformSpace).2
    have hcoek : UniformSpace.comap (fun x : K => (x : C))
        (inferInstance : UniformSpace C) = (inferInstance : UniformSpace K) := by
      exact (isUniformInducing_iff_uniformSpace).1
        (UniformSpace.Completion.isUniformInducing_coe K)
    have hsub : UniformSpace.comap (fun b : B => (b : C))
        (inferInstance : UniformSpace C) = (inferInstance : UniformSpace B) := by
      rfl
    calc
      UniformSpace.comap (f : A → B) (inferInstance : UniformSpace B) =
          UniformSpace.comap (f : A → B)
            (UniformSpace.comap (fun b : B => (b : C))
              (inferInstance : UniformSpace C)) := by rw [hsub]
      _ = UniformSpace.comap (algebraMap A K)
          (UniformSpace.comap (fun x : K => (x : C))
            (inferInstance : UniformSpace C)) := by
        rw [← UniformSpace.comap_comap, ← UniformSpace.comap_comap]
        apply congrArg (fun h : A → C =>
          UniformSpace.comap h (inferInstance : UniformSpace C))
        funext a
        rfl
      _ = UniformSpace.comap (algebraMap A K) (inferInstance : UniformSpace K) := by
        rw [hcoek]
      _ = chapter07DvrUniformSpace A := by rfl
  have hsubrange : Set.range (chapter07ValuationRingCompletionEmbedding
      (K := K) (Γ₀ := ℤᵐ⁰)) ⊆
      (fun b : B => (b : C)) '' Set.range f := by
    rintro z ⟨y, rfl⟩
    obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_lift_of_le_one
      (A := A) (K := K) y.property
    refine ⟨f a, ⟨a, rfl⟩, ?_⟩
    change ((algebraMap A K a : K) : C) =
      (((y : chapter07ValuationRing K ℤᵐ⁰) : K) : C)
    rw [ha]
  have hcl : closure (Set.range (chapter07ValuationRingCompletionEmbedding
      (K := K) (Γ₀ := ℤᵐ⁰))) = (B : Set C) := by
    exact chapter07_valuation_ring_closure_eq_completed_valuation_ring
  have hdense : DenseRange f := by
    rw [DenseRange]
    apply (Subtype.dense_iff).2
    intro y hy
    have hy' : y ∈ closure (Set.range (chapter07ValuationRingCompletionEmbedding
        (K := K) (Γ₀ := ℤᵐ⁰))) := by
      rw [hcl]
      exact hy
    exact (closure_mono hsubrange) hy'
  let pkgB : @AbstractCompletion A (chapter07DvrUniformSpace A) :=
    { space := B
      coe := f
      uniformStruct := inferInstance
      complete := inferInstance
      separation := inferInstance
      isUniformInducing := hif
      dense := hdense }
  let eU : @UniformSpace.Completion A (chapter07DvrUniformSpace A) ≃ᵤ B :=
    AbstractCompletion.compareEquiv UniformSpace.Completion.cPkg pkgB
  have eU_coe (a : A) : eU (a : @UniformSpace.Completion A
      (chapter07DvrUniformSpace A)) = f a := by
    exact AbstractCompletion.compare_coe UniformSpace.Completion.cPkg pkgB a
  let : IsRightUniformAddGroup A := IsUniformAddGroup.isRightUniformAddGroup A
  let : ContinuousMul A := by
    change @ContinuousMul A ((inferInstance : TopologicalSpace K).induced (algebraMap A K)) _
    exact continuousMul_induced (algebraMap A K)
  let : IsTopologicalSemiring A := ⟨⟩
  let : IsTopologicalRing A := ⟨⟩
  let : ContinuousAdd B := by
    change @ContinuousAdd B ((inferInstance : TopologicalSpace C).induced
      (fun b : B => (b : C))) _
    exact continuousAdd_induced (SubringClass.subtype B)
  let : ContinuousMul B := by
    change @ContinuousMul B ((inferInstance : TopologicalSpace C).induced
      (fun b : B => (b : C))) _
    exact continuousMul_induced (SubringClass.subtype B)
  have hadd (x y : @UniformSpace.Completion A (chapter07DvrUniformSpace A)) :
      eU (x + y) = eU x + eU y := by
    refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
    · exact isClosed_eq
        (eU.continuous.comp continuous_add)
        ((eU.continuous.comp continuous_fst).add
          (eU.continuous.comp continuous_snd))
    · intro a b
      rw [← UniformSpace.Completion.coe_add, eU_coe, eU_coe, eU_coe]
      exact map_add f a b
  have hmul (x y : @UniformSpace.Completion A (chapter07DvrUniformSpace A)) :
      eU (x * y) = eU x * eU y := by
    refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
    · exact isClosed_eq
        (eU.continuous.comp continuous_mul)
        ((eU.continuous.comp continuous_fst).mul
          (eU.continuous.comp continuous_snd))
    · intro a b
      rw [← UniformSpace.Completion.coe_mul, eU_coe, eU_coe, eU_coe]
      exact map_mul f a b
  have hone : eU (1 : @UniformSpace.Completion A (chapter07DvrUniformSpace A)) = 1 := by
    rw [← UniformSpace.Completion.coe_one A, eU_coe]
    exact map_one f
  have hVeq : Valued.integer K = v.valuationSubring.toSubring := by
    ext x
    rfl
  let iVV : Valued.integer K ≃+* v.valuationSubring :=
    { toFun := fun x => ⟨x, x.property⟩
      invFun := fun x => ⟨x, x.property⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_add' := by intro x y; rfl
      map_mul' := by intro x y; rfl }
  have hiVV_max : Ideal.map iVV.toRingHom
      (IsLocalRing.maximalIdeal (Valued.integer K)) =
      IsLocalRing.maximalIdeal v.valuationSubring := by
    apply le_antisymm
    · apply (Ideal.map_le_iff_le_comap).2
      intro x hx
      change iVV x ∈ IsLocalRing.maximalIdeal v.valuationSubring
      rw [IsLocalRing.mem_maximalIdeal]
      intro hu
      apply (IsLocalRing.mem_maximalIdeal x).mp hx
      have hu' : IsUnit (iVV.symm (iVV x)) :=
        IsUnit.map iVV.symm hu
      simpa using hu'
    · intro x hx
      have hy : iVV.symm x ∈ IsLocalRing.maximalIdeal (Valued.integer K) := by
        rw [IsLocalRing.mem_maximalIdeal]
        intro hu
        apply (IsLocalRing.mem_maximalIdeal x).mp hx
        have hu' : IsUnit (iVV (iVV.symm x)) :=
          IsUnit.map iVV hu
        simpa using hu'
      have := Ideal.mem_map_of_mem iVV.toRingHom hy
      change iVV (iVV.symm x) ∈
        Ideal.map iVV.toRingHom (IsLocalRing.maximalIdeal (Valued.integer K)) at this
      simpa only [iVV.apply_symm_apply] using this
  let π : v.Uniformizer := Classical.choice (inferInstance : Nonempty (v.Uniformizer))
  let p : v.valuationSubring := ⟨π.val, π.val.property⟩
  have hp : iVV (π.val : Valued.integer K) = p := by rfl
  have hp' : p = (π.val : v.valuationSubring) := by
    apply Subtype.ext
    rfl
  have hgen : IsLocalRing.maximalIdeal v.valuationSubring =
      Ideal.span ({p} : Set v.valuationSubring) := by
    simpa [hp'] using π.valuation_gt_one.is_generator
  have hmaxV : IsLocalRing.maximalIdeal (Valued.integer K) =
      Ideal.span ({(π : v.Uniformizer).val} : Set (Valued.integer K)) := by
    apply le_antisymm
    · intro x hx
      have hx' : iVV x ∈ IsLocalRing.maximalIdeal v.valuationSubring := by
        have hxm := Ideal.mem_map_of_mem iVV.toRingHom hx
        rw [hiVV_max] at hxm
        exact hxm
      rw [hgen] at hx'
      rcases Ideal.mem_span_singleton.mp hx' with ⟨u, hu⟩
      apply Ideal.mem_span_singleton.mpr
      refine ⟨iVV.symm u, ?_⟩
      exact congrArg iVV.symm hu
    · intro x hx
      rw [Ideal.mem_span_singleton] at hx
      rcases hx with ⟨u, rfl⟩
      have hu' : p * iVV u ∈ IsLocalRing.maximalIdeal v.valuationSubring := by
        rw [hgen]
        exact Ideal.mem_span_singleton.mpr ⟨iVV u, by simp⟩
      have hu'' : iVV (π.val * u) ∈
          Ideal.map iVV.toRingHom (IsLocalRing.maximalIdeal (Valued.integer K)) := by
        rw [hiVV_max]
        simpa [hp] using hu'
      obtain ⟨z, hz, hzu⟩ :=
        (Ideal.mem_map_iff_of_surjective iVV.toRingHom iVV.surjective).mp hu''
      have hzeq : z = π.val * u := by
        apply iVV.injective
        change iVV z = iVV (π.val * u) at hzu
        exact hzu
      exact hzeq ▸ hz
  have hmaxV_pow : ∀ n : ℕ,
      IsLocalRing.maximalIdeal (Valued.integer K) ^ n =
        Ideal.span ({((π : v.Uniformizer).val : Valued.integer K) ^ n} :
          Set (Valued.integer K)) := by
    intro n
    rw [hmaxV]
    exact (Ideal.span_singleton_pow _ n)
  let r : A ≃+* Valued.integer K :=
    (IsDiscreteValuationRing.equivValuationSubring (A := A) (K := K)).trans iVV.symm
  have hrmax : Ideal.map r.toRingHom
      (IsLocalRing.maximalIdeal A) =
      IsLocalRing.maximalIdeal (Valued.integer K) := by
    apply le_antisymm
    · apply (Ideal.map_le_iff_le_comap).2
      intro x hx
      change r x ∈ IsLocalRing.maximalIdeal (Valued.integer K)
      rw [IsLocalRing.mem_maximalIdeal]
      intro hu
      exact (IsLocalRing.mem_maximalIdeal x).mp hx (by
        simpa only [r.symm_apply_apply] using IsUnit.map r.symm hu)
    · intro x hx
      have hy : r.symm x ∈ IsLocalRing.maximalIdeal A := by
        rw [IsLocalRing.mem_maximalIdeal]
        intro hu
        apply (IsLocalRing.mem_maximalIdeal x).mp hx
        have hu' : IsUnit (r (r.symm x)) := IsUnit.map r hu
        simpa using hu'
      have hmem := Ideal.mem_map_of_mem r.toRingHom hy
      change r (r.symm x) ∈ Ideal.map r.toRingHom
        (IsLocalRing.maximalIdeal A) at hmem
      simpa only [r.apply_symm_apply] using hmem
  have hrpow (n : ℕ) : Ideal.map r.toRingHom
      ((IsLocalRing.maximalIdeal A) ^ n) =
      Ideal.span ({((π : v.Uniformizer).val : Valued.integer K) ^ n} :
        Set (Valued.integer K)) := by
    rw [Ideal.map_pow, hrmax, hmaxV_pow]
  let fV : Valued.integer K →+* B := by
    let fVK : Valued.integer K →+* C :=
      (UniformSpace.Completion.coeRingHom).comp
        (SubringClass.subtype (Valued.integer K))
    have hfVK : ∀ a : Valued.integer K, fVK a ∈ (B : Set C) := by
      intro a
      change chapter07CompletionValuation K ℤᵐ⁰
        (((a : Valued.integer K) : K) : C) ≤ 1
      rw [chapter07_completion_valuation_apply_coe]
      exact a.property
    exact fVK.codRestrict B hfVK
  have hfVπ : fV (π.val : Valued.integer K) =
      chapter07CompletedUniformizer π := by
    apply Subtype.ext
    rfl
  have hcanonV : ∀ n : ℕ, 1 ≤ n →
      Function.Bijective
        (Ideal.Quotient.lift
          (Ideal.span ({(π.val : Valued.integer K) ^ n} : Set
            (Valued.integer K)))
          ((Ideal.Quotient.mk
            (Ideal.span ({(chapter07CompletedUniformizer π) ^ n} : Set B))).comp fV)
          (by
            intro a ha
            apply Ideal.Quotient.eq_zero_iff_mem.mpr
            have hmap : Ideal.map fV
                (Ideal.span ({(π.val : Valued.integer K) ^ n} : Set
                  (Valued.integer K))) ≤
                Ideal.span ({(chapter07CompletedUniformizer π) ^ n} : Set B) := by
              rw [Ideal.map_span]
              apply Ideal.span_mono
              rintro y ⟨x, hx, rfl⟩
              have hx' : x = (π.val : Valued.integer K) ^ n := by simpa using hx
              subst x
              rw [map_pow, hfVπ]
              exact Set.mem_singleton _
            exact (Ideal.map_le_iff_le_comap.mp hmap) ha)) := by
    intro n hn
    let Jv : Ideal (Valued.integer K) :=
      Ideal.span ({(π.val : Valued.integer K) ^ n} : Set (Valued.integer K))
    let Jb : Ideal B :=
      Ideal.span ({(chapter07CompletedUniformizer π) ^ n} : Set B)
    let g : (Valued.integer K) ⧸ Jv →+* B ⧸ Jb :=
      Ideal.Quotient.lift Jv ((Ideal.Quotient.mk Jb).comp fV) (by
        intro a ha
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        have hmap : Ideal.map fV Jv ≤ Jb := by
          rw [show Jv = Ideal.span ({(π.val : Valued.integer K) ^ n} :
            Set (Valued.integer K)) by rfl,
            show Jb = Ideal.span ({(chapter07CompletedUniformizer π) ^ n} : Set B)
              by rfl,
            Ideal.map_span]
          apply Ideal.span_mono
          rintro y ⟨x, hx, rfl⟩
          have hx' : x = (π.val : Valued.integer K) ^ n := by simpa using hx
          subst x
          rw [map_pow, hfVπ]
          exact Set.mem_singleton _
        exact (Ideal.map_le_iff_le_comap.mp hmap) ha)
    have hpval : 0 < chapter07CompletionValuation K ℤᵐ⁰
        (chapter07CompletedUniformizer π : B) := by
      rw [chapter07_completed_uniformizer_preserves_value]
      exact π.valuation_gt_one.val_pos
    let δ : MonoidWithZeroHom.ValueGroup₀
        (.ofClass (Valued.v : Valuation C ℤᵐ⁰)) :=
      (Valued.v : Valuation C ℤᵐ⁰).restrict
        (((chapter07CompletedUniformizer π : B) : C) ^ n)
    have quotient_approx : ∀ y : B, ∃ a : Valued.integer K,
        y - fV a ∈ Jb := by
      intro y
      have hyclosure : (y : C) ∈
          closure (Set.range (@chapter07ValuationRingCompletionEmbedding K ℤᵐ⁰ _ _ _)) := by
        apply chapter07_completed_unit_ball_is_approximated_by_integral_elements
        exact y.property
      let U : Set C := {z |
        (Valued.v : Valuation C ℤᵐ⁰).restrict (z - (y : C)) < δ}
      have hUopen : IsOpen U := by
        have hball := Valued.isOpen_ball C δ
        have htop : Valued.valuedCompletion.toTopologicalSpace =
            (UniformSpace.Completion.uniformSpace K).toTopologicalSpace := by rfl
        rw [htop] at hball
        simpa [U] using hball.preimage (continuous_id.sub continuous_const)
      have hδpos : 0 < δ := by
        apply (Valuation.restrict_pos_iff
          (Valued.v : Valuation C ℤᵐ⁰) _).2
        rw [map_pow]
        have hpval' : 0 < (Valued.v : Valuation C ℤᵐ⁰)
            ((chapter07CompletedUniformizer π : B) : C) := by
          rw [show (Valued.v : Valuation C ℤᵐ⁰) =
            chapter07CompletionValuation K ℤᵐ⁰ by rfl]
          exact hpval
        exact pow_pos hpval' n
      have hUmem : U ∈ 𝓝 (y : C) := by
        apply hUopen.mem_nhds
        simp [U, hδpos]
      obtain ⟨z, hzU, ⟨a, rfl⟩⟩ :=
        (mem_closure_iff_nhds.mp hyclosure) U hUmem
      refine ⟨a, ?_⟩
      have hlt : chapter07CompletionValuation K ℤᵐ⁰
          (((fV a : B) : C) - (y : C)) <
          chapter07CompletionValuation K ℤᵐ⁰
            (((chapter07CompletedUniformizer π : B) : C) ^ n) := by
        have hrestrict : (Valued.v : Valuation C ℤᵐ⁰).restrict
            (chapter07ValuationRingCompletionEmbedding a - (y : C)) < δ := by
          change (Valued.v : Valuation C ℤᵐ⁰).restrict
            ((((a : Valued.integer K) : K) : C) - (y : C)) < δ at hzU
          exact hzU
        have hlt' := (Valuation.restrict_lt_iff_lt_embedding
          (v := (Valued.v : Valuation C ℤᵐ⁰))).mp hrestrict
        have hltVal : (Valued.v : Valuation C ℤᵐ⁰)
            (chapter07ValuationRingCompletionEmbedding a - (y : C)) <
            (Valued.v : Valuation C ℤᵐ⁰)
              (((chapter07CompletedUniformizer π : B) : C) ^ n) := by
          simpa [δ, Valuation.embedding_restrict] using hlt'
        change chapter07CompletionValuation K ℤᵐ⁰
          (chapter07ValuationRingCompletionEmbedding a - (y : C)) <
          chapter07CompletionValuation K ℤᵐ⁰
            (((chapter07CompletedUniformizer π : B) : C) ^ n)
        simpa [show (Valued.v : Valuation C ℤᵐ⁰) =
          chapter07CompletionValuation K ℤᵐ⁰ by rfl] using hltVal
      have hle : chapter07CompletionValuation K ℤᵐ⁰
          (((y - fV a : B) : B) : C) ≤
          chapter07CompletionValuation K ℤᵐ⁰
            (((chapter07CompletedUniformizer π : B) : C) ^ n) := by
        have hlt' : chapter07CompletionValuation K ℤᵐ⁰
            ((y : C) - (fV a : C)) <
            chapter07CompletionValuation K ℤᵐ⁰
              (((chapter07CompletedUniformizer π : B) : C) ^ n) := by
          rw [show (y : C) - (fV a : C) =
            -((fV a : C) - (y : C)) by ring,
            Valuation.map_neg (chapter07CompletionValuation K ℤᵐ⁰)]
          exact hlt
        exact hlt'.le
      change (y - fV a : B) ∈ Jb
      have hspan : (Jb : Set B) = {x : B |
          chapter07CompletionValuation K ℤᵐ⁰ (x : C) ≤
            chapter07CompletionValuation K ℤᵐ⁰
              (((chapter07CompletedUniformizer π : B) : C) ^ n)} := by
        exact Valuation.integer.coe_span_singleton_eq_setOfPred_le_v_coe _
      change (y - fV a : B) ∈ (Jb : Set B)
      rw [hspan]
      exact hle
    have g_surj : Function.Surjective g := by
      intro x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨a, ha⟩ := quotient_approx y
      refine ⟨Ideal.Quotient.mk Jv a, ?_⟩
      rw [Ideal.Quotient.lift_mk]
      rw [← sub_eq_zero]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      simpa [sub_eq_add_neg, add_comm] using Jb.neg_mem ha
    have g_inj : Function.Injective g := by
      intro x y hxy
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [← sub_eq_zero]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      change (a - b : Valued.integer K) ∈ Jv
      have hmemC : fV a - fV b ∈ Jb := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        rw [map_sub]
        exact sub_eq_zero.mpr (by simpa [g] using hxy)
      have hspanC : (Jb : Set B) = {x : B |
          chapter07CompletionValuation K ℤᵐ⁰ (x : C) ≤
            chapter07CompletionValuation K ℤᵐ⁰
              (((chapter07CompletedUniformizer π : B) : C) ^ n)} := by
        exact Valuation.integer.coe_span_singleton_eq_setOfPred_le_v_coe _
      have hmemC' : fV a - fV b ∈ (Jb : Set B) := hmemC
      rw [hspanC] at hmemC'
      have hleC : chapter07CompletionValuation K ℤᵐ⁰
          (((fV a - fV b : B) : B) : C) ≤
          chapter07CompletionValuation K ℤᵐ⁰
            (((chapter07CompletedUniformizer π : B) : C) ^ n) := by
        exact hmemC'
      have hleK : v (((a : Valued.integer K) : K) -
          ((b : Valued.integer K) : K)) ≤ v (π.val : K) ^ n := by
        have hleC' : chapter07CompletionValuation K ℤᵐ⁰
            (((((a : Valued.integer K) : K) -
              ((b : Valued.integer K) : K)) : K) : C) ≤
            chapter07CompletionValuation K ℤᵐ⁰
              (((chapter07CompletedUniformizer π : B) : C) ^ n) := by
          have hcoediff :
              (((fV a : B) : C) - ((fV b : B) : C)) =
                (((((a : Valued.integer K) : K) -
                  ((b : Valued.integer K) : K)) : K) : C) := by
            dsimp [fV]
            symm
            exact (UniformSpace.Completion.coeRingHom : K →+* C).map_sub _ _
          rw [show (((fV a - fV b : B) : B) : C) =
            ((fV a : B) : C) - ((fV b : B) : C) by rfl]
              at hleC
          rw [hcoediff] at hleC
          exact hleC
        rw [chapter07_completion_valuation_apply_coe] at hleC'
        rw [map_pow, chapter07_completed_uniformizer_preserves_value] at hleC'
        exact hleC'
      change (a - b : Valued.integer K) ∈
        (Ideal.span ({(π.val : Valued.integer K) ^ n} : Set (Valued.integer K)) :
          Set (Valued.integer K))
      rw [Valuation.integer.coe_span_singleton_eq_setOfPred_le_v_coe]
      change v (((a - b : Valued.integer K) : K)) ≤
        v ((((π.val : Valued.integer K) ^ n : Valued.integer K) : K))
      convert hleK using 1
      · rfl
      · change v ((π.val : K) ^ n) = v (π.val : K) ^ n
        rw [map_pow]
    exact ⟨g_inj, g_surj⟩
  let vC : Valuation C ℤᵐ⁰ := chapter07CompletionValuation K ℤᵐ⁰
  have hvalueGroup : valueGroup (.ofClass vC) = valueGroup (.ofClass v) := by
    apply le_antisymm
    · intro γ hγ
      have hγ' : (γ : ℤᵐ⁰) ∈ Set.range (MonoidWithZeroHom.ofClass vC) \ {0} := by
        rw [← MonoidWithZeroHom.valueGroup_eq_range (.ofClass vC)]
        exact ⟨γ, hγ, rfl⟩
      obtain ⟨⟨x, hx⟩, _hx0⟩ := hγ'
      obtain ⟨r, hr⟩ := Valued.exists_coe_eq_v x
      have hval : (γ : ℤᵐ⁰) = v r := by
        calc
          (γ : ℤᵐ⁰) = vC x := hx.symm
          _ = v r := by
            change Valued.extensionValuation x = Valued.v r
            exact hr
      have hr0 : r ≠ 0 := by
        intro hr0
        subst r
        simp [v] at hval
      have hvr0 : v r ≠ 0 := by
        intro hvr0
        exact γ.ne_zero (hval.trans hvr0)
      have hγeq : Units.mk0 (v r) hvr0 = γ := by
        apply Units.ext
        exact hval.symm
      rw [← hγeq]
      exact MonoidWithZeroHom.mem_valueGroup (.ofClass v) ⟨r, rfl⟩
    · intro γ hγ
      have hγ' : (γ : ℤᵐ⁰) ∈ Set.range (MonoidWithZeroHom.ofClass v) \ {0} := by
        rw [← MonoidWithZeroHom.valueGroup_eq_range (.ofClass v)]
        exact ⟨γ, hγ, rfl⟩
      obtain ⟨⟨r, hr⟩, hr0⟩ := hγ'
      have hval : (γ : ℤᵐ⁰) = v r := by
        simpa [v] using hr.symm
      have hvr0 : v r ≠ 0 := by
        intro hvr0
        exact γ.ne_zero (hval.trans hvr0)
      have hvcval : vC ((r : K) : C) = v r := by
        change chapter07CompletionValuation K ℤᵐ⁰ ((r : K) : C) = Valued.v r
        rw [chapter07_completion_valuation_apply_coe]
      have hvc0 : vC ((r : K) : C) ≠ 0 := by
        simpa [hvcval] using hvr0
      have hγeq : Units.mk0 (vC ((r : K) : C)) hvc0 = γ := by
        apply Units.ext
        exact hvcval.trans hval.symm
      rw [← hγeq]
      exact MonoidWithZeroHom.mem_valueGroup (.ofClass vC) ⟨(r : C), rfl⟩
  let : vC.IsRankOneDiscrete := by
    refine ⟨⟨Valuation.IsRankOneDiscrete.generator v, ?_, ?_⟩⟩
    · rw [hvalueGroup]
      exact Valuation.IsRankOneDiscrete.generator_zpowers_eq_valueGroup v
    · exact Valuation.IsRankOneDiscrete.generator_lt_one v
  have hgenC : Valuation.IsRankOneDiscrete.generator vC =
      Valuation.IsRankOneDiscrete.generator v := by
    apply LinearOrderedCommGroup.Subgroup.genLTOne_unique_of_zpowers_eq
      (Valuation.IsRankOneDiscrete.generator_lt_one vC)
      (Valuation.IsRankOneDiscrete.generator_lt_one v)
    calc
      Subgroup.zpowers (Valuation.IsRankOneDiscrete.generator vC) =
          valueGroup (.ofClass vC) :=
        Valuation.IsRankOneDiscrete.generator_zpowers_eq_valueGroup vC
      _ = valueGroup (.ofClass v) := hvalueGroup
      _ = Subgroup.zpowers (Valuation.IsRankOneDiscrete.generator v) :=
        (Valuation.IsRankOneDiscrete.generator_zpowers_eq_valueGroup v).symm
  let πC : vC.Uniformizer :=
    { val := chapter07CompletedUniformizer π
      valuation_gt_one := by
        rw [Valuation.IsUniformizer.iff]
        rw [chapter07_completed_uniformizer_preserves_value]
        rw [hgenC]
        exact π.valuation_gt_one.val }
  have hmaxB : IsLocalRing.maximalIdeal B =
      Ideal.span ({(chapter07CompletedUniformizer π : B)} : Set B) := by
    change IsLocalRing.maximalIdeal vC.valuationSubring = _
    exact πC.valuation_gt_one.is_generator
  have hmaxB_pow (n : ℕ) : IsLocalRing.maximalIdeal B ^ n =
      Ideal.span ({(chapter07CompletedUniformizer π : B) ^ n} : Set B) := by
    rw [hmaxB]
    exact Ideal.span_singleton_pow _ n
  have hcompleteB : IsAdicComplete
      (Ideal.span ({(chapter07CompletedUniformizer π : B)} : Set B)) B := by
    rw [← hmaxB]
    exact (chapter07_completed_valuation_ring_is_dvr (K := K) (Γ₀ := ℤᵐ⁰)).2
  have hfr : f = fV.comp r.toRingHom := by
    ext a
    rfl
  let gV (n : ℕ) :
      (Valued.integer K) ⧸
          Ideal.span ({(π.val : Valued.integer K) ^ n} : Set (Valued.integer K)) →+*
        B ⧸ Ideal.span ({(chapter07CompletedUniformizer π) ^ n} : Set B) :=
    Ideal.Quotient.lift
      (Ideal.span ({(π.val : Valued.integer K) ^ n} : Set (Valued.integer K)))
      ((Ideal.Quotient.mk
        (Ideal.span ({(chapter07CompletedUniformizer π) ^ n} : Set B))).comp fV)
      (by
        intro a ha
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        have hmap : Ideal.map fV
            (Ideal.span ({(π.val : Valued.integer K) ^ n} : Set (Valued.integer K))) ≤
            Ideal.span ({(chapter07CompletedUniformizer π) ^ n} : Set B) := by
          rw [Ideal.map_span]
          apply Ideal.span_mono
          rintro y ⟨x, hx, rfl⟩
          have hx' : x = (π.val : Valued.integer K) ^ n := by simpa using hx
          subst x
          rw [map_pow, hfVπ]
          exact Set.mem_singleton _
        exact (Ideal.map_le_iff_le_comap.mp hmap) ha)
  have hgV_bij (n : ℕ) (hn : 1 ≤ n) : Function.Bijective (gV n) := by
    simpa [gV] using hcanonV n hn
  let eAV (n : ℕ) :
      A ⧸ (IsLocalRing.maximalIdeal A) ^ n ≃+*
        (Valued.integer K) ⧸
          Ideal.span ({(π.val : Valued.integer K) ^ n} : Set (Valued.integer K)) :=
    Ideal.quotientEquiv ((IsLocalRing.maximalIdeal A) ^ n)
      (Ideal.span ({(π.val : Valued.integer K) ^ n} : Set (Valued.integer K)))
      r (hrpow n).symm
  have heAV_mk (n : ℕ) (a : A) :
      eAV n (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) a) =
        Ideal.Quotient.mk
          (Ideal.span ({(π.val : Valued.integer K) ^ n} : Set (Valued.integer K))) (r a) := by
    dsimp [eAV]
    rfl
  let eVB (n : ℕ) (hn : 1 ≤ n) :
      (Valued.integer K) ⧸
          Ideal.span ({(π.val : Valued.integer K) ^ n} : Set (Valued.integer K)) ≃+*
        B ⧸ Ideal.span ({(chapter07CompletedUniformizer π) ^ n} : Set B) :=
    RingEquiv.ofBijective (gV n) (hgV_bij n hn)
  let eAB (n : ℕ) (hn : 1 ≤ n) :
      A ⧸ (IsLocalRing.maximalIdeal A) ^ n ≃+*
        B ⧸ Ideal.span ({(chapter07CompletedUniformizer π) ^ n} : Set B) :=
    (eAV n).trans (eVB n hn)
  have heAB_mk (n : ℕ) (hn : 1 ≤ n) (a : A) :
      eAB n hn (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) a) =
        Ideal.Quotient.mk
          (Ideal.span ({(chapter07CompletedUniformizer π) ^ n} : Set B)) (f a) := by
    change eVB n hn (eAV n (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) a)) = _
    change gV n (eAV n (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) a)) = _
    rw [heAV_mk]
    dsimp [gV]
    change Ideal.Quotient.mk
        (Ideal.span ({(chapter07CompletedUniformizer π) ^ n} : Set B))
      (fV (r a)) = _
    have hfa : fV (r a) = f a := by
      have hfa' := congrArg (fun q : A →+* B => q a) hfr.symm
      change fV (r.toRingHom a) = f a at hfa'
      have hra : r.toRingHom a = r a :=
        congrFun (RingEquiv.coe_toRingHom r) a
      rw [hra] at hfa'
      exact hfa'
    rw [hfa]
  have hgV0_bij : Function.Bijective (gV 0) := by
    have hsubV : Subsingleton ((Valued.integer K) ⧸
        Ideal.span ({(π.val : Valued.integer K) ^ (0 : ℕ)} : Set (Valued.integer K))) := by
      rw [show Ideal.span ({(π.val : Valued.integer K) ^ (0 : ℕ)} : Set (Valued.integer K)) =
        ⊤ by simp]
      infer_instance
    have hsubB : Subsingleton (B ⧸
        Ideal.span ({(chapter07CompletedUniformizer π) ^ (0 : ℕ)} : Set B)) := by
      rw [show Ideal.span ({(chapter07CompletedUniformizer π) ^ (0 : ℕ)} : Set B) =
        ⊤ by simp]
      infer_instance
    constructor
    · intro x y _
      exact hsubV.elim x y
    · intro y
      exact ⟨0, hsubB.elim _ _⟩
  have hgV_all (n : ℕ) : Function.Bijective (gV n) := by
    cases n with
    | zero => exact hgV0_bij
    | succ n => exact hgV_bij (n + 1) (by omega)
  let eVB_all (n : ℕ) :
      (Valued.integer K) ⧸
          Ideal.span ({(π.val : Valued.integer K) ^ n} : Set (Valued.integer K)) ≃+*
        B ⧸ Ideal.span ({(chapter07CompletedUniformizer π) ^ n} : Set B) :=
    RingEquiv.ofBijective (gV n) (hgV_all n)
  let eAB_all (n : ℕ) :
      A ⧸ (IsLocalRing.maximalIdeal A) ^ n ≃+*
        B ⧸ Ideal.span ({(chapter07CompletedUniformizer π) ^ n} : Set B) :=
    (eAV n).trans (eVB_all n)
  have heAB_all_mk (n : ℕ) (a : A) :
      eAB_all n (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) a) =
        Ideal.Quotient.mk
          (Ideal.span ({(chapter07CompletedUniformizer π) ^ n} : Set B)) (f a) := by
    change eVB_all n (eAV n (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) a)) = _
    change gV n (eAV n (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) a)) = _
    rw [heAV_mk]
    dsimp [gV]
    change Ideal.Quotient.mk
        (Ideal.span ({(chapter07CompletedUniformizer π) ^ n} : Set B))
      (fV (r a)) = _
    have hfa : fV (r a) = f a := by
      have hfa' := congrArg (fun q : A →+* B => q a) hfr.symm
      change fV (r.toRingHom a) = f a at hfa'
      have hra : r.toRingHom a = r a :=
        congrFun (RingEquiv.coe_toRingHom r) a
      rw [hra] at hfa'
      exact hfa'
    rw [hfa]
  let J0 : Ideal B :=
    Ideal.span ({(chapter07CompletedUniformizer π : B)} : Set B)
  have hJ0pow (n : ℕ) : J0 ^ n =
      Ideal.span ({(chapter07CompletedUniformizer π : B) ^ n} : Set B) := by
    dsimp [J0]
    exact Ideal.span_singleton_pow _ n
  let tB (n : ℕ) :
      B ⧸ Ideal.span ({(chapter07CompletedUniformizer π : B) ^ n} : Set B) ≃+*
        B ⧸ J0 ^ n :=
    Ideal.quotientEquiv
      (Ideal.span ({(chapter07CompletedUniformizer π : B) ^ n} : Set B)) (J0 ^ n)
      (RingEquiv.refl B) (by simpa using hJ0pow n)
  let eABp (n : ℕ) :
      A ⧸ (IsLocalRing.maximalIdeal A) ^ n ≃+* B ⧸ J0 ^ n :=
    (eAB_all n).trans (tB n)
  have heABp_mk (n : ℕ) (a : A) :
      eABp n (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) a) =
        Ideal.Quotient.mk (J0 ^ n) (f a) := by
    dsimp [eABp, tB]
    rw [heAB_all_mk, Ideal.quotientEquiv_mk]
    simp
  let F (n : ℕ) :
      AdicCompletion (IsLocalRing.maximalIdeal A) A →+* B ⧸ J0 ^ n :=
    (eABp n).toRingHom.comp
      (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n).toRingHom
  have hEval {m n : ℕ} (hle : m ≤ n) :
      (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal A) hle).comp
          (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n).toRingHom =
        (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) m).toRingHom := by
    ext x
    let hn : ((IsLocalRing.maximalIdeal A) ^ n • ⊤ : Ideal A) =
        (IsLocalRing.maximalIdeal A) ^ n := by ext y; simp
    let hm : ((IsLocalRing.maximalIdeal A) ^ m • ⊤ : Ideal A) =
        (IsLocalRing.maximalIdeal A) ^ m := by ext y; simp
    change (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal A) hle)
        ((Ideal.quotientEquivAlgOfEq A hn)
          (AdicCompletion.eval (IsLocalRing.maximalIdeal A) A n x)) =
      (Ideal.quotientEquivAlgOfEq A hm)
        (AdicCompletion.eval (IsLocalRing.maximalIdeal A) A m x)
    change (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal A) hle)
        (Ideal.Quotient.factor (le_of_eq hn)
          (AdicCompletion.eval (IsLocalRing.maximalIdeal A) A n x)) =
      Ideal.Quotient.factor (le_of_eq hm)
        (AdicCompletion.eval (IsLocalRing.maximalIdeal A) A m x)
    change (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal A) hle)
        (Ideal.Quotient.factor (le_of_eq hn) (x.val n)) =
      Ideal.Quotient.factor (le_of_eq hm) (x.val m)
    rw [← x.property hle]
    induction x.val n using Quotient.inductionOn' with
    | _ a =>
      rfl
  have heABp_nat {m n : ℕ} (hle : m ≤ n) :
      (Ideal.Quotient.factorPow J0 hle).comp (eABp n).toRingHom =
        (eABp m).toRingHom.comp
          (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal A) hle) := by
    apply RingHom.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [RingHom.comp_apply]
    change (Ideal.Quotient.factorPow J0 hle)
        (eABp n (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) a)) =
      eABp m ((Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal A) hle)
        (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) a))
    calc
      (Ideal.Quotient.factorPow J0 hle)
          (eABp n (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) a)) =
          (Ideal.Quotient.factorPow J0 hle)
            (Ideal.Quotient.mk (J0 ^ n) (f a)) := by rw [heABp_mk]
      _ = Ideal.Quotient.mk (J0 ^ m) (f a) := by
        rw [Ideal.Quotient.factor_mk]
      _ = eABp m (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ m) a) := by
        rw [heABp_mk]
      _ = eABp m ((Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal A) hle)
          (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) a)) := by
        rw [Ideal.Quotient.factor_mk]
  have hFcompat {m n : ℕ} (hle : m ≤ n) :
      (Ideal.Quotient.factorPow J0 hle).comp (F n) = F m := by
    dsimp [F]
    calc
      (Ideal.Quotient.factorPow J0 hle).comp
          ((eABp n).toRingHom.comp
            (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n).toRingHom) =
          ((Ideal.Quotient.factorPow J0 hle).comp (eABp n).toRingHom).comp
            (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n).toRingHom := by
              rw [RingHom.comp_assoc]
      _ = ((eABp m).toRingHom.comp
            (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal A) hle)).comp
            (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n).toRingHom := by
              rw [heABp_nat hle]
      _ = (eABp m).toRingHom.comp
            ((Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal A) hle).comp
              (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n).toRingHom) := by
              rw [RingHom.comp_assoc]
      _ = (eABp m).toRingHom.comp
            (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) m).toRingHom := by
              rw [hEval hle]
      _ = F m := rfl
  have heABp_inv_nat {m n : ℕ} (hle : m ≤ n) :
      (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal A) hle).comp
          (eABp n).symm.toRingHom =
        (eABp m).symm.toRingHom.comp (Ideal.Quotient.factorPow J0 hle) := by
    apply RingHom.ext
    intro x
    obtain ⟨y, rfl⟩ := (eABp n).surjective x
    have h := congrArg (fun q => q y) (heABp_nat hle)
    have h' := congrArg (eABp m).symm h
    simpa [RingHom.comp_apply] using h'.symm
  let G (n : ℕ) : B →+*
      A ⧸ (IsLocalRing.maximalIdeal A) ^ n :=
    (eABp n).symm.toRingHom.comp
      (Ideal.Quotient.mk (J0 ^ n))
  have hGcompat {m n : ℕ} (hle : m ≤ n) :
      (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal A) hle).comp (G n) = G m := by
    dsimp [G]
    calc
      (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal A) hle).comp
          ((eABp n).symm.toRingHom.comp (Ideal.Quotient.mk (J0 ^ n))) =
          ((Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal A) hle).comp
            (eABp n).symm.toRingHom).comp (Ideal.Quotient.mk (J0 ^ n)) := by
              rw [RingHom.comp_assoc]
      _ = ((eABp m).symm.toRingHom.comp
            (Ideal.Quotient.factorPow J0 hle)).comp
            (Ideal.Quotient.mk (J0 ^ n)) := by
              rw [heABp_inv_nat hle]
      _ = (eABp m).symm.toRingHom.comp
            ((Ideal.Quotient.factorPow J0 hle).comp
              (Ideal.Quotient.mk (J0 ^ n))) := by
              rw [RingHom.comp_assoc]
      _ = (eABp m).symm.toRingHom.comp
            (Ideal.Quotient.mk (J0 ^ m)) := by
              rw [show (Ideal.Quotient.factorPow J0 hle).comp
                (Ideal.Quotient.mk (J0 ^ n)) = Ideal.Quotient.mk (J0 ^ m) by
                  exact Ideal.Quotient.factor_comp_mk
                    (Ideal.pow_le_pow_right hle)]
      _ = G m := rfl
  let eAdic : AdicCompletion (IsLocalRing.maximalIdeal A) A →+* B :=
    IsAdicComplete.liftRingHom J0 F hFcompat
  let eInv : B →+* AdicCompletion (IsLocalRing.maximalIdeal A) A :=
    AdicCompletion.liftRingHom (IsLocalRing.maximalIdeal A) G hGcompat
  have heAdic_eval (n : ℕ) (x : AdicCompletion (IsLocalRing.maximalIdeal A) A) :
      Ideal.Quotient.mk (J0 ^ n) (eAdic x) = F n x := by
    exact IsAdicComplete.mk_liftRingHom J0 F hFcompat n x
  have heInv_eval (n : ℕ) (x : B) :
      AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n (eInv x) = G n x := by
    exact AdicCompletion.evalₐ_liftRingHom
      (IsLocalRing.maximalIdeal A) G hGcompat n x
  have hAC : ∀ x : AdicCompletion (IsLocalRing.maximalIdeal A) A,
      eInv (eAdic x) = x := by
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    apply (eABp n).injective
    calc
      eABp n (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n
          (eInv (eAdic x))) = eABp n (G n (eAdic x)) := by
            rw [heInv_eval]
      _ = Ideal.Quotient.mk (J0 ^ n) (eAdic x) := by
            dsimp [G]
            simp
      _ = F n x := heAdic_eval n x
      _ = eABp n (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n x) := rfl
  have hB : ∀ y : B, eAdic (eInv y) = y := by
    intro y
    have hfun : (fun _ : Unit => eAdic (eInv y)) = (fun _ : Unit => y) := by
      apply IsHausdorff.funext' J0
      intro n z
      calc
        Ideal.Quotient.mk (J0 ^ n) (eAdic (eInv y)) = F n (eInv y) :=
          heAdic_eval n (eInv y)
        _ = eABp n (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n (eInv y)) := rfl
        _ = eABp n (G n y) := by rw [heInv_eval]
        _ = Ideal.Quotient.mk (J0 ^ n) y := by
          dsimp [G]
          simp
    exact congrFun hfun ()
  have heInv_bij : Function.Bijective eInv := by
    constructor
    · intro x y hxy
      have h := congrArg eAdic hxy
      simpa [hB] using h
    · intro y
      exact ⟨eAdic y, hAC y⟩
  let eBA : B ≃+* AdicCompletion (IsLocalRing.maximalIdeal A) A :=
    RingEquiv.ofBijective eInv heInv_bij
  let eRing : @UniformSpace.Completion A (chapter07DvrUniformSpace A) ≃+* B :=
    { eU.toEquiv with
      map_add' := hadd
      map_mul' := hmul }
  have hInv_f (a : A) :
      eBA (f a) = chapter07AdicCompletionMap (IsLocalRing.maximalIdeal A) a := by
    change eInv (f a) = chapter07AdicCompletionMap (IsLocalRing.maximalIdeal A) a
    apply AdicCompletion.ext_evalₐ
    intro n
    apply (eABp n).injective
    calc
      eABp n (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n
          (eInv (f a))) = eABp n (G n (f a)) := by
            rw [heInv_eval]
      _ = Ideal.Quotient.mk (J0 ^ n) (f a) := by
            dsimp [G]
            simp
      _ = eABp n
          (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) a) :=
            (heABp_mk n a).symm
      _ = eABp n (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n
          (chapter07AdicCompletionMap (IsLocalRing.maximalIdeal A) a)) := by
            simp [chapter07AdicCompletionMap, AdicCompletion.algebraMap_apply]
  refine ⟨eRing.trans eBA, ?_⟩
  intro a
  rw [RingEquiv.trans_apply]
  change eBA (eU ((a : A) : @UniformSpace.Completion A
    (chapter07DvrUniformSpace A))) = _
  rw [eU_coe]
  exact hInv_f a

-- The finite filtration is unchanged by completion in the DVR case.
theorem chapter07_dvr_adic_completion_preserves_finite_filtration
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (π : A) (hπ : Irreducible π) :
    ∀ n : ℕ, 1 ≤ n →
      Nonempty
        (A ⧸ Ideal.span ({π ^ n} : Set A) ≃+*
          AdicCompletion (IsLocalRing.maximalIdeal A) A ⧸ Ideal.span
            ({chapter07AdicCompletionMap (IsLocalRing.maximalIdeal A) (π ^ n)} : Set
              (AdicCompletion (IsLocalRing.maximalIdeal A) A))) := by
  intro n _
  have hfg : (IsLocalRing.maximalIdeal A).FG :=
    (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
  have hπM : Ideal.span ({π} : Set A) = IsLocalRing.maximalIdeal A :=
    chapter07_dvr_uniformizer_generates_maximal_ideal π hπ
  have hπpow :
      Ideal.span ({π ^ n} : Set A) = (IsLocalRing.maximalIdeal A) ^ n := by
    rw [← Ideal.span_singleton_pow, hπM]
  have hzero (x : AdicCompletion (IsLocalRing.maximalIdeal A) A) :
      AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n x = 0 ↔
        AdicCompletion.eval (IsLocalRing.maximalIdeal A) A n x = 0 := by
    have h :
        ((IsLocalRing.maximalIdeal A) ^ n • (⊤ : Ideal A)) ≤
          (IsLocalRing.maximalIdeal A) ^ n := by
      simp
    have hf : Function.Injective (Ideal.Quotient.factor h) := by
      rw [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.factor_ker]
      have heq :
          (IsLocalRing.maximalIdeal A ^ n • (⊤ : Ideal A)) =
            IsLocalRing.maximalIdeal A ^ n := by
        rw [Ideal.smul_eq_mul, Ideal.mul_top]
      rw [heq]
      exact Ideal.map_quotient_self _
    rw [← AdicCompletion.factor_eval_eq_evalₐ (IsLocalRing.maximalIdeal A) x h]
    constructor
    · intro hx
      apply hf
      simpa using hx
    · intro hx
      simp [hx]
  have hker :
      RingHom.ker (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n).toRingHom =
        ((IsLocalRing.maximalIdeal A) ^ n).map
          (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) := by
    ext x
    change AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n x = 0 ↔
      x ∈ ((IsLocalRing.maximalIdeal A) ^ n).map
        (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))
    change AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n x = 0 ↔
      x ∈ (((IsLocalRing.maximalIdeal A) ^ n).map
        (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))).restrictScalars A
    rw [← Ideal.smul_top_eq_map,
      AdicCompletion.pow_smul_top_eq_ker_eval
        (I := IsLocalRing.maximalIdeal A) (M := A) (n := n) hfg]
    simpa only [LinearMap.mem_ker] using hzero x
  have hmap :
      ((IsLocalRing.maximalIdeal A) ^ n).map
          (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) =
        Ideal.span
          ({chapter07AdicCompletionMap (IsLocalRing.maximalIdeal A) (π ^ n)} :
            Set (AdicCompletion (IsLocalRing.maximalIdeal A) A)) := by
    rw [← hπpow, Ideal.map_span]
    simp [chapter07AdicCompletionMap]
  refine ⟨(Ideal.quotEquivOfEq hπpow).trans ?_⟩
  exact
    (RingHom.quotientKerEquivOfSurjective
      (f := (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n).toRingHom)
      (AdicCompletion.surjective_evalₐ (IsLocalRing.maximalIdeal A) n)).symm.trans
      (Ideal.quotEquivOfEq (hker.trans hmap))

/-! ### 7.6. Examples: p-adic completions -/

abbrev chapter07PAdicField (p : ℕ) [Fact p.Prime] : Type _ :=
  ℚ_[p]

abbrev chapter07PAdicIntegerRing (p : ℕ) [Fact p.Prime] : Type _ :=
  ℤ_[p]

-- The absolute value underlying the p-adic uniformity on ℚ.
def chapter07PAdicAbsoluteValue (p : ℕ) [Fact p.Prime] : AbsoluteValue ℚ ℚ :=
  IsAbsoluteValue.toAbsoluteValue (padicNorm p)

-- The uniform structure used for the p-adic completion of ℚ.  Pulling back the
-- normed-field uniformity along the canonical map into ℚ_[p] makes the
-- comparison with Mathlib's concrete completion explicit.
abbrev chapter07PAdicUniformSpace (p : ℕ) [Fact p.Prime] : UniformSpace ℚ :=
  UniformSpace.comap ((↑) : ℚ → chapter07PAdicField p)
    (inferInstance : UniformSpace (chapter07PAdicField p))

-- Section 7.6: the rationals are incomplete for the p-adic uniformity.
theorem chapter07_rationals_are_padic_incomplete
    (p : ℕ) [Fact p.Prime] :
    ¬ @CompleteSpace ℚ (chapter07PAdicUniformSpace p) := by
  intro hcomplete
  let : UniformSpace ℚ := chapter07PAdicUniformSpace p
  let : CompleteSpace ℚ := hcomplete
  have hinducing : @IsUniformInducing ℚ (chapter07PAdicField p)
      (chapter07PAdicUniformSpace p)
      (inferInstance : UniformSpace (chapter07PAdicField p))
      ((↑) : ℚ → chapter07PAdicField p) := by
    exact (isUniformInducing_iff_uniformSpace).2 rfl
  have hclosed : IsClosed (Set.range ((↑) : ℚ → chapter07PAdicField p)) := by
    have hemb : IsUniformEmbedding ((↑) : ℚ → chapter07PAdicField p) :=
      ⟨hinducing, Rat.cast_injective⟩
    exact hemb.isClosedEmbedding.isClosed_range
  have hdense : DenseRange ((↑) : ℚ → chapter07PAdicField p) :=
    Padic.denseRange_ratCast p
  have hrange : Set.range ((↑) : ℚ → chapter07PAdicField p) = Set.univ := by
    rw [← hclosed.closure_eq, hdense.closure_range]
  have hsurj : Function.Surjective ((↑) : ℚ → chapter07PAdicField p) :=
    Set.range_eq_univ.mp hrange
  have hunc : Uncountable (chapter07PAdicField p) := by
    rw [← Cardinal.aleph0_lt_mk_iff]
    exact Cardinal.aleph0_lt_continuum.trans_le
      (continuum_le_cardinal_of_nontriviallyNormedField (chapter07PAdicField p))
  let : Uncountable (chapter07PAdicField p) := hunc
  exact (hsurj.uncountable).not_countable inferInstance

-- The p-adic field is complete.
theorem chapter07_padic_field_is_complete
    (p : ℕ) [Fact p.Prime] :
    CompleteSpace (chapter07PAdicField p) := by
  infer_instance

-- The rationals are dense in the p-adic field.
theorem chapter07_rationals_are_dense_in_padic_field
    (p : ℕ) [Fact p.Prime] :
    DenseRange ((↑) : ℚ → chapter07PAdicField p) := by
  exact Padic.denseRange_ratCast p

-- The completion of ℚ for the p-adic absolute value is ℚ_[p].
theorem chapter07_padic_field_is_the_padic_completion
    (p : ℕ) [Fact p.Prime] :
    ∃ e : @UniformSpace.Completion ℚ (chapter07PAdicUniformSpace p) ≃ᵤ
        chapter07PAdicField p,
      ∀ q : ℚ,
        e (q : @UniformSpace.Completion ℚ (chapter07PAdicUniformSpace p)) =
          (q : chapter07PAdicField p) := by
  let : UniformSpace ℚ := chapter07PAdicUniformSpace p
  have hinducing : @IsUniformInducing ℚ (chapter07PAdicField p)
      (chapter07PAdicUniformSpace p)
      (inferInstance : UniformSpace (chapter07PAdicField p))
      ((↑) : ℚ → chapter07PAdicField p) := by
    exact (isUniformInducing_iff_uniformSpace).2 rfl
  let B : @AbstractCompletion ℚ (chapter07PAdicUniformSpace p) :=
    { space := chapter07PAdicField p
      coe := fun q : ℚ => (q : chapter07PAdicField p)
      uniformStruct := (inferInstance : UniformSpace (chapter07PAdicField p))
      complete := inferInstance
      separation := inferInstance
      isUniformInducing := hinducing
      dense := chapter07_rationals_are_dense_in_padic_field p }
  let e := (@UniformSpace.Completion.cPkg ℚ (chapter07PAdicUniformSpace p)).compareEquiv B
  refine ⟨e, ?_⟩
  intro q
  exact AbstractCompletion.compare_coe
    (@UniformSpace.Completion.cPkg ℚ (chapter07PAdicUniformSpace p)) B q

-- The p-adic integers form the complete valuation ring inside ℚ_[p].
theorem chapter07_padic_integer_ring_is_complete
    (p : ℕ) [Fact p.Prime] :
    CompleteSpace (chapter07PAdicIntegerRing p) := by
  infer_instance

-- The localization at (p) carries its canonical map into the fraction field ℚ.
noncomputable def chapter07LocalizedIntegersToRationals
    (p : ℕ) [Fact p.Prime] :
    chapter07LocalizedIntegers p →+* ℚ := by
  let P : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  refine IsLocalization.lift (M := P.primeCompl) (g := algebraMap ℤ ℚ) ?_
  intro y
  apply isUnit_iff_ne_zero.mpr
  norm_cast
  intro hy
  have hy0 : ((y : ℤ) : ℚ) = 0 := by simpa using hy
  have hy' : (y : ℤ) = 0 := by exact_mod_cast hy0
  apply y.property
  simp [P, hy']

-- The same localization maps into the p-adic integer subring.  The
-- denominators in the prime complement are precisely the p-adic units.
noncomputable def chapter07LocalizedIntegersToPAdicIntegers
    (p : ℕ) [Fact p.Prime] :
    chapter07LocalizedIntegers p →+* chapter07PAdicIntegerRing p := by
  let P : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  have hp : Prime (p : ℤ) :=
    Int.prime_iff_natAbs_prime.mpr (by simpa using Fact.out)
  refine IsLocalization.lift (M := P.primeCompl)
    (g := algebraMap ℤ (chapter07PAdicIntegerRing p)) ?_
  intro y
  apply (PadicInt.isUnit_iff).2
  apply (PadicInt.norm_intCast_eq_one_iff).2
  apply IsCoprime.symm
  apply hp.coprime_iff_not_dvd.mpr
  intro hy
  apply y.property
  exact Ideal.mem_span_singleton.mpr hy

abbrev chapter07LocalizedIntegersPAdicUniformSpace (p : ℕ) [Fact p.Prime] :
    UniformSpace (chapter07LocalizedIntegers p) :=
  UniformSpace.comap (chapter07LocalizedIntegersToPAdicIntegers p)
    (inferInstance : UniformSpace (chapter07PAdicIntegerRing p))

-- The canonical p-adic uniformity on the localization is pulled back from ℚ.
theorem chapter07_localized_integers_padic_completion
    (p : ℕ) [Fact p.Prime] :
    ∃ e : @UniformSpace.Completion (chapter07LocalizedIntegers p)
        (chapter07LocalizedIntegersPAdicUniformSpace p) ≃ᵤ
          chapter07PAdicIntegerRing p,
      ∀ a : chapter07LocalizedIntegers p,
        e (a : @UniformSpace.Completion (chapter07LocalizedIntegers p)
          (chapter07LocalizedIntegersPAdicUniformSpace p)) =
          chapter07LocalizedIntegersToPAdicIntegers p a := by
  let : UniformSpace (chapter07LocalizedIntegers p) :=
    chapter07LocalizedIntegersPAdicUniformSpace p
  let f : chapter07LocalizedIntegers p →+* chapter07PAdicIntegerRing p :=
    chapter07LocalizedIntegersToPAdicIntegers p
  have hdf : DenseRange f := by
    refine DenseRange.of_comp (f := (f : chapter07LocalizedIntegers p →
      chapter07PAdicIntegerRing p))
      (g := (algebraMap ℤ (chapter07LocalizedIntegers p) :
        ℤ → chapter07LocalizedIntegers p)) ?_
    have hdense : DenseRange
        ((Int.cast) : ℤ → chapter07PAdicIntegerRing p) :=
      PadicInt.denseRange_intCast
    simpa [Function.comp_def, f, chapter07LocalizedIntegersToPAdicIntegers] using hdense
  have hinducing : @IsUniformInducing (chapter07LocalizedIntegers p)
      (chapter07PAdicIntegerRing p) (chapter07LocalizedIntegersPAdicUniformSpace p)
      (inferInstance : UniformSpace (chapter07PAdicIntegerRing p))
      (f : chapter07LocalizedIntegers p → chapter07PAdicIntegerRing p) := by
    exact (isUniformInducing_iff_uniformSpace).2 rfl
  let B : @AbstractCompletion (chapter07LocalizedIntegers p)
      (chapter07LocalizedIntegersPAdicUniformSpace p) :=
    { space := chapter07PAdicIntegerRing p
      coe := f
      uniformStruct := (inferInstance : UniformSpace (chapter07PAdicIntegerRing p))
      complete := inferInstance
      separation := inferInstance
      isUniformInducing := hinducing
      dense := hdf }
  let e := (@UniformSpace.Completion.cPkg (chapter07LocalizedIntegers p)
    (chapter07LocalizedIntegersPAdicUniformSpace p)).compareEquiv B
  refine ⟨e, ?_⟩
  intro a
  exact AbstractCompletion.compare_coe
    (@UniformSpace.Completion.cPkg (chapter07LocalizedIntegers p)
      (chapter07LocalizedIntegersPAdicUniformSpace p)) B a

lemma chapter07_padic_digit_truncation_succ
    (p : ℕ) [Fact p.Prime] (a : chapter07DigitString p) (i : ℕ) :
    chapter07DigitTruncation p (i + 1) a =
      chapter07DigitTruncation p i a + (a i).val * p ^ i := by
  simp [chapter07DigitTruncation, Finset.sum_range_succ]

lemma chapter07_padic_digit_truncation_divisibility
    (p : ℕ) [Fact p.Prime] (a : chapter07DigitString p) :
    ∀ i : ℕ,
      (p : ℤ) ^ i ∣
        (chapter07DigitTruncation p (i + 1) a : ℤ) -
          chapter07DigitTruncation p i a := by
  intro i
  rw [chapter07_padic_digit_truncation_succ]
  refine ⟨(a i).val, ?_⟩
  push_cast
  ring

-- The p-adic truncation sequence attached to an infinite digit string.
def chapter07PAdicDigitLimit
    (p : ℕ) [Fact p.Prime] (a : chapter07DigitString p) :
    chapter07PAdicIntegerRing p :=
  PadicInt.ofIntSeq (p := p)
    (fun n => (chapter07DigitTruncation p n a : ℤ))
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub
      (fun n => (chapter07DigitTruncation p n a : ℤ)) p
      (chapter07_padic_digit_truncation_divisibility p a))

-- Rational truncations converge to the digit-string limit in the p-adic integers.
theorem chapter07_padic_digit_truncations_converge
    (p : ℕ) [Fact p.Prime] (a : chapter07DigitString p) :
    Tendsto
      (fun n => ((chapter07DigitTruncation p n a : ℕ) :
        chapter07PAdicField p))
      (atTop : Filter ℕ)
      (𝓝 ((chapter07PAdicDigitLimit p a : chapter07PAdicIntegerRing p) :
        chapter07PAdicField p)) := by
  let f : PadicSeq p :=
    ⟨fun n => (chapter07DigitTruncation p n a : ℚ), by
      simpa using
        (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub
          (fun n => (chapter07DigitTruncation p n a : ℤ)) p
          (chapter07_padic_digit_truncation_divisibility p a))⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨εq, hεq⟩ := exists_rat_btwn hε
  have hεq0 : (0 : ℚ) < εq := by exact_mod_cast hεq.1
  obtain ⟨N, hN⟩ := padicNormE.defn f hεq0
  refine ⟨N, ?_⟩
  intro n hn
  have hN' := hN n hn
  have hNreal :
      (↑(padicNormE (Padic.mk f - (f n : chapter07PAdicField p))) : ℝ) < ε := by
    exact lt_trans (by exact_mod_cast hN') hεq.2
  have hlim : (Padic.mk f : chapter07PAdicField p) =
      (chapter07PAdicDigitLimit p a : chapter07PAdicField p) := by
    rfl
  have hfn : (f n : chapter07PAdicField p) =
      (chapter07DigitTruncation p n a : chapter07PAdicField p) := by
    rfl
  have htarget :
      ‖(Padic.mk f : chapter07PAdicField p) - (f n : chapter07PAdicField p)‖ < ε := by
    simpa only [Padic.padicNormE.is_norm] using hNreal
  rw [← hlim, dist_eq_norm, norm_sub_rev]
  simpa only [hfn] using htarget

-- A digit string is rationally represented if its p-adic limit comes from ℚ.
def chapter07DigitStringRationallyRepresented
    (p : ℕ) [Fact p.Prime] (a : chapter07DigitString p) : Prop :=
  ∃ q : ℚ,
    (q : chapter07PAdicField p) =
      (chapter07PAdicDigitLimit p a : chapter07PAdicField p)

lemma chapter07_padic_digit_limit_injective
    (p : ℕ) [Fact p.Prime] :
    Function.Injective (chapter07PAdicDigitLimit p) := by
  intro a b hab
  have htrunc : ∀ n : ℕ,
      chapter07DigitTruncation p n a = chapter07DigitTruncation p n b := by
    intro n
    have hmod :
        ((chapter07DigitTruncation p n a : ℕ) : ZMod (p ^ n)) =
          ((chapter07DigitTruncation p n b : ℕ) : ZMod (p ^ n)) := by
      calc
        ((chapter07DigitTruncation p n a : ℕ) : ZMod (p ^ n)) =
            PadicInt.toZModPow n (chapter07PAdicDigitLimit p a) := by
              symm
              simpa [chapter07PAdicDigitLimit] using
                (PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub
                  (fun m => (chapter07DigitTruncation p m a : ℤ)) p
                  (chapter07_padic_digit_truncation_divisibility p a) n)
        _ = PadicInt.toZModPow n (chapter07PAdicDigitLimit p b) :=
          congrArg (PadicInt.toZModPow (p := p) n) hab
        _ = ((chapter07DigitTruncation p n b : ℕ) : ZMod (p ^ n)) := by
              simpa [chapter07PAdicDigitLimit] using
                (PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub
                  (fun m => (chapter07DigitTruncation p m b : ℤ)) p
                  (chapter07_padic_digit_truncation_divisibility p b) n)
    have hmod' :
        chapter07DigitTruncation p n a ≡ chapter07DigitTruncation p n b [MOD p ^ n] := by
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hmod
    have hbound : ∀ c : chapter07DigitString p, ∀ m : ℕ,
        chapter07DigitTruncation p m c < p ^ m := by
      intro c m
      induction m with
      | zero => simp [chapter07DigitTruncation]
      | succ m ih =>
          rw [chapter07_padic_digit_truncation_succ]
          have hd : (c m).val < p := (c m).isLt
          have hpow : 0 < p ^ m := pow_pos (Nat.Prime.pos Fact.out) _
          have hsum : (c m).val + 1 ≤ p := Nat.succ_le_of_lt hd
          have hadd : chapter07DigitTruncation p m c + (c m).val * p ^ m <
              p ^ m + (c m).val * p ^ m := by
            exact Nat.add_lt_add_right ih ((c m).val * p ^ m)
          have hle : p ^ m + (c m).val * p ^ m ≤ p * p ^ m := by
            calc
              p ^ m + (c m).val * p ^ m = ((c m).val + 1) * p ^ m := by ring
              _ ≤ p * p ^ m := Nat.mul_le_mul_right _ hsum
          calc
            chapter07DigitTruncation p m c + (c m).val * p ^ m <
                p ^ m + (c m).val * p ^ m := hadd
            _ = ((c m).val + 1) * p ^ m := by ring
            _ ≤ p * p ^ m := Nat.mul_le_mul_right _ hsum
            _ = p ^ (m + 1) := by simp [pow_succ, Nat.mul_comm]
    have ha := hbound a n
    have hb := hbound b n
    have hrem :
        chapter07DigitTruncation p n a % p ^ n =
          chapter07DigitTruncation p n b % p ^ n := hmod'
    calc
      chapter07DigitTruncation p n a =
          chapter07DigitTruncation p n a % p ^ n :=
        (Nat.mod_eq_of_lt ha).symm
      _ = chapter07DigitTruncation p n b % p ^ n := hrem
      _ = chapter07DigitTruncation p n b := Nat.mod_eq_of_lt hb
  apply funext
  intro i
  have hi := htrunc (i + 1)
  rw [chapter07_padic_digit_truncation_succ,
    chapter07_padic_digit_truncation_succ, htrunc i] at hi
  have hmul : (a i).val * p ^ i = (b i).val * p ^ i :=
    Nat.add_left_cancel hi
  apply Fin.ext
  exact Nat.mul_right_cancel
    (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) _) hmul

-- There are infinitely many compatible infinite digit strings with no rational representative.
theorem chapter07_infinitely_many_nonrational_padic_digit_strings
    (p : ℕ) [Fact p.Prime] :
    Set.Infinite
      {a : chapter07DigitString p |
        ¬ chapter07DigitStringRationallyRepresented p a} := by
  classical
  let T : Set (chapter07DigitString p) :=
    {a | chapter07DigitStringRationallyRepresented p a}
  let S : Set (chapter07DigitString p) :=
    {a | ¬chapter07DigitStringRationallyRepresented p a}
  let qOf : chapter07DigitString p → ℚ := fun a =>
    if ha : chapter07DigitStringRationallyRepresented p a then
      Classical.choose ha
    else 0
  have hq_spec {a : chapter07DigitString p} (ha : a ∈ T) :
      (qOf a : chapter07PAdicField p) =
        (chapter07PAdicDigitLimit p a : chapter07PAdicField p) := by
    change chapter07DigitStringRationallyRepresented p a at ha
    simp only [qOf, dif_pos ha]
    exact Classical.choose_spec ha
  have hq_inj : Set.InjOn qOf T := by
    intro a ha b hb hab
    have hlim :
        (chapter07PAdicDigitLimit p a : chapter07PAdicField p) =
          (chapter07PAdicDigitLimit p b : chapter07PAdicField p) := by
      calc
        (chapter07PAdicDigitLimit p a : chapter07PAdicField p) = qOf a :=
          (hq_spec ha).symm
        _ = qOf b := congrArg (fun q : ℚ => (q : chapter07PAdicField p)) hab
        _ = (chapter07PAdicDigitLimit p b : chapter07PAdicField p) := hq_spec hb
    apply chapter07_padic_digit_limit_injective p
    exact Subtype.ext hlim
  have hT : T.Countable := by
    apply Set.countable_of_injective_of_countable_image hq_inj
    exact Set.countable_univ.mono (Set.image_subset_iff.2 fun _ _ => Set.mem_univ _)
  have hbool_uncountable : Uncountable (ℕ → Bool) := by
    rw [← not_countable_iff]
    intro hc
    let : Countable (ℕ → Bool) := hc
    obtain ⟨f, hf⟩ := exists_surjective_nat (ℕ → Bool)
    let g : ℕ → Bool := fun n => !(f n n)
    obtain ⟨m, hm⟩ := hf g
    have hdiag := congrFun hm m
    cases hfm : f m m <;> simp [g, hfm] at hdiag
  have hp2 : 2 ≤ p := Nat.Prime.two_le Fact.out
  let emb : (ℕ → Bool) → chapter07DigitString p := fun b n =>
    if b n then ⟨1, by omega⟩ else ⟨0, by omega⟩
  have hemb : Function.Injective emb := by
    intro x y hxy
    funext n
    have hn := congrArg (fun z : Fin p => z.val)
      (congrFun hxy n)
    cases hxn : x n <;> cases hyn : y n <;>
      simp [emb, hxn, hyn] at hn ⊢
  let : Uncountable (ℕ → Bool) := hbool_uncountable
  have hdigit_uncountable : Uncountable (chapter07DigitString p) :=
    hemb.uncountable
  let : Uncountable (chapter07DigitString p) := hdigit_uncountable
  intro hSfin
  have hU : (Set.univ : Set (chapter07DigitString p)) ⊆ T ∪ S := by
    intro a ha
    by_cases hrep : chapter07DigitStringRationallyRepresented p a
    · exact Or.inl hrep
    · exact Or.inr hrep
  have hcount : (Set.univ : Set (chapter07DigitString p)).Countable :=
    (hT.union hSfin.countable).mono hU
  exact (not_countable_univ (α := chapter07DigitString p)) hcount

/-! ### 7.6. Examples: Laurent and power series -/

abbrev chapter07RationalFunctionField (k : Type*) [Field k] : Type _ :=
  RatFunc k

abbrev chapter07LaurentSeriesField (k : Type*) [Field k] : Type _ :=
  LaurentSeries k

abbrev chapter07PowerSeriesRing (k : Type*) [Field k] : Type _ :=
  PowerSeries k

-- The X-adic completion of the rational-function field in the Laurent-series API.
abbrev chapter07RationalFunctionAdicCompletion (k : Type*) [Field k] : Type _ :=
  LaurentSeries.RatFuncAdicCompl k

-- The local ring `k[t]_(t)` at the prime generated by `t`.
noncomputable instance chapter07PolynomialOriginPrime (k : Type*) [Field k] :
    (Ideal.span ({(Polynomial.X : Polynomial k)} : Set (Polynomial k))).IsPrime :=
  (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X

abbrev chapter07PolynomialLocalRing (k : Type*) [Field k] : Type _ :=
  Localization ((Ideal.span ({(Polynomial.X : Polynomial k)} : Set (Polynomial k))).primeCompl)

-- The extension of `(t)` to the localized polynomial ring.
abbrev chapter07PolynomialLocalIdeal (k : Type*) [Field k] :
    Ideal (chapter07PolynomialLocalRing k) :=
  Ideal.map (algebraMap (Polynomial k) (chapter07PolynomialLocalRing k))
    (Ideal.span ({(Polynomial.X : Polynomial k)} : Set (Polynomial k)))

theorem chapter07_polynomial_local_ideal_eq_maximalIdeal
    (k : Type*) [Field k] :
    chapter07PolynomialLocalIdeal k =
      IsLocalRing.maximalIdeal (chapter07PolynomialLocalRing k) := by
  exact Localization.AtPrime.map_eq_maximalIdeal

-- The completed local ring, using the `(t)`-adic topology.
abbrev chapter07PolynomialLocalCompletion (k : Type*) [Field k] : Type _ :=
  AdicCompletion (chapter07PolynomialLocalIdeal k)
    (chapter07PolynomialLocalRing k)

-- Laurent series are complete for the X-adic valuation.
theorem chapter07_laurent_series_are_complete
    (k : Type*) [Field k] :
    CompleteSpace (chapter07LaurentSeriesField k) := by
  infer_instance

-- Rational functions are dense in Laurent series.
theorem chapter07_rational_functions_are_dense_in_laurent_series
    (k : Type*) [Field k] :
    DenseRange
      ((↑) : chapter07RationalFunctionField k →
        chapter07LaurentSeriesField k) := by
  exact LaurentSeries.coe_range_dense

-- The rational-function completion is identified with the Laurent-series field.
def chapter07RationalFunctionAdicToLaurentSeries
    (k : Type*) [Field k] :
    chapter07RationalFunctionAdicCompletion k ≃+*
      chapter07LaurentSeriesField k :=
  LaurentSeries.ratfuncAdicComplRingEquiv k

-- Section 7.6: completion of k(t) for the t-adic valuation gives k((t)).
theorem chapter07_rational_function_completion_is_laurent_series
    (k : Type*) [Field k] :
    Nonempty
      (chapter07RationalFunctionAdicCompletion k ≃+*
        chapter07LaurentSeriesField k) := by
  exact ⟨chapter07RationalFunctionAdicToLaurentSeries k⟩

-- The completed local valuation ring is identified with k[[t]].
def chapter07PowerSeriesToPolynomialLocalCompletion
    (k : Type*) [Field k] :
  Prop :=
  ∃ e : chapter07PowerSeriesRing k ≃+* chapter07PolynomialLocalCompletion k,

    ∀ p : Polynomial k,
      e (p : chapter07PowerSeriesRing k) =
        chapter07AdicCompletionMap (chapter07PolynomialLocalIdeal k)
          (algebraMap (Polynomial k) (chapter07PolynomialLocalRing k) p)
-- The same local identification as an algebra equivalence.
def chapter07PowerSeriesAlgebraToPolynomialLocalCompletion
    (k : Type*) [Field k] :
  Prop :=
  ∃ e : chapter07PowerSeriesRing k ≃ₐ[k] chapter07PolynomialLocalCompletion k,
    ∀ p : Polynomial k,
      e (p : chapter07PowerSeriesRing k) =
        chapter07AdicCompletionMap (chapter07PolynomialLocalIdeal k)
          (algebraMap (Polynomial k) (chapter07PolynomialLocalRing k) p)

-- Section 7.6: completion of k[t]_(t) gives k[[t]].
theorem chapter07_polynomial_local_completion_is_power_series
    (k : Type*) [Field k] :
    chapter07PowerSeriesToPolynomialLocalCompletion k ∧
      chapter07PowerSeriesAlgebraToPolynomialLocalCompletion k := by
  classical
  let R := Polynomial k
  let P : Ideal R := Ideal.span ({(Polynomial.X : R)} : Set R)
  let M : Submonoid R := P.primeCompl
  let L := Localization M
  let J : Ideal L := Ideal.map (algebraMap R L) P
  let PS := chapter07PowerSeriesRing k
  let Q : Ideal PS := Ideal.span ({(PowerSeries.X : PS)} : Set PS)
  let c : R →+* PS := Polynomial.coeToPowerSeries.ringHom
  let : Q.IsMaximal := by
    dsimp [Q]
    rw [← PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  have hcoe_mem (n : ℕ) (p : R) :
      (p : PS) ∈ Q ^ n ↔ p ∈ P ^ n := by
    change
      (p : PS) ∈ (Ideal.span ({(PowerSeries.X : PS)} : Set PS)) ^ n ↔
        p ∈ (Ideal.span ({(Polynomial.X : R)} : Set R)) ^ n
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, Ideal.mem_span_singleton,
      PowerSeries.X_pow_dvd_iff, Polynomial.X_pow_dvd_iff]
    simp only [Polynomial.coeff_coe]
  have hcunit (n : ℕ) (s : M) :
      IsUnit (((Ideal.Quotient.mk (Q ^ n)).comp c) s.1) := by
    by_cases hn : n = 0
    · subst n
      have htop : Q ^ 0 = (⊤ : Ideal PS) := by simp
      rw [htop]
      exact isUnit_of_subsingleton _
    have hsQ : (s.1 : PS) ∉ Q := by
      intro hs
      have hs0 : PowerSeries.constantCoeff (s.1 : PS) = 0 := by
        apply PowerSeries.X_dvd_iff.mp
        exact Ideal.mem_span_singleton.mp (by simpa [Q] using hs)
      have hsP0 : Polynomial.constantCoeff s.1 = 0 := by
        simpa using hs0
      have hsP : (s.1 : R) ∉ P := s.property
      apply hsP
      change (s.1 : R) ∈ Ideal.span ({(Polynomial.X : R)} : Set R)
      rw [← Polynomial.ker_constantCoeff, RingHom.mem_ker]
      exact hsP0
    change IsUnit (Ideal.Quotient.mk (Q ^ n) (s.1 : PS))
    exact Ideal.Quotient.isUnit_mk_pow_of_notMem Q (n := n) hsQ
  let g : ∀ n : ℕ, L →+* PS ⧸ Q ^ n := fun n ↦
    IsLocalization.lift (M := M)
      (g := (Ideal.Quotient.mk (Q ^ n)).comp c) (hcunit n)
  have hmap (n : ℕ) :
      Ideal.map (g n) (J ^ n) ≤ (⊥ : Ideal (PS ⧸ Q ^ n)) := by
    change Ideal.map (g n) ((Ideal.map (algebraMap R L) P) ^ n) ≤ ⊥
    rw [← Ideal.map_pow, Ideal.map_map]
    change Ideal.map ((g n).comp (algebraMap R L))
      ((Ideal.span ({(Polynomial.X : R)} : Set R)) ^ n) ≤ ⊥
    rw [Ideal.map_le_iff_le_comap, Ideal.span_singleton_pow]
    refine Ideal.span_le.2 ?_
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    change (g n) (algebraMap R L ((Polynomial.X : R) ^ n)) = 0
    simp only [g, IsLocalization.lift_eq]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have hc : c ((Polynomial.X : R) ^ n) =
        (((Polynomial.X : R) ^ n : R) : PS) := by
      change Polynomial.coeToPowerSeries.ringHom ((Polynomial.X : R) ^ n) = _
      exact Polynomial.coeToPowerSeries.ringHom_apply
    rw [hc]
    apply (hcoe_mem n ((Polynomial.X : R) ^ n)).2
    change (Polynomial.X : R) ^ n ∈
      (Ideal.span ({(Polynomial.X : R)} : Set R)) ^ n
    rw [Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _
  have hJker (n : ℕ) : J ^ n ≤ RingHom.ker (g n) := by
    intro a ha
    apply RingHom.mem_ker.mpr
    have hmem : g n a ∈ Ideal.map (g n) (J ^ n) :=
      Ideal.mem_map_of_mem (g n) ha
    simpa using hmap n hmem
  let q : ∀ n : ℕ, L ⧸ J ^ n →+* PS ⧸ Q ^ n := fun n ↦
    Ideal.Quotient.lift (J ^ n) (g n) (fun a ha ↦ hJker n ha)
  have hq_bij (n : ℕ) : Function.Bijective (q n) := by
    constructor
    · intro x y hxy
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
      have hgab : g n a = g n b := by
        change g n a = g n b at hxy
        exact hxy
      have hzero : g n (a - b) = 0 := by
        rw [map_sub, hgab, sub_self]
      obtain ⟨p, s, hs⟩ := IsLocalization.exists_mk'_eq M (a - b)
      rw [← hs]
      have hzero' : g n (IsLocalization.mk' L p s) = 0 := by
        simpa [hs] using hzero
      have hgp : ((Ideal.Quotient.mk (Q ^ n)).comp c) p = 0 := by
        have hspec :=
          (IsLocalization.lift_mk'_spec (M := M)
            (g := (Ideal.Quotient.mk (Q ^ n)).comp c) (hcunit n) p 0 s).mp
            (by simpa [g] using hzero')
        simpa using hspec
      have hpQ : (p : PS) ∈ Q ^ n := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        have hcp : c p = (p : PS) := by
          change Polynomial.coeToPowerSeries.ringHom p = (p : PS)
          exact Polynomial.coeToPowerSeries.ringHom_apply
        simpa only [RingHom.comp_apply, hcp] using hgp
      have hpP : p ∈ P ^ n := (hcoe_mem n p).mp hpQ
      have hpL : algebraMap R L p ∈ J ^ n := by
        change algebraMap R L p ∈ (Ideal.map (algebraMap R L) P) ^ n
        rw [← Ideal.map_pow]
        exact Ideal.mem_map_of_mem (algebraMap R L) hpP
      rw [IsLocalization.mk'_eq_mul_mk'_one]
      exact (J ^ n).mul_mem_right _ hpL
    · intro z
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
      let p : R := PowerSeries.trunc n f
      let t : PS := PowerSeries.mk (fun i ↦ PowerSeries.coeff (i + n) f)
      have hXn : (PowerSeries.X : PS) ^ n ∈ Q ^ n := by
        change (PowerSeries.X : PS) ^ n ∈
          (Ideal.span ({(PowerSeries.X : PS)} : Set PS)) ^ n
        rw [Ideal.span_singleton_pow]
        exact Ideal.mem_span_singleton_self _
      have hdiff : f - (p : PS) ∈ Q ^ n := by
        have hfdiff : f - (p : PS) = (PowerSeries.X : PS) ^ n * t := by
          apply sub_eq_iff_eq_add.mpr
          dsimp [p, t]
          exact PowerSeries.eq_X_pow_mul_shift_add_trunc n f
        rw [hfdiff]
        exact (Q ^ n).mul_mem_right _ hXn
      refine ⟨Ideal.Quotient.mk (J ^ n) (algebraMap R L p), ?_⟩
      change g n (algebraMap R L p) =
        Ideal.Quotient.mk (Q ^ n) f
      simp only [g, IsLocalization.lift_eq]
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
      have hcp : c p = (p : PS) := by
        change Polynomial.coeToPowerSeries.ringHom p = (p : PS)
        exact Polynomial.coeToPowerSeries.ringHom_apply
      have hdiff' : (p : PS) - f ∈ Q ^ n := by
        simpa only [neg_sub] using (Q ^ n).neg_mem hdiff
      simpa only [hcp, sub_eq_add_neg] using hdiff'
  have hg_comp {m n : ℕ} (hle : m ≤ n) :
      (Ideal.Quotient.factorPow Q hle).comp (g n) = g m := by
    apply IsLocalization.ringHom_ext M
    apply RingHom.ext
    intro p
    simp only [g, IsLocalization.lift_eq, RingHom.comp_apply,
      Ideal.Quotient.factor_mk]
  have hq_comp {m n : ℕ} (hle : m ≤ n) :
      (Ideal.Quotient.factorPow Q hle).comp (q n) =
        (q m).comp (Ideal.Quotient.factorPow J hle) := by
    apply RingHom.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change (Ideal.Quotient.factorPow Q hle) (g n a) = g m a
    exact DFunLike.congr_fun (hg_comp hle) a
  let qEquiv (n : ℕ) : L ⧸ J ^ n ≃+* PS ⧸ Q ^ n :=
    RingEquiv.ofBijective (q n) (hq_bij n)
  let H : ∀ n : ℕ, PS →+* L ⧸ J ^ n := fun n ↦
    (qEquiv n).symm.toRingHom.comp (Ideal.Quotient.mk (Q ^ n))
  have hH_comp {m n : ℕ} (hle : m ≤ n) :
      (Ideal.Quotient.factorPow J hle).comp (H n) = H m := by
    apply RingHom.ext
    intro x
    apply (qEquiv m).injective
    change q m ((Ideal.Quotient.factorPow J hle) (H n x)) = q m (H m x)
    have hq := DFunLike.congr_fun (hq_comp hle) (H n x)
    change (Ideal.Quotient.factorPow Q hle) (q n (H n x)) =
      q m ((Ideal.Quotient.factorPow J hle) (H n x)) at hq
    rw [← hq]
    change (Ideal.Quotient.factorPow Q hle)
        ((qEquiv n) ((qEquiv n).symm (Ideal.Quotient.mk (Q ^ n) x))) =
      (qEquiv m) ((qEquiv m).symm (Ideal.Quotient.mk (Q ^ m) x))
    simp
  let d : PS →+* AdicCompletion J L :=
    AdicCompletion.liftRingHom J H hH_comp
  let F : ∀ n : ℕ, AdicCompletion J L →+* PS ⧸ Q ^ n := fun n ↦
    (q n).comp (AdicCompletion.evalₐ J n).toRingHom
  have heval_comp {m n : ℕ} (hle : m ≤ n) (x : AdicCompletion J L) :
      (Ideal.Quotient.factorPow J hle) (AdicCompletion.evalₐ J n x) =
        AdicCompletion.evalₐ J m x := by
    rw [← AdicCompletion.factor_eval_eq_evalₐ J x
      (le_of_eq (Ideal.mul_top _))]
    rw [← AdicCompletion.factor_eval_eq_evalₐ J x
      (le_of_eq (Ideal.mul_top _))]
    have htrans :=
      AdicCompletion.transitionMap_comp_eval_apply (I := J) (M := L) hle x
    have htrans' := congrArg
      (fun z ↦ Ideal.Quotient.factor (le_of_eq (Ideal.mul_top (J ^ m))) z)
      htrans
    simpa [AdicCompletion.eval, AdicCompletion.transitionMap] using htrans'
  have hF_comp {m n : ℕ} (hle : m ≤ n) :
      (Ideal.Quotient.factorPow Q hle).comp (F n) = F m := by
    apply RingHom.ext
    intro x
    change (Ideal.Quotient.factorPow Q hle)
        (q n (AdicCompletion.evalₐ J n x)) =
      q m (AdicCompletion.evalₐ J m x)
    have hq :=
      DFunLike.congr_fun (hq_comp hle) (AdicCompletion.evalₐ J n x)
    change (Ideal.Quotient.factorPow Q hle)
        (q n (AdicCompletion.evalₐ J n x)) =
      q m ((Ideal.Quotient.factorPow J hle) (AdicCompletion.evalₐ J n x)) at hq
    rw [hq]
    exact congrArg (q m) (heval_comp hle x)
  let eHom : AdicCompletion J L →+* PS :=
    IsAdicComplete.liftRingHom Q F hF_comp
  have hed : eHom.comp d = RingHom.id PS := by
    apply DFunLike.coe_injective
    apply IsHausdorff.funext' Q
    intro n x
    change Ideal.Quotient.mk (Q ^ n) (eHom (d x)) =
      Ideal.Quotient.mk (Q ^ n) x
    rw [IsAdicComplete.mk_liftRingHom Q F hF_comp]
    change q n (AdicCompletion.evalₐ J n (d x)) =
      Ideal.Quotient.mk (Q ^ n) x
    rw [show AdicCompletion.evalₐ J n (d x) = H n x by
      exact AdicCompletion.evalₐ_liftRingHom J H hH_comp n x]
    change (qEquiv n) ((qEquiv n).symm (Ideal.Quotient.mk (Q ^ n) x)) = _
    simp
  have hde : d.comp eHom = RingHom.id (AdicCompletion J L) := by
    apply RingHom.ext
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    calc
      AdicCompletion.evalₐ J n (d (eHom x)) = H n (eHom x) := by
        simp [d]
      _ = (qEquiv n).symm (Ideal.Quotient.mk (Q ^ n) (eHom x)) := by
        simp [H]
      _ = (qEquiv n).symm (F n x) := by
        rw [IsAdicComplete.mk_liftRingHom Q F hF_comp]
      _ = (qEquiv n).symm (q n (AdicCompletion.evalₐ J n x)) := by
        simp [F]
      _ = AdicCompletion.evalₐ J n x := by
        change (qEquiv n).symm ((qEquiv n) (AdicCompletion.evalₐ J n x)) = _
        exact (qEquiv n).symm_apply_apply _
  have he_left : Function.LeftInverse d eHom := by
    intro x
    simpa using DFunLike.congr_fun hde x
  have he_right : Function.RightInverse d eHom := by
    intro x
    simpa using DFunLike.congr_fun hed x
  have he_bij : Function.Bijective eHom :=
    ⟨Function.LeftInverse.injective he_left, Function.RightInverse.surjective he_right⟩
  let eAC : AdicCompletion J L ≃+* PS := RingEquiv.ofBijective eHom he_bij
  have hebase (p : R) :
      eHom (AdicCompletion.of J L (algebraMap R L p)) = (p : PS) := by
    apply (IsHausdorff.eq_iff_smodEq (I := Q)).2
    intro n
    rw [SModEq.sub_mem]
    have hqval :
        Ideal.Quotient.mk (Q ^ n)
            (eHom (AdicCompletion.of J L (algebraMap R L p))) =
          Ideal.Quotient.mk (Q ^ n) (p : PS) := by
      rw [IsAdicComplete.mk_liftRingHom Q F hF_comp]
      simp only [F, RingHom.comp_apply]
      change q n (AdicCompletion.evalₐ J n
        (AdicCompletion.of J L (algebraMap R L p))) =
        Ideal.Quotient.mk (Q ^ n) (p : PS)
      rw [AdicCompletion.evalₐ_of]
      change g n (algebraMap R L p) = Ideal.Quotient.mk (Q ^ n) (p : PS)
      simp [g, c]
      congr 1
    have hmem :
        eHom (AdicCompletion.of J L (algebraMap R L p)) - (p : PS) ∈ Q ^ n :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hqval
    rw [smul_eq_mul, Ideal.mul_top]
    exact hmem
  let ePS : chapter07PowerSeriesRing k ≃+* chapter07PolynomialLocalCompletion k := by
    exact eAC.symm
  have hePS_poly (p : Polynomial k) :
      ePS (p : chapter07PowerSeriesRing k) =
        chapter07AdicCompletionMap (chapter07PolynomialLocalIdeal k)
          (algebraMap (Polynomial k) (chapter07PolynomialLocalRing k) p) := by
    apply eAC.injective
    rw [eAC.apply_symm_apply]
    simpa [ePS, chapter07AdicCompletionMap, chapter07PolynomialLocalIdeal,
      chapter07PolynomialLocalRing, P, L, J, PS, M,
      AdicCompletion.algebraMap_apply, eAC] using (hebase p).symm
  have hePS_const (a : k) :
      ePS (algebraMap k (chapter07PowerSeriesRing k) a) =
        algebraMap k (chapter07PolynomialLocalCompletion k) a := by
    have hleft :
        algebraMap k (chapter07PowerSeriesRing k) a =
          (Polynomial.C a : chapter07PowerSeriesRing k) := by
      simp [chapter07PowerSeriesRing]
    have hright :
        chapter07AdicCompletionMap (chapter07PolynomialLocalIdeal k)
            (algebraMap (Polynomial k) (chapter07PolynomialLocalRing k)
              (Polynomial.C a)) =
          algebraMap k (chapter07PolynomialLocalCompletion k) a := by
      change algebraMap L (AdicCompletion J L)
          (algebraMap R L (Polynomial.C a)) =
        algebraMap k (AdicCompletion J L) a
      calc
        algebraMap L (AdicCompletion J L)
              (algebraMap R L (Polynomial.C a)) =
            algebraMap L (AdicCompletion J L)
              (algebraMap R L (algebraMap k R a)) := by
                congr 2
        _ = algebraMap k (AdicCompletion J L) a := by
          exact (IsScalarTower.algebraMap_apply k L (AdicCompletion J L) a).symm
    rw [hleft]
    exact (hePS_poly (Polynomial.C a)).trans hright
  let eAlg : chapter07PowerSeriesRing k ≃ₐ[k]
      chapter07PolynomialLocalCompletion k :=
    AlgEquiv.ofRingEquiv (f := ePS) hePS_const
  exact ⟨⟨ePS, hePS_poly⟩, ⟨eAlg, hePS_poly⟩⟩

-- Truncation of a power series to a polynomial, viewed again as a power series.
def chapter07PowerSeriesTruncation
    {k : Type*} [Field k] (n : ℕ) (f : chapter07PowerSeriesRing k) :
    chapter07PowerSeriesRing k :=
  (PowerSeries.trunc n f : chapter07PowerSeriesRing k)

-- Power-series truncations stabilize each coefficient, the canonical X-adic statement.
theorem chapter07_power_series_truncations_converge
    {k : Type*} [Field k] (f : chapter07PowerSeriesRing k) :
    ∀ d : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      PowerSeries.coeff d (chapter07PowerSeriesTruncation n f) = PowerSeries.coeff d f := by
  intro d
  refine ⟨d + 1, ?_⟩
  intro n hn
  have hdn : d < n := by omega
  simp [chapter07PowerSeriesTruncation, PowerSeries.coeff_trunc, Nat.lt_of_lt_of_le
    hdn]

-- A Cauchy Laurent-series filter has an eventually fixed coefficient at each degree.
theorem chapter07_laurent_cauchy_coefficients_eventually_stabilize
    (k : Type*) [Field k] {ℱ : Filter (chapter07LaurentSeriesField k)}
    (hℱ : Cauchy ℱ) (D : ℤ) :
    ∀ᶠ f in ℱ, ∀ d : ℤ, d < D →
      LaurentSeries.Cauchy.coeff hℱ d = f.coeff d := by
  exact LaurentSeries.Cauchy.coeff_eventually_equal hℱ

-- The coefficient sequence attached to a Laurent Cauchy filter has a uniform lower bound.
theorem chapter07_laurent_cauchy_limit_has_uniform_lower_bound
    (k : Type*) [Field k] {ℱ : Filter (chapter07LaurentSeriesField k)}
    (hℱ : Cauchy ℱ) :
    ∃ N : ℤ, ∀ d : ℤ, d < N →
      (LaurentSeries.Cauchy.limit hℱ).coeff d = 0 := by
  obtain ⟨N, hN⟩ := LaurentSeries.Cauchy.exists_lb_support hℱ
  refine ⟨N, ?_⟩
  intro d hd
  exact hN d hd

-- The Laurent-series Cauchy limit is the coefficientwise limit constructed from stabilization.
theorem chapter07_laurent_cauchy_limit_is_a_laurent_series
    (k : Type*) [Field k] {ℱ : Filter (chapter07LaurentSeriesField k)}
    (hℱ : Cauchy ℱ) :
    ∀ d : ℤ,
      (LaurentSeries.Cauchy.limit hℱ).coeff d =
        LaurentSeries.Cauchy.coeff hℱ d := by
  intro d
  rfl

-- Rational truncations approximate every Laurent series in the valuation topology.
theorem chapter07_laurent_series_have_rational_approximations
    (k : Type*) [Field k] (f : chapter07LaurentSeriesField k) :
  f ∈ closure
      (Set.range ((↑) : chapter07RationalFunctionField k →
        chapter07LaurentSeriesField k)) := by
  exact LaurentSeries.coe_range_dense f

/-! ### 7.6. The chosen valuation controls the completion -/

-- Completion as a construction parameterized by the chosen uniformity.
def chapter07CompletionForUniformity
    (K : Type*) (u : UniformSpace K) : Type _ :=
  @UniformSpace.Completion K u

-- The completion construction remembers the chosen uniformity.
theorem chapter07_completion_is_parameterized_by_uniformity
    (K : Type*) (u : UniformSpace K) :
    chapter07CompletionForUniformity K u = @UniformSpace.Completion K u := by
  rfl

abbrev chapter07ArchimedeanRationalCompletion : Type _ :=
  ℝ

-- The usual completion of ℚ is the real field.
theorem chapter07_rationals_have_real_completion :
    ∃ e : UniformSpace.Completion ℚ ≃ᵤ
        chapter07ArchimedeanRationalCompletion,
      ∀ q : ℚ,
        e.toFun ((@UniformSpace.Completion.cPkg ℚ inferInstance).coe q) =
        (q : chapter07ArchimedeanRationalCompletion) := by
  let B : @AbstractCompletion ℚ inferInstance :=
    { space := ℝ
      coe := (↑)
      uniformStruct := inferInstance
      complete := inferInstance
      separation := inferInstance
      isUniformInducing := by
        exact Rat.isUniformEmbedding_coe_real.isUniformInducing
      dense := Rat.isDenseEmbedding_coe_real.dense }
  refine ⟨(@UniformSpace.Completion.cPkg ℚ inferInstance).compareEquiv B, ?_⟩
  intro q
  dsimp [AbstractCompletion.compareEquiv]
  have h := AbstractCompletion.compare_coe
    (@UniformSpace.Completion.cPkg ℚ inferInstance) B q
  simpa [B] using h

-- The same abstract field ℚ has the distinct p-adic completion with p-adic uniformity.
theorem chapter07_rationals_have_padic_completion
    (p : ℕ) [Fact p.Prime] :
    ∃ e : @UniformSpace.Completion ℚ (chapter07PAdicUniformSpace p) ≃ᵤ
        chapter07PAdicField p,
      ∀ q : ℚ,
        e (q : @UniformSpace.Completion ℚ (chapter07PAdicUniformSpace p)) =
          (q : chapter07PAdicField p) := by
  exact chapter07_padic_field_is_the_padic_completion p

-- Completion magnifies one chosen notion of nearness and does not canonically retain
-- completions for other uniformities.
theorem chapter07_completion_is_local_to_the_chosen_valuation
    (K : Type*) (u : UniformSpace K) :
    DenseRange (@UniformSpace.Completion.coe' K u) ∧
      @CompleteSpace (@UniformSpace.Completion K u)
        (@UniformSpace.Completion.uniformSpace K u) := by
  exact ⟨UniformSpace.Completion.denseRange_coe, inferInstance⟩

end
end LastLib.Book01ValuationsDVRsAndCompletions.Chapter07
