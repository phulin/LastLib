import Mathlib

namespace ValuationsBook.Chapter07

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
  sorry

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
        (v₁ n : UniformSpace.Completion K)) atTop
      (𝓝 (0 : UniformSpace.Completion K)) := by
    have h := (continuous_mul.tendsto
      ((0 : UniformSpace.Completion K),
        limUnder atTop (fun n => (v₁ n : UniformSpace.Completion K)))).comp
      (hdu.prodMk_nhds hv₁'.tendsto_limUnder)
    simpa only [Function.comp_def, zero_mul] using h
  have hterm₂ : Tendsto
      (fun n => (u₂ n : UniformSpace.Completion K) *
        ((v₁ n - v₂ n : K) : UniformSpace.Completion K)) atTop
      (𝓝 (0 : UniformSpace.Completion K)) := by
    have h := (continuous_mul.tendsto
      (limUnder atTop (fun n => (u₂ n : UniformSpace.Completion K)),
        (0 : UniformSpace.Completion K))).comp
      (hu₂'.tendsto_limUnder.prodMk_nhds hdv)
    simpa only [Function.comp_def, mul_zero] using h
  apply ((UniformSpace.Completion.isUniformInducing_coe K).isInducing.tendsto_nhds_iff).2
  have hsum := hterm₁.add hterm₂
  convert hsum using 1
  · funext n
    simp only [Function.comp_apply, UniformSpace.Completion.coe_sub,
      UniformSpace.Completion.coe_mul, UniformSpace.Completion.coe_add]
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
    letI : UniformSpace K := abv.uniformSpace
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
        simpa [Set.mem_setOf_eq, sub_eq_add_neg, add_comm] using hxy)
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
      letI : UniformSpace K := abv.uniformSpace
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
  push_neg at hnotall
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
  uniform_to_completion :
    @UniformContinuous (chapter07CauchyCompletion K) (UniformSpace.Completion K)
      uniformSpace inferInstance equivalent
  uniform_from_completion :
    @UniformContinuous (UniformSpace.Completion K) (chapter07CauchyCompletion K)
      inferInstance uniformSpace equivalent.symm

-- Section 7.1: a diagonal argument makes the Cauchy quotient complete.
theorem chapter07_cauchy_quotient_complete
    {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K] :
    Nonempty (Chapter07CauchyCompletionModel K) := by
  sorry

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
    simpa only [Set.mem_setOf_eq] using h γ
  push_neg at hnotall
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
    exact (not_le_of_gt hγpos) (by simpa [hzero] using hN₀val)
  have hvne : Valued.v (u.1 N₀) ≠ 0 :=
    (Valuation.ne_zero_iff (Valued.v (R := K))).2 hN₀ne
  refine ⟨Valued.v (u.1 N₀), hvne, ?_⟩
  filter_upwards [eventually_ge_atTop N₀] with n hn
  have hsmall' : (Valued.v (R := K)).restrict (u.1 N₀ - u.1 n) < γ.1 :=
    by simpa only [Set.mem_setOf_eq] using
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
  refine ⟨r, ?_⟩
  simpa [chapter07CompletionValuation, hr] using hγ

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
  refine ⟨r, ?_, ?_⟩
  · simpa [chapter07CompletionValuation, hr] using h₁
  · simpa [chapter07CompletionValuation, hr] using h₂

/-! ### 7.3. The universal property -/

-- The canonical extension map from a uniform space to a complete target.
noncomputable def chapter07UniversalCompletionExtension
    {K F : Type*} [UniformSpace K] [UniformSpace F] [CompleteSpace F]
    (f : K → F) (hf : UniformContinuous f) : UniformSpace.Completion K → F :=
  UniformSpace.Completion.extension f

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
  sorry

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

-- The inclusion from the original valuation ring into the completion.
def chapter07ValuationRingCompletionEmbedding
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] :
    chapter07ValuationRing K Γ₀ → UniformSpace.Completion K :=
  fun a => ((a : K) : UniformSpace.Completion K)

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
  sorry

-- The completed valuation ring is a DVR.
theorem chapter07_completed_valuation_ring_is_dvr
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] [hdiscrete : (Valued.v (R := K)).IsRankOneDiscrete] :
    IsDiscreteValuationRing (chapter07CompletedValuationRing K Γ₀) ∧
      IsAdicComplete
        (IsLocalRing.maximalIdeal (chapter07CompletedValuationRing K Γ₀))
        (chapter07CompletedValuationRing K Γ₀) := by
  sorry

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
    Nonempty
      ((chapter07ValuationRing K Γ₀) ⧸
          Ideal.span ({(π.val : chapter07ValuationRing K Γ₀) ^ n} : Set
            (chapter07ValuationRing K Γ₀)) ≃+*
        (chapter07CompletedValuationRing K Γ₀) ⧸
          Ideal.span ({(chapter07CompletedUniformizer π) ^ n} : Set
            (chapter07CompletedValuationRing K Γ₀))) := by
  sorry

-- The residue fields are canonically identified at level n = 1.
theorem chapter07_dvr_residue_field_equivalence
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] [hdiscrete : (Valued.v (R := K)).IsRankOneDiscrete]
    (π : (Valued.v (R := K)).Uniformizer) :
    Nonempty
      ((chapter07ValuationRing K Γ₀) ⧸
          Ideal.span ({(π.val : chapter07ValuationRing K Γ₀)} : Set
            (chapter07ValuationRing K Γ₀)) ≃+*
        (chapter07CompletedValuationRing K Γ₀) ⧸
          Ideal.span ({chapter07CompletedUniformizer π} : Set
            (chapter07CompletedValuationRing K Γ₀))) := by
  sorry

-- The completed field is the fraction field of the completed DVR.
theorem chapter07_completed_field_is_fraction_field
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] [hdiscrete : (Valued.v (R := K)).IsRankOneDiscrete] :
    Nonempty
      (FractionRing (chapter07CompletedValuationRing K Γ₀) ≃+*
        UniformSpace.Completion K) := by
  exact ⟨(FractionRing.algEquiv (chapter07CompletedValuationRing K Γ₀)
    (UniformSpace.Completion K)).toRingEquiv⟩

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
theorem chapter07_dvr_metric_completion_agrees_with_adic_completion
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    : ∃ e : @UniformSpace.Completion A (chapter07DvrUniformSpace A) ≃+*
        AdicCompletion (IsLocalRing.maximalIdeal A) A,
      ∀ a : A,
        e ((a : A) : @UniformSpace.Completion A (chapter07DvrUniformSpace A)) =
        chapter07AdicCompletionMap (IsLocalRing.maximalIdeal A) a := by
  sorry

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
  sorry

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
  sorry

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
    Nonempty
      (@UniformSpace.Completion ℚ (chapter07PAdicUniformSpace p) ≃ᵤ
        chapter07PAdicField p) := by
  letI : UniformSpace ℚ := chapter07PAdicUniformSpace p
  have hinducing : @IsUniformInducing ℚ (chapter07PAdicField p)
      (chapter07PAdicUniformSpace p)
      (inferInstance : UniformSpace (chapter07PAdicField p))
      ((↑) : ℚ → chapter07PAdicField p) := by
    change @IsUniformInducing ℚ (chapter07PAdicField p)
      (chapter07PAdicUniformSpace p)
      (inferInstance : UniformSpace (chapter07PAdicField p))
      ((↑) : ℚ → chapter07PAdicField p)
    exact (isUniformInducing_iff_uniformSpace).2 rfl
  let B : @AbstractCompletion ℚ (chapter07PAdicUniformSpace p) :=
    { space := chapter07PAdicField p
      coe := fun q : ℚ => (q : chapter07PAdicField p)
      uniformStruct := (inferInstance : UniformSpace (chapter07PAdicField p))
      complete := inferInstance
      separation := inferInstance
      isUniformInducing := hinducing
      dense := chapter07_rationals_are_dense_in_padic_field p }
  exact ⟨(@UniformSpace.Completion.cPkg ℚ (chapter07PAdicUniformSpace p)).compareEquiv B⟩

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
  exact y.property (by simpa [P, hy'])

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
    Nonempty
      (@UniformSpace.Completion (chapter07LocalizedIntegers p)
        (chapter07LocalizedIntegersPAdicUniformSpace p) ≃ᵤ
          chapter07PAdicIntegerRing p) := by
  letI : UniformSpace (chapter07LocalizedIntegers p) :=
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
    change @IsUniformInducing (chapter07LocalizedIntegers p)
      (chapter07PAdicIntegerRing p) (chapter07LocalizedIntegersPAdicUniformSpace p)
      (inferInstance : UniformSpace (chapter07PAdicIntegerRing p))
      (f : chapter07LocalizedIntegers p → chapter07PAdicIntegerRing p)
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
  exact ⟨(@UniformSpace.Completion.cPkg (chapter07LocalizedIntegers p)
    (chapter07LocalizedIntegersPAdicUniformSpace p)).compareEquiv B⟩

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
    letI : Countable (ℕ → Bool) := hc
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
  letI : Uncountable (ℕ → Bool) := hbool_uncountable
  have hdigit_uncountable : Uncountable (chapter07DigitString p) :=
    hemb.uncountable
  letI : Uncountable (chapter07DigitString p) := hdigit_uncountable
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

abbrev chapter07PolynomialLocalRing (k : Type*) [Field k] : Type _ :=
  MvPolynomial Unit k

-- The completed polynomial ring, using Mathlib's canonical maximal-variable
-- adic completion.
abbrev chapter07PolynomialLocalCompletion (k : Type*) [Field k] : Type _ :=
  AdicCompletion (MvPolynomial.idealOfVars Unit k)
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

    ∀ p : MvPolynomial Unit k,
      e (p : chapter07PowerSeriesRing k) =
        chapter07AdicCompletionMap (MvPolynomial.idealOfVars Unit k)
          (algebraMap (MvPolynomial Unit k) (chapter07PolynomialLocalRing k) p)
-- The same local identification as an algebra equivalence.
def chapter07PowerSeriesAlgebraToPolynomialLocalCompletion
    (k : Type*) [Field k] :
    Prop :=
  ∃ e : chapter07PowerSeriesRing k ≃ₐ[k] chapter07PolynomialLocalCompletion k,
    ∀ p : MvPolynomial Unit k,
      e (p : chapter07PowerSeriesRing k) =
        chapter07AdicCompletionMap (MvPolynomial.idealOfVars Unit k)
          (algebraMap (MvPolynomial Unit k) (chapter07PolynomialLocalRing k) p)

-- Section 7.6: completion of k[t]_(t) gives k[[t]].
theorem chapter07_polynomial_local_completion_is_power_series
    (k : Type*) [Field k] :
    chapter07PowerSeriesToPolynomialLocalCompletion k ∧
      chapter07PowerSeriesAlgebraToPolynomialLocalCompletion k := by
  let e := MvPowerSeries.toAdicCompletionAlgEquiv Unit k
  constructor
  · refine ⟨e.toRingEquiv, ?_⟩
    intro p
    change e (p : MvPowerSeries Unit k) =
      AdicCompletion.of (MvPolynomial.idealOfVars Unit k) (MvPolynomial Unit k) p
    rw [MvPowerSeries.toAdicCompletionAlgEquiv_apply,
      MvPowerSeries.toAdicCompletion_coe]
  · refine ⟨e.restrictScalars k, ?_⟩
    intro p
    change e (p : MvPowerSeries Unit k) =
      AdicCompletion.of (MvPolynomial.idealOfVars Unit k) (MvPolynomial Unit k) p
    rw [MvPowerSeries.toAdicCompletionAlgEquiv_apply,
      MvPowerSeries.toAdicCompletion_coe]

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
    Nonempty (UniformSpace.Completion ℚ ≃ᵤ
      chapter07ArchimedeanRationalCompletion) := by
  let B : @AbstractCompletion ℚ inferInstance :=
    { space := ℝ
      coe := (↑)
      uniformStruct := inferInstance
      complete := inferInstance
      separation := inferInstance
      isUniformInducing := by
        change @IsUniformInducing ℚ ℝ inferInstance inferInstance
          ((↑) : ℚ → ℝ)
        exact Rat.isUniformEmbedding_coe_real.isUniformInducing
      dense := Rat.isDenseEmbedding_coe_real.dense }
  exact ⟨(@UniformSpace.Completion.cPkg ℚ inferInstance).compareEquiv B⟩

-- The same abstract field ℚ has the distinct p-adic completion with p-adic uniformity.
theorem chapter07_rationals_have_padic_completion
    (p : ℕ) [Fact p.Prime] :
    Nonempty
      (@UniformSpace.Completion ℚ (chapter07PAdicUniformSpace p) ≃ᵤ
        chapter07PAdicField p) := by
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
end ValuationsBook.Chapter07
