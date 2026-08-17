import LastLib.Book01ValuationsDVRsAndCompletions.Chapter07.Section01FillingTheMissingLimits
import Mathlib.RingTheory.Valuation.Discrete.RankOne

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter07

open Filter Set Function MonoidWithZeroHom
open scoped Topology WithZero

noncomputable section

/-!
  Chapter 7 develops completion from the metric point of view and compares it with
  valuation rings and ideal-adic completion. Proofs are deferred to a later pass.
-/

/-! # Book 1, Chapter 7, Section 7.2: Extending Inverses
-/

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
    (abv : AbsoluteValue K ℝ) [Chapter07NonarchimedeanCompatibility K abv]
    (u : chapter07CauchySequence K)
    (hu : chapter07CauchyBoundedAwayFromZero abv u) :
    CauchySeq (fun n => (u.1 n)⁻¹) := by
  rcases hu with ⟨c, hc, hc_event⟩
  rw [cauchySeq_iff]
  intro V hV
  have hV' : V ∈ @uniformity K abv.uniformSpace := by
    have heq := Chapter07NonarchimedeanCompatibility.uniformSpace_eq
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
    have heq := Chapter07NonarchimedeanCompatibility.uniformSpace_eq
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
    (abv : AbsoluteValue K ℝ) [Chapter07NonarchimedeanCompatibility K abv]
    (u : chapter07CauchySequence K)
    (hu : chapter07CauchyBoundedAwayFromZero abv u) :
  chapter07CauchySequence K :=
  ⟨fun n => (u.1 n)⁻¹, chapter07_inverse_terms_are_cauchy abv u hu⟩

-- Section 7.2: the inverse of a nonzero Cauchy class is represented by inverse terms.
theorem chapter07_inverse_sequence_is_cauchy
    {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K]
    [IsTopologicalRing K]
    (abv : AbsoluteValue K ℝ) [Chapter07NonarchimedeanCompatibility K abv]
    (u : chapter07CauchySequence K)
    (hu : chapter07CauchyBoundedAwayFromZero abv u) :
    CauchySeq (fun n => (u.1 n)⁻¹) := by
  exact chapter07_inverse_terms_are_cauchy abv u hu

-- The inverse class is a two-sided inverse.
theorem chapter07_cauchy_completion_nonzero_has_inverse
    {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K] [IsTopologicalRing K]
    (abv : AbsoluteValue K ℝ) [Chapter07NonarchimedeanCompatibility K abv]
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

-- A globally well-defined choice of inverse in the Cauchy quotient.
noncomputable def chapter07CauchyCompletionInverse
    {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K]
    [IsTopologicalRing K]
    (abv : AbsoluteValue K ℝ) [Chapter07NonarchimedeanCompatibility K abv]
    (x : chapter07CauchyCompletion K) : chapter07CauchyCompletion K := by
  classical
  exact if hx : x = chapter07CauchyCompletionZero then
    chapter07CauchyCompletionZero
  else
    Classical.choose (chapter07_cauchy_completion_nonzero_has_inverse abv x hx)

-- The chosen inverse has the expected two-sided inverse equations.
theorem chapter07_cauchy_completion_inverse_spec
    {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K]
    [IsTopologicalRing K]
    (abv : AbsoluteValue K ℝ) [Chapter07NonarchimedeanCompatibility K abv]
    (x : chapter07CauchyCompletion K)
    (hx : x ≠ chapter07CauchyCompletionZero) :
    chapter07CauchyCompletionMul x (chapter07CauchyCompletionInverse abv x) =
        chapter07CauchyCompletionOne ∧
      chapter07CauchyCompletionMul (chapter07CauchyCompletionInverse abv x) x =
        chapter07CauchyCompletionOne := by
  rw [chapter07CauchyCompletionInverse, dif_neg hx]
  exact Classical.choose_spec (chapter07_cauchy_completion_nonzero_has_inverse abv x hx)

-- Section 7.2: every nonzero class has a two-sided inverse for the
-- termwise multiplication defined on the Cauchy quotient.  The quotient
-- does not yet carry a `Field` instance in this file, so the theorem name
-- records precisely the interface established here.
theorem chapter07_valued_cauchy_completion_nonzero_has_two_sided_inverse
    {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K] [IsTopologicalRing K]
    (abv : AbsoluteValue K ℝ) [Chapter07NonarchimedeanCompatibility K abv] :
    ∀ x : chapter07CauchyCompletion K,
      x ≠ chapter07CauchyCompletionZero →
        chapter07CauchyCompletionMul x (chapter07CauchyCompletionInverse abv x) =
            chapter07CauchyCompletionOne ∧
          chapter07CauchyCompletionMul (chapter07CauchyCompletionInverse abv x) x =
            chapter07CauchyCompletionOne := by
  intro x hx
  exact chapter07_cauchy_completion_inverse_spec abv x hx

-- The valuation on the standard completion, obtained by extending the original valuation.
noncomputable def chapter07CompletionValuation
    (K Γ₀ : Type*) [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] :
    Valuation (UniformSpace.Completion K) Γ₀ :=
  Valued.extensionValuation

-- The standard valued-field completion already carries Mathlib's field structure.
theorem chapter07_standard_completion_nonzero_has_two_sided_inverse
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] (x : UniformSpace.Completion K) (hx : x ≠ 0) :
    x * x⁻¹ = 1 ∧ x⁻¹ * x = 1 := by
  exact ⟨mul_inv_cancel₀ hx, inv_mul_cancel₀ hx⟩

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

-- Valuations have eventually constant values on nonzero Cauchy sequences.
theorem chapter07_valuation_values_eventually_constant
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀]
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

/- Approximation of a completed element by an element of the dense field. -/
def Chapter07ValueApproximatedByOriginalValues
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] (x : UniformSpace.Completion K) : Prop :=
  ∃ r : K,
    chapter07CompletionValuation K Γ₀ (x - (r : UniformSpace.Completion K)) <
      chapter07CompletionValuation K Γ₀ x ∧
        chapter07CompletionValuation K Γ₀ (r : UniformSpace.Completion K) =
          chapter07CompletionValuation K Γ₀ x

-- A nonzero completed element has an original representative strictly closer than it is to zero.
theorem chapter07_completion_nonzero_value_is_approximated
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] (x : UniformSpace.Completion K) (hx : x ≠ 0) :
    Chapter07ValueApproximatedByOriginalValues x := by
  let δ : MonoidWithZeroHom.ValueGroup₀
      (.ofClass (Valued.v : Valuation (UniformSpace.Completion K) Γ₀)) :=
    (Valued.v : Valuation (UniformSpace.Completion K) Γ₀).restrict x
  have hδpos : 0 < δ := by
    apply (Valuation.restrict_pos_iff
      (v := (Valued.v : Valuation (UniformSpace.Completion K) Γ₀)) x).2
    exact (Valuation.pos_iff (Valued.v : Valuation (UniformSpace.Completion K) Γ₀)).2 hx
  let U : Set (UniformSpace.Completion K) :=
    {z | (Valued.v : Valuation (UniformSpace.Completion K) Γ₀).restrict (z - x) < δ}
  have hUopen : IsOpen U := by
    have hball := Valued.isOpen_ball (UniformSpace.Completion K) δ
    have htop : Valued.valuedCompletion.toTopologicalSpace =
        (UniformSpace.Completion.uniformSpace K).toTopologicalSpace := by
      rfl
    rw [htop] at hball
    simpa [U] using
      hball.preimage (continuous_id.sub continuous_const)
  have hUmem : U ∈ 𝓝 x := by
    apply hUopen.mem_nhds
    change (Valued.v : Valuation (UniformSpace.Completion K) Γ₀).restrict (x - x) < δ
    rw [sub_self, map_zero]
    exact hδpos
  obtain ⟨r, hr⟩ :=
    UniformSpace.Completion.denseRange_coe.mem_nhds hUmem
  have hrestrict :
      (Valued.v : Valuation (UniformSpace.Completion K) Γ₀).restrict
          ((r : K) - x) < δ := by
    exact hr
  have hlt :
      (Valued.v : Valuation (UniformSpace.Completion K) Γ₀) ((r : K) - x) <
        (Valued.v : Valuation (UniformSpace.Completion K) Γ₀) x := by
    have hlt' := (Valuation.restrict_lt_iff_lt_embedding
      (v := (Valued.v : Valuation (UniformSpace.Completion K) Γ₀))).mp hrestrict
    simpa [δ, Valuation.embedding_restrict] using hlt'
  refine ⟨r, ?_, ?_⟩
  · change (Valued.v : Valuation (UniformSpace.Completion K) Γ₀)
        (x - (r : UniformSpace.Completion K)) <
      (Valued.v : Valuation (UniformSpace.Completion K) Γ₀) x
    rw [show x - (r : UniformSpace.Completion K) = -((r : K) - x) by ring,
      (Valued.v : Valuation (UniformSpace.Completion K) Γ₀).map_neg]
    exact hlt
  · change (Valued.v : Valuation (UniformSpace.Completion K) Γ₀)
        (r : UniformSpace.Completion K) =
      (Valued.v : Valuation (UniformSpace.Completion K) Γ₀) x
    exact Valuation.map_eq_of_sub_lt
      (v := (Valued.v : Valuation (UniformSpace.Completion K) Γ₀)) hlt

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

end
end LastLib.Book01ValuationsDVRsAndCompletions.Chapter07
