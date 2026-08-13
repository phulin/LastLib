import LastLib.Book01ValuationsDVRsAndCompletions.Chapter07.Section02ExtendingInverses

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter07

open Filter Set Function MonoidWithZeroHom
open scoped BigOperators Topology PowerSeries LaurentSeries RatFunc WithZero
  WithZeroTopology Multiplicative

noncomputable section

/-!
  Chapter 7 develops completion from the metric point of view and compares it with
  valuation rings and ideal-adic completion. Proofs are deferred to a later pass.
-/

/-! # Book 1, Chapter 7, Section 7.4: Completion of the Valuation Ring
-/

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

-- Completion preserves the residue field of the valuation ring.
theorem chapter07_completion_residue_field_equivalence
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] :
    ∃ e : (chapter07ValuationRing K Γ₀) ⧸
          IsLocalRing.maximalIdeal (chapter07ValuationRing K Γ₀) ≃+*
        (chapter07CompletedValuationRing K Γ₀) ⧸
          IsLocalRing.maximalIdeal (chapter07CompletedValuationRing K Γ₀),
      ∀ a : chapter07ValuationRing K Γ₀,
        e (Ideal.Quotient.mk _ a) =
          Ideal.Quotient.mk _
            (chapter07ValuationRingCompletionRingHom (K := K) (Γ₀ := Γ₀) a) := by
  let A := chapter07ValuationRing K Γ₀
  let B := chapter07CompletedValuationRing K Γ₀
  let mA : Ideal A := IsLocalRing.maximalIdeal A
  let mB : Ideal B := IsLocalRing.maximalIdeal B
  let f : A →+* B := chapter07ValuationRingCompletionRingHom (K := K) (Γ₀ := Γ₀)
  have hmap : Ideal.map f mA ≤ mB := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    apply (Valuation.mem_maximalIdeal_iff
      (v := chapter07CompletionValuation K Γ₀)).2
    have ha' := (Valuation.mem_maximalIdeal_iff
      (v := (Valued.v : Valuation K Γ₀))).1 ha
    change chapter07CompletionValuation K Γ₀
      (((f a : B) : UniformSpace.Completion K)) < 1
    change chapter07CompletionValuation K Γ₀
      ((((a : A) : K) : UniformSpace.Completion K)) < 1
    rw [chapter07_completion_valuation_apply_coe]
    exact ha'
  let g : A ⧸ mA →+* B ⧸ mB :=
    Ideal.Quotient.lift mA ((Ideal.Quotient.mk mB).comp f) (by
      intro a ha
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact (Ideal.map_le_iff_le_comap.mp hmap) ha)
  have g_surj : Function.Surjective g := by
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hbclosure : (b : UniformSpace.Completion K) ∈
        closure (Set.range (@chapter07ValuationRingCompletionEmbedding K Γ₀ _ _ _)) := by
      apply chapter07_completed_unit_ball_is_approximated_by_integral_elements
      exact b.property
    let U : Set (UniformSpace.Completion K) := {z |
      (Valued.v : Valuation (UniformSpace.Completion K) Γ₀).restrict
          (z - (b : UniformSpace.Completion K)) <
        (1 : MonoidWithZeroHom.ValueGroup₀
          (.ofClass (Valued.v : Valuation (UniformSpace.Completion K) Γ₀)))}
    have hUopen : IsOpen U := by
      have hball := Valued.isOpen_ball (UniformSpace.Completion K)
        (1 : MonoidWithZeroHom.ValueGroup₀
          (.ofClass (Valued.v : Valuation (UniformSpace.Completion K) Γ₀)))
      have htop : Valued.valuedCompletion.toTopologicalSpace =
          (UniformSpace.Completion.uniformSpace K).toTopologicalSpace := by
        rfl
      rw [htop] at hball
      simpa [U] using hball.preimage (continuous_id.sub continuous_const)
    have hUmem : U ∈ 𝓝 (b : UniformSpace.Completion K) := by
      apply hUopen.mem_nhds
      simp [U]
    obtain ⟨z, hzU, ⟨a, rfl⟩⟩ :=
      (mem_closure_iff_nhds.mp hbclosure) U hUmem
    refine ⟨Ideal.Quotient.mk mA a, ?_⟩
    rw [Ideal.Quotient.lift_mk]
    rw [← sub_eq_zero]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply (Valuation.mem_maximalIdeal_iff
      (v := chapter07CompletionValuation K Γ₀)).2
    have hrestrict : (Valued.v : Valuation (UniformSpace.Completion K) Γ₀).restrict
        (chapter07ValuationRingCompletionEmbedding a - (b : UniformSpace.Completion K)) <
        (1 : MonoidWithZeroHom.ValueGroup₀
          (.ofClass (Valued.v : Valuation (UniformSpace.Completion K) Γ₀))) := by
      change (Valued.v : Valuation (UniformSpace.Completion K) Γ₀).restrict
        ((((a : A) : K) : UniformSpace.Completion K) -
          (b : UniformSpace.Completion K)) < _ at hzU
      exact hzU
    have hlt' := (Valuation.restrict_lt_iff_lt_embedding
      (v := (Valued.v : Valuation (UniformSpace.Completion K) Γ₀))).mp hrestrict
    have hlt : (Valued.v : Valuation (UniformSpace.Completion K) Γ₀)
        (chapter07ValuationRingCompletionEmbedding a -
          (b : UniformSpace.Completion K)) < 1 := by
      simpa [Valuation.embedding_restrict] using hlt'
    change chapter07CompletionValuation K Γ₀
      ((((f a : B) : B) : UniformSpace.Completion K) -
        (b : UniformSpace.Completion K)) < 1
    have hfa : (((f a : B) : B) : UniformSpace.Completion K) =
        chapter07ValuationRingCompletionEmbedding a := by
      rfl
    simpa [show (Valued.v : Valuation (UniformSpace.Completion K) Γ₀) =
      chapter07CompletionValuation K Γ₀ by rfl, hfa] using hlt
  have g_inj : Function.Injective g := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← sub_eq_zero]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have hmemB : f a - f b ∈ mB := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub]
      exact sub_eq_zero.mpr (by simpa [g] using hxy)
    have hltB := (Valuation.mem_maximalIdeal_iff
      (v := chapter07CompletionValuation K Γ₀)).1 hmemB
    change chapter07CompletionValuation K Γ₀
      ((((f a : B) : B) : UniformSpace.Completion K) -
        (((f b : B) : B) : UniformSpace.Completion K)) < 1 at hltB
    apply (Valuation.mem_maximalIdeal_iff
      (v := (Valued.v : Valuation K Γ₀))).2
    change (Valued.v : Valuation K Γ₀)
      (((a : A) : K) - ((b : A) : K)) < 1
    have hcoediff : (((f a : B) : B) : UniformSpace.Completion K) -
        (((f b : B) : B) : UniformSpace.Completion K) =
        (((((a : A) : K) - ((b : A) : K)) : K) : UniformSpace.Completion K) := by
      change ((((a : A) : K) : UniformSpace.Completion K) -
        (((b : A) : K) : UniformSpace.Completion K)) = _
      symm
      exact (UniformSpace.Completion.coeRingHom : K →+* UniformSpace.Completion K).map_sub _ _
    rw [hcoediff, chapter07_completion_valuation_apply_coe] at hltB
    exact hltB
  let e := RingEquiv.ofBijective g ⟨g_inj, g_surj⟩
  refine ⟨e, ?_⟩
  intro a
  change g (Ideal.Quotient.mk mA a) =
    Ideal.Quotient.mk mB (f a)
  rw [Ideal.Quotient.lift_mk]
  rfl

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

end
end LastLib.Book01ValuationsDVRsAndCompletions.Chapter07
