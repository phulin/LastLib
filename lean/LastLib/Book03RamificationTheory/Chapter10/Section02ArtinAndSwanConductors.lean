import LastLib.Book03RamificationTheory.Chapter10.Dependencies

namespace LastLib.Book03RamificationTheory.Chapter10

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## 10.2. Artin and Swan conductors -/

universe u v w

variable {E : Type u} {G : Type v} {V : Type w}
variable [Field E] [Group G] [Fintype G] [AddCommGroup V] [Module E V]
  [FiniteDimensional E V]

/-- The codimension of the fixed space at a lower-numbered group. -/
def lowerFixedSpaceCodim
    (F : RamificationFiltration G) (ρ : Representation E G V) (i : ℕ) : ℕ :=
  fixedSpaceCodim ρ (F.lower.group i)

def lowerFixedSpaceCodimRat
    (F : RamificationFiltration G) (ρ : Representation E G V) (i : ℕ) : ℚ :=
  (lowerFixedSpaceCodim F ρ i : ℚ)

/-- The single lower-numbered contribution to the Artin conductor. -/
def lowerConductorTerm
    (F : RamificationFiltration G) (ρ : Representation E G V) (i : ℕ) : ℚ :=
  F.lower.weight i * lowerFixedSpaceCodimRat F ρ i

/--
The Artin conductor exponent.  The displayed finite sum is the source's
`∑ i ≥ 0`: the chosen cutoff makes every omitted term zero.
-/
def artinConductor
    (F : RamificationFiltration G) (_hseparable : F.residue_separable)
    (ρ : Representation E G V) : ℚ :=
  ∑ i ∈ Finset.range (F.lower.cutoff + 1), lowerConductorTerm F ρ i

/-- The tame part, namely the codimension of inertia invariants. -/
def tameConductor
    (F : RamificationFiltration G) (_hseparable : F.residue_separable)
    (ρ : Representation E G V) : ℚ :=
  lowerFixedSpaceCodimRat F ρ 0

/-- The Swan conductor, retaining only the positive lower-numbered groups. -/
def swanConductor
    (F : RamificationFiltration G) (_hseparable : F.residue_separable)
    (ρ : Representation E G V) : ℚ :=
  ∑ i ∈ Finset.Ico 1 (F.lower.cutoff + 1), lowerConductorTerm F ρ i

@[simp] theorem lowerConductorTerm_eq_weight_mul_codimension
    (F : RamificationFiltration G) (ρ : Representation E G V) (i : ℕ) :
    lowerConductorTerm F ρ i =
      F.lower.weight i * lowerFixedSpaceCodimRat F ρ i := rfl

@[simp] theorem tameConductor_eq_inertia_codimension
    (F : RamificationFiltration G) (hseparable : F.residue_separable)
    (ρ : Representation E G V) :
    tameConductor F hseparable ρ = fixedSpaceCodimRat ρ (inertiaGroup F) := by
  rfl

theorem lower_weight_increment_is_upper_depth
    (F : RamificationFiltration G) {i : ℕ} (hi : i < F.lower.cutoff) :
    F.upper.depth (i + 1) - F.upper.depth i = (F.lower.weight (i + 1) : ℝ) :=
  F.upper.depth_step hi

theorem artinConductor_eq_tame_add_swan
    (F : RamificationFiltration G) (hseparable : F.residue_separable)
    (ρ : Representation E G V) :
    artinConductor F hseparable ρ =
      tameConductor F hseparable ρ + swanConductor F hseparable ρ := by
  classical
  unfold artinConductor tameConductor swanConductor lowerFixedSpaceCodimRat
  have hsplit : Finset.range (F.lower.cutoff + 1) =
      {0} ∪ Finset.Ico 1 (F.lower.cutoff + 1) := by
    ext i
    cases i with
    | zero => simp
    | succ i => simp
  rw [hsplit, Finset.sum_union]
  · simp [lowerConductorTerm, lowerFixedSpaceCodimRat,
      LowerRamificationFiltration.weight]
  · simp

theorem artinConductor_eq_full_lower_sum
    (F : RamificationFiltration G) (hseparable : F.residue_separable)
    (ρ : Representation E G V) {N : ℕ} (hN : F.lower.cutoff ≤ N) :
    artinConductor F hseparable ρ =
      ∑ i ∈ Finset.range (N + 1), lowerConductorTerm F ρ i := by
  classical
  have hterm : ∀ {i : ℕ}, F.lower.cutoff ≤ i →
      lowerConductorTerm F ρ i = 0 := by
    intro i hi
    have hfixed : fixedSpace ρ (F.lower.group i) = ⊤ := by
      rw [F.lower.group_eq_bot_of_ge hi]
      apply fixedSpace.top_of_trivial_on
      intro g
      have hg : (g : G) = 1 := by
        exact congrArg Subtype.val (Subsingleton.elim g (1 : (⊥ : Subgroup G)))
      rw [hg]
      simpa only [Module.End.one_eq_id] using ρ.map_one
    unfold lowerConductorTerm
    change F.lower.weight i * fixedSpaceCodimRat ρ (F.lower.group i) = 0
    rw [(fixedSpaceCodimRat_eq_zero_iff ρ (F.lower.group i)).2 hfixed, mul_zero]
  unfold artinConductor
  apply Finset.sum_subset
  · intro i hi
    exact Finset.mem_range.mpr <|
      Nat.lt_of_lt_of_le (Finset.mem_range.mp hi) (Nat.add_le_add_right hN 1)
  · intro i hi hnot
    apply hterm
    by_contra hcut
    apply hnot
    exact Finset.mem_range.mpr <|
      Nat.lt_succ_of_lt (Nat.lt_of_not_ge hcut)

theorem swanConductor_eq_full_positive_lower_sum
    (F : RamificationFiltration G) (hseparable : F.residue_separable)
    (ρ : Representation E G V) {N : ℕ} (hN : F.lower.cutoff ≤ N) :
    swanConductor F hseparable ρ =
      ∑ i ∈ Finset.Ico 1 (N + 1), lowerConductorTerm F ρ i := by
  classical
  have hterm : ∀ {i : ℕ}, F.lower.cutoff ≤ i →
      lowerConductorTerm F ρ i = 0 := by
    intro i hi
    have hfixed : fixedSpace ρ (F.lower.group i) = ⊤ := by
      rw [F.lower.group_eq_bot_of_ge hi]
      apply fixedSpace.top_of_trivial_on
      intro g
      have hg : (g : G) = 1 := by
        exact congrArg Subtype.val (Subsingleton.elim g (1 : (⊥ : Subgroup G)))
      rw [hg]
      simpa only [Module.End.one_eq_id] using ρ.map_one
    unfold lowerConductorTerm
    change F.lower.weight i * fixedSpaceCodimRat ρ (F.lower.group i) = 0
    rw [(fixedSpaceCodimRat_eq_zero_iff ρ (F.lower.group i)).2 hfixed, mul_zero]
  unfold swanConductor
  apply Finset.sum_subset
  · intro i hi
    exact Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hi).1,
      Nat.lt_of_lt_of_le (Finset.mem_Ico.mp hi).2 (Nat.add_le_add_right hN 1)⟩
  · intro i hi hnot
    apply hterm
    have hi_ge_one := (Finset.mem_Ico.mp hi).1
    have hi_ge_cutoff_succ : F.lower.cutoff + 1 ≤ i := by
      exact Nat.le_of_not_gt fun hlt => hnot (Finset.mem_Ico.mpr ⟨hi_ge_one, hlt⟩)
    exact Nat.le_trans (Nat.le_succ _) hi_ge_cutoff_succ

theorem lowerConductorTerm_nonnegative
    (F : RamificationFiltration G) (ρ : Representation E G V) (i : ℕ) :
    0 ≤ lowerConductorTerm F ρ i := by
  exact mul_nonneg (F.lower.weight_nonnegative i)
    (fixedSpaceCodimRat_nonnegative ρ (F.lower.group i))

theorem artinConductor_nonnegative
    (F : RamificationFiltration G) (hseparable : F.residue_separable)
    (ρ : Representation E G V) :
    0 ≤ artinConductor F hseparable ρ := by
  unfold artinConductor
  exact Finset.sum_nonneg fun i hi => lowerConductorTerm_nonnegative F ρ i

theorem tameConductor_nonnegative
    (F : RamificationFiltration G) (hseparable : F.residue_separable)
    (ρ : Representation E G V) :
    0 ≤ tameConductor F hseparable ρ := by
  exact fixedSpaceCodimRat_nonnegative ρ (inertiaGroup F)

theorem swanConductor_nonnegative
    (F : RamificationFiltration G) (hseparable : F.residue_separable)
    (ρ : Representation E G V) :
    0 ≤ swanConductor F hseparable ρ := by
  unfold swanConductor
  exact Finset.sum_nonneg fun i hi => lowerConductorTerm_nonnegative F ρ i

theorem lowerConductorTerm_eq_zero_of_fixed_space_top
    (F : RamificationFiltration G) (ρ : Representation E G V) (i : ℕ)
  (hfixed : fixedSpace ρ (F.lower.group i) = ⊤) :
    lowerConductorTerm F ρ i = 0 := by
  unfold lowerConductorTerm
  change F.lower.weight i * fixedSpaceCodimRat ρ (F.lower.group i) = 0
  rw [(fixedSpaceCodimRat_eq_zero_iff ρ (F.lower.group i)).2 hfixed, mul_zero]

/-- The upper-depth-area form of Swan, with the integral over `[0, ∞)`. -/
theorem swanConductor_eq_upperDepthArea
    (F : RamificationFiltration G) (hseparable : F.residue_separable)
    (ρ : Representation E G V) :
    ((swanConductor F hseparable ρ : ℚ) : ℝ) = upperDepthArea F ρ := by
  classical
  have hfixed_bot : fixedSpace ρ (⊥ : Subgroup G) = ⊤ := by
    apply fixedSpace.top_of_trivial_on
    intro g
    have hg : (g : G) = 1 := by
      exact congrArg Subtype.val (Subsingleton.elim g (1 : (⊥ : Subgroup G)))
    rw [hg]
    simpa only [Module.End.one_eq_id] using ρ.map_one
  have hdepth_nonneg : ∀ i : ℕ, 0 ≤ F.upper.depth i := by
    intro i
    rw [← F.upper.depth_zero]
    exact F.upper.depth_monotone (Nat.zero_le _)
  have hinterval_union {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
      Set.Ioc a b ∪ Set.Ioc b c = Set.Ioc a c := by
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact ⟨hx.1, hx.2.trans hbc⟩
      · exact ⟨hab.trans_lt hx.1, hx.2⟩
    · intro hx
      by_cases hxb : x ≤ b
      · exact Or.inl ⟨hx.1, hxb⟩
      · exact Or.inr ⟨lt_of_not_ge hxb, hx.2⟩
  have hunion : ∀ n : ℕ,
      (⋃ i ∈ Finset.range n,
        Set.Ioc (F.upper.depth i) (F.upper.depth (i + 1))) =
        Set.Ioc 0 (F.upper.depth n) := by
    intro n
    induction n with
    | zero => simp [F.upper.depth_zero]
    | succ n ih =>
        have hrange : Finset.range (Nat.succ n) =
            insert n (Finset.range n) := by
          ext i
          simp only [Finset.mem_range, Finset.mem_insert]
          constructor
          · intro h
            rcases lt_or_eq_of_le (Nat.le_of_lt_succ h) with hlt | heq
            · exact Or.inr hlt
            · exact Or.inl heq
          · intro h
            rcases h with rfl | hlt
            · exact Nat.lt_succ_self _
            · exact Nat.lt_trans hlt (Nat.lt_succ_self n)
        rw [hrange]
        simp only [Finset.set_biUnion_insert]
        rw [ih, Set.union_comm]
        exact hinterval_union (hdepth_nonneg n)
          (F.upper.depth_monotone (Nat.le_succ n))
  have hsubset :
      (⋃ i ∈ Finset.range F.lower.cutoff,
        Set.Ioc (F.upper.depth i) (F.upper.depth (i + 1))) ⊆ Set.Ici 0 := by
    rw [hunion]
    intro v hv
    exact le_of_lt hv.1
  have hzero_ae : ∀ᵐ v : ℝ ∂volume,
      v ∈ Set.Ici 0 \ (⋃ i ∈ Finset.range F.lower.cutoff,
        Set.Ioc (F.upper.depth i) (F.upper.depth (i + 1))) →
        upperFixedSpaceFunction F ρ v = 0 := by
    filter_upwards [show ∀ᵐ v : ℝ ∂volume, v ≠ 0 by
      simp [ae_iff]] with v hv hmem
    have hvpos : 0 < v := lt_of_le_of_ne hmem.1 (Ne.symm hv)
    by_cases hvdepth : v ≤ F.upper.depth F.lower.cutoff
    · exfalso
      apply hmem.2
      rw [hunion]
      exact ⟨hvpos, hvdepth⟩
    · rw [upperFixedSpaceFunction,
        F.upper.group_eq_bot_of_gt (lt_of_not_ge hvdepth)]
      exact (fixedSpaceCodimReal_eq_zero_iff ρ (⊥ : Subgroup G)).2 hfixed_bot
  have hset :
      (∫ v in Set.Ici (0 : ℝ), upperFixedSpaceFunction F ρ v) =
        ∫ v in (⋃ i ∈ Finset.range F.lower.cutoff,
          Set.Ioc (F.upper.depth i) (F.upper.depth (i + 1))),
          upperFixedSpaceFunction F ρ v := by
    have hmeas : MeasurableSet (Set.Ici (0 : ℝ)) := measurableSet_Ici
    exact setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (μ := (volume : Measure ℝ))
      (f := upperFixedSpaceFunction F ρ)
      (s := ⋃ i ∈ Finset.range F.lower.cutoff,
        Set.Ioc (F.upper.depth i) (F.upper.depth (i + 1)))
      (t := Set.Ici (0 : ℝ)) hmeas.nullMeasurableSet hsubset hzero_ae
  have hdisjoint : ∀ {i j : ℕ}, i < j →
      Disjoint (Set.Ioc (F.upper.depth i) (F.upper.depth (i + 1)))
        (Set.Ioc (F.upper.depth j) (F.upper.depth (j + 1))) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro v hvi hvj
    have hdepth : F.upper.depth (i + 1) ≤ F.upper.depth j :=
      F.upper.depth_monotone (Nat.succ_le_of_lt hij)
    exact (lt_irrefl _)
      (lt_of_lt_of_le hvj.1 (hvi.2.trans hdepth))
  have hpairwise : Set.Pairwise (↑(Finset.range F.lower.cutoff))
      (fun i j => Disjoint
        (Set.Ioc (F.upper.depth i) (F.upper.depth (i + 1)))
        (Set.Ioc (F.upper.depth j) (F.upper.depth (j + 1)))) := by
    intro i hi j hj hij
    rcases lt_or_gt_of_ne hij with hij | hij
    · exact hdisjoint hij
    · exact (hdisjoint hij).symm
  have hfi : Integrable (upperFixedSpaceFunction F ρ)
      (volume.restrict (Set.Ici (0 : ℝ))) :=
    upperFixedSpaceFunction_integrable_restrict F ρ
  have hinterval_integrable (i : ℕ) :
      IntegrableOn (upperFixedSpaceFunction F ρ)
        (Set.Ioc (F.upper.depth i) (F.upper.depth (i + 1))) volume := by
    have h' : IntegrableOn (upperFixedSpaceFunction F ρ)
        (Set.Ioc (F.upper.depth i) (F.upper.depth (i + 1)))
        (volume.restrict (Set.Ici (0 : ℝ))) := hfi.integrableOn
    have h'' := h'.inter_of_restrict (μ := volume) (t := Set.Ici (0 : ℝ))
    have hsub : Set.Ioc (F.upper.depth i) (F.upper.depth (i + 1)) ⊆ Set.Ici 0 := by
      intro v hv
      change 0 ≤ v
      exact le_of_lt ((hdepth_nonneg i).trans_lt hv.1)
    simpa [Set.inter_eq_self_of_subset_left hsub] using h''
  have hinterval_integral {i : ℕ} (hi : i < F.lower.cutoff) :
      (∫ v in Set.Ioc (F.upper.depth i) (F.upper.depth (i + 1)),
        upperFixedSpaceFunction F ρ v) =
        (F.upper.depth (i + 1) - F.upper.depth i) *
          fixedSpaceCodimReal ρ (F.lower.group (i + 1)) := by
    calc
      (∫ v in Set.Ioc (F.upper.depth i) (F.upper.depth (i + 1)),
          upperFixedSpaceFunction F ρ v) =
          ∫ v in Set.Ioc (F.upper.depth i) (F.upper.depth (i + 1)),
            (fun _ => fixedSpaceCodimReal ρ (F.lower.group (i + 1))) v := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
        simp only [upperFixedSpaceFunction]
        rw [F.upper.group_on_interval hi hv.1 hv.2]
      _ = (F.upper.depth (i + 1) - F.upper.depth i) *
          fixedSpaceCodimReal ρ (F.lower.group (i + 1)) := by
        rw [setIntegral_const,
          Real.volume_real_Ioc_of_le (F.upper.depth_monotone (Nat.le_succ i)),
          smul_eq_mul]
  have hunion_integral :
      (∫ v in (⋃ i ∈ Finset.range F.lower.cutoff,
          Set.Ioc (F.upper.depth i) (F.upper.depth (i + 1))),
          upperFixedSpaceFunction F ρ v) =
        ∑ i ∈ Finset.range F.lower.cutoff,
          (∫ v in Set.Ioc (F.upper.depth i) (F.upper.depth (i + 1)),
            upperFixedSpaceFunction F ρ v) := by
    apply integral_biUnion_finset
    · intro i hi
      exact measurableSet_Ioc
    · exact hpairwise
    · intro i hi
      exact hinterval_integrable i
  have hsum_reindex :
      (∑ i ∈ Finset.range F.lower.cutoff,
        (F.upper.depth (i + 1) - F.upper.depth i) *
          fixedSpaceCodimReal ρ (F.lower.group (i + 1))) =
        ∑ j ∈ Finset.Ico 1 (F.lower.cutoff + 1),
          (F.lower.weight j : ℝ) *
            fixedSpaceCodimReal ρ (F.lower.group j) := by
    apply Finset.sum_bij (fun i _ => i + 1)
    · intro i hi
      exact Finset.mem_Ico.mpr ⟨Nat.succ_le_succ (Nat.zero_le _),
        Nat.succ_lt_succ (Finset.mem_range.mp hi)⟩
    · intro i₁ hi₁ i₂ hi₂ h
      exact Nat.succ.inj h
    · intro j hj
      refine ⟨j - 1, Finset.mem_range.mpr ?_,
        Nat.sub_add_cancel (Finset.mem_Ico.mp hj).1⟩
      exact (Nat.sub_lt (lt_of_lt_of_le Nat.zero_lt_one
        (Finset.mem_Ico.mp hj).1) Nat.zero_lt_one).trans_le
        (Nat.le_of_lt_succ (Finset.mem_Ico.mp hj).2)
    · intro i hi
      rw [F.upper.depth_step (Finset.mem_range.mp hi)]
  calc
    ((swanConductor F hseparable ρ : ℚ) : ℝ) =
        ∑ j ∈ Finset.Ico 1 (F.lower.cutoff + 1),
          (F.lower.weight j : ℝ) *
            fixedSpaceCodimReal ρ (F.lower.group j) := by
      simp [swanConductor, lowerConductorTerm, lowerFixedSpaceCodim,
        lowerFixedSpaceCodimRat,
        fixedSpaceCodimReal, Rat.cast_sum, Rat.cast_mul]
    _ = ∑ i ∈ Finset.range F.lower.cutoff,
        (F.upper.depth (i + 1) - F.upper.depth i) *
          fixedSpaceCodimReal ρ (F.lower.group (i + 1)) := hsum_reindex.symm
    _ = ∑ i ∈ Finset.range F.lower.cutoff,
        ∫ v in Set.Ioc (F.upper.depth i) (F.upper.depth (i + 1)),
          upperFixedSpaceFunction F ρ v := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (hinterval_integral (Finset.mem_range.mp hi)).symm
    _ = ∫ v in (⋃ i ∈ Finset.range F.lower.cutoff,
          Set.Ioc (F.upper.depth i) (F.upper.depth (i + 1))),
          upperFixedSpaceFunction F ρ v := hunion_integral.symm
    _ = upperDepthArea F ρ := by
      simp only [upperDepthArea]
      exact hset.symm

theorem swanConductor_eq_upper_depth_integral
    (F : RamificationFiltration G) (hseparable : F.residue_separable)
    (ρ : Representation E G V) :
    ((swanConductor F hseparable ρ : ℚ) : ℝ) =
      ∫ v in Set.Ici (0 : ℝ), fixedSpaceCodimReal ρ (F.upper.group v) := by
  simpa [upperDepthArea, upperFixedSpaceFunction] using
    swanConductor_eq_upperDepthArea F hseparable ρ

/-- The fixed-space codimension function is stepwise constant and eventually
zero; endpoint choices do not affect its upper-depth integral. -/
theorem upper_fixed_space_function_is_step_with_finite_support
    (F : RamificationFiltration G) (ρ : Representation E G V) :
    (∃ B : ℝ, ∀ v, B ≤ v → upperFixedSpaceFunction F ρ v = 0) ∧
      (∀ {i : ℕ} {v w : ℝ}, i < F.lower.cutoff →
        F.upper.depth i < v → v ≤ F.upper.depth (i + 1) →
        F.upper.depth i < w → w ≤ F.upper.depth (i + 1) →
        upperFixedSpaceFunction F ρ v = upperFixedSpaceFunction F ρ w) := by
  have hfixed_bot : fixedSpace ρ (⊥ : Subgroup G) = ⊤ := by
    apply fixedSpace.top_of_trivial_on
    intro g
    have hg : (g : G) = 1 := by
      exact congrArg Subtype.val (Subsingleton.elim g (1 : (⊥ : Subgroup G)))
    rw [hg]
    simpa only [Module.End.one_eq_id] using ρ.map_one
  constructor
  · refine ⟨F.upper.depth F.lower.cutoff + 1, ?_⟩
    intro v hv
    change fixedSpaceCodimReal ρ (F.upper.group v) = 0
    rw [F.upper.group_eq_bot_of_gt
      (lt_of_lt_of_le (lt_add_one (F.upper.depth F.lower.cutoff)) hv)]
    exact (fixedSpaceCodimReal_eq_zero_iff ρ (⊥ : Subgroup G)).2 hfixed_bot
  · intro i v w hi hvv hvle hww hwl
    simp only [upperFixedSpaceFunction]
    rw [F.upper.group_on_interval hi hvv hvle,
      F.upper.group_on_interval hi hww hwl]

theorem upper_fixed_space_function_endpoint_values_irrelevant
    (F : RamificationFiltration G) (ρ : Representation E G V)
    {f : ℝ → ℝ}
    (hf : ∀ᵐ v ∂volume.restrict (Set.Ici (0 : ℝ)),
      f v = upperFixedSpaceFunction F ρ v) :
    (∫ v in Set.Ici (0 : ℝ), f v) = upperDepthArea F ρ := by
  exact upperDepthArea_congr_ae hf

end
end LastLib.Book03RamificationTheory.Chapter10
