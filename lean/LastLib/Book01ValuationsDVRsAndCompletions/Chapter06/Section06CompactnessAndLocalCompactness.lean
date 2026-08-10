import LastLib.Book01ValuationsDVRsAndCompletions.Chapter06.Section05InfiniteProducts

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter06

open Set Filter Function
open scoped BigOperators Pointwise Topology WithZero NNReal Valued PowerSeries

noncomputable section

/-! # Book 1, Chapter 6, Section 6.6: Compactness and Local Compactness
-/

/-! ### 6.6 Compactness and local compactness -/

section Compactness

variable {A : Type*} [CommRing A]

/-- A residue-class cover modulo an ideal. -/
def chapter06ResidueClassCover (m : Ideal A) :
    (A ⧸ m) → Set A := fun c =>
      (Ideal.Quotient.mk m) ⁻¹' ({c} : Set (A ⧸ m))

/-- Finite quotients permit a subsequence constant in one residue class. -/
theorem chapter06_subsequence_constant_mod_ideal
    (m : Ideal A) [Finite (A ⧸ m)] (x : ℕ → A) :
    ∃ c : A ⧸ m, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ n : ℕ, Ideal.Quotient.mk m (x (φ n)) = c := by
  classical
  let f : ℕ → A ⧸ m := fun n => Ideal.Quotient.mk m (x n)
  obtain ⟨c, hc⟩ := Finite.exists_infinite_fiber f
  have htail : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ f n = c := by
    intro N
    obtain ⟨n, hn, hn'⟩ :=
      (Set.infinite_coe_iff.mp hc).exists_notMem_finset (Finset.range (N + 1))
    refine ⟨n, ?_, ?_⟩
    · have hnle : N + 1 ≤ n := Nat.le_of_not_gt (by
        simpa [Finset.mem_range] using hn')
      omega
    · simpa [f] using hn
  obtain ⟨φ, hφ, hφc⟩ := Nat.exists_strictMono_subsequence htail
  refine ⟨c, φ, hφ, ?_⟩
  intro n
  simpa [f] using hφc n

/-- Finite residue fields give finite quotients modulo all powers in a DVR. -/
theorem chapter06_dvr_power_quotient_finite
    [IsDomain A] [IsDiscreteValuationRing A] [Finite (IsLocalRing.ResidueField A)] (n : ℕ) :
    Finite (A ⧸ ((IsLocalRing.maximalIdeal A) ^ n)) := by
  letI : Finite (A ⧸ IsLocalRing.maximalIdeal A) := by
    exact (inferInstance : Finite (IsLocalRing.ResidueField A))
  exact Ideal.finite_quotient_pow
    (IsPrincipalIdealRing.principal (IsLocalRing.maximalIdeal A)).fg n

/-- The diagonal subsequence construction is eventually constant modulo every power. -/
theorem chapter06_dvr_diagonal_subsequence
    [IsDomain A] [IsDiscreteValuationRing A] [Finite (IsLocalRing.ResidueField A)]
    (x : ℕ → A) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ n : ℕ, ∃ a : A, ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
        x (φ k) - a ∈ (IsLocalRing.maximalIdeal A) ^ n := by
  classical
  let m := IsLocalRing.maximalIdeal A
  letI : Finite (A ⧸ m) := by
    dsimp [m]
    exact (inferInstance : Finite (IsLocalRing.ResidueField A))
  let H (n : ℕ) (g : ℕ → ℕ) :
      ∃ c : A ⧸ (m ^ (n + 1)), ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∀ k : ℕ,
          Ideal.Quotient.mk (m ^ (n + 1)) (x (g (ψ k))) = c :=
    by
      letI : Finite (A ⧸ (m ^ (n + 1))) :=
        chapter06_dvr_power_quotient_finite (n + 1)
      exact chapter06_subsequence_constant_mod_ideal
        (m := m ^ (n + 1)) (x := x ∘ g)
  let c (n : ℕ) (g : ℕ → ℕ) : A ⧸ (m ^ (n + 1)) := Classical.choose (H n g)
  let ψ (n : ℕ) (g : ℕ → ℕ) : ℕ → ℕ :=
    Classical.choose (Classical.choose_spec (H n g))
  let f : ℕ → (ℕ → ℕ) :=
    Nat.rec (fun k => k) (fun n g => g ∘ ψ n g)
  have hH (n : ℕ) (g : ℕ → ℕ) :
      StrictMono (ψ n g) ∧
        ∀ k : ℕ,
          Ideal.Quotient.mk (m ^ (n + 1)) (x (g (ψ n g k))) = c n g := by
    exact Classical.choose_spec (Classical.choose_spec (H n g))
  have hf_succ (n : ℕ) : f (n + 1) = f n ∘ ψ n (f n) := by
    rfl
  have hf_strict : ∀ n : ℕ, StrictMono (f n) := by
    intro n
    induction n with
    | zero => exact strictMono_id
    | succ n ih =>
        rw [hf_succ n]
        exact ih.comp (hH n (f n)).1
  have hf_const : ∀ n : ℕ, ∃ a : A, ∀ k : ℕ,
      x (f n k) - a ∈ m ^ n := by
    intro n
    induction n with
    | zero =>
        refine ⟨0, fun k => ?_⟩
        simp [m]
    | succ n ih =>
        obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (c n (f n))
        refine ⟨a, fun k => ?_⟩
        have hk := (hH n (f n)).2 k
        have hmk :
            Ideal.Quotient.mk (m ^ (n + 1)) (x (f (n + 1) k)) =
              Ideal.Quotient.mk (m ^ (n + 1)) a := by
          rw [hf_succ n]
          exact (hk.trans ha.symm)
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        rw [map_sub, hmk]
        simp
  have hf_mem : ∀ {n j : ℕ}, n ≤ j → ∀ k : ℕ, ∃ l : ℕ, f j k = f n l := by
    intro n j hnj
    induction hnj with
    | refl =>
        intro k
        exact ⟨k, rfl⟩
    | @step j hnj ih =>
        intro k
        obtain ⟨l, hl⟩ := ih (ψ j (f j) k)
        refine ⟨l, ?_⟩
        rw [hf_succ j]
        simpa [Function.comp_apply] using hl
  have hdiag : StrictMono (fun n => f n n) := by
    intro i j hij
    have hfirst : f i i < f i (i + 1) := hf_strict i (Nat.lt_succ_self i)
    have hmid : f i (i + 1) ≤ f j (i + 1) := by
      induction hij with
      | refl =>
          rw [hf_succ i]
          exact (hf_strict i).monotone ((hH i (f i)).1.le_apply)
      | @step j hij ih =>
          exact ih.trans (by
            rw [hf_succ j]
            exact (hf_strict j).monotone ((hH j (f j)).1.le_apply))
    have hlast : f j (i + 1) ≤ f j j :=
      (hf_strict j).monotone (Nat.succ_le_iff.mpr hij)
    exact hfirst.trans_le (hmid.trans hlast)
  refine ⟨fun n => f n n, hdiag, ?_⟩
  intro n
  obtain ⟨a, ha⟩ := hf_const n
  refine ⟨a, n, fun k hk => ?_⟩
  obtain ⟨l, hl⟩ := hf_mem hk k
  simpa [hl] using ha l

/-- The diagonal subsequence is Cauchy in the maximal-ideal filtration. -/
def chapter06AdicCauchySeq (m : Ideal A) (x : ℕ → A) : Prop :=
  ∀ n : ℕ, ∃ N : ℕ, ∀ i j : ℕ,
    N ≤ i → N ≤ j → x i - x j ∈ m ^ n

/-- The diagonal construction yields an adically Cauchy subsequence. -/
theorem chapter06_dvr_diagonal_subsequence_is_adic_cauchy
    [IsDomain A] [IsDiscreteValuationRing A] [Finite (IsLocalRing.ResidueField A)]
    (x : ℕ → A) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      chapter06AdicCauchySeq (IsLocalRing.maximalIdeal A) (x ∘ φ) := by
  obtain ⟨φ, hφ, hφc⟩ := chapter06_dvr_diagonal_subsequence x
  refine ⟨φ, hφ, ?_⟩
  intro n
  obtain ⟨a, N, hN⟩ := hφc n
  refine ⟨N, fun i j hi hj => ?_⟩
  simpa [Function.comp_apply, sub_eq_add_neg, sub_add_sub_cancel] using
    (IsLocalRing.maximalIdeal A ^ n).sub_mem (hN i hi) (hN j hj)

/-- A complete DVR with finite residue field has compact valuation ring. -/
theorem chapter06_complete_dvr_integer_compact
    [IsDomain A] [IsDiscreteValuationRing A]
    [Finite (IsLocalRing.ResidueField A)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    @CompactSpace A (IsLocalRing.maximalIdeal A).adicTopology := by
  classical
  let m := IsLocalRing.maximalIdeal A
  let B := m.ringFilterBasis.toAddGroupFilterBasis
  letI : UniformSpace A := B.uniformSpace
  letI : IsUniformAddGroup A := B.isUniformAddGroup
  have hbasis :
      (@uniformity A B.uniformSpace).HasBasis (fun _ : ℕ => True)
        (fun n => {p : A × A |
          p.2 - p.1 ∈ ((m ^ n : Ideal A) : Set A)}) := by
    simpa [B] using (m.hasBasis_nhds_zero_adic.uniformity_of_nhds_zero)
  have htb : TotallyBounded (Set.univ : Set A) := by
    rw [hbasis.totallyBounded_iff]
    intro n _
    letI : Finite (A ⧸ m ^ n) := chapter06_dvr_power_quotient_finite n
    letI := Fintype.ofFinite (A ⧸ m ^ n)
    let rep : A ⧸ m ^ n → A := fun c => Classical.choose (Ideal.Quotient.mk_surjective c)
    have hrep (c : A ⧸ m ^ n) :
        Ideal.Quotient.mk (m ^ n) (rep c) = c :=
      Classical.choose_spec (Ideal.Quotient.mk_surjective c)
    refine ⟨Set.range rep, Set.finite_range rep, ?_⟩
    intro x _
    let c : A ⧸ m ^ n := Ideal.Quotient.mk (m ^ n) x
    refine Set.mem_iUnion.2 ⟨rep c, Set.mem_iUnion.2 ⟨Set.mem_range_self c, ?_⟩⟩
    change rep c - x ∈ ((m ^ n : Ideal A) : Set A)
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, hrep]
    simp [c]
  have hcomplete : CompleteSpace A := by
    exact ((IsAdic.isAdicComplete_iff (I := m) (by rfl)).mp
      (inferInstance : IsAdicComplete m A)).1
  refine ⟨?_⟩
  exact (isCompact_iff_totallyBounded_isComplete).2
    ⟨htb, completeSpace_iff_isComplete_univ.mp hcomplete⟩

/-- Infinite residue classes give an infinite disjoint open cover, hence noncompactness. -/
theorem chapter06_infinite_residue_field_integer_not_compact
    [IsDomain A] [IsDiscreteValuationRing A]
    [Infinite (IsLocalRing.ResidueField A)] :
    ¬ @CompactSpace A (IsLocalRing.maximalIdeal A).adicTopology := by
  classical
  let m := IsLocalRing.maximalIdeal A
  letI : Infinite (A ⧸ m) := by
    dsimp [m]
    exact (inferInstance : Infinite (IsLocalRing.ResidueField A))
  let B := m.ringFilterBasis.toAddGroupFilterBasis
  letI : UniformSpace A := B.uniformSpace
  letI : IsUniformAddGroup A := B.isUniformAddGroup
  have hm : @IsOpen A m.adicTopology (m : Set A) := by
    change @IsOpen A (IsLocalRing.maximalIdeal A).adicTopology
      (IsLocalRing.maximalIdeal A : Set A)
    convert ((IsLocalRing.maximalIdeal A).openAddSubgroup 1).isOpen' using 1
    simp [Ideal.openAddSubgroup, pow_one]
  have hcoset (c : A ⧸ m) :
      chapter06ResidueClassCover m c = c.out +ᵥ (m : Set A) := by
    ext x
    change Ideal.Quotient.mk m x = c ↔ x ∈ c.out +ᵥ (m : Set A)
    constructor
    · intro hx
      have hz : Ideal.Quotient.mk m (x - c.out) = 0 := by
        rw [map_sub, hx, Ideal.Quotient.mk_out]
        simp
      refine Set.mem_vadd_set.2 ⟨x - c.out,
        Ideal.Quotient.eq_zero_iff_mem.mp hz, ?_⟩
      simp only [vadd_eq_add]
      abel
    · intro hx
      obtain ⟨y, hy, hxy⟩ := Set.mem_vadd_set.1 hx
      rw [← hxy]
      simp only [vadd_eq_add, map_add, Ideal.Quotient.mk_out,
        Ideal.Quotient.eq_zero_iff_mem.mpr hy, add_zero]
  have hopen : ∀ c : A ⧸ m, @IsOpen A m.adicTopology
      (chapter06ResidueClassCover m c) :=
    fun c => (hcoset c ▸ hm.left_addCoset c.out)
  have hcover : (Set.univ : Set A) ⊆ ⋃ c : A ⧸ m,
      chapter06ResidueClassCover m c := by
    intro a _
    exact Set.mem_iUnion.2 ⟨Ideal.Quotient.mk m a, by
      change Ideal.Quotient.mk m a = Ideal.Quotient.mk m a
      rfl⟩
  intro hcompact
  letI : CompactSpace A := hcompact
  obtain ⟨t, ht⟩ :=
    isCompact_univ.elim_finite_subcover
      (fun c : A ⧸ m => chapter06ResidueClassCover m c) hopen hcover
  have hfinite : (Set.univ : Set (A ⧸ m)).Finite := by
    refine t.finite_toSet.subset ?_
    intro c _
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective c
    obtain ⟨d, hd⟩ := Set.mem_iUnion.1 (ht (Set.mem_univ a))
    obtain ⟨hdt, had⟩ := Set.mem_iUnion.1 hd
    change Ideal.Quotient.mk m a = d at had
    exact ha ▸ (had ▸ hdt)
  exact (not_finite_iff_infinite.mpr (inferInstance : Infinite (A ⧸ m)))
    (Finite.of_finite_univ hfinite)

/-- The residue-class cover modulo the maximal ideal is exhaustive and pairwise disjoint. -/
theorem chapter06_maximalIdeal_residue_class_cover
    [IsLocalRing A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [DiscreteTopology (A ⧸ IsLocalRing.maximalIdeal A)]
    (hm : @IsOpen A inferInstance (IsLocalRing.maximalIdeal A : Set A)) :
    (∀ c : A ⧸ IsLocalRing.maximalIdeal A,
        @IsOpen A inferInstance (chapter06ResidueClassCover (IsLocalRing.maximalIdeal A) c)) ∧
      (⋃ c : A ⧸ IsLocalRing.maximalIdeal A,
        chapter06ResidueClassCover (IsLocalRing.maximalIdeal A) c) = Set.univ ∧
      Pairwise (Disjoint on
        (chapter06ResidueClassCover (IsLocalRing.maximalIdeal A))) := by
  classical
  let m := IsLocalRing.maximalIdeal A
  have hcoset (c : A ⧸ m) :
      chapter06ResidueClassCover m c = c.out +ᵥ (m : Set A) := by
    ext x
    change Ideal.Quotient.mk m x = c ↔ x ∈ c.out +ᵥ (m : Set A)
    constructor
    · intro hx
      have hz : Ideal.Quotient.mk m (x - c.out) = 0 := by
        rw [map_sub, hx, Ideal.Quotient.mk_out]
        simp
      refine Set.mem_vadd_set.2 ⟨x - c.out,
        Ideal.Quotient.eq_zero_iff_mem.mp hz, ?_⟩
      simp only [vadd_eq_add]
      abel
    · intro hx
      obtain ⟨y, hy, hxy⟩ := Set.mem_vadd_set.1 hx
      rw [← hxy]
      simp only [vadd_eq_add, map_add, Ideal.Quotient.mk_out,
        Ideal.Quotient.eq_zero_iff_mem.mpr hy, add_zero]
  have hopen : ∀ c : A ⧸ m, @IsOpen A inferInstance
      (chapter06ResidueClassCover m c) := by
    intro c
    rw [hcoset]
    exact hm.left_addCoset c.out
  refine ⟨hopen, ?_, ?_⟩
  · ext x
    simp [chapter06ResidueClassCover]
  · intro c d hcd
    change Disjoint (chapter06ResidueClassCover (IsLocalRing.maximalIdeal A) c)
      (chapter06ResidueClassCover (IsLocalRing.maximalIdeal A) d)
    rw [Set.disjoint_left]
    intro x hxc hxd
    apply hcd
    change Ideal.Quotient.mk m x = c at hxc
    change Ideal.Quotient.mk m x = d at hxd
    exact hxc.symm.trans hxd

/- The following theorem is the valued-field form of the compactness criterion. -/
section ValuedCompactness

variable {K : Type*} [Field K]
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable [(Valued.v : Valuation K Γ₀).RankOne]

/-- Compactness of the valuation ring is equivalent to completeness, DVR, and finite residue field. -/
theorem chapter06_integer_compact_iff_complete_dvr_finite_residue :
    CompactSpace ((Valued.v : Valuation K Γ₀).valuationSubring) ↔
      CompleteSpace ((Valued.v : Valuation K Γ₀).valuationSubring) ∧
        IsDiscreteValuationRing ((Valued.v : Valuation K Γ₀).valuationSubring) ∧
          Finite (IsLocalRing.ResidueField ((Valued.v : Valuation K Γ₀).valuationSubring)) := by
  exact Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField

/-- A complete discretely valued field is locally compact exactly when its residue field is finite. -/
theorem chapter06_complete_dv_field_locallyCompact_iff_finite_residue
    [CompleteSpace ((Valued.v : Valuation K Γ₀).valuationSubring)]
    [IsDiscreteValuationRing ((Valued.v : Valuation K Γ₀).valuationSubring)] :
    LocallyCompactSpace K ↔
      Finite (IsLocalRing.ResidueField ((Valued.v : Valuation K Γ₀).valuationSubring)) := by
  constructor
  · intro _
    letI : ProperSpace K :=
      ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
    exact
      (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
        (K := K) (Γ₀ := Γ₀)).mp (inferInstance : ProperSpace K) |>.2.2
  · intro hfinite
    letI : Finite (IsLocalRing.ResidueField
        ((Valued.v : Valuation K Γ₀).valuationSubring)) := hfinite
    have hc : CompactSpace ((Valued.v : Valuation K Γ₀).valuationSubring) :=
      (chapter06_integer_compact_iff_complete_dvr_finite_residue).mpr
        ⟨inferInstance, inferInstance, hfinite⟩
    letI : CompactSpace ((Valued.v : Valuation K Γ₀).valuationSubring) := hc
    letI : ProperSpace K :=
      (Valued.integer.properSpace_iff_compactSpace_integer (K := K) (Γ₀ := Γ₀)).mpr
        hc
    infer_instance

/-- Fractional valuation balls exhaust the field. -/
def chapter06FractionalDVRBall (A : Subring K) (π : A) (n : ℕ) : Set K :=
  {x | ∃ a : A, x = (a : K) * (π : K) ^ (-(n : ℤ))}

/-- The usual `K = ⋃ₙ π⁻ⁿ A` description. -/
theorem chapter06_field_is_union_fractional_dvr_balls
    (A : Subring K) [IsDiscreteValuationRing A] [IsFractionRing A K]
    (π : A) (hπ : Irreducible π) :
    (Set.univ : Set K) = ⋃ n : ℕ, chapter06FractionalDVRBall A π n := by
  have hdecomp : ∀ x : K, ∃ n : ℕ, ∃ a : A,
      x = (a : K) * (π : K) ^ (-(n : ℤ)) := by
    intro x
    by_cases hx : x = 0
    · refine ⟨0, 0, ?_⟩
      simp [hx]
    · obtain ⟨a, b, hb, hfrac⟩ := IsFractionRing.div_surjective A x
      obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        (x := b) (nonZeroDivisors.ne_zero hb) hπ
      refine ⟨n, a * (↑u⁻¹ : A), ?_⟩
      rw [← hfrac, hu]
      simp only [map_mul, map_inv₀, map_pow, Units.val_inv_eq_inv_val,
        Algebra.smul_def]
      rw [zpow_neg]
      field_simp [hπ.ne_zero]
      simp [Subring.coe_mul, Units.val_inv_eq_inv_val,
        mul_assoc, mul_comm, mul_left_comm]
      change (π : K) ^ n * (a : K) =
        (a : K) * ((↑(u⁻¹) : K) * ((↑u : K) * (π : K) ^ n))
      have huinv : (↑(u⁻¹) : K) * (↑u : K) = 1 := by
        change (↑u.inv : K) * (↑u.val : K) = 1
        exact congrArg (fun q : A => (q : K)) u.inv_val
      calc
        (π : K) ^ n * (a : K) =
            (a : K) * ((↑(u⁻¹) : K) * (↑u : K)) * (π : K) ^ n := by
              rw [huinv]
              ring
        _ = (a : K) * ((↑(u⁻¹) : K) * ((↑u : K) * (π : K) ^ n)) := by
              ring
  ext x
  constructor
  · intro _
    obtain ⟨n, a, ha⟩ := hdecomp x
    exact Set.mem_iUnion.2 ⟨n, ⟨a, ha⟩⟩
  · intro _
    trivial

/-- In the finite-residue case the field is locally compact but not compact. -/
theorem chapter06_complete_dv_field_locally_compact_not_compact
    [CompleteSpace ((Valued.v : Valuation K Γ₀).valuationSubring)]
    [IsDiscreteValuationRing ((Valued.v : Valuation K Γ₀).valuationSubring)]
    [Finite (IsLocalRing.ResidueField ((Valued.v : Valuation K Γ₀).valuationSubring))] :
    LocallyCompactSpace K ∧ ¬ CompactSpace K := by
  refine ⟨(chapter06_complete_dv_field_locallyCompact_iff_finite_residue).mpr inferInstance, ?_⟩
  intro hcompact
  have hfiniteK : Finite K :=
    DivisionRing.finite_of_compactSpace_of_t2Space
  exact (not_finite_iff_infinite.mpr (inferInstance : Infinite K)) hfiniteK

end ValuedCompactness

/-- The p-adic numbers are locally compact. -/
theorem chapter06_padic_numbers_locally_compact
    {p : ℕ} [Fact p.Prime] : LocallyCompactSpace ℚ_[p] := by
  infer_instance

/-- Finite extensions of p-adic fields are locally compact. -/
theorem chapter06_finite_extension_of_padic_field_locally_compact
    {p : ℕ} {L : Type*} [Fact p.Prime] [NormedField L]
    [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L] :
    LocallyCompactSpace L := by
  exact LocallyCompactSpace.of_finiteDimensional_of_complete ℚ_[p] L

private noncomputable def chapter06LaurentUnitBallEquiv
    (k : Type*) [Field k] :
    k⟦X⟧ ≃+* (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring :=
  { toFun := fun F =>
      ⟨(F : LaurentSeries k), by
        rw [Valuation.mem_valuationSubring_iff]
        exact (LaurentSeries.val_le_one_iff_eq_coe k _).2 ⟨F, rfl⟩⟩
    invFun := fun x =>
      Classical.choose
        ((LaurentSeries.val_le_one_iff_eq_coe k (x : LaurentSeries k)).1
          ((Valuation.mem_valuationSubring_iff
            (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰) (x : LaurentSeries k)).1
            x.property))
    left_inv := by
      intro F
      apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := k)
      simpa using
        (Classical.choose_spec
          ((LaurentSeries.val_le_one_iff_eq_coe k (F : LaurentSeries k)).1
            ((LaurentSeries.val_le_one_iff_eq_coe k (F : LaurentSeries k)).2 ⟨F, rfl⟩)))
    right_inv := by
      intro x
      apply Subtype.ext
      exact (Classical.choose_spec
        ((LaurentSeries.val_le_one_iff_eq_coe k (x : LaurentSeries k)).1
          ((Valuation.mem_valuationSubring_iff
            (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰) (x : LaurentSeries k)).1
            x.property)))
    map_add' := by
      intro F G
      apply Subtype.ext
      exact PowerSeries.coe_add F G
    map_mul' := by
      intro F G
      apply Subtype.ext
      exact PowerSeries.coe_mul F G }

private theorem chapter06LaurentUnitBallMaximalIdealComap
    (k : Type*) [Field k] :
    IsLocalRing.maximalIdeal k⟦X⟧ =
      (IsLocalRing.maximalIdeal
        ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring)).comap
        (chapter06LaurentUnitBallEquiv k) := by
  let e := chapter06LaurentUnitBallEquiv k
  ext F
  constructor
  · intro hF
    change e F ∈ IsLocalRing.maximalIdeal
      ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring)
    apply (Valuation.mem_maximalIdeal_iff
      (K := LaurentSeries k)
      (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰)).2
    have hzero : PowerSeries.constantCoeff F = 0 := by
      rw [← PowerSeries.ker_coeff_eq_max_ideal] at hF
      exact RingHom.mem_ker.mp hF
    obtain ⟨G, hG⟩ := PowerSeries.X_dvd_iff.mpr hzero
    change (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰) (F : LaurentSeries k) < 1
    rw [hG, PowerSeries.coe_mul, map_mul]
    have hX :
        (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰)
            ((PowerSeries.X : k⟦X⟧) : LaurentSeries k) = WithZero.exp (-(1 : ℤ)) := by
      simpa using (LaurentSeries.valuation_X_pow (K := k) 1)
    rw [hX]
    have hGle :
        (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰) (G : LaurentSeries k) ≤
          (1 : ℤᵐ⁰) :=
      (LaurentSeries.val_le_one_iff_eq_coe k _).2 ⟨G, rfl⟩
    calc
      WithZero.exp (-(1 : ℤ)) *
          (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰) (G : LaurentSeries k) ≤
        WithZero.exp (-(1 : ℤ)) * 1 :=
        mul_le_mul_of_nonneg_left hGle WithZero.exp_pos.le
      _ = WithZero.exp (-(1 : ℤ)) := by simp
      _ < (1 : ℤᵐ⁰) := by
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
        norm_num
  · intro hF
    change e F ∈ IsLocalRing.maximalIdeal
      ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring) at hF
    by_contra hzero
    have hu : IsUnit F := IsLocalRing.notMem_maximalIdeal.mp hzero
    have hue : IsUnit (e F) := hu.map e
    exact (IsLocalRing.notMem_maximalIdeal.mpr hue) hF

/-- `k((t))` is locally compact when `k` is finite. -/
theorem chapter06_laurentSeries_locally_compact_of_finite_residue
    {k : Type*} [Field k] [Finite k] :
    LocallyCompactSpace (LaurentSeries k) := by
  let e := chapter06LaurentUnitBallEquiv k
  have he : IsLocalRing.maximalIdeal k⟦X⟧ =
      (IsLocalRing.maximalIdeal
        ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring)).comap e :=
    chapter06LaurentUnitBallMaximalIdealComap k
  letI : (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).IsRankOneDiscrete := by
    change Valuation.IsRankOneDiscrete ((PowerSeries.idealX k).valuation (LaurentSeries k))
    infer_instance
  letI : (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne (v := Valued.v) (by norm_num : 1 < (2 : ℝ≥0))
  letI : CompleteSpace (LaurentSeries k) := inferInstance
  letI : CompleteSpace
      ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring) := by
    exact IsComplete.completeSpace_coe
      ((Valued.isClosed_valuationSubring (LaurentSeries k) (Γ₀ := ℤᵐ⁰)).isComplete)
  letI : Finite ( (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring ⧸
      IsLocalRing.maximalIdeal
        ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring)) := by
    apply Finite.of_surjective
      (fun a : k => Ideal.Quotient.mk _ (e (PowerSeries.C a)))
    intro x
    obtain ⟨F, hF⟩ := Ideal.Quotient.mk_surjective x
    let F' : k⟦X⟧ := e.symm F
    refine ⟨PowerSeries.constantCoeff F', ?_⟩
    have hmem : PowerSeries.C (PowerSeries.constantCoeff F') - F' ∈
        IsLocalRing.maximalIdeal k⟦X⟧ := by
      rw [← PowerSeries.ker_coeff_eq_max_ideal]
      simp
    have hmem' : e (PowerSeries.C (PowerSeries.constantCoeff F') - F') ∈
        IsLocalRing.maximalIdeal
          ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring) := by
      change PowerSeries.C (PowerSeries.constantCoeff F') - F' ∈
        (IsLocalRing.maximalIdeal
          ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring)).comap e
      rw [← he]
      exact hmem
    have hF' : e F' = F := by
      dsimp [F']
      exact e.apply_symm_apply F
    rw [← hF, ← hF', ← sub_eq_zero, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa using hmem')
  letI : Finite (IsLocalRing.ResidueField
      ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring)) := by
    change Finite ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring ⧸
      IsLocalRing.maximalIdeal
        ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring))
    infer_instance
  exact (chapter06_complete_dv_field_locallyCompact_iff_finite_residue
    (K := LaurentSeries k) (Γ₀ := ℤᵐ⁰)).mpr inferInstance

/-- `k((t))` is not locally compact when `k` is infinite. -/
theorem chapter06_laurentSeries_not_locally_compact_of_infinite_residue
    {k : Type*} [Field k] [Infinite k] :
    ¬ LocallyCompactSpace (LaurentSeries k) := by
  intro hloc
  let e := chapter06LaurentUnitBallEquiv k
  have he : IsLocalRing.maximalIdeal k⟦X⟧ =
      (IsLocalRing.maximalIdeal
        ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring)).comap e :=
    chapter06LaurentUnitBallMaximalIdealComap k
  letI : (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).IsRankOneDiscrete := by
    change Valuation.IsRankOneDiscrete ((PowerSeries.idealX k).valuation (LaurentSeries k))
    infer_instance
  letI : (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne (v := Valued.v) (by norm_num : 1 < (2 : ℝ≥0))
  letI : CompleteSpace
      ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring) := by
    exact IsComplete.completeSpace_coe
      ((Valued.isClosed_valuationSubring (LaurentSeries k) (Γ₀ := ℤᵐ⁰)).isComplete)
  have hfin : Finite (IsLocalRing.ResidueField
      ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring)) :=
    (chapter06_complete_dv_field_locallyCompact_iff_finite_residue
      (K := LaurentSeries k) (Γ₀ := ℤᵐ⁰)).mp hloc
  letI : Finite (IsLocalRing.ResidueField k⟦X⟧) := by
    letI : Finite (IsLocalRing.ResidueField
        ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring)) := hfin
    exact Finite.of_equiv
      (IsLocalRing.ResidueField
        ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring))
      (by
        simpa only [IsLocalRing.ResidueField] using
          (IsLocalRing.ResidueField.mapEquiv e).symm.toEquiv)
  letI : Finite k := by
    exact Finite.of_equiv (IsLocalRing.ResidueField k⟦X⟧)
      (PowerSeries.residueFieldOfPowerSeries (k := k)).toEquiv
  exact (not_finite_iff_infinite.mpr (inferInstance : Infinite k)) inferInstance

end Compactness

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter06
