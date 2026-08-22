import LastLib.Book05LocalClassFieldTheory.Chapter06.Dependencies

namespace LastLib.Book05LocalClassFieldTheory.Chapter06

noncomputable section

open scoped BigOperators Pointwise

/-!
### 6.1. Why a separate existence construction is necessary
-/

/-- The explicit finite-precision subgroups occurring in the source. -/
def chapter06PrecisionFamily
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) :
    Set (Subgroup Kˣ) :=
  {H | ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ H = chapter06PrecisionSubgroup D m n}

/- SOURCE_WARNING (§6.2, after the independence discussion): the precision
   and torsion coordinates retain the chosen uniformizer.  The intrinsic
   object is the resulting family of extensions, not a canonical equality of
   coordinate presentations attached to two different uniformizers. -/

theorem chapter06_mem_precisionFamily_iff
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (H : Subgroup Kˣ) :
    H ∈ chapter06PrecisionFamily D ↔
      ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ H = chapter06PrecisionSubgroup D m n :=
  Iff.rfl

/-- The valuation and unit directions commute in the multiplicative group. -/
theorem chapter06_precisionSubgroup_is_product
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (m n : ℕ) (x : Kˣ) :
    x ∈ chapter06PrecisionSubgroup D m n ↔
      ∃ z : ℤ, ∃ u : Kˣ,
        u ∈ Chapter06UnitFiltration D n ∧
          x = (chapter06UniformizerUnit D) ^ (m * z) * u := by
  exact chapter06_mem_precisionSubgroup_iff D m n x

private theorem chapter06_additive_value_group_eq_top
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ))
    (hdiscrete :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation v) :
    MonoidWithZeroHom.valueGroup (.ofClass v.toValuation) = ⊤ := by
  obtain ⟨π, hπ0, hπ, hv⟩ := hdiscrete
  have hone : ∀ z : ℕ, z • (1 : WithTop ℤ) = (z : WithTop ℤ) := by
    intro z
    induction z with
    | zero => simp
    | succ z ih =>
        rw [succ_nsmul, Nat.cast_succ, ih]
  have hnegcast : ∀ z : ℕ,
      (Int.negSucc z : WithTop ℤ) = -((z + 1 : ℕ) : WithTop ℤ) := by
    intro z
    simp [Int.negSucc_eq]
  have hpow : ∀ z : ℤ, v (π ^ z) = (z : WithTop ℤ) := by
    intro z
    cases z with
    | ofNat z =>
        change v (π ^ (z : ℤ)) = (z : WithTop ℤ)
        rw [zpow_natCast, v.map_pow, hπ, hone]
    | negSucc z =>
        rw [zpow_negSucc, v.map_inv, v.map_pow, hπ]
        rw [hnegcast z, hone]
  apply top_unique
  intro u _hu
  have hu0 :
      (OrderDual.ofDual (Multiplicative.toAdd
        (u : Multiplicative (WithTop ℤ)ᵒᵈ)) : WithTop ℤ) ≠ ⊤ := by
    intro htop
    apply Units.ne_zero u
    change Multiplicative.ofAdd (OrderDual.toDual
      (OrderDual.ofDual (Multiplicative.toAdd
        (u : Multiplicative (WithTop ℤ)ᵒᵈ)))) =
      Multiplicative.ofAdd (OrderDual.toDual (⊤ : WithTop ℤ))
    rw [htop]
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hu0
  apply MonoidWithZeroHom.mem_valueGroup
  refine ⟨π ^ n, ?_⟩
  change Multiplicative.ofAdd (OrderDual.toDual (v (π ^ n))) =
    (u : Multiplicative (WithTop ℤ)ᵒᵈ)
  rw [hpow n]
  exact congrArg (fun z : WithTop ℤ =>
    Multiplicative.ofAdd (OrderDual.toDual z)) hn

private theorem chapter06_additive_value_one_is_uniformizer
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (π : K)
    (_hπ0 : π ≠ 0) (hπ : v π = 1)
    (hdiscrete :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation v)
    [Valuation.IsRankOneDiscrete v.toValuation] :
    v.toValuation.IsUniformizer
      (⟨π, (Valuation.mem_valuationSubring_iff v.toValuation π).mpr (by
        change Multiplicative.ofAdd (OrderDual.toDual (v π)) ≤ 1
        rw [hπ]
        change (0 : WithTop ℤ) ≤ 1
        norm_num)⟩ : v.toValuation.valuationSubring) := by
  have hvg := chapter06_additive_value_group_eq_top v hdiscrete
  let γ : (Multiplicative (WithTop ℤ)ᵒᵈ)ˣ :=
    Units.mk0 (Multiplicative.ofAdd (OrderDual.toDual (1 : WithTop ℤ)))
      (by
        intro h
        have htop : (1 : WithTop ℤ) = ⊤ := congrArg (fun z =>
          OrderDual.ofDual (Multiplicative.toAdd z)) h
        exact (WithTop.coe_lt_top 1).ne htop)
  have hγ_lt : γ < 1 := by
    change Multiplicative.ofAdd (OrderDual.toDual (1 : WithTop ℤ)) < 1
    change (0 : WithTop ℤ) < 1
    norm_num
  have hone : ∀ z : ℕ, z • (1 : WithTop ℤ) = (z : WithTop ℤ) := by
    intro z
    induction z with
    | zero => simp
    | succ z ih =>
        rw [succ_nsmul, Nat.cast_succ, ih]
  have hnegcast : ∀ z : ℕ,
      (Int.negSucc z : WithTop ℤ) = -((z + 1 : ℕ) : WithTop ℤ) := by
    intro z
    simp [Int.negSucc_eq]
  have hγpow : ∀ n : ℤ,
      (γ ^ n : (Multiplicative (WithTop ℤ)ᵒᵈ)ˣ).val =
        Multiplicative.ofAdd (OrderDual.toDual (n : WithTop ℤ)) := by
    intro n
    cases n with
    | ofNat n =>
        simp [γ, zpow_natCast]
        change Multiplicative.ofAdd (OrderDual.toDual (1 : WithTop ℤ)) ^ n =
          Multiplicative.ofAdd (OrderDual.toDual (n : WithTop ℤ))
        rw [← ofAdd_nsmul n (OrderDual.toDual (1 : WithTop ℤ))]
        congr 1
        exact congrArg OrderDual.toDual (hone n)
    | negSucc n =>
        simp [γ, zpow_negSucc]
        change (Multiplicative.ofAdd (OrderDual.toDual (1 : WithTop ℤ)) ^
            (n + 1))⁻¹ =
          Multiplicative.ofAdd (OrderDual.toDual (Int.negSucc n : WithTop ℤ))
        rw [hnegcast n]
        change (Multiplicative.ofAdd (OrderDual.toDual (1 : WithTop ℤ)) ^
            (n + 1))⁻¹ =
          Multiplicative.ofAdd (-(OrderDual.toDual ((n + 1 : ℕ) : WithTop ℤ)))
        rw [ofAdd_neg]
        rw [← ofAdd_nsmul (n + 1)
          (OrderDual.toDual (1 : WithTop ℤ))]
        congr 1
        exact congrArg OrderDual.toDual (hone (n + 1))
  have hγ_zpowers : Subgroup.zpowers γ =
      (⊤ : Subgroup ((Multiplicative (WithTop ℤ)ᵒᵈ)ˣ)) := by
    apply top_unique
    intro u _hu
    have hu0 :
        (OrderDual.ofDual (Multiplicative.toAdd
          (u : Multiplicative (WithTop ℤ)ᵒᵈ)) : WithTop ℤ) ≠ ⊤ := by
      intro htop
      apply Units.ne_zero u
      change Multiplicative.ofAdd (OrderDual.toDual
        (OrderDual.ofDual (Multiplicative.toAdd
          (u : Multiplicative (WithTop ℤ)ᵒᵈ)))) =
        Multiplicative.ofAdd (OrderDual.toDual (⊤ : WithTop ℤ))
      rw [htop]
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hu0
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨n, ?_⟩
    apply Units.ext
    rw [hγpow]
    exact congrArg (fun z : WithTop ℤ =>
      Multiplicative.ofAdd (OrderDual.toDual z)) hn
  have hγ_zpowers_v : Subgroup.zpowers γ =
      MonoidWithZeroHom.valueGroup (.ofClass v.toValuation) := by
    rw [hvg]
    exact hγ_zpowers
  have hgen : γ = LinearOrderedCommGroup.Subgroup.genLTOne
      (MonoidWithZeroHom.valueGroup (.ofClass v.toValuation)) := by
    exact LinearOrderedCommGroup.Subgroup.genLTOne_unique
      (MonoidWithZeroHom.valueGroup (.ofClass v.toValuation)) hγ_lt hγ_zpowers_v
  rw [Valuation.IsUniformizer.iff]
  change Multiplicative.ofAdd (OrderDual.toDual (v π)) = _
  rw [hπ]
  calc
    Multiplicative.ofAdd (OrderDual.toDual (1 : WithTop ℤ)) = γ := by rfl
    _ = LinearOrderedCommGroup.Subgroup.genLTOne
          (MonoidWithZeroHom.valueGroup (.ofClass v.toValuation)) :=
      congrArg Units.val hgen
    _ = Valuation.IsRankOneDiscrete.generator v.toValuation :=
      congrArg Units.val
        (Valuation.IsRankOneDiscrete.valueGroup_genLTOne_eq_generator
          v.toValuation)

/- The finite-index statement is the precise form of the “cofinal family”
claim; the finite residue field is used through the cardinality of the unit
layers. -/
theorem chapter06_precisionSubgroup_finite_index
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Finite (Kˣ ⧸ chapter06PrecisionSubgroup D m n) := by
  classical
  let _ := D.residue_finite
  let _ : Valuation.IsRankOneDiscrete D.valuation.toValuation :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08_rank_one_discrete_of_add_valuation
      D.valuation D.complete.1
  have hDVR : IsDiscreteValuationRing (Chapter06ValuationRing D) := by
    change IsDiscreteValuationRing D.valuation.toValuation.valuationSubring
    infer_instance
  have hfiniteA (r : ℕ) (hr : 0 < r) :
      Finite ((Chapter06ValuationRing D)ˣ ⧸
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10UnitFiltration
          (Chapter06ValuationRing D) r) := by
    cases r with
    | zero =>
        rw [LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_unit_filtration_zero]
        infer_instance
    | succ r =>
        let _ : Finite (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Chapter10PrecisionQuotient
            (Chapter06ValuationRing D) (r + 1)) :=
          LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_finite_residue_finite_precision_quotients
            (Chapter06ValuationRing D) r hDVR
        let f : (Chapter06ValuationRing D)ˣ →*
            (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Chapter10PrecisionQuotient
              (Chapter06ValuationRing D) (r + 1))ˣ :=
          Units.map
            (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (Chapter06ValuationRing D)) ^ (r + 1))).toMonoidHom
        have hker : f.ker =
            LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10UnitFiltration
              (Chapter06ValuationRing D) (r + 1) := by
          ext u
          constructor
          · intro hu
            change f u = 1 at hu
            have hv := congrArg Units.val hu
            change Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (Chapter06ValuationRing D)) ^ (r + 1))
                (u : Chapter06ValuationRing D) = 1 at hv
            change (u : Chapter06ValuationRing D) - 1 ∈
              (IsLocalRing.maximalIdeal (Chapter06ValuationRing D)) ^ (r + 1)
            apply Ideal.Quotient.eq_zero_iff_mem.mp
            rw [map_sub]
            exact sub_eq_zero.mpr hv
          · intro hu
            apply MonoidHom.mem_ker.mpr
            apply Units.ext
            change Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (Chapter06ValuationRing D)) ^ (r + 1))
                (u : Chapter06ValuationRing D) = 1
            rw [← sub_eq_zero]
            change Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (Chapter06ValuationRing D)) ^ (r + 1))
                ((u : Chapter06ValuationRing D) - 1) = 0
            exact Ideal.Quotient.eq_zero_iff_mem.mpr (by
              change (u : Chapter06ValuationRing D) - 1 ∈
                (IsLocalRing.maximalIdeal (Chapter06ValuationRing D)) ^ (r + 1) at hu
              exact hu)
        rw [← hker]
        infer_instance
  obtain ⟨π₀, hπ₀0, hπ₀, _hvalues⟩ := D.complete.1
  have hchosen : D.valuation.toValuation.IsUniformizer D.uniformizer :=
    Valuation.isUniformizer_of_maximalIdeal_eq_span
      (v := D.valuation.toValuation) D.uniformizer_spec.2
  have hwitness : D.valuation.toValuation.IsUniformizer
      (⟨π₀, (Valuation.mem_valuationSubring_iff D.valuation.toValuation π₀).mpr (by
        change Multiplicative.ofAdd (OrderDual.toDual (D.valuation π₀)) ≤ 1
        rw [hπ₀]
        change (0 : WithTop ℤ) ≤ 1
        norm_num)⟩ : D.valuation.toValuation.valuationSubring) :=
    chapter06_additive_value_one_is_uniformizer D.valuation π₀ hπ₀0 hπ₀ D.complete.1
  have hassoc : Associated D.uniformizer
      (⟨π₀, (Valuation.mem_valuationSubring_iff D.valuation.toValuation π₀).mpr (by
        change Multiplicative.ofAdd (OrderDual.toDual (D.valuation π₀)) ≤ 1
        rw [hπ₀]
        change (0 : WithTop ℤ) ≤ 1
        norm_num)⟩ : D.valuation.toValuation.valuationSubring) :=
    Valuation.associated_of_isUniformizer hchosen hwitness
  obtain ⟨u, hu⟩ := hassoc
  have huw : (D.uniformizer : K) * (u : K) = π₀ := by
    exact congrArg (fun y : Chapter06ValuationRing D => (y : K)) hu
  have huval : D.valuation.toValuation (u : K) = 1 := by
    rw [(Valuation.isEquiv_valuation_valuationSubring D.valuation.toValuation).eq_one_iff_eq_one]
    exact (ValuationSubring.valuation_eq_one_iff _ _).1 u.isUnit
  have hvalto : D.valuation.toValuation (D.uniformizer : K) =
      D.valuation.toValuation (π₀ : K) := by
    rw [← huw, D.valuation.toValuation.map_mul, huval, mul_one]
  have hπ₀to : D.valuation.toValuation (π₀ : K) =
      Multiplicative.ofAdd (OrderDual.toDual (1 : WithTop ℤ)) := by
    exact congrArg (fun z : WithTop ℤ =>
      Multiplicative.ofAdd (OrderDual.toDual z)) hπ₀
  have hπ : D.valuation (D.uniformizer : K) = (1 : WithTop ℤ) := by
    have hπto := hvalto.trans hπ₀to
    simpa [AddValuation.toValuation_apply] using hπto
  have hpow (z : ℤ) : D.valuation ((chapter06UniformizerUnit D : K) ^ z) =
      (z : WithTop ℤ) := by
    cases z with
    | ofNat z =>
        rw [Int.ofNat_eq_natCast, zpow_natCast, D.valuation.map_pow]
        change z • D.valuation (D.uniformizer : K) = (z : WithTop ℤ)
        rw [hπ]
        simp
    | negSucc z =>
        rw [zpow_negSucc, D.valuation.map_inv, D.valuation.map_pow]
        change -((z + 1) • D.valuation (D.uniformizer : K)) =
          (Int.negSucc z : WithTop ℤ)
        rw [hπ]
        simp [Int.negSucc_eq]
  have hdecomp (x : Kˣ) :
      ∃ z : ℤ, ∃ u : (Chapter06ValuationRing D)ˣ,
        (x : K) = (chapter06UniformizerUnit D : K) ^ z * (u : K) := by
    obtain ⟨z, hz⟩ := _hvalues (x : K) (Units.ne_zero x)
    let y : K := (chapter06UniformizerUnit D : K) ^ (-z) * (x : K)
    have hyv : D.valuation y = 0 := by
      change D.valuation ((chapter06UniformizerUnit D : K) ^ (-z) * (x : K)) = 0
      rw [D.valuation.map_mul, hpow, hz]
      simp
    have hyA : y ∈ Chapter06ValuationRing D := by
      exact (Valuation.mem_valuationSubring_iff D.valuation.toValuation y).2 (by
        simp [hyv])
    have hyinvA : y⁻¹ ∈ Chapter06ValuationRing D := by
      exact (Valuation.mem_valuationSubring_iff D.valuation.toValuation y⁻¹).2 (by
        simp [hyv])
    let u : (Chapter06ValuationRing D)ˣ :=
      { val := ⟨y, hyA⟩
        inv := ⟨y⁻¹, hyinvA⟩
        val_inv := by
          apply Subtype.ext
          dsimp [y]
          field_simp [chapter06_uniformizer_ne_zero D, x.ne_zero]
        inv_val := by
          apply Subtype.ext
          dsimp [y]
          field_simp [chapter06_uniformizer_ne_zero D, x.ne_zero] }
    refine ⟨z, u, ?_⟩
    change (x : K) = (chapter06UniformizerUnit D : K) ^ z * y
    dsimp [y]
    rw [zpow_neg]
    field_simp [chapter06_uniformizer_ne_zero D]
  have hmod (z : ℤ) (r : ℕ) (hr : 1 ≤ r) :
      ∃ i : ℕ, i < r ∧ ∃ q : ℤ,
        z = (i : ℤ) + (r : ℤ) * q := by
    have hrpos : 0 < (r : ℤ) := by omega
    have hnonneg : 0 ≤ z % (r : ℤ) := Int.emod_nonneg _ (by omega)
    have hlt : z % (r : ℤ) < (r : ℤ) := Int.emod_lt_of_pos _ hrpos
    let i : ℕ := (z % (r : ℤ)).toNat
    have hi : i < r := by
      rw [Int.toNat_lt hnonneg]
      exact hlt
    refine ⟨i, hi, z / (r : ℤ), ?_⟩
    calc
      z = z % (r : ℤ) + (r : ℤ) * (z / (r : ℤ)) :=
        (Int.emod_add_mul_ediv z (r : ℤ)).symm
      _ = (i : ℤ) + (r : ℤ) * (z / (r : ℤ)) := by
        simp [i, Int.toNat_of_nonneg hnonneg]
  have hfiniteB (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
      Finite (Kˣ ⧸ chapter06PrecisionSubgroup D r s) := by
    let U : Subgroup (Chapter06ValuationRing D)ˣ :=
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10UnitFiltration
        (Chapter06ValuationRing D) s
    let _ : Finite ((Chapter06ValuationRing D)ˣ ⧸ U) := hfiniteA s (by omega)
    let _ : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    obtain ⟨t, ht, _htcover⟩ :=
      Subgroup.exists_leftTransversal_of_FiniteIndex
        (D := U) (H := (⊤ : Subgroup (Chapter06ValuationRing D)ˣ)) le_top
    let ι : (Chapter06ValuationRing D)ˣ →* Kˣ :=
      Units.map (Chapter06ValuationRing D).subtype.toMonoidHom
    let reps : Finset Kˣ :=
      (Finset.range r).biUnion (fun i =>
        t.biUnion (fun a =>
          {(chapter06UniformizerUnit D) ^ (i : ℤ) * ι (a : (Chapter06ValuationRing D)ˣ)}))
    have hcover :
        ⋃ g ∈ reps, g • (chapter06PrecisionSubgroup D r s : Set Kˣ) = Set.univ := by
      ext x
      constructor
      · intro _
        trivial
      · intro _
        obtain ⟨z, u, hxu⟩ := hdecomp x
        obtain ⟨i, hi, q, hz⟩ := hmod z r hr
        let aT := ht.toLeftFun (⟨u, trivial⟩ : (⊤ : Subgroup (Chapter06ValuationRing D)ˣ))
        let a : (⊤ : Subgroup (Chapter06ValuationRing D)ˣ) := aT
        have haU : (a : (Chapter06ValuationRing D)ˣ)⁻¹ * u ∈ U := by
          have haU' := ht.inv_toLeftFun_mul_mem
            (⟨u, trivial⟩ : (⊤ : Subgroup (Chapter06ValuationRing D)ˣ))
          change (a : (Chapter06ValuationRing D)ˣ)⁻¹ * u ∈ U at haU'
          exact haU'
        let d : (Chapter06ValuationRing D)ˣ := (a : (Chapter06ValuationRing D)ˣ)⁻¹ * u
        have hd : ι d ∈ Chapter06UnitFiltration D s := by
          exact ⟨d, haU, rfl⟩
        let g : Kˣ := (chapter06UniformizerUnit D) ^ (i : ℤ) * ι (a : (Chapter06ValuationRing D)ˣ)
        let b : Kˣ := (chapter06UniformizerUnit D) ^ ((r : ℤ) * q) * ι d
        have hb : b ∈ chapter06PrecisionSubgroup D r s := by
          apply (chapter06_mem_precisionSubgroup_iff D r s b).2
          refine ⟨q, ι d, hd, ?_⟩
          rfl
        have hg : g ∈ reps := by
          simp only [reps, Finset.mem_biUnion, Finset.mem_range, Finset.mem_singleton]
          exact ⟨i, hi, aT, aT.2, rfl⟩
        refine Set.mem_iUnion.2 ⟨g, Set.mem_iUnion.2 ⟨hg, ?_⟩⟩
        change ∃ y : Kˣ,
          y ∈ chapter06PrecisionSubgroup D r s ∧ g * y = x
        refine ⟨b, hb, ?_⟩
        apply Units.ext
        change (g : K) * (b : K) = (x : K)
        dsimp [g, b, d]
        rw [hxu, hz]
        simp [ι]
        rw [zpow_add₀ (chapter06_uniformizer_ne_zero D)]
        have ha0 : ((a : (Chapter06ValuationRing D)ˣ) : K) ≠ 0 := by
          intro ha0
          apply Units.ne_zero (a : (Chapter06ValuationRing D)ˣ)
          apply Subtype.ext
          exact ha0
        field_simp [ha0]
        rw [zpow_natCast]
        exact mul_comm _ _
    have hindex : (chapter06PrecisionSubgroup D r s).FiniteIndex :=
      Subgroup.finiteIndex_of_leftCoset_cover_const hcover
    let _ : (chapter06PrecisionSubgroup D r s).FiniteIndex := hindex
    infer_instance
  exact hfiniteB m n (by omega) (by omega)

theorem chapter06_precisionSubgroup_index
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Nat.card (Kˣ ⧸ chapter06PrecisionSubgroup D m n) =
      m * (chapter06ResidueCardinality D - 1) *
        chapter06ResidueCardinality D ^ (n - 1) := by
  sorry

/-- Every open finite-index subgroup contains a displayed precision subgroup.
This is the local-field form of Proposition 2.1 used by the chapter. -/
theorem chapter06_open_finite_index_contains_precision
    {K : Type*} [Field K]
    (D : Chapter06LocalFieldData K)
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    (htop : Chapter06UnitFiltrationNeighborhoodBasis D)
    (H : Subgroup Kˣ) (hopen : IsOpen (H : Set Kˣ))
    (hfinite : H.FiniteIndex) :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧
      chapter06PrecisionSubgroup D m n ≤ H := by
  sorry

theorem chapter06_precision_cofinality
    {K : Type*} [Field K]
    (D : Chapter06LocalFieldData K)
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    (htop : Chapter06UnitFiltrationNeighborhoodBasis D) :
    Chapter06PrecisionCofinality D htop := by
  intro H hopen hfinite
  exact chapter06_open_finite_index_contains_precision D htop H hopen hfinite

/-- The norm subgroup of a totally ramified level will be the unit precision
subgroup; this declaration keeps the two pieces separate until Section 5. -/
def chapter06RamifiedPrecisionSubgroup
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ) :
    Subgroup Kˣ :=
  Chapter06UnitFiltration D n

theorem chapter06_precision_family_realizes_valuation_and_unit_parts
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (m n : ℕ) :
    chapter06PrecisionSubgroup D m n =
      Subgroup.zpowers ((chapter06UniformizerUnit D) ^ m) ⊔
        chapter06RamifiedPrecisionSubgroup D n := by
  rfl

end

end LastLib.Book05LocalClassFieldTheory.Chapter06
