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
  classical
  let _ := D.residue_finite
  let _ : Fintype (Chapter06ResidueField D) := Fintype.ofFinite _
  let _ : Valuation.IsRankOneDiscrete D.valuation.toValuation :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08_rank_one_discrete_of_add_valuation
      D.valuation D.complete.1
  have hDVR : IsDiscreteValuationRing (Chapter06ValuationRing D) := by
    change IsDiscreteValuationRing D.valuation.toValuation.valuationSubring
    infer_instance
  let U : Subgroup (Chapter06ValuationRing D)ˣ :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10UnitFiltration
      (Chapter06ValuationRing D) n
  have hunitcard : Nat.card ((Chapter06ValuationRing D)ˣ ⧸ U) =
      (chapter06ResidueCardinality D - 1) *
        chapter06ResidueCardinality D ^ (n - 1) := by
    rw [LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_unit_quotient_cardinality
      (Chapter06ValuationRing D) n hn hDVR]
    simp [chapter06ResidueCardinality, Nat.card_eq_fintype_card]
  have hunitfinite : Finite ((Chapter06ValuationRing D)ˣ ⧸ U) := by
    apply Nat.finite_of_card_ne_zero
    rw [hunitcard]
    have hq : 1 < chapter06ResidueCardinality D := by
      simpa [chapter06ResidueCardinality, Nat.card_eq_fintype_card] using
        (Fintype.one_lt_card : 1 < Fintype.card (Chapter06ResidueField D))
    have hq1 : 0 < chapter06ResidueCardinality D - 1 := by
      omega
    exact Nat.mul_ne_zero
      (Nat.ne_of_gt hq1)
      (pow_ne_zero _ (Nat.ne_of_gt (by omega :
        0 < chapter06ResidueCardinality D)))
  let _ : Finite ((Chapter06ValuationRing D)ˣ ⧸ U) := hunitfinite
  let _ : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨t, ht, _htcover⟩ :=
    Subgroup.exists_leftTransversal_of_FiniteIndex
      (D := U) (H := (⊤ : Subgroup (Chapter06ValuationRing D)ˣ)) le_top
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
  have huw : (D.uniformizer : K) * (u : K) = π₀ :=
    congrArg (fun y : Chapter06ValuationRing D => (y : K)) hu
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
  have hpowU (z : ℤ) :
      D.valuation (((chapter06UniformizerUnit D) ^ z : Kˣ) : K) =
        (z : WithTop ℤ) := by
    let f : Kˣ →* K :=
      { toFun := fun w => (w : K)
        map_one' := Units.val_one
        map_mul' := Units.val_mul }
    have hf : (((chapter06UniformizerUnit D) ^ z : Kˣ) : K) =
        ((chapter06UniformizerUnit D : K) ^ z) := by
      change f ((chapter06UniformizerUnit D) ^ z) =
        (f (chapter06UniformizerUnit D)) ^ z
      exact map_zpow f (chapter06UniformizerUnit D) z
    rw [hf]
    exact hpow z
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
  let ι : (Chapter06ValuationRing D)ˣ →* Kˣ :=
    Units.map (Chapter06ValuationRing D).subtype.toMonoidHom
  have hunitval (a : (Chapter06ValuationRing D)ˣ) :
      D.valuation (ι a : K) = 0 := by
    have hstd : D.valuation.toValuation (ι a : K) = 1 := by
      change D.valuation.toValuation ((a : Chapter06ValuationRing D) : K) = 1
      rw [(Valuation.isEquiv_valuation_valuationSubring D.valuation.toValuation).eq_one_iff_eq_one]
      exact (ValuationSubring.valuation_eq_one_iff _ _).1 a.isUnit
    simpa [AddValuation.toValuation_apply] using hstd
  let rep : Fin m × (t : Set (⊤ : Subgroup (Chapter06ValuationRing D)ˣ)) → Kˣ :=
    fun p => (chapter06UniformizerUnit D) ^ (p.1 : ℤ) * ι (p.2 : (Chapter06ValuationRing D)ˣ)
  have hrepval (p : Fin m × (t : Set (⊤ : Subgroup (Chapter06ValuationRing D)ˣ))) :
      D.valuation (rep p : K) = (p.1 : WithTop ℤ) := by
    dsimp [rep]
    rw [D.valuation.map_mul, hpowU, hunitval]
    simp
  have hrep_inj : Function.Injective rep := by
    intro p q hpq
    have hpval := hrepval p
    have hqval := hrepval q
    have hpqval := congrArg (fun w : Kˣ => D.valuation (w : K)) hpq
    have hij : (p.1 : ℕ) = q.1 := by
      rw [hpval, hqval] at hpqval
      exact_mod_cast hpqval
    have hι : ι (p.2 : (Chapter06ValuationRing D)ˣ) =
        ι (q.2 : (Chapter06ValuationRing D)ˣ) := by
      apply (mul_left_cancel (a := (chapter06UniformizerUnit D) ^ (p.1 : ℤ)))
      simpa [rep, hij] using hpq
    have hab : (p.2 : (Chapter06ValuationRing D)ˣ) = q.2 := by
      apply Units.ext
      apply Subtype.ext
      simpa [ι] using congrArg (fun w : Kˣ => (w : K)) hι
    have habtop : (p.2 : (⊤ : Subgroup (Chapter06ValuationRing D)ˣ)) = q.2 := by
      apply Subtype.ext
      exact hab
    exact Prod.ext (Fin.ext hij) (Subtype.ext habtop)
  let B := chapter06PrecisionSubgroup D m n
  let S : Set Kˣ := Set.range rep
  have hcomp : Subgroup.IsComplement S B := by
    rw [Subgroup.isComplement_subgroup_right_iff_bijective]
    constructor
    · intro p q hpq
      rcases p with ⟨pval, ⟨p₀, hp₀⟩⟩
      rcases q with ⟨qval, ⟨q₀, hq₀⟩⟩
      subst pval
      subst qval
      change QuotientGroup.mk' B (rep p₀) = QuotientGroup.mk' B (rep q₀) at hpq
      obtain ⟨z, hz, hpqz⟩ := (QuotientGroup.mk'_eq_mk' B).mp hpq
      obtain ⟨ell, d, hd, hzrepr⟩ :=
        (chapter06_mem_precisionSubgroup_iff D m n z).1 hz
      obtain ⟨dA, hdA, hdz⟩ := hd
      have hdzι : d = ι dA := by
        simpa [ι] using hdz.symm
      have hzval : D.valuation (z : K) = ((m : ℤ) * ell : WithTop ℤ) := by
        rw [hzrepr, hdzι]
        simp only [Units.val_mul]
        rw [D.valuation.map_mul, hpowU, hunitval]
        simp
      have hpval := hrepval p₀
      have hqval := hrepval q₀
      have hv : (p₀.1 : WithTop ℤ) + ((m : ℤ) * ell : WithTop ℤ) =
          (q₀.1 : WithTop ℤ) := by
        calc
          (p₀.1 : WithTop ℤ) + ((m : ℤ) * ell : WithTop ℤ) =
              D.valuation ((rep p₀ * z : Kˣ) : K) := by
                rw [Units.val_mul, D.valuation.map_mul, hpval, hzval]
          _ = D.valuation (rep q₀ : K) := by rw [hpqz]
          _ = (q₀.1 : WithTop ℤ) := hqval
      have hvint : (p₀.1 : ℤ) + (m : ℤ) * ell = (q₀.1 : ℤ) := by
        exact_mod_cast hv
      have hp_lt : (p₀.1 : ℤ) < (m : ℤ) := by exact_mod_cast p₀.1.isLt
      have hp_nonneg : 0 ≤ (p₀.1 : ℤ) := by omega
      have hq_nonneg : 0 ≤ (q₀.1 : ℤ) := by omega
      have hq_lt : (q₀.1 : ℤ) < (m : ℤ) := by exact_mod_cast q₀.1.isLt
      have hm_int : 0 < (m : ℤ) := by omega
      have hell : ell = 0 := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hellneg | hellpos
        · have hle : ell ≤ -1 := by omega
          have hml : (m : ℤ) * ell ≤ -(m : ℤ) := by
            calc
              (m : ℤ) * ell ≤ (m : ℤ) * (-1) :=
                mul_le_mul_of_nonneg_left hle (by omega)
              _ = -(m : ℤ) := by ring
          have hqneg : (q₀.1 : ℤ) < 0 := by omega
          exact (not_lt_of_ge hq_nonneg) hqneg
        · have hge : 1 ≤ ell := by omega
          have hml : (m : ℤ) ≤ (m : ℤ) * ell := by
            calc
              (m : ℤ) = (m : ℤ) * 1 := by ring
              _ ≤ (m : ℤ) * ell :=
                mul_le_mul_of_nonneg_left hge (by omega)
          have hmq : (m : ℤ) ≤ (q₀.1 : ℤ) := by
            calc
              (m : ℤ) ≤ (m : ℤ) * ell := hml
              _ ≤ (q₀.1 : ℤ) := by omega
          exact (not_lt_of_ge hmq) hq_lt
      have hvint0 := hvint
      rw [hell, mul_zero, add_zero] at hvint0
      have hij : (p₀.1 : ℕ) = q₀.1 := by omega
      have hz0 : z = ι dA := by rw [hzrepr, hdzι, hell]; simp
      have hι : ι (p₀.2 : (Chapter06ValuationRing D)ˣ) * ι dA =
          ι (q₀.2 : (Chapter06ValuationRing D)ˣ) := by
        apply (mul_left_cancel (a := (chapter06UniformizerUnit D) ^ (p₀.1 : ℤ)))
        simpa [rep, hij, hz0, mul_assoc] using hpqz
      have hab : (p₀.2 : (Chapter06ValuationRing D)ˣ) * dA =
          (q₀.2 : (Chapter06ValuationRing D)ˣ) := by
        apply Units.ext
        apply Subtype.ext
        simpa [ι] using congrArg (fun w : Kˣ => (w : K)) hι
      let dd : U.subgroupOf (⊤ : Subgroup (Chapter06ValuationRing D)ˣ) :=
        ⟨⟨dA, trivial⟩, hdA⟩
      have hquot : QuotientGroup.mk' (U.subgroupOf (⊤ : Subgroup
          (Chapter06ValuationRing D)ˣ)) (p₀.2 : (⊤ : Subgroup
            (Chapter06ValuationRing D)ˣ)) =
          QuotientGroup.mk' (U.subgroupOf (⊤ : Subgroup
            (Chapter06ValuationRing D)ˣ)) (q₀.2 : (⊤ : Subgroup
            (Chapter06ValuationRing D)ˣ)) := by
        apply (QuotientGroup.mk'_eq_mk' _).2
        refine ⟨dd, dd.2, ?_⟩
        apply Subtype.ext
        change (p₀.2 : (Chapter06ValuationRing D)ˣ) * dA =
          (q₀.2 : (Chapter06ValuationRing D)ˣ)
        rw [hab]
      have htin := (Subgroup.isComplement_subgroup_right_iff_bijective.mp ht).1
      have hpq₀ : p₀.2 = q₀.2 := htin hquot
      apply Subtype.ext
      exact congrArg rep (Prod.ext (Fin.ext hij) hpq₀)
    · intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective B q
      obtain ⟨z, u, hxu⟩ := hdecomp x
      obtain ⟨i, hi, k, hz⟩ := hmod z m (by omega)
      let aT := ht.toLeftFun (⟨u, trivial⟩ :
        (⊤ : Subgroup (Chapter06ValuationRing D)ˣ))
      let a : (⊤ : Subgroup (Chapter06ValuationRing D)ˣ) := aT
      have haU : (a : (Chapter06ValuationRing D)ˣ)⁻¹ * u ∈ U := by
        have haU' := ht.inv_toLeftFun_mul_mem
          (⟨u, trivial⟩ : (⊤ : Subgroup (Chapter06ValuationRing D)ˣ))
        change (a : (Chapter06ValuationRing D)ˣ)⁻¹ * u ∈ U at haU'
        exact haU'
      let d : (Chapter06ValuationRing D)ˣ :=
        (a : (Chapter06ValuationRing D)ˣ)⁻¹ * u
      have hd : ι d ∈ Chapter06UnitFiltration D n := by
        exact ⟨d, haU, rfl⟩
      let p : Fin m × (t : Set (⊤ : Subgroup (Chapter06ValuationRing D)ˣ)) :=
        ⟨⟨i, hi⟩, aT⟩
      let b : Kˣ := (chapter06UniformizerUnit D) ^ ((m : ℤ) * k) * ι d
      have hb : b ∈ B := by
        apply (chapter06_mem_precisionSubgroup_iff D m n b).2
        refine ⟨k, ι d, hd, rfl⟩
      refine ⟨⟨rep p, ⟨p, rfl⟩⟩, ?_⟩
      change QuotientGroup.mk' B (rep p) = QuotientGroup.mk' B x
      apply (QuotientGroup.mk'_eq_mk' B).2
      refine ⟨b, hb, ?_⟩
      apply Units.ext
      change (rep p : K) * (b : K) = (x : K)
      dsimp [rep, p, b, d, a, aT]
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
      ring
  let _ : Finite (Kˣ ⧸ B) :=
    chapter06_precisionSubgroup_finite_index D m n hm hn
  let _ : B.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hScard : Nat.card S = m * Nat.card (t : Set
      (⊤ : Subgroup (Chapter06ValuationRing D)ˣ)) := by
    change Nat.card (Set.range rep) = _
    calc
      Nat.card (Set.range rep) = Nat.card (Fin m × (t : Set
          (⊤ : Subgroup (Chapter06ValuationRing D)ˣ))) :=
        (Nat.card_congr (Equiv.ofInjective rep hrep_inj)).symm
      _ = m * Nat.card (t : Set (⊤ : Subgroup
          (Chapter06ValuationRing D)ˣ)) := by
        rw [Nat.card_prod, Nat.card_fin]
  calc
    Nat.card (Kˣ ⧸ chapter06PrecisionSubgroup D m n) = B.index :=
      (Subgroup.index_eq_card B).symm
    _ = Nat.card S := hcomp.card_left.symm
    _ = m * Nat.card (t : Set (⊤ : Subgroup (Chapter06ValuationRing D)ˣ)) := hScard
    _ = m * Nat.card ((Chapter06ValuationRing D)ˣ ⧸ U) := by
      congr 1
      calc
        Nat.card (t : Set (⊤ : Subgroup (Chapter06ValuationRing D)ˣ)) =
            (U.subgroupOf (⊤ : Subgroup (Chapter06ValuationRing D)ˣ)).index :=
          ht.card_left
        _ = U.relIndex (⊤ : Subgroup (Chapter06ValuationRing D)ˣ) := by
          rw [← Subgroup.relIndex_subgroupOf (H := U) (K := ⊤) (L := ⊤) le_top]
          simp
        _ = U.index := Subgroup.relIndex_top_right U
        _ = Nat.card ((Chapter06ValuationRing D)ˣ ⧸ U) := Subgroup.index_eq_card U
    _ = m * (chapter06ResidueCardinality D - 1) *
        chapter06ResidueCardinality D ^ (n - 1) := by
      rw [hunitcard, Nat.mul_assoc]

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
  classical
  change
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Chapter10UnitFiltrationNeighborhoodBasis
      (Chapter06UnitFiltration D) at htop
  obtain ⟨n, hn⟩ := htop.2 (H : Set Kˣ) (hopen.mem_nhds H.one_mem)
  have hunit : Chapter06UnitFiltration D n ≤ H := hn
  have hm0 : H.index ≠ 0 := hfinite.index_ne_zero
  have hm : 0 < H.index := Nat.pos_of_ne_zero hm0
  have hπ : (chapter06UniformizerUnit D) ^ H.index ∈ H :=
    Subgroup.pow_index_mem H (chapter06UniformizerUnit D)
  have hunit_succ : Chapter06UnitFiltration D (n + 1) ≤
      Chapter06UnitFiltration D n := by
    intro u hu
    change u ∈
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10UnitFiltration
        (Chapter06ValuationRing D) (n + 1)).map
          (Units.map (Chapter06ValuationRing D).subtype.toMonoidHom) at hu
    change u ∈
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10UnitFiltration
        (Chapter06ValuationRing D) n).map
          (Units.map (Chapter06ValuationRing D).subtype.toMonoidHom)
    rcases hu with ⟨v, hv, rfl⟩
    refine ⟨v, ?_, rfl⟩
    change ((v : Chapter06ValuationRing D) : Chapter06ValuationRing D) - 1 ∈
        (IsLocalRing.maximalIdeal (Chapter06ValuationRing D)) ^ (n + 1) at hv
    change ((v : Chapter06ValuationRing D) : Chapter06ValuationRing D) - 1 ∈
      (IsLocalRing.maximalIdeal (Chapter06ValuationRing D)) ^ n
    exact Ideal.pow_le_pow_right (Nat.le_succ n) hv
  refine ⟨H.index, n + 1, hm, by omega, ?_⟩
  · intro x hx
    obtain ⟨z, u, hu, hxu⟩ :=
      (chapter06_mem_precisionSubgroup_iff D H.index (n + 1) x).1 hx
    have hz : (chapter06UniformizerUnit D) ^ (H.index * z) ∈ H := by
      simpa [zpow_natCast, zpow_mul] using H.zpow_mem hπ z
    rw [hxu]
    exact H.mul_mem hz (hunit (hunit_succ hu))

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
