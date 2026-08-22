import LastLib.Book05LocalClassFieldTheory.Chapter02.Dependencies
import LastLib.Book05LocalClassFieldTheory.Chapter02.Section01SeparatingMagnitudeFromUnits
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.Section03UniformizersAndMinimalPolynomials
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Topology.Instances.ZMod

namespace LastLib.Book05LocalClassFieldTheory.Chapter02

noncomputable section

open Function Ideal IsLocalRing
open Filter Topology
open scoped BigOperators Pointwise Topology

/-! ## 2.2. Open subgroups of finite index -/

def Chapter02OpenFiniteIndexSubgroup
    {K : Type*} [Field K] [TopologicalSpace Kˣ]
    (H : Subgroup Kˣ) : Prop :=
  IsOpen (H : Set Kˣ) ∧ Finite (Kˣ ⧸ H)

def Chapter02FiniteDiscreteQuotient
    {K : Type*} [Field K] [TopologicalSpace Kˣ]
    (H : Subgroup Kˣ) [TopologicalSpace (Kˣ ⧸ H)] : Prop :=
  Finite (Kˣ ⧸ H) ∧ DiscreteTopology (Kˣ ⧸ H)

def chapter02QuotientProjection
    {K : Type*} [Field K] (H : Subgroup Kˣ) :
    Kˣ →* (Kˣ ⧸ H) :=
  QuotientGroup.mk' H

theorem chapter02_mem_value_unit_subgroup_iff
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (π : Kˣ) (m n : ℕ) (x : Kˣ) :
    x ∈ chapter02ValueUnitSubgroup v π m n ↔
      ∃ z : ℤ, ∃ u : chapter02FieldUnitFiltration v n,
        x = π ^ ((m : ℤ) * z) * (u : Kˣ) := by
  change x ∈ Subgroup.zpowers (π ^ m) ⊔ chapter02FieldUnitFiltration v n ↔
    ∃ z : ℤ, ∃ u : chapter02FieldUnitFiltration v n,
      x = π ^ ((m : ℤ) * z) * (u : Kˣ)
  rw [Subgroup.mem_sup]
  constructor
  · rintro ⟨y, hy, u, hu, hxy⟩
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨z, ⟨u, hu⟩, ?_⟩
    rw [← hxy, ← hz, zpow_mul]
    rfl
  · rintro ⟨z, u, hxu⟩
    have hzmem : (π ^ m) ^ z ∈ Subgroup.zpowers (π ^ m) :=
      (Subgroup.mem_zpowers_iff).2 ⟨z, rfl⟩
    refine ⟨(π ^ m) ^ z, hzmem, (u : Kˣ), u.property, ?_⟩
    calc
      (π ^ m) ^ z * (u : Kˣ) = (π ^ (m : ℤ)) ^ z * (u : Kˣ) := by
        rw [zpow_natCast]
      _ = π ^ ((m : ℤ) * z) * (u : Kˣ) := by rw [zpow_mul]
      _ = x := hxu.symm

theorem chapter02_value_unit_subgroup_contains_deep_units
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (π : Kˣ) (m n : ℕ) :
    chapter02FieldUnitFiltration v n ≤
      chapter02ValueUnitSubgroup v π m n := by
  intro u hu
  exact
    (le_sup_right :
      chapter02FieldUnitFiltration v n ≤
        chapter02ValueUnitSubgroup v π m n) hu

theorem chapter02_value_unit_subgroup_contains_value_powers
    {K : Type*} [Field K]
  (v : AddValuation K (WithTop ℤ)) (π : Kˣ) (m n : ℕ) :
    Subgroup.zpowers (π ^ m) ≤ chapter02ValueUnitSubgroup v π m n := by
  exact le_sup_left

def Chapter02QuotientTopology
    {G : Type*} [CommGroup G] [TopologicalSpace G]
    (H : Subgroup G) [TopologicalSpace (G ⧸ H)] : Prop :=
  ∀ s : Set (G ⧸ H),
    IsOpen s ↔ IsOpen ((QuotientGroup.mk' H) ⁻¹' s)

theorem chapter02_open_subgroup_iff_quotient_discrete
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Subgroup G) [TopologicalSpace (G ⧸ H)]
    (hquotient : Chapter02QuotientTopology H) :
    IsOpen (H : Set G) ↔ DiscreteTopology (G ⧸ H) := by
  constructor
  · intro hH
    have hsingletons : ∀ q : G ⧸ H, IsOpen ({q} : Set (G ⧸ H)) := by
      intro q
      obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective H q
      have hpre : (QuotientGroup.mk' H) ⁻¹' ({q} : Set (G ⧸ H)) =
          (fun z : G => g * z) '' (H : Set G) := by
        ext y
        constructor
        · intro hy
          change QuotientGroup.mk' H y = q at hy
          have hyeq : QuotientGroup.mk' H y = QuotientGroup.mk' H g := by
            exact hy.trans hg.symm
          obtain ⟨z, hz, hyz⟩ :=
            (QuotientGroup.mk'_eq_mk' H).mp hyeq
          refine ⟨z⁻¹, H.inv_mem hz, ?_⟩
          calc
            g * z⁻¹ = (y * z) * z⁻¹ := by rw [hyz]
            _ = y := by simp [mul_assoc]
        · rintro ⟨z, hz, rfl⟩
          change QuotientGroup.mk' H (g * z) = q
          rw [← hg]
          apply (QuotientGroup.mk'_eq_mk' H).mpr
          exact ⟨z⁻¹, H.inv_mem hz, by simp [mul_assoc]⟩
      apply (hquotient {q}).mpr
      rw [hpre]
      exact (isOpenMap_mul_left g) _ hH
    exact ⟨eq_bot_of_singletons_open hsingletons⟩
  · intro hdiscrete
    have hone : IsOpen ({(1 : G ⧸ H)} : Set (G ⧸ H)) :=
      (discreteTopology_iff_isOpen_singleton.mp hdiscrete) 1
    have hpre : (QuotientGroup.mk' H) ⁻¹' ({(1 : G ⧸ H)} : Set (G ⧸ H)) =
        (H : Set G) := by
      ext g
      change QuotientGroup.mk' H g = 1 ↔ g ∈ H
      exact QuotientGroup.eq_one_iff g
    rw [← hpre]
    exact (hquotient {1}).mp hone

theorem proposition_2_1_open_finite_index_criterion
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ))
    (hlocal : Chapter02LocalField v)
    [TopologicalSpace Kˣ]
    [IsTopologicalGroup Kˣ]
    (_hbasis : Chapter02FieldUnitFiltrationNeighborhoodBasis v)
    (π : Kˣ) (hπ : chapter02IsUniformizerUnit v π)
    (hvaluebasis : Chapter02ValueUnitNeighborhoodBasis v π)
    (H : Subgroup Kˣ) [TopologicalSpace (Kˣ ⧸ H)]
    (hquotient : Chapter02QuotientTopology H) :
    (Chapter02OpenFiniteIndexSubgroup H ↔
      ∃ m n : ℕ, 1 ≤ m ∧ 1 ≤ n ∧
        chapter02ValueUnitSubgroup v π m n ≤ H) ∧
      (Chapter02OpenFiniteIndexSubgroup H ↔
        Chapter02FiniteDiscreteQuotient H) := by
  classical
  let A := Chapter02ValuationRing v
  let _ : Finite (Chapter02ResidueField v) := hlocal.2
  let _ : Fintype (Chapter02ResidueField v) := Fintype.ofFinite _
  let _ : Valuation.IsRankOneDiscrete v.toValuation :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08_rank_one_discrete_of_add_valuation
      v hlocal.1.1
  let _ : Nontrivial (MonoidWithZeroHom.valueGroup (.ofClass v.toValuation)) :=
    ⟨⟨Valuation.IsRankOneDiscrete.generator' v.toValuation, 1,
      ne_of_lt (Valuation.IsRankOneDiscrete.generator'_lt_one v.toValuation)⟩⟩
  have hDVR : IsDiscreteValuationRing A := by
    change IsDiscreteValuationRing v.toValuation.valuationSubring
    infer_instance
  have hfiniteA (n : ℕ) (hn : 0 < n) :
      Finite (Aˣ ⧸
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10UnitFiltration A n) := by
    apply Nat.finite_of_card_ne_zero
    rw [LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_unit_quotient_cardinality
      A n hn hDVR]
    have hq1 : 0 < Fintype.card (Chapter02ResidueField v) - 1 := by
      rw [← Fintype.card_units]
      exact Fintype.card_pos
    exact Nat.mul_ne_zero
      (Nat.ne_of_gt hq1)
      (pow_ne_zero _ (Nat.ne_of_gt (Fintype.card_pos :
        0 < Fintype.card (Chapter02ResidueField v))))
  obtain ⟨_, _, _, hvalues⟩ := hlocal.1.1
  have hpow (z : ℤ) : v ((π : K) ^ z) = (z : WithTop ℤ) := by
    cases z with
    | ofNat z =>
        rw [Int.ofNat_eq_natCast, zpow_natCast, v.map_pow, hπ]
        simp
    | negSucc z =>
        rw [zpow_negSucc, v.map_inv, v.map_pow, hπ]
        simp [Int.negSucc_eq]
  have hdecomp (x : Kˣ) :
      ∃ z : ℤ, ∃ u : Aˣ,
        (x : K) = (π : K) ^ z * (u : A) := by
    obtain ⟨z, hz⟩ := hvalues (x : K) (Units.ne_zero x)
    let y : K := (π : K) ^ (-z) * (x : K)
    have hyv : v y = 0 := by
      dsimp [y]
      rw [v.map_mul, hpow, hz]
      simp
    have hyA : y ∈ A := by
      exact (Valuation.mem_valuationSubring_iff v.toValuation y).2 (by
        simp [hyv])
    have hyinvA : y⁻¹ ∈ A := by
      exact (Valuation.mem_valuationSubring_iff v.toValuation y⁻¹).2 (by
        simp [hyv])
    let u : Aˣ :=
      { val := ⟨y, hyA⟩
        inv := ⟨y⁻¹, hyinvA⟩
        val_inv := by
          apply Subtype.ext
          dsimp [y]
          field_simp [π.ne_zero, x.ne_zero]
        inv_val := by
          apply Subtype.ext
          dsimp [y]
          field_simp [π.ne_zero, x.ne_zero] }
    refine ⟨z, u, ?_⟩
    change (x : K) = (π : K) ^ z * y
    dsimp [y]
    rw [zpow_neg]
    field_simp [π.ne_zero]
  have hmod (z : ℤ) (m : ℕ) (hm : 1 ≤ m) :
      ∃ r : ℕ, r < m ∧ ∃ q : ℤ, z = (r : ℤ) + (m : ℤ) * q := by
    have hmpos : 0 < (m : ℤ) := by omega
    have hnonneg : 0 ≤ z % (m : ℤ) := Int.emod_nonneg _ (by omega)
    have hlt : z % (m : ℤ) < (m : ℤ) := Int.emod_lt_of_pos _ hmpos
    let r : ℕ := (z % (m : ℤ)).toNat
    have hr : r < m := by
      rw [Int.toNat_lt hnonneg]
      exact hlt
    refine ⟨r, hr, z / (m : ℤ), ?_⟩
    calc
      z = z % (m : ℤ) + (m : ℤ) * (z / (m : ℤ)) :=
        (Int.emod_add_mul_ediv z (m : ℤ)).symm
      _ = (r : ℤ) + (m : ℤ) * (z / (m : ℤ)) := by
        simp [r, Int.toNat_of_nonneg hnonneg]
  have hfiniteB (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
      Finite (Kˣ ⧸ chapter02ValueUnitSubgroup v π m n) := by
    let U : Subgroup Aˣ :=
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10UnitFiltration A n
    let _ : Finite (Aˣ ⧸ U) := hfiniteA n hn
    let _ : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    obtain ⟨t, ht, _htcover⟩ :=
      Subgroup.exists_leftTransversal_of_FiniteIndex
        (D := U) (H := (⊤ : Subgroup Aˣ)) le_top
    let reps : Finset Kˣ :=
      (Finset.range m).biUnion (fun r =>
        t.biUnion (fun a =>
          {π ^ (r : ℤ) * chapter02UnitInclusion v (a : Aˣ)}))
    have hcover :
        ⋃ g ∈ reps, g • (chapter02ValueUnitSubgroup v π m n : Set Kˣ) = Set.univ := by
      ext x
      constructor
      · intro _
        trivial
      · intro _
        obtain ⟨z, u, hxu⟩ := hdecomp x
        obtain ⟨r, hr, q, hz⟩ := hmod z m hm
        let aT :=
          ht.toLeftFun (⟨u, trivial⟩ : (⊤ : Subgroup Aˣ))
        let a : (⊤ : Subgroup Aˣ) := aT
        have haU : (a : Aˣ)⁻¹ * u ∈ U := by
          have haU' := ht.inv_toLeftFun_mul_mem
            (⟨u, trivial⟩ : (⊤ : Subgroup Aˣ))
          change (a : Aˣ)⁻¹ * u ∈ U at haU'
          exact haU'
        let d : Aˣ := (a : Aˣ)⁻¹ * u
        have hd : chapter02UnitInclusion v d ∈ chapter02FieldUnitFiltration v n := by
          exact ⟨d, haU, rfl⟩
        let g : Kˣ := π ^ (r : ℤ) * chapter02UnitInclusion v (a : Aˣ)
        let b : Kˣ := π ^ ((m : ℤ) * q) * chapter02UnitInclusion v d
        have hb : b ∈ chapter02ValueUnitSubgroup v π m n := by
          apply (chapter02_mem_value_unit_subgroup_iff v π m n b).2
          refine ⟨q, ⟨chapter02UnitInclusion v d, hd⟩, ?_⟩
          rfl
        have hg : g ∈ reps := by
          simp only [reps, Finset.mem_biUnion, Finset.mem_range,
            Finset.mem_singleton]
          exact ⟨r, hr, aT, aT.2, rfl⟩
        refine Set.mem_iUnion.2 ⟨g, Set.mem_iUnion.2 ⟨hg, ?_⟩⟩
        change ∃ y : Kˣ,
          y ∈ chapter02ValueUnitSubgroup v π m n ∧ g * y = x
        refine ⟨b, hb, ?_⟩
        apply Units.ext
        change (g : K) * (b : K) = (x : K)
        dsimp [g, b, d]
        rw [hxu, hz]
        simp [chapter02UnitInclusion]
        rw [zpow_add₀ π.ne_zero]
        have ha0 : ((a : Aˣ) : K) ≠ 0 := by
          intro ha0
          apply Units.ne_zero (a : Aˣ)
          apply Subtype.ext
          exact ha0
        field_simp [ha0]
        rw [zpow_natCast]
    have hindex :
        (chapter02ValueUnitSubgroup v π m n).FiniteIndex :=
      Subgroup.finiteIndex_of_leftCoset_cover_const hcover
    let _ : (chapter02ValueUnitSubgroup v π m n).FiniteIndex := hindex
    exact (inferInstance : Finite (Kˣ ⧸ chapter02ValueUnitSubgroup v π m n))
  have hopen_of_le (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
      (J : Subgroup Kˣ)
      (hJ : chapter02ValueUnitSubgroup v π m n ≤ J) :
      Chapter02OpenFiniteIndexSubgroup J := by
    change IsOpen (J : Set Kˣ) ∧ Finite (Kˣ ⧸ J)
    refine ⟨?_, ?_⟩
    · have hBopen : IsOpen (chapter02ValueUnitSubgroup v π m n : Set Kˣ) :=
        hvaluebasis.1 m n hm hn
      have hBsub :
          (chapter02ValueUnitSubgroup v π m n : Set Kˣ) ⊆ (J : Set Kˣ) := hJ
      have hset :
          (J : Set Kˣ) =
            ⋃ j : J,
              (fun z : Kˣ => (j : Kˣ) * z) ''
                (chapter02ValueUnitSubgroup v π m n : Set Kˣ) := by
        ext x
        constructor
        · intro hx
          refine Set.mem_iUnion.2 ⟨⟨x, hx⟩, ?_⟩
          exact ⟨1, (chapter02ValueUnitSubgroup v π m n).one_mem, by simp⟩
        · intro hx
          obtain ⟨j, z, hz, rfl⟩ := Set.mem_iUnion.mp hx
          exact J.mul_mem j.2 (hBsub hz)
      rw [hset]
      exact isOpen_iUnion fun j =>
        (isOpenMap_mul_left (j : Kˣ)) _ hBopen
    · let _ : Finite (Kˣ ⧸ chapter02ValueUnitSubgroup v π m n) :=
        hfiniteB m n hm hn
      let _ : (chapter02ValueUnitSubgroup v π m n).FiniteIndex :=
        Subgroup.finiteIndex_of_finite_quotient
      have hJI : J.FiniteIndex := Subgroup.finiteIndex_of_le hJ
      let _ : J.FiniteIndex := hJI
      exact (inferInstance : Finite (Kˣ ⧸ J))
  refine ⟨?_, ?_⟩
  · change (IsOpen (H : Set Kˣ) ∧ Finite (Kˣ ⧸ H)) ↔
      ∃ m n : ℕ, 1 ≤ m ∧ 1 ≤ n ∧
        chapter02ValueUnitSubgroup v π m n ≤ H
    constructor
    · intro hHopen
      obtain ⟨m, n, hm, hn, hsub⟩ :=
        hvaluebasis.2 (H : Set Kˣ) (hHopen.1.mem_nhds H.one_mem)
      exact ⟨m, n, hm, hn, hsub⟩
    · rintro ⟨m, n, hm, hn, hsub⟩
      exact hopen_of_le m n hm hn H hsub
  · change (IsOpen (H : Set Kˣ) ∧ Finite (Kˣ ⧸ H)) ↔
      (Finite (Kˣ ⧸ H) ∧ DiscreteTopology (Kˣ ⧸ H))
    have hdisc : IsOpen (H : Set Kˣ) ↔ DiscreteTopology (Kˣ ⧸ H) :=
      chapter02_open_subgroup_iff_quotient_discrete H hquotient
    constructor
    · rintro ⟨hopen, hfinite⟩
      exact ⟨hfinite, hdisc.mp hopen⟩
    · rintro ⟨hfinite, hdiscrete⟩
      exact ⟨hdisc.mpr hdiscrete, hfinite⟩

theorem chapter02_finite_quotient_of_value_unit_neighborhood
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ))
    [TopologicalSpace Kˣ]
    [IsTopologicalGroup Kˣ]
    (_hbasis : Chapter02FieldUnitFiltrationNeighborhoodBasis v)
    (π : Kˣ) (hvaluebasis : Chapter02ValueUnitNeighborhoodBasis v π)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (H : Subgroup Kˣ)
    (hH : chapter02ValueUnitSubgroup v π m n ≤ H)
    (hfinite : Finite (Kˣ ⧸ chapter02ValueUnitSubgroup v π m n)) :
    Chapter02OpenFiniteIndexSubgroup H := by
  change IsOpen (H : Set Kˣ) ∧ Finite (Kˣ ⧸ H)
  refine ⟨?_, ?_⟩
  · have hBopen : IsOpen (chapter02ValueUnitSubgroup v π m n : Set Kˣ) :=
      hvaluebasis.1 m n hm hn
    have hBsub :
        (chapter02ValueUnitSubgroup v π m n : Set Kˣ) ⊆ (H : Set Kˣ) := hH
    have hset :
        (H : Set Kˣ) =
          ⋃ h : H,
            (fun z : Kˣ => (h : Kˣ) * z) ''
              (chapter02ValueUnitSubgroup v π m n : Set Kˣ) := by
      ext x
      constructor
      · intro hx
        refine Set.mem_iUnion.2 ⟨⟨x, hx⟩, ?_⟩
        exact ⟨1, (chapter02ValueUnitSubgroup v π m n).one_mem, by simp⟩
      · intro hx
        obtain ⟨h, z, hz, rfl⟩ := Set.mem_iUnion.mp hx
        exact H.mul_mem h.2 (hBsub hz)
    rw [hset]
    exact isOpen_iUnion fun h =>
      (isOpenMap_mul_left (h : Kˣ)) _ hBopen
  · let _ : Finite (Kˣ ⧸ chapter02ValueUnitSubgroup v π m n) := hfinite
    let _ : (chapter02ValueUnitSubgroup v π m n).FiniteIndex :=
      Subgroup.finiteIndex_of_finite_quotient
    have hHI : H.FiniteIndex := Subgroup.finiteIndex_of_le hH
    let _ : H.FiniteIndex := hHI
    exact (inferInstance : Finite (Kˣ ⧸ H))

theorem chapter02_finite_index_open_requires_continuity
    {G Q : Type*} [Group G] [Group Q]
    [TopologicalSpace G] [TopologicalSpace Q] (H : Subgroup G)
    [DiscreteTopology Q] (φ : G →* Q)
    (hker : MonoidHom.ker φ = H)
    (hcontinuous : Continuous φ) :
    IsOpen (H : Set G) := by
  rw [← hker]
  exact hcontinuous.isOpen_preimage _
    ((discreteTopology_iff_isOpen_singleton.mp inferInstance) 1)

/- A concrete profinite test object records why an abstract finite quotient is
   not enough: discontinuous finite-valued homomorphisms can have non-open
   kernels. -/
theorem chapter02_profinite_finite_index_need_not_be_open :
    ∃ H : Subgroup (Multiplicative (ℕ → ZMod 2)),
      Finite ((Multiplicative (ℕ → ZMod 2)) ⧸ H) ∧
        ¬IsOpen (H : Set (Multiplicative (ℕ → ZMod 2))) := by
  classical
  let V := ℕ → ZMod 2
  let P : Submodule (ZMod 2) V :=
    Submodule.span (ZMod 2)
      (Set.range (fun i : ℕ => Pi.single i (1 : ZMod 2)))
  let x : V := fun _ => 1
  have hfinite_support (y : V) (hy : y ∈ P) :
      Set.Finite {i | y i ≠ 0} := by
    change y ∈ Submodule.span (ZMod 2)
      (Set.range (fun i : ℕ => Pi.single i (1 : ZMod 2))) at hy
    refine Submodule.span_induction (p := fun z _ => Set.Finite {i | z i ≠ 0})
      ?_ ?_ ?_ ?_ hy
    · intro z hz
      obtain ⟨i, rfl⟩ := hz
      apply Set.Finite.subset (Set.finite_singleton i)
      intro j hj
      by_contra hji
      simp [Pi.single_apply, hji] at hj
    · apply Set.Finite.subset Set.finite_empty
      intro i hi
      change (0 : ZMod 2) ≠ 0 at hi
      simp at hi
    · intro u v _ _ hu hv
      apply Set.Finite.subset (hu.union hv)
      intro i hi
      by_contra h
      have hnot : i ∉ {j | u j ≠ 0} ∪ {j | v j ≠ 0} := h
      have hu0 : u i = 0 := by
        by_contra hu0
        exact hnot (Or.inl hu0)
      have hv0 : v i = 0 := by
        by_contra hv0
        exact hnot (Or.inr hv0)
      change u i + v i ≠ 0 at hi
      rw [hu0, hv0] at hi
      simp at hi
    · intro a z _ hz
      apply Set.Finite.subset hz
      intro i hi
      by_contra h
      have hz0 : z i = 0 := by
        by_contra hz0
        exact h hz0
      change a • z i ≠ 0 at hi
      rw [hz0] at hi
      simp at hi
  have hx_not_mem : x ∉ P := by
    intro hx
    have hs := hfinite_support x hx
    have huniv : {i | x i ≠ 0} = (Set.univ : Set ℕ) := by
      ext i
      simp [x]
    rw [huniv] at hs
    exact Set.infinite_univ.not_finite hs
  obtain ⟨f, hfx, hPker⟩ :=
    Submodule.exists_le_ker_of_notMem (K := ZMod 2) hx_not_mem
  let φ : Multiplicative V →* Multiplicative (ZMod 2) :=
    { toFun := fun y => Multiplicative.ofAdd (f (Multiplicative.toAdd y))
      map_one' := by simp
      map_mul' := by
        intro y z
        change Multiplicative.ofAdd
            (f (Multiplicative.toAdd y + Multiplicative.toAdd z)) =
          Multiplicative.ofAdd
            (f (Multiplicative.toAdd y) + f (Multiplicative.toAdd z))
        rw [map_add] }
  let H : Subgroup (Multiplicative V) := φ.ker
  have hPsub : (P : Set V) ⊆ (H : Set (Multiplicative V)) := by
    intro y hy
    change f y = 0
    exact hPker hy
  have hP_dense : Dense (P : Set V) := by
    intro y
    rw [mem_closure_iff_nhds]
    intro s hs
    obtain ⟨I, hI⟩ := exists_finset_piecewise_mem_of_mem_nhds hs (0 : V)
    have hsupport : Set.Finite {i | I.piecewise y 0 i ≠ 0} := by
      apply I.finite_toSet.subset
      intro i hi
      by_contra hnot
      have hi' : i ∈ I ∧ y i ≠ 0 := by
        simpa [Finset.piecewise, hnot] using hi
      exact hnot hi'.1
    have hspan : I.piecewise y 0 ∈ P := by
      let S := hsupport.toFinset
      have hzero : ∀ i, i ∉ S → I.piecewise y 0 i = 0 := by
        intro i hi
        by_contra hne
        exact hi (hsupport.mem_toFinset.mpr hne)
      have hsum : I.piecewise y 0 =
          Finset.sum S (fun i => (I.piecewise y 0 i) •
            Pi.single i (1 : ZMod 2)) := by
        ext i
        simp only [Finset.sum_apply]
        by_cases hi : i ∈ S
        · rw [Finset.sum_eq_single_of_mem i hi]
          · simp
          · intro j hj hji
            simp [hji.symm]
        · have hzsum : Finset.sum S (fun j =>
              ((I.piecewise y 0 j) • Pi.single j (1 : ZMod 2)) i) = 0 := by
            apply Finset.sum_eq_zero
            intro j hj
            have hji : j ≠ i := by
              intro hji
              exact hi (hji ▸ hj)
            simp [hji.symm]
          rw [hzsum]
          exact hzero i hi
      rw [hsum]
      exact P.sum_mem fun i hi =>
        P.smul_mem _ (show Pi.single i (1 : ZMod 2) ∈ P from
          Submodule.subset_span (Set.mem_range_self i))
    exact ⟨I.piecewise y 0, hI, hspan⟩
  have hH_dense : Dense (H : Set (Multiplicative V)) := by
    exact hP_dense.mono hPsub
  have hproper : H ≠ ⊤ := by
    intro htop
    have hxH : Multiplicative.ofAdd x ∈ H := by
      rw [htop]
      trivial
    change f x = 0 at hxH
    exact hfx hxH
  have hfinite : Finite ((Multiplicative V) ⧸ H) := by
    let _ : Finite φ.range :=
      Finite.of_injective Subtype.val Subtype.coe_injective
    let e := QuotientGroup.quotientKerEquivRange φ
    exact Finite.of_injective e e.injective
  refine ⟨H, hfinite, ?_⟩
  intro hopen
  have hclosed : IsClosed (H : Set (Multiplicative V)) :=
    Subgroup.isClosed_of_isOpen H hopen
  apply hproper
  ext y
  change y ∈ (H : Set (Multiplicative V)) ↔ y ∈ (Set.univ : Set (Multiplicative V))
  rw [← hclosed.closure_eq, hH_dense.closure_eq]

/- A dense proper subgroup of a Hausdorff compact group is not closed.  This
   is the topological obstruction behind the warning about algebraically
   generated candidates for norm groups. -/
theorem chapter02_dense_proper_subgroup_not_closed
    {G : Type*} [Group G] [TopologicalSpace G] [T2Space G]
    (H : Subgroup G) (hdense : Dense (H : Set G)) (hproper : H ≠ ⊤) :
    ¬IsClosed (H : Set G) := by
  intro hclosed
  apply hproper
  ext x
  change x ∈ (H : Set G) ↔ x ∈ (Set.univ : Set G)
  rw [← hclosed.closure_eq, hdense.closure_eq]

theorem chapter02_norm_candidate_with_dense_unit_part_not_closed
    {K : Type*} [Field K] [TopologicalSpace Kˣ] [T2Space Kˣ]
    (H : Subgroup Kˣ) (hdense : Dense (H : Set Kˣ))
    (hproper : H ≠ ⊤) : ¬IsClosed (H : Set Kˣ) := by
  exact chapter02_dense_proper_subgroup_not_closed H hdense hproper

end

end LastLib.Book05LocalClassFieldTheory.Chapter02
