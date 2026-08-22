import LastLib.Book04AdelesAndIdeles.Chapter04.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter04

noncomputable section

open Set Filter
open NumberField IsDedekindDomain
open scoped BigOperators Topology RestrictedProduct

/-! ### 4.2 The full adele ring -/

theorem chapter04_adeleRing_is_infinite_times_finite
    (K : Type*) [Field K] [NumberField K] :
    Chapter04AdeleRing K =
      (Chapter04InfiniteAdeleRing K × Chapter04FiniteAdeleRing K) := by
  rfl

def chapter04AdeleRingProductEquiv
    (K : Type*) [Field K] [NumberField K] :
    Chapter04AdeleRing K ≃+*
      Chapter04InfiniteAdeleRing K × Chapter04FiniteAdeleRing K :=
  RingEquiv.refl _

theorem chapter04_adeleRing_productEquiv_apply
    (K : Type*) [Field K] [NumberField K]
    (x : Chapter04AdeleRing K) :
    chapter04AdeleRingProductEquiv K x = (x.1, x.2) := by
  rfl

theorem chapter04_all_place_restrictedProduct_equiv_adeleRing
    (K : Type*) [Field K] [NumberField K] :
    Nonempty (Chapter04AllPlaceRestrictedProduct K ≃+*
      Chapter04AdeleRing K) := by
  let e : Chapter04AllPlaceRestrictedProduct K ≃+* Chapter04AdeleRing K :=
    { toFun := fun x =>
        (fun v : Chapter04InfinitePlace K => x (Sum.inr v),
          ⟨fun v : Chapter04FinitePlace K => x (Sum.inl v), by
            have h := Sum.inl_injective.tendsto_cofinite x.2
            filter_upwards [h] with v hv
            change x (Sum.inl v) ∈ chapter04LocalIntegralSubring K (Sum.inl v) at hv
            have hv' : x (Sum.inl v) ∈ v.adicCompletionIntegers K :=
              (ValuationSubring.mem_toSubring (v.adicCompletionIntegers K) _).mp hv
            change x (Sum.inl v) ∈ (v.adicCompletionIntegers K).carrier
            exact (ValuationSubring.mem_carrier (v.adicCompletionIntegers K) _).mpr hv'⟩)
      invFun := fun x =>
        ⟨fun v => match v with
          | Sum.inl w => x.2 w
          | Sum.inr w => x.1 w, by
            rw [Filter.eventually_cofinite]
            apply (chapter04_finiteAdele_exceptionalSet_finite K x.2).image
              Sum.inl |>.subset
            intro v hv
            cases v with
            | inl w =>
                have hv' : x.2 w ∉ w.adicCompletionIntegers K := by
                  intro hw
                  apply hv
                  change x.2 w ∈ chapter04LocalIntegralSubring K (Sum.inl w)
                  exact (ValuationSubring.mem_toSubring (w.adicCompletionIntegers K) _).mpr hw
                exact ⟨w, by
                  change x.2 w ∉ (w.adicCompletionIntegers K : Set _)
                  exact hv', rfl⟩
            | inr w =>
                exact (hv (by exact Set.mem_univ _)).elim⟩
      left_inv := by
        intro x
        apply RestrictedProduct.ext
        intro v
        cases v <;> rfl
      right_inv := by
        intro x
        apply Prod.ext
        · rfl
        · apply chapter04_finiteAdele_ext K
          intro v
          rfl
      map_mul' x y := by
        apply chapter04_adeleRing_ext K
        · funext v
          rfl
        · apply chapter04_finiteAdele_ext K
          intro v
          rfl
      map_add' x y := by
        apply chapter04_adeleRing_ext K
        · funext v
          rfl
        · apply chapter04_finiteAdele_ext K
          intro v
          rfl }
  exact ⟨e⟩

theorem chapter04_adeleRing_is_locally_compact_topological_ring
    (K : Type*) [Field K] [NumberField K] :
      LocallyCompactSpace (Chapter04AdeleRing K) ∧
      IsTopologicalRing (Chapter04AdeleRing K) := by
  let hfinite : LocallyCompactSpace (Chapter04FiniteAdeleRing K) :=
    (chapter04_finiteAdeleRing_is_locally_compact_topological_ring K).1
  change LocallyCompactSpace
      (Chapter04InfiniteAdeleRing K × Chapter04FiniteAdeleRing K) ∧
    IsTopologicalRing (Chapter04InfiniteAdeleRing K × Chapter04FiniteAdeleRing K)
  exact ⟨@Prod.locallyCompactSpace _ _ _ _ inferInstance hfinite, inferInstance⟩

theorem chapter04_adeleRing_multiplication_is_continuous
    (K : Type*) [Field K] [NumberField K] :
    Continuous (fun p : Chapter04AdeleRing K × Chapter04AdeleRing K =>
      p.1 * p.2) := by
  exact continuous_mul

def chapter04FullBasicOpen
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K))
    (U : ∀ v : Chapter04Place K, Set (chapter04LocalField K v)) :
    Set (Chapter04AdeleRing K) :=
  {x |
    (∀ v, v ∈ S → chapter04AdeleCoordinate K x v ∈ U v) ∧
      (∀ v : Chapter04FinitePlace K, Sum.inl v ∉ S →
        x.2 v ∈ chapter04FiniteLocalIntegerSet K v)}

def chapter04FullBasicOpenCondition
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K))
    (U : ∀ v : Chapter04Place K, Set (chapter04LocalField K v)) : Prop :=
  S.Finite ∧
    (∀ v, v ∈ S → IsOpen (U v)) ∧
    (∀ w : Chapter04InfinitePlace K, Sum.inr w ∈ S)

theorem chapter04_mem_fullBasicOpen_iff
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K))
    (U : ∀ v : Chapter04Place K, Set (chapter04LocalField K v))
    (x : Chapter04AdeleRing K) :
    x ∈ chapter04FullBasicOpen K S U ↔
      (∀ v, v ∈ S → chapter04AdeleCoordinate K x v ∈ U v) ∧
        (∀ v : Chapter04FinitePlace K, Sum.inl v ∉ S →
          x.2 v ∈ chapter04FiniteLocalIntegerSet K v) :=
  Iff.rfl

theorem chapter04_fullBasicOpen_isOpen
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K))
    (U : ∀ v : Chapter04Place K, Set (chapter04LocalField K v))
    (hU : chapter04FullBasicOpenCondition K S U) :
    IsOpen (chapter04FullBasicOpen K S U) := by
  let T : Set (Chapter04InfinitePlace K) := Sum.inr ⁻¹' S
  let CInf : Set (Chapter04InfiniteAdeleRing K) :=
    Set.pi T (fun v => U (Sum.inr v))
  let F : Set (Chapter04FinitePlace K) := Sum.inl ⁻¹' S
  let D : Set (Chapter04FiniteAdeleRing K) :=
    {y | ∀ v : Chapter04FinitePlace K, v ∈ F →
      y v ∈ U (Sum.inl v)}
  let Tail : Set (Chapter04FiniteAdeleRing K) :=
    {y | ∀ v : Chapter04FinitePlace K, Sum.inl v ∉ S →
      y v ∈ chapter04FiniteLocalIntegerSet K v}
  let CFin : Set (Chapter04FiniteAdeleRing K) := D ∩ Tail
  have hT : T.Finite := by
    exact hU.1.preimage Sum.inr_injective.injOn
  have hF : F.Finite := by
    exact hU.1.preimage Sum.inl_injective.injOn
  have hCInf : IsOpen CInf := by
    apply isOpen_set_pi hT
    intro v hv
    exact hU.2.1 (Sum.inr v) hv
  have hAopen : ∀ v : Chapter04FinitePlace K,
      IsOpen (chapter04FiniteLocalIntegerSet K v) := by
    intro v
    exact Valued.isOpen_valuationSubring _
  have hD : IsOpen D := by
    have hD' : IsOpen (⋂ v : Chapter04FinitePlace K, ⋂ _ : v ∈ F,
        (fun y : Chapter04FiniteAdeleRing K => y v) ⁻¹' U (Sum.inl v)) := by
      exact hF.isOpen_biInter fun v hv =>
        (hU.2.1 (Sum.inl v) (by exact hv)).preimage
          (RestrictedProduct.continuous_eval v)
    have hDeq : D = ⋂ v : Chapter04FinitePlace K, ⋂ _ : v ∈ F,
        (fun y : Chapter04FiniteAdeleRing K => y v) ⁻¹' U (Sum.inl v) := by
      ext y
      simp only [D, Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro hy i hi
        exact hy i hi
      · intro hy i hi
        exact hy i hi
    rw [hDeq]
    exact hD'
  have hCFin : IsOpen CFin := by
    exact hD.inter (RestrictedProduct.isOpen_forall_imp_mem hAopen)
  have hEq : chapter04FullBasicOpen K S U = CInf ×ˢ CFin := by
    ext x
    constructor
    · intro hx
      constructor
      · intro v hv
        exact hx.1 (Sum.inr v) hv
      · refine ⟨?_, ?_⟩
        · intro v hv
          change (x.2 v : chapter04LocalField K (Sum.inl v)) ∈ U (Sum.inl v)
          exact hx.1 (Sum.inl v) (by simpa [F] using hv)
        · exact hx.2
    · rintro ⟨hxInf, hxFin⟩
      constructor
      · intro v hv
        cases v with
        | inl w =>
            by_cases hw : Sum.inl w ∈ S
            · change (x.2 w : chapter04LocalField K (Sum.inl w)) ∈ U (Sum.inl w)
              exact hxFin.1 w (by simpa [F] using hw)
            · exact (hw hv).elim
        | inr w => exact hxInf w hv
      · exact hxFin.2
  rw [hEq]
  exact hCInf.prod hCFin

private def chapter04RestrictedProductBasicOpenShared
    {ι : Type*} (R : ι → Type*) (A : (i : ι) → Set (R i))
    (S : Set ι) (U : (i : ι) → Set (R i)) :
    Set (Πʳ i, [R i, A i]) :=
  {x | (∀ i ∈ S, x i ∈ U i) ∧ ∀ i ∉ S, x i ∈ A i}

private theorem chapter04_restrictedProduct_basicOpen_basis_shared
    {ι : Type*} (R : ι → Type*) (A : (i : ι) → Set (R i))
    [∀ i, TopologicalSpace (R i)] (hA : ∀ i, IsOpen (A i)) :
    ∀ x : Πʳ i, [R i, A i], ∀ V ∈ 𝓝 x,
      ∃ S : Set ι, S.Finite ∧ ∃ U : (i : ι) → Set (R i),
        (∀ i, IsOpen (U i)) ∧
          x ∈ chapter04RestrictedProductBasicOpenShared R A S U ∧
            chapter04RestrictedProductBasicOpenShared R A S U ⊆ V := by
  classical
  intro x V hV
  rcases mem_nhds_iff.mp hV with ⟨W, hWV, hWopen, hxW⟩
  let T : Set ι := {i | x i ∈ A i}
  have hT : cofinite ≤ 𝓟 T := by
    apply le_principal_iff.mpr
    change ∀ᶠ i in cofinite, x i ∈ A i
    exact x.2
  have hxT : ∀ᶠ i in 𝓟 T, x i ∈ A i :=
    Filter.mem_principal.mpr subset_rfl
  rcases RestrictedProduct.exists_inclusion_eq_of_eventually R A hT hxT with ⟨x', hxx⟩
  have hle :
      TopologicalSpace.coinduced (RestrictedProduct.inclusion R A hT)
          (RestrictedProduct.topologicalSpace R A (𝓟 T)) ≤
        (inferInstance : TopologicalSpace (Πʳ i, [R i, A i])) := by
    change TopologicalSpace.coinduced (RestrictedProduct.inclusion R A hT)
          (RestrictedProduct.topologicalSpace R A (𝓟 T)) ≤
        RestrictedProduct.topologicalSpace R A cofinite
    rw [RestrictedProduct.topologicalSpace_eq_iSup cofinite]
    exact le_iSup_of_le T (le_iSup_of_le hT le_rfl)
  have hWcomp : IsOpen[
      TopologicalSpace.coinduced (RestrictedProduct.inclusion R A hT)
        (RestrictedProduct.topologicalSpace R A (𝓟 T))] W :=
    hle W hWopen
  have hpre : IsOpen[RestrictedProduct.topologicalSpace R A (𝓟 T)]
      (RestrictedProduct.inclusion R A hT ⁻¹' W) :=
    isOpen_coinduced.mp hWcomp
  rw [RestrictedProduct.topologicalSpace_eq_of_principal] at hpre
  rcases isOpen_induced_iff.mp hpre with ⟨O, hO, hOeq⟩
  have hxpre : x' ∈ RestrictedProduct.inclusion R A hT ⁻¹' W := by
    change RestrictedProduct.inclusion R A hT x' ∈ W
    rw [hxx]
    exact hxW
  have hxO : (x' : ∀ i, R i) ∈ O := by
    have hxpre' := hxpre
    rw [← hOeq] at hxpre'
    exact hxpre'
  rcases isOpen_pi_iff.mp hO (x' : ∀ i, R i) hxO with ⟨J, q, hq, hqO⟩
  let S : Set ι := (J : Set ι) ∪ Tᶜ
  let U : (i : ι) → Set (R i) := fun i =>
    if i ∈ J then if i ∈ T then q i ∩ A i else q i else univ
  have hTcomp : Tᶜ.Finite := by
    change {i | x i ∉ A i}.Finite
    exact Filter.eventually_cofinite.mp x.2
  have hS : S.Finite := J.finite_toSet.union hTcomp
  have hU : ∀ i, IsOpen (U i) := by
    intro i
    by_cases hiJ : i ∈ J
    · by_cases hiT : i ∈ T
      · simpa [U, hiJ, hiT] using (hq i hiJ).1.inter (hA i)
      · simpa [U, hiJ, hiT] using (hq i hiJ).1
    · simp [U, hiJ]
  have hxB : x ∈ chapter04RestrictedProductBasicOpenShared R A S U := by
    constructor
    · intro i hiS
      by_cases hiJ : i ∈ J
      · have hxu : (x' : ∀ i, R i) i ∈ q i := (hq i hiJ).2
        have hxcoord : (x' : ∀ i, R i) i = x i := by
          simpa using congrArg (fun z : Πʳ i, [R i, A i] => z i) hxx
        rw [hxcoord] at hxu
        by_cases hiT : i ∈ T
        · simpa [U, hiJ, hiT] using And.intro hxu (show x i ∈ A i from hiT)
        · simpa [U, hiJ, hiT] using hxu
      · simp [S] at hiS
        simp [U, hiJ]
    · intro i hiS
      have hiT : i ∈ T := by
        by_contra hiT
        exact hiS (by simp [S, hiT])
      exact hiT
  refine ⟨S, hS, U, hU, hxB, ?_⟩
  intro z hz
  have hzT : ∀ᶠ i in 𝓟 T, z i ∈ A i := by
    apply Filter.mem_principal.mpr
    intro i hiT
    by_cases hiJ : i ∈ J
    · have hzV : z i ∈ U i := hz.1 i (by simp [S, hiJ])
      have hzVA : z i ∈ q i ∩ A i := by
        simpa [U, hiJ, hiT] using hzV
      exact hzVA.2
    · exact hz.2 i (by simp [S, hiJ, hiT])
  rcases RestrictedProduct.exists_inclusion_eq_of_eventually R A hT hzT with ⟨z', hzz⟩
  have hzO : (z' : ∀ i, R i) ∈ O := by
    apply hqO
    intro i hiJ
    have hiJ' : i ∈ J := by simpa using hiJ
    have hiS : i ∈ S := Or.inl hiJ
    have hzV : z i ∈ U i := hz.1 i hiS
    have hzq : z i ∈ q i := by
      by_cases hiT : i ∈ T
      · exact (show z i ∈ q i ∩ A i by simpa [U, hiJ', hiT] using hzV).1
      · simpa [U, hiJ', hiT] using hzV
    have hzcoord : (z' : ∀ i, R i) i = z i := by
      simpa using congrArg (fun w : Πʳ i, [R i, A i] => w i) hzz
    rw [hzcoord]
    exact hzq
  have hzpre : z' ∈ RestrictedProduct.inclusion R A hT ⁻¹' W := by
    rw [← hOeq]
    exact hzO
  apply hWV
  change RestrictedProduct.inclusion R A hT z' ∈ W at hzpre
  simpa [hzz] using hzpre

theorem chapter04_full_adele_has_local_specification_basis
    (K : Type*) [Field K] [NumberField K]
    (x : Chapter04AdeleRing K) (V : Set (Chapter04AdeleRing K))
    (hV : V ∈ 𝓝 x) :
    ∃ S : Set (Chapter04Place K), ∃ U : ∀ v : Chapter04Place K,
      Set (chapter04LocalField K v),
      chapter04FullBasicOpenCondition K S U ∧
        x ∈ chapter04FullBasicOpen K S U ∧
          chapter04FullBasicOpen K S U ⊆ V := by
  classical
  rcases mem_nhds_iff.mp hV with ⟨W, hWV, hWopen, hxW⟩
  rcases mem_nhds_prod_iff'.mp (hWopen.mem_nhds hxW) with
    ⟨CInf, CFin, hCInfOpen, hxCInf, hCFinOpen, hxCFin, hprod⟩
  rcases isOpen_pi_iff.mp hCInfOpen x.1 hxCInf with ⟨J, q, hq, hqsub⟩
  have hAopen : ∀ v : Chapter04FinitePlace K,
      IsOpen (chapter04FiniteLocalIntegerSet K v) := by
    intro v
    exact Valued.isOpen_valuationSubring _
  rcases chapter04_restrictedProduct_basicOpen_basis_shared
      (fun v : Chapter04FinitePlace K => Chapter04FiniteLocalField K v)
      (fun v : Chapter04FinitePlace K => chapter04FiniteLocalIntegerSet K v)
      hAopen x.2 CFin (hCFinOpen.mem_nhds hxCFin) with
    ⟨Sf, hSf, Vf, hVf, hxF, hsubF⟩
  let S : Set (Chapter04Place K) := Set.range Sum.inr ∪ Sum.inl '' Sf
  let U : ∀ v : Chapter04Place K, Set (chapter04LocalField K v) := fun v =>
    match v with
    | Sum.inl w =>
        if w ∈ Sf then
          cast (by rfl : Set (Chapter04FiniteLocalField K w) =
            Set (chapter04LocalField K (Sum.inl w))) (Vf w)
        else Set.univ
    | Sum.inr w =>
        if w ∈ J then
          cast (by rfl : Set (InfinitePlace.Completion w) =
            Set (chapter04LocalField K (Sum.inr w))) (q w)
        else Set.univ
  have hS : S.Finite := by
    exact (Set.finite_range Sum.inr).union (hSf.image Sum.inl)
  have hUcond : chapter04FullBasicOpenCondition K S U := by
    refine ⟨hS, ?_, ?_⟩
    · intro v hv
      cases v with
      | inl w =>
          by_cases hw : w ∈ Sf
          · simp only [U]
            rw [if_pos hw]
            exact hVf w
          · simp [U, hw]
      | inr w =>
          by_cases hw : w ∈ J
          · simp only [U]
            rw [if_pos hw]
            exact (hq w hw).1
          · simp [U, hw]
    · intro w
      simp [S]
  have hxFull : x ∈ chapter04FullBasicOpen K S U := by
    constructor
    · intro v hv
      cases v with
      | inl w =>
          have hw : w ∈ Sf := by
            simpa [S] using hv
          simp only [U]
          rw [if_pos hw]
          rw [chapter04_adelic_coordinate_finite]
          exact hxF.1 w hw
      | inr w =>
          by_cases hw : w ∈ J
          · simp only [U]
            rw [if_pos hw]
            rw [chapter04_adelic_coordinate_infinite]
            exact (hq w hw).2
          · simp [U, hw]
    · intro v hv
      have hvf : v ∉ Sf := by
        intro hvf
        apply hv
        simp [S, hvf]
      exact hxF.2 v hvf
  refine ⟨S, U, hUcond, hxFull, ?_⟩
  intro y hy
  apply hWV
  apply hprod
  constructor
  · apply hqsub
    intro w hw
    have hwS : Sum.inr w ∈ S := by simp [S]
    have hyw := hy.1 (Sum.inr w) hwS
    have hwJ : w ∈ J := by simpa using hw
    simp only [U] at hyw
    rw [if_pos hwJ] at hyw
    rw [chapter04_adelic_coordinate_infinite] at hyw
    exact hyw
  · apply hsubF
    constructor
    · intro v hv
      have hvS : Sum.inl v ∈ S := by simp [S, hv]
      have hyv := hy.1 (Sum.inl v) hvS
      simp only [U] at hyv
      rw [if_pos hv] at hyv
      rw [chapter04_adelic_coordinate_finite] at hyv
      exact hyv
    · intro v hv
      have hvS : Sum.inl v ∉ S := by simp [S, hv]
      exact hy.2 v hvS

theorem chapter04_full_basic_open_has_finitely_many_delicate_coordinates
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K))
    (U : ∀ v : Chapter04Place K, Set (chapter04LocalField K v))
    (hU : chapter04FullBasicOpenCondition K S U) :
    S.Finite ∧
      (∀ w : Chapter04InfinitePlace K, Sum.inr w ∈ S) := by
  exact ⟨hU.1, hU.2.2⟩

def chapter04FullCompactProductSet
    (K : Type*) [Field K] [NumberField K]
    (CInf : Set (Chapter04InfiniteAdeleRing K)) :
    Set (Chapter04AdeleRing K) :=
  CInf ×ˢ (Chapter04FiniteIntegralAdeleSubring K : Set (Chapter04FiniteAdeleRing K))

theorem chapter04_full_compact_product_is_compact
    (K : Type*) [Field K] [NumberField K]
    (CInf : Set (Chapter04InfiniteAdeleRing K))
    (hC : IsCompact CInf) :
    IsCompact (chapter04FullCompactProductSet K CInf) := by
  exact hC.prod (chapter04_finiteIntegralAdele_is_compact_open K).1

theorem chapter04_full_compact_product_is_a_zero_neighborhood_iff
    (K : Type*) [Field K] [NumberField K]
    (CInf : Set (Chapter04InfiniteAdeleRing K)) :
    chapter04FullCompactProductSet K CInf ∈ 𝓝 (0 : Chapter04AdeleRing K) ↔
      CInf ∈ 𝓝 (0 : Chapter04InfiniteAdeleRing K) := by
  have hfinite : (Chapter04FiniteIntegralAdeleSubring K : Set
      (Chapter04FiniteAdeleRing K)) ∈ 𝓝 (0 : Chapter04FiniteAdeleRing K) := by
    exact (chapter04_finiteIntegralAdele_is_compact_open K).2.mem_nhds
      (Chapter04FiniteIntegralAdeleSubring K).zero_mem
  have hzero : (0 : Chapter04FiniteAdeleRing K) ∈
      (Chapter04FiniteIntegralAdeleSubring K : Set (Chapter04FiniteAdeleRing K)) :=
    (Chapter04FiniteIntegralAdeleSubring K).zero_mem
  constructor
  · intro hC
    have hmap : (fun y : Chapter04InfiniteAdeleRing K =>
        (y, (0 : Chapter04FiniteAdeleRing K))) ⁻¹'
          chapter04FullCompactProductSet K CInf ∈
        𝓝 (0 : Chapter04InfiniteAdeleRing K) :=
      (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds hC
    have heq : (fun y : Chapter04InfiniteAdeleRing K =>
        (y, (0 : Chapter04FiniteAdeleRing K))) ⁻¹'
          chapter04FullCompactProductSet K CInf = CInf := by
      ext y
      constructor
      · intro hy
        exact hy.1
      · intro hy
        exact ⟨hy, hzero⟩
    rw [heq] at hmap
    exact hmap
  · intro hC
    change chapter04FullCompactProductSet K CInf ∈
      𝓝 ((0 : Chapter04InfiniteAdeleRing K),
        (0 : Chapter04FiniteAdeleRing K))
    exact prod_mem_nhds hC hfinite

theorem chapter04_full_adele_has_no_compact_open_additive_subgroup
    (K : Type*) [Field K] [NumberField K] :
    ¬ ∃ H : AddSubgroup (Chapter04AdeleRing K),
      IsCompact (H : Set (Chapter04AdeleRing K)) ∧
        IsOpen (H : Set (Chapter04AdeleRing K)) := by
  classical
  intro h
  rcases h with ⟨H, hHcompact, hHopen⟩
  let fstHom : Chapter04AdeleRing K →+ Chapter04InfiniteAdeleRing K :=
    { toFun := Prod.fst
      map_zero' := rfl
      map_add' := by intro x y; rfl }
  let HInf : AddSubgroup (Chapter04InfiniteAdeleRing K) := H.map fstHom
  have hHInfCompact : IsCompact (HInf : Set (Chapter04InfiniteAdeleRing K)) := by
    have himage : IsCompact (Prod.fst '' (H : Set (Chapter04AdeleRing K))) :=
      hHcompact.image continuous_fst
    change IsCompact (Prod.fst '' (H : Set (Chapter04AdeleRing K)))
    exact himage
  have hHInfOpen : IsOpen (HInf : Set (Chapter04InfiniteAdeleRing K)) := by
    have himage : IsOpen (Prod.fst '' (H : Set (Chapter04AdeleRing K))) :=
      isOpenMap_fst _ hHopen
    change IsOpen (Prod.fst '' (H : Set (Chapter04AdeleRing K)))
    exact himage
  let hpath : ∀ v : Chapter04InfinitePlace K,
      PathConnectedSpace v.Completion := fun v => by
    rcases v.isReal_or_isComplex with hv | hv
    · exact Function.Surjective.pathConnectedSpace
        (f := (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm)
        (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.surjective
        (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous
    · exact Function.Surjective.pathConnectedSpace
        (f := (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).symm)
        (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).symm.surjective
        (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).symm.continuous
  let hPathInf : PathConnectedSpace (Chapter04InfiniteAdeleRing K) := by
    change PathConnectedSpace (∀ v : Chapter04InfinitePlace K, v.Completion)
    exact @Pi.instPathConnectedSpace _ _ _ hpath
  let hconnected : ConnectedSpace (Chapter04InfiniteAdeleRing K) :=
    @PathConnectedSpace.connectedSpace _ _ hPathInf
  have hHInfClopen : IsClopen (HInf : Set (Chapter04InfiniteAdeleRing K)) := by
    exact ⟨AddSubgroup.isClosed_of_isOpen HInf hHInfOpen, hHInfOpen⟩
  have hHInfUniv : (HInf : Set (Chapter04InfiniteAdeleRing K)) = Set.univ := by
    exact @IsClopen.eq_univ _ _ hconnected.toPreconnectedSpace
      (HInf : Set (Chapter04InfiniteAdeleRing K)) hHInfClopen
      ⟨0, HInf.zero_mem⟩
  let w : Chapter04InfinitePlace K := Classical.choice inferInstance
  have heval_surj : Function.Surjective
      (fun z : Chapter04InfiniteAdeleRing K => z w) := by
    intro y
    refine ⟨Function.update (0 : Chapter04InfiniteAdeleRing K) w y, ?_⟩
    simp [Function.update]
  have hcoord : IsCompact (Set.univ : Set w.Completion) := by
    have hcoord' : IsCompact ((fun z : Chapter04InfiniteAdeleRing K => z w) ''
        (HInf : Set (Chapter04InfiniteAdeleRing K))) :=
      hHInfCompact.image (continuous_apply w)
    rw [hHInfUniv] at hcoord'
    have himage : (fun z : Chapter04InfiniteAdeleRing K => z w) ''
        (Set.univ : Set (Chapter04InfiniteAdeleRing K)) = Set.univ := by
      rw [Set.image_univ]
      exact heval_surj.range_eq
    rw [himage] at hcoord'
    exact hcoord'
  rcases w.isReal_or_isComplex with hw | hw
  · have hcoordR : IsCompact (Set.univ : Set ℝ) := by
      have hcoordR' := hcoord.image
        (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hw).continuous
      have himage :
          (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hw :
            w.Completion → ℝ) ''
          (Set.univ : Set w.Completion) = Set.univ := by
        rw [Set.image_univ]
        exact
          (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hw).surjective.range_eq
      rw [himage] at hcoordR'
      exact hcoordR'
    exact (IsCompact.ne_univ hcoordR) rfl
  · have hcoordC : IsCompact (Set.univ : Set ℂ) := by
      have hcoordC' := hcoord.image
        (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).continuous
      have himage :
          (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw :
            w.Completion → ℂ) ''
          (Set.univ : Set w.Completion) = Set.univ := by
        rw [Set.image_univ]
        exact Function.Surjective.range_eq
          (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).surjective
      rw [himage] at hcoordC'
      exact hcoordC'
    exact (IsCompact.ne_univ hcoordC) rfl

theorem chapter04_infiniteAdeleRing_has_no_compact_open_additive_subgroup
    (K : Type*) [Field K] [NumberField K] :
    ¬ ∃ H : AddSubgroup (Chapter04InfiniteAdeleRing K),
      IsCompact (H : Set (Chapter04InfiniteAdeleRing K)) ∧
        IsOpen (H : Set (Chapter04InfiniteAdeleRing K)) := by
  sorry

theorem chapter04_full_compact_product_neighborhood_is_not_a_subgroup
    (K : Type*) [Field K] [NumberField K]
    (CInf : Set (Chapter04InfiniteAdeleRing K))
    (hC : IsCompact CInf)
    (hnhds : chapter04FullCompactProductSet K CInf ∈
      𝓝 (0 : Chapter04AdeleRing K)) :
    ¬ ∃ H : AddSubgroup (Chapter04AdeleRing K),
      (H : Set (Chapter04AdeleRing K)) = chapter04FullCompactProductSet K CInf := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter04
