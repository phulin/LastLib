import LastLib.Book04AdelesAndIdeles.Chapter11.Dependencies
import Mathlib.Topology.Algebra.Ring.Compact

namespace LastLib.Book04AdelesAndIdeles.Chapter11

open NumberField
open scoped BigOperators nonZeroDivisors RestrictedProduct

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-! ## 11.2 Local congruence groups -/

theorem chapter11_local_unit_level_zero_is_full_unit_group
    {A : Type*} [CommRing A] [IsLocalRing A] :
    chapter11LocalUnitFiltration (A := A) 0 = ⊤ := by
  exact chapter11LocalUnitFiltration_zero

theorem chapter11_local_unit_positive_level_is_one_plus_maximal_power
    {A : Type*} [CommRing A] [IsLocalRing A] {n : ℕ} (hn : n ≠ 0) (u : Aˣ) :
    u ∈ chapter11LocalUnitFiltration (A := A) n ↔
      (u : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ n := by
  rw [chapter11LocalUnitFiltration_mem_iff]
  simp [hn]

theorem chapter11_local_unit_positive_level_is_one_plus_an_element_of_the_power
    {A : Type*} [CommRing A] [IsLocalRing A] {n : ℕ} (hn : n ≠ 0) (u : Aˣ) :
    u ∈ chapter11LocalUnitFiltration (A := A) n ↔
      ∃ z : A, z ∈ (IsLocalRing.maximalIdeal A) ^ n ∧ (u : A) = 1 + z := by
  rw [chapter11LocalUnitFiltration_mem_iff]
  simp only [hn, false_or]
  constructor
  · intro hu
    refine ⟨(u : A) - 1, hu, ?_⟩
    ring
  · rintro ⟨z, hz, huz⟩
    rw [huz]
    simpa using hz

theorem chapter11_finite_local_level_zero_is_integral_unit_condition
    (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    chapter11FiniteLocalUnitGroup K v 0 =
      (v.adicCompletionIntegers K).unitGroup := by
  exact chapter11FiniteLocalUnitGroup_zero K v

theorem chapter11_finite_local_level_one_is_principal_unit_condition
    (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    chapter11FiniteLocalUnitGroup K v 1 =
      (v.adicCompletionIntegers K).principalUnitGroup := by
  exact chapter11FiniteLocalUnitGroup_one K v

theorem chapter11_ray_unit_subgroup_mem_iff (m : RayModulus K)
    (x : Chapter11IdeleGroup K) :
    x ∈ chapter11RayUnitSubgroup m ↔
      ((∀ v, chapter11IdeleFiniteComponent K v x ∈
          chapter11FiniteLocalUnitGroup K v (m.finiteExponent v)) ∧
        (∀ v (hv : v ∈ m.infinitePart),
          chapter11RealSignComponent K v (m.infinitePart_isReal v hv) x = 1)) := by
  rfl

theorem chapter11_ray_unit_condition_at_selected_real_place
    (m : RayModulus K) {v : NumberField.InfinitePlace K}
    (hv : v ∈ m.infinitePart) {x : Chapter11IdeleGroup K} :
    x ∈ chapter11RayUnitSubgroup m →
      chapter11RealSignComponent K v (m.infinitePart_isReal v hv) x = 1 := by
  intro hx
  exact hx.2 v hv

theorem chapter11_ray_unit_subgroup_is_open (m : RayModulus K) :
    IsOpen (chapter11RayUnitSubgroup m : Set (Chapter11IdeleGroup K)) := by
  classical
  have hlocal : ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (n : ℕ),
      IsOpen (chapter11FiniteLocalUnitGroup K v n :
        Set ((v.adicCompletion K)ˣ)) := by
    intro v n
    let A := v.adicCompletionIntegers K
    let L := v.adicCompletion K
    by_cases hn0 : n = 0
    · subst n
      rw [chapter11FiniteLocalUnitGroup_zero K v]
      have hA : IsOpen (A : Set L) :=
        Valued.isOpen_valuationSubring L
      have hU : IsOpen (((Submonoid.ofClass A).units :
          Set Lˣ)) := Submonoid.isOpen_units hA
      have heq : (A.unitGroup : Set Lˣ) =
          ((Submonoid.ofClass A).units : Set Lˣ) := by
        ext x
        change x ∈ A.unitGroup ↔ x ∈ (Submonoid.ofClass A).units
        constructor
        · intro hx
          have hxval : A.valuation (x : L) = 1 :=
            (ValuationSubring.mem_unitGroup_iff A x).1 hx
          have hxi_le : A.valuation ((x⁻¹ : Lˣ) : L) ≤ 1 := by
            rw [Units.val_inv_eq_inv_val x, map_inv₀, hxval, inv_one]
          exact ⟨
            (A.valuation_le_one_iff _).1 hxval.le,
            (A.valuation_le_one_iff _).1 hxi_le⟩
        · intro hx
          rcases (Submonoid.mem_units_iff (Submonoid.ofClass A) x).mp hx with
            ⟨hxA, hxi⟩
          change (x : L) ∈ A at hxA
          change ((x⁻¹ : Lˣ) : L) ∈ A at hxi
          let u : Aˣ :=
            { val := ⟨(x : L), hxA⟩
              inv := ⟨((x⁻¹ : Lˣ) : L), hxi⟩
              val_inv := by
                apply Subtype.ext
                exact x.val_inv
              inv_val := by
                apply Subtype.ext
                exact x.inv_val }
          let y : A.unitGroup := A.unitGroupMulEquiv.symm u
          have hy : (y : Lˣ) = x := by
            apply Units.ext
            rfl
          exact hy ▸ y.property
      rw [heq]
      exact hU
    · let W : Set L :=
        (fun z : A => (z : L)) ''
          (((IsLocalRing.maximalIdeal A) ^ n : Ideal A) : Set A)
      have hsub : IsCompact (Set.univ : Set A) := by
        apply Subtype.isCompact_iff.mpr
        convert
          (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09_adic_completion_integers_compact K v)
            using 1
        ext z
        constructor
        · rintro ⟨x, -, rfl⟩
          exact x.property
        · intro hz
          exact ⟨⟨z, hz⟩, Set.mem_univ _, rfl⟩
      let compactA : CompactSpace A := ⟨hsub⟩
      have hpow : IsOpen (((IsLocalRing.maximalIdeal A) ^ n : Ideal A) : Set A) :=
        @IsLocalRing.isOpen_maximalIdeal_pow A _ _ _ compactA _ _ _ n
      have hW : IsOpen W := by
        dsimp [W]
        exact (Valued.isOpen_valuationSubring L).isOpenEmbedding_subtypeVal.isOpenMap
          _ hpow
      have heq : (chapter11FiniteLocalUnitGroup K v n : Set Lˣ) =
          (fun x : Lˣ => (x : L) - 1) ⁻¹' W := by
        ext x
        constructor
        · rintro ⟨u, hu, rfl⟩
          obtain ⟨z, hz, huz⟩ :=
            (chapter11_local_unit_positive_level_is_one_plus_an_element_of_the_power
              hn0 u).1 hu
          refine ⟨z, hz, ?_⟩
          change (z : L) = ((u : A) : L) - 1
          rw [huz]
          simp [sub_eq_add_neg, add_assoc]
        · intro hx
          dsimp [W] at hx
          rcases hx with ⟨z, hz, hxz⟩
          have hxz' : (z : L) = (x : L) - 1 := by simpa using hxz
          have hzmax : z ∈ IsLocalRing.maximalIdeal A := by
            have hpow_le : (IsLocalRing.maximalIdeal A) ^ n ≤
                IsLocalRing.maximalIdeal A := by
              simpa [pow_one] using
                (Ideal.pow_le_pow_right (Nat.one_le_iff_ne_zero.mpr hn0) :
                  (IsLocalRing.maximalIdeal A) ^ n ≤
                    (IsLocalRing.maximalIdeal A) ^ 1)
            exact hpow_le hz
          have hvalz : A.valuation (z : L) < 1 :=
            (ValuationSubring.valuation_lt_one_iff A z).1 hzmax
          have hxval : A.valuation (x : L) = 1 := by
            have hxone : (x : L) = 1 + (z : L) := by
              calc
                (x : L) = ((x : L) - 1) + 1 := by ring
                _ = (z : L) + 1 := by rw [← hxz']
                _ = 1 + (z : L) := by ring
            rw [hxone]
            exact A.valuation.map_one_add_of_lt hvalz
          have hxA : (x : L) ∈ A :=
            (A.valuation_le_one_iff _).1 hxval.le
          have hxiA : ((x⁻¹ : Lˣ) : L) ∈ A := by
            rw [← A.valuation_le_one_iff, Units.val_inv_eq_inv_val, map_inv₀, hxval, inv_one]
          let u : Aˣ :=
            { val := ⟨(x : L), hxA⟩
              inv := ⟨((x⁻¹ : Lˣ) : L), hxiA⟩
              val_inv := by
                apply Subtype.ext
                exact x.val_inv
              inv_val := by
                apply Subtype.ext
                exact x.inv_val }
          have hu : u ∈ chapter11LocalUnitFiltration (A := A) n := by
            apply
              (chapter11_local_unit_positive_level_is_one_plus_an_element_of_the_power
                hn0 u).2
            refine ⟨z, hz, ?_⟩
            apply Subtype.ext
            change (x : L) = 1 + (z : L)
            calc
              (x : L) = ((x : L) - 1) + 1 := by ring
              _ = (z : L) + 1 := by rw [← hxz']
              _ = 1 + (z : L) := by ring
          refine ⟨u, hu, ?_⟩
          apply Units.ext
          rfl
      rw [heq]
      exact hW.preimage (Units.continuous_val.sub continuous_const)
  let B : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      Set ((v.adicCompletion K)ˣ) :=
    fun v => (Submonoid.ofClass (v.adicCompletionIntegers K)).units
  let H : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      Set ((v.adicCompletion K)ˣ) :=
    fun v => chapter11FiniteLocalUnitGroup K v (m.finiteExponent v)
  have hzero : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      (chapter11FiniteLocalUnitGroup K v 0 :
        Set ((v.adicCompletion K)ˣ)) = B v := by
    intro v
    let A := v.adicCompletionIntegers K
    let L := v.adicCompletion K
    rw [chapter11FiniteLocalUnitGroup_zero K v]
    change (A.unitGroup : Set Lˣ) =
      ((Submonoid.ofClass A).units : Set Lˣ)
    ext x
    change x ∈ A.unitGroup ↔ x ∈ (Submonoid.ofClass A).units
    constructor
    · intro hx
      have hxval : A.valuation (x : L) = 1 :=
        (ValuationSubring.mem_unitGroup_iff A x).1 hx
      have hxi_le : A.valuation ((x⁻¹ : Lˣ) : L) ≤ 1 := by
        rw [Units.val_inv_eq_inv_val x, map_inv₀, hxval, inv_one]
      exact ⟨
        (A.valuation_le_one_iff _).1 hxval.le,
        (A.valuation_le_one_iff _).1 hxi_le⟩
    · intro hx
      rcases (Submonoid.mem_units_iff (Submonoid.ofClass A) x).mp hx with
        ⟨hxA, hxi⟩
      change (x : L) ∈ A at hxA
      change ((x⁻¹ : Lˣ) : L) ∈ A at hxi
      let u : Aˣ :=
        { val := ⟨(x : L), hxA⟩
          inv := ⟨((x⁻¹ : Lˣ) : L), hxi⟩
          val_inv := by
            apply Subtype.ext
            exact x.val_inv
          inv_val := by
            apply Subtype.ext
            exact x.inv_val }
      let y : A.unitGroup := A.unitGroupMulEquiv.symm u
      have hy : (y : Lˣ) = x := by
        apply Units.ext
        rfl
      exact hy ▸ y.property
  let RP :=
    (Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      [(v.adicCompletion K)ˣ, B v])
  let U0 : Set RP :=
    {z | ∀ v, m.finiteExponent v = 0 → z.1 v ∈ B v}
  have hB : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), IsOpen (B v) := by
    intro v
    exact Submonoid.isOpen_units (Valued.isOpen_valuationSubring (v.adicCompletion K))
  have hU0 : IsOpen U0 := by
    dsimp [U0]
    exact RestrictedProduct.isOpen_forall_imp_mem hB
  have hUv : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      IsOpen {z : RP | z.1 v ∈ H v} := by
    intro v
    exact (hlocal v (m.finiteExponent v)).preimage
      (show Continuous (fun z : RP => z.1 v) from
        (continuous_apply v).comp
          (RestrictedProduct.continuous_coe
            (R := fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
              (v.adicCompletion K)ˣ)
            (A := B) (𝓕 := Filter.cofinite)))
  let U : Set RP :=
    U0 ∩ ⋂ v ∈ m.finiteExponent.support, {z : RP | z.1 v ∈ H v}
  have hU : IsOpen U := by
    dsimp [U]
    exact hU0.inter (m.finiteExponent.support.finite_toSet.isOpen_biInter
      fun v hv => hUv v)
  have hU_eq : U = {z : RP | ∀ v, z.1 v ∈ H v} := by
    ext z
    constructor
    · rintro ⟨hz0, hzS⟩
      have hzS' : ∀ v, v ∈ m.finiteExponent.support → z.1 v ∈ H v := by
        intro v hv
        exact Set.mem_iInter.mp (Set.mem_iInter.mp hzS v) hv
      intro v
      by_cases hv : v ∈ m.finiteExponent.support
      · exact hzS' v hv
      · have hv0 : m.finiteExponent v = 0 :=
          Finsupp.notMem_support_iff.mp hv
        have hzB : z.1 v ∈ B v := hz0 v hv0
        have hHv : H v = B v := by
          dsimp [H, B]
          rw [hv0]
          exact hzero v
        rw [hHv]
        exact hzB
    · intro hz
      refine ⟨?_, ?_⟩
      · intro v hv0
        have hzv := hz v
        have hHv : H v = B v := by
          dsimp [H, B]
          rw [hv0]
          exact hzero v
        rw [hHv] at hzv
        exact hzv
      · refine Set.mem_iInter.mpr fun v => Set.mem_iInter.mpr fun hv => hz v
  have hfinite : IsOpen ({x : Chapter11FiniteIdeleGroup K |
      ∀ v, chapter11FiniteIdeleComponent K v x ∈ H v} :
        Set (Chapter11FiniteIdeleGroup K)) := by
    have heq : ({x : Chapter11FiniteIdeleGroup K |
        ∀ v, chapter11FiniteIdeleComponent K v x ∈ H v} :
          Set (Chapter11FiniteIdeleGroup K)) =
        (RestrictedProduct.unitsEquiv
          (𝓕 := Filter.cofinite)
          (B := fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
            v.adicCompletionIntegers K)
          (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
            v.adicCompletion K)) ⁻¹' U := by
      ext x
      rw [hU_eq]
      change (∀ v, chapter11FiniteIdeleComponent K v x ∈ H v) ↔
        (∀ v, (RestrictedProduct.unitsEquiv
          (𝓕 := Filter.cofinite)
          (B := fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
            v.adicCompletionIntegers K)
          (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
            v.adicCompletion K) x v) ∈ H v)
      constructor
      · intro hx v
        have he := RestrictedProduct.unitsEquiv_apply
          (R := fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
            v.adicCompletion K) v x
        have he' : RestrictedProduct.unitsEquiv
              (𝓕 := Filter.cofinite)
              (B := fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
                v.adicCompletionIntegers K)
              (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
                v.adicCompletion K) x v = chapter11FiniteIdeleComponent K v x := by
          apply Units.ext
          exact he
        rw [he']
        exact hx v
      · intro hx v
        have he := RestrictedProduct.unitsEquiv_apply
          (R := fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
            v.adicCompletion K) v x
        have he' : RestrictedProduct.unitsEquiv
              (𝓕 := Filter.cofinite)
              (B := fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
                v.adicCompletionIntegers K)
              (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
                v.adicCompletion K) x v = chapter11FiniteIdeleComponent K v x := by
          apply Units.ext
          exact he
        have hxv := hx v
        rw [he'] at hxv
        exact hxv
    rw [heq]
    exact isOpen_induced hU
  let S : ∀ v : NumberField.InfinitePlace K,
      Set ((LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K)ˣ) :=
    fun v => if hv : v ∈ m.infinitePart then
      {z |
        SignType.sign
            (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
              (m.infinitePart_isReal v hv)
                ((z : LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K) v)) = 1}
    else Set.univ
  have hSv : ∀ v : NumberField.InfinitePlace K, IsOpen (S v) := by
    intro v
    by_cases hv : v ∈ m.infinitePart
    · simp only [S]
      rw [dif_pos hv]
      let f : (LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K)ˣ → ℝ := fun z =>
        NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
          (m.infinitePart_isReal v hv)
            ((z : LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K) v)
      have hf : Continuous f := by
        dsimp [f]
        exact
          (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
            (m.infinitePart_isReal v hv)).continuous.comp
            ((continuous_apply v).comp Units.continuous_val)
      have heq : {z : (LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K)ˣ |
          SignType.sign
              (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
                (m.infinitePart_isReal v hv)
                  ((z : LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K) v)) = 1} =
          f ⁻¹' Set.Ioi (0 : ℝ) := by
        ext z
        change SignType.sign (f z) = 1 ↔ 0 < f z
        exact sign_eq_one_iff
      rw [heq]
      exact isOpen_Ioi.preimage hf
    · simp only [S]
      rw [dif_neg hv]
      exact isOpen_univ
  let V : Set ((LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K)ˣ) :=
    ⋂ v ∈ m.infinitePart, S v
  have hV : IsOpen V := by
    dsimp [V]
    exact m.infinitePart.finite_toSet.isOpen_biInter fun v hv => hSv v
  let F : Set (Chapter11FiniteIdeleGroup K) :=
    {y | ∀ v, chapter11FiniteIdeleComponent K v y ∈ H v}
  have hF : IsOpen F := by
    simpa [F] using hfinite
  let e := LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K
  have he : Continuous (e : Chapter11IdeleGroup K →
      (LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K)ˣ ×
        Chapter11FiniteIdeleGroup K) := by
    exact continuous_induced_dom
  let I : Set (Chapter11IdeleGroup K) :=
    {x | (e x).1 ∈ V}
  let J : Set (Chapter11IdeleGroup K) :=
    {x | (e x).2 ∈ F}
  have hI : IsOpen I := by
    dsimp [I]
    exact hV.preimage (continuous_fst.comp he)
  have hJ : IsOpen J := by
    dsimp [J]
    exact hF.preimage (continuous_snd.comp he)
  have hset : (chapter11RayUnitSubgroup m : Set (Chapter11IdeleGroup K)) =
      I ∩ J := by
    ext x
    constructor
    · intro hx
      refine ⟨?_, ?_⟩
      · dsimp [I, V]
        apply Set.mem_iInter.mpr
        intro v
        apply Set.mem_iInter.mpr
        intro hv
        simp only [S, dif_pos hv]
        have hs := hx.2 v hv
        have hs' := congrArg (fun z : SignTypeˣ => (z : SignType)) hs
        change SignType.sign
            (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
              (m.infinitePart_isReal v hv)
              (((x : Chapter11AdeleRing K).1) v)) = 1 at hs'
        change SignType.sign
            (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
              (m.infinitePart_isReal v hv)
              (((e x).1 :
                LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K) v)) = 1
        exact hs'
      · dsimp [J, F]
        intro v
        have hecomp : chapter11FiniteIdeleComponent K v (e x).2 =
            chapter11IdeleFiniteComponent K v x := by
          apply Units.ext
          rfl
        rw [hecomp]
        exact hx.1 v
    · rintro ⟨hxI, hxJ⟩
      refine ⟨?_, ?_⟩
      · intro v
        have hfv := hxJ v
        have hecomp : chapter11FiniteIdeleComponent K v (e x).2 =
            chapter11IdeleFiniteComponent K v x := by
          apply Units.ext
          rfl
        rw [hecomp] at hfv
        exact hfv
      · intro v hv
        change (e x).1 ∈ V at hxI
        have hs := Set.mem_iInter.mp (Set.mem_iInter.mp hxI v) hv
        have hs' : SignType.sign
            (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
              (m.infinitePart_isReal v hv)
              (((e x).1 :
                LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K) v)) = 1 := by
          simpa only [S, dif_pos hv, Set.mem_ofPred_eq] using hs
        apply Units.ext
        change SignType.sign
            (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
              (m.infinitePart_isReal v hv)
              (((x : Chapter11AdeleRing K).1) v)) = 1
        exact hs'
  rw [hset]
  exact hI.inter hJ

theorem chapter11_ray_class_group_is_the_idelic_quotient (m : RayModulus K) :
    chapter11RayClassGroup m =
      (Chapter11IdeleGroup K ⧸
        (chapter11PrincipalIdeleSubgroup (K := K) ⊔ chapter11RayUnitSubgroup m)) := by
  rfl

end
