import LastLib.Book04AdelesAndIdeles.Chapter11.Dependencies
import LastLib.Book04AdelesAndIdeles.Chapter05.Section05WeakApproximationAtArbitraryPlaces
import Mathlib.Topology.Algebra.Ring.Compact

namespace LastLib.Book04AdelesAndIdeles.Chapter11

open NumberField
open scoped Topology nonZeroDivisors

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-! ## 11.3 The ideal-theoretic description -/

theorem chapter11_ideal_prime_to_modulus_mem_iff (m : RayModulus K)
    (I : Chapter11FractionalIdealUnitGroup K) :
    I ∈ chapter11IdealPrimeToModulus m ↔
      ∀ v, m.finiteExponent v ≠ 0 →
        FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
  rfl

theorem chapter11_ray_principal_ideal_mem_iff (m : RayModulus K)
    (I : Chapter11IdealGroup m) :
    I ∈ chapter11RayPrincipalIdealSubgroup m ↔
      ∃ a : Kˣ, chapter11RayGenerator m a ∧
        ((I : Chapter11FractionalIdealUnitGroup K) : FractionalIdeal (𝓞 K)⁰ K) =
          (toPrincipalIdeal (𝓞 K) K a : FractionalIdeal (𝓞 K)⁰ K) := by
  rfl

theorem chapter11_ray_generator_is_local_congruence (m : RayModulus K)
    (a : Kˣ) :
    chapter11RayGenerator m a ↔
      ((∀ v, m.finiteExponent v ≠ 0 →
          chapter11FiniteGlobalComponent K v a ∈
            chapter11FiniteLocalUnitGroup K v (m.finiteExponent v)) ∧
        (∀ v (hv : v ∈ m.infinitePart),
          chapter11RealSignHom
              (chapter11RealGlobalComponent K v (m.infinitePart_isReal v hv) a) = 1)) := by
  rfl

theorem chapter11_ray_generator_principal_ideal_is_prime_to_modulus
    (m : RayModulus K) {a : Kˣ} (ha : chapter11RayGenerator m a) :
    toPrincipalIdeal (𝓞 K) K a ∈ chapter11IdealPrimeToModulus m := by
  intro v hv
  have hcount :=
    (chapter11CanonicalIdeleIdealMap K).count_eq_zero_of_local_unit
      (chapter11PrincipalIdeleHom (K := K) a) v (m.finiteExponent v) (by
        change chapter11FiniteGlobalComponent K v a ∈
          chapter11FiniteLocalUnitGroup K v (m.finiteExponent v)
        exact ha.1 v hv)
  rw [(chapter11CanonicalIdeleIdealMap K).map_principal a] at hcount
  exact hcount

theorem chapter11_exists_ray_normalizer (m : RayModulus K)
    (x : Chapter11IdeleGroup K) :
    ∃ a : Kˣ, Chapter11RayNormalizer m x a := by
  classical
  let T : Finset (LastLib.Book04AdelesAndIdeles.Chapter05.Chapter05Place K) :=
    m.finiteExponent.support.map
        ⟨Sum.inl, fun a b h => Sum.inl.inj h⟩ ∪
      m.infinitePart.map
        ⟨Sum.inr, fun a b h => Sum.inr.inj h⟩
  have hTfin {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)}
      (hv : v ∈ m.finiteExponent.support) :
      Sum.inl v ∈ T := by
    dsimp [T]
    exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨v, hv, rfl⟩)
  have hTinf {v : NumberField.InfinitePlace K}
      (hv : v ∈ m.infinitePart) :
      Sum.inr v ∈ T := by
    dsimp [T]
    exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨v, hv, rfl⟩)
  have hfin_of_mem {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)}
      (hv : Sum.inl v ∈ T) : v ∈ m.finiteExponent.support := by
    dsimp [T] at hv
    rcases Finset.mem_union.mp hv with hleft | hright
    · rcases Finset.mem_map.mp hleft with ⟨w, hw, hEq⟩
      exact Sum.inl.inj hEq ▸ hw
    · rcases Finset.mem_map.mp hright with ⟨w, hw, hEq⟩
      cases hEq
  have hinf_of_mem {v : NumberField.InfinitePlace K}
      (hv : Sum.inr v ∈ T) : v ∈ m.infinitePart := by
    dsimp [T] at hv
    rcases Finset.mem_union.mp hv with hleft | hright
    · rcases Finset.mem_map.mp hleft with ⟨w, hw, hEq⟩
      cases hEq
    · rcases Finset.mem_map.mp hright with ⟨w, hw, hEq⟩
      exact Sum.inr.inj hEq ▸ hw
  have hpow_open : ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (n : ℕ),
      IsOpen (((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n :
        Ideal (v.adicCompletionIntegers K)) : Set (v.adicCompletionIntegers K)) := by
    intro v n
    let A := v.adicCompletionIntegers K
    have hsub : IsCompact (Set.univ : Set A) := by
      apply Subtype.isCompact_iff.mpr
      convert
        (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09_adic_completion_integers_compact K v)
          using 1
      ext z
      constructor
      · rintro ⟨y, -, rfl⟩
        exact y.property
      · intro hz
        exact ⟨⟨z, hz⟩, Set.mem_univ _, rfl⟩
    let compactA : CompactSpace A := ⟨hsub⟩
    exact @IsLocalRing.isOpen_maximalIdeal_pow A _ _ _ compactA _ _ _ n
  let W0 : ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (n : ℕ),
      Set (v.adicCompletion K) := fun v n =>
    (fun z : v.adicCompletionIntegers K => (z : v.adicCompletion K)) ''
      (((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n :
        Ideal (v.adicCompletionIntegers K)) : Set (v.adicCompletionIntegers K))
  have hW0 : ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (n : ℕ),
      IsOpen (W0 v n) := by
    intro v n
    dsimp [W0]
    exact
      (Valued.isOpen_valuationSubring (v.adicCompletion K)).isOpenEmbedding_subtypeVal.isOpenMap
        _ (hpow_open v n)
  let target : ∀ w : T,
      LastLib.Book04AdelesAndIdeles.Chapter05.Chapter05LocalField K w.1 := fun w =>
    match w.1 with
    | Sum.inl v =>
        (((chapter11IdeleFiniteComponent K v x)⁻¹ : (v.adicCompletion K)ˣ) :
          v.adicCompletion K)
    | Sum.inr v =>
        (((chapter11InfiniteIdeleComponent K v x)⁻¹ : v.Completionˣ) : v.Completion)
  let W : ∀ w : T,
      Set (LastLib.Book04AdelesAndIdeles.Chapter05.Chapter05LocalField K w.1) := fun w =>
    match w.1 with
    | Sum.inl v =>
        (fun z : v.adicCompletion K =>
          z * (chapter11IdeleFiniteComponent K v x : v.adicCompletion K) - 1) ⁻¹' W0 v
            (m.finiteExponent v)
    | Sum.inr v =>
        if hv : v ∈ m.infinitePart then
          {z : v.Completion |
            0 < NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
              (m.infinitePart_isReal v hv)
              (z * (chapter11InfiniteIdeleComponent K v x : v.Completion))}
        else Set.univ
  have hW : ∀ w : T, W w ∈ 𝓝 (target w) := by
    rintro ⟨w, hw⟩
    change (IsDedekindDomain.HeightOneSpectrum (𝓞 K) ⊕ NumberField.InfinitePlace K) at w
    cases w with
    | inl v =>
        let L := v.adicCompletion K
        have hopen : IsOpen (W ⟨Sum.inl v, hw⟩) := by
          dsimp [W]
          exact (hW0 v (m.finiteExponent v)).preimage
            ((continuous_id.mul continuous_const).sub continuous_const)
        have hmem : target ⟨Sum.inl v, hw⟩ ∈ W ⟨Sum.inl v, hw⟩ := by
          dsimp [target, W, W0]
          refine ⟨(0 : v.adicCompletionIntegers K), ?_, ?_⟩
          · exact (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^
              m.finiteExponent v).zero_mem
          · simp
        exact hopen.mem_nhds hmem
    | inr v =>
        by_cases hv : v ∈ m.infinitePart
        · have hf : Continuous (fun z : v.Completion =>
              NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
                (m.infinitePart_isReal v hv)
                (z * (chapter11InfiniteIdeleComponent K v x : v.Completion))) := by
            exact
              (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
                (m.infinitePart_isReal v hv)).continuous.comp
                (continuous_id.mul continuous_const)
          have hopen : IsOpen (W ⟨Sum.inr v, hw⟩) := by
            dsimp [W]
            rw [dif_pos hv]
            exact isOpen_Ioi.preimage hf
          have hmem : target ⟨Sum.inr v, hw⟩ ∈ W ⟨Sum.inr v, hw⟩ := by
            dsimp [target, W]
            rw [dif_pos hv]
            change 0 <
              NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
                (m.infinitePart_isReal v hv)
                ((((chapter11InfiniteIdeleComponent K v x)⁻¹ : v.Completionˣ) :
                  v.Completion) *
                  (chapter11InfiniteIdeleComponent K v x : v.Completion))
            rw [map_mul]
            have hxne :
                NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
                    (m.infinitePart_isReal v hv)
                    (chapter11InfiniteIdeleComponent K v x : v.Completion) ≠ 0 := by
              exact (map_ne_zero
                    (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
                      (m.infinitePart_isReal v hv))).2 (Units.ne_zero _)
            rw [Units.val_inv_eq_inv_val, map_inv₀, inv_mul_cancel₀ hxne]
            norm_num
          exact hopen.mem_nhds hmem
        · have hopen : IsOpen (W ⟨Sum.inr v, hw⟩) := by
            dsimp [W]
            rw [dif_neg hv]
            exact isOpen_univ
          have hmem : target ⟨Sum.inr v, hw⟩ ∈ W ⟨Sum.inr v, hw⟩ := by
            dsimp [target, W]
            rw [dif_neg hv]
            exact Set.mem_univ _
          exact hopen.mem_nhds hmem
  by_cases hT : T.Nonempty
  · obtain ⟨a, ha⟩ :=
      (LastLib.Book04AdelesAndIdeles.Chapter05.chapter05_theorem_5_3_weak_approximation K T)
        target W hW
    have ha0 : a ≠ 0 := by
      intro hzero
      obtain ⟨w, hw⟩ := hT
      cases w with
      | inl v =>
          have hvT : v ∈ m.finiteExponent.support := hfin_of_mem hw
          have hmem := ha ⟨Sum.inl v, hw⟩
          dsimp [W, Chapter05.chapter05LocalEmbedding] at hmem
          change (NumberField.FinitePlace.embedding v a) *
              (chapter11IdeleFiniteComponent K v x : v.adicCompletion K) - 1 ∈
            W0 v (m.finiteExponent v) at hmem
          rw [hzero, map_zero, zero_mul, zero_sub] at hmem
          have hneg : (-1 : v.adicCompletion K) ∈ W0 v (m.finiteExponent v) := by
            exact hmem
          rcases hneg with ⟨z, hz, hzne⟩
          have hzmax : z ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
            have hpow_le : (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^
                (m.finiteExponent v) ≤ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
              exact Ideal.pow_le_self (by
                exact (Finsupp.mem_support_iff.mp hvT))
            exact hpow_le hz
          have hnegA : (-1 : v.adicCompletionIntegers K) ∈
              IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
            have hneg_eq : (-1 : v.adicCompletionIntegers K) = z := by
              apply Subtype.ext
              simpa using hzne.symm
            rw [hneg_eq]
            exact hzmax
          exact (IsLocalRing.notMem_maximalIdeal).2 isUnit_neg_one hnegA
      | inr v =>
          have hvT : v ∈ m.infinitePart := hinf_of_mem hw
          have hmem := ha ⟨Sum.inr v, hw⟩
          dsimp [W, Chapter05.chapter05LocalEmbedding] at hmem
          rw [dif_pos hvT] at hmem
          change 0 <
            NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
              (m.infinitePart_isReal v hvT)
              ((algebraMap K v.Completion a) *
                (chapter11InfiniteIdeleComponent K v x : v.Completion)) at hmem
          rw [hzero, map_zero, zero_mul] at hmem
          simp at hmem
    let au : Kˣ := Units.mk0 a ha0
    refine ⟨au, ?_⟩
    constructor
    · intro v hv
      have hvT : v ∈ m.finiteExponent.support := by
        exact Finsupp.mem_support_iff.mpr hv
      have hmem := ha ⟨Sum.inl v, hTfin hvT⟩
      dsimp [W, Chapter05.chapter05LocalEmbedding] at hmem
      rcases hmem with ⟨y, hy, hya⟩
      have hpow_le : (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^
          (m.finiteExponent v) ≤ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
        exact Ideal.pow_le_self (by exact hv)
      have hymax : y ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := hpow_le hy
      have hvaly : (v.adicCompletionIntegers K).valuation (y : v.adicCompletion K) < 1 :=
        (ValuationSubring.valuation_lt_one_iff (v.adicCompletionIntegers K) y).1 hymax
      have hzval : (v.adicCompletionIntegers K).valuation
          (1 + (y : v.adicCompletion K)) = 1 :=
        (v.adicCompletionIntegers K).valuation.map_one_add_of_lt hvaly
      have hzA : (1 + (y : v.adicCompletion K)) ∈ v.adicCompletionIntegers K :=
        ((v.adicCompletionIntegers K).valuation_le_one_iff _).1 hzval.le
      have hzinvA : (1 + (y : v.adicCompletion K))⁻¹ ∈
          v.adicCompletionIntegers K := by
        rw [← (v.adicCompletionIntegers K).valuation_le_one_iff,
          map_inv₀, hzval, inv_one]
      have hzne : (1 + (y : v.adicCompletion K)) ≠ 0 := by
        intro hzero
        simp [hzero] at hzval
      let zu : (v.adicCompletionIntegers K)ˣ :=
        { val := ⟨1 + (y : v.adicCompletion K), hzA⟩
          inv := ⟨(1 + (y : v.adicCompletion K))⁻¹, hzinvA⟩
          val_inv := by
            apply Subtype.ext
            exact mul_inv_cancel₀ hzne
          inv_val := by
            apply Subtype.ext
            exact inv_mul_cancel₀ hzne }
      have hzu : zu ∈ chapter11LocalUnitFiltration
          (A := v.adicCompletionIntegers K) (m.finiteExponent v) := by
        rw [chapter11LocalUnitFiltration_mem_iff]
        right
        change ((1 + y) - 1) ∈
          (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^
            (m.finiteExponent v)
        simpa using hy
      refine ⟨zu, hzu, ?_⟩
      apply Units.ext
      change (Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom zu :
          v.adicCompletion K) =
        (chapter11IdeleFiniteComponent K v
          (chapter11PrincipalIdeleHom (K := K) au * x) : v.adicCompletion K)
      rw [map_mul]
      change 1 + (y : v.adicCompletion K) =
        (NumberField.FinitePlace.embedding v a) *
          (chapter11IdeleFiniteComponent K v x : v.adicCompletion K)
      have hya' :
          (NumberField.FinitePlace.embedding v a) *
              (chapter11IdeleFiniteComponent K v x : v.adicCompletion K) - 1 =
            (y : v.adicCompletion K) := hya.symm
      calc
        1 + (y : v.adicCompletion K) = (y : v.adicCompletion K) + 1 := by
          rw [add_comm]
        _ = ((NumberField.FinitePlace.embedding v a) *
              (chapter11IdeleFiniteComponent K v x : v.adicCompletion K) - 1) + 1 := by
          rw [hya']
        _ = (NumberField.FinitePlace.embedding v a) *
              (chapter11IdeleFiniteComponent K v x : v.adicCompletion K) := by
          exact sub_add_cancel _ _
    · intro v hv
      have hvT : v ∈ m.infinitePart := hv
      have hmem := ha ⟨Sum.inr v, hTinf hvT⟩
      dsimp [W] at hmem
      rw [dif_pos hvT] at hmem
      apply Units.ext
      change SignType.sign
          (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
            (m.infinitePart_isReal v hv)
            (((chapter11PrincipalIdeleHom (K := K) au * x : Chapter11IdeleGroup K) :
              Chapter11AdeleRing K).1 v)) = 1
      exact sign_pos hmem
  · have hfin0 : ∀ v, m.finiteExponent v ≠ 0 → False := by
      intro v hv
      exact hT ⟨Sum.inl v, hTfin (Finsupp.mem_support_iff.mpr hv)⟩
    have hinf0 : ∀ v, v ∈ m.infinitePart → False := by
      intro v hv
      exact hT ⟨Sum.inr v, hTinf hv⟩
    refine ⟨1, ?_⟩
    constructor
    · intro v hv
      exact False.elim (hfin0 v hv)
    · intro v hv
      exact False.elim (hinf0 v hv)

theorem chapter11_normalized_idele_has_prime_to_modulus_ideal
    (m : RayModulus K)
    (x : Chapter11IdeleGroup K) :
    ∃ a : Kˣ,
      Chapter11RayNormalizer m x a ∧
        (chapter11CanonicalIdeleIdealMap K).toIdeal
            (chapter11PrincipalIdeleHom (K := K) a * x) ∈
          chapter11IdealPrimeToModulus m := by
  obtain ⟨a, ha⟩ := chapter11_exists_ray_normalizer m x
  refine ⟨a, ha, ?_⟩
  intro v hv
  exact (chapter11CanonicalIdeleIdealMap K).count_eq_zero_of_local_unit
    (chapter11PrincipalIdeleHom (K := K) a * x) v (m.finiteExponent v) (ha.1 v hv)

theorem chapter11_ray_class_quotient_map_is_unchanged_by_principal_and_ray_units
    (m : RayModulus K) (x : Chapter11IdeleGroup K) (a : Kˣ)
    (u : chapter11RayUnitSubgroup m) :
    chapter11RayClassProjection m
        (chapter11PrincipalIdeleHom (K := K) a * x * u) =
      chapter11RayClassProjection m x := by
  let S := chapter11PrincipalIdeleSubgroup (K := K) ⊔ chapter11RayUnitSubgroup m
  change QuotientGroup.mk' S
      (chapter11PrincipalIdeleHom (K := K) a * x * (u : Chapter11IdeleGroup K)) =
    QuotientGroup.mk' S x
  apply (QuotientGroup.mk'_eq_mk' S).2
  refine ⟨(u : Chapter11IdeleGroup K)⁻¹ *
      (chapter11PrincipalIdeleHom (K := K) a)⁻¹, ?_, ?_⟩
  · exact S.mul_mem
      (S.inv_mem (Subgroup.mem_sup_right u.property))
      (S.inv_mem (Subgroup.mem_sup_left ⟨a, rfl⟩))
  · simp [mul_assoc, mul_comm, mul_left_comm]

private theorem chapter11_ray_generator_of_two_normalizers
    (m : RayModulus K) (x : Chapter11IdeleGroup K) (a b : Kˣ)
    (ha : Chapter11RayNormalizer m x a)
    (hb : Chapter11RayNormalizer m x b) :
    chapter11RayGenerator m (b * a⁻¹) := by
  have hidele :
      (chapter11PrincipalIdeleHom (K := K) b * x) *
          (chapter11PrincipalIdeleHom (K := K) a * x)⁻¹ =
        chapter11PrincipalIdeleHom (K := K) (b * a⁻¹) := by
    simp [mul_assoc, mul_comm, mul_left_comm]
  constructor
  · intro v hv
    have hloc :=
      (chapter11FiniteLocalUnitGroup K v (m.finiteExponent v)).mul_mem
        (hb.1 v hv)
        ((chapter11FiniteLocalUnitGroup K v (m.finiteExponent v)).inv_mem (ha.1 v hv))
    have hloc' :
        chapter11IdeleFiniteComponent K v
            ((chapter11PrincipalIdeleHom (K := K) b * x) *
              (chapter11PrincipalIdeleHom (K := K) a * x)⁻¹) ∈
          chapter11FiniteLocalUnitGroup K v (m.finiteExponent v) := by
      simpa only [map_mul, map_inv] using hloc
    rw [hidele] at hloc'
    change chapter11FiniteGlobalComponent K v (b * a⁻¹) ∈
      chapter11FiniteLocalUnitGroup K v (m.finiteExponent v) at hloc'
    exact hloc'
  · intro v hv
    have hsign :
        chapter11RealSignComponent K v (m.infinitePart_isReal v hv)
            ((chapter11PrincipalIdeleHom (K := K) b * x) *
              (chapter11PrincipalIdeleHom (K := K) a * x)⁻¹) = 1 := by
      rw [map_mul, map_inv, hb.2 v hv, ha.2 v hv, one_mul, inv_one]
    rw [hidele] at hsign
    have hcomp :
        chapter11RealSignComponent K v (m.infinitePart_isReal v hv)
            (chapter11PrincipalIdeleHom (K := K) (b * a⁻¹)) =
          chapter11RealSignHom
            (chapter11RealGlobalComponent K v (m.infinitePart_isReal v hv)
              (b * a⁻¹)) := by
      have hreal (c : Kˣ) :
          NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
              (m.infinitePart_isReal v hv)
              (chapter11InfiniteIdeleComponent K v
                (chapter11PrincipalIdeleHom (K := K) c) : v.Completion) =
            (chapter11RealGlobalComponent K v (m.infinitePart_isReal v hv) c : ℝ) := by
        change NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
              (m.infinitePart_isReal v hv)
              (algebraMap K v.Completion (c : K)) =
            NumberField.InfinitePlace.embedding_of_isReal
              (m.infinitePart_isReal v hv) (c : K)
        simp [WithAbs.equiv,
          NumberField.InfinitePlace.Completion.algebraMap_apply,
          NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe]
      apply Units.ext
      change SignType.sign
          (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
            (m.infinitePart_isReal v hv)
            (chapter11InfiniteIdeleComponent K v
              (chapter11PrincipalIdeleHom (K := K) (b * a⁻¹)) : v.Completion)) =
        SignType.sign
          (chapter11RealGlobalComponent K v (m.infinitePart_isReal v hv)
            (b * a⁻¹) : ℝ)
      rw [hreal]
    rw [hcomp] at hsign
    exact hsign

private theorem chapter11_principal_idele_real_sign_component
    (v : NumberField.InfinitePlace K) (hv : v.IsReal) (c : Kˣ) :
    chapter11RealSignComponent K v hv
        (chapter11PrincipalIdeleHom (K := K) c) =
      chapter11RealSignHom (chapter11RealGlobalComponent K v hv c) := by
  apply Units.ext
  change SignType.sign
      (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
        (chapter11InfiniteIdeleComponent K v
          (chapter11PrincipalIdeleHom (K := K) c) : v.Completion)) =
    SignType.sign (chapter11RealGlobalComponent K v hv c : ℝ)
  have hreal :
      NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
          (chapter11InfiniteIdeleComponent K v
            (chapter11PrincipalIdeleHom (K := K) c) : v.Completion) =
        (chapter11RealGlobalComponent K v hv c : ℝ) := by
    change NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
          (algebraMap K v.Completion (c : K)) =
        NumberField.InfinitePlace.embedding_of_isReal hv (c : K)
    simp [WithAbs.equiv,
      NumberField.InfinitePlace.Completion.algebraMap_apply,
      NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe]
  rw [hreal]

theorem chapter11_idele_ray_quotient_equiv_ideal_ray_quotient
    (m : RayModulus K) :
    Nonempty (chapter11RayClassGroup m ≃* chapter11IdealRayClassGroup m) := by
  classical
  let Q := chapter11RayPrincipalIdealSubgroup m
  let idealOfNormalizer : ∀ (x : Chapter11IdeleGroup K) (a : Kˣ),
      Chapter11RayNormalizer m x a → Chapter11IdealGroup m :=
    fun x a ha =>
      ⟨(chapter11CanonicalIdeleIdealMap K).toIdeal
          (chapter11PrincipalIdeleHom (K := K) a * x), by
        intro v hv
        exact (chapter11CanonicalIdeleIdealMap K).count_eq_zero_of_local_unit
          (chapter11PrincipalIdeleHom (K := K) a * x) v (m.finiteExponent v)
          (ha.1 v hv)⟩
  let classOfNormalizer : ∀ (x : Chapter11IdeleGroup K) (a : Kˣ),
      (ha : Chapter11RayNormalizer m x a) → chapter11IdealRayClassGroup m :=
    fun x a ha => QuotientGroup.mk' Q (idealOfNormalizer x a ha)
  have hclass_independent :
      ∀ (x : Chapter11IdeleGroup K) (a b : Kˣ)
        (ha : Chapter11RayNormalizer m x a)
        (hb : Chapter11RayNormalizer m x b),
        classOfNormalizer x a ha = classOfNormalizer x b hb := by
    intro x a b ha hb
    let c : Kˣ := b * a⁻¹
    have hc : chapter11RayGenerator m c := by
      simpa [c] using chapter11_ray_generator_of_two_normalizers m x a b ha hb
    let pc : Chapter11IdealGroup m :=
      ⟨toPrincipalIdeal (𝓞 K) K c,
        chapter11_ray_generator_principal_ideal_is_prime_to_modulus m hc⟩
    have hpc : pc ∈ Q := by
      apply (chapter11_ray_principal_ideal_mem_iff m pc).2
      refine ⟨c, hc, ?_⟩
      rfl
    have hrel :
        (pc : Chapter11FractionalIdealUnitGroup K) *
            idealOfNormalizer x a ha = idealOfNormalizer x b hb := by
      apply Units.ext
      change (toPrincipalIdeal (𝓞 K) K c : FractionalIdeal (𝓞 K)⁰ K) *
          ((chapter11CanonicalIdeleIdealMap K).toIdeal
            (chapter11PrincipalIdeleHom (K := K) a * x) :
              FractionalIdeal (𝓞 K)⁰ K) =
        ((chapter11CanonicalIdeleIdealMap K).toIdeal
          (chapter11PrincipalIdeleHom (K := K) b * x) :
            FractionalIdeal (𝓞 K)⁰ K)
      rw [← (chapter11CanonicalIdeleIdealMap K).map_principal c]
      rw [map_mul]
      simp [mul_comm, mul_left_comm]
    dsimp [classOfNormalizer]
    apply (QuotientGroup.mk'_eq_mk' Q).2
    refine ⟨pc, hpc, ?_⟩
    apply Subtype.ext
    apply Units.ext
    simpa [mul_comm] using
      congrArg (fun z : Chapter11FractionalIdealUnitGroup K =>
        (z : FractionalIdeal (𝓞 K)⁰ K)) hrel
  have hnormalizer_mul :
      ∀ (x y : Chapter11IdeleGroup K) (a b : Kˣ),
        Chapter11RayNormalizer m x a →
          Chapter11RayNormalizer m y b →
            Chapter11RayNormalizer m (x * y) (a * b) := by
    intro x y a b ha hb
    constructor
    · intro v hv
      have hloc :=
        (chapter11FiniteLocalUnitGroup K v (m.finiteExponent v)).mul_mem
          (ha.1 v hv) (hb.1 v hv)
      simpa [map_mul, mul_assoc, mul_comm, mul_left_comm] using hloc
    · intro v hv
      have hsign :
          chapter11RealSignComponent K v (m.infinitePart_isReal v hv)
              (chapter11PrincipalIdeleHom (K := K) a * x) *
            chapter11RealSignComponent K v (m.infinitePart_isReal v hv)
              (chapter11PrincipalIdeleHom (K := K) b * y) = 1 := by
        rw [ha.2 v hv, hb.2 v hv, one_mul]
      simpa [map_mul, mul_assoc, mul_comm, mul_left_comm] using hsign
  let normalizer : ∀ x : Chapter11IdeleGroup K, Kˣ := fun x =>
    Classical.choose (chapter11_exists_ray_normalizer m x)
  have normalizer_spec (x : Chapter11IdeleGroup K) :
      Chapter11RayNormalizer m x (normalizer x) :=
    Classical.choose_spec (chapter11_exists_ray_normalizer m x)
  let Φ : Chapter11IdeleGroup K → chapter11IdealRayClassGroup m := fun x =>
    classOfNormalizer x (normalizer x) (normalizer_spec x)
  have hΦ_mul (x y : Chapter11IdeleGroup K) : Φ (x * y) = Φ x * Φ y := by
    have hxy := hnormalizer_mul x y (normalizer x) (normalizer y)
      (normalizer_spec x) (normalizer_spec y)
    have hind := hclass_independent (x * y) (normalizer (x * y))
      (normalizer x * normalizer y) (normalizer_spec (x * y)) hxy
    calc
      Φ (x * y) =
          classOfNormalizer (x * y) (normalizer x * normalizer y) hxy := hind
      _ = Φ x * Φ y := by
        change QuotientGroup.mk' Q
            (idealOfNormalizer (x * y) (normalizer x * normalizer y) hxy) =
          QuotientGroup.mk' Q (idealOfNormalizer x (normalizer x) (normalizer_spec x)) *
            QuotientGroup.mk' Q (idealOfNormalizer y (normalizer y) (normalizer_spec y))
        rw [← (QuotientGroup.mk' Q).map_mul]
        congr 1
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        apply Units.ext
        change ((chapter11CanonicalIdeleIdealMap K).toIdeal
              (chapter11PrincipalIdeleHom (K := K)
                (normalizer x * normalizer y) * (x * y)) :
              FractionalIdeal (𝓞 K)⁰ K) =
            ((chapter11CanonicalIdeleIdealMap K).toIdeal
              (chapter11PrincipalIdeleHom (K := K) (normalizer x) * x) :
                FractionalIdeal (𝓞 K)⁰ K) *
              ((chapter11CanonicalIdeleIdealMap K).toIdeal
                (chapter11PrincipalIdeleHom (K := K) (normalizer y) * y) :
                  FractionalIdeal (𝓞 K)⁰ K)
        simp [map_mul, mul_assoc, mul_comm, mul_left_comm]
  have hnorm_one : Chapter11RayNormalizer m (1 : Chapter11IdeleGroup K) 1 := by
    constructor
    · intro v hv
      simpa only [map_one, one_mul] using
        (chapter11FiniteLocalUnitGroup K v (m.finiteExponent v)).one_mem
    · intro v hv
      simp
  have hΦ_one : Φ 1 = 1 := by
    have hind := hclass_independent (1 : Chapter11IdeleGroup K) (normalizer 1) 1
      (normalizer_spec 1) hnorm_one
    calc
      Φ 1 = classOfNormalizer 1 1 hnorm_one := hind
      _ = 1 := by
        have hI : idealOfNormalizer 1 1 hnorm_one =
            (1 : Chapter11IdealGroup m) := by
          apply Subtype.ext
          apply Units.ext
          dsimp [idealOfNormalizer]
          change ((chapter11CanonicalIdeleIdealMap K).toIdeal
              (chapter11PrincipalIdeleHom (K := K) 1 * 1) :
              FractionalIdeal (𝓞 K)⁰ K) = 1
          rw [map_mul, (chapter11CanonicalIdeleIdealMap K).map_principal]
          simp
        change QuotientGroup.mk' Q (idealOfNormalizer 1 1 hnorm_one) = 1
        rw [hI]
        exact map_one _
  let Φhom : Chapter11IdeleGroup K →* chapter11IdealRayClassGroup m :=
    { toFun := Φ
      map_one' := hΦ_one
      map_mul' := hΦ_mul }
  have hfull_of_ray_unit (u : chapter11RayUnitSubgroup m) :
      (u : Chapter11IdeleGroup K) ∈ chapter11FullFiniteUnitSubgroup := by
    change
      (∀ v, chapter11IdeleFiniteComponent K v (u : Chapter11IdeleGroup K) ∈
        chapter11FiniteLocalUnitGroup K v 0) ∧
        (∀ v (hv : v ∈ (RayModulus.trivial (K := K)).infinitePart),
          chapter11RealSignComponent K v
            ((RayModulus.trivial (K := K)).infinitePart_isReal v hv)
            (u : Chapter11IdeleGroup K) = 1)
    constructor
    · intro v
      apply (show chapter11FiniteLocalUnitGroup K v (m.finiteExponent v) ≤
          chapter11FiniteLocalUnitGroup K v 0 from ?_) (u.property.1 v)
      intro z hz
      rcases hz with ⟨w, hw, hzw⟩
      exact ⟨w, chapter11LocalUnitFiltration_antitone (Nat.zero_le _) hw, hzw⟩
    · simp [RayModulus.trivial]
  have hideal_of_ray_unit (u : chapter11RayUnitSubgroup m) :
      (chapter11CanonicalIdeleIdealMap K).toIdeal (u : Chapter11IdeleGroup K) = 1 := by
    apply (MonoidHom.mem_ker).mp
    rw [(chapter11CanonicalIdeleIdealMap K).kernel_eq_full_finite_units]
    exact hfull_of_ray_unit u
  have hprincipal_normalizer (c : Kˣ) :
      Chapter11RayNormalizer m
        (chapter11PrincipalIdeleHom (K := K) c) c⁻¹ := by
    constructor
    · intro v hv
      have hprod :
          chapter11PrincipalIdeleHom (K := K) c⁻¹ *
              chapter11PrincipalIdeleHom (K := K) c =
            (1 : Chapter11IdeleGroup K) := by
        simp
      rw [hprod]
      simpa only [map_one] using
        (chapter11FiniteLocalUnitGroup K v (m.finiteExponent v)).one_mem
    · intro v hv
      have hprod :
          chapter11PrincipalIdeleHom (K := K) c⁻¹ *
              chapter11PrincipalIdeleHom (K := K) c =
            (1 : Chapter11IdeleGroup K) := by
        simp
      rw [hprod]
      simp
  have hprincipal (c : Kˣ) :
      Φhom (chapter11PrincipalIdeleHom (K := K) c) = 1 := by
    have hc := hprincipal_normalizer c
    have hind := hclass_independent
      (chapter11PrincipalIdeleHom (K := K) c) (normalizer _ ) c⁻¹
      (normalizer_spec _) hc
    have hI :
        idealOfNormalizer (chapter11PrincipalIdeleHom (K := K) c) c⁻¹ hc =
          (1 : Chapter11IdealGroup m) := by
      apply Subtype.ext
      apply Units.ext
      dsimp [idealOfNormalizer]
      change ((chapter11CanonicalIdeleIdealMap K).toIdeal
          (chapter11PrincipalIdeleHom (K := K) c⁻¹ *
            chapter11PrincipalIdeleHom (K := K) c) :
          FractionalIdeal (𝓞 K)⁰ K) = 1
      rw [map_mul, (chapter11CanonicalIdeleIdealMap K).map_principal c⁻¹,
        (chapter11CanonicalIdeleIdealMap K).map_principal c]
      simp
    change classOfNormalizer
        (chapter11PrincipalIdeleHom (K := K) c)
          (normalizer (chapter11PrincipalIdeleHom (K := K) c))
          (normalizer_spec (chapter11PrincipalIdeleHom (K := K) c)) = 1
    calc
      classOfNormalizer
          (chapter11PrincipalIdeleHom (K := K) c)
            (normalizer (chapter11PrincipalIdeleHom (K := K) c))
            (normalizer_spec (chapter11PrincipalIdeleHom (K := K) c)) =
          classOfNormalizer
            (chapter11PrincipalIdeleHom (K := K) c) c⁻¹ hc := hind
      _ = 1 := by
        change QuotientGroup.mk' Q
          (idealOfNormalizer (chapter11PrincipalIdeleHom (K := K) c) c⁻¹ hc) = 1
        rw [hI]
        exact map_one _
  have hrayunit_normalizer (u : chapter11RayUnitSubgroup m) :
      Chapter11RayNormalizer m (u : Chapter11IdeleGroup K) 1 := by
    constructor
    · intro v hv
      simpa only [map_one, one_mul] using u.property.1 v
    · intro v hv
      simpa only [map_one, one_mul] using u.property.2 v hv
  have hrayunit (u : chapter11RayUnitSubgroup m) :
      Φhom (u : Chapter11IdeleGroup K) = 1 := by
    have hu := hrayunit_normalizer u
    have hind := hclass_independent (u : Chapter11IdeleGroup K)
      (normalizer _) 1 (normalizer_spec _) hu
    have hI :
        idealOfNormalizer (u : Chapter11IdeleGroup K) 1 hu =
          (1 : Chapter11IdealGroup m) := by
      apply Subtype.ext
      apply Units.ext
      dsimp [idealOfNormalizer]
      change ((chapter11CanonicalIdeleIdealMap K).toIdeal
          (chapter11PrincipalIdeleHom (K := K) 1 * (u : Chapter11IdeleGroup K)) :
          FractionalIdeal (𝓞 K)⁰ K) = 1
      rw [map_mul, (chapter11CanonicalIdeleIdealMap K).map_principal,
        hideal_of_ray_unit u]
      simp
    change classOfNormalizer (u : Chapter11IdeleGroup K)
        (normalizer (u : Chapter11IdeleGroup K))
        (normalizer_spec (u : Chapter11IdeleGroup K)) = 1
    calc
      classOfNormalizer (u : Chapter11IdeleGroup K)
          (normalizer (u : Chapter11IdeleGroup K))
          (normalizer_spec (u : Chapter11IdeleGroup K)) =
          classOfNormalizer (u : Chapter11IdeleGroup K) 1 hu := hind
      _ = 1 := by
        change QuotientGroup.mk' Q
          (idealOfNormalizer (u : Chapter11IdeleGroup K) 1 hu) = 1
        rw [hI]
        exact map_one _
  have hker :
      chapter11PrincipalIdeleSubgroup (K := K) ⊔
          chapter11RayUnitSubgroup m = Φhom.ker := by
    ext x
    constructor
    · intro hx
      apply (MonoidHom.mem_ker).2
      rcases Subgroup.mem_sup.mp hx with ⟨y, hy, z, hz, rfl⟩
      rcases hy with ⟨c, rfl⟩
      rw [map_mul, hprincipal c, hrayunit ⟨z, hz⟩]
      exact one_mul (1 : chapter11IdealRayClassGroup m)
    · intro hx
      have hx' : Φhom x = 1 := hx
      change classOfNormalizer x (normalizer x) (normalizer_spec x) = 1 at hx'
      change QuotientGroup.mk' Q
          (idealOfNormalizer x (normalizer x) (normalizer_spec x)) = 1 at hx'
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
      obtain ⟨c, hc, hIc⟩ :=
        (chapter11_ray_principal_ideal_mem_iff m
          (idealOfNormalizer x (normalizer x) (normalizer_spec x))).1 hx'
      let y : Chapter11IdeleGroup K :=
        (chapter11PrincipalIdeleHom (K := K) c)⁻¹ *
          (chapter11PrincipalIdeleHom (K := K) (normalizer x) * x)
      have hyideal :
          (chapter11CanonicalIdeleIdealMap K).toIdeal y = 1 := by
        have hIc' :
            (idealOfNormalizer x (normalizer x) (normalizer_spec x) :
                Chapter11FractionalIdealUnitGroup K) =
              toPrincipalIdeal (𝓞 K) K c := by
          apply Units.ext
          exact hIc
        dsimp [y]
        rw [map_mul, map_inv,
          (chapter11CanonicalIdeleIdealMap K).map_principal]
        change (toPrincipalIdeal (𝓞 K) K c)⁻¹ *
            (idealOfNormalizer x (normalizer x) (normalizer_spec x) :
              Chapter11FractionalIdealUnitGroup K) = 1
        rw [hIc']
        simp
      have hyfull : y ∈ chapter11FullFiniteUnitSubgroup := by
        rw [← (chapter11CanonicalIdeleIdealMap K).kernel_eq_full_finite_units]
        exact (MonoidHom.mem_ker).2 hyideal
      have hyfull0 : ∀ v,
          chapter11IdeleFiniteComponent K v y ∈
            chapter11FiniteLocalUnitGroup K v 0 := by
        change
          (∀ v, chapter11IdeleFiniteComponent K v y ∈
            chapter11FiniteLocalUnitGroup K v 0) ∧ _ at hyfull
        exact hyfull.1
      have hy : y ∈ chapter11RayUnitSubgroup m := by
        constructor
        · intro v
          by_cases hv : m.finiteExponent v ≠ 0
          · have hcp : chapter11IdeleFiniteComponent K v
                  (chapter11PrincipalIdeleHom (K := K) c) ∈
                chapter11FiniteLocalUnitGroup K v (m.finiteExponent v) := by
              change chapter11FiniteGlobalComponent K v c ∈
                chapter11FiniteLocalUnitGroup K v (m.finiteExponent v)
              exact hc.1 v hv
            have hxp := (normalizer_spec x).1 v hv
            dsimp [y]
            simpa only [map_mul, map_inv] using
              (chapter11FiniteLocalUnitGroup K v (m.finiteExponent v)).mul_mem
                ((chapter11FiniteLocalUnitGroup K v (m.finiteExponent v)).inv_mem hcp) hxp
          · have hv0 : m.finiteExponent v = 0 := not_ne_iff.mp hv
            rw [hv0]
            exact hyfull0 v
        · intro v hv
          have hcp : chapter11RealSignComponent K v
                (m.infinitePart_isReal v hv)
                (chapter11PrincipalIdeleHom (K := K) c) = 1 := by
            rw [chapter11_principal_idele_real_sign_component]
            exact hc.2 v hv
          have hxp := (normalizer_spec x).2 v hv
          dsimp [y]
          simp only [map_mul, map_inv, hcp, hxp, inv_one, one_mul]
      apply Subgroup.mem_sup.mpr
      refine ⟨(chapter11PrincipalIdeleHom (K := K)
          ((normalizer x)⁻¹ * c)),
        ⟨(normalizer x)⁻¹ * c, rfl⟩, y, hy, ?_⟩
      dsimp [y]
      simp
  have hfinite_representative :
      ∀ I : Chapter11IdealGroup m,
        ∃ y : LastLib.Book04AdelesAndIdeles.Chapter08.Chapter08FiniteIdeles K,
          LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleIdealMap K y =
              (I : Chapter11FractionalIdealUnitGroup K) ∧
            ∀ v, m.finiteExponent v ≠ 0 →
              LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleComponent y v = 1 := by
    intro I
    let hI : ((I : Chapter11FractionalIdealUnitGroup K) :
        FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
      exact Units.ne_zero (I : Chapter11FractionalIdealUnitGroup K)
    let d : LastLib.Book04AdelesAndIdeles.Chapter08.Chapter08FiniteDivisors K :=
      Finsupp.mk (FractionalIdeal.finite_factors
          ((I : Chapter11FractionalIdealUnitGroup K) : FractionalIdeal (𝓞 K)⁰ K)).toFinset
        (fun v => FractionalIdeal.count K v
          ((I : Chapter11FractionalIdealUnitGroup K) : FractionalIdeal (𝓞 K)⁰ K))
        (fun _ =>
          (FractionalIdeal.finite_factors
            ((I : Chapter11FractionalIdealUnitGroup K) : FractionalIdeal (𝓞 K)⁰ K)).mem_toFinset)
    have hdv : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        m.finiteExponent v ≠ 0 → d v = 0 := by
      intro v hv
      change FractionalIdeal.count K v
          ((I : Chapter11FractionalIdealUnitGroup K) : FractionalIdeal (𝓞 K)⁰ K) = 0
      exact I.property v hv
    let localUnit : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        (v.adicCompletion K)ˣ := fun v =>
      if hm : m.finiteExponent v ≠ 0 then
          1
      else
        Units.mk0
          (Classical.choose
            (v.valuedAdicCompletion_surjective K (WithZero.exp (-d v)))) (by
            have hval := Classical.choose_spec
              (v.valuedAdicCompletion_surjective K (WithZero.exp (-d v)))
            intro hz
            rw [hz, map_zero] at hval
            exact WithZero.exp_ne_zero hval.symm)
    have hlocal : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        Valued.v (localUnit v : v.adicCompletion K) = WithZero.exp (-d v) := by
      intro v
      by_cases hm : m.finiteExponent v ≠ 0
      · have hdv' : d v = 0 := hdv v hm
        dsimp [localUnit]
        rw [if_pos hm]
        simp [hdv']
      · dsimp [localUnit]
        rw [if_neg hm]
        exact Classical.choose_spec
          (v.valuedAdicCompletion_surjective K (WithZero.exp (-d v)))
    have hdzero : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        d v = 0 := by
      rw [Filter.eventually_cofinite]
      have hsupp : {v | ¬d v = 0} = (d.support : Set _) := by
        ext v
        simp [Finsupp.mem_support_iff]
      rw [hsupp]
      exact d.support.finite_toSet
    have hunit : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        localUnit v ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
      filter_upwards [hdzero] with v hv
      apply (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one).2
      rw [hlocal v, hv]
      exact WithZero.exp_zero
    let y : LastLib.Book04AdelesAndIdeles.Chapter08.Chapter08FiniteIdeles K :=
      RestrictedProduct.mkUnit (fun v => localUnit v) hunit
    have hy :
        LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleOrderFinsupp y = d := by
      ext v
      rw [LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleOrderFinsupp_apply]
      change LastLib.Book04AdelesAndIdeles.Chapter08.chapter08LocalOrder v
          (localUnit v : v.adicCompletion K) = d v
      unfold LastLib.Book04AdelesAndIdeles.Chapter08.chapter08LocalOrder
      rw [hlocal v, dif_neg WithZero.exp_ne_zero,
        WithZero.toAdd_unzero_eq_log, WithZero.log_exp]
      ring
    refine ⟨y, ?_⟩
    have hynorm : ∀ v, m.finiteExponent v ≠ 0 →
        LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleComponent y v = 1 := by
      intro v hv
      change (localUnit v : v.adicCompletion K) = 1
      dsimp [localUnit]
      rw [if_pos hv]
      simp
    exact ⟨by
      apply Units.ext
      change LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleFractionalIdeal y =
        ((I : Chapter11FractionalIdealUnitGroup K) : FractionalIdeal (𝓞 K)⁰ K)
      rw [LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleFractionalIdeal, hy]
      have hfac := FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI
      rw [← hfac]
      rw [finprod_eq_finsetProd_of_mulSupport_subset
        (s := (FractionalIdeal.finite_factors
          ((I : Chapter11FractionalIdealUnitGroup K) : FractionalIdeal (𝓞 K)⁰ K)).toFinset)]
      · rfl
      · rw [(FractionalIdeal.finite_factors
          ((I : Chapter11FractionalIdealUnitGroup K) : FractionalIdeal (𝓞 K)⁰ K)).coe_toFinset]
        intro v hv h
        rw [Function.mem_mulSupport] at hv
        rw [h, zpow_zero] at hv
        exact hv rfl, hynorm⟩
  have hsurj : Function.Surjective Φhom := by
    intro J
    obtain ⟨I, rfl⟩ := QuotientGroup.mk'_surjective Q J
    obtain ⟨y, hyideal, hynorm⟩ := hfinite_representative I
    let z : Chapter11IdeleGroup K :=
      (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K).symm
        (1, y)
    have hzray : Chapter11RayNormalizer m z 1 := by
      constructor
      · intro v hv
        have hunitcomp : chapter11IdeleFiniteComponent K v z = 1 := by
          apply Units.ext
          change LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleComponent y v = 1
          exact hynorm v hv
        simpa only [map_mul, map_one, one_mul, hunitcomp] using
          (chapter11FiniteLocalUnitGroup K v (m.finiteExponent v)).one_mem
      · intro v hv
        have hsignz :
            chapter11RealSignComponent K v (m.infinitePart_isReal v hv) z = 1 := by
          apply Units.ext
          change SignType.sign
            (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
              (m.infinitePart_isReal v hv)
              (((z : Chapter11AdeleRing K).1) v)) = 1
          have hzdecomp :
              LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K z =
                (1, y) := by
            exact
              (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K).apply_symm_apply _
          have hzinf :
              (z : Chapter11AdeleRing K).1 =
                (1 : LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K) := by
            exact congrArg
              (fun w =>
                (w.1 : LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K))
              hzdecomp
          have hzinfv :
              ((z : Chapter11AdeleRing K).1) v = (1 : v.Completion) := by
            exact congrArg
              (fun w : LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K => w v)
              hzinf
          rw [hzinfv]
          simp
        simpa only [map_mul, map_one, one_mul] using hsignz
    have hzideal :
        (chapter11CanonicalIdeleIdealMap K).toIdeal z =
          (I : Chapter11FractionalIdealUnitGroup K) := by
      change LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleIdealMap K
          (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09FiniteIdelePartHom K z) =
        (I : Chapter11FractionalIdealUnitGroup K)
      change LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleIdealMap K y =
        (I : Chapter11FractionalIdealUnitGroup K)
      exact hyideal
    have hIzn :
        idealOfNormalizer z 1 hzray = I := by
      apply Subtype.ext
      apply Units.ext
      dsimp [idealOfNormalizer]
      rw [map_mul, (chapter11CanonicalIdeleIdealMap K).map_principal, hzideal]
      simp
    have hΦz : Φhom z = QuotientGroup.mk' Q I := by
      change classOfNormalizer z (normalizer z) (normalizer_spec z) = _
      calc
        classOfNormalizer z (normalizer z) (normalizer_spec z) =
            classOfNormalizer z 1 hzray :=
          hclass_independent z (normalizer z) 1 (normalizer_spec z) hzray
        _ = QuotientGroup.mk' Q I := by
          change QuotientGroup.mk' Q (idealOfNormalizer z 1 hzray) = _
          rw [hIzn]
    exact ⟨z, hΦz⟩
  exact ⟨QuotientGroup.liftEquiv
    (chapter11PrincipalIdeleSubgroup (K := K) ⊔ chapter11RayUnitSubgroup m)
    hsurj hker⟩

/- The preliminary principal adjustment above is essential: the ideal map
attached to an arbitrary idele is not, by itself, an API assertion that its
ideal is prime to the finite part of the modulus. -/
theorem chapter11_prime_to_modulus_ideal_requires_normalization
    (m : RayModulus K)
    (x : Chapter11IdeleGroup K) :
    ∃ a : Kˣ,
      Chapter11RayNormalizer m x a ∧
        (chapter11CanonicalIdeleIdealMap K).toIdeal
            (chapter11PrincipalIdeleHom (K := K) a * x) ∈
          chapter11IdealPrimeToModulus m := by
  exact chapter11_normalized_idele_has_prime_to_modulus_ideal m x

end
