import LastLib.Book01ValuationsDVRsAndCompletions.Chapter07.Section04CompletionOfTheValuationRing
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Topology.Algebra.IsUniformGroup.Constructions
import Mathlib.Topology.Algebra.Ring.Basic

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter07

open Filter Set Function MonoidWithZeroHom
open scoped BigOperators Topology WithZero

noncomputable section

/-!
  Chapter 7 develops completion from the metric point of view and compares it with
  valuation rings and ideal-adic completion. Proofs are deferred to a later pass.
-/

/-! # Book 1, Chapter 7, Section 7.5: Separated Completion of Rings
-/

/-! ### 7.5. Separated ideal-adic completion -/

abbrev chapter07AdicCompletion
    (R : Type*) [CommRing R] (I : Ideal R) : Type _ :=
  AdicCompletion I R

-- The canonical map from a ring to its ideal-adic completion.
def chapter07AdicCompletionMap
    {R : Type*} [CommRing R] (I : Ideal R) :
    R →+* chapter07AdicCompletion R I :=
  algebraMap R (chapter07AdicCompletion R I)

-- The inverse-limit compatibility condition in AdicCompletion.
theorem chapter07_adic_completion_compatible_family
    {R : Type*} [CommRing R] (I : Ideal R)
    (x : chapter07AdicCompletion R I) :
    ∀ {m n : ℕ} (hmn : m ≤ n),
      AdicCompletion.transitionMap I R hmn (x.val n) = x.val m := by
  intro m n hmn
  exact x.property hmn

-- The kernel of the natural map is the intersection of all powers of the ideal.
theorem chapter07_adic_completion_kernel
    {R : Type*} [CommRing R] (I : Ideal R) :
    RingHom.ker (chapter07AdicCompletionMap I) = ⨅ n : ℕ, I ^ n := by
  ext x
  constructor
  · intro hx
    have hx' : chapter07AdicCompletionMap I x =
        (0 : chapter07AdicCompletion R I) := hx
    have hcoord : ∀ n : ℕ,
        Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R R)) x = 0 := by
      intro n
      have h := congrArg (fun z => z.val n) hx'
      simpa [chapter07AdicCompletionMap, AdicCompletion.algebraMap_apply,
        AdicCompletion.val_zero_apply] using h
    change x ∈ (⨅ n : ℕ, I ^ n : Ideal R)
    refine (Ideal.mem_iInf).2 ?_
    intro n
    have hmem : x ∈ (I ^ n • (⊤ : Submodule R R)) :=
      (Submodule.Quotient.mk_eq_zero _).mp (hcoord n)
    simpa using hmem
  · intro hx
    apply Subtype.ext
    funext n
    simp only [chapter07AdicCompletionMap, AdicCompletion.algebraMap_apply,
      AdicCompletion.val_zero_apply]
    rw [AdicCompletion.of_apply]
    simp only [Submodule.mkQ_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [Submodule.Quotient.mk_eq_zero]
    simpa using (Ideal.mem_iInf.mp hx n)

-- The algebraic completion map is injective exactly in the separated case.
theorem chapter07_adic_completion_injective_iff_separated
    {R : Type*} [CommRing R] (I : Ideal R) :
    Function.Injective (chapter07AdicCompletionMap I) ↔ IsHausdorff I R := by
  exact AdicCompletion.of_injective_iff

/-- The completion of a Noetherian ring along an ideal is again Noetherian.

This is the Noetherian completion theorem.  Its proof is the standard
Artin--Rees argument: finite generation of `I` identifies the associated
graded ring of the completion with the corresponding finitely generated
graded algebra over `R ⧸ I`; lifting homogeneous generators degree by degree
and using completeness then shows that every ideal of the completion is
finitely generated. -/
theorem chapter07_adic_completion_isNoetherianRing
    {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R) :
    IsNoetherianRing (AdicCompletion I R) := by
  sorry

-- A witness in every power of I disappears in the adic completion.
theorem chapter07_adic_nonseparated_witness_in_kernel
    {R : Type*} [CommRing R] (I : Ideal R) (x : R)
    (hx : ∀ n : ℕ, x ∈ I ^ n) :
    chapter07AdicCompletionMap I x = 0 := by
  apply Subtype.ext
  funext n
  simp only [chapter07AdicCompletionMap, AdicCompletion.algebraMap_apply,
    AdicCompletion.val_zero_apply]
  rw [AdicCompletion.of_apply]
  simp only [Submodule.mkQ_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rw [Submodule.Quotient.mk_eq_zero]
  simpa using hx n

-- A nonzero intersection witness makes the completion map noninjective.
theorem chapter07_adic_nonseparated_map_not_injective
    {R : Type*} [CommRing R] (I : Ideal R)
    (h : ∃ x : R, x ≠ 0 ∧ ∀ n : ℕ, x ∈ I ^ n) :
    ¬ Function.Injective (chapter07AdicCompletionMap I) := by
  intro hinj
  obtain ⟨x, hx, hxn⟩ := h
  apply hx
  apply hinj
  rw [chapter07_adic_nonseparated_witness_in_kernel I x hxn]
  exact (map_zero (chapter07AdicCompletionMap I)).symm

-- Noetherian local domains are separated for every ideal contained in the maximal ideal.
theorem chapter07_noetherian_local_domain_is_adically_separated
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ IsLocalRing.maximalIdeal R) :
    IsHausdorff I R := by
  apply IsHausdorff.of_isDomain I
  intro htop
  have hmax : IsLocalRing.maximalIdeal R = ⊤ :=
    top_unique (htop ▸ hI)
  let M : Ideal R := IsLocalRing.maximalIdeal R
  have hM : M.IsMaximal := by
    change (IsLocalRing.maximalIdeal R : Ideal R).IsMaximal
    infer_instance
  exact hM.ne_top hmax

-- The canonical uniformity pulled back from the DVR valuation on its fraction field.
@[instance_reducible]
noncomputable def chapter07DvrUniformSpace
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] :
    UniformSpace A :=
  UniformSpace.comap (algebraMap A (FractionRing A))
    ((Valued.mk' ((IsDiscreteValuationRing.maximalIdeal A).valuation (FractionRing A))).toUniformSpace)

-- The pulled-back valuation uniformity is compatible with the ring operations.
noncomputable instance chapter07DvrUniformSpace_isUniformAddGroup
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] :
    @IsUniformAddGroup A (chapter07DvrUniformSpace A) inferInstance := by
  let K := FractionRing A
  let v : Valuation K ℤᵐ⁰ := (IsDiscreteValuationRing.maximalIdeal A).valuation K
  let : UniformSpace K := (Valued.mk' v).toUniformSpace
  let : IsUniformAddGroup K := (Valued.mk' v).toIsUniformAddGroup
  change @IsUniformAddGroup A
    (UniformSpace.comap (algebraMap A K) (inferInstance : UniformSpace K)) inferInstance
  exact IsUniformAddGroup.comap (algebraMap A K)

noncomputable instance chapter07DvrUniformSpace_isTopologicalRing
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] :
    @IsTopologicalRing A (chapter07DvrUniformSpace A).toTopologicalSpace inferInstance := by
  let K := FractionRing A
  let v : Valuation K ℤᵐ⁰ := (IsDiscreteValuationRing.maximalIdeal A).valuation K
  let : UniformSpace K := (Valued.mk' v).toUniformSpace
  let : TopologicalSpace K := (Valued.mk' v).toTopologicalSpace
  let : IsUniformAddGroup K := (Valued.mk' v).toIsUniformAddGroup
  let : UniformSpace A := chapter07DvrUniformSpace A
  let : IsUniformAddGroup A := chapter07DvrUniformSpace_isUniformAddGroup A
  let : ContinuousMul A := by
    change @ContinuousMul A ((inferInstance : TopologicalSpace K).induced (algebraMap A K)) _
    exact continuousMul_induced (algebraMap A K)
  let : IsTopologicalSemiring A := ⟨⟩
  exact ⟨⟩

-- The standard DVR statement comparing metric and ideal-adic completion.
set_option maxHeartbeats 800000 in
theorem chapter07_dvr_metric_completion_agrees_with_adic_completion
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    : ∃ e : @UniformSpace.Completion A (chapter07DvrUniformSpace A) ≃+*
        AdicCompletion (IsLocalRing.maximalIdeal A) A,
      ∀ a : A,
        e ((a : A) : @UniformSpace.Completion A (chapter07DvrUniformSpace A)) =
        chapter07AdicCompletionMap (IsLocalRing.maximalIdeal A) a := by
  let K := FractionRing A
  let v : Valuation K ℤᵐ⁰ := (IsDiscreteValuationRing.maximalIdeal A).valuation K
  let : Valued K ℤᵐ⁰ := Valued.mk' v
  let : UniformSpace K := (Valued.mk' v).toUniformSpace
  let : TopologicalSpace K := (Valued.mk' v).toTopologicalSpace
  let : IsUniformAddGroup K := (Valued.mk' v).toIsUniformAddGroup
  have hd : v.IsRankOneDiscrete := by infer_instance
  let : v.IsRankOneDiscrete := hd
  let C := UniformSpace.Completion K
  let B := chapter07CompletedValuationRing K ℤᵐ⁰
  let : UniformSpace B :=
    UniformSpace.comap (fun b : B => (b : C)) (inferInstance : UniformSpace C)
  let : TopologicalSpace B :=
    (UniformSpace.comap (fun b : B => (b : C))
      (inferInstance : UniformSpace C)).toTopologicalSpace
  have hclosed : IsClosed (B : Set C) := by
    exact chapter07_completed_valuation_ring_is_closed
  let : CompleteSpace B := hclosed.completeSpace_coe
  let : T0Space B := by infer_instance
  let fK : A →+* C := (UniformSpace.Completion.coeRingHom).comp (algebraMap A K)
  have hfK_mem : ∀ a : A, fK a ∈ (B : Set C) := by
    intro a
    change chapter07CompletionValuation K ℤᵐ⁰ (fK a) ≤ 1
    change chapter07CompletionValuation K ℤᵐ⁰
      (((algebraMap A K a) : K) : UniformSpace.Completion K) ≤ 1
    rw [chapter07_completion_valuation_apply_coe]
    change v (algebraMap A K a) ≤ 1
    exact (Valuation.mem_integer_iff v _).mp (by
      apply (Valuation.mem_integer_iff v _).2
      exact (Valuation.mem_valuationSubring_iff v _).mp (by
        change algebraMap A K a ∈ v.valuationSubring.toSubring
        rw [show v = (IsDiscreteValuationRing.maximalIdeal A).valuation K by rfl]
        rw [← IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring (A := A) (K := K)]
        exact Subring.mem_map.mpr ⟨a, Subring.mem_top _, rfl⟩))
  let f : A →+* B := fK.codRestrict B hfK_mem
  let : UniformSpace A := chapter07DvrUniformSpace A
  let : IsUniformAddGroup A := IsUniformAddGroup.comap (algebraMap A K)
  have hif : @IsUniformInducing A B (chapter07DvrUniformSpace A)
      (inferInstance : UniformSpace B) f := by
    apply (isUniformInducing_iff_uniformSpace).2
    have hcoek : UniformSpace.comap (fun x : K => (x : C))
        (inferInstance : UniformSpace C) = (inferInstance : UniformSpace K) := by
      exact (isUniformInducing_iff_uniformSpace).1
        (UniformSpace.Completion.isUniformInducing_coe K)
    have hsub : UniformSpace.comap (fun b : B => (b : C))
        (inferInstance : UniformSpace C) = (inferInstance : UniformSpace B) := by
      rfl
    calc
      UniformSpace.comap (f : A → B) (inferInstance : UniformSpace B) =
          UniformSpace.comap (f : A → B)
            (UniformSpace.comap (fun b : B => (b : C))
              (inferInstance : UniformSpace C)) := by rw [hsub]
      _ = UniformSpace.comap (algebraMap A K)
          (UniformSpace.comap (fun x : K => (x : C))
            (inferInstance : UniformSpace C)) := by
        rw [← UniformSpace.comap_comap, ← UniformSpace.comap_comap]
        apply congrArg (fun h : A → C =>
          UniformSpace.comap h (inferInstance : UniformSpace C))
        funext a
        rfl
      _ = UniformSpace.comap (algebraMap A K) (inferInstance : UniformSpace K) := by
        rw [hcoek]
      _ = chapter07DvrUniformSpace A := by rfl
  have hsubrange : Set.range (chapter07ValuationRingCompletionEmbedding
      (K := K) (Γ₀ := ℤᵐ⁰)) ⊆
      (fun b : B => (b : C)) '' Set.range f := by
    rintro z ⟨y, rfl⟩
    obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_lift_of_le_one
      (A := A) (K := K) y.property
    refine ⟨f a, ⟨a, rfl⟩, ?_⟩
    change ((algebraMap A K a : K) : C) =
      (((y : chapter07ValuationRing K ℤᵐ⁰) : K) : C)
    rw [ha]
  have hcl : closure (Set.range (chapter07ValuationRingCompletionEmbedding
      (K := K) (Γ₀ := ℤᵐ⁰))) = (B : Set C) := by
    exact chapter07_valuation_ring_closure_eq_completed_valuation_ring
  have hdense : DenseRange f := by
    rw [DenseRange]
    apply (Subtype.dense_iff).2
    intro y hy
    have hy' : y ∈ closure (Set.range (chapter07ValuationRingCompletionEmbedding
        (K := K) (Γ₀ := ℤᵐ⁰))) := by
      rw [hcl]
      exact hy
    exact (closure_mono hsubrange) hy'
  let pkgB : @AbstractCompletion A (chapter07DvrUniformSpace A) :=
    { space := B
      coe := f
      uniformStruct := inferInstance
      complete := inferInstance
      separation := inferInstance
      isUniformInducing := hif
      dense := hdense }
  let eU : @UniformSpace.Completion A (chapter07DvrUniformSpace A) ≃ᵤ B :=
    AbstractCompletion.compareEquiv UniformSpace.Completion.cPkg pkgB
  have eU_coe (a : A) : eU (a : @UniformSpace.Completion A
      (chapter07DvrUniformSpace A)) = f a := by
    exact AbstractCompletion.compare_coe UniformSpace.Completion.cPkg pkgB a
  let : IsRightUniformAddGroup A := IsUniformAddGroup.isRightUniformAddGroup A
  let : ContinuousMul A := by
    change @ContinuousMul A ((inferInstance : TopologicalSpace K).induced (algebraMap A K)) _
    exact continuousMul_induced (algebraMap A K)
  let : IsTopologicalSemiring A := ⟨⟩
  let : IsTopologicalRing A := ⟨⟩
  let : ContinuousAdd B := by
    change @ContinuousAdd B ((inferInstance : TopologicalSpace C).induced
      (fun b : B => (b : C))) _
    exact continuousAdd_induced (SubringClass.subtype B)
  let : ContinuousMul B := by
    change @ContinuousMul B ((inferInstance : TopologicalSpace C).induced
      (fun b : B => (b : C))) _
    exact continuousMul_induced (SubringClass.subtype B)
  have hadd (x y : @UniformSpace.Completion A (chapter07DvrUniformSpace A)) :
      eU (x + y) = eU x + eU y := by
    refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
    · exact isClosed_eq
        (eU.continuous.comp continuous_add)
        ((eU.continuous.comp continuous_fst).add
          (eU.continuous.comp continuous_snd))
    · intro a b
      rw [← UniformSpace.Completion.coe_add, eU_coe, eU_coe, eU_coe]
      exact map_add f a b
  have hmul (x y : @UniformSpace.Completion A (chapter07DvrUniformSpace A)) :
      eU (x * y) = eU x * eU y := by
    refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
    · exact isClosed_eq
        (eU.continuous.comp continuous_mul)
        ((eU.continuous.comp continuous_fst).mul
          (eU.continuous.comp continuous_snd))
    · intro a b
      rw [← UniformSpace.Completion.coe_mul, eU_coe, eU_coe, eU_coe]
      exact map_mul f a b
  have hone : eU (1 : @UniformSpace.Completion A (chapter07DvrUniformSpace A)) = 1 := by
    rw [← UniformSpace.Completion.coe_one A, eU_coe]
    exact map_one f
  have hVeq : Valued.integer K = v.valuationSubring.toSubring := by
    ext x
    rfl
  let iVV : Valued.integer K ≃+* v.valuationSubring :=
    { toFun := fun x => ⟨x, x.property⟩
      invFun := fun x => ⟨x, x.property⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_add' := by intro x y; rfl
      map_mul' := by intro x y; rfl }
  have hiVV_max : Ideal.map iVV.toRingHom
      (IsLocalRing.maximalIdeal (Valued.integer K)) =
      IsLocalRing.maximalIdeal v.valuationSubring := by
    apply le_antisymm
    · apply (Ideal.map_le_iff_le_comap).2
      intro x hx
      change iVV x ∈ IsLocalRing.maximalIdeal v.valuationSubring
      rw [IsLocalRing.mem_maximalIdeal]
      intro hu
      apply (IsLocalRing.mem_maximalIdeal x).mp hx
      have hu' : IsUnit (iVV.symm (iVV x)) :=
        IsUnit.map iVV.symm hu
      simpa using hu'
    · intro x hx
      have hy : iVV.symm x ∈ IsLocalRing.maximalIdeal (Valued.integer K) := by
        rw [IsLocalRing.mem_maximalIdeal]
        intro hu
        apply (IsLocalRing.mem_maximalIdeal x).mp hx
        have hu' : IsUnit (iVV (iVV.symm x)) :=
          IsUnit.map iVV hu
        simpa using hu'
      have := Ideal.mem_map_of_mem iVV.toRingHom hy
      change iVV (iVV.symm x) ∈
        Ideal.map iVV.toRingHom (IsLocalRing.maximalIdeal (Valued.integer K)) at this
      simpa only [iVV.apply_symm_apply] using this
  let π : v.Uniformizer := Classical.choice (inferInstance : Nonempty (v.Uniformizer))
  let p : v.valuationSubring := ⟨π.val, π.val.property⟩
  have hp : iVV (π.val : Valued.integer K) = p := by rfl
  have hp' : p = (π.val : v.valuationSubring) := by
    apply Subtype.ext
    rfl
  have hgen : IsLocalRing.maximalIdeal v.valuationSubring =
      Ideal.span ({p} : Set v.valuationSubring) := by
    simpa [hp'] using π.valuation_gt_one.is_generator
  have hmaxV : IsLocalRing.maximalIdeal (Valued.integer K) =
      Ideal.span ({(π : v.Uniformizer).val} : Set (Valued.integer K)) := by
    apply le_antisymm
    · intro x hx
      have hx' : iVV x ∈ IsLocalRing.maximalIdeal v.valuationSubring := by
        have hxm := Ideal.mem_map_of_mem iVV.toRingHom hx
        rw [hiVV_max] at hxm
        exact hxm
      rw [hgen] at hx'
      rcases Ideal.mem_span_singleton.mp hx' with ⟨u, hu⟩
      apply Ideal.mem_span_singleton.mpr
      refine ⟨iVV.symm u, ?_⟩
      exact congrArg iVV.symm hu
    · intro x hx
      rw [Ideal.mem_span_singleton] at hx
      rcases hx with ⟨u, rfl⟩
      have hu' : p * iVV u ∈ IsLocalRing.maximalIdeal v.valuationSubring := by
        rw [hgen]
        exact Ideal.mem_span_singleton.mpr ⟨iVV u, by simp⟩
      have hu'' : iVV (π.val * u) ∈
          Ideal.map iVV.toRingHom (IsLocalRing.maximalIdeal (Valued.integer K)) := by
        rw [hiVV_max]
        simpa [hp] using hu'
      obtain ⟨z, hz, hzu⟩ :=
        (Ideal.mem_map_iff_of_surjective iVV.toRingHom iVV.surjective).mp hu''
      have hzeq : z = π.val * u := by
        apply iVV.injective
        change iVV z = iVV (π.val * u) at hzu
        exact hzu
      exact hzeq ▸ hz
  have hmaxV_pow : ∀ n : ℕ,
      IsLocalRing.maximalIdeal (Valued.integer K) ^ n =
        Ideal.span ({((π : v.Uniformizer).val : Valued.integer K) ^ n} :
          Set (Valued.integer K)) := by
    intro n
    rw [hmaxV]
    exact (Ideal.span_singleton_pow _ n)
  let r : A ≃+* Valued.integer K :=
    (IsDiscreteValuationRing.equivValuationSubring (A := A) (K := K)).trans iVV.symm
  have hrmax : Ideal.map r.toRingHom
      (IsLocalRing.maximalIdeal A) =
      IsLocalRing.maximalIdeal (Valued.integer K) := by
    apply le_antisymm
    · apply (Ideal.map_le_iff_le_comap).2
      intro x hx
      change r x ∈ IsLocalRing.maximalIdeal (Valued.integer K)
      rw [IsLocalRing.mem_maximalIdeal]
      intro hu
      exact (IsLocalRing.mem_maximalIdeal x).mp hx (by
        simpa only [r.symm_apply_apply] using IsUnit.map r.symm hu)
    · intro x hx
      have hy : r.symm x ∈ IsLocalRing.maximalIdeal A := by
        rw [IsLocalRing.mem_maximalIdeal]
        intro hu
        apply (IsLocalRing.mem_maximalIdeal x).mp hx
        have hu' : IsUnit (r (r.symm x)) := IsUnit.map r hu
        simpa using hu'
      have hmem := Ideal.mem_map_of_mem r.toRingHom hy
      change r (r.symm x) ∈ Ideal.map r.toRingHom
        (IsLocalRing.maximalIdeal A) at hmem
      simpa only [r.apply_symm_apply] using hmem
  have hrpow (n : ℕ) : Ideal.map r.toRingHom
      ((IsLocalRing.maximalIdeal A) ^ n) =
      Ideal.span ({((π : v.Uniformizer).val : Valued.integer K) ^ n} :
        Set (Valued.integer K)) := by
    rw [Ideal.map_pow, hrmax, hmaxV_pow]
  let fV : Valued.integer K →+* B := by
    let fVK : Valued.integer K →+* C :=
      (UniformSpace.Completion.coeRingHom).comp
        (SubringClass.subtype (Valued.integer K))
    have hfVK : ∀ a : Valued.integer K, fVK a ∈ (B : Set C) := by
      intro a
      change chapter07CompletionValuation K ℤᵐ⁰
        (((a : Valued.integer K) : K) : C) ≤ 1
      rw [chapter07_completion_valuation_apply_coe]
      exact a.property
    exact fVK.codRestrict B hfVK
  have hfVπ : fV (π.val : Valued.integer K) =
      chapter07CompletedUniformizer π := by
    apply Subtype.ext
    rfl
  have hcanonV : ∀ n : ℕ, 1 ≤ n →
      Function.Bijective
        (Ideal.Quotient.lift
          (Ideal.span ({(π.val : Valued.integer K) ^ n} : Set
            (Valued.integer K)))
          ((Ideal.Quotient.mk
            (Ideal.span ({(chapter07CompletedUniformizer π) ^ n} : Set B))).comp fV)
          (by
            intro a ha
            apply Ideal.Quotient.eq_zero_iff_mem.mpr
            have hmap : Ideal.map fV
                (Ideal.span ({(π.val : Valued.integer K) ^ n} : Set
                  (Valued.integer K))) ≤
                Ideal.span ({(chapter07CompletedUniformizer π) ^ n} : Set B) := by
              rw [Ideal.map_span]
              apply Ideal.span_mono
              rintro y ⟨x, hx, rfl⟩
              have hx' : x = (π.val : Valued.integer K) ^ n := by simpa using hx
              subst x
              rw [map_pow, hfVπ]
              exact Set.mem_singleton _
            exact (Ideal.map_le_iff_le_comap.mp hmap) ha)) := by
    intro n hn
    let Jv : Ideal (Valued.integer K) :=
      Ideal.span ({(π.val : Valued.integer K) ^ n} : Set (Valued.integer K))
    let Jb : Ideal B :=
      Ideal.span ({(chapter07CompletedUniformizer π) ^ n} : Set B)
    let g : (Valued.integer K) ⧸ Jv →+* B ⧸ Jb :=
      Ideal.Quotient.lift Jv ((Ideal.Quotient.mk Jb).comp fV) (by
        intro a ha
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        have hmap : Ideal.map fV Jv ≤ Jb := by
          rw [show Jv = Ideal.span ({(π.val : Valued.integer K) ^ n} :
            Set (Valued.integer K)) by rfl,
            show Jb = Ideal.span ({(chapter07CompletedUniformizer π) ^ n} : Set B)
              by rfl,
            Ideal.map_span]
          apply Ideal.span_mono
          rintro y ⟨x, hx, rfl⟩
          have hx' : x = (π.val : Valued.integer K) ^ n := by simpa using hx
          subst x
          rw [map_pow, hfVπ]
          exact Set.mem_singleton _
        exact (Ideal.map_le_iff_le_comap.mp hmap) ha)
    have hpval : 0 < chapter07CompletionValuation K ℤᵐ⁰
        (chapter07CompletedUniformizer π : B) := by
      rw [chapter07_completed_uniformizer_preserves_value]
      exact π.valuation_gt_one.val_pos
    let δ : MonoidWithZeroHom.ValueGroup₀
        (.ofClass (Valued.v : Valuation C ℤᵐ⁰)) :=
      (Valued.v : Valuation C ℤᵐ⁰).restrict
        (((chapter07CompletedUniformizer π : B) : C) ^ n)
    have quotient_approx : ∀ y : B, ∃ a : Valued.integer K,
        y - fV a ∈ Jb := by
      intro y
      have hyclosure : (y : C) ∈
          closure (Set.range (@chapter07ValuationRingCompletionEmbedding K ℤᵐ⁰ _ _ _)) := by
        apply chapter07_completed_unit_ball_is_approximated_by_integral_elements
        exact y.property
      let U : Set C := {z |
        (Valued.v : Valuation C ℤᵐ⁰).restrict (z - (y : C)) < δ}
      have hUopen : IsOpen U := by
        have hball := Valued.isOpen_ball C δ
        have htop : Valued.valuedCompletion.toTopologicalSpace =
            (UniformSpace.Completion.uniformSpace K).toTopologicalSpace := by rfl
        rw [htop] at hball
        simpa [U] using hball.preimage (continuous_id.sub continuous_const)
      have hδpos : 0 < δ := by
        apply (Valuation.restrict_pos_iff
          (Valued.v : Valuation C ℤᵐ⁰) _).2
        rw [map_pow]
        have hpval' : 0 < (Valued.v : Valuation C ℤᵐ⁰)
            ((chapter07CompletedUniformizer π : B) : C) := by
          rw [show (Valued.v : Valuation C ℤᵐ⁰) =
            chapter07CompletionValuation K ℤᵐ⁰ by rfl]
          exact hpval
        exact pow_pos hpval' n
      have hUmem : U ∈ 𝓝 (y : C) := by
        apply hUopen.mem_nhds
        simp [U, hδpos]
      obtain ⟨z, hzU, ⟨a, rfl⟩⟩ :=
        (mem_closure_iff_nhds.mp hyclosure) U hUmem
      refine ⟨a, ?_⟩
      have hlt : chapter07CompletionValuation K ℤᵐ⁰
          (((fV a : B) : C) - (y : C)) <
          chapter07CompletionValuation K ℤᵐ⁰
            (((chapter07CompletedUniformizer π : B) : C) ^ n) := by
        have hrestrict : (Valued.v : Valuation C ℤᵐ⁰).restrict
            (chapter07ValuationRingCompletionEmbedding a - (y : C)) < δ := by
          change (Valued.v : Valuation C ℤᵐ⁰).restrict
            ((((a : Valued.integer K) : K) : C) - (y : C)) < δ at hzU
          exact hzU
        have hlt' := (Valuation.restrict_lt_iff_lt_embedding
          (v := (Valued.v : Valuation C ℤᵐ⁰))).mp hrestrict
        have hltVal : (Valued.v : Valuation C ℤᵐ⁰)
            (chapter07ValuationRingCompletionEmbedding a - (y : C)) <
            (Valued.v : Valuation C ℤᵐ⁰)
              (((chapter07CompletedUniformizer π : B) : C) ^ n) := by
          simpa [δ, Valuation.embedding_restrict] using hlt'
        change chapter07CompletionValuation K ℤᵐ⁰
          (chapter07ValuationRingCompletionEmbedding a - (y : C)) <
          chapter07CompletionValuation K ℤᵐ⁰
            (((chapter07CompletedUniformizer π : B) : C) ^ n)
        simpa [show (Valued.v : Valuation C ℤᵐ⁰) =
          chapter07CompletionValuation K ℤᵐ⁰ by rfl] using hltVal
      have hle : chapter07CompletionValuation K ℤᵐ⁰
          (((y - fV a : B) : B) : C) ≤
          chapter07CompletionValuation K ℤᵐ⁰
            (((chapter07CompletedUniformizer π : B) : C) ^ n) := by
        have hlt' : chapter07CompletionValuation K ℤᵐ⁰
            ((y : C) - (fV a : C)) <
            chapter07CompletionValuation K ℤᵐ⁰
              (((chapter07CompletedUniformizer π : B) : C) ^ n) := by
          rw [show (y : C) - (fV a : C) =
            -((fV a : C) - (y : C)) by ring,
            Valuation.map_neg (chapter07CompletionValuation K ℤᵐ⁰)]
          exact hlt
        exact hlt'.le
      change (y - fV a : B) ∈ Jb
      have hspan : (Jb : Set B) = {x : B |
          chapter07CompletionValuation K ℤᵐ⁰ (x : C) ≤
            chapter07CompletionValuation K ℤᵐ⁰
              (((chapter07CompletedUniformizer π : B) : C) ^ n)} := by
        exact Valuation.integer.coe_span_singleton_eq_setOfPred_le_v_coe _
      change (y - fV a : B) ∈ (Jb : Set B)
      rw [hspan]
      exact hle
    have g_surj : Function.Surjective g := by
      intro x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨a, ha⟩ := quotient_approx y
      refine ⟨Ideal.Quotient.mk Jv a, ?_⟩
      rw [Ideal.Quotient.lift_mk]
      rw [← sub_eq_zero]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      simpa [sub_eq_add_neg, add_comm] using Jb.neg_mem ha
    have g_inj : Function.Injective g := by
      intro x y hxy
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [← sub_eq_zero]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      change (a - b : Valued.integer K) ∈ Jv
      have hmemC : fV a - fV b ∈ Jb := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        rw [map_sub]
        exact sub_eq_zero.mpr (by simpa [g] using hxy)
      have hspanC : (Jb : Set B) = {x : B |
          chapter07CompletionValuation K ℤᵐ⁰ (x : C) ≤
            chapter07CompletionValuation K ℤᵐ⁰
              (((chapter07CompletedUniformizer π : B) : C) ^ n)} := by
        exact Valuation.integer.coe_span_singleton_eq_setOfPred_le_v_coe _
      have hmemC' : fV a - fV b ∈ (Jb : Set B) := hmemC
      rw [hspanC] at hmemC'
      have hleC : chapter07CompletionValuation K ℤᵐ⁰
          (((fV a - fV b : B) : B) : C) ≤
          chapter07CompletionValuation K ℤᵐ⁰
            (((chapter07CompletedUniformizer π : B) : C) ^ n) := by
        exact hmemC'
      have hleK : v (((a : Valued.integer K) : K) -
          ((b : Valued.integer K) : K)) ≤ v (π.val : K) ^ n := by
        have hleC' : chapter07CompletionValuation K ℤᵐ⁰
            (((((a : Valued.integer K) : K) -
              ((b : Valued.integer K) : K)) : K) : C) ≤
            chapter07CompletionValuation K ℤᵐ⁰
              (((chapter07CompletedUniformizer π : B) : C) ^ n) := by
          have hcoediff :
              (((fV a : B) : C) - ((fV b : B) : C)) =
                (((((a : Valued.integer K) : K) -
                  ((b : Valued.integer K) : K)) : K) : C) := by
            dsimp [fV]
            symm
            exact (UniformSpace.Completion.coeRingHom : K →+* C).map_sub _ _
          rw [show (((fV a - fV b : B) : B) : C) =
            ((fV a : B) : C) - ((fV b : B) : C) by rfl]
              at hleC
          rw [hcoediff] at hleC
          exact hleC
        rw [chapter07_completion_valuation_apply_coe] at hleC'
        rw [map_pow, chapter07_completed_uniformizer_preserves_value] at hleC'
        exact hleC'
      change (a - b : Valued.integer K) ∈
        (Ideal.span ({(π.val : Valued.integer K) ^ n} : Set (Valued.integer K)) :
          Set (Valued.integer K))
      rw [Valuation.integer.coe_span_singleton_eq_setOfPred_le_v_coe]
      change v (((a - b : Valued.integer K) : K)) ≤
        v ((((π.val : Valued.integer K) ^ n : Valued.integer K) : K))
      convert hleK using 1
      · rfl
      · change v ((π.val : K) ^ n) = v (π.val : K) ^ n
        rw [map_pow]
    exact ⟨g_inj, g_surj⟩
  let vC : Valuation C ℤᵐ⁰ := chapter07CompletionValuation K ℤᵐ⁰
  have hvalueGroup : valueGroup (.ofClass vC) = valueGroup (.ofClass v) := by
    apply le_antisymm
    · intro γ hγ
      have hγ' : (γ : ℤᵐ⁰) ∈ Set.range (MonoidWithZeroHom.ofClass vC) \ {0} := by
        rw [← MonoidWithZeroHom.valueGroup_eq_range (.ofClass vC)]
        exact ⟨γ, hγ, rfl⟩
      obtain ⟨⟨x, hx⟩, _hx0⟩ := hγ'
      obtain ⟨r, hr⟩ := Valued.exists_coe_eq_v x
      have hval : (γ : ℤᵐ⁰) = v r := by
        calc
          (γ : ℤᵐ⁰) = vC x := hx.symm
          _ = v r := by
            change Valued.extensionValuation x = Valued.v r
            exact hr
      have hr0 : r ≠ 0 := by
        intro hr0
        subst r
        simp [v] at hval
      have hvr0 : v r ≠ 0 := by
        intro hvr0
        exact γ.ne_zero (hval.trans hvr0)
      have hγeq : Units.mk0 (v r) hvr0 = γ := by
        apply Units.ext
        exact hval.symm
      rw [← hγeq]
      exact MonoidWithZeroHom.mem_valueGroup (.ofClass v) ⟨r, rfl⟩
    · intro γ hγ
      have hγ' : (γ : ℤᵐ⁰) ∈ Set.range (MonoidWithZeroHom.ofClass v) \ {0} := by
        rw [← MonoidWithZeroHom.valueGroup_eq_range (.ofClass v)]
        exact ⟨γ, hγ, rfl⟩
      obtain ⟨⟨r, hr⟩, hr0⟩ := hγ'
      have hval : (γ : ℤᵐ⁰) = v r := by
        simpa [v] using hr.symm
      have hvr0 : v r ≠ 0 := by
        intro hvr0
        exact γ.ne_zero (hval.trans hvr0)
      have hvcval : vC ((r : K) : C) = v r := by
        change chapter07CompletionValuation K ℤᵐ⁰ ((r : K) : C) = Valued.v r
        rw [chapter07_completion_valuation_apply_coe]
      have hvc0 : vC ((r : K) : C) ≠ 0 := by
        simpa [hvcval] using hvr0
      have hγeq : Units.mk0 (vC ((r : K) : C)) hvc0 = γ := by
        apply Units.ext
        exact hvcval.trans hval.symm
      rw [← hγeq]
      exact MonoidWithZeroHom.mem_valueGroup (.ofClass vC) ⟨(r : C), rfl⟩
  let : vC.IsRankOneDiscrete := by
    refine ⟨⟨Valuation.IsRankOneDiscrete.generator v, ?_, ?_⟩⟩
    · rw [hvalueGroup]
      exact Valuation.IsRankOneDiscrete.generator_zpowers_eq_valueGroup v
    · exact Valuation.IsRankOneDiscrete.generator_lt_one v
  have hgenC : Valuation.IsRankOneDiscrete.generator vC =
      Valuation.IsRankOneDiscrete.generator v := by
    apply LinearOrderedCommGroup.Subgroup.genLTOne_unique_of_zpowers_eq
      (Valuation.IsRankOneDiscrete.generator_lt_one vC)
      (Valuation.IsRankOneDiscrete.generator_lt_one v)
    calc
      Subgroup.zpowers (Valuation.IsRankOneDiscrete.generator vC) =
          valueGroup (.ofClass vC) :=
        Valuation.IsRankOneDiscrete.generator_zpowers_eq_valueGroup vC
      _ = valueGroup (.ofClass v) := hvalueGroup
      _ = Subgroup.zpowers (Valuation.IsRankOneDiscrete.generator v) :=
        (Valuation.IsRankOneDiscrete.generator_zpowers_eq_valueGroup v).symm
  let πC : vC.Uniformizer :=
    { val := chapter07CompletedUniformizer π
      valuation_gt_one := by
        rw [Valuation.IsUniformizer.iff]
        rw [chapter07_completed_uniformizer_preserves_value]
        rw [hgenC]
        exact π.valuation_gt_one.val }
  have hmaxB : IsLocalRing.maximalIdeal B =
      Ideal.span ({(chapter07CompletedUniformizer π : B)} : Set B) := by
    change IsLocalRing.maximalIdeal vC.valuationSubring = _
    exact πC.valuation_gt_one.is_generator
  have hmaxB_pow (n : ℕ) : IsLocalRing.maximalIdeal B ^ n =
      Ideal.span ({(chapter07CompletedUniformizer π : B) ^ n} : Set B) := by
    rw [hmaxB]
    exact Ideal.span_singleton_pow _ n
  have hcompleteB : IsAdicComplete
      (Ideal.span ({(chapter07CompletedUniformizer π : B)} : Set B)) B := by
    rw [← hmaxB]
    exact (chapter07_completed_valuation_ring_is_dvr (K := K) (Γ₀ := ℤᵐ⁰)).2
  have hfr : f = fV.comp r.toRingHom := by
    ext a
    rfl
  let gV (n : ℕ) :
      (Valued.integer K) ⧸
          Ideal.span ({(π.val : Valued.integer K) ^ n} : Set (Valued.integer K)) →+*
        B ⧸ Ideal.span ({(chapter07CompletedUniformizer π) ^ n} : Set B) :=
    Ideal.Quotient.lift
      (Ideal.span ({(π.val : Valued.integer K) ^ n} : Set (Valued.integer K)))
      ((Ideal.Quotient.mk
        (Ideal.span ({(chapter07CompletedUniformizer π) ^ n} : Set B))).comp fV)
      (by
        intro a ha
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        have hmap : Ideal.map fV
            (Ideal.span ({(π.val : Valued.integer K) ^ n} : Set (Valued.integer K))) ≤
            Ideal.span ({(chapter07CompletedUniformizer π) ^ n} : Set B) := by
          rw [Ideal.map_span]
          apply Ideal.span_mono
          rintro y ⟨x, hx, rfl⟩
          have hx' : x = (π.val : Valued.integer K) ^ n := by simpa using hx
          subst x
          rw [map_pow, hfVπ]
          exact Set.mem_singleton _
        exact (Ideal.map_le_iff_le_comap.mp hmap) ha)
  have hgV_bij (n : ℕ) (hn : 1 ≤ n) : Function.Bijective (gV n) := by
    simpa [gV] using hcanonV n hn
  let eAV (n : ℕ) :
      A ⧸ (IsLocalRing.maximalIdeal A) ^ n ≃+*
        (Valued.integer K) ⧸
          Ideal.span ({(π.val : Valued.integer K) ^ n} : Set (Valued.integer K)) :=
    Ideal.quotientEquiv ((IsLocalRing.maximalIdeal A) ^ n)
      (Ideal.span ({(π.val : Valued.integer K) ^ n} : Set (Valued.integer K)))
      r (hrpow n).symm
  have heAV_mk (n : ℕ) (a : A) :
      eAV n (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) a) =
        Ideal.Quotient.mk
          (Ideal.span ({(π.val : Valued.integer K) ^ n} : Set (Valued.integer K))) (r a) := by
    dsimp [eAV]
    rfl
  let eVB (n : ℕ) (hn : 1 ≤ n) :
      (Valued.integer K) ⧸
          Ideal.span ({(π.val : Valued.integer K) ^ n} : Set (Valued.integer K)) ≃+*
        B ⧸ Ideal.span ({(chapter07CompletedUniformizer π) ^ n} : Set B) :=
    RingEquiv.ofBijective (gV n) (hgV_bij n hn)
  let eAB (n : ℕ) (hn : 1 ≤ n) :
      A ⧸ (IsLocalRing.maximalIdeal A) ^ n ≃+*
        B ⧸ Ideal.span ({(chapter07CompletedUniformizer π) ^ n} : Set B) :=
    (eAV n).trans (eVB n hn)
  have heAB_mk (n : ℕ) (hn : 1 ≤ n) (a : A) :
      eAB n hn (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) a) =
        Ideal.Quotient.mk
          (Ideal.span ({(chapter07CompletedUniformizer π) ^ n} : Set B)) (f a) := by
    change eVB n hn (eAV n (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) a)) = _
    change gV n (eAV n (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) a)) = _
    rw [heAV_mk]
    dsimp [gV]
    change Ideal.Quotient.mk
        (Ideal.span ({(chapter07CompletedUniformizer π) ^ n} : Set B))
      (fV (r a)) = _
    have hfa : fV (r a) = f a := by
      have hfa' := congrArg (fun q : A →+* B => q a) hfr.symm
      change fV (r.toRingHom a) = f a at hfa'
      have hra : r.toRingHom a = r a :=
        congrFun (RingEquiv.coe_toRingHom r) a
      rw [hra] at hfa'
      exact hfa'
    rw [hfa]
  have hgV0_bij : Function.Bijective (gV 0) := by
    have hsubV : Subsingleton ((Valued.integer K) ⧸
        Ideal.span ({(π.val : Valued.integer K) ^ (0 : ℕ)} : Set (Valued.integer K))) := by
      rw [show Ideal.span ({(π.val : Valued.integer K) ^ (0 : ℕ)} : Set (Valued.integer K)) =
        ⊤ by simp]
      infer_instance
    have hsubB : Subsingleton (B ⧸
        Ideal.span ({(chapter07CompletedUniformizer π) ^ (0 : ℕ)} : Set B)) := by
      rw [show Ideal.span ({(chapter07CompletedUniformizer π) ^ (0 : ℕ)} : Set B) =
        ⊤ by simp]
      infer_instance
    constructor
    · intro x y _
      exact hsubV.elim x y
    · intro y
      exact ⟨0, hsubB.elim _ _⟩
  have hgV_all (n : ℕ) : Function.Bijective (gV n) := by
    cases n with
    | zero => exact hgV0_bij
    | succ n => exact hgV_bij (n + 1) (by omega)
  let eVB_all (n : ℕ) :
      (Valued.integer K) ⧸
          Ideal.span ({(π.val : Valued.integer K) ^ n} : Set (Valued.integer K)) ≃+*
        B ⧸ Ideal.span ({(chapter07CompletedUniformizer π) ^ n} : Set B) :=
    RingEquiv.ofBijective (gV n) (hgV_all n)
  let eAB_all (n : ℕ) :
      A ⧸ (IsLocalRing.maximalIdeal A) ^ n ≃+*
        B ⧸ Ideal.span ({(chapter07CompletedUniformizer π) ^ n} : Set B) :=
    (eAV n).trans (eVB_all n)
  have heAB_all_mk (n : ℕ) (a : A) :
      eAB_all n (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) a) =
        Ideal.Quotient.mk
          (Ideal.span ({(chapter07CompletedUniformizer π) ^ n} : Set B)) (f a) := by
    change eVB_all n (eAV n (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) a)) = _
    change gV n (eAV n (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) a)) = _
    rw [heAV_mk]
    dsimp [gV]
    change Ideal.Quotient.mk
        (Ideal.span ({(chapter07CompletedUniformizer π) ^ n} : Set B))
      (fV (r a)) = _
    have hfa : fV (r a) = f a := by
      have hfa' := congrArg (fun q : A →+* B => q a) hfr.symm
      change fV (r.toRingHom a) = f a at hfa'
      have hra : r.toRingHom a = r a :=
        congrFun (RingEquiv.coe_toRingHom r) a
      rw [hra] at hfa'
      exact hfa'
    rw [hfa]
  let J0 : Ideal B :=
    Ideal.span ({(chapter07CompletedUniformizer π : B)} : Set B)
  have hJ0pow (n : ℕ) : J0 ^ n =
      Ideal.span ({(chapter07CompletedUniformizer π : B) ^ n} : Set B) := by
    dsimp [J0]
    exact Ideal.span_singleton_pow _ n
  let tB (n : ℕ) :
      B ⧸ Ideal.span ({(chapter07CompletedUniformizer π : B) ^ n} : Set B) ≃+*
        B ⧸ J0 ^ n :=
    Ideal.quotientEquiv
      (Ideal.span ({(chapter07CompletedUniformizer π : B) ^ n} : Set B)) (J0 ^ n)
      (RingEquiv.refl B) (by simpa using hJ0pow n)
  let eABp (n : ℕ) :
      A ⧸ (IsLocalRing.maximalIdeal A) ^ n ≃+* B ⧸ J0 ^ n :=
    (eAB_all n).trans (tB n)
  have heABp_mk (n : ℕ) (a : A) :
      eABp n (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) a) =
        Ideal.Quotient.mk (J0 ^ n) (f a) := by
    dsimp [eABp, tB]
    rw [heAB_all_mk, Ideal.quotientEquiv_mk]
    simp
  let F (n : ℕ) :
      AdicCompletion (IsLocalRing.maximalIdeal A) A →+* B ⧸ J0 ^ n :=
    (eABp n).toRingHom.comp
      (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n).toRingHom
  have hEval {m n : ℕ} (hle : m ≤ n) :
      (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal A) hle).comp
          (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n).toRingHom =
        (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) m).toRingHom := by
    ext x
    let hn : ((IsLocalRing.maximalIdeal A) ^ n • ⊤ : Ideal A) =
        (IsLocalRing.maximalIdeal A) ^ n := by ext y; simp
    let hm : ((IsLocalRing.maximalIdeal A) ^ m • ⊤ : Ideal A) =
        (IsLocalRing.maximalIdeal A) ^ m := by ext y; simp
    change (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal A) hle)
        ((Ideal.quotientEquivAlgOfEq A hn)
          (AdicCompletion.eval (IsLocalRing.maximalIdeal A) A n x)) =
      (Ideal.quotientEquivAlgOfEq A hm)
        (AdicCompletion.eval (IsLocalRing.maximalIdeal A) A m x)
    change (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal A) hle)
        (Ideal.Quotient.factor (le_of_eq hn)
          (AdicCompletion.eval (IsLocalRing.maximalIdeal A) A n x)) =
      Ideal.Quotient.factor (le_of_eq hm)
        (AdicCompletion.eval (IsLocalRing.maximalIdeal A) A m x)
    change (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal A) hle)
        (Ideal.Quotient.factor (le_of_eq hn) (x.val n)) =
      Ideal.Quotient.factor (le_of_eq hm) (x.val m)
    rw [← x.property hle]
    induction x.val n using Quotient.inductionOn' with
    | _ a =>
      rfl
  have heABp_nat {m n : ℕ} (hle : m ≤ n) :
      (Ideal.Quotient.factorPow J0 hle).comp (eABp n).toRingHom =
        (eABp m).toRingHom.comp
          (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal A) hle) := by
    apply RingHom.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [RingHom.comp_apply]
    change (Ideal.Quotient.factorPow J0 hle)
        (eABp n (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) a)) =
      eABp m ((Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal A) hle)
        (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) a))
    calc
      (Ideal.Quotient.factorPow J0 hle)
          (eABp n (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) a)) =
          (Ideal.Quotient.factorPow J0 hle)
            (Ideal.Quotient.mk (J0 ^ n) (f a)) := by rw [heABp_mk]
      _ = Ideal.Quotient.mk (J0 ^ m) (f a) := by
        rw [Ideal.Quotient.factor_mk]
      _ = eABp m (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ m) a) := by
        rw [heABp_mk]
      _ = eABp m ((Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal A) hle)
          (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) a)) := by
        rw [Ideal.Quotient.factor_mk]
  have hFcompat {m n : ℕ} (hle : m ≤ n) :
      (Ideal.Quotient.factorPow J0 hle).comp (F n) = F m := by
    dsimp [F]
    calc
      (Ideal.Quotient.factorPow J0 hle).comp
          ((eABp n).toRingHom.comp
            (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n).toRingHom) =
          ((Ideal.Quotient.factorPow J0 hle).comp (eABp n).toRingHom).comp
            (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n).toRingHom := by
              rw [RingHom.comp_assoc]
      _ = ((eABp m).toRingHom.comp
            (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal A) hle)).comp
            (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n).toRingHom := by
              rw [heABp_nat hle]
      _ = (eABp m).toRingHom.comp
            ((Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal A) hle).comp
              (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n).toRingHom) := by
              rw [RingHom.comp_assoc]
      _ = (eABp m).toRingHom.comp
            (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) m).toRingHom := by
              rw [hEval hle]
      _ = F m := rfl
  have heABp_inv_nat {m n : ℕ} (hle : m ≤ n) :
      (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal A) hle).comp
          (eABp n).symm.toRingHom =
        (eABp m).symm.toRingHom.comp (Ideal.Quotient.factorPow J0 hle) := by
    apply RingHom.ext
    intro x
    obtain ⟨y, rfl⟩ := (eABp n).surjective x
    have h := congrArg (fun q => q y) (heABp_nat hle)
    have h' := congrArg (eABp m).symm h
    simpa [RingHom.comp_apply] using h'.symm
  let G (n : ℕ) : B →+*
      A ⧸ (IsLocalRing.maximalIdeal A) ^ n :=
    (eABp n).symm.toRingHom.comp
      (Ideal.Quotient.mk (J0 ^ n))
  have hGcompat {m n : ℕ} (hle : m ≤ n) :
      (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal A) hle).comp (G n) = G m := by
    dsimp [G]
    calc
      (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal A) hle).comp
          ((eABp n).symm.toRingHom.comp (Ideal.Quotient.mk (J0 ^ n))) =
          ((Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal A) hle).comp
            (eABp n).symm.toRingHom).comp (Ideal.Quotient.mk (J0 ^ n)) := by
              rw [RingHom.comp_assoc]
      _ = ((eABp m).symm.toRingHom.comp
            (Ideal.Quotient.factorPow J0 hle)).comp
            (Ideal.Quotient.mk (J0 ^ n)) := by
              rw [heABp_inv_nat hle]
      _ = (eABp m).symm.toRingHom.comp
            ((Ideal.Quotient.factorPow J0 hle).comp
              (Ideal.Quotient.mk (J0 ^ n))) := by
              rw [RingHom.comp_assoc]
      _ = (eABp m).symm.toRingHom.comp
            (Ideal.Quotient.mk (J0 ^ m)) := by
              rw [show (Ideal.Quotient.factorPow J0 hle).comp
                (Ideal.Quotient.mk (J0 ^ n)) = Ideal.Quotient.mk (J0 ^ m) by
                  exact Ideal.Quotient.factor_comp_mk
                    (Ideal.pow_le_pow_right hle)]
      _ = G m := rfl
  let eAdic : AdicCompletion (IsLocalRing.maximalIdeal A) A →+* B :=
    IsAdicComplete.liftRingHom J0 F hFcompat
  let eInv : B →+* AdicCompletion (IsLocalRing.maximalIdeal A) A :=
    AdicCompletion.liftRingHom (IsLocalRing.maximalIdeal A) G hGcompat
  have heAdic_eval (n : ℕ) (x : AdicCompletion (IsLocalRing.maximalIdeal A) A) :
      Ideal.Quotient.mk (J0 ^ n) (eAdic x) = F n x := by
    exact IsAdicComplete.mk_liftRingHom J0 F hFcompat n x
  have heInv_eval (n : ℕ) (x : B) :
      AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n (eInv x) = G n x := by
    exact AdicCompletion.evalₐ_liftRingHom
      (IsLocalRing.maximalIdeal A) G hGcompat n x
  have hAC : ∀ x : AdicCompletion (IsLocalRing.maximalIdeal A) A,
      eInv (eAdic x) = x := by
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    apply (eABp n).injective
    calc
      eABp n (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n
          (eInv (eAdic x))) = eABp n (G n (eAdic x)) := by
            rw [heInv_eval]
      _ = Ideal.Quotient.mk (J0 ^ n) (eAdic x) := by
            dsimp [G]
            simp
      _ = F n x := heAdic_eval n x
      _ = eABp n (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n x) := rfl
  have hB : ∀ y : B, eAdic (eInv y) = y := by
    intro y
    have hfun : (fun _ : Unit => eAdic (eInv y)) = (fun _ : Unit => y) := by
      apply IsHausdorff.funext' J0
      intro n z
      calc
        Ideal.Quotient.mk (J0 ^ n) (eAdic (eInv y)) = F n (eInv y) :=
          heAdic_eval n (eInv y)
        _ = eABp n (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n (eInv y)) := rfl
        _ = eABp n (G n y) := by rw [heInv_eval]
        _ = Ideal.Quotient.mk (J0 ^ n) y := by
          dsimp [G]
          simp
    exact congrFun hfun ()
  have heInv_bij : Function.Bijective eInv := by
    constructor
    · intro x y hxy
      have h := congrArg eAdic hxy
      simpa [hB] using h
    · intro y
      exact ⟨eAdic y, hAC y⟩
  let eBA : B ≃+* AdicCompletion (IsLocalRing.maximalIdeal A) A :=
    RingEquiv.ofBijective eInv heInv_bij
  let eRing : @UniformSpace.Completion A (chapter07DvrUniformSpace A) ≃+* B :=
    { eU.toEquiv with
      map_add' := hadd
      map_mul' := hmul }
  have hInv_f (a : A) :
      eBA (f a) = chapter07AdicCompletionMap (IsLocalRing.maximalIdeal A) a := by
    change eInv (f a) = chapter07AdicCompletionMap (IsLocalRing.maximalIdeal A) a
    apply AdicCompletion.ext_evalₐ
    intro n
    apply (eABp n).injective
    calc
      eABp n (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n
          (eInv (f a))) = eABp n (G n (f a)) := by
            rw [heInv_eval]
      _ = Ideal.Quotient.mk (J0 ^ n) (f a) := by
            dsimp [G]
            simp
      _ = eABp n
          (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) a) :=
            (heABp_mk n a).symm
      _ = eABp n (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n
          (chapter07AdicCompletionMap (IsLocalRing.maximalIdeal A) a)) := by
            simp [chapter07AdicCompletionMap, AdicCompletion.algebraMap_apply]
  refine ⟨eRing.trans eBA, ?_⟩
  intro a
  rw [RingEquiv.trans_apply]
  change eBA (eU ((a : A) : @UniformSpace.Completion A
    (chapter07DvrUniformSpace A))) = _
  rw [eU_coe]
  exact hInv_f a

-- The finite filtration is unchanged by completion in the DVR case.
theorem chapter07_dvr_adic_completion_preserves_finite_filtration
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (π : A) (hπ : Irreducible π) :
    ∀ n : ℕ, 1 ≤ n →
      Nonempty
        (A ⧸ Ideal.span ({π ^ n} : Set A) ≃+*
          AdicCompletion (IsLocalRing.maximalIdeal A) A ⧸ Ideal.span
            ({chapter07AdicCompletionMap (IsLocalRing.maximalIdeal A) (π ^ n)} : Set
              (AdicCompletion (IsLocalRing.maximalIdeal A) A))) := by
  intro n _
  have hfg : (IsLocalRing.maximalIdeal A).FG :=
    (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
  have hπM : Ideal.span ({π} : Set A) = IsLocalRing.maximalIdeal A :=
    chapter07_dvr_uniformizer_generates_maximal_ideal π hπ
  have hπpow :
      Ideal.span ({π ^ n} : Set A) = (IsLocalRing.maximalIdeal A) ^ n := by
    rw [← Ideal.span_singleton_pow, hπM]
  have hzero (x : AdicCompletion (IsLocalRing.maximalIdeal A) A) :
      AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n x = 0 ↔
        AdicCompletion.eval (IsLocalRing.maximalIdeal A) A n x = 0 := by
    have h :
        ((IsLocalRing.maximalIdeal A) ^ n • (⊤ : Ideal A)) ≤
          (IsLocalRing.maximalIdeal A) ^ n := by
      simp
    have hf : Function.Injective (Ideal.Quotient.factor h) := by
      rw [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.factor_ker]
      have heq :
          (IsLocalRing.maximalIdeal A ^ n • (⊤ : Ideal A)) =
            IsLocalRing.maximalIdeal A ^ n := by
        rw [Ideal.smul_eq_mul, Ideal.mul_top]
      rw [heq]
      exact Ideal.map_quotient_self _
    rw [← AdicCompletion.factor_eval_eq_evalₐ (IsLocalRing.maximalIdeal A) x h]
    constructor
    · intro hx
      apply hf
      simpa using hx
    · intro hx
      simp [hx]
  have hker :
      RingHom.ker (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n).toRingHom =
        ((IsLocalRing.maximalIdeal A) ^ n).map
          (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) := by
    ext x
    change AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n x = 0 ↔
      x ∈ ((IsLocalRing.maximalIdeal A) ^ n).map
        (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))
    change AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n x = 0 ↔
      x ∈ (((IsLocalRing.maximalIdeal A) ^ n).map
        (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))).restrictScalars A
    rw [← Ideal.smul_top_eq_map,
      AdicCompletion.pow_smul_top_eq_ker_eval
        (I := IsLocalRing.maximalIdeal A) (M := A) (n := n) hfg]
    simpa only [LinearMap.mem_ker] using hzero x
  have hmap :
      ((IsLocalRing.maximalIdeal A) ^ n).map
          (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) =
        Ideal.span
          ({chapter07AdicCompletionMap (IsLocalRing.maximalIdeal A) (π ^ n)} :
            Set (AdicCompletion (IsLocalRing.maximalIdeal A) A)) := by
    rw [← hπpow, Ideal.map_span]
    simp [chapter07AdicCompletionMap]
  refine ⟨(Ideal.quotEquivOfEq hπpow).trans ?_⟩
  exact
    (RingHom.quotientKerEquivOfSurjective
      (f := (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n).toRingHom)
      (AdicCompletion.surjective_evalₐ (IsLocalRing.maximalIdeal A) n)).symm.trans
      (Ideal.quotEquivOfEq (hker.trans hmap))

end
end LastLib.Book01ValuationsDVRsAndCompletions.Chapter07
