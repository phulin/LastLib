import LastLib.Book04AdelesAndIdeles.Chapter04.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter04

noncomputable section

open Set Filter
open NumberField IsDedekindDomain
open LastLib.Book04AdelesAndIdeles.Chapter01
open scoped BigOperators Topology RestrictedProduct nonZeroDivisors

/-! ### 4.3 Neighborhoods as local specifications -/

def chapter04FiniteBasicNeighborhood
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04FinitePlace K))
    (U : ∀ v : Chapter04FinitePlace K, Set (Chapter04FiniteLocalField K v)) :
    Set (Chapter04FiniteAdeleRing K) :=
  {x |
    (∀ v, v ∈ S → x v ∈ U v) ∧
    (∀ v, v ∉ S → x v ∈ chapter04FiniteLocalIntegerSet K v)}

def chapter04FiniteBasicNeighborhoodCondition
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04FinitePlace K))
    (U : ∀ v : Chapter04FinitePlace K, Set (Chapter04FiniteLocalField K v)) : Prop :=
  S.Finite ∧ ∀ v, v ∈ S → IsOpen (U v)

def chapter04FiniteDifferenceNeighborhood
    (K : Type*) [Field K] [NumberField K]
    (x₀ : Chapter04FiniteAdeleRing K)
    (S : Set (Chapter04FinitePlace K))
    (U : ∀ v : Chapter04FinitePlace K, Set (Chapter04FiniteLocalField K v)) :
    Set (Chapter04FiniteAdeleRing K) :=
  {y |
    (∀ v, v ∈ S → y v ∈ U v) ∧
      (∀ v, v ∉ S → y v - x₀ v ∈ chapter04FiniteLocalIntegerSet K v)}

theorem chapter04_mem_finiteDifferenceNeighborhood_iff
    (K : Type*) [Field K] [NumberField K]
    (x₀ : Chapter04FiniteAdeleRing K)
    (S : Set (Chapter04FinitePlace K))
    (U : ∀ v : Chapter04FinitePlace K, Set (Chapter04FiniteLocalField K v))
    (y : Chapter04FiniteAdeleRing K) :
    y ∈ chapter04FiniteDifferenceNeighborhood K x₀ S U ↔
      (∀ v, v ∈ S → y v ∈ U v) ∧
        (∀ v, v ∉ S → y v - x₀ v ∈ chapter04FiniteLocalIntegerSet K v) :=
  Iff.rfl

private def chapter04FiniteRestrictedProductBasicOpen
    {ι : Type*} (R : ι → Type*) (A : (i : ι) → Set (R i))
    (S : Set ι) (U : (i : ι) → Set (R i)) :
    Set (Πʳ i, [R i, A i]) :=
  {x | (∀ i ∈ S, x i ∈ U i) ∧ ∀ i ∉ S, x i ∈ A i}

private theorem chapter04_finiteRestrictedProduct_basicOpen_basis
    {ι : Type*} (R : ι → Type*) (A : (i : ι) → Set (R i))
    [∀ i, TopologicalSpace (R i)] (hA : ∀ i, IsOpen (A i)) :
    ∀ x : Πʳ i, [R i, A i], ∀ V ∈ 𝓝 x,
      ∃ S : Set ι, S.Finite ∧ ∃ U : (i : ι) → Set (R i),
        (∀ i, IsOpen (U i)) ∧
          x ∈ chapter04FiniteRestrictedProductBasicOpen R A S U ∧
            chapter04FiniteRestrictedProductBasicOpen R A S U ⊆ V := by
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
  have hxB : x ∈ chapter04FiniteRestrictedProductBasicOpen R A S U := by
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

theorem chapter04_finiteAdele_has_difference_local_specification_basis
    (K : Type*) [Field K] [NumberField K]
    (x₀ : Chapter04FiniteAdeleRing K) (V : Set (Chapter04FiniteAdeleRing K))
    (hV : V ∈ 𝓝 x₀) :
    ∃ S : Set (Chapter04FinitePlace K), ∃ U : ∀ v : Chapter04FinitePlace K,
      Set (Chapter04FiniteLocalField K v),
      chapter04FiniteBasicNeighborhoodCondition K S U ∧
        x₀ ∈ chapter04FiniteDifferenceNeighborhood K x₀ S U ∧
          chapter04FiniteDifferenceNeighborhood K x₀ S U ⊆ V := by
  classical
  have hAopen : ∀ v : Chapter04FinitePlace K,
      IsOpen (chapter04FiniteLocalIntegerSet K v) := by
    intro v
    exact Valued.isOpen_valuationSubring _
  rcases chapter04_finiteRestrictedProduct_basicOpen_basis
      (fun v : Chapter04FinitePlace K => Chapter04FiniteLocalField K v)
      (fun v : Chapter04FinitePlace K => chapter04FiniteLocalIntegerSet K v)
      hAopen x₀ V hV with
    ⟨S, hS, U, hU, hx₀, hsub⟩
  refine ⟨S, U, ⟨hS, fun v _ => hU v⟩, ?_, ?_⟩
  · rw [chapter04_mem_finiteDifferenceNeighborhood_iff]
    refine ⟨hx₀.1, ?_⟩
    intro v hv
    rw [sub_self]
    change (0 : Chapter04FiniteLocalField K v) ∈
      (v.adicCompletionIntegers K : Set (v.adicCompletion K))
    exact (v.adicCompletionIntegers K).zero_mem
  · intro y hy
    apply hsub
    rw [chapter04_mem_finiteDifferenceNeighborhood_iff] at hy
    refine ⟨hy.1, ?_⟩
    intro v hv
    have hyx : y v - x₀ v ∈ chapter04FiniteLocalIntegerSet K v := hy.2 v hv
    have hx₀' : x₀ v ∈ chapter04FiniteLocalIntegerSet K v := hx₀.2 v hv
    change y v - x₀ v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) at hyx
    change x₀ v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) at hx₀'
    change y v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K))
    have hsum := (v.adicCompletionIntegers K).add_mem (y v - x₀ v) (x₀ v) hyx hx₀'
    simpa [sub_add_cancel] using hsum

theorem chapter04_difference_neighborhood_agrees_with_integral_tail
    (K : Type*) [Field K] [NumberField K]
    (x₀ : Chapter04FiniteAdeleRing K)
    (S : Set (Chapter04FinitePlace K))
    (U : ∀ v : Chapter04FinitePlace K, Set (Chapter04FiniteLocalField K v))
    (hS : ∀ v, v ∉ S → x₀ v ∈ chapter04FiniteLocalIntegerSet K v) :
    chapter04FiniteDifferenceNeighborhood K x₀ S U =
      chapter04FiniteBasicNeighborhood K S U := by
  ext y
  change ((∀ v, v ∈ S → y v ∈ U v) ∧
      (∀ v, v ∉ S → y v - x₀ v ∈ chapter04FiniteLocalIntegerSet K v)) ↔
    ((∀ v, v ∈ S → y v ∈ U v) ∧
      (∀ v, v ∉ S → y v ∈ chapter04FiniteLocalIntegerSet K v))
  constructor
  · rintro ⟨hyS, hyTail⟩
    refine ⟨hyS, ?_⟩
    intro v hv
    have hyx : y v - x₀ v ∈ chapter04FiniteLocalIntegerSet K v := hyTail v hv
    have hx₀ : x₀ v ∈ chapter04FiniteLocalIntegerSet K v := hS v hv
    change y v - x₀ v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) at hyx
    change x₀ v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) at hx₀
    change y v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K))
    have hsum := (v.adicCompletionIntegers K).add_mem (y v - x₀ v) (x₀ v) hyx hx₀
    simpa [sub_add_cancel] using hsum
  · rintro ⟨hyS, hyTail⟩
    refine ⟨hyS, ?_⟩
    intro v hv
    have hy : y v ∈ chapter04FiniteLocalIntegerSet K v := hyTail v hv
    have hx₀ : x₀ v ∈ chapter04FiniteLocalIntegerSet K v := hS v hv
    change y v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) at hy
    change x₀ v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) at hx₀
    change y v - x₀ v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K))
    exact (v.adicCompletionIntegers K).toSubring.sub_mem hy hx₀

theorem chapter04_mem_finiteBasicNeighborhood_iff
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04FinitePlace K))
    (U : ∀ v : Chapter04FinitePlace K, Set (Chapter04FiniteLocalField K v))
    (x : Chapter04FiniteAdeleRing K) :
    x ∈ chapter04FiniteBasicNeighborhood K S U ↔
      (∀ v, v ∈ S → x v ∈ U v) ∧
        (∀ v, v ∉ S → x v ∈ chapter04FiniteLocalIntegerSet K v) :=
  Iff.rfl

theorem chapter04_finiteBasicNeighborhood_isOpen
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04FinitePlace K))
    (U : ∀ v : Chapter04FinitePlace K, Set (Chapter04FiniteLocalField K v))
    (hU : chapter04FiniteBasicNeighborhoodCondition K S U) :
    IsOpen (chapter04FiniteBasicNeighborhood K S U) := by
  let D : Set (Chapter04FiniteAdeleRing K) :=
    {y | ∀ v : Chapter04FinitePlace K, v ∈ S → y v ∈ U v}
  let Tail : Set (Chapter04FiniteAdeleRing K) :=
    {y | ∀ v : Chapter04FinitePlace K, v ∉ S →
      y v ∈ chapter04FiniteLocalIntegerSet K v}
  have hD : IsOpen D := by
    have hD' : IsOpen (⋂ v : Chapter04FinitePlace K, ⋂ _ : v ∈ S,
        (fun y : Chapter04FiniteAdeleRing K => y v) ⁻¹' U v) := by
      exact hU.1.isOpen_biInter fun v hv =>
        (hU.2 v hv).preimage (RestrictedProduct.continuous_eval v)
    have hDeq : D = ⋂ v : Chapter04FinitePlace K, ⋂ _ : v ∈ S,
        (fun y : Chapter04FiniteAdeleRing K => y v) ⁻¹' U v := by
      ext y
      simp only [D, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
    rw [hDeq]
    exact hD'
  have hAopen : ∀ v : Chapter04FinitePlace K,
      IsOpen (chapter04FiniteLocalIntegerSet K v) := by
    intro v
    exact Valued.isOpen_valuationSubring _
  have hTail : IsOpen Tail := by
    exact RestrictedProduct.isOpen_forall_imp_mem hAopen
  have hEq : chapter04FiniteBasicNeighborhood K S U = D ∩ Tail := by
    ext y
    simp [chapter04FiniteBasicNeighborhood, D, Tail]
  rw [hEq]
  exact hD.inter hTail

theorem chapter04_finiteAdele_has_local_specification_basis
    (K : Type*) [Field K] [NumberField K]
    (x : Chapter04FiniteAdeleRing K) (V : Set (Chapter04FiniteAdeleRing K))
    (hV : V ∈ 𝓝 x) :
    ∃ S : Set (Chapter04FinitePlace K), ∃ U : ∀ v : Chapter04FinitePlace K,
      Set (Chapter04FiniteLocalField K v),
      chapter04FiniteBasicNeighborhoodCondition K S U ∧
        x ∈ chapter04FiniteBasicNeighborhood K S U ∧
          chapter04FiniteBasicNeighborhood K S U ⊆ V := by
  classical
  have hAopen : ∀ v : Chapter04FinitePlace K,
      IsOpen (chapter04FiniteLocalIntegerSet K v) := by
    intro v
    exact Valued.isOpen_valuationSubring _
  rcases chapter04_finiteRestrictedProduct_basicOpen_basis
      (fun v : Chapter04FinitePlace K => Chapter04FiniteLocalField K v)
      (fun v : Chapter04FinitePlace K => chapter04FiniteLocalIntegerSet K v)
      hAopen x V hV with
    ⟨S, hS, U, hU, hx, hsub⟩
  refine ⟨S, U, ⟨hS, fun v _ => hU v⟩, ?_, ?_⟩
  · exact hx
  · exact hsub

def chapter04RationalLocalIntegerMultiple
    (m : ℤ) (v : Chapter04FinitePlace ℚ) :
    Set (Chapter04FiniteLocalField ℚ v) :=
  {x | ∃ z : Chapter04FiniteLocalIntegerRing ℚ v,
    x = (m : Chapter04FiniteLocalField ℚ v) * (z : Chapter04FiniteLocalField ℚ v)}

def chapter04RationalIntegerMultipleHatZ (m : ℤ) :
    Set (Chapter04FiniteAdeleRing ℚ) :=
  {x | ∀ v : Chapter04FinitePlace ℚ,
    x v ∈ chapter04RationalLocalIntegerMultiple m v}

theorem chapter04_rational_integer_multiple_hatZ_is_multiplication_by_m
    (m : ℤ) :
    chapter04RationalIntegerMultipleHatZ m =
      {x | ∃ z : Chapter04FiniteIntegralAdele ℚ,
        x = (m : Chapter04FiniteAdeleRing ℚ) *
          chapter04FiniteIntegralAdeleEmbedding ℚ z} := by
  ext x
  constructor
  · intro hx
    change ∀ v : Chapter04FinitePlace ℚ,
      ∃ z : Chapter04FiniteLocalIntegerRing ℚ v,
        x v = (m : Chapter04FiniteLocalField ℚ v) *
          (z : Chapter04FiniteLocalField ℚ v) at hx
    let z : Chapter04FiniteIntegralAdele ℚ :=
      fun v => Classical.choose (hx v)
    have hz : ∀ v : Chapter04FinitePlace ℚ,
        x v = (m : Chapter04FiniteLocalField ℚ v) *
          (z v : Chapter04FiniteLocalField ℚ v) := by
      intro v
      exact Classical.choose_spec (hx v)
    change ∃ z : Chapter04FiniteIntegralAdele ℚ,
      x = (m : Chapter04FiniteAdeleRing ℚ) *
        chapter04FiniteIntegralAdeleEmbedding ℚ z
    refine ⟨z, ?_⟩
    apply chapter04_finiteAdele_ext ℚ
    intro v
    rw [chapter04_finiteAdele_mul_apply]
    exact hz v
  · intro hx
    change ∃ z : Chapter04FiniteIntegralAdele ℚ,
      x = (m : Chapter04FiniteAdeleRing ℚ) *
        chapter04FiniteIntegralAdeleEmbedding ℚ z at hx
    rcases hx with ⟨z, rfl⟩
    change ∀ v : Chapter04FinitePlace ℚ,
      ∃ w : Chapter04FiniteLocalIntegerRing ℚ v,
        ((m : Chapter04FiniteAdeleRing ℚ) *
          chapter04FiniteIntegralAdeleEmbedding ℚ z) v =
            (m : Chapter04FiniteLocalField ℚ v) *
              (w : Chapter04FiniteLocalField ℚ v)
    intro v
    refine ⟨z v, ?_⟩
    rw [chapter04_finiteAdele_mul_apply]
    rfl

theorem chapter04_rational_integer_multiple_hatZ_is_compact_open
    (m : ℤ) (hm : m ≠ 0) :
    IsCompact (chapter04RationalIntegerMultipleHatZ m) ∧
      IsOpen (chapter04RationalIntegerMultipleHatZ m) := by
  let uℚ : ℚˣ := Units.mk0 (m : ℚ) (by exact_mod_cast hm)
  let u : (Chapter04FiniteAdeleRing ℚ)ˣ :=
    IsDedekindDomain.FiniteAdeleRing.unitEmbedding (𝓞 ℚ) ℚ uℚ
  have hu : (u : Chapter04FiniteAdeleRing ℚ) = (m : Chapter04FiniteAdeleRing ℚ) := by
    change algebraMap ℚ (Chapter04FiniteAdeleRing ℚ) (uℚ : ℚ) =
      (m : Chapter04FiniteAdeleRing ℚ)
    simp [uℚ]
  have hset :
      {x : Chapter04FiniteAdeleRing ℚ |
        ∃ z : Chapter04FiniteIntegralAdele ℚ,
          x = (m : Chapter04FiniteAdeleRing ℚ) *
            chapter04FiniteIntegralAdeleEmbedding ℚ z} =
        (fun y : Chapter04FiniteAdeleRing ℚ =>
          (u : Chapter04FiniteAdeleRing ℚ) * y) ''
          (Chapter04FiniteIntegralAdeleSubring ℚ :
            Set (Chapter04FiniteAdeleRing ℚ)) := by
    ext x
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨chapter04FiniteIntegralAdeleEmbedding ℚ z, ⟨z, rfl⟩, ?_⟩
      rw [hu]
      exact hz.symm
    · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
      refine ⟨z, ?_⟩
      rw [hu]
  rw [chapter04_rational_integer_multiple_hatZ_is_multiplication_by_m m, hset]
  constructor
  · exact (chapter04_finiteIntegralAdele_is_compact_open ℚ).1.image
      (continuous_const_mul (u : Chapter04FiniteAdeleRing ℚ))
  · exact (ContinuousAddEquiv.mulLeft u).isOpenMap _
      (chapter04_finiteIntegralAdele_is_compact_open ℚ).2

theorem chapter04_rational_integer_multiple_hatZ_is_a_neighborhood_subgroup
    (m : ℤ) (hm : m ≠ 0) :
    ∃ H : AddSubgroup (Chapter04FiniteAdeleRing ℚ),
      (H : Set (Chapter04FiniteAdeleRing ℚ)) =
        chapter04RationalIntegerMultipleHatZ m ∧
        IsCompact (H : Set (Chapter04FiniteAdeleRing ℚ)) ∧
        IsOpen (H : Set (Chapter04FiniteAdeleRing ℚ)) := by
  let uℚ : ℚˣ := Units.mk0 (m : ℚ) (by exact_mod_cast hm)
  let u : (Chapter04FiniteAdeleRing ℚ)ˣ :=
    IsDedekindDomain.FiniteAdeleRing.unitEmbedding (𝓞 ℚ) ℚ uℚ
  have hu : (u : Chapter04FiniteAdeleRing ℚ) = (m : Chapter04FiniteAdeleRing ℚ) := by
    change algebraMap ℚ (Chapter04FiniteAdeleRing ℚ) (uℚ : ℚ) =
      (m : Chapter04FiniteAdeleRing ℚ)
    simp [uℚ]
  let H : AddSubgroup (Chapter04FiniteAdeleRing ℚ) :=
    (Chapter04FiniteIntegralAdeleAddSubgroup ℚ).map
      (ContinuousAddEquiv.mulLeft u).toAddMonoidHom
  have hset :
      (H : Set (Chapter04FiniteAdeleRing ℚ)) =
        chapter04RationalIntegerMultipleHatZ m := by
    rw [AddSubgroup.coe_map]
    rw [chapter04_rational_integer_multiple_hatZ_is_multiplication_by_m m]
    ext x
    constructor
    · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
      refine ⟨z, ?_⟩
      change (u : Chapter04FiniteAdeleRing ℚ) *
        chapter04FiniteIntegralAdeleEmbedding ℚ z =
          (m : Chapter04FiniteAdeleRing ℚ) *
            chapter04FiniteIntegralAdeleEmbedding ℚ z
      rw [hu]
    · rintro ⟨z, hz⟩
      refine ⟨chapter04FiniteIntegralAdeleEmbedding ℚ z, ⟨z, rfl⟩, ?_⟩
      change (u : Chapter04FiniteAdeleRing ℚ) *
        chapter04FiniteIntegralAdeleEmbedding ℚ z = x
      rw [hu]
      exact hz.symm
  refine ⟨H, hset, ?_, ?_⟩
  · rw [hset]
    exact (chapter04_rational_integer_multiple_hatZ_is_compact_open m hm).1
  · rw [hset]
    exact (chapter04_rational_integer_multiple_hatZ_is_compact_open m hm).2

def chapter04FractionalIdealCompletion
    (K : Type*) [Field K] [NumberField K]
  (I : FractionalIdeal (𝓞 K)⁰ K) : Set (Chapter04FiniteAdeleRing K) :=
  {x | ∀ v : Chapter04FinitePlace K,
    x v ∈ chapter01LocalFractionalIdealBall v I}

private theorem chapter04_local_fractionalIdealBall_is_compact_open_additive_subgroup
    (K : Type*) [Field K] [NumberField K]
    (v : Chapter04FinitePlace K)
    (I : FractionalIdeal (𝓞 K)⁰ K) :
    ∃ H : AddSubgroup (Chapter04FiniteLocalField K v),
      (H : Set (Chapter04FiniteLocalField K v)) =
        chapter01LocalFractionalIdealBall v I ∧
        IsCompact (chapter01LocalFractionalIdealBall v I) ∧
        IsOpen (chapter01LocalFractionalIdealBall v I) := by
  let r : ℤ := chapter01FractionalIdealOrder v I
  let c : Chapter04FiniteLocalField K v :=
    Classical.choose (v.valuedAdicCompletion_surjective K (WithZero.exp (-r)))
  have hcval : Valued.v c = WithZero.exp (-r) := by
    exact Classical.choose_spec
      (v.valuedAdicCompletion_surjective K (WithZero.exp (-r)))
  have hcval0 : Valued.v c ≠ 0 := by
    rw [hcval]
    exact WithZero.exp_pos.ne'
  have hpos : 0 < Valued.v c := by
    rw [hcval]
    exact WithZero.exp_pos
  have hc : c ≠ 0 := by
    intro hc0
    apply hcval0
    simp [hc0]
  have hball :
      chapter01LocalFractionalIdealBall v I =
        (fun y : Chapter04FiniteLocalField K v => c * y) ''
          (chapter04FiniteLocalIntegerSet K v) := by
    ext y
    constructor
    · intro hy
      change Valued.v y ≤ WithZero.exp (-r) at hy
      refine ⟨c⁻¹ * y, ?_, ?_⟩
      · apply (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
          (𝓞 K) K v).2
        change Valued.v (c⁻¹ * y) ≤ 1
        rw [Valuation.map_mul, map_inv₀]
        have hy' : Valued.v y ≤ Valued.v c := by
          simpa [hcval] using hy
        have hdiv : Valued.v y / Valued.v c ≤ 1 :=
          (div_le_one₀ hpos).2 hy'
        simpa [div_eq_mul_inv, mul_comm] using hdiv
      · simp [hc]
    · rintro ⟨y, hy, rfl⟩
      change Valued.v (c * y) ≤ WithZero.exp (-r)
      rw [Valuation.map_mul, hcval]
      have hyv : Valued.v y ≤ 1 := by
        exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
          (𝓞 K) K v).1 hy
      calc
        WithZero.exp (-r) * Valued.v y ≤ WithZero.exp (-r) * 1 := by
          gcongr
        _ = WithZero.exp (-r) := by simp
  let H : AddSubgroup (Chapter04FiniteLocalField K v) :=
    (v.adicCompletionIntegers K).toAddSubgroup.map
      (ContinuousAddEquiv.mulLeft (Units.mk0 c hc)).toAddMonoidHom
  refine ⟨H, ?_, ?_, ?_⟩
  · rw [AddSubgroup.coe_map]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [hball]
      refine ⟨z, ?_, ?_⟩
      · exact hz
      · rfl
    · intro hy
      rw [hball] at hy
      rcases hy with ⟨z, hz, rfl⟩
      refine ⟨z, hz, ?_⟩
      rfl
  · rw [hball]
    have hcompact : IsCompact (chapter04FiniteLocalIntegerSet K v) := by
      have hcompact' : IsCompact
          (Set.univ : Set (Chapter04FiniteLocalIntegerRing K v)) :=
        isCompact_univ_iff.mpr
          (LastLib.Book04AdelesAndIdeles.Chapter01.chapter01_completion_integers_compact K v)
      have himage := hcompact'.image
        (show Continuous (fun x : Chapter04FiniteLocalIntegerRing K v =>
          (x : Chapter04FiniteLocalField K v)) from continuous_subtype_val)
      simpa [chapter04FiniteLocalIntegerSet] using himage
    exact hcompact.image (continuous_const_mul c)
  · rw [hball]
    exact (ContinuousAddEquiv.mulLeft (Units.mk0 c hc)).isOpenMap _
      (Valued.isOpen_valuationSubring _)

theorem chapter04_fractionalIdealCompletion_is_compact_open_additive_subgroup
    (K : Type*) [Field K] [NumberField K]
    (I : FractionalIdeal (𝓞 K)⁰ K) :
    ∃ H : AddSubgroup (Chapter04FiniteAdeleRing K),
      (H : Set (Chapter04FiniteAdeleRing K)) =
        chapter04FractionalIdealCompletion K I ∧
        IsCompact (H : Set (Chapter04FiniteAdeleRing K)) ∧
        IsOpen (H : Set (Chapter04FiniteAdeleRing K)) := by
  classical
  have hcount :
      ∀ᶠ v : Chapter04FinitePlace K in Filter.cofinite,
        chapter01FractionalIdealOrder v I = 0 := by
    simpa [chapter01FractionalIdealOrder] using FractionalIdeal.finite_factors I
  let T : Set (Chapter04FinitePlace K) :=
    {v | chapter01LocalFractionalIdealBall v I = chapter04FiniteLocalIntegerSet K v}
  have hT : ∀ᶠ v : Chapter04FinitePlace K in Filter.cofinite, v ∈ T := by
    filter_upwards [hcount] with v hv
    change chapter01LocalFractionalIdealBall v I = chapter04FiniteLocalIntegerSet K v
    ext y
    change (Valued.v y ≤ WithZero.exp (-chapter01FractionalIdealOrder v I)) ↔
      y ∈ v.adicCompletionIntegers K
    rw [hv, neg_zero, WithZero.exp_zero]
    exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
      (𝓞 K) K v).symm
  have hTle : Filter.cofinite ≤ Filter.principal T := by
    exact le_principal_iff.mpr hT
  have hlocal : ∀ v : Chapter04FinitePlace K,
      IsCompact (chapter01LocalFractionalIdealBall v I) ∧
        IsOpen (chapter01LocalFractionalIdealBall v I) := by
    intro v
    rcases chapter04_local_fractionalIdealBall_is_compact_open_additive_subgroup K v I with
      ⟨H, hH, hcompact, hopen⟩
    exact ⟨hcompact, hopen⟩
  let g : (∀ v : Chapter04FinitePlace K,
      {y : Chapter04FiniteLocalField K v //
        y ∈ chapter01LocalFractionalIdealBall v I}) →
      Πʳ v : Chapter04FinitePlace K,
        [Chapter04FiniteLocalField K v, chapter04FiniteLocalIntegerSet K v]_[Filter.principal T] :=
    fun x => ⟨fun v => x v, by
      intro v hv
      change (x v : Chapter04FiniteLocalField K v) ∈ chapter04FiniteLocalIntegerSet K v
      rw [← show chapter01LocalFractionalIdealBall v I =
        chapter04FiniteLocalIntegerSet K v from hv]
      exact (x v).property⟩
  have hg : Continuous g := by
    apply RestrictedProduct.continuous_rng_of_principal.mpr
    exact continuous_pi fun v => continuous_subtype_val.comp (continuous_apply v)
  let f : (∀ v : Chapter04FinitePlace K,
      {y : Chapter04FiniteLocalField K v //
        y ∈ chapter01LocalFractionalIdealBall v I}) →
      Chapter04FiniteAdeleRing K :=
    RestrictedProduct.inclusion (fun v : Chapter04FinitePlace K =>
      Chapter04FiniteLocalField K v) (chapter04FiniteLocalIntegerSet K)
      hTle ∘ g
  have hf : Continuous f := by
    exact (RestrictedProduct.continuous_inclusion hTle).comp hg
  have hproduct : IsCompact (Set.univ : Set (∀ v : Chapter04FinitePlace K,
      {y : Chapter04FiniteLocalField K v //
        y ∈ chapter01LocalFractionalIdealBall v I})) := by
    rw [← Set.pi_univ univ]
    exact isCompact_univ_pi fun v => by
      exact isCompact_univ_iff.mpr (isCompact_iff_compactSpace.mp (hlocal v).1)
  have hset : f '' (Set.univ : Set (∀ v : Chapter04FinitePlace K,
      {y : Chapter04FiniteLocalField K v //
        y ∈ chapter01LocalFractionalIdealBall v I})) =
      chapter04FractionalIdealCompletion K I := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      change ∀ v : Chapter04FinitePlace K,
        (y v : Chapter04FiniteLocalField K v) ∈
          chapter01LocalFractionalIdealBall v I
      intro v
      exact (y v).property
    · intro hx
      let y : ∀ v : Chapter04FinitePlace K,
          {z : Chapter04FiniteLocalField K v //
            z ∈ chapter01LocalFractionalIdealBall v I} := fun v =>
        ⟨x v, hx v⟩
      refine ⟨y, Set.mem_univ _, ?_⟩
      apply RestrictedProduct.ext
      intro v
      rfl
  have hcompact : IsCompact (chapter04FractionalIdealCompletion K I) := by
    rw [← hset]
    exact hproduct.image hf
  have hopen : IsOpen (chapter04FractionalIdealCompletion K I) := by
    change IsOpen ({x : Πʳ v : Chapter04FinitePlace K,
      [Chapter04FiniteLocalField K v, chapter04FiniteLocalIntegerSet K v] |
      ∀ v : Chapter04FinitePlace K,
        x v ∈ chapter01LocalFractionalIdealBall v I} : Set (Πʳ v : Chapter04FinitePlace K,
          [Chapter04FiniteLocalField K v, chapter04FiniteLocalIntegerSet K v]))
    rw [RestrictedProduct.topologicalSpace_eq_iSup Filter.cofinite]
    simp_rw [isOpen_iSup_iff, isOpen_coinduced]
    intro S hS
    have hST : Filter.cofinite ≤ Filter.principal (S ∩ T) := by
      apply le_principal_iff.mpr
      exact inter_mem (le_principal_iff.mp hS) hT
    have hfinite : (S ∩ T)ᶜ.Finite := by
      exact mem_cofinite.mp (le_principal_iff.mp hST)
    have hU : IsOpen ((S ∩ T)ᶜ.pi
        (fun v : Chapter04FinitePlace K => chapter01LocalFractionalIdealBall v I)) := by
      exact isOpen_set_pi hfinite (fun v _ => (hlocal v).2)
    have hpre : IsOpen ((fun x :
        Πʳ v : Chapter04FinitePlace K,
          [Chapter04FiniteLocalField K v, chapter04FiniteLocalIntegerSet K v]_[Filter.principal S] =>
        (x : ∀ v : Chapter04FinitePlace K, Chapter04FiniteLocalField K v)) ⁻¹'
          ((S ∩ T)ᶜ.pi
            (fun v : Chapter04FinitePlace K => chapter01LocalFractionalIdealBall v I))) :=
      hU.preimage RestrictedProduct.continuous_coe
    convert hpre using 1
    ext x
    change (∀ v : Chapter04FinitePlace K,
      x v ∈ chapter01LocalFractionalIdealBall v I) ↔
      ∀ v : Chapter04FinitePlace K, v ∈ (S ∩ T)ᶜ →
        x v ∈ chapter01LocalFractionalIdealBall v I
    constructor
    · intro hx v hv
      exact hx v
    · intro hx v
      by_cases hv : v ∈ S ∩ T
      · have hvT : chapter01LocalFractionalIdealBall v I =
            chapter04FiniteLocalIntegerSet K v := hv.2
        rw [hvT]
        exact x.2 hv.1
      · exact hx v hv
  let H : AddSubgroup (Chapter04FiniteAdeleRing K) :=
    { carrier := chapter04FractionalIdealCompletion K I
      zero_mem' := by
        change ∀ v : Chapter04FinitePlace K,
          (0 : Chapter04FiniteLocalField K v) ∈ chapter01LocalFractionalIdealBall v I
        intro v
        rcases chapter04_local_fractionalIdealBall_is_compact_open_additive_subgroup K v I with
          ⟨Hv, hHv, _, _⟩
        rw [← hHv]
        exact Hv.zero_mem
      add_mem' := by
        intro x y hx hy
        change ∀ v : Chapter04FinitePlace K,
          (x + y) v ∈ chapter01LocalFractionalIdealBall v I
        change ∀ v : Chapter04FinitePlace K,
          x v ∈ chapter01LocalFractionalIdealBall v I at hx
        change ∀ v : Chapter04FinitePlace K,
          y v ∈ chapter01LocalFractionalIdealBall v I at hy
        intro v
        rcases chapter04_local_fractionalIdealBall_is_compact_open_additive_subgroup K v I with
          ⟨Hv, hHv, _, _⟩
        rw [← hHv]
        have hxv : (x v : Chapter04FiniteLocalField K v) ∈ (Hv : Set _) := by
          rw [hHv]
          exact hx v
        have hyv : (y v : Chapter04FiniteLocalField K v) ∈ (Hv : Set _) := by
          rw [hHv]
          exact hy v
        exact Hv.add_mem hxv hyv
      neg_mem' := by
        intro x hx
        change ∀ v : Chapter04FinitePlace K,
          (-x) v ∈ chapter01LocalFractionalIdealBall v I
        change ∀ v : Chapter04FinitePlace K,
          x v ∈ chapter01LocalFractionalIdealBall v I at hx
        intro v
        rcases chapter04_local_fractionalIdealBall_is_compact_open_additive_subgroup K v I with
          ⟨Hv, hHv, _, _⟩
        rw [← hHv]
        have hxv : (x v : Chapter04FiniteLocalField K v) ∈ (Hv : Set _) := by
          rw [hHv]
          exact hx v
        exact Hv.neg_mem hxv }
  refine ⟨H, rfl, ?_, ?_⟩
  · exact hcompact
  · exact hopen

def chapter04FinitePrecisionNeighborhood
    (K : Type*) [Field K] [NumberField K]
    (S : Finset (Chapter04FinitePlace K))
    (m : ∀ _ : S, ℤ) : Set (Chapter04FiniteAdeleRing K) :=
  {x |
    (∀ v : S,
      x v.1 ∈ chapter01LocalNeighborhood v.1 (m v)) ∧
      (∀ v : Chapter04FinitePlace K, v ∉ S →
        x v ∈ chapter04FiniteLocalIntegerSet K v)}

private theorem chapter04_local_neighborhood_is_compact_open_additive_subgroup
    (K : Type*) [Field K] [NumberField K]
    (v : Chapter04FinitePlace K) (n : ℤ) :
    ∃ H : AddSubgroup (Chapter04FiniteLocalField K v),
      (H : Set (Chapter04FiniteLocalField K v)) =
        chapter01LocalNeighborhood v n ∧
        IsCompact (chapter01LocalNeighborhood v n) ∧
        IsOpen (chapter01LocalNeighborhood v n) := by
  let c : Chapter04FiniteLocalField K v :=
    Classical.choose (v.valuedAdicCompletion_surjective K (WithZero.exp (-n)))
  have hcval : Valued.v c = WithZero.exp (-n) := by
    exact Classical.choose_spec
      (v.valuedAdicCompletion_surjective K (WithZero.exp (-n)))
  have hcval0 : Valued.v c ≠ 0 := by
    rw [hcval]
    exact WithZero.exp_pos.ne'
  have hpos : 0 < Valued.v c := by
    rw [hcval]
    exact WithZero.exp_pos
  have hc : c ≠ 0 := by
    intro hc0
    apply hcval0
    simp [hc0]
  have hball :
      chapter01LocalNeighborhood v n =
        (fun y : Chapter04FiniteLocalField K v => c * y) ''
          (chapter04FiniteLocalIntegerSet K v) := by
    ext y
    constructor
    · intro hy
      change Valued.v y ≤ WithZero.exp (-n) at hy
      refine ⟨c⁻¹ * y, ?_, ?_⟩
      · apply (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
          (𝓞 K) K v).2
        change Valued.v (c⁻¹ * y) ≤ 1
        rw [Valuation.map_mul, map_inv₀]
        have hy' : Valued.v y ≤ Valued.v c := by
          simpa [hcval] using hy
        have hdiv : Valued.v y / Valued.v c ≤ 1 :=
          (div_le_one₀ hpos).2 hy'
        simpa [div_eq_mul_inv, mul_comm] using hdiv
      · simp [hc]
    · rintro ⟨y, hy, rfl⟩
      change Valued.v (c * y) ≤ WithZero.exp (-n)
      rw [Valuation.map_mul, hcval]
      have hyv : Valued.v y ≤ 1 := by
        exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
          (𝓞 K) K v).1 hy
      calc
        WithZero.exp (-n) * Valued.v y ≤ WithZero.exp (-n) * 1 := by
          gcongr
        _ = WithZero.exp (-n) := by simp
  let H : AddSubgroup (Chapter04FiniteLocalField K v) :=
    (v.adicCompletionIntegers K).toAddSubgroup.map
      (ContinuousAddEquiv.mulLeft (Units.mk0 c hc)).toAddMonoidHom
  refine ⟨H, ?_, ?_, ?_⟩
  · rw [AddSubgroup.coe_map]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [hball]
      refine ⟨z, hz, ?_⟩
      rfl
    · intro hy
      rw [hball] at hy
      rcases hy with ⟨z, hz, rfl⟩
      refine ⟨z, hz, ?_⟩
      rfl
  · rw [hball]
    have hcompact : IsCompact (chapter04FiniteLocalIntegerSet K v) := by
      have hcompact' : IsCompact
          (Set.univ : Set (Chapter04FiniteLocalIntegerRing K v)) :=
        isCompact_univ_iff.mpr
          (LastLib.Book04AdelesAndIdeles.Chapter01.chapter01_completion_integers_compact K v)
      have himage := hcompact'.image
        (show Continuous (fun x : Chapter04FiniteLocalIntegerRing K v =>
          (x : Chapter04FiniteLocalField K v)) from continuous_subtype_val)
      simpa [chapter04FiniteLocalIntegerSet] using himage
    exact hcompact.image (continuous_const_mul c)
  · rw [hball]
    exact (ContinuousAddEquiv.mulLeft (Units.mk0 c hc)).isOpenMap _
      (Valued.isOpen_valuationSubring _)

theorem chapter04_mem_finitePrecisionNeighborhood_iff
    (K : Type*) [Field K] [NumberField K]
    (S : Finset (Chapter04FinitePlace K))
    (m : ∀ _ : S, ℤ) (x : Chapter04FiniteAdeleRing K) :
    x ∈ chapter04FinitePrecisionNeighborhood K S m ↔
      (∀ v : S,
        x v.1 ∈ chapter01LocalNeighborhood v.1 (m v)) ∧
        (∀ v : Chapter04FinitePlace K, v ∉ S →
          x v ∈ chapter04FiniteLocalIntegerSet K v) :=
  Iff.rfl

theorem chapter04_finitePrecisionNeighborhood_is_compact_open
    (K : Type*) [Field K] [NumberField K]
    (S : Finset (Chapter04FinitePlace K))
    (m : ∀ _v : S, ℤ) :
    IsCompact (chapter04FinitePrecisionNeighborhood K S m) ∧
      IsOpen (chapter04FinitePrecisionNeighborhood K S m) := by
  classical
  let B : ∀ v : Chapter04FinitePlace K, Set (Chapter04FiniteLocalField K v) :=
    fun v => if hv : v ∈ S then
      chapter01LocalNeighborhood v (m ⟨v, hv⟩)
    else chapter04FiniteLocalIntegerSet K v
  have hB : ∀ v : Chapter04FinitePlace K,
      IsCompact (B v) ∧ IsOpen (B v) := by
    intro v
    by_cases hv : v ∈ S
    · simp only [B, dif_pos hv]
      rcases chapter04_local_neighborhood_is_compact_open_additive_subgroup K v
          (m ⟨v, hv⟩) with ⟨H, hH, hcompact, hopen⟩
      exact ⟨hcompact, hopen⟩
    · simp only [B, dif_neg hv]
      have hcompact' : IsCompact
          (Set.univ : Set (Chapter04FiniteLocalIntegerRing K v)) :=
        isCompact_univ_iff.mpr
          (LastLib.Book04AdelesAndIdeles.Chapter01.chapter01_completion_integers_compact K v)
      have himage := hcompact'.image
        (show Continuous (fun x : Chapter04FiniteLocalIntegerRing K v =>
          (x : Chapter04FiniteLocalField K v)) from continuous_subtype_val)
      exact ⟨by simpa [chapter04FiniteLocalIntegerSet] using himage,
        Valued.isOpen_valuationSubring _⟩
  have hTle : Filter.cofinite ≤ Filter.principal ((S : Set (Chapter04FinitePlace K))ᶜ) := by
    apply le_principal_iff.mpr
    rw [mem_cofinite]
    simpa only [compl_compl] using S.finite_toSet
  let g : (∀ v : Chapter04FinitePlace K, {y : Chapter04FiniteLocalField K v // y ∈ B v}) →
      Πʳ v : Chapter04FinitePlace K,
        [Chapter04FiniteLocalField K v, chapter04FiniteLocalIntegerSet K v]_[
          Filter.principal ((S : Set (Chapter04FinitePlace K))ᶜ)] :=
    fun x => ⟨fun v => x v, by
      intro v hv
      change v ∉ S at hv
      change (x v : Chapter04FiniteLocalField K v) ∈
        chapter04FiniteLocalIntegerSet K v
      have hxv := (x v).property
      change (x v : Chapter04FiniteLocalField K v) ∈
        (if h : v ∈ S then chapter01LocalNeighborhood v (m ⟨v, h⟩)
          else chapter04FiniteLocalIntegerSet K v) at hxv
      simpa [hv] using hxv⟩
  have hg : Continuous g := by
    apply RestrictedProduct.continuous_rng_of_principal.mpr
    exact continuous_pi fun v => continuous_subtype_val.comp (continuous_apply v)
  let f : (∀ v : Chapter04FinitePlace K, {y : Chapter04FiniteLocalField K v // y ∈ B v}) →
      Chapter04FiniteAdeleRing K :=
    RestrictedProduct.inclusion (fun v : Chapter04FinitePlace K =>
      Chapter04FiniteLocalField K v) (chapter04FiniteLocalIntegerSet K) hTle ∘ g
  have hf : Continuous f :=
    (RestrictedProduct.continuous_inclusion hTle).comp hg
  have hproduct : IsCompact (Set.univ : Set
      (∀ v : Chapter04FinitePlace K, {y : Chapter04FiniteLocalField K v // y ∈ B v})) := by
    rw [← Set.pi_univ univ]
    exact isCompact_univ_pi fun v => by
      exact isCompact_univ_iff.mpr (isCompact_iff_compactSpace.mp (hB v).1)
  have hset : f '' (Set.univ : Set
      (∀ v : Chapter04FinitePlace K, {y : Chapter04FiniteLocalField K v // y ∈ B v})) =
      chapter04FinitePrecisionNeighborhood K S m := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      change (∀ v : S,
          (y v.1 : Chapter04FiniteLocalField K v.1) ∈
            chapter01LocalNeighborhood v.1 (m v)) ∧
        (∀ v : Chapter04FinitePlace K, v ∉ S →
          (y v : Chapter04FiniteLocalField K v) ∈ chapter04FiniteLocalIntegerSet K v)
      constructor
      · intro v
        simpa [B, v.2] using (y v.1).property
      · intro v hv
        simpa [B, hv] using (y v).property
    · intro hx
      change (∀ v : S,
          x v.1 ∈ chapter01LocalNeighborhood v.1 (m v)) ∧
        (∀ v : Chapter04FinitePlace K, v ∉ S →
          x v ∈ chapter04FiniteLocalIntegerSet K v) at hx
      let y : ∀ v : Chapter04FinitePlace K, {z : Chapter04FiniteLocalField K v // z ∈ B v} :=
        fun v => if hv : v ∈ S then
          ⟨x v, by simpa [B, hv] using hx.1 ⟨v, hv⟩⟩
        else ⟨x v, by simpa [B, hv] using hx.2 v hv⟩
      refine ⟨y, Set.mem_univ _, ?_⟩
      apply RestrictedProduct.ext
      intro v
      change (y v : Chapter04FiniteLocalField K v) = x v
      by_cases hv : v ∈ S
      · simp [y, hv]
      · simp [y, hv]
  have hcompact : IsCompact (chapter04FinitePrecisionNeighborhood K S m) := by
    rw [← hset]
    exact hproduct.image hf
  have hopen : IsOpen (chapter04FinitePrecisionNeighborhood K S m) := by
    let U : ∀ v : Chapter04FinitePlace K, Set (Chapter04FiniteLocalField K v) :=
      fun v => if hv : v ∈ S then
        chapter01LocalNeighborhood v (m ⟨v, hv⟩)
      else Set.univ
    have hU : chapter04FiniteBasicNeighborhoodCondition K (S : Set _) U := by
      refine ⟨S.finite_toSet, ?_⟩
      intro v hv
      have hv' : v ∈ S := hv
      simp only [U, dif_pos hv']
      exact (chapter04_local_neighborhood_is_compact_open_additive_subgroup K v
        (m ⟨v, hv'⟩)).choose_spec.2.2
    have hEq : chapter04FinitePrecisionNeighborhood K S m =
        chapter04FiniteBasicNeighborhood K (S : Set _) U := by
      ext x
      change ((∀ v : S, x v.1 ∈ chapter01LocalNeighborhood v.1 (m v)) ∧
        (∀ v : Chapter04FinitePlace K, v ∉ S →
          x v ∈ chapter04FiniteLocalIntegerSet K v)) ↔ _
      constructor
      · rintro ⟨hxS, hxT⟩
        refine ⟨?_, hxT⟩
        intro v hv
        have hv' : v ∈ S := hv
        simpa [U, hv'] using hxS ⟨v, hv'⟩
      · rintro ⟨hxS, hxT⟩
        refine ⟨?_, hxT⟩
        intro v
        simpa [U, v.property] using hxS v
    rw [hEq]
    exact chapter04_finiteBasicNeighborhood_isOpen K (S : Set _) U hU
  exact ⟨hcompact, hopen⟩

theorem chapter04_finitePrecisionNeighborhood_is_a_compact_open_additive_subgroup
    (K : Type*) [Field K] [NumberField K]
    (S : Finset (Chapter04FinitePlace K))
    (m : ∀ _v : S, ℤ) :
    ∃ H : AddSubgroup (Chapter04FiniteAdeleRing K),
      (H : Set (Chapter04FiniteAdeleRing K)) =
        chapter04FinitePrecisionNeighborhood K S m ∧
        IsCompact (H : Set (Chapter04FiniteAdeleRing K)) ∧
        IsOpen (H : Set (Chapter04FiniteAdeleRing K)) := by
  classical
  let B : ∀ v : Chapter04FinitePlace K, Set (Chapter04FiniteLocalField K v) :=
    fun v => if hv : v ∈ S then
      chapter01LocalNeighborhood v (m ⟨v, hv⟩)
    else chapter04FiniteLocalIntegerSet K v
  have hsub : ∀ v : Chapter04FinitePlace K, ∃ Hv : AddSubgroup
      (Chapter04FiniteLocalField K v),
      (Hv : Set (Chapter04FiniteLocalField K v)) = B v := by
    intro v
    by_cases hv : v ∈ S
    · rcases chapter04_local_neighborhood_is_compact_open_additive_subgroup K v
        (m ⟨v, hv⟩) with ⟨Hv, hHv, _, _⟩
      exact ⟨Hv, by simpa [B, hv] using hHv⟩
    · refine ⟨(v.adicCompletionIntegers K).toAddSubgroup, ?_⟩
      simp [B, hv, chapter04FiniteLocalIntegerSet]
      ext x
      rfl
  have hBeq : chapter04FinitePrecisionNeighborhood K S m =
      {x : Chapter04FiniteAdeleRing K |
        ∀ v : Chapter04FinitePlace K, x v ∈ B v} := by
    ext x
    change ((∀ v : S, x v.1 ∈ chapter01LocalNeighborhood v.1 (m v)) ∧
      (∀ v : Chapter04FinitePlace K, v ∉ S →
        x v ∈ chapter04FiniteLocalIntegerSet K v)) ↔
      ∀ v : Chapter04FinitePlace K, x v ∈ B v
    constructor
    · rintro ⟨hxS, hxT⟩ v
      by_cases hv : v ∈ S
      · simpa [B, hv] using hxS ⟨v, hv⟩
      · simpa [B, hv] using hxT v hv
    · intro hx
      refine ⟨?_, ?_⟩
      · intro v
        simpa [B, v.property] using hx v
      · intro v hv
        simpa [B, hv] using hx v
  let H : AddSubgroup (Chapter04FiniteAdeleRing K) :=
    { carrier := {x : Chapter04FiniteAdeleRing K |
          ∀ v : Chapter04FinitePlace K, x v ∈ B v}
      zero_mem' := by
        intro v
        rcases hsub v with ⟨Hv, hHv⟩
        rw [← hHv]
        exact Hv.zero_mem
      add_mem' := by
        intro x y hx hy
        change ∀ v : Chapter04FinitePlace K, (x + y) v ∈ B v
        change ∀ v : Chapter04FinitePlace K, x v ∈ B v at hx
        change ∀ v : Chapter04FinitePlace K, y v ∈ B v at hy
        intro v
        rcases hsub v with ⟨Hv, hHv⟩
        rw [← hHv]
        have hxv : (x v : Chapter04FiniteLocalField K v) ∈
            (Hv : Set (Chapter04FiniteLocalField K v)) := by
          rw [hHv]
          exact hx v
        have hyv : (y v : Chapter04FiniteLocalField K v) ∈
            (Hv : Set (Chapter04FiniteLocalField K v)) := by
          rw [hHv]
          exact hy v
        exact Hv.add_mem hxv hyv
      neg_mem' := by
        intro x hx
        change ∀ v : Chapter04FinitePlace K, (-x) v ∈ B v
        change ∀ v : Chapter04FinitePlace K, x v ∈ B v at hx
        intro v
        rcases hsub v with ⟨Hv, hHv⟩
        rw [← hHv]
        have hxv : (x v : Chapter04FiniteLocalField K v) ∈
            (Hv : Set (Chapter04FiniteLocalField K v)) := by
          rw [hHv]
          exact hx v
        exact Hv.neg_mem hxv }
  have hHset : (H : Set (Chapter04FiniteAdeleRing K)) =
      chapter04FinitePrecisionNeighborhood K S m := by
    change {x : Chapter04FiniteAdeleRing K |
        ∀ v : Chapter04FinitePlace K, x v ∈ B v} = _
    rw [← hBeq]
  refine ⟨H, hHset, ?_, ?_⟩
  · rw [hHset]
    exact (chapter04_finitePrecisionNeighborhood_is_compact_open K S m).1
  · rw [hHset]
    exact (chapter04_finitePrecisionNeighborhood_is_compact_open K S m).2

theorem chapter04_finitePrecisionNeighborhoods_form_a_zero_basis
    (K : Type*) [Field K] [NumberField K]
    (V : Set (Chapter04FiniteAdeleRing K)) (hV : V ∈ 𝓝 0) :
    ∃ S : Finset (Chapter04FinitePlace K), ∃ m : ∀ v : S, ℤ,
      chapter04FinitePrecisionNeighborhood K S m ⊆ V := by
  sorry

theorem chapter04_independent_finite_exponents_are_fractional_ideal_completions
    (K : Type*) [Field K] [NumberField K]
    (S : Finset (Chapter04FinitePlace K)) (m : ∀ v : S, ℤ) :
    ∃ I : FractionalIdeal (𝓞 K)⁰ K,
      chapter04FinitePrecisionNeighborhood K S m =
        chapter04FractionalIdealCompletion K I := by
  sorry

theorem chapter04_finiteAdele_neighborhoods_are_local_specifications_not_plain_product_neighborhoods
    (K : Type*) [Field K] [NumberField K]
    (x : Chapter04FiniteAdeleRing K) (V : Set (Chapter04FiniteAdeleRing K))
    (hV : V ∈ 𝓝 x) :
    ∃ S : Set (Chapter04FinitePlace K), ∃ U : ∀ v : Chapter04FinitePlace K,
      Set (Chapter04FiniteLocalField K v),
      S.Finite ∧
        (∀ v, IsOpen (U v)) ∧
        (∀ v, v ∉ S → U v = chapter04FiniteLocalIntegerSet K v) ∧
        x ∈ chapter04FiniteBasicNeighborhood K S U ∧
        chapter04FiniteBasicNeighborhood K S U ⊆ V := by
  sorry

abbrev chapter04FiniteAdeleUnrestrictedSubspaceTopology
    (K : Type*) [Field K] [NumberField K] :
    TopologicalSpace (Chapter04FiniteAdeleRing K) :=
  TopologicalSpace.induced
    (fun x : Chapter04FiniteAdeleRing K =>
      (x : ∀ v : Chapter04FinitePlace K, Chapter04FiniteLocalField K v))
    inferInstance

theorem chapter04_finiteAdele_restricted_topology_differs_from_plain_product_subspace
    (K : Type*) [Field K] [NumberField K] :
    (inferInstance : TopologicalSpace (Chapter04FiniteAdeleRing K)) ≠
      chapter04FiniteAdeleUnrestrictedSubspaceTopology K := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter04
