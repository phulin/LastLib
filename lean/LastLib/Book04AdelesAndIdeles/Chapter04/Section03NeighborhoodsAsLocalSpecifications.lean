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
  sorry

theorem chapter04_rational_integer_multiple_hatZ_is_compact_open
    (m : ℤ) (hm : m ≠ 0) :
    IsCompact (chapter04RationalIntegerMultipleHatZ m) ∧
      IsOpen (chapter04RationalIntegerMultipleHatZ m) := by
  sorry

theorem chapter04_rational_integer_multiple_hatZ_is_a_neighborhood_subgroup
    (m : ℤ) (hm : m ≠ 0) :
    ∃ H : AddSubgroup (Chapter04FiniteAdeleRing ℚ),
      (H : Set (Chapter04FiniteAdeleRing ℚ)) =
        chapter04RationalIntegerMultipleHatZ m ∧
        IsCompact (H : Set (Chapter04FiniteAdeleRing ℚ)) ∧
        IsOpen (H : Set (Chapter04FiniteAdeleRing ℚ)) := by
  sorry

def chapter04FractionalIdealCompletion
    (K : Type*) [Field K] [NumberField K]
  (I : FractionalIdeal (𝓞 K)⁰ K) : Set (Chapter04FiniteAdeleRing K) :=
  {x | ∀ v : Chapter04FinitePlace K,
    x v ∈ chapter01LocalFractionalIdealBall v I}

theorem chapter04_fractionalIdealCompletion_is_compact_open_additive_subgroup
    (K : Type*) [Field K] [NumberField K]
    (I : FractionalIdeal (𝓞 K)⁰ K) :
    ∃ H : AddSubgroup (Chapter04FiniteAdeleRing K),
      (H : Set (Chapter04FiniteAdeleRing K)) =
        chapter04FractionalIdealCompletion K I ∧
        IsCompact (H : Set (Chapter04FiniteAdeleRing K)) ∧
        IsOpen (H : Set (Chapter04FiniteAdeleRing K)) := by
  sorry

def chapter04FinitePrecisionNeighborhood
    (K : Type*) [Field K] [NumberField K]
    (S : Finset (Chapter04FinitePlace K))
    (m : ∀ _ : S, ℤ) : Set (Chapter04FiniteAdeleRing K) :=
  {x |
    (∀ v : S,
      x v.1 ∈ chapter01LocalNeighborhood v.1 (m v)) ∧
      (∀ v : Chapter04FinitePlace K, v ∉ S →
        x v ∈ chapter04FiniteLocalIntegerSet K v)}

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
    (m : ∀ v : S, ℤ) :
    IsCompact (chapter04FinitePrecisionNeighborhood K S m) ∧
      IsOpen (chapter04FinitePrecisionNeighborhood K S m) := by
  sorry

theorem chapter04_finitePrecisionNeighborhood_is_a_compact_open_additive_subgroup
    (K : Type*) [Field K] [NumberField K]
    (S : Finset (Chapter04FinitePlace K))
    (m : ∀ v : S, ℤ) :
    ∃ H : AddSubgroup (Chapter04FiniteAdeleRing K),
      (H : Set (Chapter04FiniteAdeleRing K)) =
        chapter04FinitePrecisionNeighborhood K S m ∧
        IsCompact (H : Set (Chapter04FiniteAdeleRing K)) ∧
        IsOpen (H : Set (Chapter04FiniteAdeleRing K)) := by
  sorry

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
