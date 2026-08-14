import LastLib.Book04AdelesAndIdeles.Chapter03.Section04MappingProperties

namespace LastLib.Book04AdelesAndIdeles.Chapter03

open Set Filter
open scoped BigOperators Pointwise Topology

noncomputable section

/-! ### 3.5 Restricted products as increasing unions -/

universe u v

section IncreasingUnion

variable {I : Type u}

/-- A countable increasing exhaustion of the index set by finite subsets. -/
structure Chapter03StageExhaustion (I : Type u) where
  stage : ℕ → Set I
  finite : ∀ n, (stage n).Finite
  mono : Monotone stage
  exhaustive : ∀ i, ∃ n, i ∈ stage n

theorem chapter03_stageExhaustion_is_increasing
    (E : Chapter03StageExhaustion I) {m n : ℕ} (hmn : m ≤ n) :
    E.stage m ⊆ E.stage n := by
  exact E.mono hmn

section MultiplicativeUnion

variable {G : I → Type v} [∀ i, Group (G i)]

theorem chapter03_restrictedProduct_eq_iUnion_exhaustion
    (H : ∀ i, Subgroup (G i)) (E : Chapter03StageExhaustion I) :
    (Set.univ : Set (Chapter03RestrictedProduct H)) =
      ⋃ n : ℕ,
        (chapter03StageSubgroup H (E.stage n) :
          Set (Chapter03RestrictedProduct H)) := by
  classical
  apply Set.Subset.antisymm
  · intro x _
    have hfin :=
      (chapter03_restrictedProduct_mem_iff_exceptional_finite H
        (x : ∀ i, G i)).1 x.property
    let n : ℕ := hfin.toFinset.sup (fun i => (E.exhaustive i).choose)
    have hsubset : chapter03ExceptionalSet H (x : ∀ i, G i) ⊆ E.stage n := by
      intro i hi
      exact E.mono (Finset.le_sup (hfin.mem_toFinset.mpr hi))
        (E.exhaustive i).choose_spec
    exact Set.mem_iUnion.2 ⟨n,
      chapter03_stage_contains_restricted_family H (E.stage n) x hsubset⟩
  · intro x _
    exact Set.mem_univ x

def chapter03StageInclusionBetween
    {G : I → Type v} [∀ i, Group (G i)]
    (H : ∀ i, Subgroup (G i)) (E : Chapter03StageExhaustion I)
    {m n : ℕ} (hmn : m ≤ n) :
    Chapter03Stage H (E.stage m) → Chapter03Stage H (E.stage n) :=
  fun x =>
    ⟨x.1, chapter03_stage_mono H (E.mono hmn) x.2⟩

theorem chapter03_stage_exhaustion_inclusions_are_open
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i)) (E : Chapter03StageExhaustion I)
    (hH : ∀ i, IsOpen (H i : Set (G i)))
    {m n : ℕ} (hmn : m ≤ n) :
    IsOpenMap (chapter03StageInclusionBetween H E hmn) := by
  classical
  let f : Chapter03Stage H (E.stage m) → Chapter03Stage H (E.stage n) :=
    chapter03StageInclusionBetween H E hmn
  let eₘ : Chapter03Stage H (E.stage m) → ∀ i, G i :=
    fun x => ((x : Chapter03Stage H (E.stage m)).1 : ∀ i, G i)
  let eₙ : Chapter03Stage H (E.stage n) → ∀ i, G i :=
    fun x => ((x : Chapter03Stage H (E.stage n)).1 : ∀ i, G i)
  have heₘ : Topology.IsEmbedding eₘ := by
    refine { eq_induced := ?_, injective := ?_ }
    · change chapter03StageSubtypeTopology H (E.stage m) =
        chapter03StageProductTopology H (E.stage m)
      exact chapter03_stage_subtype_topology_eq_product_topology H
        (E.finite m) hH
    · intro x y hxy
      apply Subtype.ext
      apply chapter03_restrictedProduct_ext H
      intro i
      exact congrFun hxy i
  have heₙ : Topology.IsEmbedding eₙ := by
    refine { eq_induced := ?_, injective := ?_ }
    · change chapter03StageSubtypeTopology H (E.stage n) =
        chapter03StageProductTopology H (E.stage n)
      exact chapter03_stage_subtype_topology_eq_product_topology H
        (E.finite n) hH
    · intro x y hxy
      apply Subtype.ext
      apply chapter03_restrictedProduct_ext H
      intro i
      exact congrFun hxy i
  have hcomp : Topology.IsEmbedding (eₙ ∘ f) := by
    simpa [eₘ, eₙ, f, chapter03StageInclusionBetween, Function.comp_def] using heₘ
  have hfcont : Continuous f := by
    apply heₙ.isInducing.continuous_iff.mpr
    simpa [eₘ, eₙ, f, chapter03StageInclusionBetween, Function.comp_def] using
      heₘ.continuous
  have hfembed : Topology.IsEmbedding f :=
    Topology.IsEmbedding.of_comp hfcont heₙ.continuous hcomp
  let D : Set I := E.stage n \ E.stage m
  have hD : D.Finite := by
    exact (E.finite n).sdiff
  let V : ∀ i, Set (G i) := fun i => if i ∈ D then (H i : Set (G i)) else Set.univ
  have hVopen : IsOpen (Set.pi Set.univ V) := by
    rw [show Set.pi Set.univ V = Set.pi D V by
      ext x
      constructor
      · intro hx i hi
        exact hx i (by simp)
      · intro hx i hi
        by_cases hiD : i ∈ D
        · exact hx i hiD
        · simp [V, hiD]]
    apply isOpen_set_pi hD
    intro i hi
    by_cases hiD : i ∈ D
    · simpa [V, hiD] using hH i
    · simp [V, hiD]
  have hrange : Set.range f = eₙ ⁻¹' Set.pi Set.univ V := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      simp only [Set.mem_preimage, Set.mem_pi, mem_univ, true_implies]
      intro i
      by_cases hiD : i ∈ D
      · have hiM : i ∉ E.stage m := by
          intro hiM
          exact hiD.2 hiM
        simpa [eₙ, f, chapter03StageInclusionBetween, V, hiD] using y.2 i hiM
      · simp [V, hiD]
    · intro hx
      have hx' : ∀ i, ((x : Chapter03Stage H (E.stage n)).1 : ∀ i, G i) i ∈ V i := by
        simpa only [Set.mem_preimage, Set.mem_pi, mem_univ, true_implies] using hx
      have hxM : ∀ i, i ∉ E.stage m →
          ((x : Chapter03Stage H (E.stage n)).1 : ∀ i, G i) i ∈ H i := by
        intro i hiM
        by_cases hiN : i ∈ E.stage n
        · have hiD : i ∈ D := ⟨hiN, hiM⟩
          simpa [V, hiD] using hx' i
        · exact x.2 i hiN
      let y : Chapter03Stage H (E.stage m) := ⟨x.1, hxM⟩
      refine ⟨y, ?_⟩
      apply Subtype.ext
      rfl
  have hopen_range : IsOpen (Set.range f) := by
    rw [hrange, heₙ.eq_induced]
    exact isOpen_induced hVopen
  have hopenEmbedding : Topology.IsOpenEmbedding f := ⟨hfembed, hopen_range⟩
  exact hopenEmbedding.isOpenMap

theorem chapter03_stage_exhaustion_inclusion_is_open_subgroup
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i)) (E : Chapter03StageExhaustion I)
    (hH : ∀ i, IsOpen (H i : Set (G i))) {n : ℕ} :
    IsOpen (chapter03StageSubgroup H (E.stage n) :
      Set (Chapter03RestrictedProduct H)) := by
  exact chapter03_stage_isOpen H (E.finite n) hH

/-- Every compact subset is contained in one member of an increasing open
stage exhaustion. -/
theorem chapter03_compact_subset_contained_in_stage
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i)) (E : Chapter03StageExhaustion I)
    (hH : ∀ i, IsOpen (H i : Set (G i)))
    (K : Set (Chapter03RestrictedProduct H)) (hK : IsCompact K) :
    ∃ n : ℕ, K ⊆
      (chapter03StageSubgroup H (E.stage n) :
        Set (Chapter03RestrictedProduct H)) := by
  apply hK.elim_directed_cover
    (fun n => (chapter03StageSubgroup H (E.stage n) :
      Set (Chapter03RestrictedProduct H)))
    (fun n => chapter03_stage_isOpen H (E.finite n) hH)
  · intro x hx
    have hxuniv : x ∈ (Set.univ : Set (Chapter03RestrictedProduct H)) :=
      Set.mem_univ x
    rw [chapter03_restrictedProduct_eq_iUnion_exhaustion H E] at hxuniv
    exact hxuniv
  · intro m n
    refine ⟨max m n, ?_, ?_⟩
    · exact chapter03_stage_mono H (E.mono (Nat.le_max_left _ _))
    · exact chapter03_stage_mono H (E.mono (Nat.le_max_right _ _))

theorem chapter03_compact_arguments_reduce_to_finite_stage
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i)) (E : Chapter03StageExhaustion I)
    (hH : ∀ i, IsOpen (H i : Set (G i)))
    (K : Set (Chapter03RestrictedProduct H)) (hK : IsCompact K) :
    ∃ n : ℕ, IsCompact
      (K ∩ (chapter03StageSubgroup H (E.stage n) :
        Set (Chapter03RestrictedProduct H))) := by
  obtain ⟨n, hn⟩ :=
    chapter03_compact_subset_contained_in_stage H E hH K hK
  refine ⟨n, ?_⟩
  rw [inter_eq_left.mpr hn]
  exact hK

/-- The infinite distinguished tail is part of the restricted union topology,
not an auxiliary convention attached after taking an algebraic union. -/
theorem chapter03_restrictedProduct_union_retains_distinguished_tail
    {G : I → Type v} [∀ i, Group (G i)]
    (H : ∀ i, Subgroup (G i)) :
    chapter03DistinguishedTail H =
      (chapter03StageSubgroup H (∅ : Set I) :
        Set (Chapter03RestrictedProduct H)) := by
  rfl

end MultiplicativeUnion

end IncreasingUnion

end
end LastLib.Book04AdelesAndIdeles.Chapter03
