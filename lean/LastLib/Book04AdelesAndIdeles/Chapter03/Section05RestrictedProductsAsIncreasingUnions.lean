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
  sorry

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
  sorry

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
  sorry

theorem chapter03_compact_arguments_reduce_to_finite_stage
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i)) (E : Chapter03StageExhaustion I)
    (hH : ∀ i, IsOpen (H i : Set (G i)))
    (K : Set (Chapter03RestrictedProduct H)) (hK : IsCompact K) :
    ∃ n : ℕ, IsCompact
      (K ∩ (chapter03StageSubgroup H (E.stage n) :
        Set (Chapter03RestrictedProduct H))) := by
  sorry

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
