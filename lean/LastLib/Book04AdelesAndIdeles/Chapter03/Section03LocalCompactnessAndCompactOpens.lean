import LastLib.Book04AdelesAndIdeles.Chapter03.Section02TheRestrictedProductTopology

namespace LastLib.Book04AdelesAndIdeles.Chapter03

open Set Filter
open scoped BigOperators Pointwise Topology

noncomputable section

/-! ### 3.3 Local compactness and compact opens -/

universe u v

section RestrictedProductLocalCompactness

variable {I : Type u} {G : I → Type v} [∀ i, Group (G i)]

/-- The hypotheses used by the local-compactness proposition. -/
structure Chapter03LocallyCompactRestrictedProductHypotheses
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i)) : Prop where
  local_locally_compact : ∀ i, LocallyCompactSpace (G i)
  distinguished_compact : ∀ i, IsCompact (H i : Set (G i))
  distinguished_open : ∀ i, IsOpen (H i : Set (G i))

theorem chapter03_distinguishedTail_is_compact
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    (hH : ∀ i, IsCompact (H i : Set (G i))) :
    IsCompact (chapter03DistinguishedTail H) := by
  sorry

theorem chapter03_distinguishedTail_is_open
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    (hH : ∀ i, IsOpen (H i : Set (G i))) :
    IsOpen (chapter03DistinguishedTail H) := by
  sorry

theorem chapter03_distinguishedTail_is_compact_open
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    (hcompact : ∀ i, IsCompact (H i : Set (G i)))
    (hopen : ∀ i, IsOpen (H i : Set (G i))) :
    IsCompact (chapter03DistinguishedTail H) ∧
      IsOpen (chapter03DistinguishedTail H) := by
  exact ⟨chapter03_distinguishedTail_is_compact H hcompact,
    chapter03_distinguishedTail_is_open H hopen⟩

/-- Compact neighborhoods in finitely many exceptional factors give compact
neighborhoods everywhere in the restricted product. -/
theorem chapter03_restrictedProduct_has_compact_neighborhood
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    (hlocal : ∀ i, LocallyCompactSpace (G i))
    (hcompact : ∀ i, IsCompact (H i : Set (G i)))
    (hopen : ∀ i, IsOpen (H i : Set (G i)))
    (x : Chapter03RestrictedProduct H) :
    ∃ K : Set (Chapter03RestrictedProduct H),
      IsCompact K ∧ K ∈ 𝓝 x := by
  sorry

theorem chapter03_restrictedProduct_locallyCompact
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    (hlocal : ∀ i, LocallyCompactSpace (G i))
    (hcompact : ∀ i, IsCompact (H i : Set (G i)))
    (hopen : ∀ i, IsOpen (H i : Set (G i))) :
    LocallyCompactSpace (Chapter03RestrictedProduct H) := by
  sorry

theorem chapter03_additive_distinguishedTail_is_compact_open
    {G : I → Type v} [∀ i, AddGroup (G i)]
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, AddSubgroup (G i))
    (hcompact : ∀ i, IsCompact (H i : Set (G i)))
    (hopen : ∀ i, IsOpen (H i : Set (G i))) :
    IsCompact (chapter03AdditiveDistinguishedTail H) ∧
      IsOpen (chapter03AdditiveDistinguishedTail H) := by
  sorry

theorem chapter03_additive_restrictedProduct_locallyCompact
    {G : I → Type v} [∀ i, AddGroup (G i)]
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, AddSubgroup (G i))
    (hlocal : ∀ i, LocallyCompactSpace (G i))
    (hcompact : ∀ i, IsCompact (H i : Set (G i)))
    (hopen : ∀ i, IsOpen (H i : Set (G i))) :
    LocallyCompactSpace (Chapter03AdditiveRestrictedProduct H) := by
  sorry

/-- Infinitely many noncompact coordinates obstruct local compactness of the
unrestricted product. -/
def chapter03InfinitelyManyNoncompactFactors
    [∀ i, TopologicalSpace (G i)] : Prop :=
  {i | ¬ IsCompact (Set.univ : Set (G i))}.Infinite

theorem chapter03_unrestrictedProduct_not_locallyCompact
    [∀ i, TopologicalSpace (G i)]
    (hlocal : ∀ i, LocallyCompactSpace (G i))
    (hhausdorff : ∀ i, T2Space (G i))
    (hinfinite : chapter03InfinitelyManyNoncompactFactors (G := G)) :
    ¬ LocallyCompactSpace (∀ i, G i) := by
  sorry

section DirectSumWarning

variable {A : Type v} [∀ i, AddGroup (G i)]

/-- The finite-support additive subgroup, used here as the direct-sum model. -/
def chapter03FiniteSupportAddSubgroup : AddSubgroup (∀ i, G i) where
  carrier := {x | {i | x i ≠ 0}.Finite}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    refine (hx.union hy).subset ?_
    intro i hi
    by_cases hxi : x i ≠ 0
    · exact Or.inl hxi
    by_cases hyi : y i ≠ 0
    · exact Or.inr hyi
    · exfalso
      apply hi
      have hxi_zero : x i = 0 := not_ne_iff.mp hxi
      have hyi_zero : y i = 0 := not_ne_iff.mp hyi
      simp [hxi_zero, hyi_zero]
  neg_mem' := by
    intro x hx
    simpa using hx

abbrev Chapter03DirectSum := chapter03FiniteSupportAddSubgroup (G := G)

omit [(i : I) → Group (G i)] in
theorem chapter03_directSum_contains_additive_identity :
    chapter03AdditiveZeroFamily ∈ Chapter03DirectSum (G := G) := by
  exact (chapter03FiniteSupportAddSubgroup (G := G)).zero_mem

omit [(i : I) → Group (G i)] in
theorem chapter03_directSum_mem_iff_finite_support (x : ∀ i, G i) :
    x ∈ Chapter03DirectSum (G := G) ↔ {i | x i ≠ 0}.Finite :=
  Iff.rfl

omit [(i : I) → Group (G i)] in
theorem chapter03_directSum_excludes_infinite_support
    (x : ∀ i, G i) (hinfinite : {i | x i ≠ 0}.Infinite) :
    x ∉ Chapter03DirectSum (G := G) := by
  exact fun hx => hinfinite
    ((chapter03_directSum_mem_iff_finite_support x).mp hx)

/- SOURCE_ISSUE:
  The sentence "The direct sum has other defects and does not contain the
  diagonal identity" is false if identity means the identity element: the
  additive zero family is always finitely supported.  The precise replacement
  used here is that the direct sum excludes diagonal families with infinitely
  many nonzero coordinates (and, in a multiplicative reading, nontrivial
  constant diagonal families).
-/
omit [(i : I) → Group (G i)] in
theorem chapter03_directSum_diagonal_family_excluded_when_support_infinite
    (diagonal : A → ∀ i, G i) (a : A)
    (hinfinite : {i | diagonal a i ≠ 0}.Infinite) :
    diagonal a ∉ Chapter03DirectSum (G := G) := by
  exact chapter03_directSum_excludes_infinite_support _ hinfinite

end DirectSumWarning

end RestrictedProductLocalCompactness

end
end LastLib.Book04AdelesAndIdeles.Chapter03
