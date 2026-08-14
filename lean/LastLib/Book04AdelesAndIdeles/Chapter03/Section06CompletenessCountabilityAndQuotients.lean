import LastLib.Book04AdelesAndIdeles.Chapter03.Section05RestrictedProductsAsIncreasingUnions
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.UniformSpace.Cauchy

namespace LastLib.Book04AdelesAndIdeles.Chapter03

open Set Filter Function TopologicalSpace
open scoped BigOperators Pointwise Topology

noncomputable section

/-! ### 3.6 Completeness, countability, and quotients -/

universe u v

section Countability

variable {I : Type u} {G : I → Type v} [∀ i, Group (G i)]

theorem chapter03_restrictedProduct_metrizable
    [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalGroup (G i)]
    (H : ∀ i, Subgroup (G i))
    [Countable I]
    (hmetric : ∀ i, MetrizableSpace (G i))
    (hH : ∀ i, IsOpen (H i : Set (G i))) :
    MetrizableSpace (Chapter03RestrictedProduct H) := by
  sorry

theorem chapter03_restrictedProduct_secondCountable
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    [Countable I]
    (hsecond : ∀ i, SecondCountableTopology (G i))
    (hH : ∀ i, IsOpen (H i : Set (G i))) :
    SecondCountableTopology (Chapter03RestrictedProduct H) := by
  sorry

theorem chapter03_restrictedProduct_sigmaCompact_of_local_data
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    [Countable I]
    (hlocal : ∀ i, LocallyCompactSpace (G i))
    (hsecond : ∀ i, SecondCountableTopology (G i))
    (hHcompact : ∀ i, IsCompact (H i : Set (G i)))
    (hHopen : ∀ i, IsOpen (H i : Set (G i))) :
    SigmaCompactSpace (Chapter03RestrictedProduct H) := by
  sorry

theorem chapter03_restrictedProduct_secondCountable_sigmaCompact
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    [Countable I]
    (hlocal : ∀ i, LocallyCompactSpace (G i))
    (hsecond : ∀ i, SecondCountableTopology (G i))
    (hHcompact : ∀ i, IsCompact (H i : Set (G i)))
    (hHopen : ∀ i, IsOpen (H i : Set (G i))) :
    SecondCountableTopology (Chapter03RestrictedProduct H) ∧
      SigmaCompactSpace (Chapter03RestrictedProduct H) := by
  exact ⟨chapter03_restrictedProduct_secondCountable H hsecond hHopen,
    chapter03_restrictedProduct_sigmaCompact_of_local_data H hlocal hsecond
      hHcompact hHopen⟩

theorem chapter03_secondCountable_closure_has_convergent_sequence
    {X : Type v} [TopologicalSpace X] [SecondCountableTopology X]
    (s : Set X) {x : X} (hx : x ∈ closure s) :
    ∃ u : ℕ → X, (∀ n, u n ∈ s) ∧ Tendsto u atTop (𝓝 x) := by
  sorry

end Countability

section Completeness

variable {I : Type u} {G : I → Type v} [∀ i, Group (G i)]

/-- The tail part of the Cauchy condition in a restricted product. -/
def chapter03CauchyTailCondition
    [∀ i, UniformSpace (G i)]
    (H : ∀ i, Subgroup (G i)) (u : ℕ → Chapter03RestrictedProduct H) : Prop :=
  ∃ S : Set I, S.Finite ∧
    ∀ᶠ n in Filter.atTop, ∀ m : ℕ, n ≤ m →
      ∀ i, i ∉ S →
        ((((u n : ∀ i, G i) i)⁻¹) * ((u m : ∀ i, G i) i)) ∈ H i

/-- A natural uniformity is recorded by the coordinatewise Cauchy and tail
characterization used in the proof of completeness. -/
/- DEPENDENCY_GUESS: No earlier LastLib restricted-product uniformity is
available in the assigned workspace.  The later reconciliation pass should
replace these characterizations with the canonical uniform-space construction
if one is introduced by another chapter draft. -/
def chapter03NaturalCauchySequenceCharacterization
    [∀ i, UniformSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    [UniformSpace (Chapter03RestrictedProduct H)] : Prop :=
  ∀ u : ℕ → Chapter03RestrictedProduct H,
    CauchySeq u ↔
      (∀ i, CauchySeq (fun n => ((u n : ∀ i, G i) i))) ∧
        chapter03CauchyTailCondition H u

/-- The filter-level tail condition used for Cauchy nets. -/
def chapter03CauchyFilterTailCondition
    [∀ i, UniformSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    (l : Filter (Chapter03RestrictedProduct H)) : Prop :=
    ∃ S : Set I, S.Finite ∧
    ∀ᶠ p in l ×ˢ l, ∀ i, i ∉ S →
      (((((p.1 : Chapter03RestrictedProduct H) : ∀ i, G i) i)⁻¹) *
        (((p.2 : Chapter03RestrictedProduct H) : ∀ i, G i) i)) ∈ H i

def chapter03NaturalCauchyFilterCharacterization
    [∀ i, UniformSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    [UniformSpace (Chapter03RestrictedProduct H)] : Prop :=
  ∀ l : Filter (Chapter03RestrictedProduct H),
    Cauchy l ↔
      (∀ i, Cauchy (l.map (fun x : Chapter03RestrictedProduct H =>
        ((x : ∀ i, G i) i)))) ∧
        chapter03CauchyFilterTailCondition H l

/-- The convergence characterization needed in addition to the Cauchy
characterization when proving completeness for a chosen restricted-product
uniformity. -/
def chapter03NaturalConvergenceFilterCharacterization
    [∀ i, UniformSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    [UniformSpace (Chapter03RestrictedProduct H)] : Prop :=
  ∀ l : Filter (Chapter03RestrictedProduct H),
    ∀ x : Chapter03RestrictedProduct H,
      Tendsto (fun y : Chapter03RestrictedProduct H => y) l (𝓝 x) ↔
          (∀ i, Tendsto (fun y : Chapter03RestrictedProduct H =>
          ((y : ∀ i, G i) i)) l
            (𝓝 (((x : ∀ i, G i) i)))) ∧
          ∃ S : Set I, S.Finite ∧
            ∀ᶠ y : Chapter03RestrictedProduct H in l, ∀ i, i ∉ S →
              ((y : ∀ i, G i) i) ∈ H i

theorem chapter03_cauchy_sequence_has_eventually_integral_tail
    [∀ i, UniformSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    [UniformSpace (Chapter03RestrictedProduct H)]
    (hchar : chapter03NaturalCauchySequenceCharacterization H)
    (u : ℕ → Chapter03RestrictedProduct H) (hu : CauchySeq u) :
    chapter03CauchyTailCondition H u := by
  exact ((hchar u).mp hu).2

theorem chapter03_cauchy_filter_has_eventually_integral_tail
    [∀ i, UniformSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    [UniformSpace (Chapter03RestrictedProduct H)]
    (hchar : chapter03NaturalCauchyFilterCharacterization H)
    (l : Filter (Chapter03RestrictedProduct H)) (hl : Cauchy l) :
    chapter03CauchyFilterTailCondition H l := by
  exact ((hchar l).mp hl).2

theorem chapter03_restrictedProduct_complete_of_natural_characterization
    [∀ i, UniformSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    [UniformSpace (Chapter03RestrictedProduct H)]
    (hlocal : ∀ i, CompleteSpace (G i))
    (hclosed : ∀ i, IsClosed (H i : Set (G i)))
    (hchar : chapter03NaturalCauchyFilterCharacterization H)
    (hconv : chapter03NaturalConvergenceFilterCharacterization H) :
    CompleteSpace (Chapter03RestrictedProduct H) := by
  sorry

/-!
The source's completeness assertion is conditional on complete local uniform
spaces and closed distinguished subgroups.  Since this chapter does not yet
choose a canonical uniform-space construction for the restricted product, the
theorem above exposes the corresponding Cauchy and convergence
characterizations as explicit interfaces.
-/

end Completeness

section ClosedSubgroupsAndQuotients

variable {G : Type v} [Group G] [TopologicalSpace G]

theorem chapter03_closed_subgroup_is_locallyCompact
    [LocallyCompactSpace G] [T2Space G]
    (H : Subgroup G) (hclosed : IsClosed (H : Set G)) :
    LocallyCompactSpace H := by
  sorry

theorem chapter03_closed_subgroup_is_secondCountable
    [SecondCountableTopology G]
    (H : Subgroup G) :
    SecondCountableTopology H := by
  exact TopologicalSpace.secondCountableTopology_induced (H : Set G) G (↑)

theorem chapter03_closed_normal_quotient_is_locallyCompact_hausdorff
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    (N : Subgroup G) [N.Normal]
    (hclosed : IsClosed (N : Set G)) :
    LocallyCompactSpace (G ⧸ N) ∧ T2Space (G ⧸ N) := by
  sorry

/-- Closedness of a diagonal range is the interface needed before forming the
locally compact Hausdorff quotient by diagonal global points. -/
def chapter03DiagonalRangeClosed {A : Type*} [Monoid A]
    (ι : A →* G) : Prop :=
  IsClosed (Set.range ι)

theorem chapter03_closed_diagonal_quotient_is_locallyCompact_hausdorff
    {A : Type*} [Group A]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    (ι : A →* G) (N : Subgroup G) [N.Normal]
    (hι : chapter03DiagonalRangeClosed ι)
    (hrange : Set.range ι = (N : Set G)) :
    LocallyCompactSpace (G ⧸ N) ∧ T2Space (G ⧸ N) := by
  apply chapter03_closed_normal_quotient_is_locallyCompact_hausdorff N
  rw [← hrange]
  exact hι

end ClosedSubgroupsAndQuotients

end
end LastLib.Book04AdelesAndIdeles.Chapter03
