import LastLib.Book04AdelesAndIdeles.Chapter06.Section01WhyCompactnessIsCentral
import LastLib.Book04AdelesAndIdeles.Chapter04.Section05FinitePrincipalPartsQuotient
import LastLib.Book04AdelesAndIdeles.Chapter05.Section02StrongApproximationInTheFiniteAdeles

namespace LastLib.Book04AdelesAndIdeles.Chapter06

open LastLib.Book04AdelesAndIdeles.Chapter04
open LastLib.Book04AdelesAndIdeles.Chapter05

noncomputable section

/-! # Book 4, Chapter 6, Section 6.2: Principal parts at finite places -/

universe uK uO uInf uFin uHat

variable {K : Type uK} {O : Type uO} {KInf : Type uInf} {Af : Type uFin}
  {Ohat : Type uHat}
variable [Field K] [CommRing O] [AddCommGroup KInf] [AddCommGroup Af]
  [AddCommGroup Ohat] [TopologicalSpace KInf] [TopologicalSpace Af]
  [TopologicalSpace Ohat]

/-- The book-facing sum `K + Ohat` inside the finite adeles. -/
def chapter06FiniteAdeleSum
    (P : Chapter06AdeleData K O KInf Af Ohat) : Set Af :=
  {x | ∃ a : K, ∃ u : Ohat,
    x = P.globalToFinite a + P.finiteIntegralEmbedding u}

@[simp] theorem mem_chapter06FiniteAdeleSum
    (P : Chapter06AdeleData K O KInf Af Ohat) (x : Af) :
    x ∈ chapter06FiniteAdeleSum P ↔
      ∃ a : K, ∃ u : Ohat,
        x = P.globalToFinite a + P.finiteIntegralEmbedding u := Iff.rfl

/-- Lemma 6.1: every finite adele has one global principal part and an
    integral remainder.  It follows from density of the finite diagonal and
    openness of the integral finite part. -/
theorem chapter06_finite_principal_parts
    [IsTopologicalAddGroup Af]
    (P : Chapter06AdeleData K O KInf Af Ohat) (x : Af) :
    ∃ a : K, ∃ u : Ohat,
      x = P.globalToFinite a + P.finiteIntegralEmbedding u := by
  let U : Set Af := {y | x - y ∈ Set.range P.finiteIntegralEmbedding}
  have hUopen : IsOpen U := by
    exact P.finiteIntegral_range_open.preimage
      (continuous_const.sub continuous_id)
  have hU_nonempty : U.Nonempty := by
    refine ⟨x, ?_⟩
    exact ⟨0, by simp⟩
  rcases P.finite_diagonal_dense.exists_mem_open hUopen hU_nonempty with
    ⟨y, ⟨a, rfl⟩, hy⟩
  change x - P.globalToFinite a ∈ Set.range P.finiteIntegralEmbedding at hy
  rcases hy with ⟨u, hu⟩
  refine ⟨a, u, ?_⟩
  rw [hu]
  abel

/-- The additive set equality form of Lemma 6.1. -/
theorem chapter06_finite_adele_sum_eq_univ
    [IsTopologicalAddGroup Af]
    (P : Chapter06AdeleData K O KInf Af Ohat) :
    chapter06FiniteAdeleSum P = Set.univ := by
  ext x
  constructor
  · intro
    simp
  · intro
    exact chapter06_finite_principal_parts P x

theorem chapter06_finite_principal_parts_iff
    (P : Chapter06AdeleData K O KInf Af Ohat) (x : Af) :
    x ∈ chapter06FiniteAdeleSum P ↔
      ∃ a : K, ∃ u : Ohat,
        x = P.globalToFinite a + P.finiteIntegralEmbedding u := by
  rfl

/- The canonical Chapter 4 carrier already has the exact principal-parts
   statement used by the book.  Keep this bridge next to the abstract adapter
   theorem so later arguments can use the established number-field API. -/
theorem chapter06_canonical_finite_principal_parts
    (K : Type*) [Field K] [NumberField K]
    (x : Chapter04FiniteAdeleRing K) :
    ∃ a : K, ∀ v : Chapter04FinitePlace K,
      x v - (a : Chapter04FiniteLocalField K v) ∈
        chapter04FiniteLocalIntegerSet K v := by
  exact chapter04_finite_principal_parts_are_represented_by_one_global_element K x

theorem chapter06_canonical_finite_diagonal_dense
    (K : Type*) [Field K] [NumberField K] :
    Dense (Set.range (chapter05FiniteDiagonal K)) := by
  exact chapter05_theorem_5_1_strong_approximation_away_from_infinity K

end

end LastLib.Book04AdelesAndIdeles.Chapter06
