import LastLib.Book04AdelesAndIdeles.Chapter06.Section01WhyCompactnessIsCentral

namespace LastLib.Book04AdelesAndIdeles.Chapter06

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

end

end LastLib.Book04AdelesAndIdeles.Chapter06
