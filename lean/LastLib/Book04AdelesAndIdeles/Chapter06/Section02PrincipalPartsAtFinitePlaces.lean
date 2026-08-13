import LastLib.Book04AdelesAndIdeles.Chapter06.Dependencies

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
    integral remainder.  The preceding strong-approximation statement is
    recorded in the adapter data. -/
theorem chapter06_finite_principal_parts
    (P : Chapter06AdeleData K O KInf Af Ohat) (x : Af) :
    ∃ a : K, ∃ u : Ohat,
      x = P.globalToFinite a + P.finiteIntegralEmbedding u := by
  exact P.finite_principal_parts x

/-- The additive set equality form of Lemma 6.1. -/
theorem chapter06_finite_adele_sum_eq_univ
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
