import LastLib.Book04AdelesAndIdeles.Chapter06.Dependencies
import LastLib.Book04AdelesAndIdeles.Chapter05.Section03DiscretenessInTheFullAdeles

namespace LastLib.Book04AdelesAndIdeles.Chapter06

open LastLib.Book04AdelesAndIdeles.Chapter05

noncomputable section

/-! # Book 4, Chapter 6, Section 6.1: Why compactness is the central additive theorem -/

universe uK uO uInf uFin uHat

variable {K : Type uK} {O : Type uO} {KInf : Type uInf} {Af : Type uFin}
  {Ohat : Type uHat}
variable [Field K] [CommRing O] [AddCommGroup KInf] [AddCommGroup Af]
  [AddCommGroup Ohat] [TopologicalSpace KInf] [TopologicalSpace Af]
  [TopologicalSpace Ohat]

/- The lattice formulation is kept separate from the motivational prose: it
records exactly the two structural assertions used throughout the chapter. -/

theorem chapter06_additive_lattice_iff
    {G : Type*} {H : Type*} [AddCommGroup G] [AddCommGroup H]
    [TopologicalSpace H] [IsTopologicalAddGroup H] [T2Space H]
    (ι : G →+ H) :
    Chapter06AdditiveLattice ι ↔
      Chapter06DiscreteEmbedding ι ∧
        CompactSpace (H ⧸ ι.range) := Iff.rfl

theorem chapter06_adelic_diagonal_injective
    (P : Chapter06AdeleData K O KInf Af Ohat) :
    Function.Injective (chapter06Diagonal P) := by
  simpa [chapter06Diagonal] using P.diagonal_injective

theorem chapter06_additive_lattice_of_discrete_and_cocompact
    {G : Type*} {H : Type*} [AddCommGroup G] [AddCommGroup H]
    [TopologicalSpace H] [IsTopologicalAddGroup H] [T2Space H]
    (ι : G →+ H)
    (hdiscrete : Chapter06DiscreteEmbedding ι)
    (hcocompact : CompactSpace (H ⧸ ι.range)) :
    Chapter06AdditiveLattice ι := by
  exact ⟨hdiscrete, hcocompact⟩

/- The canonical Chapter 5 diagonal supplies the two global structural facts
   used by the source before compactness is added. -/
theorem chapter06_canonical_diagonal_is_discrete_closed
    (K : Type*) [Field K] [NumberField K] :
    DiscreteTopology (Set.range (chapter05Diagonal K)) ∧
      IsClosed (Set.range (chapter05Diagonal K)) := by
  exact chapter05_theorem_5_2_diagonal_is_discrete_closed K

end

end LastLib.Book04AdelesAndIdeles.Chapter06
