import LastLib.Book04AdelesAndIdeles.Chapter06.Section02PrincipalPartsAtFinitePlaces

namespace LastLib.Book04AdelesAndIdeles.Chapter06

noncomputable section

/-! # Book 4, Chapter 6, Section 6.3: A compact fundamental set -/

universe uK uO uInf uFin uHat

variable {K : Type uK} {O : Type uO} {KInf : Type uInf} {Af : Type uFin}
  {Ohat : Type uHat}
variable [Field K] [CommRing O] [AddCommGroup KInf] [AddCommGroup Af]
  [AddCommGroup Ohat] [TopologicalSpace KInf] [TopologicalSpace Af]
  [TopologicalSpace Ohat]

/-- The product of an archimedean cell with the integral finite adele part is
compact. -/
theorem chapter06_fundamental_set_compact
    (P : Chapter06AdeleData K O KInf Af Ohat) (D : Set KInf)
    (hD : IsCompact D) :
    IsCompact (chapter06FundamentalSet P D) := by
  sorry

/-- Every full adele reduces to the compact set `D × Ohat`. -/
theorem chapter06_adele_reduced_to_fundamental_set
    (P : Chapter06AdeleData K O KInf Af Ohat)
    (D : Chapter06ArchimedeanCell P)
    (x : Chapter06FullAdele KInf Af) :
    ∃ a : K,
      x - chapter06Diagonal P a ∈
      chapter06FundamentalSet P D.carrier := by
  sorry

theorem chapter06_adelic_has_compact_fundamental_set
    (P : Chapter06AdeleData K O KInf Af Ohat)
    (D : Chapter06ArchimedeanCell P) :
    Chapter06CompactFundamentalSet (chapter06Diagonal P) := by
  refine ⟨chapter06FundamentalSet P D.carrier,
    chapter06_fundamental_set_compact P D.carrier D.compact, ?_⟩
  intro x
  exact chapter06_adele_reduced_to_fundamental_set P D x

/-- The compact covering set maps surjectively to the adelic quotient. -/
theorem chapter06_fundamental_set_quotient_surjective
    (P : Chapter06AdeleData K O KInf Af Ohat)
    (D : Chapter06ArchimedeanCell P) :
    Function.Surjective (chapter06FundamentalSetQuotientMap P D.carrier) := by
  sorry

/-- A compact covering set makes the additive quotient compact. -/
theorem chapter06_compact_quotient_of_compact_cover
    {G : Type*} {H : Type*} [AddCommGroup G] [AddCommGroup H]
    [TopologicalSpace H] (ι : G →+ H) (C : Set H)
    (hC : IsCompact C)
    (hcover : ∀ x : H, ∃ g : G, x - ι g ∈ C) :
    CompactSpace (H ⧸ chapter06ImageSubgroup ι) := by
  sorry

/-- Theorem 6.2: the adelic quotient is compact. -/
theorem chapter06_adelic_quotient_compact
    (P : Chapter06AdeleData K O KInf Af Ohat)
    (D : Chapter06ArchimedeanCell P) :
    CompactSpace (Chapter06AdeleQuotient P) := by
  sorry

/-- The quotient is Hausdorff once the diagonal is closed in the Hausdorff
full adele group. -/
theorem chapter06_adelic_quotient_hausdorff
    (P : Chapter06AdeleData K O KInf Af Ohat)
    [IsTopologicalAddGroup KInf] [IsTopologicalAddGroup Af]
    [T2Space KInf] [T2Space Af]
    (hclosed : IsClosed (Set.range (chapter06Diagonal P))) :
    T2Space (Chapter06AdeleQuotient P) := by
  sorry

theorem chapter06_adelic_quotient_hausdorff_of_data
    (P : Chapter06AdeleData K O KInf Af Ohat)
    [IsTopologicalAddGroup KInf] [IsTopologicalAddGroup Af]
    [T2Space KInf] [T2Space Af] :
    T2Space (Chapter06AdeleQuotient P) := by
  exact chapter06_adelic_quotient_hausdorff P
    (by simpa [chapter06Diagonal] using P.diagonal_closed)

/-- The pair of discreteness and compactness is the additive local--global
lattice theorem. -/
theorem chapter06_adelic_diagonal_is_lattice
    (P : Chapter06AdeleData K O KInf Af Ohat)
    (D : Chapter06ArchimedeanCell P)
    (hdiscrete : Chapter06DiscreteEmbedding (chapter06Diagonal P)) :
    Chapter06AdditiveLattice (chapter06Diagonal P) := by
  exact chapter06_additive_lattice_of_discrete_and_cocompact
    (chapter06Diagonal P) hdiscrete (chapter06_adelic_quotient_compact P D)

end

end LastLib.Book04AdelesAndIdeles.Chapter06
