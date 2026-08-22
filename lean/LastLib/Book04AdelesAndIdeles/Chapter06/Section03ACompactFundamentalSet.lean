import LastLib.Book04AdelesAndIdeles.Chapter06.Section01WhyCompactnessIsCentral

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
  exact hD.prod P.finiteIntegral_range_compact

/-- Every full adele reduces to the compact set `D × Ohat`. -/
theorem chapter06_adele_reduced_to_fundamental_set
    (P : Chapter06AdeleData K O KInf Af Ohat)
    (D : Chapter06ArchimedeanCell P)
    (x : Chapter06FullAdele KInf Af) :
    ∃ a : K,
      x - chapter06Diagonal P a ∈
      chapter06FundamentalSet P D.carrier := by
  rcases P.finite_principal_parts x.2 with ⟨a, u, hu⟩
  rcases D.covers (x.1 - P.globalToInfinite a) with ⟨b, hb⟩
  refine ⟨a + P.integerToGlobal b, ?_⟩
  change x.1 - P.globalToInfinite (a + P.integerToGlobal b) ∈ D.carrier ∧
    ∃ v, P.finiteIntegralEmbedding v =
      x.2 - P.globalToFinite (a + P.integerToGlobal b)
  constructor
  · simpa [map_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hb
  · refine ⟨u - P.integerToFinite b, ?_⟩
    simp [hu, map_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

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
  intro y
  rcases chapter06AdeleQuotientMap_surjective P y with ⟨x, rfl⟩
  rcases chapter06_adele_reduced_to_fundamental_set P D x with ⟨a, ha⟩
  refine ⟨⟨x - chapter06Diagonal P a, ha⟩, ?_⟩
  apply (chapter06AdeleQuotientMap_eq_iff P _ _).2
  refine ⟨-a, ?_⟩
  simp [chapter06Diagonal_apply, sub_eq_add_neg, add_left_comm, add_comm]

/-- A compact covering set makes the additive quotient compact. -/
theorem chapter06_compact_quotient_of_compact_cover
    {G : Type*} {H : Type*} [AddCommGroup G] [AddCommGroup H]
    [TopologicalSpace H] (ι : G →+ H) (C : Set H)
    (hC : IsCompact C)
    (hcover : ∀ x : H, ∃ g : G, x - ι g ∈ C) :
    CompactSpace (H ⧸ ι.range) := by
  let q : H → H ⧸ ι.range :=
    QuotientAddGroup.mk' ι.range
  have hqcont : Continuous q := QuotientAddGroup.continuous_mk
  have hsurj : Function.Surjective q :=
    QuotientAddGroup.mk'_surjective ι.range
  have himage : q '' C = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    rcases hsurj y with ⟨x, rfl⟩
    rcases hcover x with ⟨g, hg⟩
    refine ⟨x - ι g, hg, ?_⟩
    apply (QuotientAddGroup.eq_iff_sub_mem).2
    exact ⟨-g, by simp [sub_eq_add_neg, add_left_comm, add_comm]⟩
  refine ⟨?_⟩
  rw [← himage]
  exact hC.image hqcont

/-- Theorem 6.2: the adelic quotient is compact. -/
theorem chapter06_adelic_quotient_compact
    (P : Chapter06AdeleData K O KInf Af Ohat)
    (D : Chapter06ArchimedeanCell P) :
    CompactSpace (Chapter06AdeleQuotient P) := by
  exact chapter06_compact_quotient_of_compact_cover
    (chapter06Diagonal P) (chapter06FundamentalSet P D.carrier)
    (chapter06_fundamental_set_compact P D.carrier D.compact)
    (chapter06_adele_reduced_to_fundamental_set P D)

/-- The quotient is Hausdorff once the diagonal is closed in the Hausdorff
full adele group. -/
theorem chapter06_adelic_quotient_hausdorff
    (P : Chapter06AdeleData K O KInf Af Ohat)
    [IsTopologicalAddGroup KInf] [IsTopologicalAddGroup Af]
    [T2Space KInf] [T2Space Af]
    (hclosed : IsClosed (Set.range (chapter06Diagonal P))) :
    T2Space (Chapter06AdeleQuotient P) := by
  let _ : IsClosed (chapter06GlobalSubgroup P : Set (Chapter06FullAdele KInf Af)) := by
    simpa [chapter06GlobalSubgroup] using hclosed
  infer_instance

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
    [IsTopologicalAddGroup KInf] [IsTopologicalAddGroup Af]
    [T2Space KInf] [T2Space Af]
    (hdiscrete : Chapter06DiscreteEmbedding (chapter06Diagonal P)) :
    Chapter06AdditiveLattice (chapter06Diagonal P) := by
  exact chapter06_additive_lattice_of_discrete_and_cocompact
    (chapter06Diagonal P) hdiscrete (chapter06_adelic_quotient_compact P D)

end

end LastLib.Book04AdelesAndIdeles.Chapter06
