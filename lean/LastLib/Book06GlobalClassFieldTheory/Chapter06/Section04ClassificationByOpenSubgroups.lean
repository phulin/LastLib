import LastLib.Book06GlobalClassFieldTheory.Chapter06.Section01WhyReciprocityDoesNotYetGiveExistence
import LastLib.Book06GlobalClassFieldTheory.Chapter06.Section03ConstructingTheGlobalCharacter

namespace LastLib.Book06GlobalClassFieldTheory.Chapter06

open scoped BigOperators

noncomputable section

/-! # 6.4. Classification by open subgroups

The classification package below exposes both assignments in the theorem,
their inverse laws, the quotient--Galois identification, and the
inclusion-reversing order statement.  The field of an open subgroup is the
compositum already defined in Dependencies.lean.
-/

/- The norm subgroup of a finite abelian extension, with its topological
   finiteness conditions supplied separately by the existence theorem. -/
abbrev chapter06NormSubgroupOfExtension
    {K Ks C : Type*} [Field K] [Field Ks] [Algebra K Ks]
    [CommGroup C]
    (E : Chapter06FiniteAbelianExtension K Ks C) : Subgroup C :=
  chapter06NormSubgroup E.normMap

/- An explicit witness for all assertions in the global existence theorem. -/
structure Chapter06GlobalExistenceCorrespondence
    (K Ks C : Type*) [Field K] [Field Ks] [Algebra K Ks]
    [CommGroup C] [TopologicalSpace C]
    (A : Chapter06CharacterFieldAssignment K Ks C) where
  extensionOfOpen :
    Chapter06OpenFiniteIndexSubgroup C →
      Chapter06FiniteAbelianExtension K Ks C
  normSubgroupOfExtension :
    Chapter06FiniteAbelianExtension K Ks C →
      Chapter06OpenFiniteIndexSubgroup C
  normSubgroup_formula :
    ∀ E, (normSubgroupOfExtension E).subgroup =
      chapter06NormSubgroupOfExtension E
  normSubgroup_open :
    ∀ (E : Chapter06FiniteAbelianExtension K Ks C),
      IsOpen ((chapter06NormSubgroupOfExtension E : Subgroup C) : Set C)
  normSubgroup_finiteIndex :
    ∀ (E : Chapter06FiniteAbelianExtension K Ks C),
      (chapter06NormSubgroupOfExtension E).FiniteIndex
  field_of_open_is_compositum :
    ∀ H, (extensionOfOpen H).field =
      chapter06FieldOfOpenSubgroup H A
  left_inverse :
    ∀ H, chapter06NormSubgroupOfExtension (extensionOfOpen H) = H.subgroup
  right_inverse :
    ∀ E, (extensionOfOpen (normSubgroupOfExtension E)).field = E.field
  quotient_galois :
    ∀ H, (C ⧸ H.subgroup) ≃*
      Gal((extensionOfOpen H).field / K)
  artin :
    ∀ H, C →* Gal((extensionOfOpen H).field / K)
  artin_surjective :
    ∀ H, Function.Surjective (artin H)
  artin_factorization :
    ∀ H, (quotient_galois H).toMonoidHom.comp (QuotientGroup.mk' H.subgroup) =
      artin H
  artin_kernel :
    ∀ H, (artin H).ker = H.subgroup
  quotient_index_degree :
    ∀ H, Nat.card (C ⧸ H.subgroup) =
      chapter06GaloisDegree (K := K) (L := (extensionOfOpen H).field)
  compositum_kernel_intersection :
    ∀ H,
      chapter06NormSubgroupOfExtension (extensionOfOpen H) =
        ⨅ χ ∈ chapter06LiftedQuotientCharacters H, χ.ker
  inclusion_reversal :
    ∀ H₁ H₂,
      H₁.subgroup ≤ H₂.subgroup ↔
        (extensionOfOpen H₂).field ≤ (extensionOfOpen H₁).field

/- A character realization tagged with the field selected by the
   compositum assignment. -/
structure Chapter06AssignedCharacterRealization
    (K Ks C : Type*) [Field K] [Field Ks] [Algebra K Ks]
    [CommGroup C]
    (A : Chapter06CharacterFieldAssignment K Ks C)
    (χ : C →* ℂˣ) where
  realization : Chapter06FiniteCharacterRealization K Ks C χ
  field_eq_assignment :
    realization.reciprocity.extension.field = A.fieldOfCharacter χ

/- The standard construction from the character-field assignment and the
   character realization lemma.  The realization hypothesis is exactly the
   input supplied by Sections 6.2 and 6.3 for each finite quotient
   character. -/
theorem chapter06_global_existence_from_character_realizations
    {K Ks C : Type*} [Field K] [Field Ks] [Algebra K Ks]
    [CommGroup C] [TopologicalSpace C]
    (A : Chapter06CharacterFieldAssignment K Ks C)
    (realize :
      ∀ (H : Chapter06OpenFiniteIndexSubgroup C)
        (χ : C →* ℂˣ), χ ∈ chapter06LiftedQuotientCharacters H →
          Chapter06AssignedCharacterRealization K Ks C A χ) :
    Nonempty (Chapter06GlobalExistenceCorrespondence K Ks C A) := by
  sorry

/- Theorem 6.3. -/
theorem chapter06_theorem_6_3_global_existence
    {K Ks C : Type*} [Field K] [Field Ks] [Algebra K Ks]
    [CommGroup C] [TopologicalSpace C]
    (A : Chapter06CharacterFieldAssignment K Ks C)
    (realize :
      ∀ (H : Chapter06OpenFiniteIndexSubgroup C)
        (χ : C →* ℂˣ), χ ∈ chapter06LiftedQuotientCharacters H →
          Chapter06AssignedCharacterRealization K Ks C A χ) :
    Nonempty (Chapter06GlobalExistenceCorrespondence K Ks C A) :=
  chapter06_global_existence_from_character_realizations A realize

theorem chapter06_global_existence_quotient_galois
    {K Ks C : Type*} [Field K] [Field Ks] [Algebra K Ks]
    [CommGroup C] [TopologicalSpace C]
    (A : Chapter06CharacterFieldAssignment K Ks C)
    (G : Chapter06GlobalExistenceCorrespondence K Ks C A)
    (H : Chapter06OpenFiniteIndexSubgroup C) :
    Nonempty ((C ⧸ H.subgroup) ≃*
      Gal((G.extensionOfOpen H).field / K)) :=
  ⟨G.quotient_galois H⟩

theorem chapter06_global_existence_index_formula
    {K Ks C : Type*} [Field K] [Field Ks] [Algebra K Ks]
    [CommGroup C] [TopologicalSpace C]
    (A : Chapter06CharacterFieldAssignment K Ks C)
    (G : Chapter06GlobalExistenceCorrespondence K Ks C A)
    (H : Chapter06OpenFiniteIndexSubgroup C) :
    Nat.card (C ⧸ H.subgroup) =
      chapter06GaloisDegree (K := K) (L := (G.extensionOfOpen H).field) :=
  G.quotient_index_degree H

theorem chapter06_compositum_triviality_iff
    {K Ks C : Type*} [Field K] [Field Ks] [Algebra K Ks]
    [CommGroup C] [TopologicalSpace C]
    (A : Chapter06CharacterFieldAssignment K Ks C)
    (G : Chapter06GlobalExistenceCorrespondence K Ks C A)
    (H : Chapter06OpenFiniteIndexSubgroup C) (x : C) :
    x ∈ chapter06NormSubgroupOfExtension (G.extensionOfOpen H) ↔
      ∀ χ ∈ chapter06LiftedQuotientCharacters H, χ x = 1 := by
  sorry

theorem chapter06_global_existence_inclusion_reversal
    {K Ks C : Type*} [Field K] [Field Ks] [Algebra K Ks]
    [CommGroup C] [TopologicalSpace C]
    (A : Chapter06CharacterFieldAssignment K Ks C)
    (G : Chapter06GlobalExistenceCorrespondence K Ks C A)
    (H₁ H₂ : Chapter06OpenFiniteIndexSubgroup C) :
    H₁.subgroup ≤ H₂.subgroup ↔
      (G.extensionOfOpen H₂).field ≤ (G.extensionOfOpen H₁).field :=
  G.inclusion_reversal H₁ H₂

/- A finite-index subgroup without openness is outside the topological
   classification. -/
theorem chapter06_nonopen_finite_index_subgroup_not_classified
    {C : Type*} [CommGroup C] [TopologicalSpace C]
    (H : Subgroup C) (_hfinite : H.FiniteIndex)
    (hnotopen : ¬ IsOpen (H : Set C)) :
    H ∉ Set.range
      (fun T : Chapter06OpenFiniteIndexSubgroup C => T.subgroup) := by
  intro h
  rcases h with ⟨T, hT⟩
  exact hnotopen (hT ▸ T.isOpen')

theorem chapter06_open_finite_index_subgroup_range_iff
    {C : Type*} [CommGroup C] [TopologicalSpace C]
    (H : Subgroup C) :
    H ∈ Set.range
        (fun T : Chapter06OpenFiniteIndexSubgroup C => T.subgroup) ↔
      IsOpen (H : Set C) ∧ H.FiniteIndex := by
  constructor
  · rintro ⟨T, rfl⟩
    exact ⟨T.isOpen', T.finiteIndex'⟩
  · rintro ⟨hop, hfinite⟩
    exact ⟨
      { subgroup := H
        isOpen' := hop
        finiteIndex' := hfinite },
      rfl⟩

theorem chapter06_kernel_of_continuous_finite_quotient_is_open
    {C D : Type*} [CommGroup C] [CommGroup D]
    [TopologicalSpace C] [TopologicalSpace D] [DiscreteTopology D]
    (q : C →* D) (hq : Continuous q) [Finite D] :
    IsOpen (q.ker : Set C) ∧ q.ker.FiniteIndex := by
  sorry

/- The norm and field assignments are inverse on the represented finite
   abelian extensions and open finite-index subgroups. -/
theorem chapter06_global_existence_left_inverse
    {K Ks C : Type*} [Field K] [Field Ks] [Algebra K Ks]
    [CommGroup C] [TopologicalSpace C]
    (A : Chapter06CharacterFieldAssignment K Ks C)
    (G : Chapter06GlobalExistenceCorrespondence K Ks C A)
    (H : Chapter06OpenFiniteIndexSubgroup C) :
    chapter06NormSubgroupOfExtension (G.extensionOfOpen H) = H.subgroup :=
  G.left_inverse H

theorem chapter06_global_existence_right_inverse
    {K Ks C : Type*} [Field K] [Field Ks] [Algebra K Ks]
    [CommGroup C] [TopologicalSpace C]
    (A : Chapter06CharacterFieldAssignment K Ks C)
    (G : Chapter06GlobalExistenceCorrespondence K Ks C A)
    (E : Chapter06FiniteAbelianExtension K Ks C) :
    (G.extensionOfOpen (G.normSubgroupOfExtension E)).field = E.field :=
  G.right_inverse E

end

end LastLib.Book06GlobalClassFieldTheory.Chapter06
