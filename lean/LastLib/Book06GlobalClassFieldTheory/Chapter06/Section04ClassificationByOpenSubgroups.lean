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
    {K Ks C : Type*} [Field K] [NumberField K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks]
    [CommGroup C]
    (E : Chapter06FiniteAbelianExtension K Ks C) : Subgroup C :=
  chapter06NormSubgroup E.normMap

/- An explicit witness for all assertions in the global existence theorem. -/
structure Chapter06GlobalExistenceCorrespondence
    (K Ks C : Type*) [Field K] [NumberField K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks]
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
    (K Ks C : Type*) [Field K] [NumberField K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks]
    [CommGroup C] [TopologicalSpace C]
    (A : Chapter06CharacterFieldAssignment K Ks C)
    (χ : C →* ℂˣ) where
  realization : Chapter06FiniteCharacterRealization K Ks C χ
  field_eq_assignment :
    realization.reciprocity.extension.field = A.fieldOfCharacter χ

/- Individual character realizations do not by themselves supply the finite
   reciprocity witness for a compositum, the inclusion-reversing field
   lattice, or recovery of an arbitrary represented extension.  These are the
   genuinely additional lattice-level inputs needed by the source proof. -/
structure Chapter06GlobalExistenceLatticeInput
    (K Ks C : Type*) [Field K] [NumberField K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks]
    [CommGroup C] [TopologicalSpace C]
    (A : Chapter06CharacterFieldAssignment K Ks C) where
  realize :
    ∀ (H : Chapter06OpenFiniteIndexSubgroup C)
      (χ : C →* ℂˣ), χ ∈ chapter06LiftedQuotientCharacters H →
        Chapter06AssignedCharacterRealization K Ks C A χ
  /- Finite reciprocity is an earlier input: every already represented finite
     abelian extension has a witness with the same field and class-norm
     subgroup. -/
  finite_reciprocity_for_extension :
    ∀ E : Chapter06FiniteAbelianExtension K Ks C,
      ∃ R : Chapter06FiniteReciprocityWitness K Ks C,
        R.extension.field = E.field ∧
          chapter06NormSubgroup R.extension.normMap =
            chapter06NormSubgroup E.normMap
  /- The field-theoretic compositum is finite abelian, so the preceding finite
     reciprocity input can be applied to it.  Only the field identity is
     supplied here; the Artin-kernel intersection is the conclusion of the
     existence argument, not an input. -/
  compositum_reciprocity :
    ∀ H : Chapter06OpenFiniteIndexSubgroup C,
      ∃ R : Chapter06FiniteReciprocityWitness K Ks C,
        R.extension.field = chapter06FieldOfOpenSubgroup H A
  /- The compositum witness must be tied to the individual character
     realizations.  Field equality alone does not relate its Artin map to
     the characters whose fields generate the compositum. -/
  compositum_character_compatibility :
    ∀ (H : Chapter06OpenFiniteIndexSubgroup C)
      (R : Chapter06FiniteReciprocityWitness K Ks C),
      R.extension.field = chapter06FieldOfOpenSubgroup H A →
      ∀ χ ∈ chapter06LiftedQuotientCharacters H,
        ∃ q : Gal(R.extension.field / K) →* ℂˣ,
          χ = q.comp R.artin
  /- Conversely, the characters induced by the compositum witness separate
     its finite abelian Galois group.  This is the lattice-level bridge used
     to recover the starting subgroup from the compositum norm kernel. -/
  compositum_character_separation :
    ∀ (H : Chapter06OpenFiniteIndexSubgroup C)
      (R : Chapter06FiniteReciprocityWitness K Ks C),
      R.extension.field = chapter06FieldOfOpenSubgroup H A →
      ∀ q : Gal(R.extension.field / K) →* ℂˣ,
        ∃ χ ∈ chapter06LiftedQuotientCharacters H,
          χ = q.comp R.artin

theorem chapter06_finite_reciprocity_witness_kernel_finite_index
    {K Ks C : Type*} [Field K] [NumberField K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks]
    [CommGroup C] [TopologicalSpace C]
    (R : Chapter06FiniteReciprocityWitness K Ks C) :
    R.artin.ker.FiniteIndex := by
  let _ : Finite (Gal(R.extension.field / K)) := R.extension.galoisFinite
  let e : (C ⧸ R.artin.ker) ≃* Gal(R.extension.field / K) :=
    QuotientGroup.quotientKerEquivOfSurjective R.artin R.surjective_artin
  apply Subgroup.finiteIndex_iff_finite_quotient.mpr
  exact Finite.of_injective e.toEquiv e.injective

noncomputable def chapter06_finite_reciprocity_witness_quotient_galois
    {K Ks C : Type*} [Field K] [NumberField K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks]
    [CommGroup C] [TopologicalSpace C]
    (R : Chapter06FiniteReciprocityWitness K Ks C) :
    (C ⧸ R.artin.ker) ≃* Gal(R.extension.field / K) := by
  exact QuotientGroup.quotientKerEquivOfSurjective R.artin
    R.surjective_artin

/- The remaining proof uses the lattice input to assemble compatible finite
   character fields and to recover represented extensions. -/
theorem chapter06_global_existence_from_character_realizations
    {K Ks C : Type*} [Field K] [NumberField K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks]
    [CommGroup C] [TopologicalSpace C]
    (A : Chapter06CharacterFieldAssignment K Ks C)
    (input : Chapter06GlobalExistenceLatticeInput K Ks C A) :
    Nonempty (Chapter06GlobalExistenceCorrespondence K Ks C A) := by
  sorry

/- Theorem 6.3. -/
theorem chapter06_theorem_6_3_global_existence
    {K Ks C : Type*} [Field K] [NumberField K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks]
    [CommGroup C] [TopologicalSpace C]
    (A : Chapter06CharacterFieldAssignment K Ks C)
    (input : Chapter06GlobalExistenceLatticeInput K Ks C A) :
    Nonempty (Chapter06GlobalExistenceCorrespondence K Ks C A) :=
  chapter06_global_existence_from_character_realizations A input

def chapter06_global_existence_quotient_galois
    {K Ks C : Type*} [Field K] [NumberField K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks]
    [CommGroup C] [TopologicalSpace C]
    (A : Chapter06CharacterFieldAssignment K Ks C)
    (G : Chapter06GlobalExistenceCorrespondence K Ks C A)
    (H : Chapter06OpenFiniteIndexSubgroup C) :
    (C ⧸ H.subgroup) ≃*
      Gal((G.extensionOfOpen H).field / K) :=
  G.quotient_galois H

theorem chapter06_global_existence_index_formula
    {K Ks C : Type*} [Field K] [NumberField K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks]
    [CommGroup C] [TopologicalSpace C]
    (A : Chapter06CharacterFieldAssignment K Ks C)
    (G : Chapter06GlobalExistenceCorrespondence K Ks C A)
    (H : Chapter06OpenFiniteIndexSubgroup C) :
    Nat.card (C ⧸ H.subgroup) =
      chapter06GaloisDegree (K := K) (L := (G.extensionOfOpen H).field) :=
  G.quotient_index_degree H

theorem chapter06_compositum_triviality_iff
    {K Ks C : Type*} [Field K] [NumberField K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks]
    [CommGroup C] [TopologicalSpace C]
    (A : Chapter06CharacterFieldAssignment K Ks C)
    (G : Chapter06GlobalExistenceCorrespondence K Ks C A)
    (H : Chapter06OpenFiniteIndexSubgroup C) (x : C) :
    x ∈ chapter06NormSubgroupOfExtension (G.extensionOfOpen H) ↔
      ∀ χ ∈ chapter06LiftedQuotientCharacters H, χ x = 1 := by
  rw [G.compositum_kernel_intersection H]
  simp only [Subgroup.mem_iInf, MonoidHom.mem_ker]

theorem chapter06_global_existence_inclusion_reversal
    {K Ks C : Type*} [Field K] [NumberField K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks]
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
  constructor
  · change IsOpen (q ⁻¹' ({1} : Set D))
    exact IsOpen.preimage hq (isOpen_discrete _)
  · let _ : Finite (MonoidHom.range q) :=
      Finite.of_injective (MonoidHom.range q).subtype
        (MonoidHom.range q).subtype_injective
    apply Subgroup.finiteIndex_iff_finite_quotient.mpr
    exact Finite.of_injective (QuotientGroup.quotientKerEquivRange q).toEquiv
      (QuotientGroup.quotientKerEquivRange q).injective

/- The norm and field assignments are inverse on the represented finite
   abelian extensions and open finite-index subgroups. -/
theorem chapter06_global_existence_left_inverse
    {K Ks C : Type*} [Field K] [NumberField K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks]
    [CommGroup C] [TopologicalSpace C]
    (A : Chapter06CharacterFieldAssignment K Ks C)
    (G : Chapter06GlobalExistenceCorrespondence K Ks C A)
    (H : Chapter06OpenFiniteIndexSubgroup C) :
    chapter06NormSubgroupOfExtension (G.extensionOfOpen H) = H.subgroup :=
  G.left_inverse H

theorem chapter06_global_existence_right_inverse
    {K Ks C : Type*} [Field K] [NumberField K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks]
    [CommGroup C] [TopologicalSpace C]
    (A : Chapter06CharacterFieldAssignment K Ks C)
    (G : Chapter06GlobalExistenceCorrespondence K Ks C A)
    (E : Chapter06FiniteAbelianExtension K Ks C) :
    (G.extensionOfOpen (G.normSubgroupOfExtension E)).field = E.field :=
  G.right_inverse E

end

end LastLib.Book06GlobalClassFieldTheory.Chapter06
