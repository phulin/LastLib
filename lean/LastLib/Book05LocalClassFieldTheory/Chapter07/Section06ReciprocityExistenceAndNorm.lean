import LastLib.Book05LocalClassFieldTheory.Chapter07.Section05ProfiniteCompletion

namespace LastLib.Book05LocalClassFieldTheory.Chapter07

noncomputable section

open CategoryTheory Opposite

/-- The fixed field of the commutator subgroup of a finite Galois group. -/
noncomputable def chapter07MaximalAbelianSubextension
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E] :
    IntermediateField K E :=
  IntermediateField.fixedField (commutator (Gal(E / K)))

/-- The commutator fixed field is Galois over the base. -/
theorem chapter07_maximal_abelian_subextension_is_galois
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E] :
    IsGalois K
      (chapter07MaximalAbelianSubextension (K := K) (E := E)) := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the quotient of Gal(E/K) by its commutator is
abelian, and the fixed-field quotient API supplies the corresponding
abelian-Galois instance. -/
theorem chapter07_maximal_abelian_subextension_is_abelian
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E] :
    IsAbelianGalois K
      (chapter07MaximalAbelianSubextension (K := K) (E := E)) := by
  sorry

/-- Every abelian intermediate field of E/K lies in the commutator fixed
field. -/
theorem chapter07_maximal_abelian_subextension_is_maximal
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E]
    (L : IntermediateField K E) [IsAbelianGalois K L] :
    L ≤ chapter07MaximalAbelianSubextension (K := K) (E := E) := by
  sorry

/-- The fixing subgroup of the maximal abelian subextension is the
commutator subgroup. -/
theorem chapter07_maximal_abelian_subextension_fixing_subgroup
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E] :
    (chapter07MaximalAbelianSubextension (K := K) (E := E)).fixingSubgroup =
      commutator (Gal(E / K)) := by
  sorry

/-- The unique finite abelian level attached by the local existence theorem
to an open finite-index subgroup. -/
/- LOCAL_DEPENDENCY_GUESS: the direct construction and uniqueness proof are
the local-existence theorem supplied by the preceding chapters. -/
theorem chapter07_local_existence_theorem
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsAbelianGalois K KAb]
    (D : Chapter07LocalFieldData K)
    (hmax : chapter07IsMaximalAbelianExtension K KAb)
    (H : Chapter07OpenFiniteIndexSubgroup Kˣ) :
    ∃! L : Chapter07FiniteAbelianIndex K KAb,
      chapter07NormSubgroup (K := K) (L := L) = H.1 := by
  sorry

/-- The pointwise local-existence theorem is the chapter's existence
property used by the completion and correspondence APIs. -/
theorem chapter07_local_existence_gives_existence_property
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsAbelianGalois K KAb]
    (D : Chapter07LocalFieldData K)
    (hmax : chapter07IsMaximalAbelianExtension K KAb) :
    chapter07ExistenceProperty K KAb := by
  intro H
  exact chapter07_local_existence_theorem D hmax H

/-- The unique finite abelian level attached by the local existence theorem
to an open finite-index subgroup. -/
noncomputable def chapter07ExtensionOfOpenSubgroup
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsAbelianGalois K KAb]
    (hExist : chapter07ExistenceProperty K KAb)
    (H : Chapter07OpenFiniteIndexSubgroup Kˣ) :
    Chapter07FiniteAbelianIndex K KAb :=
  (hExist H).choose

/-- The norm group of the extension chosen from H is H. -/
theorem chapter07_norm_of_extension_of_open_subgroup
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsAbelianGalois K KAb]
    (hExist : chapter07ExistenceProperty K KAb)
    (H : Chapter07OpenFiniteIndexSubgroup Kˣ) :
    chapter07NormSubgroup (K := K)
        (L := chapter07ExtensionOfOpenSubgroup hExist H) = H.1 :=
  ((hExist H).choose_spec).1

/-- Uniqueness in the local existence theorem. -/
theorem chapter07_extension_of_open_subgroup_unique
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsAbelianGalois K KAb]
    (hExist : chapter07ExistenceProperty K KAb)
    (H : Chapter07OpenFiniteIndexSubgroup Kˣ)
    (L : Chapter07FiniteAbelianIndex K KAb)
    (hL : chapter07NormSubgroup (K := K) (L := L) = H.1) :
    L = chapter07ExtensionOfOpenSubgroup hExist H :=
  (hExist H).unique hL ((hExist H).choose_spec).1

/-- The degree/index formula in the local existence theorem. -/
theorem chapter07_local_existence_degree
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsAbelianGalois K KAb]
    (hExist : chapter07ExistenceProperty K KAb)
    (H : Chapter07OpenFiniteIndexSubgroup Kˣ) :
    Module.finrank K (chapter07ExtensionOfOpenSubgroup hExist H) =
      H.1.index := by
  sorry

/-- Finite reciprocity at the level selected by an open subgroup. -/
theorem chapter07_local_existence_finite_reciprocity
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsAbelianGalois K KAb]
    (S : Chapter07FiniteArtinSystem K KAb)
    (hExist : chapter07ExistenceProperty K KAb)
    (H : Chapter07OpenFiniteIndexSubgroup Kˣ) :
    Nonempty
      (Kˣ ⧸ H.1 ≃*
        Gal(chapter07ExtensionOfOpenSubgroup hExist H / K)) := by
  sorry

/-- Under the existence theorem, the norm-subgroup assignment lands in the
open finite-index subgroup API. -/
noncomputable def chapter07NormSubgroupAsOpenFiniteIndex
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsAbelianGalois K KAb]
    (S : Chapter07FiniteArtinSystem K KAb)
    (hopen :
      ∀ L : Chapter07FiniteAbelianIndex K KAb,
        IsOpen (chapter07NormSubgroup (K := K) (L := L) : Set Kˣ))
    (L : Chapter07FiniteAbelianIndex K KAb) :
    Chapter07OpenFiniteIndexSubgroup Kˣ where
  val := chapter07NormSubgroup (K := K) (L := L)
  property := by
    constructor
    · exact hopen L
    · rw [← S.kernel_eq_norm L]
      infer_instance

/-- Inclusion of finite abelian levels reverses inclusion of norm groups. -/
theorem chapter07_norm_subgroup_antitone
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb]
    (L₁ L₂ : Chapter07FiniteAbelianIndex K KAb)
    (hL : L₁ ≤ L₂) :
    chapter07NormSubgroup (K := K) (L := L₂) ≤
      chapter07NormSubgroup (K := K) (L := L₁) := by
  sorry

/-- Equality of norm groups determines the finite abelian level. -/
theorem chapter07_norm_subgroup_injective
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsAbelianGalois K KAb]
    (hExist : chapter07ExistenceProperty K KAb)
    {L₁ L₂ : Chapter07FiniteAbelianIndex K KAb}
    (hL : chapter07NormSubgroup (K := K) (L := L₁) =
      chapter07NormSubgroup (K := K) (L := L₂)) :
    L₁ = L₂ := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the finite reciprocity, local existence, and norm
limitation interfaces together assemble into the inclusion-reversing
correspondence stated by the chapter. -/
theorem chapter07_norm_subgroup_inclusion_reversing_bijection
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsAbelianGalois K KAb]
    (S : Chapter07FiniteArtinSystem K KAb)
    (hopen :
      ∀ L : Chapter07FiniteAbelianIndex K KAb,
        IsOpen (chapter07NormSubgroup (K := K) (L := L) : Set Kˣ))
    (hExist : chapter07ExistenceProperty K KAb) :
    Nonempty
      (Chapter07FiniteAbelianIndex K KAb ≃o
        OrderDual (Chapter07OpenFiniteIndexSubgroup Kˣ)) := by
  sorry

/-- The order equivalence sends a finite level to its norm subgroup. -/
theorem chapter07_norm_subgroup_correspondence_is_norm
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsAbelianGalois K KAb]
    (S : Chapter07FiniteArtinSystem K KAb)
    (hopen :
      ∀ L : Chapter07FiniteAbelianIndex K KAb,
        IsOpen (chapter07NormSubgroup (K := K) (L := L) : Set Kˣ))
    (hExist : chapter07ExistenceProperty K KAb) :
    ∃ e : Chapter07FiniteAbelianIndex K KAb ≃o
        OrderDual (Chapter07OpenFiniteIndexSubgroup Kˣ),
      ∀ L, e L = chapter07NormSubgroupAsOpenFiniteIndex S hopen L := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: this is the norm-limitation theorem proved at
finite level and reused by the final Chapter 7 synthesis. -/
/-- Norm limitation for a finite Galois extension. -/
theorem chapter07_norm_limitation
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E] :
    chapter07NormSubgroup (K := K) (L := E) =
      chapter07NormSubgroup (K := K)
        (L := chapter07MaximalAbelianSubextension (K := K) (E := E)) := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: this packages the three named theorems as a
single source-facing declaration; the finite Artin system and the selected
maximal abelian model are supplied by earlier chapters. -/
theorem chapter07_reciprocity_existence_and_norm_theorems
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsAbelianGalois K KAb]
    (S : Chapter07FiniteArtinSystem K KAb)
    (D : Chapter07LocalFieldData K)
    (hmax : chapter07IsMaximalAbelianExtension K KAb) :
    (∀ L : Chapter07FiniteAbelianIndex K KAb,
      Nonempty
        (Kˣ ⧸ chapter07NormSubgroup (K := K) (L := L) ≃*
          Gal(L / K))) ∧
      chapter07ExistenceProperty K KAb ∧
      (∀ (E : Type*) [Field E] [Algebra K E] [FiniteDimensional K E]
        [IsGalois K E],
        chapter07NormSubgroup (K := K) (L := E) =
          chapter07NormSubgroup (K := K)
            (L := chapter07MaximalAbelianSubextension (K := K) (E := E))) := by
  sorry

end

end LastLib.Book05LocalClassFieldTheory.Chapter07
