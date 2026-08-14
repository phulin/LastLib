import LastLib.Book06GlobalClassFieldTheory.Chapter02.Dependencies
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace LastLib.Book06GlobalClassFieldTheory.Chapter02

noncomputable section

open scoped BigOperators Pointwise

universe u v w z

/-! ## 2.4. Why principal ideles act trivially -/

/-- A convenient name for the multiplicative group `Kˣ ≃ Kˣ` representing `K×`. -/
abbrev chapter02FieldMultiplicativeGroup (K : Type u) [Field K] := Kˣ

/-
The proof of the next theorem uses the cyclic-algebra realization of the local
symbols and the global Brauer invariant sequence.  The earlier class-field
theory chapters are absent in this checkout, so the proof is left as the
chapter's principal global dependency rather than replaced by an assumption of
the conclusion.
-/

/- DEPENDENCY_GUESS: the available Book 4/Book 5 APIs still need a focused
   Brauer--idele adapter supplying the cyclic-algebra localization and
   invariant-sum argument used by this theorem.  The chapter-facing `A` and
   `P` structures are provisional; reconciliation must connect them to one
   finite abelian extension `L/K` and its completion maps. -/

/-- A family of characters that detects every element of the finite abelian
Artin target. -/
structure Chapter02CharacterSeparation
    (G T : Type*) [CommGroup G] [CommGroup T] [Finite G] where
  characters : Set (G →* T)
  separates : ∀ g : G, (∀ χ ∈ characters, χ g = 1) → g = 1

/-
The source proof obtains the principal-idele product formula by applying each
cyclic character to the local symbols, identifying the resulting values with
local Brauer invariants, and using the global invariant sum.  This adapter
records precisely that lower-level input.  It does not assume the Artin
product itself; the character-separation field is what turns the invariant
calculation into the group-valued conclusion.
-/
structure Chapter02PrincipalIdeleCharacterData
    {K : Type u} [Field K]
    {V : Type v} {H : V → Type w} [∀ x, CommGroup (H x)]
    {G : Type z} [CommGroup G] [Finite G]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G)
    (P : Chapter02PrincipalIdeleData K D)
    (S T : Type*) [CommGroup S] [CommGroup T] where
  characters : Chapter02CharacterSeparation G T
  localInvariant : ∀ χ ∈ characters.characters, ∀ v : V, H v →* S
  evaluateInvariant : ∀ _χ : G →* T, S →* T
  localInvariant_eq_artin : ∀ (χ : G →* T) (hχ : χ ∈ characters.characters)
      (v : V) (x : H v),
      evaluateInvariant χ (localInvariant χ hχ v x) = χ (A.localArtin v x)
  principalInvariant_product : ∀ (χ : G →* T) (hχ : χ ∈ characters.characters)
      (a : Kˣ),
      Finset.prod (chapter02GlobalArtinIndexSet A (P.principal a))
        (fun v => localInvariant χ hχ v ((P.principal a).1 v)) = 1

/-- Product formula for local Artin symbols on a principal idele. -/
theorem chapter02_principal_ideles_product_formula
    {K : Type u} [Field K]
    {V : Type v} {H : V → Type w} [∀ x, CommGroup (H x)]
    {G : Type z} [CommGroup G] [Finite G]
    {S T : Type*} [CommGroup S] [CommGroup T]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G)
    (P : Chapter02PrincipalIdeleData K D)
    (C : Chapter02PrincipalIdeleCharacterData A P S T)
    (a : chapter02FieldMultiplicativeGroup K) :
    chapter02GlobalArtinHom A (P.principal a) = 1 := by
  apply C.characters.separates
  intro χ hχ
  change χ (Finset.prod (chapter02GlobalArtinIndexSet A (P.principal a))
      (fun v => A.localArtin v ((P.principal a).1 v))) = 1
  rw [map_prod]
  calc
    Finset.prod (chapter02GlobalArtinIndexSet A (P.principal a))
        (fun v => χ (A.localArtin v ((P.principal a).1 v))) =
      Finset.prod (chapter02GlobalArtinIndexSet A (P.principal a))
        (fun v => C.evaluateInvariant χ
          (C.localInvariant χ hχ v ((P.principal a).1 v))) := by
          apply Finset.prod_congr rfl
          intro v hv
          exact (C.localInvariant_eq_artin χ hχ v ((P.principal a).1 v)).symm
    _ = C.evaluateInvariant χ
          (Finset.prod (chapter02GlobalArtinIndexSet A (P.principal a))
            (fun v => C.localInvariant χ hχ v ((P.principal a).1 v))) := by
      rw [map_prod]
    _ = C.evaluateInvariant χ 1 := by
      rw [C.principalInvariant_product χ hχ a]
    _ = 1 := (C.evaluateInvariant χ).map_one

theorem chapter02_principal_ideles_product_formula_as_finite_product
    {K : Type u} [Field K]
    {V : Type v} {H : V → Type w} [∀ x, CommGroup (H x)]
    {G : Type z} [CommGroup G] [Finite G]
    {S T : Type*} [CommGroup S] [CommGroup T]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G)
    (P : Chapter02PrincipalIdeleData K D)
    (C : Chapter02PrincipalIdeleCharacterData A P S T)
    (a : chapter02FieldMultiplicativeGroup K) :
    Finset.prod (chapter02GlobalArtinIndexSet A (P.principal a))
      (fun v => A.localArtin v ((P.principal a).1 v)) = 1 := by
  change chapter02GlobalArtinHom A (P.principal a) = 1
  exact chapter02_principal_ideles_product_formula A P C a

theorem chapter02_characters_separate_points
    {G A : Type*} [CommGroup G] [CommGroup A] [Finite G]
    (C : Chapter02CharacterSeparation G A) (g : G)
    (h : ∀ χ ∈ C.characters, χ g = 1) :
    g = 1 := by
  exact C.separates g h

/-- The local Artin map induced by a quotient of a finite abelian group. -/
theorem chapter02_abelian_local_artin_quotient_compatibility
    {B E D Q : Type*} [CommGroup B] [CommGroup E]
    [CommGroup D] [CommGroup Q]
    (q : D →* Q)
    (R : Chapter02LocalReciprocityData B E D)
    (R' : Chapter02LocalReciprocityData B E Q)
    (hR : R'.reciprocity =
      (Abelianization.map q).comp R.reciprocity) :
    chapter02LocalArtinMap R' = q.comp (chapter02LocalArtinMap R) := by
  have hcompat :
      (Abelianization.equivOfComm (H := Q)).symm.toMonoidHom.comp
          (Abelianization.map q) =
        q.comp (Abelianization.equivOfComm (H := D)).symm.toMonoidHom := by
    apply Abelianization.hom_ext
    ext d
    rfl
  rw [chapter02LocalArtinMap, chapter02LocalArtinMap, hR,
    ← MonoidHom.comp_assoc, hcompat, MonoidHom.comp_assoc]

/-- The principal map kills the quotient relation. -/
theorem chapter02_principal_subgroup_le_global_artin_kernel
    {K : Type u} [Field K]
    {V : Type v} {H : V → Type w} [∀ x, CommGroup (H x)]
    {G : Type z} [CommGroup G] [Finite G]
    {S T : Type*} [CommGroup S] [CommGroup T]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G)
    (P : Chapter02PrincipalIdeleData K D)
    (C : Chapter02PrincipalIdeleCharacterData A P S T) :
    chapter02PrincipalSubgroup P ≤ (chapter02GlobalArtinHom A).ker := by
  intro x hx
  rcases hx with ⟨a, rfl⟩
  exact chapter02_principal_ideles_product_formula A P C a

/-- The global Artin map descended to the idele class group. -/
noncomputable def chapter02GlobalArtinOnIdeleClasses
    {K : Type u} [Field K]
    {V : Type v} {H : V → Type w} [∀ x, CommGroup (H x)]
    {G : Type z} [CommGroup G] [Finite G]
    {S T : Type*} [CommGroup S] [CommGroup T]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G)
    (P : Chapter02PrincipalIdeleData K D)
    (C : Chapter02PrincipalIdeleCharacterData A P S T) :
    chapter02IdeleClassGroup P →* G :=
  QuotientGroup.lift (chapter02PrincipalSubgroup P)
    (chapter02GlobalArtinHom A)
    (chapter02_principal_subgroup_le_global_artin_kernel A P C)

@[simp]
theorem chapter02_global_artin_on_classes_mk
    {K : Type u} [Field K]
    {V : Type v} {H : V → Type w} [∀ x, CommGroup (H x)]
    {G : Type z} [CommGroup G] [Finite G]
    {S T : Type*} [CommGroup S] [CommGroup T]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G)
    (P : Chapter02PrincipalIdeleData K D)
    (C : Chapter02PrincipalIdeleCharacterData A P S T) (x : chapter02Ideles D) :
    chapter02GlobalArtinOnIdeleClasses A P C
        (chapter02IdeleClassProjection P x) =
      chapter02GlobalArtinHom A x := by
  simp [chapter02GlobalArtinOnIdeleClasses, chapter02IdeleClassProjection]

/-- The descended map is characterized by its pullback along the quotient. -/
theorem chapter02_global_artin_on_classes_unique
    {K : Type u} [Field K]
    {V : Type v} {H : V → Type w} [∀ x, CommGroup (H x)]
    {G : Type z} [CommGroup G] [Finite G]
    {S T : Type*} [CommGroup S] [CommGroup T]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G)
    (P : Chapter02PrincipalIdeleData K D)
    (C : Chapter02PrincipalIdeleCharacterData A P S T)
    {φ : chapter02IdeleClassGroup P →* G}
    (hφ : φ.comp (chapter02IdeleClassProjection P) =
      chapter02GlobalArtinHom A) :
    φ = chapter02GlobalArtinOnIdeleClasses A P C := by
  apply MonoidHom.ext
  intro x
  rcases QuotientGroup.mk'_surjective (chapter02PrincipalSubgroup P) x with ⟨y, rfl⟩
  calc
    φ (chapter02IdeleClassProjection P y) = chapter02GlobalArtinHom A y := by
      simpa using DFunLike.congr_fun hφ y
    _ = chapter02GlobalArtinOnIdeleClasses A P C
        (chapter02IdeleClassProjection P y) :=
      (chapter02_global_artin_on_classes_mk A P C y).symm

theorem chapter02_global_artin_factors_uniquely_through_idele_classes
    {K : Type u} [Field K]
    {V : Type v} {H : V → Type w} [∀ x, CommGroup (H x)]
    {G : Type z} [CommGroup G] [Finite G]
    {S T : Type*} [CommGroup S] [CommGroup T]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G)
    (P : Chapter02PrincipalIdeleData K D)
    (C : Chapter02PrincipalIdeleCharacterData A P S T) :
    ∃! φ : chapter02IdeleClassGroup P →* G,
      φ.comp (chapter02IdeleClassProjection P) =
        chapter02GlobalArtinHom A := by
  refine ⟨chapter02GlobalArtinOnIdeleClasses A P C, ?_, ?_⟩
  · ext x
    exact chapter02_global_artin_on_classes_mk A P C x
  · intro φ hφ
    exact chapter02_global_artin_on_classes_unique A P C hφ

/-
The ordinary absolute-value product formula is a different statement.  The
idele class factorization above uses the local norm-residue symbols and the
global Brauer invariant sum, not merely `∏ v |a|_v = 1`.
-/

end

end LastLib.Book06GlobalClassFieldTheory.Chapter02
