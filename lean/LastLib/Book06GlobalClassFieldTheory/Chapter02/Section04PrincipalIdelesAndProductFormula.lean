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

/- DEPENDENCY_GUESS: the missing Book 4/Book 5 Brauer--idele interface supplies
   the cyclic-algebra localization and invariant-sum argument used by this
   theorem.  The chapter-facing `A` and `P` structures are the provisional
   realization interface; reconciliation must connect them to one finite
   abelian extension `L/K` and its completion maps. -/

/-- Product formula for local Artin symbols on a principal idele. -/
theorem chapter02_principal_ideles_product_formula
    {K : Type u} [Field K]
    {V : Type v} {H : V → Type w} [∀ x, CommGroup (H x)]
    {G : Type z} [CommGroup G] [Finite G]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G)
    (P : Chapter02PrincipalIdeleData K D)
    (a : chapter02FieldMultiplicativeGroup K) :
    chapter02GlobalArtinHom A (P.principal a) = 1 := by
  sorry

theorem chapter02_principal_ideles_product_formula_as_finite_product
    {K : Type u} [Field K]
    {V : Type v} {H : V → Type w} [∀ x, CommGroup (H x)]
    {G : Type z} [CommGroup G] [Finite G]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G)
    (P : Chapter02PrincipalIdeleData K D)
    (a : chapter02FieldMultiplicativeGroup K) :
    Finset.prod (chapter02GlobalArtinIndexSet A (P.principal a))
      (fun v => A.localArtin v ((P.principal a).1 v)) = 1 := by
  sorry

/-- A generic finite-abelian character family that separates points. -/
structure Chapter02CharacterSeparation
    (G A : Type*) [CommGroup G] [CommGroup A] [Finite G] where
  characters : Set (G →* A)
  separates : ∀ g : G, (∀ χ ∈ characters, χ g = 1) → g = 1

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
  sorry

/-- The principal map kills the quotient relation. -/
theorem chapter02_principal_subgroup_le_global_artin_kernel
    {K : Type u} [Field K]
    {V : Type v} {H : V → Type w} [∀ x, CommGroup (H x)]
    {G : Type z} [CommGroup G] [Finite G]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G)
    (P : Chapter02PrincipalIdeleData K D) :
    chapter02PrincipalSubgroup P ≤ (chapter02GlobalArtinHom A).ker := by
  intro x hx
  rcases hx with ⟨a, rfl⟩
  exact chapter02_principal_ideles_product_formula A P a

/-- The global Artin map descended to the idele class group. -/
noncomputable def chapter02GlobalArtinOnIdeleClasses
    {K : Type u} [Field K]
    {V : Type v} {H : V → Type w} [∀ x, CommGroup (H x)]
    {G : Type z} [CommGroup G] [Finite G]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G)
    (P : Chapter02PrincipalIdeleData K D) :
    chapter02IdeleClassGroup P →* G :=
  QuotientGroup.lift (chapter02PrincipalSubgroup P)
    (chapter02GlobalArtinHom A)
    (chapter02_principal_subgroup_le_global_artin_kernel A P)

@[simp]
theorem chapter02_global_artin_on_classes_mk
    {K : Type u} [Field K]
    {V : Type v} {H : V → Type w} [∀ x, CommGroup (H x)]
    {G : Type z} [CommGroup G] [Finite G]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G)
    (P : Chapter02PrincipalIdeleData K D) (x : chapter02Ideles D) :
    chapter02GlobalArtinOnIdeleClasses A P
        (chapter02IdeleClassProjection P x) =
      chapter02GlobalArtinHom A x := by
  sorry

/-- The descended map is characterized by its pullback along the quotient. -/
theorem chapter02_global_artin_on_classes_unique
    {K : Type u} [Field K]
    {V : Type v} {H : V → Type w} [∀ x, CommGroup (H x)]
    {G : Type z} [CommGroup G] [Finite G]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G)
    (P : Chapter02PrincipalIdeleData K D)
    {φ : chapter02IdeleClassGroup P →* G}
    (hφ : φ.comp (chapter02IdeleClassProjection P) =
      chapter02GlobalArtinHom A) :
    φ = chapter02GlobalArtinOnIdeleClasses A P := by
  sorry

theorem chapter02_global_artin_factors_uniquely_through_idele_classes
    {K : Type u} [Field K]
    {V : Type v} {H : V → Type w} [∀ x, CommGroup (H x)]
    {G : Type z} [CommGroup G] [Finite G]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G)
    (P : Chapter02PrincipalIdeleData K D) :
    ∃! φ : chapter02IdeleClassGroup P →* G,
      φ.comp (chapter02IdeleClassProjection P) =
        chapter02GlobalArtinHom A := by
  refine ⟨chapter02GlobalArtinOnIdeleClasses A P, ?_, ?_⟩
  · ext x
    sorry
  · intro φ hφ
    exact chapter02_global_artin_on_classes_unique A P hφ

/-
The ordinary absolute-value product formula is a different statement.  The
idele class factorization above uses the local norm-residue symbols and the
global Brauer invariant sum, not merely `∏ v |a|_v = 1`.
-/

end

end LastLib.Book06GlobalClassFieldTheory.Chapter02
