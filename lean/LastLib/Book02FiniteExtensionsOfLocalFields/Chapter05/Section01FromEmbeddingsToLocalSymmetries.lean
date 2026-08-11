import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05

noncomputable section

open scoped BigOperators

/-! ## 5.1. From embeddings to local symmetries -/

/-
The first section uses Mathlib's `IsGalois`, `Algebra.IsSeparable`, `Normal`,
and `Gal` interfaces directly.  In particular, the fixed field of a subgroup
is represented by `IntermediateField.fixedField`; its bottom field is the
embedded copy of the base field.
-/

/-- The exact valuation-preservation assertion used for a normalized local valuation. -/
def chapter05ValuationPreserving
    {L Γ : Type*} [Ring L] [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation L Γ) (σ : L ≃+* L) : Prop :=
  ∀ x : L, w (σ x) = w x

/--
 A uniqueness predicate for an exactly normalized valuation in a fixed value
 group.  Book 1 also records uniqueness up to Mathlib's valuation equivalence;
 this stronger form is what is needed for the displayed equality
 `v_L (σ x) = v_L x`.
 -/
def chapter05UniqueNormalizedValuationExtension
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (w : Valuation L Γ) : Prop :=
  v.IsEquiv (w.comap (algebraMap K L)) ∧
    ∀ w' : Valuation L Γ,
      v.IsEquiv (w'.comap (algebraMap K L)) → w' = w

/-
The Henselian uniqueness theorem is naturally stated up to valuation
equivalence.  The normalized predicate above is intentionally stronger: it
is the interface needed for literal value equalities in this chapter.
-/
def chapter05UniqueValuationExtension
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (w : Valuation L Γ) : Prop :=
  v.IsEquiv (w.comap (algebraMap K L)) ∧
    ∀ w' : Valuation L Γ,
      v.IsEquiv (w'.comap (algebraMap K L)) → w'.IsEquiv w

/-- A finite extension has no more embeddings into an algebraic closure than its degree. -/
theorem finite_extension_embeddings_at_most_degree
    {K L Ω : Type*} [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [FiniteDimensional K L]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K L] :
    Nat.card (L →ₐ[K] Ω) ≤ Module.finrank K L := by
  sorry

/-- Equality in the embedding bound is equivalent to separability. -/
theorem finite_extension_embeddings_eq_degree_iff_separable
    {K L Ω : Type*} [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [FiniteDimensional K L]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K L] :
    Nat.card (L →ₐ[K] Ω) = Module.finrank K L ↔ Algebra.IsSeparable K L := by
  sorry

/-- The order of a finite Galois group is the field degree. -/
theorem finite_galois_group_order_eq_degree
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    Nat.card Gal(L / K) = Module.finrank K L := by
  sorry

/-- The fixed field of the whole finite Galois group is the base field. -/
theorem finite_galois_fixed_field_is_base
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    IntermediateField.fixedField (⊤ : Subgroup Gal(L / K)) = ⊥ := by
  sorry

/-- Galois means separable and normal, with the two roles exposed separately. -/
theorem galois_separable_and_normal
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    Algebra.IsSeparable K L ∧ Normal K L := by
  sorry

/-- Normality makes every self-embedding over the base an automorphism. -/
theorem normal_extension_self_embeddings_are_bijective
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Normal K L]
    (σ : L →ₐ[K] L) : Function.Bijective σ := by
  sorry

/-- A purely inseparable finite Galois extension is trivial. -/
theorem purely_inseparable_galois_extension_is_trivial
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsPurelyInseparable K L] [IsGalois K L] :
    Module.finrank K L = 1 := by
  sorry

/-- In the foundational convention, unramified includes separable residue extension. -/
theorem unramified_condition_implies_residue_separable
    (e : ℕ) (residueSeparable : Prop)
    (h : e = 1 ∧ residueSeparable) :
    residueSeparable := by
  sorry

/-- An equality `e = 1` alone does not imply unramifiedness. -/
theorem ramification_index_one_without_separable_residue_is_not_unramified
    (residueSeparable : Prop) (hnot : ¬residueSeparable) :
    ¬(1 = 1 ∧ residueSeparable) := by
  sorry

/-- Unique normalized extension forces every base-field automorphism to preserve `w`. -/
theorem galois_automorphism_preserves_unique_valuation
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (w : Valuation L Γ)
    (hext : v.IsEquiv (w.comap (algebraMap K L)))
    (hunique : chapter05UniqueNormalizedValuationExtension v w)
    (σ : Gal(L / K)) :
    chapter05ValuationPreserving w σ.toRingEquiv := by
  sorry

/-- The valuation-ring form of valuation preservation. -/
theorem valuation_preservation_preserves_valuation_ring
    {L Γ : Type*} [Field L] [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation L Γ) (σ : L ≃+* L)
    (hσ : chapter05ValuationPreserving w σ) :
    ∀ x : L, x ∈ w.valuationSubring ↔ σ x ∈ w.valuationSubring := by
  sorry

/-- Automorphisms preserving a unique valuation preserve the full local bounded ring. -/
theorem unique_local_valuation_gives_integral_symmetries
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (w : Valuation L Γ)
    (hext : v.IsEquiv (w.comap (algebraMap K L)))
    (hunique : chapter05UniqueNormalizedValuationExtension v w) :
    ∀ σ : Gal(L / K),
      ∀ x : L, x ∈ w.valuationSubring ↔ σ x ∈ w.valuationSubring := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05
