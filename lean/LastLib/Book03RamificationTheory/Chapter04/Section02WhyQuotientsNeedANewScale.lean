import LastLib.Book03RamificationTheory.Chapter04.Section01PassingToAnIntermediateBase
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.Section01TheLocalExtensionProblem

namespace LastLib.Book03RamificationTheory.Chapter04

noncomputable section

open scoped BigOperators Pointwise

/-! ## 4.2. Why quotients require a new scale -/

/- SOURCE_NOTE (4.2): The source uses the consistent formulation that the
   Herbrand clock slows, or compresses lower depth, when the ramification group
   becomes smaller; this agrees with the slope `|G_t| / |G_0|` in §4.4. -/

/-- The lower group obtained by the tempting, but generally invalid, naive
quotient operation.  It is retained as a named candidate so that later
statements can distinguish it from the normalized quotient filtration. -/
def chapter04NaiveQuotientLowerGroup
    {G : Type*} [Group G]
    (F : Chapter04LowerFiltration G) (H : Subgroup G) [H.Normal] (i : ℤ) :
    Subgroup (G ⧸ H) :=
  (chapter04LowerGroup F i).map (QuotientGroup.mk' H)

/-- The universal equality one would have to assert in order to identify the
downstairs lower groups with `Gᵢ H / H`.  The `Q` argument is the independently
normalized downstairs filtration; no such equality is built into the quotient
operation. -/
def chapter04NaiveQuotientLowerFormula
    {G : Type*} [Group G]
    (F : Chapter04LowerFiltration G) (H : Subgroup G) [H.Normal]
    (Q : Chapter04LowerFiltration (G ⧸ H)) : Prop :=
  ∀ i : ℤ,
    chapter04LowerGroup Q i = chapter04NaiveQuotientLowerGroup F H i

/-- Membership in the naive quotient group is existential over lifts.  This is
the group-theoretic part of the quotient warning: different lifts can merge. -/
theorem chapter04_naive_quotient_membership_iff
    {G : Type*} [Group G]
    (F : Chapter04LowerFiltration G) (H : Subgroup G) [H.Normal]
    (i : ℤ) (g : G) :
    QuotientGroup.mk' H g ∈ chapter04NaiveQuotientLowerGroup F H i ↔
      ∃ a : G, a ∈ chapter04LowerGroup F i ∧
        QuotientGroup.mk' H a = QuotientGroup.mk' H g := by
  rfl

/-- A mismatch witness proves that naive quotienting is not the normalized
downstairs lower filtration.  This is deliberately a conditional interface:
the actual mismatch comes from the rescaled normalized valuation in a tower. -/
theorem chapter04_naive_quotient_formula_fails_of_mismatch
    {G : Type*} [Group G]
    (F : Chapter04LowerFiltration G) (H : Subgroup G) [H.Normal]
    (Q : Chapter04LowerFiltration (G ⧸ H)) (i : ℤ)
    (hmismatch : chapter04LowerGroup Q i ≠
      chapter04NaiveQuotientLowerGroup F H i) :
    ¬ chapter04NaiveQuotientLowerFormula F H Q := by
  intro hformula
  exact hmismatch (hformula i)

/- SOURCE_WARNING: `chapter04NaiveQuotientLowerGroup` is only the displayed
   candidate `Gᵢ H / H`.  The source explicitly warns that it is generally
   false after normalized valuations are compared downstairs.  The comparison
   is recorded by the established Book 2 interface
   `chapter01ValuationRestrictionScale`; this file does not turn the candidate
   into an axiom or theorem. -/

/-- When `H` is normal, the fixed field is Galois over `K`, and Mathlib's
canonical quotient equivalence identifies its Galois group with `G / H`. -/
def chapter04_normal_fixed_field_quotient_galois_group
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L / K)) [H.Normal] :
    (Gal(L / K) ⧸ H) ≃* Gal(chapter04FixedField H / K) := by
  exact IsGalois.normalAutEquivQuotient H

/-- The normal subgroup condition is the exact field-theoretic condition used
by the quotient construction; without it, there is no canonical quotient
extension with group `G / H`. -/
theorem chapter04_quotient_extension_requires_normal_subgroup
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L / K))
    (hM : IsGalois K (chapter04FixedField H)) : H.Normal := by
  exact (chapter04_fixed_field_is_galois_over_base_iff_normal H).mp hM

end
end LastLib.Book03RamificationTheory.Chapter04
