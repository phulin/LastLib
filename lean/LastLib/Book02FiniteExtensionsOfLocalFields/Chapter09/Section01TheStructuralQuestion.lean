import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09

open scoped BigOperators Polynomial
open Ideal IsLocalRing Polynomial

noncomputable section

universe u v

/-! # Book 2, Chapter 9.1: the structural question

The chapter works with finite extensions of complete discretely valued fields.
The ring-level data below makes the valuation rings and their residue fields
explicit.  In particular, `e` is Mathlib's ramification index and `f` is the
finite-dimensional degree of the induced residue-field extension.
-/

/-- A finite local extension package used throughout Chapter 9.

The DVRs `A` and `B` are the valuation rings in `K` and `L`; the explicit
completeness fields record the henselian hypothesis used by residue lifting. -/
class Chapter09FiniteLocalExtension
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsDomain B] [IsLocalRing A] [IsLocalRing B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsLocalHom (algebraMap A B)] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Module.Finite A B] [Module.IsTorsionFree A B]
    [FaithfulSMul A B] [IsIntegralClosure B A L]
    [Module.Finite (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField B)] : Prop where
  base_complete : IsAdicComplete (IsLocalRing.maximalIdeal A) A
  extension_complete : IsAdicComplete (IsLocalRing.maximalIdeal B) B

/-- The canonical residue fields of the two valuation rings. -/
abbrev chapter09BaseResidueField (A : Type*) [CommRing A] [IsLocalRing A] : Type _ :=
  IsLocalRing.ResidueField A

abbrev chapter09ExtensionResidueField (B : Type*) [CommRing B] [IsLocalRing B] : Type _ :=
  IsLocalRing.ResidueField B

/-- Unramified means ramification index one and separable residue extension. -/
def chapter09Unramified
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [IsDomain A] [IsDomain B] [IsLocalRing A] [IsLocalRing B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsLocalHom (algebraMap A B)]
    [Module.Finite (chapter09BaseResidueField A)
      (chapter09ExtensionResidueField B)] : Prop :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.foundationalUnramified
    (LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex A B
      (IsLocalRing.maximalIdeal B))
    (Algebra.IsSeparable (chapter09BaseResidueField A)
      (chapter09ExtensionResidueField B))

/-- Totally ramified means that the residue degree is one. -/
def chapter09TotallyRamified
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)]
    [Module.Finite (chapter09BaseResidueField A)
      (chapter09ExtensionResidueField B)] : Prop :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.foundationalTotallyRamified
    (LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree A B
      (IsLocalRing.maximalIdeal B))

/-- The separable part of a finite residue extension, using Mathlib's canonical
separable closure rather than redeclaring a subfield. -/
noncomputable def chapter09MaximalSeparableResidueSubfield
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [Algebra.IsAlgebraic k l] : IntermediateField k l :=
  separableClosure k l

/-- The intrinsic condition characterizing the maximal separable residue part. -/
def chapter09SeparablePartProperty
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    (s : IntermediateField k l) : Prop :=
  Algebra.IsSeparable k s ∧ IsPurelyInseparable s l

/-- The residue extension decomposes into a separable part followed by a purely
inseparable part. -/
theorem chapter09_separable_residue_part_properties
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [Algebra.IsAlgebraic k l] :
    chapter09SeparablePartProperty k l
      (chapter09MaximalSeparableResidueSubfield k l) := by
  change Algebra.IsSeparable k (separableClosure k l) ∧
    IsPurelyInseparable (separableClosure k l) l
  exact ⟨inferInstance, inferInstance⟩

/-- The separable part is the unique intermediate field with separable base
extension and purely inseparable remainder. -/
theorem chapter09_separable_residue_part_unique
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [Algebra.IsAlgebraic k l] :
    ∃! s : IntermediateField k l, chapter09SeparablePartProperty k l s := by
  let s₀ := chapter09MaximalSeparableResidueSubfield k l
  have hs₀ : chapter09SeparablePartProperty k l s₀ :=
    chapter09_separable_residue_part_properties k l
  refine ⟨s₀, hs₀, ?_⟩
  intro s hs
  rcases hs with ⟨hs_sep, hs_pure⟩
  letI : Algebra.IsSeparable k s := hs_sep
  letI : IsPurelyInseparable s l := hs_pure
  apply le_antisymm
  · simpa [s₀, chapter09MaximalSeparableResidueSubfield] using
      le_separableClosure k l s
  · intro x hx
    have hx' : x ∈ separableClosure k l := by
      simpa [s₀, chapter09MaximalSeparableResidueSubfield] using hx
    have hx_sep : IsSeparable s x :=
      IsSeparable.tower_top s (mem_separableClosure_iff.mp hx')
    letI : Algebra.IsSeparable s
        (IntermediateField.adjoin s ({x} : Set l)) := by
      exact (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable s l).2 hx_sep
    obtain ⟨y, hy⟩ :=
      IsPurelyInseparable.surjective_algebraMap_of_isSeparable s
        (IntermediateField.adjoin s ({x} : Set l))
        ⟨x, IntermediateField.mem_adjoin_simple_self s x⟩
    have hxy : (y : l) = x := by
      simpa using congrArg
        (fun z : IntermediateField.adjoin s ({x} : Set l) => (z : l)) hy
    rw [← hxy]
    exact y.property

/-- The maximal separable part is all of the residue field exactly when the
residue extension is separable. -/
theorem chapter09_separable_residue_part_eq_top_iff
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [Algebra.IsAlgebraic k l] :
    (chapter09MaximalSeparableResidueSubfield k l = ⊤) ↔
      Algebra.IsSeparable k l := by
  simpa [chapter09MaximalSeparableResidueSubfield] using
    (separableClosure.eq_top_iff k l)

/-- A perfect residue field makes every algebraic residue extension separable. -/
theorem chapter09_perfect_residue_field_gives_separable_extension
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [Algebra.IsAlgebraic k l] [PerfectField k] :
    Algebra.IsSeparable k l := by
  infer_instance

/-- The degree formula separates value-group growth from residue-field growth. -/
-- SOURCE_ISSUE: The source's unrestricted degree formula is false for finite
-- defect extensions over imperfect residue fields.  The minimal correction
-- here is to assume a perfect base residue field (an explicit defectless
-- hypothesis would also suffice).
theorem chapter09_local_degree_formula
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsDomain B] [IsLocalRing A] [IsLocalRing B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsLocalHom (algebraMap A B)] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Module.Finite A B] [Module.IsTorsionFree A B]
    [FaithfulSMul A B] [IsIntegralClosure B A L]
    [Module.Finite (chapter09BaseResidueField A)
      (chapter09ExtensionResidueField B)]
    [PerfectField (chapter09BaseResidueField A)]
    [Chapter09FiniteLocalExtension A B K L] :
    Module.finrank K L =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex A B
          (IsLocalRing.maximalIdeal B) *
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree A B
          (IsLocalRing.maximalIdeal B) := by
  letI : IsDedekindDomain A :=
    ((IsDiscreteValuationRing.TFAE A (IsDiscreteValuationRing.not_isField A)).out 0 2).mp
      (inferInstance : IsDiscreteValuationRing A)
  letI : IsDedekindDomain B :=
    ((IsDiscreteValuationRing.TFAE B (IsDiscreteValuationRing.not_isField B)).out 0 2).mp
      (inferInstance : IsDiscreteValuationRing B)
  have hprimes :
      Ideal.primesOver (IsLocalRing.maximalIdeal A) B =
        {IsLocalRing.maximalIdeal B} :=
    IsLocalRing.primesOver_eq (R := A) (A := B)
      (p := IsLocalRing.maximalIdeal A)
      (IsDiscreteValuationRing.maximalIdeal A).ne_bot
  have hmem :
      (IsLocalRing.maximalIdeal B : Ideal B) ∈
        Ideal.primesOver (IsLocalRing.maximalIdeal A) B := by
    rw [hprimes]
    simp
  let q₀ : Ideal.primesOver (IsLocalRing.maximalIdeal A) B :=
    ⟨IsLocalRing.maximalIdeal B, hmem⟩
  letI : Unique (Ideal.primesOver (IsLocalRing.maximalIdeal A) B) :=
    { default := q₀
      uniq := by
        intro q
        have hq : q.1 = (IsLocalRing.maximalIdeal B : Ideal B) := by
          have hq' : q.1 ∈
              ({(IsLocalRing.maximalIdeal B : Ideal B)} : Set (Ideal B)) :=
            by simpa only [hprimes] using q.2
          exact Set.mem_singleton_iff.mp hq'
        exact Subtype.ext hq }
  have hsum :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.final_sum_ramification_times_residue_degree
      (R := A) (S := B) (IsLocalRing.maximalIdeal A : Ideal A)
  have hsum' :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex A B
          (IsLocalRing.maximalIdeal B) *
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree A B
          (IsLocalRing.maximalIdeal B) = Module.finrank A B := by
    rw [Fintype.sum_unique] at hsum
    have hdefault :
        (default : Ideal.primesOver (IsLocalRing.maximalIdeal A) B) = q₀ :=
      (Unique.eq_default q₀).symm
    rw [hdefault] at hsum
    simpa [q₀,
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex,
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree] using hsum
  calc
    Module.finrank K L = Module.finrank A B :=
      IsFractionRing.finrank_eq A K B L
    _ = LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex A B
          (IsLocalRing.maximalIdeal B) *
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree A B
          (IsLocalRing.maximalIdeal B) := hsum'.symm


end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09
