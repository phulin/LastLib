import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.Section02DecompositionGroups
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Valuation.Discrete.RankOne

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05

noncomputable section

open scoped BigOperators

/-! ## 5.3. The residue action and inertia -/

/-- The residue field attached to a valuation subring. -/
abbrev chapter05ResidueField {E : Type*} [Field E] (A : ValuationSubring E) : Type _ :=
  IsLocalRing.ResidueField A

/-- The action of the decomposition group on the valuation ring. -/
noncomputable def chapter05ValuationRingAction
    (F : Type*) {E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) :
    chapter05DecompositionGroup F A →* RingAut A :=
  MulSemiringAction.toRingAut _ _

/-- The induced action on the residue field. -/
noncomputable def chapter05ResidueAction
    (F : Type*) {E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) :
    chapter05DecompositionGroup F A →* RingAut (IsLocalRing.ResidueField A) :=
  MulSemiringAction.toRingAut _ _

/-- Mathlib's inertia subgroup, exposed at the chapter namespace. -/
abbrev chapter05InertiaGroup
    (F : Type*) {E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) :
    Subgroup (chapter05DecompositionGroup F A) :=
  ValuationSubring.inertiaSubgroup F A

/-- The inertia subgroup embedded in the ambient Galois group. -/
def chapter05InertiaGroupInG
    (F : Type*) {E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) : Subgroup (Gal(E / F)) :=
  (chapter05InertiaGroup F A).map (Subgroup.subtype _)

/-- Automorphisms of a residue extension that fix the base residue field. -/
def chapter05ResidueAutomorphismsOver
    (k l : Type*) [CommRing k] [CommRing l] [Algebra k l] :
    Subgroup (RingAut l) := by
  classical
  refine
    { carrier := {φ | ∀ x : k, φ (algebraMap k l x) = algebraMap k l x}
      one_mem' := ?_
      mul_mem' := ?_
      inv_mem' := ?_ }
  · intro φ ψ hφ hψ x
    change φ (ψ (algebraMap k l x)) = algebraMap k l x
    rw [hψ x, hφ x]
  · intro x
    rfl
  · intro φ hφ x
    apply φ.injective
    simpa using (hφ x).symm

/-- The residue automorphism target agrees with the Galois group in the finite Galois case. -/
theorem residue_automorphisms_over_base_is_galois_group
    {k l : Type*} [Field k] [Field l] [Algebra k l] :
    Nonempty
      (chapter05ResidueAutomorphismsOver k l ≃* Gal(l / k)) := by
  sorry

/-- Restriction of a residue action to automorphisms over the base. -/
def chapter05ResidueActionOverBase
    (F : Type*) {E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) (k : Type*) [CommRing k]
    [Algebra k (IsLocalRing.ResidueField A)]
    (hbase : ∀ σ : chapter05DecompositionGroup F A, ∀ x : k,
      chapter05ResidueAction F A σ (algebraMap k (IsLocalRing.ResidueField A) x) =
        algebraMap k (IsLocalRing.ResidueField A) x) :
    chapter05DecompositionGroup F A →*
      chapter05ResidueAutomorphismsOver k (IsLocalRing.ResidueField A) :=
  (chapter05ResidueAction F A).codRestrict _ (fun σ => hbase σ)

/-- The Mathlib inertia subgroup is exactly the kernel of residue reduction. -/
theorem inertia_group_is_residue_action_kernel
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) :
    chapter05InertiaGroup F A = MonoidHom.ker (chapter05ResidueAction F A) := by
  sorry

/-- Kernel membership is invisibility on every residue class. -/
theorem inertia_mem_iff_residue_fixed
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) (σ : chapter05DecompositionGroup F A) :
    σ ∈ chapter05InertiaGroup F A ↔
      ∀ x : IsLocalRing.ResidueField A,
        chapter05ResidueAction F A σ x = x := by
  sorry

/-- Reduction commutes with the residue action. -/
theorem residue_action_commutes_with_reduction
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) (σ : chapter05DecompositionGroup F A) (x : A) :
    IsLocalRing.residue A (σ • x) =
      chapter05ResidueAction F A σ (IsLocalRing.residue A x) := by
  sorry

/-- The first congruence condition is the elementary description of inertia. -/
theorem inertia_iff_positive_valuation_displacement
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    (w : AddValuation L (WithTop ℤ))
    (σ : chapter05DecompositionGroup F w.toValuation.valuationSubring) :
    σ ∈ chapter05InertiaGroup F w.toValuation.valuationSubring ↔
      ∀ x : w.toValuation.valuationSubring,
        w ((σ : Gal(L / F)) (x : L) - (x : L)) > 0 := by
  sorry

/- SOURCE_ISSUE: The surjectivity argument in §5.3 invokes Hensel's lemma
   after the chapter has introduced a possibly noncomplete global extension.
   It requires the chosen base valuation to be henselian (for example, after
   passing to the completion); the explicit completeness and normalization
   hypotheses of the theorem below record that missing local context. -/
/-- The exactness assertion for a residue action whose kernel is inertia. -/
theorem residue_action_exact_sequence
    {D Q : Type*} [Group D] [Group Q]
    (ρ : D →* Q) (hρ : Function.Surjective ρ) :
    Function.MulExact (Subgroup.subtype (MonoidHom.ker ρ)) ρ ∧
      Function.Surjective ρ := by
  sorry

/--
 In the complete local Galois situation, separability of the residue
 extension is the hypothesis used by Hensel lifting to make the residue action
 surjective.
 -/
theorem residue_action_surjective_when_residue_separable
    {F E Γ : Type*} [Field F] [Field E] [Algebra F E]
    [LinearOrderedCommGroupWithZero Γ] [FiniteDimensional F E] [IsGalois F E]
    (v : Valuation F Γ) [Valuation.IsRankOneDiscrete v]
    (w : Valuation E Γ) [Valuation.IsRankOneDiscrete w]
    (hext : v.IsEquiv (w.comap (algebraMap F E)))
    (hcomplete :
      IsAdicComplete (IsLocalRing.maximalIdeal v.valuationSubring)
        v.valuationSubring)
    (hunique : chapter05UniqueNormalizedValuationExtension v w)
    [Algebra (IsLocalRing.ResidueField v.valuationSubring)
      (IsLocalRing.ResidueField w.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField v.valuationSubring)
      (IsLocalRing.ResidueField w.valuationSubring)]
    [Normal (IsLocalRing.ResidueField v.valuationSubring)
      (IsLocalRing.ResidueField w.valuationSubring)]
    (hbase : ∀ σ : chapter05DecompositionGroup F w.valuationSubring, ∀ x :
      IsLocalRing.ResidueField v.valuationSubring,
      chapter05ResidueAction F w.valuationSubring σ
          (algebraMap (IsLocalRing.ResidueField v.valuationSubring)
            (IsLocalRing.ResidueField w.valuationSubring) x) =
        algebraMap (IsLocalRing.ResidueField v.valuationSubring)
          (IsLocalRing.ResidueField w.valuationSubring) x)
    (hseparable : Algebra.IsSeparable (IsLocalRing.ResidueField v.valuationSubring)
      (IsLocalRing.ResidueField w.valuationSubring)) :
    Function.Surjective
      (chapter05ResidueActionOverBase F w.valuationSubring
        (IsLocalRing.ResidueField v.valuationSubring) hbase) := by
  sorry

/-- Finite exact residue sequences account for the group order as `|I| · |Q|`. -/
theorem residue_exact_sequence_cardinality
    {D Q : Type*} [Group D] [Group Q] [Finite D] [Finite Q]
    (ρ : D →* Q) (hρ : Function.Surjective ρ) :
    Nat.card D = Nat.card (MonoidHom.ker ρ) * Nat.card Q := by
  sorry

/-- The residue quotient cannot recover the full residue degree in an inseparable case. -/
theorem inseparable_residue_automorphism_group_is_strictly_smaller
    {k l : Type*} [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] (hinsep : ¬Algebra.IsSeparable k l) :
    Nat.card (Gal(l / k)) < Module.finrank k l := by
  sorry

/-- Perfect residue fields make every finite residue extension separable. -/
theorem perfect_residue_field_has_separable_finite_extensions
    {k l : Type*} [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] [PerfectField k] :
    Algebra.IsSeparable k l := by
  sorry

/-- A finite residue field is perfect, so it has no inseparability obstruction. -/
theorem finite_residue_field_is_perfect
    (k : Type*) [Field k] [Finite k] : PerfectField k := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05
