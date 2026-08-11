import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12.Section01TheStructuralDictionary
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12

noncomputable section

open scoped BigOperators

universe u

/-! ## 12.2. The separability map -/

/-- The trace pairing whose nondegeneracy is at issue in the separable case. -/
def tracePairingNondegenerate
    {K L : Type*} [Field K] [Field L] [Algebra K L] : Prop :=
  (Algebra.traceForm K L).Nondegenerate

/--
The interface for the factorization into an unramified part followed by a
totally ramified part.  The middle field and both valuation extensions are
part of the data; the degree labels record the two multiplicative factors.
-/
structure Chapter12UnramifiedTotallyRamifiedFactorization
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)] where
  middle : Type u
  [field_middle : Field middle]
  [algebra_K_middle : Algebra K middle]
  [algebra_middle_L : Algebra middle L]
  [tower_K_middle_L : IsScalarTower K middle L]
  vMiddle : Valuation middle Γ
  [extension_K_middle : vK.HasExtension vMiddle]
  [extension_middle_L : vMiddle.HasExtension vL]
  [middle_rank_one_discrete : Valuation.IsRankOneDiscrete vMiddle]
  [finiteDimensional_K_middle : FiniteDimensional K middle]
  [finiteDimensional_middle_L : FiniteDimensional middle L]
  [residueAlgebra_K_middle :
    Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vMiddle.valuationSubring)]
  [residueFinite_K_middle :
    FiniteDimensional (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vMiddle.valuationSubring)]
  [residueAlgebra_middle_L :
    Algebra (IsLocalRing.ResidueField vMiddle.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
  [residueFinite_middle_L :
    FiniteDimensional (IsLocalRing.ResidueField vMiddle.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
  [residueTower :
    IsScalarTower (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vMiddle.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
  [residueSeparable_K_middle :
    Algebra.IsSeparable (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vMiddle.valuationSubring)]
  eKM : ℕ
  fKM : ℕ
  eML : ℕ
  fML : ℕ
  eKM_eq_ramification_index :
    eKM = LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
      vK.valuationSubring vMiddle.valuationSubring
        (IsLocalRing.maximalIdeal vMiddle.valuationSubring)
  fKM_eq_residue_degree :
    fKM = LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
      vK.valuationSubring vMiddle.valuationSubring
        (IsLocalRing.maximalIdeal vMiddle.valuationSubring)
  eML_eq_ramification_index :
    eML = LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
      vMiddle.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring)
  fML_eq_residue_degree :
    fML = LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
      vMiddle.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring)
  eKM_eq_one : eKM = 1
  fML_eq_one : fML = 1

/-- Book 2, §12.2: finite complete degree formulas do not require separability
once a perfect residue field supplies defectlessness. -/
-- SOURCE_ISSUE: §12.2 repeats the false unconditional equality `[L : K] = e f`; the corrected interface assumes a perfect base residue field and completeness, which imply defectlessness without adding separability.
theorem complete_degree_formula_has_no_separability_hypothesis
    {K L Γ : Type*} [Field K] [Field L]
    [Algebra K L] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [Module.Finite K L]
    [PerfectField (IsLocalRing.ResidueField vK.valuationSubring)]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    :
    Module.finrank K L =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
          vK.valuationSubring vL.valuationSubring
          (IsLocalRing.maximalIdeal vL.valuationSubring) *
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
          vK.valuationSubring vL.valuationSubring
          (IsLocalRing.maximalIdeal vL.valuationSubring) := by
  exact complete_extension_degree_is_ramification_times_residue_degree
    vK vL
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
        vK.valuationSubring vL.valuationSubring
          (IsLocalRing.maximalIdeal vL.valuationSubring))
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
        vK.valuationSubring vL.valuationSubring
          (IsLocalRing.maximalIdeal vL.valuationSubring))
      hcomplete rfl rfl

/-- Book 2, §12.2: in the separable case trace and norm have embedding formulas. -/
theorem separable_trace_and_norm_are_embedding_sum_and_product
    {K L E : Type*} [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] [Algebra L E]
    [IsScalarTower K L E] [IsAlgClosed E] [Normal K E]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (x : L) :
    algebraMap K E (Algebra.trace K L x) =
      ∑ σ : L →ₐ[K] E, σ x ∧
      algebraMap K E (Algebra.norm K x) =
        ∏ σ : L →ₐ[K] E, σ x := by
  exact ⟨trace_eq_sum_embeddings E, Algebra.norm_eq_prod_embeddings E x⟩

/-- Book 2, §12.2: trace nondegeneracy is a separable-extension statement. -/
theorem separable_trace_pairing_is_nondegenerate
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    tracePairingNondegenerate (K := K) (L := L) := by
  simpa [tracePairingNondegenerate] using (traceForm_nondegenerate K L)

/-- Book 2, §12.2: Galois means both normal and separable, and then the group has degree order. -/
theorem finite_galois_is_normal_separable_and_has_degree_order
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    Algebra.IsSeparable K L ∧ Normal K L ∧
      Nat.card Gal(L / K) = Module.finrank K L := by
  exact ⟨inferInstance, inferInstance, IsGalois.card_aut_eq_finrank K L⟩

/-- Book 2, §12.2: the foundational unramified condition includes residue separability. -/
theorem unramified_requires_unit_ramification_and_residue_separability
    (e : ℕ) (residueSeparable : Prop) :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.foundationalUnramified e residueSeparable ↔
      e = 1 ∧ residueSeparable := by
  rfl

/-- Book 2, §12.2: total ramification is the endpoint `f = 1`. -/
theorem totally_ramified_requires_unit_residue_degree
    (f : ℕ) :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.foundationalTotallyRamified f ↔ f = 1 := by
  rfl

/-- Book 2, §12.2: a separable residue extension admits the two-stage factorization interface. -/
-- DEPENDENCY_GUESS: The preceding chapters prove the factorization in a
-- valuation-ring presentation; this generic valuation-level package is the
-- local interface needed here and its construction is intentionally left
-- open for a later proof.
theorem separable_residue_extension_has_unramified_then_totally_ramified_factorization
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Module.Finite K L] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    [Module.Finite (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)] :
    Nonempty (Chapter12UnramifiedTotallyRamifiedFactorization vK vL) := by
  sorry

/-- Book 2, §12.2: finiteness of the residue field implies perfection. -/
theorem finite_residue_field_is_perfect
    (k : Type*) [Field k] [Fintype k] : PerfectField k := by
  infer_instance

/-- The finite-residue-field consequences listed in Book 2, §12.2. -/
def finiteResidueFieldConsequences
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [TopologicalSpace k] [DiscreteTopology k]
    [TopologicalSpace l] [DiscreteTopology l]
    [Module.Finite k l] : Prop :=
  CompactSpace k ∧ CompactSpace l ∧ IsCyclic kˣ ∧ IsCyclic lˣ ∧
    Function.Surjective (Algebra.norm k (S := l))

/-- Book 2, §12.2: a finite residue field has compactness, cyclic units, and surjective norms. -/
theorem finite_residue_field_has_the_listed_consequences
    (k l : Type*) [Field k] [Field l] [Fintype k] [Fintype l]
    [Algebra k l] [TopologicalSpace k] [DiscreteTopology k]
    [TopologicalSpace l] [DiscreteTopology l]
    [Module.Finite k l] :
    finiteResidueFieldConsequences k l := by
  letI : Finite k := Fintype.finite k
  letI : Finite l := Fintype.finite l
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    FiniteField.norm_surjective k l⟩

/-- Book 2, §12.2: perfection supplies separability of finite algebraic residue extensions. -/
theorem perfect_residue_field_gives_separable_finite_extension
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [Module.Finite k l] [PerfectField k] :
    Algebra.IsSeparable k l := by
  infer_instance

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12
