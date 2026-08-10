import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12.Section01TheStructuralDictionary

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
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)] where
  middle : Type u
  [field_middle : Field middle]
  [algebra_K_middle : Algebra K middle]
  [algebra_middle_L : Algebra middle L]
  [tower_K_middle_L : IsScalarTower K middle L]
  vMiddle : Valuation middle Γ
  extension_K_middle : vK.IsEquiv (vMiddle.comap (algebraMap K middle))
  extension_middle_L : vMiddle.IsEquiv (vL.comap (algebraMap middle L))
  eKM : ℕ
  fKM : ℕ
  eML : ℕ
  fML : ℕ
  eKM_eq_one : eKM = 1
  fML_eq_one : fML = 1
  e_total : ℕ
  f_total : ℕ
  e_total_eq : e_total = eKM * eML
  f_total_eq : f_total = fKM * fML

/-- Book 2, §12.2: finite complete degree formulas do not require separability once defectlessness is supplied. -/
theorem complete_degree_formula_has_no_separability_hypothesis
    {K L Γ : Type*} [Field K] [Field L]
    [Algebra K L] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [Module.Finite K L]
    (hdefectless : Module.finrank K L =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
          vK.valuationSubring vL.valuationSubring
          (IsLocalRing.maximalIdeal vL.valuationSubring) *
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
          vK.valuationSubring vL.valuationSubring
          (IsLocalRing.maximalIdeal vL.valuationSubring))
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring) :
    Module.finrank K L =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
          vK.valuationSubring vL.valuationSubring
          (IsLocalRing.maximalIdeal vL.valuationSubring) *
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
          vK.valuationSubring vL.valuationSubring
          (IsLocalRing.maximalIdeal vL.valuationSubring) := by
  exact hdefectless

/-- Book 2, §12.2: in the separable case trace and norm have embedding formulas. -/
theorem separable_trace_and_norm_are_embedding_sum_and_product
    {K L E : Type*} [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] [IsAlgClosed E]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (x : L) :
    algebraMap K E (Algebra.trace K L x) =
        ∑ σ : L →ₐ[K] E, σ x ∧
      algebraMap K E (Algebra.norm K x) =
        ∏ σ : L →ₐ[K] E, σ x := by
  sorry

/-- Book 2, §12.2: trace nondegeneracy is a separable-extension statement. -/
theorem separable_trace_pairing_is_nondegenerate
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    tracePairingNondegenerate (K := K) (L := L) := by
  sorry

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
theorem separable_residue_extension_has_unramified_then_totally_ramified_factorization
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
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
    [Module.Finite k l] : Prop :=
  CompactSpace k ∧ IsCyclic kˣ ∧
    Function.Surjective (Algebra.norm k (S := l))

/-- Book 2, §12.2: a finite residue field has compactness, cyclic units, and surjective norms. -/
theorem finite_residue_field_has_the_listed_consequences
    (k l : Type*) [Field k] [Field l] [Fintype k] [Fintype l]
    [Algebra k l] [TopologicalSpace k] [DiscreteTopology k]
    [Module.Finite k l] :
    finiteResidueFieldConsequences k l := by
  sorry

/-- Book 2, §12.2: perfection supplies separability of finite algebraic residue extensions. -/
theorem perfect_residue_field_gives_separable_finite_extension
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [Module.Finite k l] [PerfectField k] :
    Algebra.IsSeparable k l := by
  infer_instance

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12
