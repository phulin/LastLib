import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter13.Dependencies
import Mathlib.NumberTheory.Padics.PadicNumbers

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter13

noncomputable section

open scoped Topology WithZero

/-! ## 13.1. The finiteness question and its exact scope -/

/-- The source-level hypotheses for Theorem 13.1. -/
def chapter13Theorem13_1Hypotheses
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) : Prop :=
  CharZero K ∧ Valuation.IsRankOneDiscrete vK ∧
    IsAdicComplete (IsLocalRing.maximalIdeal vK.valuationSubring)
      vK.valuationSubring ∧
    Finite (IsLocalRing.ResidueField vK.valuationSubring)

/-- Theorem 13.1: a complete discretely valued field of characteristic zero
with finite residue field has only finitely many bounded-degree extension
classes over the base field. -/
theorem chapter13_theorem_13_1_bounded_degree_finiteness
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) [CharZero K]
    [Valuation.IsRankOneDiscrete vK]
    [Finite (IsLocalRing.ResidueField vK.valuationSubring)]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (N : ℕ) (hN : 1 ≤ N) :
    chapter13BoundedDegreeFiniteness (K := K) N := by
  sorry

/-- The canonical `p`-adic valuation has the hypotheses used by Theorem 13.1.
The proof is kept as a reusable bridge because the compactness theorem is
stated for an arbitrary normalized valuation. -/
theorem chapter13_padic_field_has_complete_discrete_finite_residue_profile
    (p : ℕ) [Fact p.Prime] :
    chapter13CompleteFiniteResidueProfile (Padic.mulValuation (p := p)) := by
  sorry

/-- Every finite extension of a `p`-adic field is covered by Theorem 13.1. -/
theorem chapter13_padic_field_bounded_degree_finiteness
    (p : ℕ) [Fact p.Prime] (N : ℕ) (hN : 1 ≤ N) :
    chapter13BoundedDegreeFiniteness (K := ℚ_[p]) N := by
  let hprofile :=
    chapter13_padic_field_has_complete_discrete_finite_residue_profile p
  let : Valuation.IsRankOneDiscrete (Padic.mulValuation (p := p)) := hprofile.1.1
  let : Finite (IsLocalRing.ResidueField
      (Padic.mulValuation (p := p)).valuationSubring) := hprofile.2
  exact chapter13_theorem_13_1_bounded_degree_finiteness
    (vK := Padic.mulValuation (p := p))
    hprofile.1.2 N hN

/-- The source-level hypotheses for the tame bounded-degree theorem. -/
def chapter13Theorem13_2Hypotheses
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) : Prop :=
  Valuation.IsRankOneDiscrete vK ∧
    IsAdicComplete (IsLocalRing.maximalIdeal vK.valuationSubring)
      vK.valuationSubring ∧
    Finite (IsLocalRing.ResidueField vK.valuationSubring)

/-- Theorem 13.2: among finite extensions of a complete discretely valued
field with finite residue field, the tamely ramified classes of bounded degree
form a finite set.  Unramified extensions are included because their
ramification index is one. -/
theorem chapter13_theorem_13_2_bounded_tame_finiteness
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ)
    [Valuation.IsRankOneDiscrete vK]
    [Finite (IsLocalRing.ResidueField vK.valuationSubring)]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (N : ℕ) :
    chapter13TameBoundedDegreeFiniteness vK N := by
  sorry

theorem chapter13_char_zero_finiteness_restricts_to_tame_classes
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) [CharZero K]
    [Valuation.IsRankOneDiscrete vK]
    [Finite (IsLocalRing.ResidueField vK.valuationSubring)]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (N : ℕ) (hN : 1 ≤ N) :
    Set.Finite (chapter13TameBoundedDegreeClasses vK N) := by
  sorry

/-- Embeddings into a chosen overfield are not the same object as
base-field isomorphism classes. -/
def chapter13ExtensionEmbeddings
    (K L Ω : Type*) [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω]
    [IsScalarTower K L Ω] : Type _ :=
  L →ₐ[K] Ω

theorem chapter13_one_separable_class_can_have_several_embeddings
    {K L Ω : Type*} [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω]
    [IsScalarTower K L Ω] [IsAlgClosed Ω]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hdegree : 2 ≤ Module.finrank K L) :
    ∃ σ τ : chapter13ExtensionEmbeddings K L Ω, σ ≠ τ := by
  have hcard : Fintype.card (L →ₐ[K] Ω) = Module.finrank K L :=
    AlgHom.card K L Ω
  have hcard' : 2 ≤ Fintype.card (L →ₐ[K] Ω) := by
    rw [hcard]
    exact hdegree
  have hnot : ¬ Subsingleton (L →ₐ[K] Ω) := by
    intro hsub
    have hle : Fintype.card (L →ₐ[K] Ω) ≤ 1 :=
      Fintype.card_le_one_iff_subsingleton.mpr hsub
    omega
  have hnontrivial : Nontrivial (L →ₐ[K] Ω) :=
    not_subsingleton_iff_nontrivial.mp hnot
  exact hnontrivial.exists_pair_ne

theorem chapter13_unbounded_degrees_are_not_a_bounded_finiteness_claim
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) [CharZero K]
    [Valuation.IsRankOneDiscrete vK]
    [Finite (IsLocalRing.ResidueField vK.valuationSubring)]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring) :
    Set.Infinite (Set.univ : Set (Chapter13FiniteExtensionClass K)) := by
  let A := vK.valuationSubring
  obtain ⟨π, hπirr⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hπ : Ideal.span ({π} : Set A) = IsLocalRing.maximalIdeal A :=
    hπirr.maximalIdeal_eq.symm
  have hpoly (n : ℕ) :
      Irreducible
        ((LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08RadicalPolynomial
          π (n + 1)).map (algebraMap A K)) := by
    have hbook :=
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08_radical_polynomial_is_eisenstein
        π hπirr.maximalIdeal_eq (n + 1) (Nat.succ_pos n)
    let _ : (Ideal.span ({π} : Set A)).IsPrime := by
      rw [hπ]
      infer_instance
    have hE :
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08RadicalPolynomial
          π (n + 1)).IsEisensteinAt (Ideal.span ({π} : Set A)) := by
      apply hbook.1.isEisensteinAt_of_mem_of_notMem
      · rw [hπ]
        exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      · intro i hi
        exact hbook.2.2.1 i hi
      · simpa [Ideal.span_singleton_pow] using hbook.2.2.2.1
    have hirrA :
        Irreducible
          (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08RadicalPolynomial
            π (n + 1)) :=
      hE.irreducible inferInstance hbook.1.isPrimitive hbook.2.1
    exact (hbook.1.isPrimitive.irreducible_iff_irreducible_map_fraction_map).mp hirrA
  let model (n : ℕ) : Chapter13FiniteExtensionModel K := by
    let f : Polynomial K :=
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08RadicalPolynomial
        π (n + 1)).map (algebraMap A K)
    have hfmonic : f.Monic := by
      exact (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08_radical_polynomial_is_eisenstein
        π hπirr.maximalIdeal_eq (n + 1) (Nat.succ_pos n)).1.map (algebraMap A K)
    have hfirr : Irreducible f := by
      exact hpoly n
    letI : Fact (Irreducible f) := ⟨hfirr⟩
    exact
      { carrier := AdjoinRoot f
        field_carrier := inferInstance
        algebra := inferInstance
        finite_dimensional := (AdjoinRoot.powerBasis' hfmonic).finite }
  have hmodeldegree (n : ℕ) :
      chapter13FiniteExtensionDegree (model n) = n + 1 := by
    let f : Polynomial K :=
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08RadicalPolynomial
        π (n + 1)).map (algebraMap A K)
    have hfmonic : f.Monic := by
      exact (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08_radical_polynomial_is_eisenstein
        π hπirr.maximalIdeal_eq (n + 1) (Nat.succ_pos n)).1.map (algebraMap A K)
    have hfne : f ≠ 0 := hfmonic.ne_zero
    change Module.finrank K (AdjoinRoot f) = n + 1
    rw [PowerBasis.finrank (AdjoinRoot.powerBasis hfne)]
    rw [AdjoinRoot.powerBasis_dim]
    simp [f, LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08RadicalPolynomial]
  let classes (n : ℕ) : Chapter13FiniteExtensionClass K :=
    chapter13FiniteExtensionClassOf (model n)
  have hclasses_injective : Function.Injective classes := by
    intro m n hmn
    have hrel : chapter13FiniteExtensionIso (model m) (model n) :=
      Quotient.exact hmn
    letI : Field (model m).carrier := (model m).field_carrier
    letI : Algebra K (model m).carrier := (model m).algebra
    letI : FiniteDimensional K (model m).carrier := (model m).finite_dimensional
    letI : Field (model n).carrier := (model n).field_carrier
    letI : Algebra K (model n).carrier := (model n).algebra
    letI : FiniteDimensional K (model n).carrier := (model n).finite_dimensional
    change Nonempty ((model m).carrier ≃ₐ[K] (model n).carrier) at hrel
    rcases hrel with ⟨e⟩
    have hdegree :
        chapter13FiniteExtensionDegree (model m) =
          chapter13FiniteExtensionDegree (model n) := by
      change Module.finrank K (model m).carrier = Module.finrank K (model n).carrier
      exact e.toLinearEquiv.finrank_eq
    rw [hmodeldegree m, hmodeldegree n] at hdegree
    omega
  exact Set.infinite_of_injective_forall_mem hclasses_injective
    (fun n => Set.mem_univ (classes n))

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter13
