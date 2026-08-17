import LastLib.Book06GlobalClassFieldTheory.Chapter12.Dependencies

namespace LastLib.Book06GlobalClassFieldTheory.Chapter12

noncomputable section

open scoped BigOperators
open LastLib.Book06GlobalClassFieldTheory.Chapter04
open LastLib.Book06GlobalClassFieldTheory.Chapter10

/-! ## 12.6. Conclusion -/

structure Chapter12PrincipalLocalSymbolData (I A : Type*)
    [CommGroup A] where
  localSymbol : I → A
  finiteSupport : Set I
  finiteSupport_finite : finiteSupport.Finite
  outside_support_one : ∀ i, i ∉ finiteSupport → localSymbol i = 1
  product_one :
    ∏ i ∈ finiteSupport_finite.toFinset, localSymbol i = 1

theorem chapter12_principal_local_symbols_multiply_to_one
    {I A : Type*} [CommGroup A]
    (D : Chapter12PrincipalLocalSymbolData I A) :
    ∏ i ∈ D.finiteSupport_finite.toFinset, D.localSymbol i = 1 := by
  exact D.product_one

theorem chapter12_finite_level_dictionary_is_exact
    {K L C : Type*} [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [CommGroup C] [TopologicalSpace C] [IsTopologicalGroup C]
    (D : Chapter12FiniteAbelianLevel K L C) :
    IsOpen (D.normSubgroup : Set C) ∧ D.normSubgroup.FiniteIndex ∧
      D.artin.ker = D.normSubgroup ∧
      Function.Surjective D.artin ∧
      Nat.card (C ⧸ D.normSubgroup) = Module.finrank K L := by
  exact ⟨D.normSubgroup_open, D.normSubgroup_finiteIndex,
    D.artin_kernel, D.artin_surjective, D.quotient_index_degree⟩

theorem chapter12_principal_local_symbols_have_product_one
    {I : Type*} (D : Chapter04GlobalLocalizedPairingData I)
    (x : D.X) (y : D.Y) :
    ∑ i ∈ (D.finite_support x y).toFinset,
      D.localPairing i ((D.localizeX x) i) ((D.localizeY y) i) = 0 := by
  exact chapter04_global_diagonal_cup_orthogonality D x y

theorem chapter12_global_brauer_invariant_row_is_exact
    {F : Type*} [Field F] [NumberField F]
    (D : Chapter04BrauerContext F)
    (B : Chapter04BrauerInvariantSequenceData D) :
    chapter04BrauerInvariantExact D := by
  exact chapter04_global_invariant_sequence D B

theorem chapter12_global_brauer_class_has_zero_total_invariant
    {F : Type*} [Field F] [NumberField F]
    (D : Chapter04BrauerContext F)
    (B : Chapter04BrauerInvariantSequenceData D) (x : D.Br) :
    chapter04BrauerInvariantSum D (D.localization x) = 0 := by
  exact (B.exact_sequence.2.1 _).mpr ⟨x, rfl⟩

def chapter12DegreeThreeCompactSupportTrace
    {G : Type*} [Group G]
    (C : Chapter04CompactSupportAPI G) (M : Chapter04GModule G) :
    chapter04CompactSupportH C M 3 →+ chapter04QModZ :=
  chapter04CompactSupportTrace C M

theorem chapter12_degree_three_trace_is_the_normalized_global_trace
    {G : Type*} [Group G]
    (C : Chapter04CompactSupportAPI G) (M : Chapter04GModule G) :
    chapter12DegreeThreeCompactSupportTrace C M = C.trace M := by
  rfl

theorem chapter12_compact_support_trace_has_the_coefficient_range
    {G : Type*} [Group G]
    (C : Chapter04CompactSupportAPI G)
    (P : Chapter04DualCoefficientPair G)
    (z : chapter04CompactSupportH C P.μn 3) :
    chapter12DegreeThreeCompactSupportTrace C P.μn z ∈
      chapter04QModZTorsion P.n := by
  exact chapter04_compact_support_trace_has_finite_coefficient_range C P z

theorem chapter12_global_pairing_is_perfect
    {G : Type*} [Group G]
    (C : Chapter04CompactSupportAPI G)
    (P : Chapter04DualCoefficientPair G)
    (Q : Chapter04GlobalCompactPairingData C P)
    (L : Chapter04GlobalCompactPairingPerfectness C P Q) :
    ∀ r : ℤ, chapter04PerfectPairing (Q.pairing r) := by
  sorry

theorem chapter12_global_trace_sums_over_branches
    {I : Type*} [Fintype I]
    (D : Chapter04GlobalTraceBranchData I) (z : ∀ i, D.branch i) :
    D.baseInvariant (∑ i, D.branchCorestriction i (z i)) =
      ∑ i, D.branchInvariant i (z i) := by
  exact chapter04_global_trace_branch_sum_formula D z

noncomputable def chapter12_infinite_reciprocity_is_the_component_quotient
    {C K Kab : Type u} [CommGroup C] [TopologicalSpace C] [T2Space C]
    [IsTopologicalGroup C] [Field K] [Field Kab] [Algebra K Kab]
    [IsGalois K Kab]
    (T : Chapter10IdeleClassTopologyData C)
    (F : Chapter10FiniteArtinFamily C K Kab)
    (R : Chapter10FiniteReciprocityData F) :
    chapter10IdeleClassComponentQuotient C ≃ₜ* Gal(Kab / K) := by
  exact chapter10GlobalArtinQuotientEquiv T F R

def chapter12VirtualInductionRequiresEffectivity
    {R : Type*} (terms : Finset (Chapter12VirtualInductionTerm R)) : Prop :=
  chapter12VirtualCharacterIsEffective terms

theorem chapter12_virtual_induction_effectivity_is_an_extra_input
    {R : Type*} (terms : Finset (Chapter12VirtualInductionTerm R))
    (h : chapter12VirtualInductionRequiresEffectivity terms) :
    chapter12VirtualCharacterIsEffective terms := by
  exact h

/- This final interface deliberately has no theorem deriving effectivity from
the termwise reciprocity data: class field theory supplies each one-dimensional
term and its norm/transfer compatibilities, while cancellation of negative
coefficients is a separate representation-theoretic assertion. -/

end

end LastLib.Book06GlobalClassFieldTheory.Chapter12
