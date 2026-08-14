import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter10.Section01TheLocalNode

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter10

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Set
open scoped BigOperators

universe u

/-! ## 10.2. Functions under normalization -/

/-- The split, rational-node specialization of the normalization data. -/
structure Chapter10SplitNodalCurveData (k : Type u) [Field k] where
  general : Chapter10NodalCurveData k
  rationalNodes : ∀ q : general.nodes, (general.nodeData q).residue.degree = 1
  rationalBranches : Prop
  rationalBranches_holds : rationalBranches
  orderedBranches : Prop
  orderedBranches_holds : orderedBranches

def chapter10BranchValueDifference
    {k : Type u} [Field k]
    (D : Chapter10SplitNormalizationFunctionData (k := k))
    (f : Γ(D.normalization.carrier, ⊤)) (q : D.nodes.index) : k :=
  D.leftValue q f - D.rightValue q f

theorem chapter10_branch_value_difference_zero_iff_agreement
    {k : Type u} [Field k]
    (D : Chapter10SplitNormalizationFunctionData (k := k))
    (f : Γ(D.normalization.carrier, ⊤)) (q : D.nodes.index) :
    chapter10BranchValueDifference D f q = 0 ↔
      D.leftValue q f = D.rightValue q f := by
  constructor
  · intro h
    exact sub_eq_zero.mp h
  · intro h
    exact sub_eq_zero.mpr h

theorem chapter10_split_nodes_have_residue_degree_one
    {k : Type u} [Field k] (D : Chapter10SplitNodalCurveData k) (q : D.general.nodes) :
    chapter10NodeResidueDegree D.general q = 1 := by
  exact D.rationalNodes q

/-!
For a split node the final condition is equality of the two branch values.
The function criterion is stated with the canonical global-section types and
the branch evaluation interface from `Dependencies.lean`.
-/

theorem chapter10_regular_function_descends_iff_branch_values_agree
    {k : Type u} [Field k]
    (D : Chapter10SplitNormalizationFunctionData (k := k))
    (f : Γ(D.normalization.carrier, ⊤)) :
    (∃ g : Γ(D.curve.carrier, ⊤), D.pullback g = f) ↔
      ∀ q : D.nodes.index, D.leftValue q f = D.rightValue q f := by
  exact chapter10_function_descends_iff D f

/-!
The split normalization sequence.  The last sheaf is represented by the
node-discrepancy sheaf interface rather than by a bare unrelated direct sum;
its `quotient_identification` field records that it is the direct sum of the
skyscraper copies `k_q` in the rational-node case.
-/

theorem chapter10_normalization_structure_sheaf_exact_sequence
    {k : Type u} [Field k] (D : Chapter10NodalCurveData k) :
    ∃ Q : Chapter10NodeDiscrepancySheaf D,
      Nonempty (Chapter10NormalizationStructureSheafExactSequence D Q) := by
  sorry

theorem chapter10_normalization_exact_sequence_has_expected_terms
    {k : Type u} [Field k] (D : Chapter10NodalCurveData k)
    (Q : Chapter10NodeDiscrepancySheaf D)
    (E : Chapter10NormalizationStructureSheafExactSequence D Q) :
    E.quotient_identification := by
  exact E.quotient_identification_holds

theorem chapter10_nonsplit_last_term_is_sum_of_discrepancy_lines
    {k : Type u} [Field k] (D : Chapter10NodalCurveData k)
    (Q : Chapter10NodeDiscrepancySheaf D) :
    Q.isDirectSumOfPushforwardDiscrepancyLines := by
  exact Q.isDirectSumOfPushforwardDiscrepancyLines_holds

/-!
Over a nonsplit node the branch algebra and discrepancy line are intrinsic.
The orientation-free statement is recorded separately from the split
identification, since reversing an ordering changes the coordinate by a sign.
-/

def chapter10OrientationReversal {K : Type u} [Field K] : K → K :=
  Neg.neg

theorem chapter10_orientation_reversal_is_neg {K : Type u} [Field K] (a : K) :
    chapter10OrientationReversal a = -a := by
  rfl

theorem chapter10_nonsplit_discrepancy_line_is_intrinsic
    {k : Type u} [Field k] (D : Chapter10NodalCurveData k) (q : D.nodes) :
    letI := (D.nodeData q).residue.field
    Module.finrank (D.nodeData q).residue.carrier
      (chapter10NodeDiscrepancyLine (D.nodeData q)) = 1 := by
  let := (D.nodeData q).residue.field
  exact chapter10_discrepancy_line_is_one_dimensional
    (D.nodeData q).branches

abbrev Chapter10DiscrepancyOrientation
    (K Q : Type u) [Field K] [AddCommGroup Q] [Module K Q] :=
  Q ≃ₗ[K] K

theorem chapter10_discrepancy_orientation_exists_of_finrank_one
    {K Q : Type u} [Field K] [AddCommGroup Q] [Module K Q]
    (hQ : Module.finrank K Q = 1) :
    Nonempty (Chapter10DiscrepancyOrientation K Q) := by
  let : FiniteDimensional K Q :=
    FiniteDimensional.of_finrank_pos (by omega)
  exact ⟨LinearEquiv.ofFinrankEq Q K (by simp [hQ])⟩

noncomputable def chapter10ReversedDiscrepancyOrientation
    {K Q : Type u} [Field K] [AddCommGroup Q] [Module K Q]
    (e : Chapter10DiscrepancyOrientation K Q) :
    Chapter10DiscrepancyOrientation K Q := by
  exact e.trans (LinearEquiv.neg K)

theorem chapter10_reversed_discrepancy_orientation_negates_coordinates
    {K Q : Type u} [Field K] [AddCommGroup Q] [Module K Q]
    (e : Chapter10DiscrepancyOrientation K Q) (q : Q) :
    chapter10ReversedDiscrepancyOrientation e q = -(e q) := by
  rfl

/-! An orientation can be chosen noncanonically, while the discrepancy line
itself stores no such choice.  Reversing the choice is handled by the preceding
negation theorem. -/
theorem chapter10_nonsplit_discrepancy_line_orientation_exists
    {k : Type u} [Field k] (D : Chapter10NodalCurveData k) (q : D.nodes) :
    letI := (D.nodeData q).residue.field
    Nonempty (Chapter10DiscrepancyOrientation
      (D.nodeData q).residue.carrier
      (chapter10NodeDiscrepancyLine (D.nodeData q))) := by
  let := (D.nodeData q).residue.field
  exact chapter10_discrepancy_orientation_exists_of_finrank_one
    (chapter10_nonsplit_discrepancy_line_is_intrinsic D q)

/-! ### Arithmetic genus after normalization -/

theorem chapter10_arithmetic_genus_normalization_formula
    {k : Type u} [Field k] (D : Chapter10NodalCurveData k)
    (Q : Chapter10NodeDiscrepancySheaf D)
    (E : Chapter10NormalizationStructureSheafExactSequence D Q) :
    D.arithmeticGenus =
      (∑ i, D.componentGenus i) +
        (∑ q, (chapter10NodeResidueDegree D q : ℤ)) -
          (Fintype.card D.components : ℤ) + 1 := by
  rw [D.arithmeticGenus_eq_one_sub_eulerCharacteristic,
    E.eulerCharacteristic_relation,
    D.normalizationEulerCharacteristic_eq_components]
  simp [Finset.sum_sub_distrib]
  ring_nf
  rfl

theorem chapter10_split_arithmetic_genus_formula
    {k : Type u} [Field k] (D : Chapter10SplitNodalCurveData k)
    (Q : Chapter10NodeDiscrepancySheaf D.general)
    (E : Chapter10NormalizationStructureSheafExactSequence D.general Q) :
    D.general.arithmeticGenus =
      (∑ i, D.general.componentGenus i) +
        (Fintype.card D.general.nodes : ℤ) -
          (Fintype.card D.general.components : ℤ) + 1 := by
  rw [chapter10_arithmetic_genus_normalization_formula D.general Q E]
  simp [chapter10NodeResidueDegree, D.rationalNodes]

def chapter10SplitNodeCount {k : Type u} [Field k]
    (D : Chapter10SplitNodalCurveData k) : ℕ :=
  Fintype.card D.general.nodes

def chapter10NormalizationComponentCount {k : Type u} [Field k]
    (D : Chapter10SplitNodalCurveData k) : ℕ :=
  Fintype.card D.general.components

theorem chapter10_dual_graph_cycle_term_is_first_betti
    {k : Type u} [Field k] (D : Chapter10SplitNodalCurveData k)
    (G : Chapter10DualGraph)
    (hvertices : Fintype.card G.vertices =
      chapter10NormalizationComponentCount D)
    (hedges : Fintype.card G.edges = chapter10SplitNodeCount D) :
    G.firstBetti =
      (chapter10SplitNodeCount D : ℤ) -
        (chapter10NormalizationComponentCount D : ℤ) + 1 := by
  simp [Chapter10DualGraph.firstBetti, chapter10FirstBettiNumber,
    hvertices, hedges]

/-!
The residue-field degrees in the general formula are deliberately retained:
only after passing to a splitting field do all node contributions become one.
-/

theorem chapter10_residue_degree_contribution_survives_before_splitting
    {k : Type u} [Field k] (D : Chapter10NodalCurveData k) :
    (∑ q, (chapter10NodeResidueDegree D q : ℤ)) =
      ∑ q, ((D.nodeData q).residue.degree : ℤ) := by
  rfl

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter10
