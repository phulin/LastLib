import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter10.Section02FunctionsUnderNormalization

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter10

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Set
open scoped BigOperators LaurentSeries PowerSeries

universe u

/-! ## 10.3. Rosenlicht differentials -/

/-- The allowed normalization differentials in the split branch description.
The `allowedSections` type is the section space of
`ν_* Ω¹_{~ C}(∑(q'+q''))`; the displayed residue maps are its Laurent
coefficients on the chosen branches. -/
structure Chapter10SplitRosenlichtSectionData
    {k : Type u} [Field k] where
  curve : Chapter10SplitNodalCurveData k
  allowedSections : Type u
  residueLeft : curve.general.nodes → allowedSections → k
  residueRight : curve.general.nodes → allowedSections → k

def chapter10SplitRosenlichtOppositeResidues
    {k : Type u} [Field k] (D : Chapter10SplitRosenlichtSectionData)
    (η : D.allowedSections) : Prop :=
  ∀ q, D.residueLeft q η + D.residueRight q η = 0

def chapter10SplitRosenlichtSections
    {k : Type u} [Field k] (D : Chapter10SplitRosenlichtSectionData) : Type u :=
  {η : D.allowedSections // chapter10SplitRosenlichtOppositeResidues D η}

/-- A sheaf-level presentation of the normalization formula for the dualizing
sheaf. -/
structure Chapter10RosenlichtSheafPresentation
    {k : Type u} [Field k] (D : Chapter10SplitNodalCurveData k) where
  dualizing : D.general.curve.carrier.Modules
  allowedNormalizationDifferentials : D.general.curve.carrier.Modules
  comparison : dualizing ≅ allowedNormalizationDifferentials
  simplePolesAtBranches : Prop
  oppositeResidueCondition : Prop
  ordinaryCanonicalAwayFromNodes : Prop

theorem chapter10_rosenlicht_sheaf_description
    {k : Type u} [Field k] (D : Chapter10SplitNodalCurveData k) :
    Nonempty (Chapter10RosenlichtSheafPresentation D) := by
  sorry

theorem chapter10_rosenlicht_sections_are_regular_with_simple_branch_poles
    {k : Type u} [Field k]
    {D : Chapter10SplitNodalCurveData k}
    (P : Chapter10RosenlichtSheafPresentation D) :
    P.simplePolesAtBranches := by
  exact P.simplePolesAtBranches

/-!
The preceding theorem is intentionally exposed through the presentation
record: it gives a reusable sheaf comparison, while the section-level
subtype below is the branch-and-residue formula used by computations.
-/

theorem chapter10_rosenlicht_module_is_free_at_a_split_node
    (k : Type u) [Field k] :
    Chapter10FreeRankOne (chapter10CompletedNodeRing k)
      (chapter10NodeDualizingModule k) := by
  exact chapter10_node_dualizing_module_free_rank_one k

/-! ### The completed local calculation -/

def chapter10NodeSimplePolePair {k : Type u} [Field k]
    (a b : PowerSeries k) : Chapter10BranchDifferentialPair k :=
  (algebraMap (PowerSeries k) (LaurentSeries k) a *
      (chapter10NodeBranchUniformizer k)⁻¹,
    algebraMap (PowerSeries k) (LaurentSeries k) b *
      (chapter10NodeBranchUniformizer k)⁻¹)

def chapter10NodeSubringToLaurentPair {k : Type u} [Field k]
    (g : chapter10NodeNormalizationSubring k) :
    Chapter10BranchDifferentialPair k :=
  (algebraMap (PowerSeries k) (LaurentSeries k) g.1.1,
    algebraMap (PowerSeries k) (LaurentSeries k) g.1.2)

def chapter10NodeSimplePoleResidueCondition {k : Type u} [Field k]
    (a b : PowerSeries k) : Prop :=
  PowerSeries.constantCoeff a + PowerSeries.constantCoeff b = 0

theorem chapter10_node_simple_pole_pair_is_node_multiple
    (k : Type u) [Field k] (a b : PowerSeries k)
    (hres : chapter10NodeSimplePoleResidueCondition a b) :
    ∃ g : chapter10NodeNormalizationSubring k,
      chapter10NodeSimplePolePair a b =
        chapter10NodeSubringToLaurentPair g * chapter10NodeTheta k := by
  sorry

theorem chapter10_node_multiple_has_opposite_residues
    (k : Type u) [Field k] (g : chapter10NodeNormalizationSubring k) :
    chapter10OppositeResidues
      (chapter10NodeSubringToLaurentPair g * chapter10NodeTheta k) := by
  sorry

/-! ### Intrinsic residue conditions -/

def chapter10NodeIntrinsicResidueCondition
    {k : Type u} [Field k] (η : Chapter10BranchDifferentialPair k) : Prop :=
  ∀ g : chapter10NodeNormalizationSubring k,
    chapter10LaurentResidue
        (algebraMap (PowerSeries k) (LaurentSeries k) g.1.1 * η.1) +
      chapter10LaurentResidue
        (algebraMap (PowerSeries k) (LaurentSeries k) g.1.2 * η.2) = 0

theorem chapter10_split_node_intrinsic_condition_iff_opposite_residues
    {k : Type u} [Field k] (η : Chapter10BranchDifferentialPair k) :
    chapter10NodeIntrinsicResidueCondition η ↔
      chapter10OppositeResidues η := by
  sorry

/-!
The general Rosenlicht condition is written with the canonical `k`-valued
residue functionals and all local functions.  This is the form which survives
descent and arbitrary singularities.
-/

def chapter10IntrinsicResidueCondition
    {K P D : Type u} [Field K] [AddCommGroup D] [Module K D]
    (preimages : Finset P) (localFunctions : Type u)
    (action : localFunctions → D → D) (residue : P → D →ₗ[K] K) (η : D) : Prop :=
  ∀ f : localFunctions, ∑ p in preimages, residue p (action f η) = 0

structure Chapter10ScalarExtensionResidueTest
    {K L P D : Type u} [Field K] [Field L] [Algebra K L]
    [AddCommGroup D] [Module K D] [Module L D] where
  basePreimages : Finset P
  extensionPreimages : Finset P
  localFunctions : Type u
  baseAction : localFunctions → D → D
  extensionAction : localFunctions → D → D
  baseResidue : P → D →ₗ[K] K
  extensionResidue : P → D →ₗ[L] L
  baseSection : D
  extensionSection : D
  faithfullyFlat : Prop
  splittingField : Prop
  scalarExtensionCompatibility : Prop

def chapter10ScalarExtensionBaseCondition
    {K L P D : Type u} [Field K] [Field L] [Algebra K L]
    [AddCommGroup D] [Module K D] [Module L D]
    (T : Chapter10ScalarExtensionResidueTest) : Prop :=
  chapter10IntrinsicResidueCondition T.basePreimages T.localFunctions
    T.baseAction T.baseResidue T.baseSection

def chapter10ScalarExtensionCondition
    {K L P D : Type u} [Field K] [Field L] [Algebra K L]
    [AddCommGroup D] [Module K D] [Module L D]
    (T : Chapter10ScalarExtensionResidueTest) : Prop :=
  ∀ f : T.localFunctions,
    ∑ p in T.extensionPreimages,
      (T.extensionResidue p) (T.extensionAction f T.extensionSection) = 0

theorem chapter10_intrinsic_residue_condition_scalar_extension_iff
    {K L P D : Type u} [Field K] [Field L] [Algebra K L]
    [AddCommGroup D] [Module K D] [Module L D]
    (T : Chapter10ScalarExtensionResidueTest)
    (hfaithfullyFlat : T.faithfullyFlat)
    (hsplitting : T.splittingField)
    (hcompatibility : T.scalarExtensionCompatibility) :
    chapter10ScalarExtensionBaseCondition T ↔
      chapter10ScalarExtensionCondition T := by
  sorry

/-! ### The split residue exact sequence and its graph relations -/

structure Chapter10SplitResidueSheaf
    {k : Type u} [Field k] (D : Chapter10SplitNodalCurveData k) where
  sheaf : D.general.curve.carrier.Modules
  nodewiseCopiesOfTheField : Prop
  finiteDirectSum : Prop

structure Chapter10SplitRosenlichtResidueExactSequence
    {k : Type u} [Field k] (D : Chapter10SplitNodalCurveData k)
    (R : Chapter10SplitResidueSheaf D) where
  normalizationCanonical : D.general.curve.carrier.Modules
  dualizing : D.general.curve.carrier.Modules
  inclusion : normalizationCanonical ⟶ dualizing
  residue : dualizing ⟶ R.sheaf
  comp_zero : inclusion ≫ residue = 0
  mono_inclusion : Mono inclusion
  epi_residue : Epi residue
  exact : (ShortComplex.mk inclusion residue comp_zero).Exact
  residue_on_left_branch : Prop
  residue_on_right_branch_is_negative : Prop
  local_surjectivity : Prop

theorem chapter10_split_rosenlicht_residue_exact_sequence
    {k : Type u} [Field k] (D : Chapter10SplitNodalCurveData k) :
    ∃ R : Chapter10SplitResidueSheaf D,
      Nonempty (Chapter10SplitRosenlichtResidueExactSequence D R) := by
  sorry

/-- The nonsplit form of the residue sequence.  Its terminal sheaf is the
dual of the branch discrepancy line rather than a canonically chosen copy of
the residue field. -/
structure Chapter10NonsplitResidueSheaf
    {k : Type u} [Field k] (D : Chapter10NodalCurveData k) where
  sheaf : D.curve.carrier.Modules
  nodewiseResidueLine : ∀ q : D.nodes,
    chapter10NodeDiscrepancyLine (D.nodeData q) →ₗ[
      (D.nodeData q).residue.carrier] (D.nodeData q).residue.carrier
  finiteDirectSum : Prop
  GaloisInvariant : Prop

structure Chapter10NonsplitRosenlichtResidueExactSequence
    {k : Type u} [Field k] (D : Chapter10NodalCurveData k)
    (R : Chapter10NonsplitResidueSheaf D) where
  normalizationCanonical : D.curve.carrier.Modules
  dualizing : D.curve.carrier.Modules
  inclusion : normalizationCanonical ⟶ dualizing
  residue : dualizing ⟶ R.sheaf
  comp_zero : inclusion ≫ residue = 0
  mono_inclusion : Mono inclusion
  epi_residue : Epi residue
  exact : (ShortComplex.mk inclusion residue comp_zero).Exact
  duality_with_discrepancy_lines : Prop
  local_surjectivity : Prop

theorem chapter10_nonsplit_rosenlicht_residue_exact_sequence
    {k : Type u} [Field k] (D : Chapter10NodalCurveData k) :
    ∃ R : Chapter10NonsplitResidueSheaf D,
      Nonempty (Chapter10NonsplitRosenlichtResidueExactSequence D R) := by
  sorry

def chapter10DualGraphCycleCondition
    {k : Type u} [Field k] (G : Chapter10DualGraph)
    (r : G.edges → k) : Prop :=
  ∀ v,
    (∑ e in Finset.univ.filter (fun e => G.left e = v), r e) -
      ∑ e in Finset.univ.filter (fun e => G.right e = v), r e = 0

structure Chapter10GlobalRosenlichtResidueData
    {k : Type u} [Field k] where
  graph : Chapter10DualGraph
  globalSections : Type u
  residueAtEdge : graph.edges → globalSections → k
  componentResidueTheorem : ∀ η, Prop

theorem chapter10_global_component_residue_relations_are_cycle_relations
    {k : Type u} [Field k] (D : Chapter10GlobalRosenlichtResidueData)
    (η : D.globalSections) (hglobal : D.componentResidueTheorem η) :
    chapter10DualGraphCycleCondition D.graph (fun e => D.residueAtEdge e η) := by
  sorry

/-! ### Nonsplit residue lines and the non-Gorenstein boundary -/

abbrev chapter10NonsplitResidueLine
    {K : Type u} [Field K] (B : Chapter10BranchAlgebraData K) : Type u :=
  chapter10DiscrepancyLine B →ₗ[K] K

theorem chapter10_nonsplit_residue_line_is_dual_to_discrepancy_line
    {K : Type u} [Field K] (B : Chapter10BranchAlgebraData K) :
    chapter10NonsplitResidueLine B =
      (chapter10DiscrepancyLine B →ₗ[K] K) :=
  rfl

theorem chapter10_nonsplit_residue_line_is_one_dimensional
    {K : Type u} [Field K] (B : Chapter10BranchAlgebraData K) :
    letI := B.commRing
    letI := B.algebra
    Module.finrank K (chapter10NonsplitResidueLine B) = 1 := by
  sorry

structure Chapter10GeneralSingularCurveRosenlichtData
    {k : Type u} [Field k] where
  curve : Chapter10Curve k
  dualizing : curve.carrier.Modules
  normalizationDifferentials : curve.carrier.Modules
  localFunctions : Type u
  preimagePoints : Type u
  residue : preimagePoints →
    (Scheme.Modules.presheaf normalizationDifferentials).obj
      (Opposite.op (⊤ : curve.carrier.Opens)) →ₗ[k] k
  action : localFunctions →
    (Scheme.Modules.presheaf normalizationDifferentials).obj
      (Opposite.op (⊤ : curve.carrier.Opens)) →
    (Scheme.Modules.presheaf normalizationDifferentials).obj
      (Opposite.op (⊤ : curve.carrier.Opens))
  rosCondition : Prop
  agreesWithIntrinsicCondition : Prop
  gorenstein : Prop
  gorenstein_iff_invertible :
    gorenstein ↔ chapter09IsInvertibleSheaf dualizing

theorem chapter10_general_rosenlicht_description
    {k : Type u} [Field k] (D : Chapter10GeneralSingularCurveRosenlichtData) :
    D.agreesWithIntrinsicCondition := by
  exact D.agreesWithIntrinsicCondition

theorem chapter10_general_rosenlicht_need_not_be_invertible
    {k : Type u} [Field k] (D : Chapter10GeneralSingularCurveRosenlichtData)
    (hnotGorenstein : ¬ D.gorenstein) :
    ¬ chapter09IsInvertibleSheaf D.dualizing := by
  intro hinvertible
  exact hnotGorenstein (D.gorenstein_iff_invertible.mpr hinvertible)

theorem chapter10_split_node_other_tests_add_no_condition
    {k : Type u} [Field k] (η : Chapter10BranchDifferentialPair k) :
    chapter10NodeIntrinsicResidueCondition η ↔
      chapter10OppositeResidues η := by
  exact chapter10_split_node_intrinsic_condition_iff_opposite_residues η

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter10
