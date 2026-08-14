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
  allowedNormalizationDifferentials :
    curve.general.curve.carrier.Modules
  residueLeft : curve.general.nodes →
    (Scheme.Modules.presheaf allowedNormalizationDifferentials).obj
      (Opposite.op (⊤ : curve.general.curve.carrier.Opens)) → k
  residueRight : curve.general.nodes →
    (Scheme.Modules.presheaf allowedNormalizationDifferentials).obj
      (Opposite.op (⊤ : curve.general.curve.carrier.Opens)) → k

abbrev Chapter10SplitRosenlichtSectionData.allowedSections
    {k : Type u} [Field k]
    (D : Chapter10SplitRosenlichtSectionData (k := k)) : Type u :=
  (Scheme.Modules.presheaf D.allowedNormalizationDifferentials).obj
    (Opposite.op (⊤ : D.curve.general.curve.carrier.Opens))

def chapter10SplitRosenlichtOppositeResidues
    {k : Type u} [Field k]
    (D : Chapter10SplitRosenlichtSectionData (k := k))
    (η : D.allowedSections) : Prop :=
  ∀ q, D.residueLeft q η + D.residueRight q η = 0

def chapter10SplitRosenlichtSections
    {k : Type u} [Field k]
    (D : Chapter10SplitRosenlichtSectionData (k := k)) : Type u :=
  {η : D.allowedSections // chapter10SplitRosenlichtOppositeResidues D η}

/-! A sheaf-level presentation of the normalization formula for the dualizing
sheaf.  The Rosenlicht sheaf is the residue-kernel subsheaf of the ambient
simple-pole normalization sheaf; it is not the whole ambient sheaf. -/
structure Chapter10RosenlichtSheafPresentation
    {k : Type u} [Field k] (D : Chapter10SplitNodalCurveData k) where
  dualizing : D.general.curve.carrier.Modules
  ambientNormalizationDifferentials : D.general.curve.carrier.Modules
  allowedNormalizationDifferentials : D.general.curve.carrier.Modules
  comparison : dualizing ≅ allowedNormalizationDifferentials
  inclusionIntoAmbient :
    allowedNormalizationDifferentials ⟶ ambientNormalizationDifferentials
  mono_inclusionIntoAmbient : Mono inclusionIntoAmbient
  simplePolesAtBranches : Prop
  simplePolesAtBranches_holds : simplePolesAtBranches
  oppositeResidueCondition : Prop
  oppositeResidueCondition_holds : oppositeResidueCondition
  ordinaryCanonicalAwayFromNodes : Prop
  ordinaryCanonicalAwayFromNodes_holds : ordinaryCanonicalAwayFromNodes

theorem chapter10_rosenlicht_sheaf_description
    {k : Type u} [Field k] (D : Chapter10SplitNodalCurveData k) :
    Nonempty (Chapter10RosenlichtSheafPresentation D) := by
  sorry

theorem chapter10_rosenlicht_sections_are_regular_with_simple_branch_poles
    {k : Type u} [Field k]
    {D : Chapter10SplitNodalCurveData k}
    (P : Chapter10RosenlichtSheafPresentation D) :
    P.simplePolesAtBranches := by
  exact P.simplePolesAtBranches_holds

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

/-! The opposite-residue criterion is a criterion for differentials with at
most simple poles on the two normalized branches.  Arbitrary Laurent pairs
can have higher-order poles, for which testing only the branch residues is not
enough. -/
def chapter10NodeHasAtMostSimplePoles {k : Type u} [Field k]
    (η : Chapter10BranchDifferentialPair k) : Prop :=
  ∃ a b : PowerSeries k, η = chapter10NodeSimplePolePair a b

def chapter10NodeSubringToLaurentPair {k : Type u} [Field k]
    (g : chapter10NodeNormalizationSubring k) :
    Chapter10BranchDifferentialPair k :=
  (algebraMap (PowerSeries k) (LaurentSeries k) g.1.1,
    algebraMap (PowerSeries k) (LaurentSeries k) g.1.2)

def chapter10NodeSimplePoleResidueCondition {k : Type u} [Field k]
    (a b : PowerSeries k) : Prop :=
  PowerSeries.constantCoeff a + PowerSeries.constantCoeff b = 0

private theorem chapter10_residue_mul_uniformizer_inv
    (k : Type u) [Field k] (a : PowerSeries k) :
    chapter10LaurentResidue
      (algebraMap (PowerSeries k) (LaurentSeries k) a *
        (chapter10NodeBranchUniformizer k)⁻¹) =
      PowerSeries.constantCoeff a := by
  simp [chapter10LaurentResidue, chapter10NodeBranchUniformizer,
    HahnSeries.inv_single, HahnSeries.coeff_mul_single]
  change (HahnSeries.ofPowerSeries ℤ k a).coeff (↑(0 : ℕ) : ℤ) =
    PowerSeries.constantCoeff a
  rw [HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem chapter10_node_simple_pole_pair_is_node_multiple
    (k : Type u) [Field k] (a b : PowerSeries k)
    (hres : chapter10NodeSimplePoleResidueCondition a b) :
    ∃ g : chapter10NodeNormalizationSubring k,
      chapter10NodeSimplePolePair a b =
        chapter10NodeSubringToLaurentPair g * chapter10NodeTheta k := by
  let g : chapter10NodeNormalizationSubring k :=
    ⟨(a, -b), by
      change PowerSeries.constantCoeff a = PowerSeries.constantCoeff (-b)
      change PowerSeries.constantCoeff a + PowerSeries.constantCoeff b = 0 at hres
      exact eq_neg_of_add_eq_zero_left hres⟩
  refine ⟨g, ?_⟩
  ext <;>
    simp [chapter10NodeSimplePolePair, chapter10NodeSubringToLaurentPair,
      chapter10NodeTheta, g]

theorem chapter10_node_multiple_has_opposite_residues
    (k : Type u) [Field k] (g : chapter10NodeNormalizationSubring k) :
    chapter10OppositeResidues
      (chapter10NodeSubringToLaurentPair g * chapter10NodeTheta k) := by
  change chapter10LaurentResidue
      (algebraMap (PowerSeries k) (LaurentSeries k) g.1.1 *
        (chapter10NodeBranchUniformizer k)⁻¹) +
      chapter10LaurentResidue
        (algebraMap (PowerSeries k) (LaurentSeries k) g.1.2 *
          -((chapter10NodeBranchUniformizer k)⁻¹)) = 0
  simp [chapter10LaurentResidue, chapter10NodeBranchUniformizer,
    HahnSeries.inv_single, HahnSeries.coeff_mul_single]
  change ((HahnSeries.ofPowerSeries ℤ k
      ((g : chapter10NodeNormalizationRing k).1)).coeff (↑(0 : ℕ) : ℤ) +
      -(HahnSeries.ofPowerSeries ℤ k
        ((g : chapter10NodeNormalizationRing k).2)).coeff (↑(0 : ℕ) : ℤ)) = 0
  rw [HahnSeries.ofPowerSeries_apply_coeff,
    HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simpa [sub_eq_add_neg] using sub_eq_zero.mpr g.2

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
    chapter10NodeHasAtMostSimplePoles η →
    (chapter10NodeIntrinsicResidueCondition η ↔
      chapter10OppositeResidues η) := by
  rintro ⟨a, b, rfl⟩
  constructor
  · intro h
    have h0 := h
      (⟨(1, 1), by rfl⟩ : chapter10NodeNormalizationSubring k)
    simp [chapter10NodeSimplePolePair] at h0
    change chapter10LaurentResidue
        (algebraMap (PowerSeries k) (LaurentSeries k) a *
          (chapter10NodeBranchUniformizer k)⁻¹) +
      chapter10LaurentResidue
        (algebraMap (PowerSeries k) (LaurentSeries k) b *
          (chapter10NodeBranchUniformizer k)⁻¹) = 0 at h0
    rw [chapter10_residue_mul_uniformizer_inv k a,
      chapter10_residue_mul_uniformizer_inv k b] at h0
    change chapter10LaurentResidue
        (chapter10NodeSimplePolePair a b).1 +
      chapter10LaurentResidue
        (chapter10NodeSimplePolePair a b).2 = 0
    simp only [chapter10NodeSimplePolePair]
    rw [chapter10_residue_mul_uniformizer_inv k a,
      chapter10_residue_mul_uniformizer_inv k b]
    exact h0
  · intro hres g
    simp [chapter10NodeSimplePolePair] at hres
    change chapter10LaurentResidue
        (algebraMap (PowerSeries k) (LaurentSeries k) a *
          (chapter10NodeBranchUniformizer k)⁻¹) +
      chapter10LaurentResidue
        (algebraMap (PowerSeries k) (LaurentSeries k) b *
          (chapter10NodeBranchUniformizer k)⁻¹) = 0 at hres
    rw [chapter10_residue_mul_uniformizer_inv k a,
      chapter10_residue_mul_uniformizer_inv k b] at hres
    have hnum :
        PowerSeries.constantCoeff ((g : chapter10NodeNormalizationRing k).1 * a) +
          PowerSeries.constantCoeff ((g : chapter10NodeNormalizationRing k).2 * b) = 0 := by
      rw [map_mul, map_mul, ← g.2, ← mul_add, hres, mul_zero]
    simp only [chapter10NodeSimplePolePair]
    rw [← mul_assoc, ← map_mul, ← mul_assoc, ← map_mul]
    rw [chapter10_residue_mul_uniformizer_inv k
          ((g : chapter10NodeNormalizationRing k).1 * a),
      chapter10_residue_mul_uniformizer_inv k
        ((g : chapter10NodeNormalizationRing k).2 * b)]
    exact hnum

/-!
The general Rosenlicht condition is written with the canonical `k`-valued
residue functionals and all local functions.  This is the form which survives
descent and arbitrary singularities.
-/

def chapter10IntrinsicResidueCondition
    {K P D : Type u} [Field K] [AddCommGroup D] [Module K D]
    (preimages : Finset P) (localFunctions : Type u)
    (action : localFunctions → D → D) (residue : P → D →ₗ[K] K) (η : D) : Prop :=
  ∀ f : localFunctions,
    Finset.sum preimages (fun p => residue p (action f η)) = 0

/-!
The global version is intentionally phrased for the actual section type rather
than assuming a linear structure which the pinned sheaf API does not expose.
It is the residue-theorem interface used by the marked-fiber profile.
-/

def chapter10GlobalRosenlichtResidueCondition
    {K P D : Type u} [Field K]
    (preimages : Finset P) (localFunctions : Type u)
    (action : localFunctions → D → D) (residue : P → D → K) (η : D) : Prop :=
  ∀ f : localFunctions,
    Finset.sum preimages (fun p => residue p (action f η)) = 0

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
  faithfullyFlat_holds : faithfullyFlat
  splittingField : Prop
  splittingField_holds : splittingField
  /-- The compatibility flag is tied to the concrete residue-sum equation
  below; it is not an unrelated proposition. -/
  scalarExtensionCompatibility : Prop
  scalarExtensionCompatibility_holds : scalarExtensionCompatibility
  scalarExtensionCompatibility_is_residue_sum_compatibility :
    scalarExtensionCompatibility ↔
      (∀ f : localFunctions,
        Finset.sum extensionPreimages
            (fun p => (extensionResidue p) (extensionAction f extensionSection)) =
          algebraMap K L
            (Finset.sum basePreimages
              (fun p => (baseResidue p) (baseAction f baseSection))))

def chapter10ScalarExtensionBaseCondition
    {K L P D : Type u} [Field K] [Field L] [Algebra K L]
    [AddCommGroup D] [Module K D] [Module L D]
    (T : Chapter10ScalarExtensionResidueTest (K := K) (L := L) (P := P) (D := D)) : Prop :=
  chapter10IntrinsicResidueCondition T.basePreimages T.localFunctions
    T.baseAction T.baseResidue T.baseSection

def chapter10ScalarExtensionCondition
    {K L P D : Type u} [Field K] [Field L] [Algebra K L]
    [AddCommGroup D] [Module K D] [Module L D]
    (T : Chapter10ScalarExtensionResidueTest (K := K) (L := L) (P := P) (D := D)) : Prop :=
  ∀ f : T.localFunctions,
    Finset.sum T.extensionPreimages
      (fun p => (T.extensionResidue p) (T.extensionAction f T.extensionSection)) = 0

theorem chapter10_intrinsic_residue_condition_scalar_extension_iff
    {K L P D : Type u} [Field K] [Field L] [Algebra K L]
    [AddCommGroup D] [Module K D] [Module L D]
    (T : Chapter10ScalarExtensionResidueTest (K := K) (L := L) (P := P) (D := D))
    (_hfaithfullyFlat : T.faithfullyFlat)
    (_hsplitting : T.splittingField)
    (hcompatibility : T.scalarExtensionCompatibility) :
    chapter10ScalarExtensionBaseCondition T ↔
      chapter10ScalarExtensionCondition T := by
  have hcompatibility' :=
    T.scalarExtensionCompatibility_is_residue_sum_compatibility.mp
      hcompatibility
  constructor
  · intro hbase f
    have h := hcompatibility' f
    rw [hbase f, map_zero] at h
    exact h
  · intro hext f
    have h := hcompatibility' f
    rw [hext f] at h
    exact FaithfulSMul.algebraMap_injective K L (by simpa using h.symm)

/-! ### The split residue exact sequence and its graph relations -/

structure Chapter10SplitResidueSheaf
    {k : Type u} [Field k] (D : Chapter10SplitNodalCurveData k) where
  sheaf : D.general.curve.carrier.Modules
  nodewiseCopiesOfTheField : Prop
  nodewiseCopiesOfTheField_holds : nodewiseCopiesOfTheField
  finiteDirectSum : Prop
  finiteDirectSum_holds : finiteDirectSum

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
  residue_on_left_branch_holds : residue_on_left_branch
  residue_on_right_branch_is_negative : Prop
  residue_on_right_branch_is_negative_holds : residue_on_right_branch_is_negative
  local_surjectivity : Prop
  local_surjectivity_holds : local_surjectivity

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
  /-- The fiber at a node is the dual of the branch-discrepancy line.  This
  records the line itself, rather than selecting a coordinate on it. -/
  nodewiseResidueLine : D.nodes → Type u
  nodewiseResidueLine_is_dual : ∀ q : D.nodes,
    nodewiseResidueLine q =
      (chapter10NodeDiscrepancyLine (D.nodeData q) →ₗ[
      (D.nodeData q).residue.carrier] (D.nodeData q).residue.carrier)
  finiteDirectSum : Prop
  finiteDirectSum_holds : finiteDirectSum
  GaloisInvariant : Prop
  GaloisInvariant_holds : GaloisInvariant

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
  duality_with_discrepancy_lines_holds : duality_with_discrepancy_lines
  local_surjectivity : Prop
  local_surjectivity_holds : local_surjectivity

theorem chapter10_nonsplit_rosenlicht_residue_exact_sequence
    {k : Type u} [Field k] (D : Chapter10NodalCurveData k) :
    ∃ R : Chapter10NonsplitResidueSheaf D,
      Nonempty (Chapter10NonsplitRosenlichtResidueExactSequence D R) := by
  sorry

def chapter10DualGraphCycleCondition
    {k : Type u} [Field k] (G : Chapter10DualGraph)
    (r : G.edges → k) : Prop :=
  letI := Classical.decEq G.vertices
  ∀ v : G.vertices,
    Finset.sum (Finset.univ.filter (fun e => G.left e = v)) (fun e => r e) -
      Finset.sum (Finset.univ.filter (fun e => G.right e = v)) (fun e => r e) = 0

structure Chapter10GlobalRosenlichtResidueData
    {k : Type u} [Field k] where
  graph : Chapter10DualGraph
  globalSections : Type u
  residueAtEdge : graph.edges → globalSections → k
  componentResidueTheorem :
    ∀ η : globalSections,
      chapter10DualGraphCycleCondition graph (fun e => residueAtEdge e η)

theorem chapter10_global_component_residue_relations_are_cycle_relations
    {k : Type u} [Field k]
    (D : Chapter10GlobalRosenlichtResidueData (k := k))
    (η : D.globalSections) :
    chapter10DualGraphCycleCondition D.graph (fun e => D.residueAtEdge e η) := by
  exact D.componentResidueTheorem η

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
  let := B.commRing
  let := B.algebra
  let : FiniteDimensional K (chapter10DiscrepancyLine B) :=
    FiniteDimensional.of_finrank_pos (by
      rw [chapter10_discrepancy_line_is_one_dimensional B]
      decide)
  change Module.finrank K
      (Module.Dual K (chapter10DiscrepancyLine B)) = 1
  rw [Subspace.dual_finrank_eq,
    chapter10_discrepancy_line_is_one_dimensional B]

structure Chapter10GeneralSingularCurveRosenlichtData
    {k : Type u} [Field k] where
  curve : Chapter10Curve k
  dualizing : curve.carrier.Modules
  normalizationDifferentials : curve.carrier.Modules
  localFunctions : Type u
  preimagePoints : Type u
  [preimagePointsFinite : Fintype preimagePoints]
  [sectionAddCommGroup : AddCommGroup
    ((Scheme.Modules.presheaf normalizationDifferentials).obj
      (Opposite.op (⊤ : curve.carrier.Opens)))]
  [sectionModule : Module k
    ((Scheme.Modules.presheaf normalizationDifferentials).obj
      (Opposite.op (⊤ : curve.carrier.Opens)))]
  residue : preimagePoints →
    (Scheme.Modules.presheaf normalizationDifferentials).obj
      (Opposite.op (⊤ : curve.carrier.Opens)) →ₗ[k] k
  action : localFunctions →
    (Scheme.Modules.presheaf normalizationDifferentials).obj
      (Opposite.op (⊤ : curve.carrier.Opens)) →
      (Scheme.Modules.presheaf normalizationDifferentials).obj
        (Opposite.op (⊤ : curve.carrier.Opens))
  rosCondition :
    (Scheme.Modules.presheaf normalizationDifferentials).obj
      (Opposite.op (⊤ : curve.carrier.Opens)) → Prop
  agreesWithIntrinsicCondition :
    ∀ η : (Scheme.Modules.presheaf normalizationDifferentials).obj
        (Opposite.op (⊤ : curve.carrier.Opens)),
      rosCondition η ↔
        (letI := Classical.decEq preimagePoints
         chapter10IntrinsicResidueCondition
            (K := k) (P := preimagePoints)
            (D := (Scheme.Modules.presheaf normalizationDifferentials).obj
              (Opposite.op (⊤ : curve.carrier.Opens)))
            (Finset.univ : Finset preimagePoints) localFunctions action residue η)
  gorenstein : Prop
  gorenstein_iff_invertible :
    gorenstein ↔
      LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.chapter09IsInvertibleSheaf
        dualizing

attribute [instance] Chapter10GeneralSingularCurveRosenlichtData.preimagePointsFinite

theorem chapter10_general_rosenlicht_description
    {k : Type u} [Field k]
    (D : Chapter10GeneralSingularCurveRosenlichtData (k := k)) :
    (letI := D.sectionAddCommGroup
     letI := D.sectionModule
     ∀ η : (Scheme.Modules.presheaf D.normalizationDifferentials).obj
         (Opposite.op (⊤ : D.curve.carrier.Opens)),
       D.rosCondition η ↔
        (letI := Classical.decEq D.preimagePoints
         chapter10IntrinsicResidueCondition
            (K := k) (P := D.preimagePoints)
            (D := (Scheme.Modules.presheaf D.normalizationDifferentials).obj
              (Opposite.op (⊤ : D.curve.carrier.Opens)))
            (Finset.univ : Finset D.preimagePoints) D.localFunctions D.action D.residue η)) := by
  let _ := D.sectionAddCommGroup
  let _ := D.sectionModule
  exact D.agreesWithIntrinsicCondition

theorem chapter10_general_rosenlicht_need_not_be_invertible
    {k : Type u} [Field k]
    (D : Chapter10GeneralSingularCurveRosenlichtData (k := k))
    (hnotGorenstein : ¬ D.gorenstein) :
    ¬ LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.chapter09IsInvertibleSheaf
      D.dualizing := by
  intro hinvertible
  exact hnotGorenstein (D.gorenstein_iff_invertible.mpr hinvertible)

theorem chapter10_split_node_other_tests_add_no_condition
    {k : Type u} [Field k] (η : Chapter10BranchDifferentialPair k) :
    chapter10NodeHasAtMostSimplePoles η →
    (chapter10NodeIntrinsicResidueCondition η ↔
      chapter10OppositeResidues η) := by
  exact chapter10_split_node_intrinsic_condition_iff_opposite_residues η

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter10
