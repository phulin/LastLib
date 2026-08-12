import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter14.Section02TheReusableTheoremPackage

/-!
# Book 8, Chapter 14, §14.3: conclusion and boundary checklist

The final section is mostly synthesis prose.  Its mathematically precise
boundaries are recorded here so later users cannot silently drop the
finiteness, flatness, separatedness, smoothness, or polarization hypotheses.
-/

noncomputable section

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter14

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

/-! ## Proper immersions, graphs, and bounded equations -/

/- LOCAL_DEPENDENCY_GUESS: Mathlib supplies properness and immersion separately; the
standard scheme-theoretic lemma that a proper immersion is a closed immersion is the
bridge used by the source conclusion. -/
theorem chapter14_proper_immersion_is_closed_immersion
    {X Y : Scheme} (f : X ⟶ Y) [IsProper f] [IsImmersion f] :
    IsClosedImmersion f := by
  sorry

/- A graph datum keeps the canonical graph equations and separatedness explicit. -/
structure Chapter14GraphData {X Y : Scheme} (u : X ⟶ Y) where
  graph : X ⟶ Limits.prod X Y
  targetSeparated : Y.IsSeparated
  graph_is_graph_of_u :
    graph ≫ Limits.prod.fst = 𝟙 X ∧ graph ≫ Limits.prod.snd = u

/- LOCAL_DEPENDENCY_GUESS: the graph is the pullback of the diagonal of the separated
target, hence the following closedness statement is stable under every base change. -/
theorem chapter14_graph_of_a_map_to_a_separated_target_is_closed
    {X Y : Scheme} {u : X ⟶ Y} (D : Chapter14GraphData u) :
    IsClosedImmersion D.graph := by
  sorry

/-- The finite-length flat family as a relative effective Cartier divisor. -/
structure Chapter14EffectiveCartierDivisorData {C S P Z : Scheme}
    (f : C ⟶ S) (p : P ⟶ S)
    (D : Chapter14FiniteFlatFamilyData (Z := Z) f p) where
  effectiveCartier : Prop

/- SOURCE_ISSUE (§14.3): the conclusion says “smoothness of a curve turns finite
   subschemes into Cartier divisors,” but finite flatness over the base is also
   required.  A finite non-flat subscheme of a smooth relative curve need not
   be an effective Cartier divisor; the smallest correction is “smoothness of
   a curve turns finite flat subschemes into effective Cartier divisors.” -/
/- LOCAL_DEPENDENCY_GUESS: smoothness in relative dimension one identifies finite flat
subschemes with effective Cartier divisors; this is false without the smooth-curve boundary. -/
theorem chapter14_smooth_relative_curve_turns_finite_subschemes_into_cartier_divisors
    {C S P Z : Scheme} {f : C ⟶ S} {p : P ⟶ S}
    (curve : Chapter14SmoothRelativeCurveData f)
    (D : Chapter14FiniteFlatFamilyData (Z := Z) f p) :
    Nonempty (Chapter14EffectiveCartierDivisorData (Z := Z) f p D) := by
  sorry

/-- A finite group action with a quasi-projective ambient scheme. -/
structure Chapter14FiniteQuotientInput (Y : Scheme) where
  group : Type*
  groupStructure : Group group
  groupFinite : Finite group
  action : group → (Y ⟶ Y)
  action_is_group_action : Prop
  quasiProjective : Prop

/- LOCAL_DEPENDENCY_GUESS: the invariant affine charts and their gluing give the finite
categorical quotient for a finite action on a quasi-projective scheme. -/
noncomputable def chapter14FiniteGroupQuotient
    {Y : Scheme} (D : Chapter14FiniteQuotientInput Y) : Scheme := by
  sorry

noncomputable def chapter14FiniteGroupQuotientMap
    {Y : Scheme} (D : Chapter14FiniteQuotientInput Y) :
    Y ⟶ chapter14FiniteGroupQuotient D := by
  sorry

theorem chapter14_quasi_projective_finite_group_quotient_exists
    {Y : Scheme} (D : Chapter14FiniteQuotientInput Y) :
    IsFinite (chapter14FiniteGroupQuotientMap D) ∧
      Surjective (chapter14FiniteGroupQuotientMap D) := by
  sorry

/-! ## The six boundaries in the concluding checklist -/

/-- Precise checklist of the hypotheses named in the conclusion. -/
structure Chapter14BoundaryChecklist where
  noetherianFinitenessBoundsEquations : Prop
  properImmersionsAreClosed : Prop
  flatnessPreservesFiberPolynomial : Prop
  smoothCurvesMakeFiniteSubschemesCartier : Prop
  separatedTargetsMakeGraphsClosed : Prop
  quasiProjectivityMakesFiniteQuotientsSchemes : Prop
  polarizationChosenForNonconstantHilbertPolynomial : Prop

/-- Constant geometric fiber length alone is weaker than a flat family. -/
def chapter14ConstantGeometricFiberLength
    {S : Type*} (length : S → ℕ) (d : ℕ) : Prop :=
  ∀ s, length s = d

def chapter14FlatLengthFamilyCondition
    (constantLength flatOverBase : Prop) : Prop :=
  constantLength ∧ flatOverBase

/-- A polynomial is recorded together with the polarization relative to which it is measured. -/
structure Chapter14PolarizedHilbertPolynomialData (X : Scheme) where
  polarization : Chapter14LineBundle X
  polynomial : Polynomial ℚ

/- The source's final uniformity slogan is represented by the reusable package rather than
repeated as a second theorem with weaker hypotheses. -/
structure Chapter14SynthesisPackage where
  gradedDictionary : Prop
  positivityDictionary : Prop
  parameterDictionary : Prop
  boundaryChecklist : Chapter14BoundaryChecklist

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter14
