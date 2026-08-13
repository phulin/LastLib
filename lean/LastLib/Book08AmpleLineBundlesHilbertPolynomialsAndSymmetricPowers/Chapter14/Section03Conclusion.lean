import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter14.Section02TheReusableTheoremPackage
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.Dependencies

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
structure Chapter14GraphData {X Y S : Scheme}
    (x : X ⟶ S) (y : Y ⟶ S) (u : X ⟶ Y) where
  graph : X ⟶ Limits.pullback x y
  targetSeparated : IsSeparated y
  overBase : u ≫ y = x
  graph_fst : graph ≫ Limits.pullback.fst x y = 𝟙 X
  graph_snd : graph ≫ Limits.pullback.snd x y = u

/- LOCAL_DEPENDENCY_GUESS: the graph is the pullback of the diagonal of the separated
target, hence the following closedness statement is stable under every base change. -/
theorem chapter14_graph_of_a_map_to_a_separated_target_is_closed
    {X Y S : Scheme} {x : X ⟶ S} {y : Y ⟶ S} {u : X ⟶ Y}
    (D : Chapter14GraphData x y u) :
    IsClosedImmersion D.graph := by
  sorry

/-- The finite-length flat family as a relative effective Cartier divisor. -/
structure Chapter14EffectiveCartierDivisorData {C S P Z : Scheme}
    (f : C ⟶ S) (p : P ⟶ S)
    (D : Chapter14FiniteFlatFamilyData (Z := Z) f p) where
  divisor :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.EffectiveCartierDivisor
      (Limits.pullback f p)
  identification :
    ∃ e : Z ≅ divisor.subscheme,
      e.hom ≫ divisor.inclusion = D.ambientPullback
  degree :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.Chapter11FiniteLocallyFreeOfRank
      (divisor.inclusion ≫ Limits.pullback.snd f p) D.rank

/- The finite-flat hypothesis is part of `D`; it is not optional in the Cartier
   divisor identification. -/
/- LOCAL_DEPENDENCY_GUESS: smoothness in relative dimension one identifies finite flat
subschemes with effective Cartier divisors; this is false without the smooth-curve boundary. -/
theorem chapter14_smooth_relative_curve_turns_finite_flat_subschemes_into_cartier_divisors
    {C S P Z : Scheme} {f : C ⟶ S} {p : P ⟶ S}
    (curve : Chapter14SmoothRelativeCurveData f)
    (D : Chapter14FiniteFlatFamilyData (Z := Z) f p) :
    Nonempty (Chapter14EffectiveCartierDivisorData (Z := Z) f p D) := by
  sorry

/-- A finite group action with a quasi-projective ambient scheme. -/
structure Chapter14FiniteQuotientInput {S Y : Scheme} (y : Y ⟶ S) where
  group : Type*
  groupStructure : Group group
  groupFinite : Finite group
  action : group → (Over.mk y ⟶ Over.mk y)
  action_one : action 1 = 𝟙 (Over.mk y)
  action_mul : ∀ g h, action (g * h) = action g ≫ action h
  action_isIso : ∀ g, IsIso (action g)
  quasiProjective : Chapter14QuasiProjectiveMorphismData y
  finitePresentation : LocallyOfFinitePresentation y

/- The quotient carrier is kept together with its categorical universal property;
   finite and surjective are consequences, not the definition of a quotient. -/
structure Chapter14FiniteGroupQuotientData
    {S Y : Scheme} {y : Y ⟶ S} (D : Chapter14FiniteQuotientInput y) where
  quotient : Over S
  quotientMap : Over.mk y ⟶ quotient
  invariant : ∀ g, D.action g ≫ quotientMap = quotientMap
  universal : ∀ {Z : Over S} (h : Over.mk y ⟶ Z),
    (∀ g, D.action g ≫ h = h) →
      ∃! q : quotient ⟶ Z, quotientMap ≫ q = h
  integral : IsIntegralHom quotientMap.left
  finite : IsFinite quotientMap.left
  surjective : Surjective quotientMap.left
  quotientQuasiProjective : Chapter14QuasiProjectiveMorphismData quotient.hom

noncomputable def chapter14FiniteGroupQuotient
    {S Y : Scheme} {y : Y ⟶ S} (D : Chapter14FiniteQuotientInput y) :
    Chapter14FiniteGroupQuotientData D := by
  sorry

noncomputable def chapter14FiniteGroupQuotientMap
    {S Y : Scheme} {y : Y ⟶ S} (D : Chapter14FiniteQuotientInput y) :
    Over.mk y ⟶ (chapter14FiniteGroupQuotient D).quotient :=
  (chapter14FiniteGroupQuotient D).quotientMap

theorem chapter14_quasi_projective_finite_group_quotient_exists
    {S Y : Scheme} {y : Y ⟶ S} (D : Chapter14FiniteQuotientInput y) :
    IsFinite (chapter14FiniteGroupQuotientMap D).left ∧
      Surjective (chapter14FiniteGroupQuotientMap D).left ∧
        Nonempty (Chapter14QuasiProjectiveMorphismData
          (chapter14FiniteGroupQuotient D).quotient.hom) := by
  exact ⟨(chapter14FiniteGroupQuotient D).finite,
    (chapter14FiniteGroupQuotient D).surjective,
    ⟨(chapter14FiniteGroupQuotient D).quotientQuasiProjective⟩⟩

/-! ## The seven boundaries in the concluding checklist -/

/-- Precise checklist of the hypotheses named in the conclusion. -/
structure Chapter14BoundaryChecklist where
  noetherianFinitenessBoundsEquations : Prop
  properImmersionsAreClosed : Prop
  flatnessPreservesFiberPolynomial : Prop
  smoothCurvesMakeFiniteFlatSubschemesCartier : Prop
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
  polynomial : Chapter14NumericalPolynomial

/- The source's final uniformity slogan is represented by the reusable package rather than
repeated as a second theorem with weaker hypotheses. -/
structure Chapter14SynthesisPackage where
  gradedDictionary : Prop
  positivityDictionary : Prop
  parameterDictionary : Prop
  boundaryChecklist : Chapter14BoundaryChecklist

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter14
