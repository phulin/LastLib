import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter14.Dependencies

/-!
# Book 8, Chapter 14, §14.1: the three dictionaries

This leaf records the translations in the three displayed tables.  The first
table uses the absolute `Proj` API supplied by Mathlib; the relative quotient,
Hilbert, and symmetric-power entries retain explicit local dependency guesses.
-/

noncomputable section

universe u_chart

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter14

open CategoryTheory
open AlgebraicGeometry

/-! ## The graded-algebra dictionary -/

/-- The affine chart calculation `(A_f)₀ ≃ Γ(D₊(f), 𝒪)` in scheme form. -/
noncomputable def chapter14StandardOpenIsoSpec
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : Chapter14GradedAlgebra A σ) {n : ℕ} (f : A)
    (hf : f ∈ G.component n) (hn : 0 < n) :
    (chapter14StandardOpen G f).toScheme ≅
      AlgebraicGeometry.Spec (CommRingCat.of (chapter14ChartRing G f)) := by
  exact AlgebraicGeometry.Proj.basicOpenIsoSpec G.component f hf hn

@[simp]
theorem chapter14_standard_open_chart_is_affine
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : Chapter14GradedAlgebra A σ) {n : ℕ} (f : A)
    (hf : f ∈ G.component n) (hn : 0 < n) :
    IsAffineOpen (chapter14StandardOpen G f) := by
  exact AlgebraicGeometry.Proj.isAffineOpen_basicOpen G.component f hf hn

/-- The local form of `M(n) ↔ ẼM(n)` on every standard affine chart.

The two sides live in different categories globally, so the proof-ready bridge
is deliberately stated on sections over the affine chart. -/

structure Chapter14GradedModuleChartData (M : Type*) where
  shiftedModule : ℤ → Type u_chart
  standardOpenSections : ℤ → Type u_chart
  shiftedModule_to_tildeSections :
    ∀ n, Nonempty (shiftedModule n ≃ standardOpenSections n)

/-- The homogeneous-quotient row of the first dictionary. -/
abbrev chapter14HomogeneousIdeal
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : Chapter14GradedAlgebra A σ) := HomogeneousIdeal G.component

/- LOCAL_DEPENDENCY_GUESS: the preceding Book08 Proj construction supplies the quotient
graded ring and its canonical map.  Mathlib's pinned tree has the closed-immersion
criterion, but not the book-facing homogeneous quotient constructor. -/
noncomputable def chapter14HomogeneousQuotientProj
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : Chapter14GradedAlgebra A σ) (I : chapter14HomogeneousIdeal G) : Scheme := by
  sorry

noncomputable def chapter14HomogeneousQuotientMap
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : Chapter14GradedAlgebra A σ) (I : chapter14HomogeneousIdeal G) :
    chapter14HomogeneousQuotientProj G I ⟶ chapter14Proj G := by
  sorry

theorem chapter14_homogeneous_quotient_is_closed_projective_subscheme
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : Chapter14GradedAlgebra A σ) (I : chapter14HomogeneousIdeal G) :
    IsClosedImmersion (chapter14HomogeneousQuotientMap G I) := by
  sorry

/-- The Veronese row: the source and Veronese Proj objects. -/
noncomputable def chapter14VeroneseProj
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : Chapter14GradedAlgebra A σ) (d : ℕ) (V : Chapter14VeroneseData G d) : Scheme :=
  by
    letI := V.graded
    exact AlgebraicGeometry.Proj (chapter14VeroneseComponent G d)

/- LOCAL_DEPENDENCY_GUESS: the pinned graded-algebra API exposes the Veronese component
family but not the projective-spectrum equivalence used by the book. -/
theorem chapter14_veronese_has_the_same_proj
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : Chapter14GradedAlgebra A σ) (d : ℕ) (V : Chapter14VeroneseData G d)
    (hd : 0 < d) :
    Nonempty (chapter14Proj G ≅ chapter14VeroneseProj G d V) := by
  sorry

/-- Pullback of a book-facing line bundle along a scheme morphism. -/
noncomputable def chapter14PullbackLineBundle
    {X Y : Scheme} (f : X ⟶ Y) (L : Chapter14LineBundle Y) :
    Chapter14LineBundle X := by
  refine
    { sheaf := (Scheme.Modules.pullback f).obj L.sheaf
      isInvertible := ?_ }
  sorry

/-- The sheaf-level comparison used to say that the Veronese changes `𝒪(1)` to `𝒪(d)`. -/
def chapter14HigherTwistCorrespondence
    {X Y : Scheme} (f : X ⟶ Y)
    (L_X : Chapter14LineBundle X) (L_Y : Chapter14LineBundle Y) : Prop :=
  Nonempty ((Scheme.Modules.pullback f).obj L_Y.sheaf ≅ L_X.sheaf)

def chapter14VeroneseHigherTwistStatement
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : Chapter14GradedAlgebra A σ) (d : ℕ) (V : Chapter14VeroneseData G d)
    (f : chapter14Proj G ⟶ chapter14VeroneseProj G d V)
    (twistG : Chapter14TwistingSheafFamily (chapter14Proj G))
    (twistV : Chapter14TwistingSheafFamily (chapter14VeroneseProj G d V)) : Prop :=
  chapter14HigherTwistCorrespondence f (twistG.sheaf (d : ℤ)) (twistV.sheaf 1)

/-! ## The positivity dictionary -/

def chapter14EventualGlobalGeneration
    {X : Scheme} (O : Chapter14PositivityOperations X)
    (F : O.coefficientSheaf) (L : Chapter14LineBundle X) : Prop :=
  chapter14EventuallyHolds (fun n =>
    O.globallyGenerated (O.twist F (O.tensorPower L n)))

def chapter14EventualSerreVanishing
    {X : Scheme} (O : Chapter14PositivityOperations X)
    (F : O.coefficientSheaf) (L : Chapter14LineBundle X) : Prop :=
  chapter14EventuallyHolds (fun n =>
    ∀ i : ℕ, 0 < i →
      O.higherCohomologyVanishes (O.twist F (O.tensorPower L n)) i)

def chapter14HasVeryAmplePower
    {X : Scheme} (O : Chapter14PositivityOperations X)
    (L : Chapter14LineBundle X) : Prop :=
  ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → O.veryAmple (O.tensorPower L n)

def chapter14PositivityDictionaryStatement
    {X : Scheme} (O : Chapter14PositivityOperations X)
    (F : O.coefficientSheaf) (L : Chapter14LineBundle X) : Prop :=
  O.ample L →
    chapter14EventualGlobalGeneration O F L ∧
      chapter14EventualSerreVanishing O F L ∧
        chapter14HasVeryAmplePower O L

/- LOCAL_DEPENDENCY_GUESS: the preceding chapters instantiate the operations in
`Chapter14PositivityOperations` with affine nonvanishing, Serre vanishing, and
relative very-ampleness.  The following theorem is the book-facing bridge. -/
theorem chapter14_ample_bundle_gives_the_three_asymptotic_forms
    {X : Scheme} (O : Chapter14PositivityOperations X)
    (F : O.coefficientSheaf) (L : Chapter14LineBundle X) :
    chapter14PositivityDictionaryStatement O F L := by
  sorry

def chapter14VeryAmplePowerEmbeddingStatement
    {X S : Scheme} (f : X ⟶ S)
    (O : Chapter14PositivityOperations X) (L : Chapter14LineBundle X) (n : ℕ) : Prop :=
  O.veryAmple (O.tensorPower L n) →
    ∃ D : Chapter14ProjectiveMorphismData f, D.ambientIsProjectiveBundle

/- LOCAL_DEPENDENCY_GUESS: relative very-ampleness identifies the ambient projective
bundle with the one formed from the finite locally free pushforward of `L^n`. -/
theorem chapter14_very_ample_power_gives_projective_embedding
    {X S : Scheme} (f : X ⟶ S)
    (O : Chapter14PositivityOperations X) (L : Chapter14LineBundle X) (n : ℕ) :
    chapter14VeryAmplePowerEmbeddingStatement f O L n := by
  sorry

/-- A fiberwise polynomial together with the precise flat-family interpretation it carries. -/
structure Chapter14FiberHilbertPolynomialData {X S : Scheme} (f : X ⟶ S) where
  family : Chapter14ProjectiveFlatFamilyData f
  polarization : Chapter14LineBundle X
  polynomial : S → Polynomial ℚ
  coefficientSheaf : Chapter14CoherentSheaf X
  coefficientFlatOverBase : Prop
  polynomial_is_fiber_hilbert_polynomial : Prop

/- LOCAL_DEPENDENCY_GUESS: this is the flatness-to-constancy theorem from the preceding
Hilbert-polynomial sections, with the polynomial kept relative to the chosen polarization. -/
theorem chapter14_flat_family_has_locally_constant_fiber_polynomial
    {X S : Scheme} {f : X ⟶ S}
    (H : Chapter14FiberHilbertPolynomialData f) :
    chapter14LocallyConstant H.polynomial := by
  sorry

/-! ## The parameter-space dictionary -/

/- LOCAL_DEPENDENCY_GUESS: finite products in `Over S` and the invariant quotient
construction are supplied by the earlier relative-geometry chapters. -/
noncomputable def chapter14OrderedTupleFunctor {S : Scheme.{u}} (X : Over S) (d : ℕ) :
    Chapter14RelativeFunctor S where
  obj T := Fin d → (yoneda.obj X).obj T
  map := fun {T U} (f : T ⟶ U) =>
    TypeCat.ofHom (fun (x : Fin d → (yoneda.obj X).obj T) i =>
      (yoneda.obj X).map f (x i))
  map_id := by
    intro T
    ext x i
    simp
  map_comp := by
    intros T U V f g
    ext x i
    simp

noncomputable def chapter14PermutationQuotientFunctor {S : Scheme.{u}}
    (X : Over S) (d : ℕ) : Chapter14RelativeFunctor S := by
  sorry

noncomputable def chapter14FiniteLengthHilbertFunctor {S : Scheme.{u}}
    (X : Over S) (d : ℕ) : Chapter14RelativeFunctor S := by
  sorry

noncomputable def chapter14FixedPolynomialHilbertFunctor {S : Scheme.{u}}
    (X : Over S) (P : Polynomial ℚ) : Chapter14RelativeFunctor S := by
  sorry

/- The representing objects are kept separate from their universal families. -/
structure Chapter14ThreeDictionaryRepresentations {S : Scheme.{u}}
    (X : Over S) (d : ℕ) (P : Polynomial ℚ) where
  orderedTuple : Over S
  orderedTuple_represents :
    chapter14RepresentedBy (chapter14OrderedTupleFunctor X d) orderedTuple
  permutationQuotient : Over S
  permutationQuotient_represents :
    chapter14RepresentedBy (chapter14PermutationQuotientFunctor X d) permutationQuotient
  finiteLengthHilbert : Over S
  finiteLengthHilbert_represents :
    chapter14RepresentedBy (chapter14FiniteLengthHilbertFunctor X d) finiteLengthHilbert
  fixedPolynomialHilbert : Over S
  fixedPolynomialHilbert_represents :
    chapter14RepresentedBy (chapter14FixedPolynomialHilbertFunctor X P) fixedPolynomialHilbert

def chapter14CurveHilbertSymmetricAgreement
    {C S Z : Scheme} (f : C ⟶ S) (_curve : Chapter14SmoothRelativeCurveData f)
    (d : ℕ) (hilbertObject symmetricObject : Over S)
    (D : Chapter14FiniteFlatFamilyData (Z := Z) f hilbertObject.hom) : Prop :=
  Nonempty (hilbertObject ≅ symmetricObject) ∧ D.rank = d

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter14
