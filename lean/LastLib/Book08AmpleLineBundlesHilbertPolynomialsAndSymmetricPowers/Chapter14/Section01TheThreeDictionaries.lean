import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter14.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08.Section01FiberwiseEulerCharacteristics
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08.Section02FlatnessForcesConstancy

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
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08

/-! ## The graded-algebra dictionary -/

/-- The affine chart calculation `(A_f)₀ ≃ Γ(D₊(f), 𝒪)` in scheme form. -/
noncomputable def chapter14StandardOpenIsoSpec
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : Chapter14GradedAlgebra A σ) {n : ℕ} (f : A)
    (hf : f ∈ G.component n) (hn : 0 < n) :
    (chapter14StandardOpen G f hf hn).toScheme ≅
      AlgebraicGeometry.Spec (CommRingCat.of (chapter14ChartRing G f hf hn)) := by
  exact AlgebraicGeometry.Proj.basicOpenIsoSpec G.component f hf hn

@[simp]
theorem chapter14_standard_open_chart_is_affine
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : Chapter14GradedAlgebra A σ) {n : ℕ} (f : A)
    (hf : f ∈ G.component n) (hn : 0 < n) :
    IsAffineOpen (chapter14StandardOpen G f hf hn) := by
  exact AlgebraicGeometry.Proj.isAffineOpen_basicOpen G.component f hf hn

/-- The local form of `M(n) ↔ ẼM(n)` on every standard affine chart.

The two sides live in different categories globally, so the proof-ready bridge
is deliberately stated on sections over the affine chart. -/

structure Chapter14GradedModuleChartData (M : ℤ → Type u_chart) where
  standardOpenSections : ℤ → Type u_chart
  shiftedModule_to_tildeSections :
    ∀ n, Nonempty (M n ≃ standardOpenSections n)

/-- The homogeneous-quotient row of the first dictionary. -/
abbrev chapter14HomogeneousIdeal
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : Chapter14GradedAlgebra A σ) := HomogeneousIdeal G.component

/- LOCAL_DEPENDENCY_GUESS: the preceding Book08 Proj construction supplies the quotient
graded ring and its canonical map.  The quotient algebra itself is kept as an
explicit witness until that construction is wired in, so the map below cannot
silently be chosen independently of `I`. -/
structure Chapter14HomogeneousQuotientData
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : Chapter14GradedAlgebra A σ) (I : chapter14HomogeneousIdeal G) where
  scheme : Scheme
  map : scheme ⟶ chapter14Proj G
  closed : IsClosedImmersion map

theorem chapter14_homogeneous_quotient_exists
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : Chapter14GradedAlgebra A σ) (I : chapter14HomogeneousIdeal G) :
    Nonempty (Chapter14HomogeneousQuotientData G I) := by
  sorry

noncomputable def chapter14HomogeneousQuotientData
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : Chapter14GradedAlgebra A σ) (I : chapter14HomogeneousIdeal G) :
    Chapter14HomogeneousQuotientData G I :=
  Classical.choice (chapter14_homogeneous_quotient_exists G I)

noncomputable def chapter14HomogeneousQuotientProj
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : Chapter14GradedAlgebra A σ) (I : chapter14HomogeneousIdeal G) : Scheme :=
  (chapter14HomogeneousQuotientData G I).scheme

noncomputable def chapter14HomogeneousQuotientMap
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : Chapter14GradedAlgebra A σ) (I : chapter14HomogeneousIdeal G) :
    chapter14HomogeneousQuotientProj G I ⟶ chapter14Proj G := by
  exact (chapter14HomogeneousQuotientData G I).map

theorem chapter14_homogeneous_quotient_is_closed_subscheme
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : Chapter14GradedAlgebra A σ) (I : chapter14HomogeneousIdeal G) :
    IsClosedImmersion (chapter14HomogeneousQuotientMap G I) := by
  exact (chapter14HomogeneousQuotientData G I).closed

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
    Chapter14LineBundle X :=
  chapter04PullbackLineBundle f L

/-- The sheaf-level comparison used to say that the Veronese changes `𝒪(1)` to `𝒪(d)`. -/
def chapter14HigherTwistCorrespondence
    {X Y : Scheme} (f : X ⟶ Y)
    (L_X : Chapter14LineBundle X) (L_Y : Chapter14LineBundle Y) : Prop :=
  Nonempty ((Scheme.Modules.pullback f).obj L_Y.sheaf ≅ L_X.sheaf)

def chapter14VeroneseHigherTwistStatement
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : Chapter14GradedAlgebra A σ) (d : ℕ) (V : Chapter14VeroneseData G d)
    (twistG : Chapter14TwistingSheafFamily (chapter14Proj G))
    (twistV : Chapter14TwistingSheafFamily (chapter14VeroneseProj G d V)) : Prop :=
  ∃ e : chapter14Proj G ≅ chapter14VeroneseProj G d V,
    chapter14HigherTwistCorrespondence e.hom (twistG.sheaf (d : ℤ)) (twistV.sheaf 1)

/-! ## The positivity dictionary -/

def chapter14EventualGlobalGeneration
    {X : Scheme} (O : Chapter14PositivityOperations X)
    (F : X.Modules) (_hF : chapter04FiniteTypeQuasiCoherent F)
    (L : Chapter14LineBundle X) : Prop :=
  chapter14EventuallyHolds (fun n =>
    O.globallyGenerated F L n)

def chapter14EventualSerreVanishing
    {X : Scheme} (O : Chapter14PositivityOperations X)
    (F : X.Modules) (_hF : chapter04FiniteTypeQuasiCoherent F)
    (L : Chapter14LineBundle X) : Prop :=
  chapter14EventuallyHolds (fun n =>
    ∀ i : ℕ, 0 < i →
      O.higherCohomologyVanishes F L n i)

def chapter14HasVeryAmplePower
    {X : Scheme} (O : Chapter14PositivityOperations X)
    (L : Chapter14LineBundle X) : Prop :=
  ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    O.veryAmple (O.tensorPower L n)

def chapter14PositivityDictionaryStatement
    {X : Scheme} (O : Chapter14PositivityOperations X)
    (F : X.Modules) (hF : chapter04FiniteTypeQuasiCoherent F)
    (L : Chapter14LineBundle X) : Prop :=
  O.ample L →
    chapter14EventualGlobalGeneration O F hF L ∧
      chapter14EventualSerreVanishing O F hF L ∧
        chapter14HasVeryAmplePower O L

/- LOCAL_DEPENDENCY_GUESS: the canonical Chapter 4 Serre and tensor-power theorems
consume the finiteness, noetherianity, projectivity, and relative-positivity fields
of `Chapter14PositivityOperations`.  The following theorem is the book-facing bridge. -/
theorem chapter14_ample_bundle_gives_the_three_asymptotic_forms
    {X : Scheme} (O : Chapter14PositivityOperations X)
    (F : X.Modules) (hF : chapter04FiniteTypeQuasiCoherent F)
    (L : Chapter14LineBundle X) :
    chapter14PositivityDictionaryStatement O F hF L := by
  intro hL
  refine ⟨?_, ?_, ?_⟩
  · change chapter04EventuallyTwistGenerated O.family F L
    exact (@chapter04_serre_generation_criterion X O.base O.family
      O.familyQuasiCompact O.familySeparated O.baseAffine L).mp hL F hF
  · change chapter04EventuallyHigherCohomologyVanishes O.family F L
    exact @chapter04_serre_vanishing X O.base O.family
      O.baseAffine O.baseNoetherian O.familyNoetherian O.familyQuasiCompact
      O.familySeparated O.projective L hL F hF
  · change ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      chapter04VeryAmple O.family (chapter04LineBundleTensorPower L n)
    haveI := O.baseAffine
    haveI := O.familyQuasiCompact
    haveI := O.familyLocallyOfFiniteType
    haveI := O.familyQuasiSeparated
    exact @chapter04_ample_eventually_veryAmple_power X O.base O.family
      inferInstance inferInstance inferInstance inferInstance L
      (show chapter04Ample O.family L from hL)

def chapter14VeryAmplePowerEmbeddingStatement
    {X : Scheme} (O : Chapter14PositivityOperations X)
    (L : Chapter14LineBundle X) (n : ℕ) : Prop :=
  O.veryAmple (O.tensorPower L n) →
    Nonempty (Chapter14VeryAmpleEmbeddingData (f := O.family) (O.tensorPower L n))

/- LOCAL_DEPENDENCY_GUESS: relative very-ampleness identifies the ambient projective
bundle with the one formed from the finite locally free pushforward of `L^n`. -/
theorem chapter14_very_ample_power_gives_very_ample_embedding
    {X : Scheme} (O : Chapter14PositivityOperations X)
    (L : Chapter14LineBundle X) (n : ℕ) :
    chapter14VeryAmplePowerEmbeddingStatement O L n := by
  intro hL
  rcases hL with ⟨W⟩
  let P : Chapter14ProjectiveBundleData O.base :=
    { toChapter04ProjectiveBundle := W.projectiveBundle }
  exact ⟨Chapter14VeryAmpleEmbeddingData.mk P W.map W.immersion W.over W.pullback_iso⟩

/- A fiberwise polynomial together with the precise flat-family interpretation it carries.
The Chapter 8 datum already identifies its values with Euler characteristics of the
actual scheme-theoretic fibers of its coefficient sheaf twisted by its polarization. -/
structure Chapter14FiberHilbertPolynomialData
    {F : LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08.Chapter08PolarizedFamily}
    (E : LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08.Chapter08FamilySheaf F) where
  fiberwiseHilbertData :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08.Chapter08FiberwiseHilbertData E
  coefficientFlatOverBase :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08.Chapter08FlatOver
      F.family.f E.sheaf
  /-- The relative Serre/base-change support needed to turn flatness into
      locally constant fiber Euler characteristics. -/
  serreVanishingBaseChange :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08.Chapter08SerreVanishingBaseChangeData
      E fiberwiseHilbertData

def Chapter14FiberHilbertPolynomialData.polynomial
    {F : LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08.Chapter08PolarizedFamily}
    {E : LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08.Chapter08FamilySheaf F}
    (H : Chapter14FiberHilbertPolynomialData E) :
    F.family.S →
      LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08.Chapter08NumericalPolynomial :=
  H.fiberwiseHilbertData.fiberPolynomial

def Chapter14FiberHilbertPolynomialData.fiberEulerCharacteristic
    {F : LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08.Chapter08PolarizedFamily}
    {E : LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08.Chapter08FamilySheaf F}
    (H : Chapter14FiberHilbertPolynomialData E) (s : F.family.S) (n : ℕ) : ℤ :=
  H.fiberwiseHilbertData.fiberwise_compatibility.fiberEulerCharacteristic s
    (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08.chapter08FiberTwistedSheaf E s n)

/- LOCAL_DEPENDENCY_GUESS: this is the flatness-to-constancy theorem from the preceding
Hilbert-polynomial sections, with the polynomial kept relative to the chosen polarization. -/
theorem chapter14_flat_family_has_locally_constant_fiber_polynomial
    {F : LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08.Chapter08PolarizedFamily}
    {E : LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08.Chapter08FamilySheaf F}
    (H : Chapter14FiberHilbertPolynomialData E) :
    chapter14LocallyConstant H.polynomial := by
  exact chapter08_hilbert_polynomial_locally_constant E H.fiberwiseHilbertData
    H.serreVanishingBaseChange H.coefficientFlatOverBase

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

/- The permutation quotient functor is the orbit presheaf, not an arbitrary
   functor chosen by the representability statement. -/
def chapter14TupleOrbitRelation {S : Scheme.{u}} {X : Over S} {T : (Over S)ᵒᵖ} (d : ℕ)
    (x y : Fin d → (yoneda.obj X).obj T) : Prop :=
  ∃ σ : Equiv.Perm (Fin d), ∀ i, x (σ i) = y i

def chapter14TupleOrbitSetoid {S : Scheme.{u}} (X : Over S) (T : (Over S)ᵒᵖ) (d : ℕ) :
    Setoid (Fin d → (yoneda.obj X).obj T) where
  r := chapter14TupleOrbitRelation d
  iseqv := by
    constructor
    · intro x
      refine ⟨1, ?_⟩
      intro i
      simp
    · intro x y hxy
      rcases hxy with ⟨σ, hσ⟩
      refine ⟨σ⁻¹, ?_⟩
      intro i
      simpa using (hσ (σ⁻¹ i)).symm
    · intro x y z hxy hyz
      rcases hxy with ⟨σ, hσ⟩
      rcases hyz with ⟨τ, hτ⟩
      refine ⟨σ * τ, ?_⟩
      intro i
      change x (σ (τ i)) = z i
      exact (hσ (τ i)).trans (hτ i)

noncomputable def chapter14PermutationQuotientFunctor {S : Scheme.{u}}
    (X : Over S) (d : ℕ) : Chapter14RelativeFunctor S := by
  refine
    { obj := fun T => Quotient (chapter14TupleOrbitSetoid X T d)
      map := fun {T U} (f : T ⟶ U) =>
        TypeCat.ofHom (Quotient.map
          (fun x i => (yoneda.obj X).map f (x i)) ?_)
      map_id := ?_
      map_comp := ?_ }
  · intro x y hxy
    change chapter14TupleOrbitRelation d x y at hxy
    rcases hxy with ⟨σ, hσ⟩
    change chapter14TupleOrbitRelation d _ _
    refine ⟨σ, ?_⟩
    intro i
    exact congrArg ((yoneda.obj X).map _) (hσ i)
  · intro T
    ext x
    refine Quotient.inductionOn x ?_
    intro x
    simp
  · intros T U V f g
    ext x
    refine Quotient.inductionOn x ?_
    intro x
    simp

noncomputable def chapter14FiniteLengthHilbertFunctor {S : Scheme.{u}}
    (X : Over S) (d : ℕ) : Chapter14RelativeFunctor S := by
  sorry

noncomputable def chapter14EffectiveCartierDivisorFunctor {S : Scheme.{u}}
    (X : Over S) (d : ℕ) : Chapter14RelativeFunctor S := by
  sorry

noncomputable def chapter14FixedPolynomialHilbertFunctor {S : Scheme.{u}}
    (X : Over S) (polarization : Chapter14LineBundle X.left)
    (P : Chapter14NumericalPolynomial) :
    Chapter14RelativeFunctor S := by
  sorry

/- The representing objects are kept separate from their universal families. -/
structure Chapter14ThreeDictionaryRepresentations {S : Scheme.{u}}
    (X : Over S) (polarization : Chapter14LineBundle X.left) (d : ℕ)
    (P : Chapter14NumericalPolynomial) where
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
    chapter14RepresentedBy
      (chapter14FixedPolynomialHilbertFunctor X polarization P) fixedPolynomialHilbert

def chapter14CurveHilbertSymmetricAgreement
    {C S Z : Scheme} (f : C ⟶ S) (_curve : Chapter14SmoothRelativeCurveData f)
    (d : ℕ) (hilbertObject symmetricObject : Over S)
    (D : Chapter14FiniteFlatFamilyData (Z := Z) f hilbertObject.hom) : Prop :=
  chapter14RepresentedBy
      (chapter14FiniteLengthHilbertFunctor (Over.mk f) d) hilbertObject ∧
    chapter14RepresentedBy
      (chapter14PermutationQuotientFunctor (Over.mk f) d) symmetricObject ∧
      Nonempty (hilbertObject ≅ symmetricObject) ∧ D.rank = d

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter14
