import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.Dependencies
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory

/-!
## 2.2 Invertible quotients

For a morphism `f : T ⟶ S`, the universal property identifies morphisms from `T` to the relative
projective bundle with isomorphism classes of invertible quotients of `f^*E`.  The quotient-pair
and quotient-class types come from `Dependencies.lean`; this section supplies the universal
equivalence and the base-change square.
-/

abbrev Chapter02ProjectiveBundlePoint
    {S T : Scheme.{u}} {E : Chapter02QuasiCoherentModule S}
    (P : Chapter02ProjectiveBundleData S E) (f : T ⟶ S) :=
  {u : T ⟶ P.scheme // u ≫ P.projection = f}

/- LOCAL_DEPENDENCY_GUESS: the universal property of relative Proj. -/
theorem chapter02_projective_bundle_universal_equiv_exists
    {S T : Scheme.{u}} {E : Chapter02QuasiCoherentModule S}
    (P : Chapter02ProjectiveBundleData S E) (f : T ⟶ S) :
    Nonempty (Chapter02ProjectiveBundlePoint P f ≃
      Chapter02InvertibleQuotientClass (chapter02PullbackModule f E)) := by
  exact ⟨P.universalProperty f⟩

noncomputable def chapter02ProjectiveBundleUniversalEquiv
    {S T : Scheme.{u}} {E : Chapter02QuasiCoherentModule S}
    (P : Chapter02ProjectiveBundleData S E) (f : T ⟶ S) :
    Chapter02ProjectiveBundlePoint P f ≃
      Chapter02InvertibleQuotientClass (chapter02PullbackModule f E) :=
  P.universalProperty f

def chapter02UniversalQuotientClassOfPoint
    {S T : Scheme.{u}} {E : Chapter02QuasiCoherentModule S}
    (P : Chapter02ProjectiveBundleData S E) (f : T ⟶ S)
    (u : Chapter02ProjectiveBundlePoint P f) :
    Chapter02InvertibleQuotientClass (chapter02PullbackModule f E) :=
  chapter02ProjectiveBundleUniversalEquiv P f u

theorem chapter02_projective_bundle_universal_equiv_injective
    {S T : Scheme.{u}} {E : Chapter02QuasiCoherentModule S}
    (P : Chapter02ProjectiveBundleData S E) (f : T ⟶ S)
    {u v : Chapter02ProjectiveBundlePoint P f}
    (h : chapter02UniversalQuotientClassOfPoint P f u =
      chapter02UniversalQuotientClassOfPoint P f v) :
    u = v := by
  exact (chapter02ProjectiveBundleUniversalEquiv P f).injective h

/-!
The representative statement spells out the direction of the universal quotient.  Its line is
`u^*𝒪(1)` and its quotient is obtained by pulling back the universal quotient, after the canonical
comparison between pullback along `u ≫ P.projection` and iterated pullback.
-/
theorem chapter02_universal_point_is_pullback_universal_quotient
    {S T : Scheme.{u}} {E : Chapter02QuasiCoherentModule S}
    (P : Chapter02ProjectiveBundleData S E) (u : T ⟶ P.scheme) :
    ∃ p : Chapter02InvertibleQuotientPair
        (chapter02PullbackModule (u ≫ P.projection) E),
      chapter02ProjectiveBundleUniversalEquiv P (u ≫ P.projection) ⟨u, rfl⟩ =
          chapter02QuotientClassMk p ∧
      ∃ e : p.line.carrier ≅ (Scheme.Modules.pullback u).obj P.twistingLineBundle.carrier,
        p.quotient ≫ e.hom =
          (chapter02PullbackCompositionIso u P.projection E.carrier).hom ≫
            (Scheme.Modules.pullback u).map P.universalQuotient := by
  let point : Chapter02ProjectiveBundlePoint P (u ≫ P.projection) := ⟨u, rfl⟩
  obtain ⟨p, hp, e, he⟩ :=
    P.universalProperty_compatible (u ≫ P.projection) point
  dsimp [point] at e he
  refine ⟨p, ?_, e, ?_⟩
  · change P.universalProperty (u ≫ P.projection) ⟨u, rfl⟩ = _
    rw [show (⟨u, rfl⟩ : Chapter02ProjectiveBundlePoint P (u ≫ P.projection)) = point by
      apply Subtype.ext
      rfl]
    exact hp
  · simpa [chapter02PullbackModule, chapter02PullbackCompositionIso,
      Scheme.Modules.pullbackCongr] using he

/-!
This data structure is the precise commutative square expressing compatibility with base change:
points are postcomposed with `g`, quotient classes are pulled back, and the universal equivalences
commute.  It is deliberately independent of a particular implementation of tensor products.
-/
structure Chapter02UniversalBaseChangeData
    {S T U : Scheme.{u}} {E : Chapter02QuasiCoherentModule S}
    (P : Chapter02ProjectiveBundleData S E) (f : T ⟶ S) (g : U ⟶ T) where
  pointMap : Chapter02ProjectiveBundlePoint P f →
    Chapter02ProjectiveBundlePoint P (g ≫ f)
  pointMap_eq_comp : ∀ u, (pointMap u).1 = g ≫ u.1
  classMap : Chapter02InvertibleQuotientClass (chapter02PullbackModule f E) →
    Chapter02InvertibleQuotientClass (chapter02PullbackModule (g ≫ f) E)
  classMap_is_pullback : ∀ p : Chapter02InvertibleQuotientPair (chapter02PullbackModule f E),
    classMap (chapter02QuotientClassMk p) =
      chapter02QuotientClassMk
        (chapter02PullbackInvertibleQuotientPairAlongComposition g f p)
  commutes : ∀ u,
    classMap (chapter02UniversalQuotientClassOfPoint P f u) =
      chapter02UniversalQuotientClassOfPoint P (g ≫ f) (pointMap u)

/- LOCAL_DEPENDENCY_GUESS: pullback of quotient pairs and the comparison isomorphism. -/
theorem chapter02_universal_base_change_data_exists
    {S T U : Scheme.{u}} {E : Chapter02QuasiCoherentModule S}
    (P : Chapter02ProjectiveBundleData S E) (f : T ⟶ S) (g : U ⟶ T) :
    Nonempty (Chapter02UniversalBaseChangeData P f g) := by
  sorry

noncomputable def chapter02UniversalBaseChangeData
    {S T U : Scheme.{u}} {E : Chapter02QuasiCoherentModule S}
    (P : Chapter02ProjectiveBundleData S E) (f : T ⟶ S) (g : U ⟶ T) :
    Chapter02UniversalBaseChangeData P f g :=
  Classical.choice (chapter02_universal_base_change_data_exists P f g)

theorem chapter02_projective_bundle_universal_property_base_change
    {S T U : Scheme.{u}} {E : Chapter02QuasiCoherentModule S}
    (P : Chapter02ProjectiveBundleData S E) (f : T ⟶ S) (g : U ⟶ T)
    (u : Chapter02ProjectiveBundlePoint P f) :
    (chapter02UniversalBaseChangeData P f g).classMap
        (chapter02UniversalQuotientClassOfPoint P f u) =
      chapter02UniversalQuotientClassOfPoint P (g ≫ f)
        ((chapter02UniversalBaseChangeData P f g).pointMap u) := by
  exact (chapter02UniversalBaseChangeData P f g).commutes u

/-! An `E` of finite locally free rank `r+1` gives a projective, finitely presented morphism.  The
projective-morphism predicate uses Mathlib's `IsClosedImmersion` and the shared relative
projective-bundle interface, so it also covers nontrivial finite locally free bundles over the base.

The finite locally free condition itself is declared in `Dependencies.lean` so later chapters can
reuse the same interface without importing this section.
-/

def Chapter02FiniteTypeMorphism {S X : Scheme.{u}} (f : X ⟶ S) : Prop :=
  QuasiCompact f ∧ LocallyOfFiniteType f

def Chapter02FinitePresentationMorphism {S X : Scheme.{u}} (f : X ⟶ S) : Prop :=
  QuasiCompact f ∧ QuasiSeparated f ∧ LocallyOfFinitePresentation f

theorem chapter02_projective_bundle_is_projective_and_finitely_presented
    {S : Scheme.{u}} {E : Chapter02QuasiCoherentModule S}
    (P : Chapter02ProjectiveBundleData S E) (r : ℕ)
    (hE : Chapter02LocallyFreeRank E.carrier (r + 1)) :
    Chapter02ProjectiveMorphism P.projection ∧
      Chapter02FinitePresentationMorphism P.projection := by
  sorry

theorem chapter02_projective_bundle_is_finite_type
    {S : Scheme.{u}} {E : Chapter02QuasiCoherentModule S}
    (P : Chapter02ProjectiveBundleData S E) (r : ℕ)
    (hE : Chapter02LocallyFreeRank E.carrier (r + 1)) :
    Chapter02FiniteTypeMorphism P.projection := by
  sorry

/-!
The finite locally free hypothesis is essential for finite presentation.  The following
book-facing predicate and counterexample statement preserve the warning for arbitrary infinite
quasi-coherent modules.
-/
def Chapter02ModuleIsFiniteType {S : Scheme.{u}}
    (E : Chapter02QuasiCoherentModule S) : Prop :=
  E.carrier.IsFiniteType

def Chapter02ModuleIsFinitePresentation {S : Scheme.{u}}
    (E : Chapter02QuasiCoherentModule S) : Prop :=
  E.carrier.IsFinitePresentation

theorem chapter02_arbitrary_quasi_coherent_projective_bundle_need_not_be_finite_type :
    ∃ (S : Scheme.{u}) (E : Chapter02QuasiCoherentModule S),
      ¬ Chapter02ModuleIsFiniteType E ∧
        ¬ Chapter02FiniteTypeMorphism (chapter02ProjectiveBundleProjection S E) := by
  sorry

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02
