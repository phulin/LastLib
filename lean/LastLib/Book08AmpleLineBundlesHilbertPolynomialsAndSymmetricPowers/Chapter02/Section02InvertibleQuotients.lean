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

theorem chapter02_projective_bundle_point_eq_iff
    {S T : Scheme.{u}} {E : Chapter02QuasiCoherentModule S}
    (P : Chapter02ProjectiveBundleData S E) (f : T ⟶ S)
    {u v : Chapter02ProjectiveBundlePoint P f} :
    u = v ↔
      chapter02UniversalQuotientClassOfPoint P f u =
        chapter02UniversalQuotientClassOfPoint P f v := by
  exact ⟨fun h => h ▸ rfl, chapter02_projective_bundle_universal_equiv_injective P f⟩

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
  obtain ⟨p, hp, e, he⟩ :=
    P.universalProperty_compatible (f := u ≫ P.projection) (u := ⟨u, rfl⟩)
  exact ⟨p, hp, e, he⟩

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

private noncomputable def chapter02UniversalBaseChangeClassMap
    {S T U : Scheme.{u}} {E : Chapter02QuasiCoherentModule S}
    (f : T ⟶ S) (g : U ⟶ T) :
    Chapter02InvertibleQuotientClass (chapter02PullbackModule f E) ⟶
      Chapter02InvertibleQuotientClass (chapter02PullbackModule (g ≫ f) E) := by
  change Chapter02InvertibleQuotientClass ((Scheme.Modules.pullback f).obj E.carrier) ⟶
    Chapter02InvertibleQuotientClass ((Scheme.Modules.pullback (g ≫ f)).obj E.carrier)
  refine TypeCat.ofHom ?_
  refine Quotient.lift
    (fun p : Chapter02InvertibleQuotientPair ((Scheme.Modules.pullback f).obj E.carrier) =>
      chapter02QuotientClassMk
        (chapter02PullbackInvertibleQuotientPairAlongComposition g f p)) ?_
  intro p q h
  apply Quotient.sound
  obtain ⟨e, he⟩ := h
  let e' := (Scheme.Modules.pullback g).mapIso e
  refine ⟨e', ?_⟩
  change ((chapter02PullbackCompositionIso g f E.carrier).hom ≫
      (Scheme.Modules.pullback g).map p.quotient) ≫ e'.hom =
    (chapter02PullbackCompositionIso g f E.carrier).hom ≫
      (Scheme.Modules.pullback g).map q.quotient
  change (chapter02PullbackCompositionIso g f E.carrier).hom ≫
      ((Scheme.Modules.pullback g).map p.quotient ≫
        (Scheme.Modules.pullback g).map e.hom) = _
  rw [← (Scheme.Modules.pullback g).map_comp, he]

/- LOCAL_DEPENDENCY_GUESS: pullback of quotient pairs and the comparison isomorphism. -/
theorem chapter02_universal_base_change_data_exists
    {S T U : Scheme.{u}} {E : Chapter02QuasiCoherentModule S}
    (P : Chapter02ProjectiveBundleData S E) (f : T ⟶ S) (g : U ⟶ T) :
    Nonempty (Chapter02UniversalBaseChangeData P f g) := by
  let classMap := chapter02UniversalBaseChangeClassMap (E := E) f g
  refine ⟨{
    pointMap := fun u => chapter02ProjectiveBundlePointPostcompose P.projection f g u
    pointMap_eq_comp := fun u => rfl
    classMap := classMap
    classMap_is_pullback := ?_
    commutes := ?_ }⟩
  · intro p
    rfl
  · intro u
    change classMap (P.universalProperty f u) =
      P.universalProperty (g ≫ f)
        (chapter02ProjectiveBundlePointPostcompose P.projection f g u)
    obtain ⟨p, hp, hnat⟩ := P.universalProperty_natural f g u
    rw [hp]
    change chapter02QuotientClassMk
        (chapter02PullbackInvertibleQuotientPairAlongComposition g f p) = _
    exact hnat.symm

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

/-! A finite locally free `E` gives a projective, finitely presented morphism.  The
projective-morphism predicate uses Mathlib's `IsClosedImmersion` and the shared relative
projective-bundle interface, so it also covers nontrivial finite locally free bundles over the base.

The finite locally free condition itself is declared in `Dependencies.lean` so later chapters can
reuse the same interface without importing this section.
-/

def Chapter02FiniteTypeMorphism {S X : Scheme.{u}} (f : X ⟶ S) : Prop :=
  QuasiCompact f ∧ LocallyOfFiniteType f

def Chapter02FinitePresentationMorphism {S X : Scheme.{u}} (f : X ⟶ S) : Prop :=
  QuasiCompact f ∧ QuasiSeparated f ∧ LocallyOfFinitePresentation f

/-!
The universal-property fields of `Chapter02ProjectiveBundleData` are deliberately available for
arbitrary quasi-coherent modules.  They do not by themselves make the projection finite type.
The following theorems record the additional geometric conclusions for a finite locally free
module; their proofs are deferred to the relative-projective-bundle construction.
-/
theorem chapter02_projective_bundle_is_projective_and_finitely_presented
    {S : Scheme.{u}} {E : Chapter02QuasiCoherentModule S}
    (P : Chapter02ProjectiveBundleData S E)
    (hE : Chapter02FiniteLocallyFreeModule E) :
    Chapter02ProjectiveMorphism P.projection ∧
      Chapter02FinitePresentationMorphism P.projection := by
  sorry

theorem chapter02_projective_bundle_is_finite_type
    {S : Scheme.{u}} {E : Chapter02QuasiCoherentModule S}
    (P : Chapter02ProjectiveBundleData S E)
    (hE : Chapter02FiniteLocallyFreeModule E) :
    Chapter02FiniteTypeMorphism P.projection := by
  have h := chapter02_projective_bundle_is_projective_and_finitely_presented P hE
  refine ⟨h.2.1, ?_⟩
  have hf : LocallyOfFinitePresentation P.projection := h.2.2.2
  rw [HasRingHomProperty.eq_affineLocally @LocallyOfFinitePresentation] at hf
  rw [HasRingHomProperty.eq_affineLocally @LocallyOfFiniteType]
  refine affineLocally_le (fun hf ↦ ?_) P.projection hf
  exact RingHom.FiniteType.of_finitePresentation hf

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

abbrev Chapter02InfiniteCounterexampleBase : Scheme.{u} :=
  AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℤ))

abbrev Chapter02InfiniteCounterexampleIndex : Type u := ULift.{u} ℕ

noncomputable def chapter02InfiniteCounterexampleModule :
    Chapter02QuasiCoherentModule Chapter02InfiniteCounterexampleBase :=
  chapter02FreeQuasiCoherentModule Chapter02InfiniteCounterexampleBase
    Chapter02InfiniteCounterexampleIndex

theorem chapter02_explicit_infinite_quasi_coherent_module_is_not_finite_type :
    ¬ Chapter02ModuleIsFiniteType chapter02InfiniteCounterexampleModule := by
  sorry

theorem chapter02_explicit_infinite_quasi_coherent_counterexample :
    ¬ Chapter02ModuleIsFiniteType chapter02InfiniteCounterexampleModule ∧
      ¬ Chapter02FiniteTypeMorphism
        (chapter02ProjectiveBundleProjection Chapter02InfiniteCounterexampleBase
          chapter02InfiniteCounterexampleModule) := by
  sorry

theorem chapter02_arbitrary_quasi_coherent_projective_bundle_need_not_be_finite_type :
    ∃ (S : Scheme.{u}) (E : Chapter02QuasiCoherentModule S),
      ¬ Chapter02ModuleIsFiniteType E ∧
        ¬ Chapter02FiniteTypeMorphism (chapter02ProjectiveBundleProjection S E) := by
  exact ⟨_, _, chapter02_explicit_infinite_quasi_coherent_counterexample⟩

/-! The bounded twisting step for composing projective presentations is made available as an
earlier interface.  The finite-rank ambient module produced by the construction is intentionally
hidden behind the presentation object; callers only need the resulting closed (or locally closed)
immersion over the composite base map.
-/
theorem chapter02_projective_presentation_comp
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    (P : Chapter02ProjectivePresentation f)
    (Q : Chapter02ProjectivePresentation g) :
    Nonempty (Chapter02ProjectivePresentation (f ≫ g)) := by
  sorry

theorem chapter02_quasi_projective_presentation_comp
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    (P : Chapter02QuasiProjectivePresentation f)
    (Q : Chapter02QuasiProjectivePresentation g)
    (hfqc : QuasiCompact f) (hgqc : QuasiCompact g) :
    Nonempty (Chapter02QuasiProjectivePresentation (f ≫ g)) := by
  sorry

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02
