import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter15.Dependencies
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Section04TheDivisorPicardCorrespondence

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter15

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11

universe u v

/-!
### 15.1 Abel maps before the Picard scheme

The earlier symmetric-power chapter supplies the representing functor of
effective relative Cartier divisors.  The following records make the second
functor, degree components of the Picard functor, and the Abel morphism
explicit.  The construction of the line bundle of a Cartier divisor is a
local dependency guess because it is not exposed by the pinned sheaf API.
-/

/- The inverse ideal is the canonical coefficient module for a divisor.  The
   construction is named here because the pinned sheaf API does not expose its
   invertibility proof as a reusable definition. -/
noncomputable def chapter15InverseIdealModule {X : Scheme.{u}}
    (D : Chapter15EffectiveCartierDivisor X) : X.Modules := by
  sorry

def Chapter15IsDivisorLineBundle {X : Scheme.{u}}
  (D : Chapter15EffectiveCartierDivisor X)
    (L : Chapter15LineBundle X) : Prop :=
  Nonempty (L.module ≅ chapter15InverseIdealModule D)

noncomputable def chapter15DivisorLineBundle {X : Scheme.{u}}
    (D : Chapter15EffectiveCartierDivisor X) : Chapter15LineBundle X :=
  { module := chapter15InverseIdealModule D
    isInvertible := by sorry }

theorem chapter15_divisorLineBundle_is_divisorLineBundle {X : Scheme.{u}}
    (D : Chapter15EffectiveCartierDivisor X) :
    Chapter15IsDivisorLineBundle D (chapter15DivisorLineBundle D) := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: degree of a line bundle on a relative curve is not
   yet a named earlier-project function.  The function is deliberately
   separated from the Picard point so its Euler-characteristic implementation
   can be installed without changing the representing API. -/
noncomputable def chapter15LineBundleDegree
    {S : Scheme.{u}} (C T : RelativeScheme S)
    (L : Chapter15LineBundle (pullback C.structuralMap T.structuralMap)) : ℤ := by
  sorry

def Chapter15LineBundleHasDegree {S : Scheme.{u}}
    (C T : RelativeScheme S)
    (L : Chapter15LineBundle (pullback C.structuralMap T.structuralMap))
    (d : ℤ) : Prop :=
  chapter15LineBundleDegree C T L = d

/- The earlier relative-Picard relation is stated for the Chapter 4
   line-bundle wrapper.  This bridge keeps the Chapter 15 wrapper in the
   public API while reusing that canonical relation. -/
noncomputable def chapter15AsBook09Chapter04LineBundle {X : Scheme.{u}}
    (L : Chapter15LineBundle X) :
    LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Chapter04LineBundle X :=
  { sheaf := L.module
    isInvertible := by sorry }

abbrev Chapter15PicardRawPoints {S : Scheme.{u}} (C : RelativeScheme S)
    (T : RelativeScheme S) (d : ℤ) :=
  {L : Chapter15LineBundle (pullback C.structuralMap T.structuralMap) //
    Chapter15LineBundleHasDegree C T L d}

def chapter15PicardRawEquivalent {S : Scheme.{u}} (C : RelativeScheme S)
    (T : RelativeScheme S) (d : ℤ)
    (L M : Chapter15PicardRawPoints C T d) : Prop :=
  chapter04RelativePicardRelation
    (pullback.snd C.structuralMap T.structuralMap)
    (chapter15AsBook09Chapter04LineBundle L.1)
    (chapter15AsBook09Chapter04LineBundle M.1)

def chapter15PicardRawPointsSetoid {S : Scheme.{u}} (C : RelativeScheme S)
    (T : RelativeScheme S) (d : ℤ) : Setoid (Chapter15PicardRawPoints C T d) where
  r := chapter15PicardRawEquivalent C T d
  iseqv :=
    { refl := by
        intro L
        exact chapter04_relativePicardRelation_refl _ _
      symm := by
        intro L M h
        exact chapter04_relativePicardRelation_symm _ h
      trans := by
        intro L M N hLM hMN
        exact chapter04_relativePicardRelation_trans _ hLM hMN }

/- The relative Picard functor quotients degree-d line bundles by the
   fiberwise equivalence relation, rather than retaining a chosen
   representative. -/
abbrev Chapter15PicardPoints {S : Scheme.{u}} (C : RelativeScheme S)
    (T : RelativeScheme S) (d : ℤ) :=
  Quotient (chapter15PicardRawPointsSetoid C T d)

noncomputable def chapter15PicardRepresentativeData {S : Scheme.{u}}
    (C : RelativeScheme S) (T : RelativeScheme S) (d : ℤ)
    (P : Chapter15PicardPoints C T d) : Chapter15PicardRawPoints C T d :=
  Quotient.out P

theorem chapter15PicardPoints_eq_iff {S : Scheme.{u}} (C : RelativeScheme S)
    (T : RelativeScheme S) (d : ℤ)
    (L M : Chapter15PicardRawPoints C T d) :
    (Quotient.mk (chapter15PicardRawPointsSetoid C T d) L :
      Chapter15PicardPoints C T d) =
      Quotient.mk (chapter15PicardRawPointsSetoid C T d) M ↔
      chapter15PicardRawEquivalent C T d L M := by
  sorry

structure Chapter15RelativePicardFunctorData {S : Scheme.{u}}
    (C : RelativeScheme S) (d : ℤ) where
  restriction : ∀ {T U : RelativeScheme S} (_u : U ⟶ T),
    Chapter15PicardPoints C T d → Chapter15PicardPoints C U d
  restriction_lineBundle : ∀ {T U : RelativeScheme S} (u : U ⟶ T)
    (L : Chapter15PicardPoints C T d),
    Nonempty (Chapter15LineBundleIso
      (chapter15PullbackLineBundle (chapter15CurveBaseChangeMap u)
        (chapter15PicardRepresentativeData C T d L).1)
      (chapter15PicardRepresentativeData C U d (restriction u L)).1)
  restriction_id : ∀ (T : RelativeScheme S)
    (L : Chapter15PicardPoints C T d), restriction (𝟙 T) L = L
  restriction_comp : ∀ {T U V : RelativeScheme S}
    (u : U ⟶ T) (v : V ⟶ U) (L : Chapter15PicardPoints C T d),
    restriction v (restriction u L) = restriction (v ≫ u) L

structure Chapter15PicardRepresentingData {S : Scheme.{u}}
    (C : RelativeScheme S) (d : ℤ) where
  representing : RelativeScheme S
  functor : Chapter15RelativePicardFunctorData C d
  equivalence : ∀ T : RelativeScheme S,
    (T ⟶ representing) ≃ Chapter15PicardPoints C T d
  natural : ∀ {T U : RelativeScheme S} (u : U ⟶ T)
    (f : T ⟶ representing),
    functor.restriction u (equivalence T f) = equivalence U (u ≫ f)

def Chapter15PicardRepresented {S : Scheme.{u}}
    (C : RelativeScheme S) (d : ℤ) : Prop :=
  Nonempty (Chapter15PicardRepresentingData C d)

noncomputable def chapter15PicardScheme {S : Scheme.{u}}
    (C : RelativeScheme S) (d : ℤ)
    (hpicard : Chapter15PicardRepresented C d) : RelativeScheme S :=
  (Classical.choice hpicard).representing

/- The universal divisor is converted pointwise to O(D); the base-change
   comparison is retained as an isomorphism, rather than as a definitional
   equality of sheaves. -/
structure Chapter15UniversalDivisorLineBundleData {S : Scheme.{u}}
    (C : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] where
  lineBundle : ∀ T : RelativeScheme S,
    (D : Chapter15RelativeEffectiveCartierDivisor C T d) →
      Chapter15LineBundle (pullback C.structuralMap T.structuralMap)
  divisor_lineBundle : ∀ (T : RelativeScheme S)
    (D : Chapter15RelativeEffectiveCartierDivisor C T d),
    Nonempty ((lineBundle T D).module ≅ chapter15InverseIdealModule D.divisor)
  restriction_iso : ∀ {T U : RelativeScheme S} (u : U ⟶ T)
    (D : Chapter15RelativeEffectiveCartierDivisor C T d),
    Nonempty (Chapter15LineBundleIso
      (chapter15PullbackLineBundle (chapter15CurveBaseChangeMap u)
        (lineBundle T D))
      (lineBundle U (divisorRestriction d u D)))

/- LOCAL_DEPENDENCY_GUESS: this is the standard divisor-to-line-bundle
   construction and its naturality, separated from the Picard representability
   assumption. -/
theorem chapter15_universal_divisor_lineBundle_exists {S : Scheme.{u}}
    (C : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] :
    Nonempty (Chapter15UniversalDivisorLineBundleData C d) := by
  sorry

noncomputable def chapter15UniversalDivisorLineBundle {S : Scheme.{u}}
    (C : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] :
    Chapter15UniversalDivisorLineBundleData C d :=
  Classical.choice (chapter15_universal_divisor_lineBundle_exists C d)

theorem chapter15_universal_divisor_allows_repeated_roots {S : Scheme.{u}}
    (C : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] :
    ∀ (T : RelativeScheme S) (f : T ⟶ symmetricPower C d),
      Chapter11FiniteLocallyFreeOfRank
        ((pullbackUniversalDivisor C T d f).divisor.inclusion ≫
          pullback.snd C.structuralMap T.structuralMap) d := by
  sorry

structure Chapter15AbelMapData {S : Scheme.{u}}
    (C : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] where
  picard : Chapter15PicardRepresentingData C (d : ℤ)
  abelMap : symmetricPower C d ⟶ picard.representing
  universal_lineBundle : ∀ (T : RelativeScheme S)
    (f : T ⟶ symmetricPower C d),
    Nonempty (Chapter15LineBundleIso
      ((chapter15PicardRepresentativeData C T (d : ℤ)
        (picard.equivalence T (f ≫ abelMap))).1)
      ((chapter15UniversalDivisorLineBundle C d).lineBundle T
        (universalDivisorEquiv C T d f)))

def Chapter15AbelMapRepresented {S : Scheme.{u}}
    (C : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] : Prop :=
  Nonempty (Chapter15AbelMapData C d)

theorem chapter15_abel_map_exists {S : Scheme.{u}}
    (C : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C]
    (hpicard : Chapter15PicardRepresented C (d : ℤ)) :
    Nonempty (Chapter15AbelMapData C d) := by
  sorry

noncomputable def chapter15AbelMapData {S : Scheme.{u}}
    (C : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C]
    (hpicard : Chapter15PicardRepresented C (d : ℤ)) :
    Chapter15AbelMapData C d :=
  Classical.choice (chapter15_abel_map_exists C d hpicard)

noncomputable def chapter15AbelMap {S : Scheme.{u}}
    (C : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C]
    (hpicard : Chapter15PicardRepresented C (d : ℤ)) :
    symmetricPower C d ⟶
      (chapter15AbelMapData C d hpicard).picard.representing :=
  (chapter15AbelMapData C d hpicard).abelMap

def Chapter15DivisorLinearEquivalent {X : Scheme.{u}}
    (D E : Chapter15EffectiveCartierDivisor X) : Prop :=
  chapter09LineBundleIsomorphic
    (chapter15DivisorLineBundle D) (chapter15DivisorLineBundle E)

theorem chapter15_divisorLinearEquivalent_refl {X : Scheme.{u}}
    (D : Chapter15EffectiveCartierDivisor X) :
    Chapter15DivisorLinearEquivalent D D := by
  exact ⟨{ hom := Iso.refl _ }⟩

theorem chapter15_divisorLinearEquivalent_symm {X : Scheme.{u}}
    {D E : Chapter15EffectiveCartierDivisor X}
    (_h : Chapter15DivisorLinearEquivalent D E) :
    Chapter15DivisorLinearEquivalent E D := by
  sorry

theorem chapter15_divisorLinearEquivalent_trans {X : Scheme.{u}}
    {D E F : Chapter15EffectiveCartierDivisor X}
    (_hDE : Chapter15DivisorLinearEquivalent D E)
    (_hEF : Chapter15DivisorLinearEquivalent E F) :
    Chapter15DivisorLinearEquivalent D F := by
  sorry

noncomputable def chapter15AbelPoint {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (A : Chapter15AbelMapData C.curve d)
    (D : Chapter15FieldDivisor C d) :
    RelativeScheme.Hom (RelativeScheme.base (chapter15FieldBase k))
      A.picard.representing :=
  divisorToSymmetricPoint C.curve (RelativeScheme.base (chapter15FieldBase k)) d D ≫
    A.abelMap

theorem chapter15_abel_same_image_iff_linearly_equivalent
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (A : Chapter15AbelMapData C.curve d)
    (D E : Chapter15FieldDivisor C d) :
    chapter15AbelPoint C d A D = chapter15AbelPoint C d A E ↔
      Chapter15DivisorLinearEquivalent D.divisor E.divisor := by
  sorry

/- Projective-space fiber convention.  The coefficient modules and the fiber
   are now tied to the earlier H0 and projective-bundle interfaces. -/
noncomputable def chapter15H0Module {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k)
    (L : Chapter15LineBundle C.curve.carrier) : ModuleCat k := by
  sorry

noncomputable def chapter15DualH0Module {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k)
    (L : Chapter15LineBundle C.curve.carrier) : ModuleCat k := by
  sorry

noncomputable def chapter15ProjectiveFiberBundle {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k)
    (L : Chapter15LineBundle C.curve.carrier) :
    Chapter04ProjectiveBundle (chapter15FieldBase k) := by
  sorry

def Chapter15HasNonzeroH0 {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k)
    (L : Chapter15LineBundle C.curve.carrier) : Prop :=
  ∃ s : (chapter15H0Module C L : Type u), s ≠ 0

structure Chapter15ProjectiveBundleFiber {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k)
    (L : Chapter15LineBundle C.curve.carrier) where
  sections : ModuleCat k
  dualSections : ModuleCat k
  fiber : Scheme.{u}
  sections_are_H0 : sections = chapter15H0Module C L
  dual_is_dual : Nonempty (dualSections ≅ chapter15DualH0Module C L)
  projectiveFiber : Chapter04ProjectiveBundle (chapter15FieldBase k)
  fiber_is_projective_space : fiber = projectiveFiber.space

theorem chapter15_projective_bundle_fiber {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k)
    (L : Chapter15LineBundle C.curve.carrier)
    (hsections : Chapter15HasNonzeroH0 C L) :
    Nonempty (Chapter15ProjectiveBundleFiber C L) := by
  sorry

def Chapter15AbelFiberDimension {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ) : ℤ :=
  (d : ℤ) - C.genus

structure Chapter15AbelFiberDimensionData
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (A : Chapter15AbelMapData C.curve d)
    (P : A.picard.representing.carrier) where
  fiberPoints : Set (symmetricPower C.curve d).carrier
  fiberPoints_are_abel_fiber : ∀ x,
    x ∈ fiberPoints ↔ A.abelMap.hom x = P
  dimension : ℤ
  dimension_is_RiemannRoch : dimension = Chapter15AbelFiberDimension C d

theorem chapter15_abel_fibers_have_dimension_d_sub_g
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (A : Chapter15AbelMapData C.curve d)
    (P : A.picard.representing.carrier)
    (F : Chapter15AbelFiberDimensionData C d A P)
    (hd : 2 * (C.genus : ℤ) - 2 < (d : ℤ)) :
    F.dimension = Chapter15AbelFiberDimension C d := by
  sorry

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter15
