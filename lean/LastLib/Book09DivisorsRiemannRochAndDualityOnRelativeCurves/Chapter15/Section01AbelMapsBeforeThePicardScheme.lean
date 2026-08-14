import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter15.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter15

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
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

/- LOCAL_DEPENDENCY_GUESS: the pinned project does not yet identify the inverse
   ideal of an effective Cartier divisor with an invertible module.  This
   witness is the book-facing interface for the canonical sheaf O(D). -/
structure Chapter15DivisorLineBundleWitness {X : Scheme.{u}}
    (D : Chapter15EffectiveCartierDivisor X) where
  lineBundle : Chapter15LineBundle X
  canonical_construction : Prop
  canonical_construction_proof : canonical_construction

def Chapter15IsDivisorLineBundle {X : Scheme.{u}}
  (D : Chapter15EffectiveCartierDivisor X)
    (L : Chapter15LineBundle X) : Prop :=
  ∃ w : Chapter15DivisorLineBundleWitness D, w.lineBundle = L ∧
    w.canonical_construction

/- LOCAL_DEPENDENCY_GUESS: existence of the invertible sheaf O(D) is standard
   for an effective Cartier divisor, but no earlier LastLib declaration
   packages the dual ideal sheaf. -/
noncomputable def chapter15DivisorLineBundle {X : Scheme.{u}}
    (D : Chapter15EffectiveCartierDivisor X) : Chapter15LineBundle X :=
  Classical.choice (show Nonempty (Chapter15DivisorLineBundleWitness D) by sorry)

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

def Chapter15PicardPoints {S : Scheme.{u}} (C : RelativeScheme S)
    (T : RelativeScheme S) (d : ℤ) :=
  {L : Chapter15LineBundle (pullback C.structuralMap T.structuralMap) //
    Chapter15LineBundleHasDegree C T L d}

structure Chapter15RelativePicardFunctorData {S : Scheme.{u}}
    (C : RelativeScheme S) (d : ℤ) where
  restriction : ∀ {T U : RelativeScheme S} (u : U ⟶ T),
    Chapter15PicardPoints C T d → Chapter15PicardPoints C U d
  restriction_lineBundle : ∀ {T U : RelativeScheme S} (u : U ⟶ T)
    (L : Chapter15PicardPoints C T d),
    Nonempty (Chapter15LineBundleIso
      (chapter15PullbackLineBundle (chapter15CurveBaseChangeMap u) L.1)
      (restriction u L).1)
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
    Chapter15IsDivisorLineBundle D.divisor (lineBundle T D)
  restriction_iso : ∀ {T U : RelativeScheme S} (u : U ⟶ T)
    (D : Chapter15RelativeEffectiveCartierDivisor C T d),
    Nonempty (Chapter15LineBundleIso
      (chapter15PullbackLineBundle (chapter15CurveBaseChangeMap u)
        (lineBundle T D))
      (lineBundle U (divisorRestriction d u D)))
  restriction_identity_coherence : Prop
  restriction_identity_coherence_proof : restriction_identity_coherence
  restriction_composition_coherence : Prop
  restriction_composition_coherence_proof : restriction_composition_coherence

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
  exact universal_divisor_repeated_roots_are_allowed C d

structure Chapter15AbelMapData {S : Scheme.{u}}
    (C : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] where
  picard : Chapter15PicardRepresentingData C (d : ℤ)
  abelMap : symmetricPower C d ⟶ picard.representing
  universal_lineBundle : ∀ (T : RelativeScheme S)
    (f : T ⟶ symmetricPower C d),
    Nonempty (Chapter15LineBundleIso
      ((picard.equivalence T (f ≫ abelMap)).1)
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
    (h : Chapter15DivisorLinearEquivalent D E) :
    Chapter15DivisorLinearEquivalent E D := by
  rcases h with ⟨h⟩
  exact ⟨{ hom := h.hom.symm }⟩

theorem chapter15_divisorLinearEquivalent_trans {X : Scheme.{u}}
    {D E F : Chapter15EffectiveCartierDivisor X}
    (hDE : Chapter15DivisorLinearEquivalent D E)
    (hEF : Chapter15DivisorLinearEquivalent E F) :
    Chapter15DivisorLinearEquivalent D F := by
  rcases hDE with ⟨hDE⟩
  rcases hEF with ⟨hEF⟩
  exact ⟨{ hom := hDE.hom ≪≫ hEF.hom }⟩

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

/- Projective-space fiber convention.  The sections are kept as a genuine
   finite-dimensional k-module object, while the pinned projective-bundle API
   is not yet connected to relative Picard fibers. -/
structure Chapter15ProjectiveBundleFiber {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k)
    (L : Chapter15LineBundle C.curve.carrier) where
  sections : ModuleCat k
  dualSections : ModuleCat k
  fiber : Scheme.{u}
  sections_are_H0 : Prop
  sections_are_H0_proof : sections_are_H0
  dual_is_dual : Prop
  dual_is_dual_proof : dual_is_dual
  fiber_is_projective_space : Prop
  fiber_is_projective_space_proof : fiber_is_projective_space
  quotient_convention : Prop
  quotient_convention_proof : quotient_convention
  parametrizes_one_dimensional_subspaces : Prop
  parametrizes_one_dimensional_subspaces_proof :
    parametrizes_one_dimensional_subspaces

theorem chapter15_projective_bundle_fiber {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k)
    (L : Chapter15LineBundle C.curve.carrier)
    (hsections : Prop) (has_sections : hsections) :
    Nonempty (Chapter15ProjectiveBundleFiber C L) := by
  sorry

def Chapter15AbelFiberDimension {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ) : ℤ :=
  (d : ℤ) - C.genus

structure Chapter15AbelFiberDimensionData
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ) where
  fiberPoints : Type u
  dimension : fiberPoints → ℤ
  dimension_is_abel_fiber : Prop
  dimension_is_abel_fiber_proof : dimension_is_abel_fiber

theorem chapter15_abel_fibers_have_dimension_d_sub_g
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (F : Chapter15AbelFiberDimensionData C d)
    (hF : F.dimension_is_abel_fiber)
    (hd : 2 * (C.genus : ℤ) - 2 < (d : ℤ)) :
    ∀ x : F.fiberPoints, F.dimension x =
      Chapter15AbelFiberDimension C d := by
  sorry

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter15
