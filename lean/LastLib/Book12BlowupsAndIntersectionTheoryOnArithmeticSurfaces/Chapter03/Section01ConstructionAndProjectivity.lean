import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter03.Dependencies

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter03

universe u v

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07
open scoped AlgebraicGeometry

/-! ## 3.1. Construction and projectivity -/

/-- The center is nowhere dense when its complement is dense. -/
def Chapter03NowhereDenseCenter
    {X : Scheme.{u}} (I : Chapter03CoherentIdeal X) : Prop :=
  Dense ((I.ideal.support : Set X)ᶜ)

/-- The restriction of the blowup morphism over an open of the target. -/
def chapter03BlowupRestriction
    {X : Scheme.{u}} {I : Chapter03CoherentIdeal X}
    (B : Chapter03Blowup I) (U : X.Opens) :
    (B.projection ⁻¹ᵁ U).toScheme ⟶ U.toScheme :=
  B.projection ∣_ U

theorem chapter03_blowup_is_projective
    {X : Scheme.{u}} {I : Chapter03CoherentIdeal X}
    (B : Chapter03Blowup I) :
    Chapter07IsProjectiveMorphism B.projection := by
  sorry

theorem chapter03_blowup_isIso_off_center
    {X : Scheme.{u}} {I : Chapter03CoherentIdeal X}
    (B : Chapter03Blowup I) :
    IsIso (chapter03BlowupRestriction B I.ideal.support.compl) := by
  sorry

def Chapter03BlowupIsBirational
    {X Y : Scheme.{u}} (f : Y ⟶ X) : Prop :=
  ∃ U : X.Opens, Dense (U : Set X) ∧ IsIso (f ∣_ U)

theorem chapter03_blowup_is_birational
    {X : Scheme.{u}} {I : Chapter03CoherentIdeal X}
    (B : Chapter03Blowup I) (hX : IsIntegral X)
    (hcenter : Chapter03NowhereDenseCenter I) :
    Chapter03BlowupIsBirational B.projection := by
  sorry

/-- Finite composites of blowups, with their target morphism retained in the index. -/
inductive Chapter03ProjectiveBlowupChain :
    {Y X : Scheme.{u}} → (Y ⟶ X) → Prop
  | single {X : Scheme.{u}} {I : Chapter03CoherentIdeal X}
      (B : Chapter03Blowup I) :
      Chapter03ProjectiveBlowupChain B.projection
  | comp {Z Y X : Scheme.{u}} {g : Z ⟶ Y} {f : Y ⟶ X}
      (hg : Chapter03ProjectiveBlowupChain g)
      (hf : Chapter03ProjectiveBlowupChain f) :
      Chapter03ProjectiveBlowupChain (g ≫ f)

theorem chapter03_projective_blowup_chain_is_projective
    {Y X : Scheme.{u}} {f : Y ⟶ X}
    (h : Chapter03ProjectiveBlowupChain f) :
    Chapter07IsProjectiveMorphism f := by
  sorry

/-! ### The tautological line and the sign convention -/

abbrev Chapter03LineBundle (X : Scheme.{u}) := Chapter04LineBundle X

def chapter03LineBundleIsomorphic
    {X : Scheme.{u}} (L M : Chapter03LineBundle X) : Prop :=
  Nonempty (L.sheaf ≅ M.sheaf)

structure Chapter03BlowupSignData
    {X : Scheme.{u}} {I : Chapter03CoherentIdeal X}
    (B : Chapter03Blowup I) where
  exceptional : EffectiveCartierDivisor B.carrier
  exceptional_ideal : exceptional.ideal = chapter03BlowupExceptionalIdeal B
  tautological : Chapter03LineBundle B.carrier
  tautological_is_relatively_ample :
    chapter04Ample B.projection tautological
  ideal_line : Chapter07IdealLineBundleIso exceptional.ideal
  tautological_is_O_one :
    Nonempty (ideal_line.line.sheaf ≅ tautological.sheaf)

/- LOCAL_DEPENDENCY_GUESS (3.1): on an integral scheme with nowhere-dense center, the extended
ideal is an effective Cartier ideal and the relative-Proj tautological line is its `O(1) = O(-E)`
line. -/
theorem chapter03_blowup_sign_data_exists
    {X : Scheme.{u}} {I : Chapter03CoherentIdeal X}
    (B : Chapter03Blowup I)
    (hX : IsIntegral X)
    (hcenter : Chapter03NowhereDenseCenter I) :
    Nonempty (Chapter03BlowupSignData B) := by
  sorry

noncomputable def chapter03BlowupSignData
    {X : Scheme.{u}} {I : Chapter03CoherentIdeal X}
    (B : Chapter03Blowup I)
    (hX : IsIntegral X)
    (hcenter : Chapter03NowhereDenseCenter I) :
    Chapter03BlowupSignData B :=
  Classical.choice (chapter03_blowup_sign_data_exists B hX hcenter)

theorem chapter03_blowup_extended_ideal_is_invertible
    {X : Scheme.{u}} {I : Chapter03CoherentIdeal X}
    (B : Chapter03Blowup I) :
    Chapter07IsInvertibleIdeal (chapter03BlowupExceptionalIdeal B) := by
  sorry

theorem chapter03_blowup_tautological_is_relatively_ample
    {X : Scheme.{u}} {I : Chapter03CoherentIdeal X}
    (B : Chapter03Blowup I)
    (hX : IsIntegral X)
    (hcenter : Chapter03NowhereDenseCenter I) :
    chapter04Ample B.projection
      (chapter03BlowupSignData B hX hcenter).tautological := by
  exact (chapter03BlowupSignData B hX hcenter).tautological_is_relatively_ample

/- LOCAL_DEPENDENCY_GUESS (3.1): the pinned line-bundle library has no degree operation for an
abstract projective line, so this small interface records the two normalized degrees used by the
sign check. -/
structure Chapter03ProjectiveLineDegreeConvention
    (K : Type u) [Field K] where
  degree : Chapter03LineBundle (chapter04ProjectiveLine K) → ℤ
  tensor_additive : ∀ L M,
    degree (chapter04LineBundleTensor L M) = degree L + degree M
  trivial_degree :
    degree (chapter04ProjectiveLineTrivialLineBundle K) = 0
  tautological : Chapter03LineBundle (chapter04ProjectiveLine K)
  tautological_is_standard :
    Nonempty (tautological.sheaf ≅
      (chapter04ProjectiveLineTautologicalLineBundle K).sheaf)
  tautological_degree : degree tautological = 1
  inverse_tautological : Chapter03LineBundle (chapter04ProjectiveLine K)
  inverse_is_O_E : Prop
  inverse_degree : degree inverse_tautological = -1

theorem chapter03_projective_line_degree_convention_exists
    (K : Type u) [Field K] :
    Nonempty (Chapter03ProjectiveLineDegreeConvention K) := by
  sorry

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter03
