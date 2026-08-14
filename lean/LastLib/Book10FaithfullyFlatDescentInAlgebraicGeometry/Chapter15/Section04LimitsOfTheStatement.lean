import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter15.Section03NormAndRemovingPolarization

/-!
# 15.4 Limits of the statement

This section records the exact safe forms of the descent assertions and the
two independent warnings: an arbitrary upstairs polarization is not descent
data, and properness by itself is not a projective embedding.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10

universe u

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter15

noncomputable section

structure UnpolarizedUpstairsProjectivityData
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) where
  cover : FpqcCoverData g
  lineBundle : LineBundle (baseChange f g)
  ample : IsAmple (baseChangeToBase f g) lineBundle
  projective : IsProjectiveMorphism (baseChangeToBase f g)

def IsPullbackOf {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (M : LineBundle (baseChange f g)) : Prop :=
  ∃ L : LineBundle X, lineBundleIsomorphic M (baseChangeLineBundle f g L)

structure PullbackFailureWarning
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) where
  cover : FpqcCoverData g
  lineBundle : LineBundle (baseChange f g)
  ample : IsAmple (baseChangeToBase f g) lineBundle
  not_a_pullback : ¬ IsPullbackOf f g lineBundle

structure NonCocycleOverlapWarning {Y X : Scheme.{u}} (q : Y ⟶ X) where
  cover : FpqcCoverData q
  lineBundle : LineBundle Y
  overlap : LineBundleIso
    (pullbackLineBundle (cechFirst q) lineBundle)
    (pullbackLineBundle (cechSecond q) lineBundle)
  face01 : cechTriple q ⟶ cechDouble q
  face12 : cechTriple q ⟶ cechDouble q
  face02 : cechTriple q ⟶ cechDouble q
  face01_is_canonical : face01 = cechFace01 q
  face12_is_canonical : face12 = cechFace12 q
  face02_is_canonical : face02 = cechFace02 q
  face01_right_eq_face12_left : face01 ≫ cechSecond q = face12 ≫ cechFirst q
  face01_left_eq_face02_left : face01 ≫ cechFirst q = face02 ≫ cechFirst q
  face12_right_eq_face02_right : face12 ≫ cechSecond q = face02 ≫ cechSecond q
  not_cocycle : ¬ lineBundleCechCocycleCondition q lineBundle overlap face01 face12 face02
    face01_right_eq_face12_left face01_left_eq_face02_left face12_right_eq_face02_right

theorem safe_polarized_quasiProjective_statement
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (hf : IsFinitePresentation f) (hg : FpqcCoverData g)
    (D : PolarizedBaseChangeData f g) :
    ∃ L : LineBundle X,
      Nonempty (LineBundleDescentRealization D.descent.descent L) ∧
        IsAmple f L ∧ HasLocalFiniteRankEmbedding f := by
  rcases polarized_quasiProjective_effective_descent f g hf hg D with
    ⟨L, hL, hample, hlocal⟩
  exact ⟨L, hL, hample, hasLocalFiniteRankEmbeddingFor_implies hlocal⟩

theorem safe_polarized_quasiProjective_statement_on_quasiCompact_base
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (hf : IsFinitePresentation f) (hg : FpqcCoverData g)
    (hS : QuasiCompact (𝟙 S)) (D : PolarizedBaseChangeData f g) :
    ∃ L : LineBundle X,
      Nonempty (LineBundleDescentRealization D.descent.descent L) ∧
        IsAmple f L ∧ HasGlobalFiniteRankEmbedding f := by
  rcases polarized_quasiProjective_global_embedding f g hf hg hS D with
    ⟨L, hL, hample, n, hn, hembedding⟩
  exact ⟨L, hL, hample, ⟨L.tensorPower n, hembedding⟩⟩

theorem safe_finite_locally_free_statement
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (G : FiniteLocallyFreeConstantRank g) (hf : IsFinitePresentation f)
    (M : LineBundle (baseChange f g))
    (hM : IsAmple (baseChangeToBase f g) M) :
    HasLocalFiniteRankEmbedding f := by
  exact quasiProjectivity_finiteLocallyFree_descent_local f g G hf M hM

theorem safe_finite_locally_free_statement_on_quasiCompact_base
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (G : FiniteLocallyFreeConstantRank g) (hf : IsFinitePresentation f)
    (hS : QuasiCompact (𝟙 S)) (M : LineBundle (baseChange f g))
    (hM : IsAmple (baseChangeToBase f g) M) :
    HasGlobalFiniteRankEmbedding f := by
  exact quasiProjectivity_finiteLocallyFree_descent_global f g G hf hS M hM

theorem safe_canonical_positive_data_statement
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (hf : IsFinitePresentation f) (hg : FpqcCoverData g)
    [Chapter10IdealDualAPI (baseChange f g)]
    (D : MarkedDivisorDescentData f g) :
    ∃ L : LineBundle X,
      Nonempty (LineBundleDescentRealization D.descent.descent L) ∧
        IsAmple f L := by
  exact marked_divisor_fixed_power_descends f g hf hg D

theorem proper_plus_quasiProjective_is_projective
    {X S : Scheme.{u}} (f : X ⟶ S) (hproper : IsProper f)
    (hquasi : IsQuasiProjectiveMorphism f) : IsProjectiveMorphism f := by
  sorry

def PropernessAloneWithoutProjectiveEmbedding {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  IsProper f ∧ ¬ IsProjectiveMorphism f

def ArbitraryPolarizationClassWarning {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ L M : LineBundle X,
    IsAmple f L ∧ IsAmple f M ∧ ¬ lineBundleIsomorphic L M

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter15
