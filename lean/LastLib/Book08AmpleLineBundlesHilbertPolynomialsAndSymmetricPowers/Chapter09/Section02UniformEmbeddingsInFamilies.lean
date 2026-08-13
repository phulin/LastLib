import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Dependencies

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09

open AlgebraicGeometry CategoryTheory
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04

noncomputable section

/-! ### 9.2 Uniform embeddings in families -/

structure Chapter09ProjectiveFlatCurveFamily (S : Scheme) where
  curve : Scheme
  map : curve ⟶ S
  projective : Chapter09ProjectiveMorphism map
  flat : Flat map
  finitePresentation : LocallyOfFinitePresentation map
  fibers_are_curves : Chapter09RelativeCurve map

def chapter09FamilyPowerPushforward {S : Scheme}
    (F : Chapter09ProjectiveFlatCurveFamily S)
    [Chapter09LineBundleTensorTheory F.curve]
    (L : Chapter09LineBundle F.curve) (n : ℕ) : S.Modules :=
  (Scheme.Modules.pushforward F.map).obj (chapter09LineBundlePower L n).module

def chapter09LocallyFreeModule {S : Scheme} (E : S.Modules) : Prop :=
  chapter04FiniteLocallyFree E

def chapter09FiberAmbientDimension {S : Scheme}
    [Chapter09ModuleRankTheory S] (E : S.Modules) (s : S) : ℕ :=
  chapter09ModuleRank E s - 1

theorem chapter09_family_rank_eq_fiber_hilbert_polynomial
    {S : Scheme} [IsNoetherian S]
    (F : Chapter09ProjectiveFlatCurveFamily S)
    [Chapter09LineBundleTensorTheory F.curve]
    [Chapter09ModuleRankTheory S]
    (L : Chapter09LineBundle F.curve)
    [Chapter09FiberHilbertPolynomialTheory F.map L]
    : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ s : S,
      (chapter09ModuleRank (chapter09FamilyPowerPushforward F L n) s : ℤ) =
        (chapter09FiberHilbertPolynomial F.map L s).value n := by
  sorry

theorem chapter09_family_rank_constant_on_connected_components
    {S : Scheme}
    (F : Chapter09ProjectiveFlatCurveFamily S)
    [Chapter09LineBundleTensorTheory F.curve]
    [Chapter09ModuleRankTheory S]
    (L : Chapter09LineBundle F.curve)
    (n : ℕ)
    (hE : chapter09LocallyFreeModule (chapter09FamilyPowerPushforward F L n)) :
    chapter09ConstantOnConnectedComponents
      (chapter09ModuleRank (chapter09FamilyPowerPushforward F L n)) := by
  sorry

theorem chapter09_family_ambient_dimension_constant_on_connected_components
    {S : Scheme}
    (F : Chapter09ProjectiveFlatCurveFamily S)
    [Chapter09LineBundleTensorTheory F.curve]
    [Chapter09ModuleRankTheory S]
    (L : Chapter09LineBundle F.curve)
    (n : ℕ)
    (hE : chapter09LocallyFreeModule (chapter09FamilyPowerPushforward F L n)) :
    chapter09ConstantOnConnectedComponents
      (chapter09FiberAmbientDimension (chapter09FamilyPowerPushforward F L n)) := by
  sorry

theorem chapter09_uniform_embedding_in_a_projective_flat_family
    {S : Scheme} [IsNoetherian S]
    (F : Chapter09ProjectiveFlatCurveFamily S)
    [Chapter09LineBundleTensorTheory F.curve]
    (L : Chapter09LineBundle F.curve)
    (hL : chapter09RelativelyAmple F.map L) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      chapter09LocallyFreeModule (chapter09FamilyPowerPushforward F L n) ∧
      chapter09PushforwardCommutesWithBaseChange F.map
        (chapter09LineBundlePower L n).module ∧
      ∃ E : Chapter09EvaluationWitness F.map
          (chapter09LineBundlePower L n)
          (chapter09FamilyPowerPushforward F L n),
        IsClosedImmersion E.map := by
  sorry

structure Chapter09NonFlatRankJumpWitness where
  base : Scheme
  curve : Scheme
  map : curve ⟶ base
  projective : Chapter09ProjectiveMorphism map
  finitePresentation : LocallyOfFinitePresentation map
  notFlat : ¬ Flat map
  lineBundle : Chapter09LineBundle curve
  tensorTheory : Chapter09LineBundleTensorTheory curve
  power : ℕ
  completeLinearSystem : base.Modules
  completeLinearSystemIso :
    letI := tensorTheory
    completeLinearSystem ≅
      (Scheme.Modules.pushforward map).obj
        (chapter09LineBundlePower lineBundle power).module
  rankTheory : Chapter09ModuleRankTheory base
  rank : base → ℕ
  rank_is_fiber_rank : ∀ s, rank s = rankTheory.rank completeLinearSystem s
  ranks_jump : ∃ s t, rank s ≠ rank t
  completeLinearSystemNotVectorBundle : ¬ completeLinearSystem.IsLocallyFree

theorem chapter09_without_flatness_ranks_can_jump :
    Nonempty Chapter09NonFlatRankJumpWitness := by
  sorry

theorem chapter09_nonflat_complete_linear_system_need_not_be_a_vector_bundle
    (W : Chapter09NonFlatRankJumpWitness) :
    ¬ W.completeLinearSystem.IsLocallyFree := by
  exact W.completeLinearSystemNotVectorBundle

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09
