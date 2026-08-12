import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Dependencies

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

/-! ### 9.1 Embedding projective curves -/

structure Chapter09ProperCurveOverField (k : Type*) [Field k] where
  carrier : Scheme
  structureMap : carrier ⟶ Spec (.of k)
  proper : IsProper structureMap
  nonempty : Nonempty carrier
  curve : Chapter09RelativeCurve structureMap

structure Chapter09LengthTwoSubscheme (C : Scheme) where
  support : Scheme
  inclusion : support ⟶ C
  closed : IsClosedImmersion inclusion
  finite : IsFinite inclusion
  finiteLocallyFree : Prop
  length : ℕ
  length_eq_two : length = 2

theorem chapter09_serre_eventual_very_ampleness
    {k : Type*} [Field k]
    (C : Chapter09ProperCurveOverField k)
    [Chapter09LineBundleTensorTheory C.carrier]
    [Chapter09RelativePositivityTheory C.structureMap]
    (L : Chapter09LineBundle C.carrier)
    (hL : chapter09RelativelyAmple C.structureMap L) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      chapter09RelativelyVeryAmple C.structureMap (chapter09LineBundlePower L n) := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: this is the missing restriction/evaluation
interface for a finite subscheme.  `sectionsOn` is the book-facing module of
sections on `Z`, and `restrictionMap` is induced by the canonical pullback. -/
class Chapter09LengthTwoSectionTheory (C : Scheme)
    [Chapter09LineBundleTensorTheory C] where
  sectionsOn :
    ∀ (_Z : Chapter09LengthTwoSubscheme C)
      (_L : Chapter09LineBundle C) (_n : ℕ), Type*
  restrictionMap :
    ∀ (Z : Chapter09LengthTwoSubscheme C)
      (L : Chapter09LineBundle C) (n : ℕ),
      chapter09GlobalSection L n → sectionsOn Z L n

def chapter09SectionsSeparateLengthTwo {C : Scheme}
    [Chapter09LineBundleTensorTheory C]
    [Chapter09LengthTwoSectionTheory C]
    (Z : Chapter09LengthTwoSubscheme C) (L : Chapter09LineBundle C) (n : ℕ) : Prop :=
  Function.Surjective
    (Chapter09LengthTwoSectionTheory.restrictionMap Z L n)

theorem chapter09SectionsSeparateLengthTwo_iff {C : Scheme}
    [Chapter09LineBundleTensorTheory C]
    [Chapter09LengthTwoSectionTheory C]
    (Z : Chapter09LengthTwoSubscheme C) (L : Chapter09LineBundle C) (n : ℕ) :
    chapter09SectionsSeparateLengthTwo Z L n ↔
      Function.Surjective (Chapter09LengthTwoSectionTheory.restrictionMap Z L n) :=
  Iff.rfl

/- LOCAL_DEPENDENCY_GUESS: the ideal-twist/restriction sheaf construction is
not yet in the pinned global sheaf API.  The short complex is retained as a
genuine categorical object, while its term labels are exposed by the
`terms_are_ideal_restriction` field. -/
class Chapter09LengthTwoRestrictionTheory (C : Scheme)
    [Chapter09LineBundleTensorTheory C] where
  sequence :
    ∀ (_Z : Chapter09LengthTwoSubscheme C)
      (_L : Chapter09LineBundle C) (_n : ℕ), ShortComplex C.Modules
  terms_are_ideal_restriction :
    ∀ (_Z : Chapter09LengthTwoSubscheme C)
      (_L : Chapter09LineBundle C) (_n : ℕ), Prop

def chapter09IdealRestrictionSequence {C : Scheme}
    [Chapter09LineBundleTensorTheory C]
    [Chapter09LengthTwoRestrictionTheory C]
    (Z : Chapter09LengthTwoSubscheme C) (L : Chapter09LineBundle C) (n : ℕ) :
    ShortComplex C.Modules :=
  Chapter09LengthTwoRestrictionTheory.sequence Z L n

theorem chapter09_length_two_ideal_restriction_exact {C : Scheme}
    [Chapter09LineBundleTensorTheory C]
    [Chapter09LengthTwoRestrictionTheory C]
    (Z : Chapter09LengthTwoSubscheme C) (L : Chapter09LineBundle C) (n : ℕ) :
    (chapter09IdealRestrictionSequence Z L n).Exact := by
  sorry

theorem chapter09_length_two_restriction_terms {C : Scheme}
    [Chapter09LineBundleTensorTheory C]
    [Chapter09LengthTwoRestrictionTheory C]
    (Z : Chapter09LengthTwoSubscheme C) (L : Chapter09LineBundle C) (n : ℕ) :
    Chapter09LengthTwoRestrictionTheory.terms_are_ideal_restriction Z L n := by
  sorry

theorem chapter09_length_two_hOne_vanishing_for_large_twists
    {k : Type*} [Field k]
    (C : Chapter09ProperCurveOverField k)
    [Chapter09LineBundleTensorTheory C.carrier]
    [Chapter09RelativePositivityTheory C.structureMap]
    [Chapter09CohomologyTheory C.carrier]
    [Chapter09LengthTwoRestrictionTheory C.carrier]
    (L : Chapter09LineBundle C.carrier)
    (hL : chapter09RelativelyAmple C.structureMap L) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ Z : Chapter09LengthTwoSubscheme C.carrier,
        chapter09HOneVanishes (chapter09IdealRestrictionSequence Z L n).X₁ := by
  sorry

theorem chapter09_hOne_vanishing_separates_length_two
    {C : Scheme}
    [Chapter09LineBundleTensorTheory C]
    [Chapter09CohomologyTheory C]
    [Chapter09LengthTwoRestrictionTheory C]
    [Chapter09LengthTwoSectionTheory C]
    (Z : Chapter09LengthTwoSubscheme C) (L : Chapter09LineBundle C) (n : ℕ)
    (hvan : chapter09HOneVanishes (chapter09IdealRestrictionSequence Z L n).X₁) :
    chapter09SectionsSeparateLengthTwo Z L n := by
  sorry

theorem chapter09_ample_power_separates_all_length_two_subschemes
    {k : Type*} [Field k]
    (C : Chapter09ProperCurveOverField k)
    [Chapter09LineBundleTensorTheory C.carrier]
    [Chapter09RelativePositivityTheory C.structureMap]
    [Chapter09CohomologyTheory C.carrier]
    [Chapter09LengthTwoRestrictionTheory C.carrier]
    [Chapter09LengthTwoSectionTheory C.carrier]
    (L : Chapter09LineBundle C.carrier)
    (hL : chapter09RelativelyAmple C.structureMap L) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ Z : Chapter09LengthTwoSubscheme C.carrier,
        chapter09SectionsSeparateLengthTwo Z L n := by
  sorry

structure Chapter09ClosedCurveEmbedding
    {k : Type*} [Field k]
    (C : Chapter09ProperCurveOverField k)
    (L : Chapter09LineBundle C.carrier) (n : ℕ) where
  target : Scheme
  map : C.carrier ⟶ target
  realizesCompleteLinearSystem : Prop

theorem chapter09_length_two_separation_gives_closed_embedding
    {k : Type*} [Field k]
    (C : Chapter09ProperCurveOverField k)
    [Chapter09LineBundleTensorTheory C.carrier]
    [Chapter09RelativePositivityTheory C.structureMap]
    [Chapter09LengthTwoSectionTheory C.carrier]
    (L : Chapter09LineBundle C.carrier) (n : ℕ)
    (hsep : ∀ Z : Chapter09LengthTwoSubscheme C.carrier,
      chapter09SectionsSeparateLengthTwo Z L n) :
    ∃ E : Chapter09ClosedCurveEmbedding C L n,
      IsClosedImmersion E.map ∧ E.realizesCompleteLinearSystem := by
  sorry

theorem chapter09_ample_power_is_closed_embedding
    {k : Type*} [Field k]
    (C : Chapter09ProperCurveOverField k)
    [Chapter09LineBundleTensorTheory C.carrier]
    [Chapter09RelativePositivityTheory C.structureMap]
    [Chapter09CohomologyTheory C.carrier]
    [Chapter09LengthTwoRestrictionTheory C.carrier]
    [Chapter09LengthTwoSectionTheory C.carrier]
    (L : Chapter09LineBundle C.carrier)
    (hL : chapter09RelativelyAmple C.structureMap L) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ E : Chapter09ClosedCurveEmbedding C L n,
        IsClosedImmersion E.map ∧ E.realizesCompleteLinearSystem := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the pinned tree does not package effective Cartier
divisors, their canonical sections, or the complement/nonvanishing relation in
one relative scheme API. -/
structure Chapter09FiniteEffectiveCartierDivisor
    (C : Scheme) [Chapter09LineBundleTensorTheory C] where
  support : Scheme
  inclusion : support ⟶ C
  closed : IsClosedImmersion inclusion
  finite : IsFinite inclusion
  effectiveCartier : Prop
  degree : ℕ
  nonempty : Nonempty support
  associatedLineBundle : Chapter09LineBundle C
  canonicalSection : chapter09GlobalSection associatedLineBundle 1
  complement : C.Opens
  complementIsAffine : IsAffineOpen complement
  canonicalSectionNonvanishing : Prop

theorem chapter09_smooth_proper_curve_has_closed_point
    {k : Type*} [Field k]
    (C : Chapter09ProperCurveOverField k)
    [Smooth C.structureMap] :
    ∃ x : C.carrier, IsClosed ({x} : Set C.carrier) := by
  sorry

theorem chapter09_smooth_proper_curve_has_finite_effective_cartier_divisor
    {k : Type*} [Field k] (C : Chapter09ProperCurveOverField k)
    [Chapter09LineBundleTensorTheory C.carrier]
    [Smooth C.structureMap] :
    ∃ D : Chapter09FiniteEffectiveCartierDivisor C.carrier,
      D.effectiveCartier ∧ Nonempty D.support := by
  sorry

theorem chapter09_effective_divisor_complement_is_affine
    {C : Scheme} [Chapter09LineBundleTensorTheory C]
    (D : Chapter09FiniteEffectiveCartierDivisor C) :
    IsAffineOpen D.complement := by
  exact D.complementIsAffine

theorem chapter09_effective_divisor_can_be_enlarged_to_an_ample_bundle
    {k : Type*} [Field k]
    (C : Chapter09ProperCurveOverField k)
    [Chapter09LineBundleTensorTheory C.carrier]
    [Chapter09RelativePositivityTheory C.structureMap]
    [Smooth C.structureMap]
    (D : Chapter09FiniteEffectiveCartierDivisor C.carrier) :
    ∃ D' : Chapter09FiniteEffectiveCartierDivisor C.carrier,
      chapter09RelativelyAmple C.structureMap D'.associatedLineBundle := by
  sorry

theorem chapter09_smooth_proper_curve_has_an_ample_line_bundle
    {k : Type*} [Field k]
    (C : Chapter09ProperCurveOverField k)
    [Chapter09LineBundleTensorTheory C.carrier]
    [Chapter09RelativePositivityTheory C.structureMap]
    [Smooth C.structureMap] :
    ∃ L : Chapter09LineBundle C.carrier,
      chapter09RelativelyAmple C.structureMap L := by
  sorry

theorem chapter09_smooth_proper_curve_is_projective
    {k : Type*} [Field k]
    (C : Chapter09ProperCurveOverField k)
    [Chapter09LineBundleTensorTheory C.carrier]
    [Chapter09RelativePositivityTheory C.structureMap]
    [Smooth C.structureMap] :
    Chapter09ProjectiveMorphism C.structureMap := by
  sorry

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09
