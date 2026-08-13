import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Dependencies

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04

noncomputable section

/-! ### 9.1 Embedding projective curves -/

structure Chapter09ProperCurveOverField (k : Type*) [Field k] where
  carrier : Scheme
  structureMap : carrier ⟶ Spec (.of k)
  proper : IsProper structureMap
  quasiCompact : QuasiCompact structureMap
  nonempty : Nonempty carrier
  curve : Chapter09RelativeCurve structureMap

structure Chapter09LengthTwoSubscheme (C : Scheme) where
  support : Scheme
  inclusion : support ⟶ C
  closed : IsClosedImmersion inclusion
  base : Scheme
  baseMap : support ⟶ base
  curveToBase : C ⟶ base
  overBase : inclusion ≫ curveToBase = baseMap
  finiteLocallyFree : Chapter09FiniteLocallyFreeProfile baseMap 2

theorem chapter09_length_two_subscheme_finrank
    {C : Scheme} (Z : Chapter09LengthTwoSubscheme C) (x : Z.base) :
    Scheme.Hom.finrank Z.baseMap x = 2 :=
  Z.finiteLocallyFree.rank x

theorem chapter09_serre_eventual_very_ampleness
    {k : Type*} [Field k]
    (C : Chapter09ProperCurveOverField k)
    [Chapter09LineBundleTensorTheory C.carrier]
    (L : Chapter09LineBundle C.carrier)
    (hL : chapter09RelativelyAmple C.structureMap L) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      chapter09RelativelyVeryAmple C.structureMap (chapter09LineBundlePower L n) := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the canonical pullback map on global sections is not
named in the pinned sheaf API.  The codomain is nevertheless fixed to the
actual sections of the pulled-back twist, so this interface cannot replace it
by an unrelated arbitrary type. -/
abbrev chapter09LengthTwoSectionsOn {C : Scheme}
    [Chapter09LineBundleTensorTheory C]
    (Z : Chapter09LengthTwoSubscheme C) (L : Chapter09LineBundle C) (n : ℕ) :=
  ((Scheme.Modules.pullback Z.inclusion).obj (chapter09LineBundlePower L n).module).val.sections

class Chapter09LengthTwoSectionTheory (C : Scheme)
    [Chapter09LineBundleTensorTheory C] where
  restrictionMap :
    ∀ (Z : Chapter09LengthTwoSubscheme C)
      (L : Chapter09LineBundle C) (n : ℕ),
      chapter09GlobalSection L n → chapter09LengthTwoSectionsOn Z L n

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
genuine categorical object until that canonical construction is available. -/
class Chapter09LengthTwoRestrictionTheory (C : Scheme)
    [Chapter09LineBundleTensorTheory C] where
  sequence :
    ∀ (_Z : Chapter09LengthTwoSubscheme C)
      (_L : Chapter09LineBundle C) (_n : ℕ), ShortComplex C.Modules
  restrictionTerm :
    ∀ (_Z : Chapter09LengthTwoSubscheme C)
      (_L : Chapter09LineBundle C) (_n : ℕ), C.Modules
  firstTermIso :
    ∀ (Z : Chapter09LengthTwoSubscheme C) (L : Chapter09LineBundle C) (n : ℕ),
      (sequence Z L n).X₁ ≅ restrictionTerm Z L n
  exact :
    ∀ (Z : Chapter09LengthTwoSubscheme C) (L : Chapter09LineBundle C) (n : ℕ),
      (sequence Z L n).Exact

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
  exact Chapter09LengthTwoRestrictionTheory.exact Z L n

/- LOCAL_DEPENDENCY_GUESS: the connecting morphism in the long exact
cohomology sequence is not exposed by the pinned API.  This bridge records
only the standard consequence used below, with the restriction map and the
short complex already fixed by the preceding interfaces. -/
class Chapter09LengthTwoSeparationTheory (C : Scheme)
    [Chapter09LineBundleTensorTheory C]
    [Chapter09CohomologyTheory C]
    [Chapter09LengthTwoRestrictionTheory C]
    [Chapter09LengthTwoSectionTheory C] where
  separates_of_hOne_vanishing :
    ∀ (Z : Chapter09LengthTwoSubscheme C) (L : Chapter09LineBundle C) (n : ℕ),
      chapter09HOneVanishes (chapter09IdealRestrictionSequence Z L n).X₁ →
        chapter09SectionsSeparateLengthTwo Z L n

theorem chapter09_length_two_hOne_vanishing_for_large_twists
    {k : Type*} [Field k]
    (C : Chapter09ProperCurveOverField k)
    [Chapter09LineBundleTensorTheory C.carrier]
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
    [Chapter09LengthTwoSeparationTheory C]
    (Z : Chapter09LengthTwoSubscheme C) (L : Chapter09LineBundle C) (n : ℕ)
    (hvan : chapter09HOneVanishes (chapter09IdealRestrictionSequence Z L n).X₁) :
    chapter09SectionsSeparateLengthTwo Z L n := by
  exact Chapter09LengthTwoSeparationTheory.separates_of_hOne_vanishing Z L n hvan

theorem chapter09_ample_power_separates_all_length_two_subschemes
    {k : Type*} [Field k]
    (C : Chapter09ProperCurveOverField k)
    [Chapter09LineBundleTensorTheory C.carrier]
    [Chapter09CohomologyTheory C.carrier]
    [Chapter09LengthTwoRestrictionTheory C.carrier]
    [Chapter09LengthTwoSectionTheory C.carrier]
    [Chapter09LengthTwoSeparationTheory C.carrier]
    (L : Chapter09LineBundle C.carrier)
    (hL : chapter09RelativelyAmple C.structureMap L) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      chapter09RelativelyGenerated C.structureMap (chapter09LineBundlePower L n) ∧
        ∀ Z : Chapter09LengthTwoSubscheme C.carrier,
          chapter09SectionsSeparateLengthTwo Z L n := by
  sorry

structure Chapter09ClosedCurveEmbedding
    {k : Type*} [Field k]
    (C : Chapter09ProperCurveOverField k)
    [Chapter09LineBundleTensorTheory C.carrier]
    (L : Chapter09LineBundle C.carrier) (n : ℕ) where
  witness : Chapter04VeryAmpleWitness C.structureMap
    (chapter09AsChapter04LineBundle (chapter09LineBundlePower L n))

abbrev Chapter09ClosedCurveEmbedding.map
    {k : Type*} [Field k] {C : Chapter09ProperCurveOverField k}
    [Chapter09LineBundleTensorTheory C.carrier]
    {L : Chapter09LineBundle C.carrier} {n : ℕ}
    (E : Chapter09ClosedCurveEmbedding C L n) : C.carrier ⟶
      E.witness.projectiveBundle.space :=
  E.witness.map

theorem chapter09_length_two_separation_gives_closed_embedding
    {k : Type*} [Field k]
    (C : Chapter09ProperCurveOverField k)
    [Chapter09LineBundleTensorTheory C.carrier]
    [Chapter09LengthTwoSectionTheory C.carrier]
    (L : Chapter09LineBundle C.carrier) (n : ℕ)
    (hgen : chapter09RelativelyGenerated C.structureMap (chapter09LineBundlePower L n))
    (hsep : ∀ Z : Chapter09LengthTwoSubscheme C.carrier,
      chapter09SectionsSeparateLengthTwo Z L n) :
    ∃ E : Chapter09ClosedCurveEmbedding C L n,
      IsClosedImmersion E.map := by
  sorry

theorem chapter09_ample_power_is_closed_embedding
    {k : Type*} [Field k]
    (C : Chapter09ProperCurveOverField k)
    [Chapter09LineBundleTensorTheory C.carrier]
    [Chapter09CohomologyTheory C.carrier]
    [Chapter09LengthTwoRestrictionTheory C.carrier]
    [Chapter09LengthTwoSectionTheory C.carrier]
    [Chapter09LengthTwoSeparationTheory C.carrier]
    (L : Chapter09LineBundle C.carrier)
    (hL : chapter09RelativelyAmple C.structureMap L) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ E : Chapter09ClosedCurveEmbedding C L n,
        IsClosedImmersion E.map := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the pinned tree packages the Cartier equation and
its regularity, but not the associated inverse-ideal line bundle or canonical
section in the Chapter 9 line-bundle interface. -/
structure Chapter09FiniteEffectiveCartierDivisor
    (C T : Scheme) (f : C ⟶ T) [Chapter09LineBundleTensorTheory C] where
  divisor : Chapter09EffectiveCartierDivisor C
  degree : ℕ
  finiteLocallyFree :
    Chapter09FiniteLocallyFreeProfile (divisor.ideal.subschemeι ≫ f) degree
  nonempty : Nonempty divisor.ideal.subscheme
  associatedLineBundle : Chapter09LineBundle C
  canonicalSection : chapter09GlobalSection associatedLineBundle 1

abbrev Chapter09FiniteEffectiveCartierDivisor.support
    {C T : Scheme} {f : C ⟶ T} [Chapter09LineBundleTensorTheory C]
    (D : Chapter09FiniteEffectiveCartierDivisor C T f) : Scheme :=
  D.divisor.ideal.subscheme

abbrev Chapter09FiniteEffectiveCartierDivisor.inclusion
    {C T : Scheme} {f : C ⟶ T} [Chapter09LineBundleTensorTheory C]
    (D : Chapter09FiniteEffectiveCartierDivisor C T f) : D.support ⟶ C :=
  D.divisor.ideal.subschemeι

abbrev Chapter09FiniteEffectiveCartierDivisor.closed
    {C T : Scheme} {f : C ⟶ T} [Chapter09LineBundleTensorTheory C]
    (D : Chapter09FiniteEffectiveCartierDivisor C T f) : IsClosedImmersion D.inclusion :=
  D.divisor.closed

abbrev Chapter09FiniteEffectiveCartierDivisor.effectiveCartier
    {C T : Scheme} {f : C ⟶ T} [Chapter09LineBundleTensorTheory C]
    (D : Chapter09FiniteEffectiveCartierDivisor C T f) : Prop :=
  Chapter09LocallyRegularPrincipal D.divisor.ideal

abbrev Chapter09FiniteEffectiveCartierDivisor.complement
    {C T : Scheme} {f : C ⟶ T} [Chapter09LineBundleTensorTheory C]
    (D : Chapter09FiniteEffectiveCartierDivisor C T f) : C.Opens :=
  D.divisor.ideal.support.compl

def chapter09DivisorSubsumes {C T : Scheme} {f : C ⟶ T}
    [Chapter09LineBundleTensorTheory C]
    (D E : Chapter09FiniteEffectiveCartierDivisor C T f) : Prop :=
  ∃ i : D.support ⟶ E.support, i ≫ E.inclusion = D.inclusion

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
    Nonempty (Chapter09FiniteEffectiveCartierDivisor C.carrier
      (Spec (.of k)) C.structureMap) := by
  sorry

theorem chapter09_effective_divisor_complement_is_affine
    {k : Type*} [Field k]
    (C : Chapter09ProperCurveOverField k)
    [Chapter09LineBundleTensorTheory C.carrier]
    [Smooth C.structureMap]
    (D : Chapter09FiniteEffectiveCartierDivisor C.carrier
      (Spec (.of k)) C.structureMap) :
    IsAffineOpen D.complement := by
  sorry

theorem chapter09_effective_divisor_can_be_enlarged_to_an_ample_bundle
    {k : Type*} [Field k]
    (C : Chapter09ProperCurveOverField k)
    [Chapter09LineBundleTensorTheory C.carrier]
    [Smooth C.structureMap]
    (D : Chapter09FiniteEffectiveCartierDivisor C.carrier
      (Spec (.of k)) C.structureMap) :
    ∃ D' : Chapter09FiniteEffectiveCartierDivisor C.carrier
      (Spec (.of k)) C.structureMap,
      chapter09DivisorSubsumes D D' ∧
        chapter09RelativelyAmple C.structureMap D'.associatedLineBundle := by
  sorry

theorem chapter09_smooth_proper_curve_has_an_ample_line_bundle
    {k : Type*} [Field k]
    (C : Chapter09ProperCurveOverField k)
    [Smooth C.structureMap] :
    ∃ L : Chapter09LineBundle C.carrier,
      chapter09RelativelyAmple C.structureMap L := by
  sorry

theorem chapter09_smooth_proper_curve_is_projective
    {k : Type*} [Field k]
    (C : Chapter09ProperCurveOverField k)
    [Chapter09LineBundleTensorTheory C.carrier]
    [Smooth C.structureMap] :
    Chapter09ProjectiveMorphism C.structureMap := by
  sorry

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09
