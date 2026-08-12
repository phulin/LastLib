import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter12.Section02GrassmannianConstruction

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter12

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped BigOperators

/-! ## 12.3. Representability with fixed polynomial -/

/-- One summand in a Gotzmann binomial expansion. -/
def chapter12GotzmannTerm (a i n : ℕ) : ℚ :=
  (Nat.choose (n + a - i) a : ℚ)

/-- The displayed binomial expansion of a numerical Hilbert polynomial. -/
structure Chapter12GotzmannExpansion
    (P : Chapter12NumericalPolynomial) (r : ℕ) where
  length : ℕ
  a : Fin length → ℕ
  monotone : ∀ i j : Fin length, i.1 ≤ j.1 → a j ≤ a i
  bounded : ∀ i : Fin length, a i ≤ r
  expansion : ∀ n : ℕ,
    P.eval (n : ℚ) = ∑ i : Fin length, chapter12GotzmannTerm (a i) i.1 n

/- The occurrence hypothesis in Gotzmann's theorem is kept separate from the
  binomial expansion it produces. -/
structure Chapter12NumericalHilbertPolynomialRealization
    (P : Chapter12NumericalPolynomial) (r : ℕ) where
  coefficientRing : Type*
  [coefficientRing_commRing : CommRing coefficientRing]
  ideal : Chapter12SaturatedHomogeneousIdeal coefficientRing r P
  ideal_has_polynomial :
    chapter12HasHomogeneousHilbertPolynomial ideal.ideal P

attribute [instance] Chapter12NumericalHilbertPolynomialRealization.coefficientRing_commRing

def chapter12IsNumericalHilbertPolynomial (P : Chapter12NumericalPolynomial)
    (r : ℕ) : Prop :=
  Nonempty (Chapter12NumericalHilbertPolynomialRealization.{0} P r)

theorem chapter12_gotzmann_expansion_exists
    (P : Chapter12NumericalPolynomial) (r : ℕ)
    (hP : chapter12IsNumericalHilbertPolynomial P r) :
    Nonempty (Chapter12GotzmannExpansion P r) := by
  sorry

theorem chapter12_gotzmann_expansion_unique
    (P : Chapter12NumericalPolynomial) (r : ℕ)
    (E E' : Chapter12GotzmannExpansion P r) : E = E' := by
  sorry

/-- The number of summands in the unique Gotzmann expansion. -/
noncomputable def chapter12GotzmannLength
    (P : Chapter12NumericalPolynomial) (r : ℕ)
    (hP : chapter12IsNumericalHilbertPolynomial P r) : ℕ :=
  (Classical.choice (chapter12_gotzmann_expansion_exists P r hP)).length

theorem chapter12_gotzmann_length_is_unique
    (P : Chapter12NumericalPolynomial) (r : ℕ)
    (hP : chapter12IsNumericalHilbertPolynomial P r)
    (E : Chapter12GotzmannExpansion P r) :
    E.length = chapter12GotzmannLength P r hP := by
  sorry

/-- The regularity conclusion in Gotzmann boundedness. -/
theorem chapter12_gotzmann_regular_bound
    (P : Chapter12NumericalPolynomial) (r : ℕ)
    (hP : chapter12IsNumericalHilbertPolynomial P r)
    {A : Type*} [CommRing A]
    (I : Chapter12SaturatedHomogeneousIdeal A r P)
    (hI : chapter12HasHomogeneousHilbertPolynomial I.ideal P) :
    chapter12IsMRegular I.ideal (chapter12GotzmannLength P r hP) ∧
      chapter12IsGeneratedFromDegree I.ideal (chapter12GotzmannLength P r hP) := by
  sorry

/-- Gotzmann regularity is stated without a characteristic hypothesis. -/
theorem chapter12_gotzmann_regular_bound_characteristic_free
    (P : Chapter12NumericalPolynomial) (r : ℕ)
    (hP : chapter12IsNumericalHilbertPolynomial P r)
    {A : Type*} [CommRing A]
    (I : Chapter12SaturatedHomogeneousIdeal A r P)
    (hI : chapter12HasHomogeneousHilbertPolynomial I.ideal P) :
    chapter12IsMRegular I.ideal (chapter12GotzmannLength P r hP) := by
  sorry

/-- A scheme over `S` representing the fixed-polynomial Hilbert functor. -/
structure Chapter12HilbertRepresentingScheme
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D)
    (P : Chapter12NumericalPolynomial) where
  carrier : Scheme
  structureMap : carrier ⟶ D.base
  projective : chapter12IsProjectiveMorphism structureMap
  finitePresentation : LocallyOfFinitePresentation structureMap
  representingEquivalence : ∀ T : Chapter12SchemeOver D.base,
    (T ⟶ Over.mk structureMap) ≃ Chapter12HilbertFamily D H T P
  universalFamily :
    Chapter12HilbertFamily D H (Over.mk structureMap) P

attribute [instance] Chapter12HilbertRepresentingScheme.finitePresentation

/-- The existence form of the Hilbert representability theorem. -/
theorem chapter12_hilbert_representability_exists
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D)
    (P : Chapter12NumericalPolynomial) :
    Nonempty (Chapter12HilbertRepresentingScheme D H P) := by
  sorry

/-- A chosen representing scheme, as in the source notation `Hilb^P(X/S)`. -/
noncomputable def chapter12HilbertRepresentingScheme
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D)
    (P : Chapter12NumericalPolynomial) :
    Chapter12HilbertRepresentingScheme D H P :=
  Classical.choice (chapter12_hilbert_representability_exists D H P)

/-- The representing scheme itself, separated from its universal family. -/
abbrev chapter12HilbertScheme
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D)
    (P : Chapter12NumericalPolynomial) : Scheme :=
  (chapter12HilbertRepresentingScheme D H P).carrier

/-- Its structure morphism to the base. -/
abbrev chapter12HilbertSchemeMap
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D)
    (P : Chapter12NumericalPolynomial) :
    chapter12HilbertScheme D H P ⟶ D.base :=
  (chapter12HilbertRepresentingScheme D H P).structureMap

theorem chapter12HilbertScheme_is_projective
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D)
    (P : Chapter12NumericalPolynomial) :
    chapter12IsProjectiveMorphism (chapter12HilbertSchemeMap D H P) := by
  exact (chapter12HilbertRepresentingScheme D H P).projective

theorem chapter12HilbertScheme_is_finitely_presented
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D)
    (P : Chapter12NumericalPolynomial) :
    LocallyOfFinitePresentation (chapter12HilbertSchemeMap D H P) := by
  exact (chapter12HilbertRepresentingScheme D H P).finitePresentation

/-- The universal family as a closed family on `X ×ₛ Hilb^P(X/S)`. -/
abbrev chapter12UniversalFamily
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D)
    (P : Chapter12NumericalPolynomial) :
    Chapter12HilbertFamily D H
      (Over.mk (chapter12HilbertSchemeMap D H P)) P :=
  (chapter12HilbertRepresentingScheme D H P).universalFamily

theorem chapter12UniversalFamily_is_flat
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D)
    (P : Chapter12NumericalPolynomial) :
    Flat (chapter12FamilyProjection D
      (Over.mk (chapter12HilbertSchemeMap D H P))
      (chapter12UniversalFamily D H P).closed.ideal) := by
  exact (chapter12UniversalFamily D H P).closed.flat

theorem chapter12UniversalFamily_is_finitely_presented
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D)
    (P : Chapter12NumericalPolynomial) :
    LocallyOfFinitePresentation (chapter12FamilyProjection D
      (Over.mk (chapter12HilbertSchemeMap D H P))
      (chapter12UniversalFamily D H P).closed.ideal) := by
  exact (chapter12UniversalFamily D H P).closed.finitePresentation

/-- The universal property, naturally in every `S`-scheme `T`. -/
def chapter12HilbertRepresentingEquivalence
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D)
    (P : Chapter12NumericalPolynomial)
    (T : Chapter12SchemeOver D.base) :
    (T ⟶ Over.mk (chapter12HilbertSchemeMap D H P)) ≃
      Chapter12HilbertFamily D H T P :=
  (chapter12HilbertRepresentingScheme D H P).representingEquivalence T

theorem chapter12HilbertRepresentingEquivalence_natural
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D)
    (P : Chapter12NumericalPolynomial)
    {T U : Chapter12SchemeOver D.base} (g : T ⟶ U)
    (f : U ⟶ Over.mk (chapter12HilbertSchemeMap D H P)) :
    chapter12HilbertRepresentingEquivalence D H P T (g ≫ f) =
      chapter12PullbackFamily D H g
        (chapter12HilbertRepresentingEquivalence D H P U f) := by
  sorry

/-- Containment of homogeneous ideals is the closed condition for `Z ⊂ X`. -/
def chapter12HomogeneousIdealContains
    {A : Type*} [CommRing A]
    (I J : Chapter12HomogeneousIdeal A) : Prop :=
  ∃ h : I.algebra = J.algebra, ∀ n : ℕ,
    J.degreePart n ⊆ h ▸ I.degreePart n

/-- The finite-degree containment condition used to cut the Hilbert locus for a closed `X`. -/
def chapter12FiniteDegreeIdealContainment
    {A : Type*} [CommRing A]
    (I J : Chapter12HomogeneousIdeal A) (m : ℕ) : Prop :=
  ∃ h : I.algebra = J.algebra, ∀ n : ℕ, m ≤ n →
    J.degreePart n ⊆ h ▸ I.degreePart n

/- The condition above is the book-facing finite presentation of the
  determinantal containment equations. -/
structure Chapter12ClosedAmbientHilbertLocus
    (D : Chapter12ProjectiveFamilySetup)
    (E : Chapter12ProjectiveEmbedding D)
    (H : Chapter12HilbertPolynomialTheory D)
    (P : Chapter12NumericalPolynomial) where
  carrier : Scheme
  inclusion : carrier ⟶ chapter12HilbertScheme D H P
  closed : IsClosedImmersion inclusion
  universal_ideal_contains_ambient_ideal : Prop
  containment_equations_start_at_common_regularity_bound : Prop

theorem chapter12_closed_ambient_hilbert_locus_exists
    (D : Chapter12ProjectiveFamilySetup)
    (E : Chapter12ProjectiveEmbedding D)
    (H : Chapter12HilbertPolynomialTheory D)
    (P : Chapter12NumericalPolynomial) :
    Nonempty (Chapter12ClosedAmbientHilbertLocus D E H P) := by
  sorry

noncomputable def chapter12ClosedAmbientHilbertLocus
    (D : Chapter12ProjectiveFamilySetup)
    (E : Chapter12ProjectiveEmbedding D)
    (H : Chapter12HilbertPolynomialTheory D)
    (P : Chapter12NumericalPolynomial) :
    Chapter12ClosedAmbientHilbertLocus D E H P :=
  Classical.choice (chapter12_closed_ambient_hilbert_locus_exists D E H P)

theorem chapter12ClosedAmbientHilbertLocus_is_closed
    (D : Chapter12ProjectiveFamilySetup)
    (E : Chapter12ProjectiveEmbedding D)
    (H : Chapter12HilbertPolynomialTheory D)
    (P : Chapter12NumericalPolynomial) :
    IsClosedImmersion (chapter12ClosedAmbientHilbertLocus D E H P).inclusion := by
  exact (chapter12ClosedAmbientHilbertLocus D E H P).closed

end
end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter12
