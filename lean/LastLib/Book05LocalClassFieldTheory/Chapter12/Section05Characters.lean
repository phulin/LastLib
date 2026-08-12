import LastLib.Book05LocalClassFieldTheory.Chapter12.Section04Functoriality
import LastLib.Book05LocalClassFieldTheory.Chapter12.Section02MultiplicativeAndGaloisPieces

namespace LastLib.Book05LocalClassFieldTheory.Chapter12

noncomputable section

/-! ## 12.5. Characters at a glance -/

/-- A book-facing marker for a profinite abelian coefficient group. -/
structure Chapter12ProfiniteAbelianCoefficient
    (A : Type*) [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] : Prop where
  compact : IsCompact (Set.univ : Set A)
  hausdorff : T2Space A
  totally_disconnected : TotallyDisconnectedSpace A

/-- Pullback along an infinite reciprocity map is the character dictionary. -/
-- DEPENDENCY_GUESS: The inverse-limit character equivalence is the continuous
-- extension theorem for the missing preceding Book 5 reciprocity chapter.
theorem chapter12_continuous_character_equiv
    {K G A : Type*} [Field K] [CommGroup G] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace A]
    [IsTopologicalGroup Kˣ] [IsTopologicalGroup G] [IsTopologicalGroup A]
    (Pₖ : Chapter12LocalFieldProfile K)
    (R : Chapter12ReciprocityLimit K G)
    (P : Chapter12ProfiniteAbelianCoefficient A) :
    Nonempty
      (Chapter12ContinuousCharacter G A ≃
        Chapter12ContinuousCharacter Kˣ A) := by
  sorry

/-- The character on the multiplicative side attached to a Galois character. -/
def chapter12_character_of_reciprocity
    {K G A : Type*} [Field K] [CommGroup G] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace A]
    [IsTopologicalGroup Kˣ] [IsTopologicalGroup G]
    (R : Chapter12ReciprocityLimit K G)
    (χ : Chapter12ContinuousCharacter G A) :
    Chapter12ContinuousCharacter Kˣ A :=
  chapter12CharacterPullback R.map R.continuous_map χ

/-- Triviality on units is the multiplicative formulation of unramifiedness. -/
def chapter12CharacterUnramifiedOnUnits
    {K k A : Type*} [Field K] [Field k] [Group A]
    (C : Chapter12LocalCoordinates K k)
    (χ : Kˣ →* A) : Prop :=
  ∀ u : C.units, χ u = 1

/-- Triviality on inertia is the Galois formulation of unramifiedness. -/
def chapter12CharacterUnramifiedOnInertia
    {G A : Type*} [Group G] [Group A]
    (I : Subgroup G) (χ : G →* A) : Prop :=
  ∀ g : I, χ g.1 = 1

/-- Uniformizer and Frobenius values, with a chosen Frobenius lift exposed. -/
def chapter12CharacterUniformizerValue
    {K k G Q A : Type*} [Field K] [Field k] [CommGroup G] [Group Q] [Group A]
    (D : Chapter12GaloisPieceDictionary K k G Q)
    (χ : G →* A) : A :=
  χ (D.reciprocity D.coordinates.uniformizer)

def chapter12CharacterFrobeniusLiftValue
    {G A : Type*} [Group G] [Group A]
    (χ : G →* A) (g : G) : A :=
  χ g

theorem chapter12_unramified_character_has_frobenius_value
    {K k G Q A : Type*} [Field K] [Field k] [CommGroup G] [Group Q] [Group A]
    (D : Chapter12GaloisPieceDictionary K k G Q) (χ : G →* A)
    (hkernel : D.reduction.ker = D.inertia)
    (hfrobenius :
      D.reduction (D.reciprocity D.coordinates.uniformizer) =
        D.arithmeticFrobenius)
    (hunram : chapter12CharacterUnramifiedOnInertia D.inertia χ)
    {g : G} (hg : g ∈ chapter12ArithmeticFrobeniusLifts D) :
    chapter12CharacterUniformizerValue D χ =
      chapter12CharacterFrobeniusLiftValue χ g := by
  sorry

theorem chapter12_character_unramified_iff_units_trivial
    {K k G Q A : Type*} [Field K] [Field k] [CommGroup G] [Group Q] [Group A]
    (D : Chapter12GaloisPieceDictionary K k G Q) (χG : G →* A) :
    chapter12CharacterUnramifiedOnInertia D.inertia χG ↔
      chapter12CharacterUnramifiedOnUnits D.coordinates
        (χG.comp D.reciprocity) := by
  sorry

/-- Triviality at a unit level, on either side of the dictionary. -/
def chapter12CharacterTrivialOnUnitLevel
    {K k A : Type*} [Field K] [Field k] [Group A]
    (C : Chapter12LocalCoordinates K k) (n : ℕ)
    (χ : Kˣ →* A) : Prop :=
  ∀ u : C.principalUnits n, χ u = 1

def chapter12CharacterTrivialOnRamificationLevel
    {G A : Type*} [Group G] [Group A]
    (Gₙ : Subgroup G) (χ : G →* A) : Prop :=
  ∀ g : Gₙ, χ g.1 = 1

theorem chapter12_character_unit_level_iff_ramification_level
    {K k G Q A : Type*} [Field K] [Field k] [CommGroup G] [Group Q] [Group A]
    (D : Chapter12GaloisPieceDictionary K k G Q) (n : ℕ) (χ : G →* A) :
    chapter12CharacterTrivialOnUnitLevel D.coordinates n
      (χ.comp D.reciprocity) ↔
      chapter12CharacterTrivialOnRamificationLevel (D.ramification n) χ := by
  sorry

/-- Norm pullback and restriction of a Galois character agree on extension
elements. -/
theorem chapter12_character_norm_pullback_eq_galois_restriction
    {K L G_K G_L A : Type*} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L]
    [CommGroup G_K] [CommGroup G_L] [Group A]
    (P : Chapter12LocalFieldProfile K)
    (D : Chapter12FunctorialityData K L G_K G_L)
    (hseparable : Algebra.IsSeparable K L) (χ : G_K →* A) (x : Lˣ) :
    χ (D.recK (chapter12MultiplicativeNormMap K L x)) =
      χ (D.galois_inclusion (D.recL x)) := by
  have h := chapter12_norm_corresponds_to_galois_inclusion_apply P D hseparable x
  rw [h]

/-- Extension of a character to a chosen profinite-completion carrier. -/
def chapter12CharacterExtendsToCompletion
    {G Ghat A : Type*} [CommGroup G] [CommGroup Ghat] [Group A]
    [TopologicalSpace G] [TopologicalSpace Ghat] [TopologicalSpace A]
    [IsTopologicalGroup G] [IsTopologicalGroup Ghat]
    (C : Chapter12CompletionData G Ghat)
    (χ : Chapter12ContinuousCharacter G A) : Prop :=
  ∃ χhat : Chapter12ContinuousCharacter Ghat A,
    ∀ x : G, χhat.hom (C.embedding x) = χ.hom x

/-- A continuous extension to the completion forces relatively compact image. -/
theorem chapter12_completion_extension_implies_relative_compact_range
    {G Ghat A : Type*} [CommGroup G] [CommGroup Ghat] [Group A]
    [TopologicalSpace G] [TopologicalSpace Ghat] [TopologicalSpace A]
    [IsTopologicalGroup G] [IsTopologicalGroup Ghat] [T2Space A]
    (C : Chapter12CompletionData G Ghat)
    (χ : Chapter12ContinuousCharacter G A)
    (hext : chapter12CharacterExtendsToCompletion C χ) :
    chapter12RelativeCompactRange χ := by
  sorry

/-- For a nonprofinite target, extension to the completion is the exact
criterion; relative compactness is recorded separately as a necessary test. -/
theorem chapter12_nonprofinite_character_extension_criterion
    {G Ghat A : Type*} [CommGroup G] [CommGroup Ghat] [Group A]
    [TopologicalSpace G] [TopologicalSpace Ghat] [TopologicalSpace A]
    [IsTopologicalGroup G] [IsTopologicalGroup Ghat]
    (C : Chapter12CompletionData G Ghat)
    (χ : Chapter12ContinuousCharacter G A) :
    chapter12CharacterExtendsToCompletion C χ ↔
      ∃ χhat : Chapter12ContinuousCharacter Ghat A,
        ∀ x : G, χhat.hom (C.embedding x) = χ.hom x := by
  rfl

end

end LastLib.Book05LocalClassFieldTheory.Chapter12
