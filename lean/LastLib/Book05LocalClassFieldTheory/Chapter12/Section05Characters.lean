import LastLib.Book05LocalClassFieldTheory.Chapter12.Section04Functoriality
import LastLib.Book05LocalClassFieldTheory.Chapter12.Section02MultiplicativeAndGaloisPieces

namespace LastLib.Book05LocalClassFieldTheory.Chapter12

noncomputable section

open LastLib.Book05LocalClassFieldTheory.Chapter09

/-! ## 12.5. Characters at a glance -/

/-- Pullback along an infinite reciprocity map is the character dictionary. -/
theorem chapter12_continuous_character_equiv
    {K G A : Type*} [Field K] [Group G] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace A]
    [IsTopologicalGroup G] [IsTopologicalGroup A]
    [T2Space A] [CompactSpace A] [TotallyDisconnectedSpace A]
    (R : Chapter12ReciprocityLimit K G) :
    Nonempty
      (Chapter12ContinuousCharacter G A ≃
        Chapter12ContinuousCharacter Kˣ A) := by
  exact ⟨LastLib.Book05LocalClassFieldTheory.Chapter11.chapter11ContinuousCharacterEquiv R⟩

/-- The character on the multiplicative side attached to a Galois character. -/
def chapter12_character_of_reciprocity
    {K G A : Type*} [Field K] [Group G] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace A]
    [IsTopologicalGroup G] [IsTopologicalGroup A]
    [T2Space A] [CompactSpace A] [TotallyDisconnectedSpace A]
    (R : Chapter12ReciprocityLimit K G)
    (χ : Chapter12ContinuousCharacter G A) :
    Chapter12ContinuousCharacter Kˣ A :=
  LastLib.Book05LocalClassFieldTheory.Chapter11.chapter11ContinuousCharacterEquiv R χ

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
    {K k G Q A : Type*} [Field K] [Field k] [CommGroup G] [Finite G] [Group Q] [Group A]
    (D : Chapter12GaloisPieceDictionary K k G Q)
    (χ : G →* A) : A :=
  χ (D.reciprocity D.coordinates.uniformizer)

def chapter12CharacterFrobeniusLiftValue
    {G A : Type*} [Group G] [Group A]
    (χ : G →* A) (g : G) : A :=
  χ g

theorem chapter12_unramified_character_has_frobenius_value
    {K k G Q A : Type*} [Field K] [Field k] [CommGroup G] [Finite G] [Group Q] [Group A]
    (D : Chapter12GaloisPieceDictionary K k G Q) (χ : G →* A)
    (hunram : chapter12CharacterUnramifiedOnInertia
      D.inertia χ)
    {g : G} (hg : g ∈ chapter12ArithmeticFrobeniusLifts D) :
    chapter12CharacterUniformizerValue D χ =
      chapter12CharacterFrobeniusLiftValue χ g := by
  change χ (D.reciprocity D.coordinates.uniformizer) = χ g
  have hdiff : g⁻¹ * D.reciprocity D.coordinates.uniformizer ∈ D.inertia :=
    chapter12_frobenius_lifts_differ_by_inertia D D.reduction_kernel hg
      D.uniformizer_mod_inertia
  have hχ : χ (g⁻¹ * D.reciprocity D.coordinates.uniformizer) = 1 :=
    hunram ⟨g⁻¹ * D.reciprocity D.coordinates.uniformizer, hdiff⟩
  rw [map_mul, map_inv] at hχ
  calc
    χ (D.reciprocity D.coordinates.uniformizer) =
        χ g * ((χ g)⁻¹ * χ (D.reciprocity D.coordinates.uniformizer)) := by
          rw [← mul_assoc, mul_inv_cancel, one_mul]
    _ = χ g * 1 := by rw [hχ]
    _ = χ g := mul_one _

theorem chapter12_character_unramified_iff_units_trivial
    {K k G Q A : Type*} [Field K] [Field k] [CommGroup G] [Finite G] [Group Q] [Group A]
    (D : Chapter12GaloisPieceDictionary K k G Q) (χG : G →* A) :
    chapter12CharacterUnramifiedOnInertia
        D.inertia χG ↔
    chapter12CharacterUnramifiedOnUnits D.coordinates
        (χG.comp D.reciprocity) := by
  constructor
  · intro hunram u
    change χG (D.reciprocity u) = 1
    exact hunram ⟨D.reciprocity u, by
      rw [D.inertia_eq_units]
      exact Subgroup.mem_map_of_mem D.reciprocity u.property⟩
  · intro hunits g
    have hg : (g : G) ∈ chapter12GaloisInertia D.coordinates D.reciprocity := by
      rw [← D.inertia_eq_units]
      exact g.property
    rcases Subgroup.mem_map.mp hg with ⟨u, hu, hgu⟩
    have hunit := hunits ⟨u, hu⟩
    change χG (D.reciprocity u) = 1 at hunit
    change χG g.1 = 1
    rw [← hgu]
    exact hunit

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
    {K k G Q A : Type*} [Field K] [Field k] [CommGroup G] [Finite G] [Group Q] [Group A]
    (D : Chapter12GaloisPieceDictionary K k G Q) (n : ℕ) (χ : G →* A) :
    chapter12CharacterTrivialOnUnitLevel D.coordinates n
      (χ.comp D.reciprocity) ↔
      chapter12CharacterTrivialOnRamificationLevel
        (D.ramification n) χ := by
  constructor
  · intro hunit g
    have hg : (g : G) ∈ chapter12GaloisRamification D.coordinates D.reciprocity n := by
      rw [← D.ramification_eq_principal n]
      exact g.property
    rcases Subgroup.mem_map.mp hg with ⟨u, hu, hgu⟩
    have hvalue := hunit ⟨u, hu⟩
    change χ (D.reciprocity u) = 1 at hvalue
    change χ g.1 = 1
    rw [← hgu]
    exact hvalue
  · intro hram u
    change χ (D.reciprocity u) = 1
    exact hram ⟨D.reciprocity u, by
      rw [D.ramification_eq_principal n]
      exact Subgroup.mem_map_of_mem D.reciprocity u.property⟩

/-- Norm pullback and restriction of a Galois character agree on extension
elements. -/
theorem chapter12_character_norm_pullback_eq_galois_restriction
    (K L Ks A : Type) [Field K] [Field L] [Field Ks]
    [Algebra K L] [Algebra K Ks] [Algebra L Ks]
    [IsScalarTower K L Ks] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [Group A]
    (D : Chapter12FunctorialityData K L Ks)
    (χ : Abelianization (Gal(Ks / K)) →* A) (x : Lˣ) :
    χ (D.reciprocity.recK.reciprocity (chapter12MultiplicativeNormMap K L x)) =
      χ (chapter09GaloisInclusionAbelianization K L Ks
        (D.reciprocity.recL.reciprocity x)) := by
  have h := chapter12_norm_corresponds_to_galois_inclusion_apply K L Ks D x
  rw [h]

/-- Extension of a character through the canonical profinite completion of
the local multiplicative group. -/
abbrev chapter12CharacterExtendsToCompletion
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A] [IsTopologicalGroup A]
    (χ : Chapter12ContinuousCharacter Kˣ A) : Prop :=
  LastLib.Book05LocalClassFieldTheory.Chapter11.chapter11ProfiniteExtensionOf χ

/-- A continuous extension to the completion forces relatively compact image. -/
theorem chapter12_completion_extension_implies_relative_compact_range
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [UniformSpace A] [IsUniformGroup A]
    [IsTopologicalGroup A] [T2Space A]
    (χ : Chapter12ContinuousCharacter Kˣ A)
    (hext : chapter12CharacterExtendsToCompletion χ) :
    chapter12RelativeCompactRange χ := by
  sorry

/-- For a nonprofinite target, extension to the completion is the exact
criterion; relative compactness is recorded separately as a necessary test. -/
theorem chapter12_nonprofinite_character_extension_criterion
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [UniformSpace A] [IsUniformGroup A]
    [IsTopologicalGroup A] [T2Space A]
    (χ : Chapter12ContinuousCharacter Kˣ A)
    (hcofinal : LastLib.Book05LocalClassFieldTheory.Chapter11.chapter11OpenFiniteIndexCofinality
      (K := K)) :
    chapter12CharacterExtendsToCompletion χ ↔
      IsComplete (closure (Set.range χ)) ∧
        LastLib.Book05LocalClassFieldTheory.Chapter11.chapter11FiniteIndexNeighborhoodCondition χ := by
  exact LastLib.Book05LocalClassFieldTheory.Chapter11.chapter11_profinite_extension_iff_finite_index_neighborhood_condition
    χ hcofinal

end

end LastLib.Book05LocalClassFieldTheory.Chapter12
