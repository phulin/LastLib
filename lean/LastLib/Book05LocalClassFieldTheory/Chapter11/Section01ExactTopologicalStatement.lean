import LastLib.Book05LocalClassFieldTheory.Chapter11.Dependencies
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.Complex

namespace LastLib.Book05LocalClassFieldTheory.Chapter11

noncomputable section

open scoped Topology

/-! ## 11.1. The exact topological statement -/

def chapter11IsProfiniteAbelianTarget
    (A : Type*) [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [T2Space A] : Prop :=
  Nonempty (CompactSpace A) ∧ Nonempty (TotallyDisconnectedSpace A)

def chapter11FactorsThroughAbelianization
    {G A : Type*} [Group G] [CommGroup A]
    [TopologicalSpace G] [TopologicalSpace A] [IsTopologicalGroup G]
    (ρ : G →ₜ* A) : Prop :=
  ∃ ρab : TopologicalAbelianization G →ₜ* A,
    ρ = ρab.comp (chapter11AbelianizationMap G)

theorem chapter11_galois_character_factors_through_abelianization
    {G A : Type*} [Group G] [CommGroup A]
    [TopologicalSpace G] [TopologicalSpace A] [IsTopologicalGroup G]
    [T2Space A] (ρ : G →ₜ* A) :
    chapter11FactorsThroughAbelianization ρ := by
  sorry

noncomputable def chapter11CharacterAbelianization
    {G A : Type*} [Group G] [CommGroup A]
    [TopologicalSpace G] [TopologicalSpace A] [IsTopologicalGroup G]
    [T2Space A] (ρ : G →ₜ* A) : TopologicalAbelianization G →ₜ* A :=
  Classical.choose (chapter11_galois_character_factors_through_abelianization ρ)

theorem chapter11CharacterAbelianization_spec
    {G A : Type*} [Group G] [CommGroup A]
    [TopologicalSpace G] [TopologicalSpace A] [IsTopologicalGroup G]
    [T2Space A] (ρ : G →ₜ* A) :
    ρ = (chapter11CharacterAbelianization ρ).comp
      (chapter11AbelianizationMap G) := by
  exact Classical.choose_spec
    (chapter11_galois_character_factors_through_abelianization ρ)

def chapter11ProfiniteExtensionOf
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    [IsTopologicalGroup A]
    (χ : Kˣ →ₜ* A) : Prop :=
  ∃ F : Chapter11ProfiniteCompletion Kˣ →ₜ* A,
    ∀ x : Kˣ,
      F (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionEtaFn
        Kˣ x) = χ x

theorem chapter11_profinite_extension_unique
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A] [IsTopologicalGroup A]
    [T2Space A]
    (χ : Kˣ →ₜ* A)
    {F₁ F₂ : Chapter11ProfiniteCompletion Kˣ →ₜ* A}
    (h₁ : ∀ x : Kˣ,
      F₁ (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionEtaFn
        Kˣ x) = χ x)
    (h₂ : ∀ x : Kˣ,
      F₂ (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionEtaFn
        Kˣ x) = χ x) :
    F₁ = F₂ := by
  sorry

def chapter11FiniteIndexNeighborhoodCondition
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A] [IsTopologicalGroup A]
    (χ : Kˣ →ₜ* A) : Prop :=
  ∀ V : Set A, V ∈ 𝓝[closure (Set.range χ)] (1 : A) →
    ∃ H : Subgroup Kˣ,
      IsOpen (H : Set Kˣ) ∧ H.FiniteIndex ∧
        ∀ x ∈ H, χ x ∈ V

theorem chapter11_profinite_extension_iff_finite_index_neighborhood_condition
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ]
    [UniformSpace A] [IsUniformGroup A]
    [IsTopologicalGroup A]
    [T2Space A]
    (χ : Kˣ →ₜ* A)
    (hcofinal : chapter11OpenFiniteIndexCofinality (K := K)) :
    chapter11ProfiniteExtensionOf χ ↔
      IsComplete (closure (Set.range χ)) ∧
        chapter11FiniteIndexNeighborhoodCondition χ := by
  sorry

theorem chapter11_profinite_extension_iff_finite_index_neighborhood_condition_of_complete_target
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ]
    [UniformSpace A] [IsUniformGroup A]
    [IsTopologicalGroup A]
    [T2Space A] [CompleteSpace A]
    (χ : Kˣ →ₜ* A)
    (hcofinal : chapter11OpenFiniteIndexCofinality (K := K)) :
    chapter11ProfiniteExtensionOf χ ↔
      chapter11FiniteIndexNeighborhoodCondition χ := by
  sorry

/-!
The main classification is stated as an equivalence.  The proof uses the
completion comparison in `Chapter11ReciprocityData` and the universal
-/

noncomputable def chapter11AbelianContinuousCharacterEquiv
    {K G A : Type*} [Field K] [Group G] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace A]
    [IsTopologicalGroup G] [IsTopologicalGroup A] [T2Space A]
    [CompactSpace A] [TotallyDisconnectedSpace A]
    (R : Chapter11ReciprocityData K G) :
    (TopologicalAbelianization G →ₜ* A) ≃ (Kˣ →ₜ* A) := by
  sorry

noncomputable def chapter11ContinuousCharacterEquiv
    {K G A : Type*} [Field K] [Group G] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace A]
    [IsTopologicalGroup G] [IsTopologicalGroup A] [T2Space A]
    [CompactSpace A] [TotallyDisconnectedSpace A]
    (R : Chapter11ReciprocityData K G) :
    (G →ₜ* A) ≃ (Kˣ →ₜ* A) := by
  sorry

theorem chapter11_abelian_continuous_character_equiv_apply
    {K G A : Type*} [Field K] [Group G] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace A]
    [IsTopologicalGroup G] [IsTopologicalGroup A] [T2Space A]
    [CompactSpace A] [TotallyDisconnectedSpace A]
    (R : Chapter11ReciprocityData K G)
    (ρ : TopologicalAbelianization G →ₜ* A) :
    chapter11AbelianContinuousCharacterEquiv R ρ =
      ρ.comp R.reciprocity := by
  sorry

theorem chapter11_continuous_character_equiv_apply
    {K G A : Type*} [Field K] [Group G] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace A]
    [IsTopologicalGroup G] [IsTopologicalGroup A] [T2Space A]
    [CompactSpace A] [TotallyDisconnectedSpace A]
    (R : Chapter11ReciprocityData K G) (ρ : G →ₜ* A) :
    chapter11ContinuousCharacterEquiv R ρ =
      ((chapter11AbelianContinuousCharacterEquiv R)
        (chapter11CharacterAbelianization ρ)) := by
  sorry

theorem chapter11_theorem_11_1
    {K G A : Type*} [Field K] [Group G] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace A]
    [IsTopologicalGroup G] [IsTopologicalGroup A] [T2Space A]
    [CompactSpace A] [TotallyDisconnectedSpace A]
    (R : Chapter11ReciprocityData K G) :
    Nonempty ((G →ₜ* A) ≃ (Kˣ →ₜ* A)) := by
  exact ⟨chapter11ContinuousCharacterEquiv R⟩

theorem chapter11_continuous_character_equiv_bijective
    {K G A : Type*} [Field K] [Group G] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace A]
    [IsTopologicalGroup G] [IsTopologicalGroup A] [T2Space A]
    [CompactSpace A] [TotallyDisconnectedSpace A]
    (R : Chapter11ReciprocityData K G) :
    Function.Bijective (chapter11ContinuousCharacterEquiv (A := A) R) := by
  exact (chapter11ContinuousCharacterEquiv (A := A) R).bijective

theorem chapter11_continuous_character_equiv_natural
    {K G A B : Type*} [Field K] [Group G] [CommGroup A] [CommGroup B]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace A]
    [TopologicalSpace B] [IsTopologicalGroup G] [IsTopologicalGroup A]
    [IsTopologicalGroup B] [T2Space A] [T2Space B]
    [CompactSpace A] [TotallyDisconnectedSpace A]
    [CompactSpace B] [TotallyDisconnectedSpace B]
    (R : Chapter11ReciprocityData K G) (f : A →ₜ* B) (ρ : G →ₜ* A) :
    (chapter11ContinuousCharacterEquiv R) (f.comp ρ) =
      f.comp ((chapter11ContinuousCharacterEquiv R) ρ) := by
  sorry

def chapter11CharacterOfPair
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A] [IsTopologicalGroup A]
    (D : Chapter11LocalFieldData K) (α : A)
    (η : D.unitGroup →ₜ* A) : Kˣ →ₜ* A :=
  { toFun := fun x =>
      let p := D.decomposition.symm x
      α ^ p.1.toAdd * η p.2
    map_one' := by
      sorry
    map_mul' := by
      intro x y
      sorry
    continuous_toFun := by
      sorry }

theorem chapter11_character_of_pair_apply_decomposition
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A] [IsTopologicalGroup A]
    (D : Chapter11LocalFieldData K) (α : A)
    (η : D.unitGroup →ₜ* A) (r : ℤ) (u : D.unitGroup) :
    chapter11CharacterOfPair D α η
        (D.uniformizer ^ r * (u : Kˣ)) = α ^ r * η u := by
  sorry

def chapter11CharacterPairEquiv
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A] [IsTopologicalGroup A]
    (D : Chapter11LocalFieldData K) :
    (Kˣ →ₜ* A) ≃ (A × (D.unitGroup →ₜ* A)) where
  toFun χ := (χ D.uniformizer, χ.comp (chapter11UnitInclusion D))
  invFun p := chapter11CharacterOfPair D p.1 p.2
  left_inv := by
    intro χ
    ext x
    sorry
  right_inv := by
    rintro ⟨α, η⟩
    apply Prod.ext
    · sorry
    · ext u
      sorry

def chapter11ChangedUniformizer
    {K : Type*} [Field K] [TopologicalSpace Kˣ]
    (D : Chapter11LocalFieldData K) (a : D.unitGroup) : Kˣ :=
  (a : Kˣ) * D.uniformizer

def chapter11PairAfterUniformizerChange
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A] [IsTopologicalGroup A]
    (D : Chapter11LocalFieldData K) (α : A)
    (η : D.unitGroup →ₜ* A) (a : D.unitGroup) : A × (D.unitGroup →ₜ* A) :=
  (α * η a, η)

theorem chapter11_uniformizer_change_value
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A] [IsTopologicalGroup A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A) (a : D.unitGroup) :
    χ (chapter11ChangedUniformizer D a) = χ D.uniformizer * χ (a : Kˣ) := by
  sorry

theorem chapter11_character_pair_finite_image_iff
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A] [IsTopologicalGroup A]
    (D : Chapter11LocalFieldData K) (α : A)
    (η : D.unitGroup →ₜ* A) :
    chapter11FiniteImage (chapter11CharacterOfPair D α η) ↔
      IsOfFinOrder α ∧ chapter11FiniteImage η := by
  sorry

def chapter11ComplexCounterexample
    {K : Type*} [Field K] [TopologicalSpace Kˣ]
    (D : Chapter11LocalFieldData K) : Kˣ →ₜ* ℂˣ :=
  chapter11CharacterOfPair D
    (Units.mk0 (2 : ℂ) (by norm_num))
    (1 : D.unitGroup →ₜ* ℂˣ)

theorem chapter11_complex_counterexample_not_galois
    {K : Type*} [Field K] [TopologicalSpace Kˣ]
    (D : Chapter11LocalFieldData K) :
    ¬ chapter11ProfiniteExtensionOf (chapter11ComplexCounterexample D) ∧
      ¬ IsCompact (closure (Set.range (chapter11ComplexCounterexample D))) := by
  sorry

end
end LastLib.Book05LocalClassFieldTheory.Chapter11
