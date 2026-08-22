import LastLib.Book05LocalClassFieldTheory.Chapter11.Dependencies
import LastLib.Book05LocalClassFieldTheory.Chapter11.Section01ExactTopologicalStatement

namespace LastLib.Book05LocalClassFieldTheory.Chapter11

noncomputable section

open scoped Topology

/-! ## 11.3. Unramified characters -/

def chapter11IsUnramified
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A) : Prop :=
  ∀ u : D.unitGroup, χ (u : Kˣ) = 1

def chapter11IsRamified
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A) : Prop :=
  ¬ chapter11IsUnramified D χ

def chapter11IsTamelyRamified
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A) : Prop :=
  (∀ x ∈ D.unitFiltration 1, χ x = 1) ∧
    chapter11IsRamified D χ

def chapter11IsWildlyRamified
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A) : Prop :=
  ¬ ∀ x ∈ D.unitFiltration 1, χ x = 1

def chapter11UnramifiedCharacterOfValue
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A] [IsTopologicalGroup A]
    (D : Chapter11LocalFieldData K) (α : A) : Kˣ →ₜ* A :=
  chapter11CharacterOfPair D α (1 : D.unitGroup →ₜ* A)

theorem chapter11_unramified_character_iff_pair
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A] [IsTopologicalGroup A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A) :
    chapter11IsUnramified D χ ↔
      χ = chapter11UnramifiedCharacterOfValue D (χ D.uniformizer) := by
  constructor
  · intro hχ
    have hunit :
        χ.comp (chapter11UnitInclusion D) = (1 : D.unitGroup →ₜ* A) := by
      ext u
      exact hχ u
    have hpair := (chapter11CharacterPairEquiv D).left_inv χ
    change χ = chapter11CharacterOfPair D (χ D.uniformizer)
      (1 : D.unitGroup →ₜ* A)
    calc
      χ = chapter11CharacterOfPair D (χ D.uniformizer)
          (χ.comp (chapter11UnitInclusion D)) := hpair.symm
      _ = chapter11CharacterOfPair D (χ D.uniformizer)
          (1 : D.unitGroup →ₜ* A) := by rw [hunit]
  · intro hχ u
    rw [hχ]
    change chapter11CharacterOfPair D (χ D.uniformizer)
      (1 : D.unitGroup →ₜ* A) (u : Kˣ) = 1
    have h :=
      chapter11_character_of_pair_apply_decomposition D (χ D.uniformizer)
        (1 : D.unitGroup →ₜ* A) 0 u
    simpa using h

theorem chapter11_unramified_character_determined_by_uniformizer
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A] [IsTopologicalGroup A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A)
    (hχ : chapter11IsUnramified D χ) :
    ∀ x : Kˣ, χ x = (χ D.uniformizer) ^ Multiplicative.toAdd (D.valuation x) := by
  sorry

def chapter11CorrespondingAbelianGaloisCharacter
    {K G A : Type*} [Field K] [Group G] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace A]
    [IsTopologicalGroup G] [IsTopologicalGroup A] [T2Space A]
    [CompactSpace A] [TotallyDisconnectedSpace A]
    (R : Chapter11ReciprocityData K G) (χ : Kˣ →ₜ* A) :
    TopologicalAbelianization G →ₜ* A :=
  (chapter11AbelianContinuousCharacterEquiv R).symm χ

theorem chapter11_unramified_character_trivial_on_inertia
    {K G A : Type*} [Field K] [Group G] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace A]
    [IsTopologicalGroup G] [IsTopologicalGroup A] [T2Space A]
    [CompactSpace A] [TotallyDisconnectedSpace A]
    (D : Chapter11LocalFieldData K) (R : Chapter11ReciprocityData K G)
    (F : Chapter11FrobeniusData K G D R) (χ : Kˣ →ₜ* A)
    (hχ : chapter11IsUnramified D χ) :
    ∀ g : F.inertia,
      chapter11CorrespondingAbelianGaloisCharacter R χ
        ((chapter11AbelianizationMap G) (g : G)) = 1 := by
  sorry

theorem chapter11_unramified_character_sends_arithmetic_frobenius_to_parameter
    {K G A : Type*} [Field K] [Group G] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace A]
    [IsTopologicalGroup G] [IsTopologicalGroup A] [T2Space A]
    [CompactSpace A] [TotallyDisconnectedSpace A]
    (D : Chapter11LocalFieldData K) (R : Chapter11ReciprocityData K G)
    (F : Chapter11FrobeniusData K G D R) (χ : Kˣ →ₜ* A)
    (hχ : chapter11IsUnramified D χ) :
    chapter11CorrespondingAbelianGaloisCharacter R χ F.arithmeticFrobenius =
      χ D.uniformizer := by
  sorry

def chapter11GeometricFrobenius
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (F : TopologicalAbelianization G) :
    TopologicalAbelianization G := F⁻¹

theorem chapter11_geometric_frobenius_normalization
    {K G A : Type*} [Field K] [Group G] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace A]
    [IsTopologicalGroup G] [IsTopologicalGroup A] [T2Space A]
    [CompactSpace A] [TotallyDisconnectedSpace A]
    (D : Chapter11LocalFieldData K) (R : Chapter11ReciprocityData K G)
    (F : Chapter11FrobeniusData K G D R) (χ : Kˣ →ₜ* A)
    (hχ : chapter11IsUnramified D χ) :
    chapter11CorrespondingAbelianGaloisCharacter R χ
        (chapter11GeometricFrobenius F.arithmeticFrobenius) =
      (χ D.uniformizer)⁻¹ := by
  sorry

/- The closure, rather than the raw subgroup of integer powers, is the compact
  procyclic object used for profinite extension. -/
def chapter11CompactProcyclicClosure
    {A : Type*} [CommGroup A] [TopologicalSpace A] (α : A) : Set A :=
  closure (Subgroup.zpowers α : Set A)

theorem chapter11_profinite_parameter_has_compact_procyclic_closure
    {A : Type*} [CommGroup A] [TopologicalSpace A]
    [CompactSpace A]
    (α : A) :
    IsCompact (chapter11CompactProcyclicClosure α) := by
  sorry

/- The closure is not merely a compact set: in a topological group it is the
   canonical closed subgroup generated by the parameter. -/
def chapter11CompactProcyclicSubgroup
    {A : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] (α : A) : Subgroup A :=
  Subgroup.topologicalClosure (Subgroup.zpowers α)

theorem chapter11_compact_procyclic_subgroup_coe
    {A : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] (α : A) :
    (chapter11CompactProcyclicSubgroup α : Set A) =
      chapter11CompactProcyclicClosure α := by
  rfl

theorem chapter11_unramified_parameter_extends_to_profinite_integer_power
    {A : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [T2Space A] [CompactSpace A]
    [TotallyDisconnectedSpace A]
    (α : A) :
    ∃ F : Chapter11ProfiniteCompletion (Multiplicative ℤ) →ₜ* A,
      ∀ n : ℤ,
        F (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionEtaFn
          (Multiplicative ℤ) (Multiplicative.ofAdd n)) = α ^ n := by
  sorry

end
end LastLib.Book05LocalClassFieldTheory.Chapter11
