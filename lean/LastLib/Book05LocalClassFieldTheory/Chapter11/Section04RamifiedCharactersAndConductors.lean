import LastLib.Book05LocalClassFieldTheory.Chapter11.Dependencies
import LastLib.Book05LocalClassFieldTheory.Chapter11.Section03UnramifiedCharacters

namespace LastLib.Book05LocalClassFieldTheory.Chapter11

noncomputable section

open scoped Topology

/-! ## 11.4. Ramified characters and conductor -/

def chapter11ConductorExists
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A) : Prop :=
  ∃ n : ℕ, ∀ x ∈ D.unitFiltration n, χ x = 1

def chapter11Conductor
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A)
    (hχ : chapter11ConductorExists D χ) : ℕ :=
  by
    classical
    exact Nat.find hχ

theorem chapter11_conductor_spec
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A)
    (hχ : chapter11ConductorExists D χ) :
    ∀ x ∈ D.unitFiltration (chapter11Conductor D χ hχ), χ x = 1 := by
  classical
  exact Nat.find_spec hχ

theorem chapter11_conductor_minimal
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A)
    (hχ : chapter11ConductorExists D χ) :
    ∀ n, (∀ x ∈ D.unitFiltration n, χ x = 1) →
      chapter11Conductor D χ hχ ≤ n := by
  sorry

structure Chapter11GaloisRamificationFiltration
    (G : Type*) [Group G] where
  group : ℕ → Subgroup G
  group_succ_le : ∀ n, group (n + 1) ≤ group n

def chapter11GaloisConductor
    {G A : Type*} [Group G] [CommGroup A]
    [TopologicalSpace G] [TopologicalSpace A]
    (F : Chapter11GaloisRamificationFiltration G)
    (ρ : G →ₜ* A)
    (hρ : ∃ n : ℕ, ∀ g ∈ F.group n, ρ g = 1) : ℕ :=
  by
    classical
    exact Nat.find hρ

theorem chapter11_galois_conductor_spec
    {G A : Type*} [Group G] [CommGroup A]
    [TopologicalSpace G] [TopologicalSpace A]
    (F : Chapter11GaloisRamificationFiltration G)
    (ρ : G →ₜ* A)
    (hρ : ∃ n : ℕ, ∀ g ∈ F.group n, ρ g = 1) :
    ∀ g ∈ F.group (chapter11GaloisConductor F ρ hρ), ρ g = 1 := by
  classical
  exact Nat.find_spec hρ

theorem chapter11_conductor_matches_reciprocity_filtration
    {K G A : Type*} [Field K] [Group G] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace A]
    [IsTopologicalGroup G] [IsTopologicalGroup A] [T2Space A]
    [CompactSpace A] [TotallyDisconnectedSpace A]
    (D : Chapter11LocalFieldData K) (R : Chapter11ReciprocityData K G)
    (F : Chapter11GaloisRamificationFiltration (TopologicalAbelianization G))
    (χ : Kˣ →ₜ* A) (hχ : chapter11ConductorExists D χ)
    (hρ : ∃ n : ℕ, ∀ g ∈ F.group n,
      chapter11CorrespondingAbelianGaloisCharacter R χ g = 1)
    (hfiltration :
      ∀ n, F.group n = (D.unitFiltration n).map R.reciprocity.toMonoidHom) :
    chapter11Conductor D χ hχ =
      chapter11GaloisConductor F
        (chapter11CorrespondingAbelianGaloisCharacter R χ) hρ := by
  sorry

theorem chapter11_finite_image_has_finite_conductor
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A] [T2Space A]
    [IsTopologicalGroup A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A)
    (hχ : chapter11FiniteImage χ) :
    chapter11ConductorExists D χ := by
  sorry

theorem chapter11_unit_restriction_finite_image_has_finite_conductor
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A] [T2Space A]
    [IsTopologicalGroup A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A)
    (hχ : (Set.range (fun u : D.unitGroup => χ (u : Kˣ))).Finite) :
    chapter11ConductorExists D χ := by
  sorry

theorem chapter11_infinite_unit_image_has_no_finite_conductor
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A)
    (hinfinite :
      ∀ n, ∃ x ∈ D.unitFiltration n, χ x ≠ 1) :
    ¬ chapter11ConductorExists D χ := by
  sorry

def chapter11UnitImage
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A) (n : ℕ) : Subgroup A :=
  (D.unitFiltration n).map χ.toMonoidHom

theorem chapter11_unit_image_membership_iff
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A) (n : ℕ) (a : A) :
    a ∈ chapter11UnitImage D χ n ↔
      ∃ x ∈ D.unitFiltration n, χ x = a := by
  sorry

def chapter11ResidueDegreeOfCharacter
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A)
    (_hχ : chapter11FiniteImage χ) : ℕ :=
  orderOf (QuotientGroup.mk' (chapter11UnitImage D χ 0) (χ D.uniformizer))

theorem chapter11_residue_degree_of_character_eq_subgroup
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A)
    (hχ : chapter11FiniteImage χ) :
    chapter11ResidueDegreeOfCharacter D χ hχ =
      chapter11ResidueDegreeOfSubgroup D (chapter11CharacterKernel χ) := by
  sorry

theorem chapter11_conductor_zero_iff_unramified
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A)
    (hχ : chapter11ConductorExists D χ) :
    chapter11Conductor D χ hχ = 0 ↔ chapter11IsUnramified D χ := by
  sorry

theorem chapter11_conductor_one_of_nontrivial_tame
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A)
    (hχ : chapter11ConductorExists D χ)
    (htame : chapter11IsTamelyRamified D χ) :
    chapter11Conductor D χ hχ = 1 := by
  sorry

theorem chapter11_conductor_at_least_two_iff_wild
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A)
    (hχ : chapter11ConductorExists D χ) :
    2 ≤ chapter11Conductor D χ hχ ↔ chapter11IsWildlyRamified D χ := by
  sorry

def chapter11InertiaImageFinite
    {G A : Type*} [Group G] [CommGroup A]
    [TopologicalSpace G] [TopologicalSpace A]
    (I : Subgroup G) (ρ : G →ₜ* A) : Prop :=
  (Set.range (fun g : I => ρ (g : G))).Finite

theorem chapter11_finite_inertia_image_gives_finite_conductor
    {K G A : Type*} [Field K] [Group G] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace A]
    [IsTopologicalGroup G] [IsTopologicalGroup A] [T2Space A]
    [CompactSpace A] [TotallyDisconnectedSpace A]
    (D : Chapter11LocalFieldData K) (R : Chapter11ReciprocityData K G)
    (F : Chapter11FrobeniusData K G D R) (χ : Kˣ →ₜ* A)
    (hfinite : chapter11InertiaImageFinite
      (F.inertia.map (chapter11AbelianizationMap G).toMonoidHom)
      (chapter11CorrespondingAbelianGaloisCharacter R χ)) :
    chapter11ConductorExists D χ := by
  sorry

end
end LastLib.Book05LocalClassFieldTheory.Chapter11
