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
  LastLib.Book05LocalClassFieldTheory.Chapter08.chapter08ConductorExists
    D.base.valuation χ.toMonoidHom

def chapter11Conductor
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A)
    (hχ : chapter11ConductorExists D χ) : ℕ :=
  LastLib.Book05LocalClassFieldTheory.Chapter08.chapter08Conductor
    D.base.valuation χ.toMonoidHom hχ

theorem chapter11_conductor_spec
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A)
    (hχ : chapter11ConductorExists D χ) :
    ∀ x ∈ D.unitFiltration (chapter11Conductor D χ hχ), χ x = 1 := by
  classical
  -- Prior attempt: `exact Nat.find_spec hχ` used the canonical Chapter 8
  -- filtration directly and did not rewrite it to the Chapter 11 interface.
  intro x hx
  have hx' : x ∈
      LastLib.Book05LocalClassFieldTheory.Chapter08.chapter08UnitFiltration
        D.base.valuation (chapter11Conductor D χ hχ) := by
    rw [← D.unitFiltration_eq_canonical]
    exact hx
  exact (Nat.find_spec hχ) x hx'

theorem chapter11_conductor_minimal
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A)
    (hχ : chapter11ConductorExists D χ) :
    ∀ n, (∀ x ∈ D.unitFiltration n, χ x = 1) →
      chapter11Conductor D χ hχ ≤ n := by
  classical
  intro n hn
  exact Nat.find_min' hχ (fun x hx => hn x (by
    rw [D.unitFiltration_eq_canonical]
    exact hx))

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
  classical
  have hcompat :
      (chapter11CorrespondingAbelianGaloisCharacter R χ).comp R.reciprocity = χ := by
    have hcomp := chapter11_abelian_continuous_character_equiv_apply R
      (chapter11CorrespondingAbelianGaloisCharacter R χ)
    calc
      _ = (chapter11AbelianContinuousCharacterEquiv R)
          (chapter11CorrespondingAbelianGaloisCharacter R χ) := hcomp.symm
      _ = χ := (chapter11AbelianContinuousCharacterEquiv R).apply_symm_apply χ
  apply Nat.le_antisymm
  · apply chapter11_conductor_minimal D χ hχ
      (chapter11GaloisConductor F
        (chapter11CorrespondingAbelianGaloisCharacter R χ) hρ)
    intro x hx
    have hxg :
        R.reciprocity x ∈ F.group
          (chapter11GaloisConductor F
            (chapter11CorrespondingAbelianGaloisCharacter R χ) hρ) := by
      rw [hfiltration]
      exact ⟨x, hx, rfl⟩
    have hρx := chapter11_galois_conductor_spec F
      (chapter11CorrespondingAbelianGaloisCharacter R χ) hρ
      (R.reciprocity x) hxg
    exact (congrArg (fun f : Kˣ →ₜ* A => f x) hcompat).symm.trans hρx
  · change Nat.find hρ ≤ chapter11Conductor D χ hχ
    apply Nat.find_min' hρ
    intro g hg
    rw [hfiltration (chapter11Conductor D χ hχ)] at hg
    rcases hg with ⟨x, hx, hgx⟩
    rw [← hgx]
    exact (congrArg (fun f : Kˣ →ₜ* A => f x) hcompat).trans
      (chapter11_conductor_spec D χ hχ x hx)

private theorem chapter11_conductor_exists_of_finite_unit_image
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A] [T2Space A]
    [IsTopologicalGroup A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A)
    (hχ : (Set.range (fun u : D.unitGroup => χ (u : Kˣ))).Finite) :
    chapter11ConductorExists D χ := by
  have hclosed : IsClosed
      (Set.range (fun u : D.unitGroup => χ (u : Kˣ)) \ ({1} : Set A)) := by
    exact hχ.sdiff.isClosed
  have hone : (1 : A) ∉
      Set.range (fun u : D.unitGroup => χ (u : Kˣ)) \ ({1} : Set A) := by
    simp
  have hA :
      (Set.range (fun u : D.unitGroup => χ (u : Kˣ)) \ ({1} : Set A))ᶜ ∈ 𝓝 (1 : A) :=
    IsOpen.mem_nhds hclosed.isOpen_compl hone
  have hK :
      χ ⁻¹' (Set.range (fun u : D.unitGroup => χ (u : Kˣ)) \ ({1} : Set A))ᶜ ∈
        𝓝 (1 : Kˣ) := by
    apply χ.continuous_toFun.continuousAt.preimage_mem_nhds
    change (Set.range (fun u : D.unitGroup => χ (u : Kˣ)) \ ({1} : Set A))ᶜ ∈
      𝓝 (χ (1 : Kˣ))
    rw [map_one]
    exact hA
  obtain ⟨n, hn⟩ := D.unitFiltration_basis _ hK
  have hunit : ∀ n, D.unitFiltration n ≤ D.unitGroup := by
    intro n
    have hlevel : ∀ m, D.unitFiltration m ≤ D.unitFiltration 0 := by
      intro m
      induction m with
      | zero => exact le_rfl
      | succ m ihm =>
          exact (D.unitFiltration_succ_le m).trans ihm
    exact (hlevel n).trans_eq D.unitFiltration_zero
  change ∃ n : ℕ, ∀ x ∈
    LastLib.Book05LocalClassFieldTheory.Chapter08.chapter08UnitFiltration
      D.base.valuation n, χ.toMonoidHom x = 1
  refine ⟨n, ?_⟩
  intro x hx
  have hxD : x ∈ D.unitFiltration n := by
    rw [D.unitFiltration_eq_canonical]
    exact hx
  have hxunit : x ∈ D.unitGroup := hunit n hxD
  have hxrange : χ x ∈ Set.range (fun u : D.unitGroup => χ (u : Kˣ)) := by
    exact ⟨⟨x, hxunit⟩, rfl⟩
  have hxnhds : χ x ∈
      (Set.range (fun u : D.unitGroup => χ (u : Kˣ)) \ ({1} : Set A))ᶜ := hn hxD
  by_contra hne
  exact hxnhds ⟨hxrange, hne⟩

theorem chapter11_finite_image_has_finite_conductor
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A] [T2Space A]
    [IsTopologicalGroup A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A)
    (hχ : chapter11FiniteImage χ) :
    chapter11ConductorExists D χ := by
  change (Set.range χ).Finite at hχ
  apply chapter11_conductor_exists_of_finite_unit_image D χ
  apply hχ.subset
  rintro y ⟨u, rfl⟩
  exact ⟨(u : Kˣ), rfl⟩

theorem chapter11_unit_restriction_finite_image_has_finite_conductor
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A] [T2Space A]
    [IsTopologicalGroup A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A)
    (hχ : (Set.range (fun u : D.unitGroup => χ (u : Kˣ))).Finite) :
    chapter11ConductorExists D χ := by
  exact chapter11_conductor_exists_of_finite_unit_image D χ hχ

theorem chapter11_infinite_unit_image_has_no_finite_conductor
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A)
    (hinfinite :
      ∀ n, ∃ x ∈ D.unitFiltration n, χ x ≠ 1) :
    ¬ chapter11ConductorExists D χ := by
  intro hχ
  obtain ⟨x, hx, hne⟩ := hinfinite (chapter11Conductor D χ hχ)
  exact hne (chapter11_conductor_spec D χ hχ x hx)

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
  rfl

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
      chapter11ResidueDegreeOfSubgroup D (chapter11CharacterKernel χ)
        (chapter11_finite_image_character_kernel_finite_index χ hχ) := by
  apply (orderOf_eq_orderOf_iff).2
  intro m
  constructor
  · intro hpow
    have hmem : (χ D.uniformizer) ^ m ∈ chapter11UnitImage D χ 0 := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (chapter11UnitImage D χ 0)
          ((χ D.uniformizer) ^ m) = 1
      rw [map_pow]
      exact hpow
    rcases (chapter11_unit_image_membership_iff D χ 0 _).mp hmem with
      ⟨x, hx, hxχ⟩
    have hxunit : x ∈ D.unitGroup := by
      rw [D.unitFiltration_zero] at hx
      exact hx
    have heq :
        QuotientGroup.mk' (chapter11CharacterKernel χ) (x : Kˣ) =
          QuotientGroup.mk' (chapter11CharacterKernel χ) (D.uniformizer ^ m) := by
      change ((x : Kˣ) : Kˣ ⧸ chapter11CharacterKernel χ) =
        ((D.uniformizer ^ m : Kˣ) : Kˣ ⧸ chapter11CharacterKernel χ)
      rw [QuotientGroup.eq_iff_div_mem]
      change χ ((x : Kˣ) / D.uniformizer ^ m) = 1
      rw [map_div, hxχ, map_pow]
      simp
    have hmem' :
        QuotientGroup.mk' (chapter11CharacterKernel χ) (D.uniformizer ^ m) ∈
          D.unitGroup.map (QuotientGroup.mk' (chapter11CharacterKernel χ)) := by
      exact ⟨x, hxunit, heq⟩
    exact (QuotientGroup.eq_one_iff _).mpr hmem'
  · intro hpow
    have hmem :
        QuotientGroup.mk' (chapter11CharacterKernel χ) (D.uniformizer ^ m) ∈
          D.unitGroup.map (QuotientGroup.mk' (chapter11CharacterKernel χ)) := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk'
          (D.unitGroup.map (QuotientGroup.mk' (chapter11CharacterKernel χ)))
          ((QuotientGroup.mk' (chapter11CharacterKernel χ) D.uniformizer) ^ m) = 1
      rw [map_pow]
      exact hpow
    rcases hmem with ⟨x, hxunit, heq⟩
    have heq' := heq
    change ((x : Kˣ) : Kˣ ⧸ chapter11CharacterKernel χ) =
      ((D.uniformizer ^ m : Kˣ) : Kˣ ⧸ chapter11CharacterKernel χ) at heq'
    have hker :
        (x : Kˣ) / D.uniformizer ^ m ∈ chapter11CharacterKernel χ := by
      exact (QuotientGroup.eq_iff_div_mem.mp heq')
    have hxχ : χ (x : Kˣ) = χ (D.uniformizer ^ m) := by
      change χ ((x : Kˣ) / D.uniformizer ^ m) = 1 at hker
      apply div_eq_one.mp
      rw [map_div] at hker
      exact hker
    have hmem' : χ (D.uniformizer ^ m) ∈ chapter11UnitImage D χ 0 := by
      apply (chapter11_unit_image_membership_iff D χ 0 _).mpr
      exact ⟨x, by rw [D.unitFiltration_zero]; exact hxunit, hxχ⟩
    have hmem'' : (χ D.uniformizer) ^ m ∈ chapter11UnitImage D χ 0 := by
      simpa only [map_pow] using hmem'
    exact (QuotientGroup.eq_one_iff _).mpr hmem''

theorem chapter11_conductor_zero_iff_unramified
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A)
    (hχ : chapter11ConductorExists D χ) :
    chapter11Conductor D χ hχ = 0 ↔ chapter11IsUnramified D χ := by
  constructor
  · intro hzero u
    have hspec := chapter11_conductor_spec D χ hχ
    rw [hzero, D.unitFiltration_zero] at hspec
    exact hspec u u.property
  · intro hunram
    exact Nat.le_zero.mp (chapter11_conductor_minimal D χ hχ 0 (by
      intro x hx
      have hx0 : x ∈ D.unitFiltration 0 := hx
      rw [D.unitFiltration_zero] at hx0
      exact hunram ⟨x, hx0⟩))

theorem chapter11_conductor_one_of_nontrivial_tame
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A)
    (hχ : chapter11ConductorExists D χ)
    (htame : chapter11IsTamelyRamified D χ) :
    chapter11Conductor D χ hχ = 1 := by
  apply Nat.le_antisymm
  · apply chapter11_conductor_minimal D χ hχ 1
    exact htame.1
  · apply Nat.one_le_iff_ne_zero.mpr
    intro hzero
    exact htame.2 ((chapter11_conductor_zero_iff_unramified D χ hχ).mp hzero)

theorem chapter11_conductor_at_least_two_iff_wild
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A)
    (hχ : chapter11ConductorExists D χ) :
    2 ≤ chapter11Conductor D χ hχ ↔ chapter11IsWildlyRamified D χ := by
  constructor
  · intro hlarge hlevel
    have hsmall := chapter11_conductor_minimal D χ hχ 1 hlevel
    exact (Nat.not_succ_le_self 1) (hlarge.trans hsmall)
  · intro hwild
    by_contra hnot
    have hle : chapter11Conductor D χ hχ ≤ 1 := by
      apply Nat.le_of_lt_succ
      simpa using Nat.lt_of_not_ge hnot
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with hzero | hone
    · apply hwild
      intro x hx
      have hunram :=
        (chapter11_conductor_zero_iff_unramified D χ hχ).mp hzero
      have hx0 : x ∈ D.unitFiltration 0 := by
        have hx' := D.unitFiltration_succ_le 0 hx
        simpa using hx'
      rw [D.unitFiltration_zero] at hx0
      exact hunram ⟨x, hx0⟩
    · apply hwild
      intro x hx
      have hspec := chapter11_conductor_spec D χ hχ
      rw [hone] at hspec
      exact hspec x hx

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
  unfold chapter11InertiaImageFinite at hfinite
  have hcompat :
      (chapter11CorrespondingAbelianGaloisCharacter R χ).comp R.reciprocity = χ := by
    have hcomp := chapter11_abelian_continuous_character_equiv_apply R
      (chapter11CorrespondingAbelianGaloisCharacter R χ)
    calc
      _ = (chapter11AbelianContinuousCharacterEquiv R)
          (chapter11CorrespondingAbelianGaloisCharacter R χ) := hcomp.symm
      _ = χ := (chapter11AbelianContinuousCharacterEquiv R).apply_symm_apply χ
  apply chapter11_conductor_exists_of_finite_unit_image D χ
  apply hfinite.subset
  rintro y ⟨u, rfl⟩
  have huI :
      R.reciprocity (u : Kˣ) ∈
        F.inertia.map (chapter11AbelianizationMap G).toMonoidHom := by
    rw [F.inertia_ab_eq_reciprocity_unit_image]
    exact ⟨u, u.property, rfl⟩
  refine ⟨⟨R.reciprocity (u : Kˣ), huI⟩, ?_⟩
  exact congrArg (fun f : Kˣ →ₜ* A => f (u : Kˣ)) hcompat

end
end LastLib.Book05LocalClassFieldTheory.Chapter11
