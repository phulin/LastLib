import LastLib.Book03RamificationTheory.Chapter11.Section02ArtinsIntegrality
import LastLib.Book03RamificationTheory.Chapter11.Section03AdditivityAndExactSequences

namespace LastLib.Book03RamificationTheory.Chapter11

noncomputable section

open scoped BigOperators DirectSum

/-! ## 11.4. Fixed-space calculations -/

def Chapter11TwoDimensional
    {k G V : Type*} [Field k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (_ρ : Representation k G V) : Prop :=
  Module.finrank k V = 2

def Chapter11InertiaActsTrivially
    {k G V : Type*} [Field k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V) : Prop :=
  ∀ σ : D.inertia, ρ σ = LinearMap.id

def Chapter11TameOneNontrivialLine
    {k G V : Type*} [Field k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V) : Prop :=
    ∃ (L₁ L₂ : Submodule k V) (χ : D.inertia →* kˣ),
    Module.finrank k V = 2 ∧
      Module.finrank k L₁ = 1 ∧ Module.finrank k L₂ = 1 ∧
      L₁ ⊔ L₂ = ⊤ ∧ L₁ ⊓ L₂ = ⊥ ∧
      (∀ σ : D.inertia, ∀ x : V, x ∈ L₁ →
        ρ σ x = (χ σ : k) • x) ∧
      (∀ σ : D.inertia, ∀ x : V, x ∈ L₂ → ρ σ x = x) ∧
      (∀ σ : D.lower 1, ρ σ = LinearMap.id) ∧
      ∃ σ : D.inertia, χ σ ≠ 1

def Chapter11TameNoFixedVectors
    {k G V : Type*} [Field k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V) : Prop :=
  Module.finrank k V = 2 ∧
    (∀ σ : D.lower 1, ρ σ = LinearMap.id) ∧
    Representation.invariants (ρ.comp D.inertia.subtype) = ⊥

private theorem chapter11_tame_one_nontrivial_line_fixed_space
    {k G V : Type*} [Field k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V)
    (L₁ L₂ : Submodule k V) (χ : D.inertia →* kˣ)
    (hact₁ : ∀ σ : D.inertia, ∀ x : V, x ∈ L₁ →
      ρ σ x = (χ σ : k) • x)
    (hact₂ : ∀ σ : D.inertia, ∀ x : V, x ∈ L₂ → ρ σ x = x)
    (hjoin : L₁ ⊔ L₂ = ⊤)
    (hnontriv : ∃ σ : D.inertia, χ σ ≠ 1) :
    LastLib.Book03RamificationTheory.Chapter10.fixedSpace ρ D.inertia = L₂ := by
  rcases hnontriv with ⟨σ, hσ⟩
  have hσcast : (χ σ : k) ≠ 1 := by
    intro h
    apply hσ
    apply Units.ext
    exact h
  ext x
  constructor
  · intro hx
    have hx' : x ∈ L₁ ⊔ L₂ := by
      rw [hjoin]
      exact Submodule.mem_top
    rcases Submodule.mem_sup.mp hx' with ⟨x₁, hx₁, x₂, hx₂, hxsum⟩
    have hfix :=
      (LastLib.Book03RamificationTheory.Chapter10.fixedSpace.mem_iff
        ρ D.inertia x).mp hx σ
    have hfix' : ρ (σ : G) (x₁ + x₂) = x₁ + x₂ := by
      simpa only [hxsum] using hfix
    rw [map_add, hact₁ σ x₁ hx₁, hact₂ σ x₂ hx₂] at hfix'
    have hx₁zero : x₁ = 0 := by
      have hscalar : ((χ σ : k) - 1) • x₁ = 0 := by
        rw [sub_smul, one_smul]
        exact sub_eq_zero.mpr (add_right_cancel hfix')
      exact (smul_eq_zero.mp hscalar).resolve_left (sub_ne_zero.mpr hσcast)
    rw [← hxsum, hx₁zero, zero_add]
    exact hx₂
  · intro hx
    rw [LastLib.Book03RamificationTheory.Chapter10.fixedSpace.mem_iff]
    intro σ'
    exact hact₂ σ' x hx

theorem chapter11_two_dimensional_inertia_trivial_conductor_zero
    {k G V : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V)
    (_hρ : Chapter11TwoDimensional ρ)
    (htrivial : Chapter11InertiaActsTrivially D ρ) :
    chapter11ArtinConductor D ρ = 0 := by
  have hfixed (i : ℕ) :
      LastLib.Book03RamificationTheory.Chapter10.fixedSpace ρ (D.lower i) = ⊤ := by
    apply LastLib.Book03RamificationTheory.Chapter10.fixedSpace.top_of_trivial_on
    intro g
    exact htrivial ⟨g, (chapter11_lower_le_inertia D i) g.property⟩
  have hcodim (i : ℕ) :
      LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim ρ (D.lower i) = 0 := by
    exact (LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim.eq_zero_iff
      ρ (D.lower i)).2 (hfixed i)
  unfold chapter11ArtinConductor
  simp_rw [hcodim]
  simp

theorem chapter11_two_dimensional_tame_one_nontrivial_line_conductor_one
    {k G V : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V)
    (hρ : Chapter11TameOneNontrivialLine D ρ) :
    chapter11ArtinConductor D ρ = 1 := by
  rcases hρ with ⟨L₁, L₂, χ, hdim, hL₁, hL₂, hjoin, _hmeet, hact₁, hact₂,
    htame, hnontriv⟩
  have hbound : 0 < D.bound := by
    by_contra hb
    have hbound0 : D.bound = 0 := Nat.eq_zero_of_not_pos hb
    have hinertia : D.inertia = ⊥ := by
      rw [← D.lower_zero]
      exact D.lower_eq_bot_of_bound_le 0 (by simp [hbound0])
    rcases hnontriv with ⟨σ, hσ⟩
    apply hσ
    have hσmem : (σ : G) ∈ (⊥ : Subgroup G) := by
      rw [← hinertia]
      exact σ.property
    have hσval : (σ : G) = 1 := Subgroup.mem_bot.mp hσmem
    have hσone : σ = 1 := Subtype.ext hσval
    simp [hσone]
  have hfixed := chapter11_tame_one_nontrivial_line_fixed_space
    D ρ L₁ L₂ χ hact₁ hact₂ hjoin hnontriv
  have hcodim0 :
      LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim ρ D.inertia = 1 := by
    unfold LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim
    rw [Submodule.finrank_quotient, hfixed, hL₂, hdim]
  have hlower (i : ℕ) (hi : 1 ≤ i) : D.lower i ≤ D.lower 1 := by
    induction i with
    | zero => omega
    | succ i ih =>
        cases i with
        | zero => exact le_rfl
        | succ i =>
            exact (D.lower_succ_le (Nat.succ i)).trans (ih (by omega))
  have hcodim (i : ℕ) (hi : 1 ≤ i) :
      LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim ρ (D.lower i) = 0 := by
    apply (LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim.eq_zero_iff
      ρ (D.lower i)).2
    apply LastLib.Book03RamificationTheory.Chapter10.fixedSpace.top_of_trivial_on
    intro g
    exact htame ⟨g, hlower i hi g.property⟩
  unfold chapter11ArtinConductor
  have hsum :
      (∑ i ∈ Finset.range D.bound,
        chapter11LowerWeight D i *
          (LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim ρ
            (D.lower i) : ℚ)) =
        chapter11LowerWeight D 0 *
          (LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim ρ
            (D.lower 0) : ℚ) := by
    apply Finset.sum_eq_single 0
    · intro i hi hne
      have hi' : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hne
      rw [hcodim i hi']
      simp
    · intro hnot
      exact (hnot (Finset.mem_range.mpr hbound)).elim
  rw [hsum, D.lower_zero, hcodim0]
  simp [chapter11LowerWeight, D.lower_zero]

theorem chapter11_two_dimensional_tame_one_nontrivial_line_fixed_space_dimension_one
    {k G V : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V)
    (hρ : Chapter11TameOneNontrivialLine D ρ) :
    Module.finrank k (Representation.invariants (ρ.comp D.inertia.subtype)) = 1 := by
  rcases hρ with ⟨L₁, L₂, χ, _hdim, _hL₁, hL₂, hjoin, _hmeet, hact₁, hact₂,
    _htame, hnontriv⟩
  have hfixed := chapter11_tame_one_nontrivial_line_fixed_space
    D ρ L₁ L₂ χ hact₁ hact₂ hjoin hnontriv
  change Module.finrank k
    (LastLib.Book03RamificationTheory.Chapter10.fixedSpace ρ D.inertia) = 1
  rw [hfixed, hL₂]

theorem chapter11_two_dimensional_tame_fixed_space_zero_conductor_two
    {k G V : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V)
    (hρ : Chapter11TameNoFixedVectors D ρ) :
    chapter11ArtinConductor D ρ = 2 := by
  rcases hρ with ⟨hdim, htame, hinv⟩
  change LastLib.Book03RamificationTheory.Chapter10.fixedSpace ρ D.inertia = ⊥ at hinv
  have hbound : 0 < D.bound := by
    by_contra hb
    have hbound0 : D.bound = 0 := Nat.eq_zero_of_not_pos hb
    have hinertia : D.inertia = ⊥ := by
      rw [← D.lower_zero]
      exact D.lower_eq_bot_of_bound_le 0 (by simp [hbound0])
    have hfixed_bot :
        LastLib.Book03RamificationTheory.Chapter10.fixedSpace ρ (⊥ : Subgroup G) = ⊤ := by
      apply LastLib.Book03RamificationTheory.Chapter10.fixedSpace.top_of_trivial_on
      intro g
      have hg : (g : G) = 1 := Subgroup.mem_bot.mp g.property
      rw [hg]
      simpa only [Module.End.one_eq_id] using ρ.map_one
    have htop_bot : (⊤ : Submodule k V) = ⊥ := by
      calc
        (⊤ : Submodule k V) =
            LastLib.Book03RamificationTheory.Chapter10.fixedSpace ρ (⊥ : Subgroup G) :=
          hfixed_bot.symm
        LastLib.Book03RamificationTheory.Chapter10.fixedSpace ρ (⊥ : Subgroup G) =
            LastLib.Book03RamificationTheory.Chapter10.fixedSpace ρ D.inertia := by
          rw [hinertia]
        LastLib.Book03RamificationTheory.Chapter10.fixedSpace ρ D.inertia = ⊥ := hinv
    have hfin := congrArg (fun W : Submodule k V => Module.finrank k W) htop_bot
    rw [finrank_top, finrank_bot, hdim] at hfin
    omega
  have hcodim0 :
      LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim ρ D.inertia = 2 := by
    unfold LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim
    rw [Submodule.finrank_quotient, hinv, finrank_bot, hdim]
  have hlower (i : ℕ) (hi : 1 ≤ i) : D.lower i ≤ D.lower 1 := by
    induction i with
    | zero => omega
    | succ i ih =>
        cases i with
        | zero => exact le_rfl
        | succ i =>
            exact (D.lower_succ_le (Nat.succ i)).trans (ih (by omega))
  have hcodim (i : ℕ) (hi : 1 ≤ i) :
      LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim ρ (D.lower i) = 0 := by
    apply (LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim.eq_zero_iff
      ρ (D.lower i)).2
    apply LastLib.Book03RamificationTheory.Chapter10.fixedSpace.top_of_trivial_on
    intro g
    exact htame ⟨g, hlower i hi g.property⟩
  unfold chapter11ArtinConductor
  have hsum :
      (∑ i ∈ Finset.range D.bound,
        chapter11LowerWeight D i *
          (LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim ρ
            (D.lower i) : ℚ)) =
        chapter11LowerWeight D 0 *
          (LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim ρ
            (D.lower 0) : ℚ) := by
    apply Finset.sum_eq_single 0
    · intro i hi hne
      have hi' : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hne
      rw [hcodim i hi']
      simp
    · intro hnot
      exact (hnot (Finset.mem_range.mpr hbound)).elim
  rw [hsum, D.lower_zero, hcodim0]
  simp [chapter11LowerWeight, D.lower_zero]

theorem chapter11_two_dimensional_tame_fixed_space_zero_dimension_zero
    {k G V : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V)
    (hρ : Chapter11TameNoFixedVectors D ρ) :
    Module.finrank k (Representation.invariants (ρ.comp D.inertia.subtype)) = 0 := by
  rcases hρ with ⟨_, _, hinv⟩
  rw [hinv, finrank_bot]

/- The source's `V_χ` is represented canonically by
  `chapter11OneDimensionalRepresentation χ`. -/

/-! The wild cyclic one-break laboratory. -/

structure Chapter11WildCyclicBreakData
    (G : Type*) [Fintype G] [Group G]
    (D : Chapter11RamificationData G) where
  p : ℕ
  m : ℕ
  p_prime : Nat.Prime p
  m_pos : 0 < m
  cyclic : IsCyclic G
  group_card_eq_p : Fintype.card G = p
  inertia_eq_top : D.inertia = ⊤
  lower_eq_inertia_of_le : ∀ i, i ≤ m → D.lower i = D.inertia
  lower_eq_bot_of_gt : ∀ i, m < i → D.lower i = ⊥

def Chapter11NontrivialMultiplicativeCharacter
    {k G : Type*} [Field k] [Group G] (χ : G →* kˣ) : Prop :=
  ∃ g : G, χ g ≠ 1

def Chapter11FixedSpaceIsZero
    {k G V : Type*} [Field k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (H : Subgroup G) : Prop :=
  Representation.invariants (ρ.comp H.subtype) = ⊥

private theorem chapter11_nontrivial_character_fixed_space_zero
    {k G : Type*} [Field k] [Fintype G] [Group G]
    (χ : G →* kˣ) (H : Subgroup G)
    (hχ : ∃ g : H, χ (g : G) ≠ 1) :
    LastLib.Book03RamificationTheory.Chapter10.fixedSpace
        (chapter11OneDimensionalRepresentation χ) H = ⊥ := by
  rcases hχ with ⟨g, hg⟩
  have hg' : (χ (g : G) : k) ≠ 1 := by
    intro h
    apply hg
    apply Units.ext
    exact h
  ext x
  constructor
  · intro hx
    have hfix :=
      (LastLib.Book03RamificationTheory.Chapter10.fixedSpace.mem_iff
        (chapter11OneDimensionalRepresentation χ) H x).mp hx g
    have hfix' : (χ (g : G) : k) • x = x := by
      simpa [chapter11OneDimensionalRepresentation] using hfix
    have hscalar : ((χ (g : G) : k) - 1) • x = 0 := by
      rw [sub_smul, one_smul]
      exact sub_eq_zero.mpr hfix'
    have hxzero : x = 0 := by
      exact (smul_eq_zero.mp hscalar).resolve_left (sub_ne_zero.mpr hg')
    rw [hxzero]
    exact Submodule.zero_mem _
  · intro hx
    have hxzero : x = 0 := by simpa using hx
    rw [hxzero]
    exact Submodule.zero_mem _

theorem chapter11_wild_cyclic_nontrivial_character_fixed_spaces
    {k G : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    {D : Chapter11RamificationData G}
    (W : Chapter11WildCyclicBreakData G D) (χ : G →* kˣ)
    (hχ : Chapter11NontrivialMultiplicativeCharacter χ) :
    ∀ i, i ≤ W.m →
      Chapter11FixedSpaceIsZero
        (chapter11OneDimensionalRepresentation χ) (D.lower i) := by
  intro i hi
  rw [W.lower_eq_inertia_of_le i hi]
  change LastLib.Book03RamificationTheory.Chapter10.fixedSpace
      (chapter11OneDimensionalRepresentation χ) D.inertia = ⊥
  apply chapter11_nontrivial_character_fixed_space_zero χ D.inertia
  rcases hχ with ⟨g, hg⟩
  refine ⟨⟨g, ?_⟩, hg⟩
  simp [W.inertia_eq_top]

theorem chapter11_wild_cyclic_nontrivial_character_fixed_spaces_after_break
    {k G : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    {D : Chapter11RamificationData G}
    (W : Chapter11WildCyclicBreakData G D) (χ : G →* kˣ)
    (_hχ : Chapter11NontrivialMultiplicativeCharacter χ) :
    ∀ i, W.m < i →
      Representation.invariants
        ((chapter11OneDimensionalRepresentation χ).comp (D.lower i).subtype) = ⊤ := by
  intro i hi
  rw [W.lower_eq_bot_of_gt i hi]
  change LastLib.Book03RamificationTheory.Chapter10.fixedSpace
      (chapter11OneDimensionalRepresentation χ) (⊥ : Subgroup G) = ⊤
  apply LastLib.Book03RamificationTheory.Chapter10.fixedSpace.top_of_trivial_on
  intro g
  have hg : (g : G) = 1 := Subgroup.mem_bot.mp g.property
  rw [hg]
  simpa only [Module.End.one_eq_id] using
    (chapter11OneDimensionalRepresentation χ).map_one

theorem chapter11_wild_cyclic_character_conductor_and_swan
    {k G : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    {D : Chapter11RamificationData G}
    (W : Chapter11WildCyclicBreakData G D) (χ : G →* kˣ)
    (hχ : Chapter11NontrivialMultiplicativeCharacter χ) :
    chapter11ArtinConductor D (chapter11OneDimensionalRepresentation χ) =
        (W.m + 1 : ℚ) ∧
      chapter11SwanConductor D (chapter11OneDimensionalRepresentation χ) =
        (W.m : ℚ) := by
  rcases hχ with ⟨g, hg⟩
  have hbound : W.m < D.bound := by
    by_contra h
    have hle : D.bound ≤ W.m := Nat.le_of_not_gt h
    have hbot : D.lower W.m = ⊥ := D.lower_eq_bot_of_bound_le W.m hle
    have hinertia : D.inertia = (⊥ : Subgroup G) := by
      rw [← W.lower_eq_inertia_of_le W.m (le_refl _)]
      exact hbot
    have hgmem : g ∈ D.inertia := by
      simp [W.inertia_eq_top]
    have hg1 : g = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← hinertia]
      exact hgmem
    apply hg
    rw [hg1]
    exact χ.map_one
  have hfixed_zero :
      LastLib.Book03RamificationTheory.Chapter10.fixedSpace
          (chapter11OneDimensionalRepresentation χ) D.inertia = ⊥ := by
    apply chapter11_nontrivial_character_fixed_space_zero χ D.inertia
    exact ⟨⟨g, by simp [W.inertia_eq_top]⟩, hg⟩
  have hcodim (i : ℕ) (hi : i ≤ W.m) :
      LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim
          (chapter11OneDimensionalRepresentation χ) (D.lower i) = 1 := by
    rw [W.lower_eq_inertia_of_le i hi]
    unfold LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim
    rw [Submodule.finrank_quotient, hfixed_zero, finrank_bot]
    simp [Module.finrank_self]
  have hcodim_bot (i : ℕ) (hi : W.m < i) :
      LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim
          (chapter11OneDimensionalRepresentation χ) (D.lower i) = 0 := by
    rw [W.lower_eq_bot_of_gt i hi]
    apply (LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim.eq_zero_iff
      (chapter11OneDimensionalRepresentation χ) (⊥ : Subgroup G)).2
    apply LastLib.Book03RamificationTheory.Chapter10.fixedSpace.top_of_trivial_on
    intro h
    have hh : (h : G) = 1 := Subgroup.mem_bot.mp h.property
    rw [hh]
    simpa only [Module.End.one_eq_id] using
      (chapter11OneDimensionalRepresentation χ).map_one
  have hterm (i : ℕ) (hi : i < D.bound) :
      chapter11LowerWeight D i *
          (LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim
            (chapter11OneDimensionalRepresentation χ) (D.lower i) : ℚ) =
        if i ≤ W.m then 1 else 0 := by
    by_cases hi_m : i ≤ W.m
    · rw [if_pos hi_m, hcodim i hi_m]
      simp [chapter11LowerWeight, W.lower_eq_inertia_of_le i hi_m]
    · have hi_gt : W.m < i := Nat.lt_of_not_ge hi_m
      rw [if_neg hi_m, hcodim_bot i hi_gt]
      simp
  have hfilter :
      (Finset.range D.bound).filter (fun i => i ≤ W.m) =
        Finset.range (W.m + 1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor <;> omega
  have hsum :
      (∑ i ∈ Finset.range D.bound,
        if i ≤ W.m then (1 : ℚ) else 0) = (W.m + 1 : ℚ) := by
    rw [← Finset.sum_filter, hfilter]
    simp
  have hartin :
      chapter11ArtinConductor D
          (chapter11OneDimensionalRepresentation χ) = (W.m + 1 : ℚ) := by
    unfold chapter11ArtinConductor
    calc
      (∑ i ∈ Finset.range D.bound,
          chapter11LowerWeight D i *
            (LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim
              (chapter11OneDimensionalRepresentation χ) (D.lower i) : ℚ)) =
          ∑ i ∈ Finset.range D.bound, if i ≤ W.m then (1 : ℚ) else 0 := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hterm i (Finset.mem_range.mp hi)
      _ = (W.m + 1 : ℚ) := hsum
  have hfilter_swan :
      (Finset.Ico 1 D.bound).filter (fun i => i ≤ W.m) =
        Finset.Ico 1 (W.m + 1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Ico]
    constructor <;> omega
  have hsum_swan :
      (∑ i ∈ Finset.Ico 1 D.bound,
        if i ≤ W.m then (1 : ℚ) else 0) = (W.m : ℚ) := by
    rw [← Finset.sum_filter, hfilter_swan]
    simp
  have hswan :
      chapter11SwanConductor D
          (chapter11OneDimensionalRepresentation χ) = (W.m : ℚ) := by
    unfold chapter11SwanConductor
    calc
      (∑ i ∈ Finset.Ico 1 D.bound,
          chapter11LowerWeight D i *
            (LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim
              (chapter11OneDimensionalRepresentation χ) (D.lower i) : ℚ)) =
          ∑ i ∈ Finset.Ico 1 D.bound, if i ≤ W.m then (1 : ℚ) else 0 := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hterm i (Finset.mem_Ico.mp hi).2
      _ = (W.m : ℚ) := hsum_swan
  exact ⟨hartin, hswan⟩

/-- A complete list of the nontrivial complex characters of a cyclic group of prime order. -/
structure Chapter11AllNontrivialCharacters
    (G : Type*) [Fintype G] [Group G]
    (D : Chapter11RamificationData G)
  (W : Chapter11WildCyclicBreakData G D) where
  characters : Fin (W.p - 1) → G →* ℂˣ
  pairwise_ne : Function.Injective characters
  nontrivial : ∀ j, Chapter11NontrivialMultiplicativeCharacter (characters j)
  complete :
    ∀ χ : G →* ℂˣ,
      Chapter11NontrivialMultiplicativeCharacter χ →
        ∃ j, characters j = χ

def chapter11DirectSumOfAllNontrivialCharacters
    {G : Type*} [Fintype G] [Group G]
    {D : Chapter11RamificationData G}
    (W : Chapter11WildCyclicBreakData G D)
    (C : Chapter11AllNontrivialCharacters G D W) :
    Representation ℂ G (⨁ _j : Fin (W.p - 1), ℂ) :=
  Representation.directSum (fun j => chapter11OneDimensionalRepresentation (C.characters j))

theorem chapter11_wild_cyclic_sum_of_nontrivial_characters
    {G : Type*} [Fintype G] [Group G]
    {D : Chapter11RamificationData G}
    (W : Chapter11WildCyclicBreakData G D)
    (C : Chapter11AllNontrivialCharacters G D W) :
    chapter11ArtinConductor D (chapter11DirectSumOfAllNontrivialCharacters W C) =
      ((W.p - 1 : ℕ) : ℚ) * (W.m + 1 : ℚ) := by
  have hp : 2 ≤ W.p := W.p_prime.two_le
  have hp_sub : 0 < W.p - 1 := by omega
  let j₀ : Fin (W.p - 1) := ⟨0, hp_sub⟩
  rcases C.nontrivial j₀ with ⟨g, hg⟩
  have hbound : W.m < D.bound := by
    by_contra h
    have hle : D.bound ≤ W.m := Nat.le_of_not_gt h
    have hbot : D.lower W.m = ⊥ := D.lower_eq_bot_of_bound_le W.m hle
    have hinertia : D.inertia = (⊥ : Subgroup G) := by
      rw [← W.lower_eq_inertia_of_le W.m (le_refl _)]
      exact hbot
    have hgmem : g ∈ D.inertia := by
      simp [W.inertia_eq_top]
    have hg1 : g = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← hinertia]
      exact hgmem
    apply hg
    rw [hg1]
    exact (C.characters j₀).map_one
  have hfixed_zero :
      LastLib.Book03RamificationTheory.Chapter10.fixedSpace
          (chapter11DirectSumOfAllNontrivialCharacters W C) D.inertia = ⊥ := by
    ext x
    constructor
    · intro hx
      have hxzero : x = 0 := by
        ext j
        rcases C.nontrivial j with ⟨g, hg⟩
        have hfix :=
          (LastLib.Book03RamificationTheory.Chapter10.fixedSpace.mem_iff
            (chapter11DirectSumOfAllNontrivialCharacters W C) D.inertia x).mp hx
            ⟨g, by simp [W.inertia_eq_top]⟩
        have hfixj := congrArg (fun y => y j) hfix
        have hfixj' :
            (C.characters j (g : G) : ℂ) • x j = x j := by
          simpa [chapter11DirectSumOfAllNontrivialCharacters,
            Representation.directSum, chapter11OneDimensionalRepresentation] using hfixj
        have hscalar : ((C.characters j (g : G) : ℂ) - 1) • x j = 0 := by
          rw [sub_smul, one_smul]
          exact sub_eq_zero.mpr hfixj'
        have hg' : (C.characters j (g : G) : ℂ) ≠ 1 := by
          intro h
          apply hg
          apply Units.ext
          exact h
        exact (smul_eq_zero.mp hscalar).resolve_left (sub_ne_zero.mpr hg')
      rw [hxzero]
      exact Submodule.zero_mem _
    · intro hx
      have hxzero : x = 0 := by simpa using hx
      rw [hxzero]
      exact Submodule.zero_mem _
  have hcodim (i : ℕ) (hi : i ≤ W.m) :
      LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim
          (chapter11DirectSumOfAllNontrivialCharacters W C) (D.lower i) =
        W.p - 1 := by
    rw [W.lower_eq_inertia_of_le i hi]
    unfold LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim
    rw [Submodule.finrank_quotient, hfixed_zero, finrank_bot]
    simp [Module.finrank_directSum]
  have hcodim_bot (i : ℕ) (hi : W.m < i) :
      LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim
          (chapter11DirectSumOfAllNontrivialCharacters W C) (D.lower i) = 0 := by
    rw [W.lower_eq_bot_of_gt i hi]
    apply (LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim.eq_zero_iff
      (chapter11DirectSumOfAllNontrivialCharacters W C) (⊥ : Subgroup G)).2
    apply LastLib.Book03RamificationTheory.Chapter10.fixedSpace.top_of_trivial_on
    intro h
    have hh : (h : G) = 1 := Subgroup.mem_bot.mp h.property
    rw [hh]
    simpa only [Module.End.one_eq_id] using
      (chapter11DirectSumOfAllNontrivialCharacters W C).map_one
  have hterm (i : ℕ) (hi : i < D.bound) :
      chapter11LowerWeight D i *
          (LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim
            (chapter11DirectSumOfAllNontrivialCharacters W C) (D.lower i) : ℚ) =
        if i ≤ W.m then ((W.p - 1 : ℕ) : ℚ) else 0 := by
    by_cases hi_m : i ≤ W.m
    · rw [if_pos hi_m, hcodim i hi_m]
      simp [chapter11LowerWeight, W.lower_eq_inertia_of_le i hi_m]
    · have hi_gt : W.m < i := Nat.lt_of_not_ge hi_m
      rw [if_neg hi_m, hcodim_bot i hi_gt]
      simp
  have hfilter :
      (Finset.range D.bound).filter (fun i => i ≤ W.m) =
        Finset.range (W.m + 1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor <;> omega
  have hsum :
      (∑ i ∈ Finset.range D.bound,
        if i ≤ W.m then ((W.p - 1 : ℕ) : ℚ) else 0) =
        ((W.p - 1 : ℕ) : ℚ) * (W.m + 1 : ℚ) := by
    rw [← Finset.sum_filter, hfilter]
    simp
    ring
  unfold chapter11ArtinConductor
  calc
    (∑ i ∈ Finset.range D.bound,
        chapter11LowerWeight D i *
          (LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim
            (chapter11DirectSumOfAllNontrivialCharacters W C) (D.lower i) : ℚ)) =
        ∑ i ∈ Finset.range D.bound,
          if i ≤ W.m then ((W.p - 1 : ℕ) : ℚ) else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hterm i (Finset.mem_range.mp hi)
    _ = ((W.p - 1 : ℕ) : ℚ) * (W.m + 1 : ℚ) := hsum

end
end LastLib.Book03RamificationTheory.Chapter11
