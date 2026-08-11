import LastLib.Book03RamificationTheory.Chapter11.Section03AdditivityAndExactSequences

namespace LastLib.Book03RamificationTheory.Chapter11

noncomputable section

open scoped BigOperators

/-! ## 11.4. Fixed-space calculations -/

def Chapter11TwoDimensional
    {k G V : Type*} [Field k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) : Prop :=
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
  ∃ (L₁ L₂ : Submodule k V) (χ : G →* kˣ),
    Module.finrank k V = 2 ∧
      Module.finrank k L₁ = 1 ∧ Module.finrank k L₂ = 1 ∧
      L₁ ⊔ L₂ = ⊤ ∧ L₁ ⊓ L₂ = ⊥ ∧
      (∀ σ : D.inertia, ∀ x : V, x ∈ L₁ →
        ρ σ x = (χ (σ : G) : k) • x) ∧
      (∀ σ : D.inertia, ∀ x : V, x ∈ L₂ → ρ σ x = x) ∧
      (∀ σ : D.lower 1, ρ σ = LinearMap.id) ∧
      ∃ σ : D.inertia, χ (σ : G) ≠ 1

def Chapter11TameNoFixedVectors
    {k G V : Type*} [Field k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V) : Prop :=
  Module.finrank k V = 2 ∧
    (∀ σ : D.lower 1, ρ σ = LinearMap.id) ∧
    Representation.invariants (ρ.comp D.inertia.subtype) = ⊥

theorem chapter11_two_dimensional_inertia_trivial_conductor_zero
    {k G V : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V)
    (hρ : Chapter11TwoDimensional ρ)
    (htrivial : Chapter11InertiaActsTrivially D ρ) :
    chapter11ArtinConductor D ρ = 0 := by
  sorry

theorem chapter11_two_dimensional_tame_one_nontrivial_line_conductor_one
    {k G V : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V)
    (hρ : Chapter11TameOneNontrivialLine D ρ) :
    chapter11ArtinConductor D ρ = 1 := by
  sorry

theorem chapter11_two_dimensional_tame_fixed_space_zero_conductor_two
    {k G V : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V)
    (hρ : Chapter11TameNoFixedVectors D ρ) :
    chapter11ArtinConductor D ρ = 2 := by
  sorry

/- SOURCE_ISSUE: Section 11.4 says “let `χ` be a nontrivial one-dimensional
  character” and then uses `V` without introducing the representation carried
  by `χ`.  The declarations below use the canonical correction
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
  residue_characteristic_divides_e : p ∣ D.e

def Chapter11NontrivialMultiplicativeCharacter
    {k G : Type*} [Field k] [Group G] (χ : G →* kˣ) : Prop :=
  ∃ g : G, χ g ≠ 1

def Chapter11FixedSpaceIsZero
    {k G V : Type*} [Field k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (H : Subgroup G) : Prop :=
  Representation.invariants (ρ.comp H.subtype) = ⊥

theorem chapter11_wild_cyclic_nontrivial_character_fixed_spaces
    {k G : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    {D : Chapter11RamificationData G}
    (W : Chapter11WildCyclicBreakData G D) (χ : G →* kˣ)
    (hχ : Chapter11NontrivialMultiplicativeCharacter χ) :
    ∀ i, i ≤ W.m →
      Chapter11FixedSpaceIsZero
        (chapter11OneDimensionalRepresentation χ) (D.lower i) := by
  sorry

theorem chapter11_wild_cyclic_character_conductor_and_swan
    {k G : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    {D : Chapter11RamificationData G}
    (W : Chapter11WildCyclicBreakData G D) (χ : G →* kˣ)
    (hχ : Chapter11NontrivialMultiplicativeCharacter χ) :
    chapter11ArtinConductor D (chapter11OneDimensionalRepresentation χ) =
        (W.m + 1 : ℚ) ∧
      chapter11SwanConductor D (chapter11OneDimensionalRepresentation χ) =
        (W.m : ℚ) := by
  sorry

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
    Representation ℂ G (⨁ j : Fin (W.p - 1), ℂ) :=
  Representation.directSum (fun j => chapter11OneDimensionalRepresentation (C.characters j))

theorem chapter11_wild_cyclic_sum_of_nontrivial_characters
    {G : Type*} [Fintype G] [Group G]
    {D : Chapter11RamificationData G}
    (W : Chapter11WildCyclicBreakData G D)
    (C : Chapter11AllNontrivialCharacters G D W) :
    chapter11ArtinConductor D (chapter11DirectSumOfAllNontrivialCharacters W C) =
      ((W.p - 1 : ℕ) : ℚ) * (W.m + 1 : ℚ) := by
  sorry

end
end LastLib.Book03RamificationTheory.Chapter11
