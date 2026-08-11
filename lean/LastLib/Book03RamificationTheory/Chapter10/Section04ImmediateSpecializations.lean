import LastLib.Book03RamificationTheory.Chapter10.Section03IndependenceOfTheCuttingField

namespace LastLib.Book03RamificationTheory.Chapter10

noncomputable section

/-! ## 10.4. Immediate specializations -/

universe u v w

variable {E : Type u} {G : Type v} {V : Type w}
variable [Field E] [CharZero E] [Group G] [Fintype G]
  [AddCommGroup V] [Module E V] [FiniteDimensional E V]

/-- `G₀` acts trivially on an unramified representation. -/
def IsUnramifiedRepresentation
    (F : RamificationFiltration G) (ρ : Representation E G V) : Prop :=
  ∀ g : F.lower.group 0, ρ g = LinearMap.id

/-- `G₁` acts trivially on a tamely ramified representation. -/
def IsTamelyRamifiedRepresentation
    (F : RamificationFiltration G) (ρ : Representation E G V) : Prop :=
  ∀ g : F.lower.group 1, ρ g = LinearMap.id

/-- The trivial representation predicate, stated on the action maps. -/
def IsTrivialRepresentation (ρ : Representation E G V) : Prop :=
  ∀ g : G, ρ g = LinearMap.id

def IsOneDimensionalRepresentation (ρ : Representation E G V) : Prop :=
  Module.finrank E V = 1

/-- A nontrivial one-dimensional tame character. -/
def IsNontrivialTameCharacter
    (F : RamificationFiltration G) (ρ : Representation E G V) : Prop :=
  IsOneDimensionalRepresentation ρ ∧
    IsTamelyRamifiedRepresentation F ρ ∧
    ¬ IsUnramifiedRepresentation F ρ

/--
The one-break condition used by the last specialization.  The values at the
single endpoint `r` are intentionally left unconstrained, matching the
endpoint-insensitivity of the upper integral.
-/
def HasUniqueUpperBreak
    (F : RamificationFiltration G) (ρ : Representation E G V) (r : ℝ) : Prop :=
  0 < r ∧
    (∀ {v : ℝ}, 0 ≤ v → v < r →
      fixedSpaceCodimReal ρ (F.upper.group v) = 1) ∧
    (∀ {v : ℝ}, r < v →
      fixedSpaceCodimReal ρ (F.upper.group v) = 0)

theorem isUnramified_iff_inertia_trivial
    (F : RamificationFiltration G) (ρ : Representation E G V) :
    IsUnramifiedRepresentation F ρ ↔
      ∀ g : inertiaGroup F, ρ g = LinearMap.id := by
  rfl

theorem isTame_iff_wild_group_trivial
    (F : RamificationFiltration G) (ρ : Representation E G V) :
    IsTamelyRamifiedRepresentation F ρ ↔
      ∀ g : wildRamificationGroup F, ρ g = LinearMap.id := by
  rfl

theorem artinConductor_eq_zero_of_unramified
    (F : RamificationFiltration G) (hseparable : F.residue_separable)
    (ρ : Representation E G V)
    (hρ : IsUnramifiedRepresentation F ρ) :
    artinConductor F hseparable ρ = 0 := by
  sorry

theorem swanConductor_eq_zero_of_tame
    (F : RamificationFiltration G) (hseparable : F.residue_separable)
    (ρ : Representation E G V)
    (hρ : IsTamelyRamifiedRepresentation F ρ) :
    swanConductor F hseparable ρ = 0 := by
  sorry

theorem artinConductor_eq_tame_of_tame
    (F : RamificationFiltration G) (hseparable : F.residue_separable)
    (ρ : Representation E G V)
    (hρ : IsTamelyRamifiedRepresentation F ρ) :
    artinConductor F hseparable ρ = tameConductor F hseparable ρ := by
  sorry

theorem trivialRepresentation_conductor_zero
    (F : RamificationFiltration G) (hseparable : F.residue_separable)
    (ρ : Representation E G V)
    (hρ : IsTrivialRepresentation ρ) :
    artinConductor F hseparable ρ = 0 := by
  sorry

theorem nontrivial_one_dimensional_tame_character_conductor_one
    (F : RamificationFiltration G) (hseparable : F.residue_separable)
    (ρ : Representation E G V)
    (hρ : IsNontrivialTameCharacter F ρ) :
    artinConductor F hseparable ρ = 1 := by
  sorry

theorem unique_upper_break_swan_eq_break
    (F : RamificationFiltration G) (hseparable : F.residue_separable)
    (ρ : Representation E G V) {r : ℝ}
    (hρ : IsOneDimensionalRepresentation ρ)
    (hbreak : HasUniqueUpperBreak F ρ r) :
    ((swanConductor F hseparable ρ : ℚ) : ℝ) = r := by
  sorry

theorem unique_upper_break_artin_eq_break_add_one
    (F : RamificationFiltration G) (hseparable : F.residue_separable)
    (ρ : Representation E G V) {r : ℝ}
    (hρ : IsOneDimensionalRepresentation ρ)
    (hbreak : HasUniqueUpperBreak F ρ r) :
    ((artinConductor F hseparable ρ : ℚ) : ℝ) = r + 1 := by
  sorry

theorem unique_upper_break_conductors
    (F : RamificationFiltration G) (hseparable : F.residue_separable)
    (ρ : Representation E G V) {r : ℝ}
    (hρ : IsOneDimensionalRepresentation ρ)
    (hbreak : HasUniqueUpperBreak F ρ r) :
    ((swanConductor F hseparable ρ : ℚ) : ℝ) = r ∧
      ((artinConductor F hseparable ρ : ℚ) : ℝ) = r + 1 := by
  sorry

end
end LastLib.Book03RamificationTheory.Chapter10
