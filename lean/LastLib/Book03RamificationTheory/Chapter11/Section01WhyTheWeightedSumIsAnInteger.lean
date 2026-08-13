import LastLib.Book03RamificationTheory.Chapter11.Dependencies

namespace LastLib.Book03RamificationTheory.Chapter11

noncomputable section

open scoped BigOperators

/-! ## 11.1. Why the weighted sum is an integer -/

/-- The Artin class function attached to the lower displacement function. -/
def chapter11ArtinClassFunction
    {k G : Type*} [Field k] [Fintype G] [Group G]
    (D : Chapter11RamificationData G) : G → k := by
  classical
  exact fun σ ↦ if hσ : σ = 1 then
      (D.f : k) * ∑ τ ∈ (Finset.univ.erase (1 : G)),
        (chapter11Displacement D τ : k)
    else -(D.f : k) * (chapter11Displacement D σ : k)

/-- The normalized character pairing, with the inverse convention used by the source. -/
def chapter11CharacterPairing
    {k G V : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (A : G → k) (ρ : Representation k G V) : k :=
  (Fintype.card G : k)⁻¹ *
    ∑ σ : G, A σ * Representation.character ρ σ⁻¹

/-- The averaging operator for a subgroup, written in the same coordinates as the source. -/
def chapter11AveragingProjector
    {k G V : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (H : Subgroup G) : V →ₗ[k] V := by
  classical
  exact (Nat.card H : k)⁻¹ • ∑ h : H, ρ h

theorem chapter11_card_inertia_eq_e
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) : Nat.card D.inertia = D.e := by
  sorry

theorem chapter11_card_group_eq_ef
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) : Fintype.card G = D.e * D.f := by
  sorry

theorem chapter11_displacement_conjugation_invariant
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (g σ : G) :
    chapter11Displacement D (g * σ * g⁻¹) = chapter11Displacement D σ := by
  sorry

theorem chapter11_displacement_inverse_invariant
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (σ : G) :
    chapter11Displacement D σ⁻¹ = chapter11Displacement D σ := by
  sorry

theorem chapter11_artin_class_function_conjugation_invariant
    {k G : Type*} [Field k] [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (g σ : G) :
    chapter11ArtinClassFunction (k := k) D (g * σ * g⁻¹) =
      chapter11ArtinClassFunction (k := k) D σ := by
  sorry

theorem chapter11_artin_class_function_sum_eq_zero
    {k G : Type*} [Field k] [Fintype G] [Group G]
    (D : Chapter11RamificationData G) :
    ∑ σ : G, chapter11ArtinClassFunction (k := k) D σ = 0 := by
  sorry

theorem chapter11_artin_class_function_eq_zero_of_not_mem_inertia
    {k G : Type*} [Field k] [Fintype G] [Group G]
    (D : Chapter11RamificationData G) {σ : G}
    (hσ : σ ∉ D.inertia) :
    chapter11ArtinClassFunction (k := k) D σ = 0 := by
  sorry

theorem chapter11_averaging_projector_range
    {k G V : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (H : Subgroup G) :
    LinearMap.range (chapter11AveragingProjector ρ H) =
      Representation.invariants (ρ.comp H.subtype) := by
  sorry

theorem chapter11_averaging_projector_fixed
    {k G V : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (H : Subgroup G) (v : V)
    (hv : v ∈ Representation.invariants (ρ.comp H.subtype)) :
    chapter11AveragingProjector ρ H v = v := by
  sorry

/-- The fixed-space formula in the displayed weighted-sum normalization. -/
theorem chapter11_artin_conductor_eq_fixed_space_sum
    {k G V : Type*} [Field k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V) :
    chapter11ArtinConductor D ρ =
      ∑ i ∈ Finset.range D.bound,
        ((Nat.card (D.lower i) : ℚ) / (Nat.card D.inertia : ℚ)) *
          ((Module.finrank k V -
            Module.finrank k (Representation.invariants (ρ.comp (D.lower i).subtype))) : ℚ) := by
  sorry

/-- The Artin character pairing is the conductor.  The target field only changes the scalar cast. -/
theorem chapter11_artin_class_function_pairing_eq_artin_conductor
    {k G V : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V) :
    chapter11CharacterPairing (chapter11ArtinClassFunction D) ρ =
      (chapter11ArtinConductor D ρ : k) := by
  sorry

/-- The pairing is unchanged if the summation variable is inverted. -/
theorem chapter11_artin_class_function_pairing_inverse_form
    {k G V : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V) :
    chapter11CharacterPairing (chapter11ArtinClassFunction D) ρ =
      (Fintype.card G : k)⁻¹ *
        ∑ σ : G, chapter11ArtinClassFunction D σ⁻¹ *
          Representation.character ρ σ := by
  sorry

end
end LastLib.Book03RamificationTheory.Chapter11
