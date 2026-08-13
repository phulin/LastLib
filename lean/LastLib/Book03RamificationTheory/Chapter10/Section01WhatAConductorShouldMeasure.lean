import LastLib.Book03RamificationTheory.Chapter10.Dependencies

namespace LastLib.Book03RamificationTheory.Chapter10

noncomputable section

/-! ## 10.1. What a conductor should measure -/

/- The source first chooses a finite local Galois quotient through which the
finite-image action factors.  `FiniteQuotientRealization` records that choice
explicitly, together with its filtration and factorization map. -/

universe u v w

variable {E : Type u} {G : Type v} {V : Type w}
variable [Field E] [Group G] [AddCommGroup V] [Module E V]
  [FiniteDimensional E V]

/-!
The semisimple statements below are deliberately isolated from the conductor
definitions.  They use the exact Maschke condition and therefore do not make
the coefficient-characteristic assertion stronger than the source.
-/

/-- The coefficient condition under which finite-group averaging is available. -/
def MaschkeCoefficientCondition [Fintype G] : Prop :=
  IsUnit (Fintype.card G : E)

/-- The modular coefficient regime excluded by the elementary semisimple API. -/
def ModularCoefficientRegime [Fintype G] : Prop :=
  ¬ MaschkeCoefficientCondition (E := E) (G := G)

theorem charZero_maschkeCoefficientCondition [Fintype G] [CharZero E] :
    MaschkeCoefficientCondition (E := E) (G := G) := by
  simp [MaschkeCoefficientCondition, isUnit_iff_ne_zero]

theorem charZero_not_modularCoefficientRegime [Fintype G] [CharZero E] :
    ¬ ModularCoefficientRegime (E := E) (G := G) := by
  exact fun h => h (charZero_maschkeCoefficientCondition (E := E) (G := G))

omit [FiniteDimensional E V] in
/-- Maschke semisimplicity for a finite group over a characteristic-zero field. -/
theorem finite_group_representation_is_semisimple
    [Fintype G] [CharZero E] (ρ : Representation E G V) :
    Representation.IsSemisimpleRepresentation ρ := by
  have : NeZero (Nat.card G : E) := ⟨by
    simpa only [Fintype.card_eq_nat_card] using
      (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero : Fintype.card G ≠ 0))⟩
  infer_instance

/-- The averaging operator used to split the invariant subspace. -/
def invariantAverage [Fintype G] [Invertible (Fintype.card G : E)]
    (ρ : Representation E G V) : V →ₗ[E] V :=
  Representation.averageMap ρ

omit [FiniteDimensional E V] in
theorem invariantAverage_mem [Fintype G] [Invertible (Fintype.card G : E)]
    (ρ : Representation E G V) (v : V) :
    invariantAverage ρ v ∈ fixedSpace ρ (⊤ : Subgroup G) := by
  rw [fixedSpace.mem_iff]
  intro g
  simpa [invariantAverage] using Representation.averageMap_invariant ρ v g

omit [FiniteDimensional E V] in
theorem invariantAverage_eq_self_of_mem [Fintype G] [Invertible (Fintype.card G : E)]
    (ρ : Representation E G V) {v : V}
    (hv : v ∈ fixedSpace ρ (⊤ : Subgroup G)) :
    invariantAverage ρ v = v := by
  change Representation.averageMap ρ v = v
  apply Representation.averageMap_id
  rw [Representation.mem_invariants]
  intro g
  exact (fixedSpace.mem_iff ρ (⊤ : Subgroup G) v).mp hv ⟨g, by simp⟩

omit [FiniteDimensional E V] in
/-- Averaging is a projection onto the fixed space; this is the exact
split-invariants interface needed for the characteristic-zero discussion. -/
theorem invariantAverage_splits_fixedSpace
    [Fintype G] [Invertible (Fintype.card G : E)] (ρ : Representation E G V) :
    (∀ v, invariantAverage ρ v ∈ fixedSpace ρ (⊤ : Subgroup G)) ∧
      (∀ v, v ∈ fixedSpace ρ (⊤ : Subgroup G) → invariantAverage ρ v = v) := by
  constructor
  · intro v
    exact invariantAverage_mem ρ v
  · intro v hv
    exact invariantAverage_eq_self_of_mem ρ hv

/-- A finite-image representation together with a chosen cutting quotient. -/
def HasFiniteCuttingQuotient
    (ρ : FiniteImageRepresentation E G V)
    (Q : Type*) [Group Q] [Fintype Q] : Prop :=
  Nonempty (FiniteQuotientRealization ρ Q)

theorem finiteCuttingQuotient_factorization
    (ρ : FiniteImageRepresentation E G V)
    {Q : Type*} [Group Q] [Fintype Q]
    (R : FiniteQuotientRealization ρ Q) :
    ρ.toRepresentation = R.action.comp R.quotient := R.factorization

end
end LastLib.Book03RamificationTheory.Chapter10
