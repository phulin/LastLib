import LastLib.Book03RamificationTheory.Chapter10.Dependencies

namespace LastLib.Book03RamificationTheory.Chapter10

noncomputable section

/-! ## 10.1. What a conductor should measure -/

/- SOURCE_ISSUE (10.1): the source writes `G` as an arbitrary group and then
chooses finite local Galois groups `G_i`.  The minimal principled correction is
to make a finite quotient, its ramification filtration, and the factorization
of the representation explicit through `FiniteQuotientRealization`. -/

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
  sorry

theorem charZero_not_modularCoefficientRegime [Fintype G] [CharZero E] :
    ¬ ModularCoefficientRegime (E := E) (G := G) := by
  sorry

/-- Maschke semisimplicity for a finite group over a characteristic-zero field. -/
theorem finite_group_representation_is_semisimple
    [Fintype G] [CharZero E] (ρ : Representation E G V) :
    Representation.IsSemisimpleRepresentation ρ := by
  sorry

/-- The averaging operator used to split the invariant subspace. -/
def invariantAverage [Fintype G] [Invertible (Fintype.card G : E)]
    (ρ : Representation E G V) : V →ₗ[E] V :=
  Representation.averageMap ρ

theorem invariantAverage_mem [Fintype G] [Invertible (Fintype.card G : E)]
    (ρ : Representation E G V) (v : V) :
    invariantAverage ρ v ∈ fixedSpace ρ (⊤ : Subgroup G) := by
  sorry

theorem invariantAverage_eq_self_of_mem [Fintype G] [Invertible (Fintype.card G : E)]
    (ρ : Representation E G V) {v : V}
    (hv : v ∈ fixedSpace ρ (⊤ : Subgroup G)) :
    invariantAverage ρ v = v := by
  sorry

/-- Averaging is a projection onto the fixed space; this is the exact
split-invariants interface needed for the characteristic-zero discussion. -/
theorem invariantAverage_splits_fixedSpace
    [Fintype G] [Invertible (Fintype.card G : E)] (ρ : Representation E G V) :
    (∀ v, invariantAverage ρ v ∈ fixedSpace ρ (⊤ : Subgroup G)) ∧
      (∀ v, v ∈ fixedSpace ρ (⊤ : Subgroup G) → invariantAverage ρ v = v) := by
  sorry

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
