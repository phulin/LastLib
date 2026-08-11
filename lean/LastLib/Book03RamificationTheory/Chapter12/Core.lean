import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Notation
import Mathlib.GroupTheory.Coset.Card
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Induced
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.ValuationSubring

namespace LastLib.Book03RamificationTheory.Chapter12

noncomputable section

universe uV

open scoped BigOperators

/-!
## Shared interfaces for Chapter 12

The preceding chapters develop the local ramification and Artin-character
objects used here. Mathlib currently supplies the representation, character,
invariant-space, induction, restriction, and fixed-field primitives, but not
the book's conductor package. The small records below are the book-facing
interfaces at that boundary; they are deliberately independent of any one
valuation implementation.
-/

/- LOCAL_DEPENDENCY_GUESS: this is the numerical interface expected from the
preceding different/degree chapters. It records the canonical invariants
`e`, `f`, and the different exponent `d` without adding any conductor
conclusion as a hypothesis. -/
structure Chapter12LocalExtensionNumbers where
  ramificationIndex : ℕ
  residueDegree : ℕ
  differentExponent : ℕ
  ramificationIndex_pos : 0 < ramificationIndex
  residueDegree_pos : 0 < residueDegree
  degree : ℕ
  degree_eq : degree = ramificationIndex * residueDegree

namespace Chapter12LocalExtensionNumbers

def discriminantExponent (p : Chapter12LocalExtensionNumbers) : ℕ :=
  p.residueDegree * p.differentExponent

@[simp] theorem discriminantExponent_def (p : Chapter12LocalExtensionNumbers) :
    p.discriminantExponent = p.residueDegree * p.differentExponent :=
  rfl

end Chapter12LocalExtensionNumbers

/- LOCAL_DEPENDENCY_GUESS: the field-level wrapper is the minimal place where
the exact finite-separable hypotheses and the degree identity are recorded.
The residue-separability witness is kept separate below because it depends on
a chosen extension of a valuation. -/
structure Chapter12FiniteSeparableLocalExtension
    (K M : Type*) [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M] [Algebra.IsSeparable K M] where
  numbers : Chapter12LocalExtensionNumbers
  degree_eq : Module.finrank K M = numbers.degree

theorem chapter12FiniteSeparableLocalExtension_degree
    {K M : Type*} [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    (p : Chapter12FiniteSeparableLocalExtension K M) :
    Module.finrank K M = p.numbers.degree :=
  p.degree_eq

def chapter12ResidueExtensionSeparable
    {K M Γ : Type*} [Field K] [Field M] [Algebra K M]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vM : Valuation M Γ)
    [vK.HasExtension vM]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vM.valuationSubring)] : Prop :=
  Algebra.IsSeparable (IsLocalRing.ResidueField vK.valuationSubring)
    (IsLocalRing.ResidueField vM.valuationSubring)

/- LOCAL_DEPENDENCY_GUESS: a residue-separability witness for the chosen finite
Galois realization. This exposes the exact Mathlib proposition rather than
replacing it by a stronger perfectness assumption. -/
structure Chapter12ResidueSeparableWitness
    {K N Γ : Type*} [Field K] [Field N] [Algebra K N]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vN : Valuation N Γ)
    [vK.HasExtension vN]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vN.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vN.valuationSubring)] where
  separable : Algebra.IsSeparable (IsLocalRing.ResidueField vK.valuationSubring)
    (IsLocalRing.ResidueField vN.valuationSubring)

/- A finite Galois realization contains the intermediate field as a fixed
field. The canonical subgroup/fixed-field equivalence is exposed below. -/
structure Chapter12FiniteGaloisRealization
    (K N : Type*) [Field K] [Field N] [Algebra K N]
    [FiniteDimensional K N] [IsGalois K N] where
  intermediate : IntermediateField K N
  subgroup : Subgroup (Gal(N / K))
  fixedField_eq : intermediate = IntermediateField.fixedField subgroup

def chapter12FixedFieldGaloisEquiv
    {K N : Type*} [Field K] [Field N] [Algebra K N]
    [FiniteDimensional K N] [IsGalois K N]
    (R : Chapter12FiniteGaloisRealization K N) :
    R.subgroup ≃* Gal(N / IntermediateField.fixedField R.subgroup) :=
  IntermediateField.subgroupEquivAlgEquiv R.subgroup

theorem chapter12FixedGaloisRealization_fixed_field
    {K N : Type*} [Field K] [Field N] [Algebra K N]
    [FiniteDimensional K N] [IsGalois K N]
    (R : Chapter12FiniteGaloisRealization K N) :
    R.intermediate = IntermediateField.fixedField R.subgroup :=
  R.fixedField_eq

/- A representation of an absolute group together with a chosen finite image.
The finite group is the object on which the conductor API is evaluated. -/
structure Chapter12FiniteImageRepresentation
    (Γ Q V : Type*) [Group Γ] [Group Q] [Fintype Q]
    [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] where
  quotient : Γ →* Q
  quotient_surjective : Function.Surjective quotient
  representation : Representation ℚ Q V

def Chapter12FiniteImageRepresentation.realized
    {Γ Q V : Type*} [Group Γ] [Group Q] [Fintype Q]
    [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (W : Chapter12FiniteImageRepresentation Γ Q V) :
    Representation ℚ Γ V :=
  W.representation.comp W.quotient

@[simp] theorem chapter12FiniteImageRepresentation_realized_apply
    {Γ Q V : Type*} [Group Γ] [Group Q] [Fintype Q]
    [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (W : Chapter12FiniteImageRepresentation Γ Q V) (g : Γ) (v : V) :
    W.realized g v = W.representation (W.quotient g) v :=
  rfl

/- The finite lower filtration needed to write the fixed-space conductor sum.
The bound makes the sum finite; `lower_succ_le` is the usual lower-numbering
monotonicity bridge. -/
structure Chapter12RamificationProfile (G : Type*) [Group G] [Fintype G] where
  inertia : Subgroup G
  lower : ℕ → Subgroup G
  bound : ℕ
  lower_zero : lower 0 = inertia
  lower_succ_le : ∀ i, lower (i + 1) ≤ lower i
  lower_eq_bot_of_bound : ∀ i, bound < i → lower i = ⊥

def chapter12FixedSpaceCodimension
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (S : Subgroup G)
    (ρ : Representation ℚ G V) : ℕ :=
    Module.finrank ℚ V -
    Module.finrank ℚ (Representation.invariants (ρ.comp S.subtype))

theorem chapter12_mem_fixed_space_iff
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℚ V]
    (S : Subgroup G) (ρ : Representation ℚ G V) (v : V) :
    v ∈ Representation.invariants (ρ.comp S.subtype) ↔
      ∀ s : S, ρ (S.subtype s) v = v := by
  rfl

def chapter12ArtinConductorSum
    {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (P : Chapter12RamificationProfile G)
    (ρ : Representation ℚ G V) : ℚ :=
  ∑ i in Finset.range (P.bound + 1),
    ((Nat.card (P.lower i) : ℚ) / (Nat.card P.inertia : ℚ)) *
      (chapter12FixedSpaceCodimension (P.lower i) ρ : ℚ)

def chapter12SwanConductorSum
    {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (P : Chapter12RamificationProfile G)
    (ρ : Representation ℚ G V) : ℚ :=
  ∑ i in Finset.Icc 1 P.bound,
    ((Nat.card (P.lower i) : ℚ) / (Nat.card P.inertia : ℚ)) *
      (chapter12FixedSpaceCodimension (P.lower i) ρ : ℚ)

def chapter12CharacterPairing
    {G : Type*} [Group G] [Fintype G]
    (A B : G → ℚ) : ℚ :=
  (Nat.card G : ℚ)⁻¹ * ∑ g : G, A g * B (g⁻¹)

def chapter12IsClassFunction
    {G R : Type*} [Group G] (A : G → R) : Prop :=
  ∀ x g, A (x * g * x⁻¹) = A g

def chapter12RestrictClassFunction
    {H G R : Type*} [Group H] [Group G]
    (ι : H →* G) (A : G → R) : H → R :=
  fun h => A (ι h)

@[simp] theorem chapter12RestrictClassFunction_apply
    {H G R : Type*} [Group H] [Group G]
    (ι : H →* G) (A : G → R) (h : H) :
    chapter12RestrictClassFunction ι A h = A (ι h) :=
  rfl

def chapter12RegularCharacter (H : Type*) [Group H] [Fintype H] : H → ℚ := by
  classical
  exact fun h => if h = 1 then (Nat.card H : ℚ) else 0

@[simp] theorem chapter12RegularCharacter_one
    (H : Type*) [Group H] [Fintype H] :
    chapter12RegularCharacter H 1 = (Nat.card H : ℚ) := by
  simp [chapter12RegularCharacter]

theorem chapter12RegularCharacter_ne_one
    (H : Type*) [Group H] [Fintype H] {h : H} (hh : h ≠ 1) :
    chapter12RegularCharacter H h = 0 := by
  classical
  rw [chapter12RegularCharacter, if_neg hh]

def chapter12SupportedAtOne {H R : Type*} [Group H]
    [Zero R]
    (A : H → R) : Prop :=
  ∀ h, h ≠ 1 → A h = 0

def chapter12ScalarMultipleOfRegularCharacter
    {H : Type*} [Group H] [Fintype H] (A : H → ℚ) : Prop :=
  ∃ c : ℚ, ∀ h, A h = c * chapter12RegularCharacter H h

theorem chapter12_supported_difference_is_scalar_regular
    {H : Type*} [Group H] [Fintype H] (A B : H → ℚ)
    (hoff : ∀ h, h ≠ 1 → A h = B h) :
    chapter12ScalarMultipleOfRegularCharacter (A - B) := by
  sorry

/-!
### Conductor and Artin-character boundary

This record is the reusable preceding-chapter API used by the chapter
statements. Its fields are the fixed-space/conductor and character-pairing
bridges, not any induction or restriction conclusion. A later reconciliation
pass should replace it by the concrete Chapter 10--11 declarations once those
modules are available under stable names.
-/
structure Chapter12ConductorProfile (G : Type*) [Group G] [Fintype G] where
  ramification : Chapter12RamificationProfile G
  artinCharacter : G → ℚ
  artinCharacter_is_class_function : chapter12IsClassFunction artinCharacter
  artinConductor :
    ∀ (V : Type uV) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V],
      Representation ℚ G V → ℕ
  swanConductor :
    ∀ (V : Type uV) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V],
      Representation ℚ G V → ℕ
  artin_eq_fixed_space_sum :
    ∀ (V : Type uV) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
      (ρ : Representation ℚ G V),
      (artinConductor V ρ : ℚ) = chapter12ArtinConductorSum ramification ρ
  swan_eq_positive_fixed_space_sum :
    ∀ (V : Type uV) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
      (ρ : Representation ℚ G V),
      (swanConductor V ρ : ℚ) = chapter12SwanConductorSum ramification ρ
  artin_eq_tame_add_swan :
    ∀ (V : Type uV) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
      (ρ : Representation ℚ G V),
      artinConductor V ρ =
        chapter12FixedSpaceCodimension ramification.inertia ρ + swanConductor V ρ
  artin_eq_character_pairing :
    ∀ (V : Type uV) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
      (ρ : Representation ℚ G V),
      (artinConductor V ρ : ℚ) =
        chapter12CharacterPairing artinCharacter ρ.character

def chapter12InducedRepresentation
    {H G V : Type*} [Group H] [Group G] [AddCommGroup V] [Module ℚ V]
    (ι : H →* G) (ρ : Representation ℚ H V) :
    Representation ℚ G (Representation.IndV ι ρ) :=
  Representation.ind ι ρ

def chapter12RestrictedRepresentation
    {H G V : Type*} [Group H] [Group G] [AddCommGroup V] [Module ℚ V]
    (ι : H →* G) (ρ : Representation ℚ G V) :
    Representation ℚ H V :=
  ρ.comp ι

@[simp] theorem chapter12RestrictedRepresentation_apply
    {H G V : Type*} [Group H] [Group G] [AddCommGroup V] [Module ℚ V]
    (ι : H →* G) (ρ : Representation ℚ G V) (h : H) (v : V) :
    chapter12RestrictedRepresentation ι ρ h v = ρ (ι h) v :=
  rfl

def chapter12InductionRHS
    (p : Chapter12LocalExtensionNumbers) (dimension conductor : ℕ) : ℕ :=
  p.residueDegree * (p.differentExponent * dimension + conductor)

def chapter12InductionRHSUsingDiscriminantExponent
    (p : Chapter12LocalExtensionNumbers) (dimension conductor : ℕ) : ℕ :=
  p.discriminantExponent * dimension + p.residueDegree * conductor

theorem chapter12_induction_rhs_rewrite
    (p : Chapter12LocalExtensionNumbers) (dimension conductor : ℕ) :
    chapter12InductionRHS p dimension conductor =
      chapter12InductionRHSUsingDiscriminantExponent p dimension conductor := by
  sorry

end
end LastLib.Book03RamificationTheory.Chapter12
