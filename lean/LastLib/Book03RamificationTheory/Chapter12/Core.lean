import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Notation
import Mathlib.GroupTheory.Coset.Card
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Induced
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Topology.Basic
import LastLib.Book03RamificationTheory.Chapter11.Dependencies

namespace LastLib.Book03RamificationTheory.Chapter12

noncomputable section

universe u

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

noncomputable def chapter12IntermediateGaloisEquiv
    {K N : Type*} [Field K] [Field N] [Algebra K N]
    [FiniteDimensional K N] [IsGalois K N]
    (R : Chapter12FiniteGaloisRealization K N) :
    R.subgroup ≃* Gal(N / R.intermediate) := by
  sorry

theorem chapter12FixedGaloisRealization_fixed_field
    {K N : Type*} [Field K] [Field N] [Algebra K N]
    [FiniteDimensional K N] [IsGalois K N]
    (R : Chapter12FiniteGaloisRealization K N) :
    R.intermediate = IntermediateField.fixedField R.subgroup :=
  R.fixedField_eq

/- A representation of a topological absolute group together with a chosen
finite image.  The open-kernel field is the continuity input needed for the
finite quotient to cut out a finite extension. -/
structure Chapter12FiniteImageRepresentation
    (E Γ Q V : Type*) [Field E] [CharZero E] [Group Γ]
    [TopologicalSpace Γ] [Group Q] [Fintype Q]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V] where
  quotient : Γ →* Q
  quotient_surjective : Function.Surjective quotient
  quotient_kernel_open : IsOpen (quotient.ker : Set Γ)
  representation : Representation E Q V

def Chapter12FiniteImageRepresentation.realized
    {E Γ Q V : Type*} [Field E] [CharZero E] [Group Γ]
    [TopologicalSpace Γ] [Group Q] [Fintype Q]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (W : Chapter12FiniteImageRepresentation E Γ Q V) :
    Representation E Γ V :=
  W.representation.comp W.quotient

@[simp] theorem chapter12FiniteImageRepresentation_realized_apply
    {E Γ Q V : Type*} [Field E] [CharZero E] [Group Γ]
    [TopologicalSpace Γ] [Group Q] [Fintype Q]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (W : Chapter12FiniteImageRepresentation E Γ Q V) (g : Γ) (v : V) :
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

/- The preceding chapter's finite ramification data is the canonical source
for the lower filtration.  This adapter keeps the Chapter-12 cutoff
convention (`bound < i`) while exposing that established interface here. -/
def chapter12RamificationProfileOfChapter11
    {G : Type*} [Group G] [Fintype G]
    (D : LastLib.Book03RamificationTheory.Chapter11.Chapter11RamificationData G) :
    Chapter12RamificationProfile G where
  inertia := D.inertia
  lower := D.lower
  bound := D.bound
  lower_zero := D.lower_zero
  lower_succ_le := D.lower_succ_le
  lower_eq_bot_of_bound := by
    intro i hi
    exact D.lower_eq_bot_of_bound_le i (Nat.le_of_lt hi)

def chapter12FixedSpaceCodimension
    {E G V : Type*} [Field E] [Group G] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] (S : Subgroup G)
    (ρ : Representation E G V) : ℕ :=
    Module.finrank E V -
    Module.finrank E (Representation.invariants (ρ.comp S.subtype))

theorem chapter12_mem_fixed_space_iff
    {E G V : Type*} [Field E] [Group G] [AddCommGroup V] [Module E V]
    (S : Subgroup G) (ρ : Representation E G V) (v : V) :
    v ∈ Representation.invariants (ρ.comp S.subtype) ↔
      ∀ s : S, ρ (S.subtype s) v = v := by
  rfl

def chapter12ArtinConductorSum
    {E G V : Type*} [Field E] [CharZero E] [Group G] [Fintype G] [AddCommGroup V]
    [Module E V] [FiniteDimensional E V] (P : Chapter12RamificationProfile G)
    (ρ : Representation E G V) : E :=
  Finset.sum (Finset.range (P.bound + 1)) (fun i =>
    ((Nat.card (P.lower i) : E) / (Nat.card P.inertia : E)) *
      (chapter12FixedSpaceCodimension (P.lower i) ρ : E))

def chapter12SwanConductorSum
    {E G V : Type*} [Field E] [CharZero E] [Group G] [Fintype G] [AddCommGroup V]
    [Module E V] [FiniteDimensional E V] (P : Chapter12RamificationProfile G)
    (ρ : Representation E G V) : E :=
  Finset.sum (Finset.Icc 1 P.bound) (fun i =>
    ((Nat.card (P.lower i) : E) / (Nat.card P.inertia : E)) *
      (chapter12FixedSpaceCodimension (P.lower i) ρ : E))

def chapter12CharacterPairing
    {G R : Type*} [Group G] [Fintype G] [Field R] [CharZero R]
    (A B : G → R) : R :=
  (Nat.card G : R)⁻¹ * ∑ g : G, A g * B (g⁻¹)

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

def chapter12RegularCharacter (H : Type*) [Group H] [Fintype H]
    {R : Type*} [Field R] : H → R := by
  classical
  exact fun h => if h = 1 then (Nat.card H : R) else 0

@[simp] theorem chapter12RegularCharacter_one
    (H : Type*) [Group H] [Fintype H] {R : Type*} [Field R] :
    chapter12RegularCharacter (R := R) H 1 = (Nat.card H : R) := by
  simp [chapter12RegularCharacter]

theorem chapter12RegularCharacter_ne_one
    (H : Type*) [Group H] [Fintype H] {R : Type*} [Field R]
    {h : H} (hh : h ≠ 1) :
    chapter12RegularCharacter (R := R) H h = 0 := by
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
pass can instantiate it from the concrete Chapter 10--11 declarations; those
modules use a different lower-filtration and rational-valued packaging.
-/
structure Chapter12ConductorProfile (G : Type u) [Group G] [Fintype G] where
  ramification : Chapter12RamificationProfile G
  artinCharacter : G → ℚ
  artinCharacter_is_class_function : chapter12IsClassFunction artinCharacter
  artinConductor :
    ∀ {E : Type u} [Field E] [CharZero E]
      (V : Type u) [AddCommGroup V] [Module E V] [FiniteDimensional E V],
      Representation E G V → ℕ
  swanConductor :
    ∀ {E : Type u} [Field E] [CharZero E]
      (V : Type u) [AddCommGroup V] [Module E V] [FiniteDimensional E V],
      Representation E G V → ℕ
  artin_eq_fixed_space_sum :
    ∀ {E : Type u} [Field E] [CharZero E]
      (V : Type u) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
      (ρ : Representation E G V),
      (artinConductor (E := E) V ρ : E) = chapter12ArtinConductorSum ramification ρ
  swan_eq_positive_fixed_space_sum :
    ∀ {E : Type u} [Field E] [CharZero E]
      (V : Type u) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
      (ρ : Representation E G V),
      (swanConductor (E := E) V ρ : E) = chapter12SwanConductorSum ramification ρ
  artin_eq_tame_add_swan :
    ∀ {E : Type u} [Field E] [CharZero E]
      (V : Type u) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
      (ρ : Representation E G V),
      artinConductor (E := E) V ρ =
        chapter12FixedSpaceCodimension ramification.inertia ρ + swanConductor (E := E) V ρ
  artin_eq_character_pairing :
    ∀ {E : Type u} [Field E] [CharZero E]
      (V : Type u) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
      (ρ : Representation E G V),
      (artinConductor (E := E) V ρ : E) =
        chapter12CharacterPairing (fun g => (artinCharacter g : E)) ρ.character

def chapter12InducedRepresentation
    {E H G V : Type*} [Field E] [Group H] [Group G] [AddCommGroup V]
    [Module E V]
    (ι : H →* G) (ρ : Representation E H V) :
    Representation E G (Representation.IndV ι ρ) :=
  Representation.ind ι ρ

def chapter12RestrictedRepresentation
    {E H G V : Type*} [Field E] [Group H] [Group G] [AddCommGroup V]
    [Module E V]
    (ι : H →* G) (ρ : Representation E G V) :
    Representation E H V :=
  ρ.comp ι

@[simp] theorem chapter12RestrictedRepresentation_apply
    {E H G V : Type*} [Field E] [Group H] [Group G] [AddCommGroup V]
    [Module E V]
    (ι : H →* G) (ρ : Representation E G V) (h : H) (v : V) :
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
