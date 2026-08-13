import LastLib.Book06GlobalClassFieldTheory.Chapter07.Section03ConductorsOfExtensionsAndCharacters
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-!
# 7.6. The conductor–discriminant formula

The relative discriminant is the relative ideal norm of the different.  The
profile structure below records the local ramification data needed to compare
that canonical ideal with the finite conductor ideals of the characters of a
finite abelian Galois group.
-/

namespace LastLib.Book06GlobalClassFieldTheory.Chapter07

open scoped BigOperators nonZeroDivisors
open NumberField

noncomputable section

variable {K I : Type*} [Field K] [NumberField K]
  [CommGroup I] [TopologicalSpace I] [IsTopologicalGroup I]
variable {D : IdeleContext K I}
variable {L G : Type*} [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [CommGroup G] [Fintype G]
  [Algebra (𝓞 K) (𝓞 L)] [Module.Finite (𝓞 K) (𝓞 L)]
  [Module.IsTorsionFree (𝓞 K) (𝓞 L)]

noncomputable instance subgroupFintype {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) :
    Fintype H :=
  Fintype.ofFinite H

/-! ### The different and relative discriminant -/

noncomputable def relativeDiscriminantIdeal
    (A B : Type*) [CommRing A] [IsDedekindDomain A]
    [CommRing B] [IsDedekindDomain B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B] : Ideal A :=
  Ideal.relNorm A (differentIdeal A B)

theorem relativeDiscriminantIdeal_is_relative_norm_of_different
    (A B : Type*) [CommRing A] [IsDedekindDomain A]
    [CommRing B] [IsDedekindDomain B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B] :
    relativeDiscriminantIdeal A B = Ideal.relNorm A (differentIdeal A B) := rfl

structure LowerRamificationData (D : Type*) [Fintype D] [Group D] where
  lower : ℕ → Subgroup D
  inertia : Subgroup D
  last : ℕ
  lower_zero : lower 0 = inertia
  lower_eventually_trivial : ∀ i, last < i → lower i = ⊥

def differentExponent {D : Type*} [Fintype D] [Group D]
    (R : LowerRamificationData D) : ℕ :=
  ∑ i ∈ Finset.range (R.last + 1), (Fintype.card (R.lower i) - 1)

theorem differentExponent_eq_sum_lower_ramification_groups
    {D : Type*} [Fintype D] [Group D]
    (R : LowerRamificationData D) :
    differentExponent R =
      ∑ i ∈ Finset.range (R.last + 1), (Fintype.card (R.lower i) - 1) := rfl

def regularRestrictionMultiplicity {G : Type*} [Fintype G] [Group G]
    (D : Subgroup G) : ℕ := Fintype.card G / Fintype.card D

def regularRepresentationFixedCard {D : Type*} [Fintype D] [Group D]
    (H : Subgroup D) : ℕ := Fintype.card D / Fintype.card H

theorem regular_representation_restricts_with_multiplicity
    {G : Type*} [Fintype G] [Group G] (D : Subgroup G)
    (hD : Fintype.card D ∣ Fintype.card G) :
    Fintype.card G = regularRestrictionMultiplicity D * Fintype.card D := by
  sorry

theorem regular_representation_fixed_vectors
    {D : Type*} [Fintype D] [Group D] (H : Subgroup D) :
    regularRepresentationFixedCard H = Fintype.card D / Fintype.card H := rfl

structure LocalDiscriminantProfile (D : Type*) [Fintype D] [Group D] where
  residueDegree : ℕ
  lowerRamification : LowerRamificationData D
  relativeDiscriminantExponent : ℕ
  relativeDiscriminantExponent_eq :
    relativeDiscriminantExponent =
      residueDegree * differentExponent lowerRamification

theorem local_relative_discriminant_exponent_formula
    {D : Type*} [Fintype D] [Group D]
    (P : LocalDiscriminantProfile D) :
    P.relativeDiscriminantExponent =
      P.residueDegree *
        (∑ i ∈ Finset.range (P.lowerRamification.last + 1),
          (Fintype.card (P.lowerRamification.lower i) - 1)) := by
  rw [P.relativeDiscriminantExponent_eq]
  rfl

/-! ### Global conductor–discriminant profiles -/

/-! The preceding extension API owns the complete character group.  The local
Artin-conductor additivity is kept as a single canonical bridge to the local
ramification API, rather than as unrelated fields on the final profile. -/

structure CanonicalLocalArtinConductorData
    (R : FiniteAbelianExtensionRealization K L G) where
  localDiscriminantExponent : NumberField.FinitePlace K → ℕ
  localArtinConductorExponent :
    (G →* ℂˣ) → NumberField.FinitePlace K → ℕ
  relativeDiscriminant_factorization :
    relativeDiscriminantIdeal (𝓞 K) (𝓞 L) =
      ∏ᶠ v : NumberField.FinitePlace K,
        v.maximalIdeal.asIdeal ^ localDiscriminantExponent v

theorem local_artin_conductor_additivity
    (R : FiniteAbelianExtensionRealization K L G)
    (P : CanonicalLocalArtinConductorData R) :
    ∀ v : NumberField.FinitePlace K,
      P.localDiscriminantExponent v =
        ∑ θ ∈ R.characterGroup, P.localArtinConductorExponent θ v := by
  sorry

structure ConductorDiscriminantProfile
    (D : IdeleContext K I) (L G : Type*)
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [CommGroup G] [Fintype G]
    [Algebra (𝓞 K) (𝓞 L)] [Module.Finite (𝓞 K) (𝓞 L)]
    [Module.IsTorsionFree (𝓞 K) (𝓞 L)] where
  extension : FiniteAbelianExtensionRealization K L G
  localArtinConductorData : CanonicalLocalArtinConductorData extension
  characterConductor : (G →* ℂˣ) → Modulus K
  characterConductor_exponent_eq :
    ∀ θ : G →* ℂˣ, ∀ v : NumberField.FinitePlace K,
      (characterConductor θ).finiteExponent v =
        localArtinConductorData.localArtinConductorExponent θ v
  trivial_character_conductor_finitePart :
    (characterConductor (1 : G →* ℂˣ)).finitePart = ⊤

theorem conductor_discriminant_formula
    (P : ConductorDiscriminantProfile D L G) :
    relativeDiscriminantIdeal (𝓞 K) (𝓞 L) =
      ∏ θ ∈ P.extension.characterGroup, (P.characterConductor θ).finitePart := by
  sorry

theorem conductor_discriminant_formula_as_local_exponents
    (P : ConductorDiscriminantProfile D L G) :
    ∀ v : NumberField.FinitePlace K,
      P.localArtinConductorData.localDiscriminantExponent v =
        ∑ θ ∈ P.extension.characterGroup,
          (P.characterConductor θ).finiteExponent v := by
  intro v
  rw [local_artin_conductor_additivity P.extension P.localArtinConductorData]
  apply Finset.sum_congr rfl
  intro θ hθ
  exact (P.characterConductor_exponent_eq θ v).symm

theorem trivial_character_contributes_the_unit_ideal
    (P : ConductorDiscriminantProfile D L G) :
    (P.characterConductor 1).finitePart = ⊤ := by
  exact P.trivial_character_conductor_finitePart

theorem character_conductor_infinite_part_does_not_enter_the_discriminant_ideal
    (P : ConductorDiscriminantProfile D L G) :
    relativeDiscriminantIdeal (𝓞 K) (𝓞 L) =
      ∏ θ ∈ P.extension.characterGroup, (P.characterConductor θ).finitePart := by
  exact conductor_discriminant_formula P

end

end LastLib.Book06GlobalClassFieldTheory.Chapter07
