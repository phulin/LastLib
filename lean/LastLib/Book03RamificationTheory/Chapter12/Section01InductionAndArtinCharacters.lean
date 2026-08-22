import LastLib.Book03RamificationTheory.Chapter12.Core

namespace LastLib.Book03RamificationTheory.Chapter12

noncomputable section

universe u

open scoped BigOperators

/-!
## 12.1--12.2. Induction and the Artin-character calculation
-/

def chapter12InducedFiniteImageRepresentation
    {E Γ H G V : Type*} [Field E] [CharZero E] [Group Γ]
    [TopologicalSpace Γ] [Group H] [Fintype H] [Group G]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (ι : H →* G) (_hι : Function.Injective ι)
    (W : Chapter12FiniteImageRepresentation E Γ H V) :
    Representation E G (Representation.IndV ι W.representation) :=
  chapter12InducedRepresentation ι W.representation

/- The value at the identity is the normalization datum supplied by Hilbert's
different formula.  Keeping it explicit makes the scalar-regular-character
argument reusable. -/
structure Chapter12ArtinCharacterNormalization
    {G : Type*} [Group G] [Fintype G]
    (A : Chapter12ConductorProfile G)
    (p : Chapter12LocalExtensionNumbers) where
  at_identity : A.artinCharacter 1 = (p.residueDegree * p.differentExponent : ℚ)

/- LOCAL_DEPENDENCY_GUESS: this records the finite realization comparison of
the two displacement functions.  It is the exact off-identity input used in
the proof of (12.1), not the induction-conductor formula itself. -/
structure Chapter12ArtinRestrictionComparison
    {G H : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
    (ι : H →* G) (AG : G → ℚ) (AH : H → ℚ)
    (p : Chapter12LocalExtensionNumbers) where
  off_identity : ∀ h, h ≠ 1 → AG (ι h) = (p.residueDegree : ℚ) * AH h

/- The field-theoretic tower identities needed to compute the scalar at one. -/
structure Chapter12InductionTowerNormalization
    (pNK pNM pMK : Chapter12LocalExtensionNumbers)
    (H : Type*) [Group H] [Fintype H] where
  residueDegree_mul :
    pNK.residueDegree = pNM.residueDegree * pMK.residueDegree
  different_transitivity :
    pNK.differentExponent =
      pNM.differentExponent + pNM.ramificationIndex * pMK.differentExponent
  subgroup_card :
    Nat.card H = pNM.ramificationIndex * pNM.residueDegree

theorem chapter12_artin_character_one_difference
    {G H : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
    (ι : H →* G) (AG : G → ℚ) (AH : H → ℚ)
    (pNK pNM pMK : Chapter12LocalExtensionNumbers)
    (T : Chapter12InductionTowerNormalization pNK pNM pMK H)
    (hAG : AG 1 = (pNK.residueDegree * pNK.differentExponent : ℚ))
    (hAH : AH 1 = (pNM.residueDegree * pNM.differentExponent : ℚ)) :
    AG (ι 1) - (pMK.residueDegree : ℚ) * AH 1 =
      (Nat.card H : ℚ) * (pMK.discriminantExponent : ℚ) := by
  sorry

theorem chapter12_artin_character_difference_supported_at_one
    {G H : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
    (ι : H →* G) (AG : G → ℚ) (AH : H → ℚ)
    (p : Chapter12LocalExtensionNumbers)
    (C : Chapter12ArtinRestrictionComparison ι AG AH p) :
    chapter12SupportedAtOne
      (fun h => AG (ι h) - (p.residueDegree : ℚ) * AH h) := by
  intro h hh
  simp only [sub_eq_zero]
  exact C.off_identity h hh

/- The exact class-function identity (12.1).  The identity-at-one hypothesis
is separated from the off-identity comparison so that each is independently
usable in later quotient and tower arguments. -/
theorem chapter12_artin_character_induction_identity
    {G H : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
    (ι : H →* G) (AG : G → ℚ) (AH : H → ℚ)
    (p : Chapter12LocalExtensionNumbers)
    (hoff : ∀ h, h ≠ 1 → AG (ι h) = (p.residueDegree : ℚ) * AH h)
    (hone : AG (ι 1) - (p.residueDegree : ℚ) * AH 1 =
      (Nat.card H : ℚ) * (p.discriminantExponent : ℚ)) :
    chapter12RestrictClassFunction ι AG =
      fun h => (p.residueDegree : ℚ) * AH h +
        (p.discriminantExponent : ℚ) * chapter12RegularCharacter H h := by
  sorry

theorem chapter12_artin_character_difference_is_scalar_regular
    {G H : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
    (ι : H →* G) (AG : G → ℚ) (AH : H → ℚ)
    (p : Chapter12LocalExtensionNumbers)
    (hoff : ∀ h, h ≠ 1 → AG (ι h) = (p.residueDegree : ℚ) * AH h) :
    chapter12ScalarMultipleOfRegularCharacter
      (fun h => AG (ι h) - (p.residueDegree : ℚ) * AH h) := by
  apply chapter12_supported_difference_is_scalar_regular
    (fun h => AG (ι h))
    (fun h => (p.residueDegree : ℚ) * AH h)
  exact hoff

/- Frobenius reciprocity at the character-pairing level. -/
theorem chapter12_frobenius_reciprocity_for_character_pairing
    {E G H V : Type*} [Field E] [CharZero E] [Group G] [Fintype G] [Group H] [Fintype H]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (ι : H →* G) (hι : Function.Injective ι)
    (AG : G → E) (hconj : chapter12IsClassFunction AG)
    (ρ : Representation E H V) :
    chapter12CharacterPairing AG
        (chapter12InducedRepresentation ι ρ).character =
      chapter12CharacterPairing (chapter12RestrictClassFunction ι AG)
        ρ.character := by
  sorry

theorem chapter12_regular_character_pairing
    {E H V : Type*} [Field E] [CharZero E] [Group H] [Fintype H]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (ρ : Representation E H V) :
    chapter12CharacterPairing (chapter12RegularCharacter H) ρ.character =
      (Module.finrank E V : E) := by
  sorry

theorem chapter12_induction_pairing_expansion
    {E H V : Type*} [Field E] [CharZero E] [Group H] [Fintype H]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (AH : H → E) (p : Chapter12LocalExtensionNumbers)
    (ρ : Representation E H V) :
    chapter12CharacterPairing
        (fun h => (p.residueDegree : E) * AH h +
          (p.discriminantExponent : E) * chapter12RegularCharacter H h)
        ρ.character =
      (p.discriminantExponent : E) * (Module.finrank E V : E) +
        (p.residueDegree : E) * chapter12CharacterPairing AH ρ.character := by
  sorry

/- The conductor formula in the normalization used in §12.1. -/
theorem chapter12_induction_conductor_formula
    {E G H V : Type u} [Field E] [CharZero E] [Group G] [Fintype G]
    [Group H] [Fintype H]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (ι : H →* G) (hι : Function.Injective ι)
    (AK : Chapter12ConductorProfile G)
    (AM : Chapter12ConductorProfile H)
    (p : Chapter12LocalExtensionNumbers) (ρ : Representation E H V)
    (hoff : ∀ h, h ≠ 1 →
      AK.artinCharacter (ι h) = (p.residueDegree : ℚ) * AM.artinCharacter h)
    (hone : AK.artinCharacter (ι 1) -
      (p.residueDegree : ℚ) * AM.artinCharacter 1 =
        (Nat.card H : ℚ) * (p.discriminantExponent : ℚ)) :
    AK.artinConductor _ (chapter12InducedRepresentation ι ρ) =
      chapter12InductionRHS p (Module.finrank E V) (AM.artinConductor _ ρ) := by
  sorry

/- The tame term in the induction proof is the codimension of the induced
inertia-fixed space.  It is kept as an explicit hypothesis here because the
abstract conductor profiles deliberately do not identify their inertia groups
with a concrete finite Galois realization. -/
theorem chapter12_induction_swan_conductor_formula
    {E G H V : Type u} [Field E] [CharZero E] [Group G] [Fintype G]
    [Group H] [Fintype H]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (ι : H →* G) (hι : Function.Injective ι)
    (AK : Chapter12ConductorProfile G)
    (AM : Chapter12ConductorProfile H)
    (p : Chapter12LocalExtensionNumbers) (ρ : Representation E H V)
    (hoff : ∀ h, h ≠ 1 →
      AK.artinCharacter (ι h) = (p.residueDegree : ℚ) * AM.artinCharacter h)
    (hone : AK.artinCharacter (ι 1) -
      (p.residueDegree : ℚ) * AM.artinCharacter 1 =
        (Nat.card H : ℚ) * (p.discriminantExponent : ℚ))
    (hbase : p.ramificationIndex ≤ p.differentExponent + 1)
    (htame :
      chapter12FixedSpaceCodimension AK.ramification.inertia
          (chapter12InducedRepresentation ι ρ) =
        p.residueDegree *
          (p.ramificationIndex * Module.finrank E V -
            Module.finrank E
              (Representation.invariants
              (ρ.comp AM.ramification.inertia.subtype)))) :
    AK.swanConductor _ (chapter12InducedRepresentation ι ρ) =
      p.residueDegree *
        (AM.swanConductor _ ρ +
          (p.differentExponent + 1 - p.ramificationIndex) *
            Module.finrank E V) := by
  sorry

/- The equivalent discriminant-exponent form
`delta * dim + f * a_M(W)`. -/
theorem chapter12_induction_conductor_formula_using_discriminant_exponent
    {E G H V : Type u} [Field E] [CharZero E] [Group G] [Fintype G]
    [Group H] [Fintype H]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (ι : H →* G) (hι : Function.Injective ι)
    (AK : Chapter12ConductorProfile G)
    (AM : Chapter12ConductorProfile H)
    (p : Chapter12LocalExtensionNumbers) (ρ : Representation E H V)
    (hoff : ∀ h, h ≠ 1 →
      AK.artinCharacter (ι h) = (p.residueDegree : ℚ) * AM.artinCharacter h)
    (hone : AK.artinCharacter (ι 1) -
      (p.residueDegree : ℚ) * AM.artinCharacter 1 =
        (Nat.card H : ℚ) * (p.discriminantExponent : ℚ)) :
    AK.artinConductor _ (chapter12InducedRepresentation ι ρ) =
      p.discriminantExponent * Module.finrank E V +
        p.residueDegree * AM.artinConductor _ ρ := by
  sorry

/- The finite-Galois-realization specialization threads the hypotheses stated
in the prose: finite separability of the intermediate field and separability
of the residue extension of the chosen realization. -/
theorem chapter12_induction_formula_in_galois_realization
    {E K N V : Type u} {Γ : Type*} [Field E] [CharZero E] [Field K] [Field N] [Algebra K N]
    [FiniteDimensional K N] [IsGalois K N]
    [Fintype (Gal(N / K))]
    [LinearOrderedCommGroupWithZero Γ]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (R : Chapter12FiniteGaloisRealization K N)
    [Algebra.IsSeparable K R.intermediate]
    (hKM : Chapter12FiniteSeparableLocalExtension K R.intermediate)
    (vK : Valuation K Γ) (vN : Valuation N Γ)
    [vK.HasExtension vN]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vN.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vN.valuationSubring)]
    (hres : Chapter12ResidueSeparableWitness vK vN)
    (AK : Chapter12ConductorProfile (Gal(N / K)))
    (AM : Chapter12ConductorProfile R.subgroup)
    (ρ : Representation E R.subgroup V)
    (hoff : ∀ h, h ≠ 1 →
      AK.artinCharacter (R.subgroup.subtype h) =
        (hKM.numbers.residueDegree : ℚ) * AM.artinCharacter h)
    (hone : AK.artinCharacter (R.subgroup.subtype 1) -
      (hKM.numbers.residueDegree : ℚ) * AM.artinCharacter 1 =
        (Nat.card R.subgroup : ℚ) *
          (hKM.numbers.discriminantExponent : ℚ)) :
    AK.artinConductor _ (chapter12InducedRepresentation R.subgroup.subtype ρ) =
      chapter12InductionRHS hKM.numbers (Module.finrank E V)
        (AM.artinConductor _ ρ) := by
  sorry

end
end LastLib.Book03RamificationTheory.Chapter12
