import LastLib.Book06GlobalClassFieldTheory.Chapter11.Section07DirichletAndCMCharacterModels

namespace LastLib.Book06GlobalClassFieldTheory.Chapter11

open scoped BigOperators NumberField.AdeleRing RestrictedProduct
open NumberField

noncomputable section

/-! ## 11.8. The quadratic induction interface -/

structure Chapter11QuadraticInductionData
    (E G H : Type*) [Field E] [Group G] [Fintype G] [Group H] [Fintype H] where
  inclusion : H →* G
  inclusion_injective : Function.Injective inclusion
  index_two : Fintype.card G = 2 * Fintype.card H
  normality : ∀ g h, ∃ k, g * inclusion h * g⁻¹ = inclusion k
  theta : H →* Eˣ
  outside : G
  outside_not_in_image : ∀ h, outside ≠ inclusion h
  conjugation : H →* H
  conjugation_spec : ∀ h,
    inclusion (conjugation h) = outside * inclusion h * outside⁻¹
  conjugate_character : H →* Eˣ
  conjugate_spec : conjugate_character = theta.comp conjugation
  outside_square : H
  outside_square_spec : outside * outside = inclusion outside_square
  quadraticCharacter : G →* Eˣ
  quadratic_trivial_on_subgroup : quadraticCharacter.comp inclusion = 1
  quadratic_nontrivial : ∃ g, quadraticCharacter g ≠ 1

def chapter11QuadraticConjugateCharacter
    {E G H : Type*} [Field E] [Group G] [Fintype G] [Group H] [Fintype H]
    (D : Chapter11QuadraticInductionData E G H) : H →* Eˣ :=
  D.conjugate_character

def chapter11QuadraticInducedRepresentation
    {E G H : Type*} [Field E] [Group G] [Fintype G] [Group H] [Fintype H]
    (D : Chapter11QuadraticInductionData E G H) :
    Representation E G (Chapter11InducedSpace E G H D.inclusion D.theta) :=
  chapter11InducedRepresentation E G H D.inclusion D.theta

def chapter11QuadraticRestrictedRepresentation
    {E G H : Type*} [Field E] [Group G] [Fintype G] [Group H] [Fintype H]
    (D : Chapter11QuadraticInductionData E G H) :
    Representation E H (Chapter11InducedSpace E G H D.inclusion D.theta) :=
  chapter11RestrictRepresentation D.inclusion
    (chapter11QuadraticInducedRepresentation D)

theorem chapter11_quadratic_conjugate_character_spec
    {E G H : Type*} [Field E] [Group G] [Fintype G] [Group H] [Fintype H]
    (D : Chapter11QuadraticInductionData E G H) :
    chapter11QuadraticConjugateCharacter D = D.theta.comp D.conjugation :=
  D.conjugate_spec

theorem chapter11_quadratic_induced_restriction
    {E G H : Type*} [Field E] [Group G] [Fintype G] [Group H] [Fintype H]
    (D : Chapter11QuadraticInductionData E G H) :
    Nonempty
      ((chapter11QuadraticRestrictedRepresentation D).Equiv
        (Representation.prod
          (chapter11CharacterRepresentation E H D.theta)
          (chapter11CharacterRepresentation E H D.conjugate_character))) := by
  sorry

theorem chapter11_quadratic_induced_restriction_character
    {E G H : Type*} [Field E] [Group G] [Fintype G] [Group H] [Fintype H]
    (D : Chapter11QuadraticInductionData E G H) :
    chapter11RepresentationCharacter (chapter11QuadraticRestrictedRepresentation D) =
      fun h => (D.theta h : E) + (D.conjugate_character h : E) := by
  sorry

theorem chapter11_quadratic_induced_irreducible_iff
    {E G H : Type*} [Field E] [IsAlgClosed E] [CharZero E]
    [Group G] [Fintype G] [Group H] [Fintype H]
    (D : Chapter11QuadraticInductionData E G H) :
    chapter11RepresentationIrreducible (chapter11QuadraticInducedRepresentation D) ↔
      D.theta ≠ D.conjugate_character := by
  sorry

def Chapter11QuadraticExtensions
    {E G H : Type*} [Field E] [Group G] [Fintype G] [Group H] [Fintype H]
    (D : Chapter11QuadraticInductionData E G H) :=
  {η : G →* Eˣ // η.comp D.inclusion = D.theta}

theorem chapter11_quadratic_extension_square_root
    {E : Type*} [Field E] [IsAlgClosed E] (a : Eˣ) :
    ∃ b : Eˣ, b ^ (2 : ℕ) = a := by
  sorry

theorem chapter11_quadratic_equal_character_has_exactly_two_extensions
    {E G H : Type*} [Field E] [IsAlgClosed E] [Group G] [Fintype G]
    [Group H] [Fintype H]
    (D : Chapter11QuadraticInductionData E G H)
    (hequal : D.theta = D.conjugate_character) :
    ∃ η₁ η₂ : Chapter11QuadraticExtensions D,
      η₁ ≠ η₂ ∧ ∀ η : Chapter11QuadraticExtensions D,
        η = η₁ ∨ η = η₂ := by
  sorry

theorem chapter11_quadratic_equal_case_induced_decomposes
    {E G H : Type*} [Field E] [Group G] [Fintype G] [Group H] [Fintype H]
    (D : Chapter11QuadraticInductionData E G H)
    (hequal : D.theta = D.conjugate_character) :
    ∃ η₁ η₂ : G →* Eˣ,
      η₁.comp D.inclusion = D.theta ∧
      η₂.comp D.inclusion = D.theta ∧ η₁ ≠ η₂ := by
  sorry

theorem chapter11_quadratic_equal_case_induced_is_direct_sum
    {E G H : Type*} [Field E] [Group G] [Fintype G] [Group H] [Fintype H]
    (D : Chapter11QuadraticInductionData E G H)
    (η₁ η₂ : G →* Eˣ)
    (h₁ : η₁.comp D.inclusion = D.theta)
    (h₂ : η₂.comp D.inclusion = D.theta)
    (hne : η₁ ≠ η₂) :
    Nonempty
      ((chapter11QuadraticInducedRepresentation D).Equiv
        (Representation.prod
          (chapter11CharacterRepresentation E G η₁)
        (chapter11CharacterRepresentation E G η₂))) := by
  sorry

theorem chapter11_quadratic_extensions_differ_by_quadratic_character
    {E G H : Type*} [Field E] [Group G] [Fintype G] [Group H] [Fintype H]
    (D : Chapter11QuadraticInductionData E G H)
    (η₁ η₂ : G →* Eˣ)
    (h₁ : η₁.comp D.inclusion = D.theta)
    (h₂ : η₂.comp D.inclusion = D.theta)
    (hne : η₁ ≠ η₂) :
    η₂ =
      { toFun := fun g => D.quadraticCharacter g * η₁ g
        map_one' := by sorry
        map_mul' := by sorry } := by
  sorry

structure Chapter11QuadraticHeckeDescentData
    (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M] [IsGalois K M] where
  normData : Chapter11NormData K M
  actionData : Chapter11GaloisIdeleActionData K M
  theta : Chapter11HeckeCharacter M
  quadraticAutomorphism : Gal(M / K)
  invariant : chapter11ConjugateCharacter actionData theta
    quadraticAutomorphism = theta
  degree_two : Module.finrank K M = 2

theorem chapter11_quadratic_invariant_hecke_character_has_two_descents
    {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
    (D : Chapter11QuadraticHeckeDescentData K M) :
    ∃ η₁ η₂ : Chapter11HeckeCharacter K,
      chapter11NormPullback D.normData η₁ = D.theta ∧
      chapter11NormPullback D.normData η₂ = D.theta ∧ η₁ ≠ η₂ := by
  sorry

def chapter11FiniteConductorIdeal
    {K : Type*} [Field K] [NumberField K]
    (a : NumberField.FinitePlace K → ℕ) : Ideal (𝓞 K) :=
  ∏ᶠ v, v.maximalIdeal.asIdeal ^ a v

structure Chapter11QuadraticConductorData
    (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M] where
  inducedConductor : Ideal (𝓞 K)
  characterConductor : Ideal (𝓞 M)
  relativeDifferent : Ideal (𝓞 K)
  normedCharacterConductor : Ideal (𝓞 K)
  normedConductor_spec :
    normedCharacterConductor =
      Ideal.relNorm (𝓞 K) characterConductor
  conductor_formula :
    inducedConductor = relativeDifferent * normedCharacterConductor

theorem chapter11_quadratic_induced_conductor_formula
    {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M]
    (D : Chapter11QuadraticConductorData K M) :
    D.inducedConductor =
      D.relativeDifferent * Ideal.relNorm (𝓞 K) D.characterConductor := by
  sorry

structure Chapter11QuadraticLocalConductorData where
  placesAbove : Finset ℕ
  differentExponent : ℕ
  inducedExponent : ℕ
  characterExponent : ℕ → ℕ
  residueDegreeAt : ℕ → ℕ
  local_formula : inducedExponent =
    differentExponent +
      Finset.sum placesAbove (fun w => residueDegreeAt w * characterExponent w)

theorem chapter11_quadratic_local_induction_conductor_exponent
    (D : Chapter11QuadraticLocalConductorData) :
    D.inducedExponent = D.differentExponent +
      Finset.sum D.placesAbove (fun w => D.residueDegreeAt w * D.characterExponent w) := by
  exact D.local_formula

structure Chapter11QuadraticFrobeniusData (E : Type*) [Field E] where
  splitCharacterAtFirst : Eˣ
  splitCharacterAtSecond : Eˣ
  splitCharacteristicPolynomial : Polynomial E
  split_formula : splitCharacteristicPolynomial =
    (Polynomial.X - Polynomial.C (splitCharacterAtFirst : E)) *
      (Polynomial.X - Polynomial.C (splitCharacterAtSecond : E))
  inertCharacter : Eˣ
  inertTrace : E
  inertCharacteristicPolynomial : Polynomial E
  inert_trace_zero : inertTrace = 0
  inert_trace_formula : inertCharacteristicPolynomial =
    Polynomial.X ^ 2 - Polynomial.C (inertCharacter : E)

theorem chapter11_quadratic_split_frobenius_characteristic_polynomial
    {E : Type*} [Field E] (D : Chapter11QuadraticFrobeniusData E) :
    D.splitCharacteristicPolynomial =
      (Polynomial.X - Polynomial.C (D.splitCharacterAtFirst : E)) *
        (Polynomial.X - Polynomial.C (D.splitCharacterAtSecond : E)) := by
  exact D.split_formula

theorem chapter11_quadratic_inert_frobenius_trace_zero
    {E : Type*} [Field E] (D : Chapter11QuadraticFrobeniusData E) :
    D.inertTrace = 0 :=
  D.inert_trace_zero

theorem chapter11_quadratic_inert_frobenius_characteristic_polynomial
    {E : Type*} [Field E] (D : Chapter11QuadraticFrobeniusData E) :
    D.inertCharacteristicPolynomial =
      Polynomial.X ^ 2 - Polynomial.C (D.inertCharacter : E) := by
  exact D.inert_trace_formula

def chapter11RepresentationTwist
    {E G V : Type*} [Field E] [Group G] [AddCommGroup V] [Module E V]
    (ρ : Representation E G V) (η : G →* Eˣ) : Representation E G V := by
  refine
    { toFun := fun g => (η g : E) • ρ g
      map_one' := by sorry
      map_mul' := by sorry }

def chapter11QuadraticTwistedCharacter
    {E G H : Type*} [Field E] [Group G] [Fintype G] [Group H] [Fintype H]
    (D : Chapter11QuadraticInductionData E G H) (η : G →* Eˣ) : H →* Eˣ :=
  { toFun := fun h => D.theta h * η (D.inclusion h)
    map_one' := by sorry
    map_mul' := by sorry }

theorem chapter11_quadratic_induction_twist_identity
    {E G H : Type*} [Field E] [Group G] [Fintype G] [Group H] [Fintype H]
    (D : Chapter11QuadraticInductionData E G H) (η : G →* Eˣ) :
    Nonempty
      ((chapter11InducedRepresentation E G H D.inclusion
        (chapter11QuadraticTwistedCharacter D η)).Equiv
        (chapter11RepresentationTwist
          (chapter11QuadraticInducedRepresentation D) η)) := by
  sorry

structure Chapter11QuadraticDeterminantData
    (E G H : Type*) [Field E] [Group G] [Group H] where
  transfer : G →* H
  quadratic : G →* Eˣ

theorem chapter11_quadratic_induced_determinant_formula
    {E G H : Type*} [Field E] [Group G] [Fintype G] [Group H] [Fintype H]
    (D : Chapter11QuadraticInductionData E G H)
    (T : Chapter11QuadraticDeterminantData E G H) :
    chapter11RepresentationDeterminant
        (chapter11QuadraticInducedRepresentation D) =
      { toFun := fun g => T.quadratic g * D.theta (T.transfer g)
        map_one' := by sorry
        map_mul' := by sorry } := by
  sorry

end

end LastLib.Book06GlobalClassFieldTheory.Chapter11
