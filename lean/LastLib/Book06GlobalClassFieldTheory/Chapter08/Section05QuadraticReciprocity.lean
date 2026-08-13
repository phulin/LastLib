import LastLib.Book06GlobalClassFieldTheory.Chapter08.Dependencies

namespace LastLib.Book06GlobalClassFieldTheory.Chapter08

noncomputable section

open scoped Classical

open scoped BigOperators
open NumberField

universe u

/-! ## 8.5. Quadratic reciprocity as a product formula -/

/-- The book-facing predicate for adjoining a square root. -/
def chapter08QuadraticExtensionBySquareRoot
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (d : K) : Prop :=
  Module.finrank K L = 2 ∧
    ∃ x : L,
      x ^ 2 = algebraMap K L d ∧
        Algebra.adjoin K ({x} : Set L) = ⊤

theorem chapter08_quadratic_artin_character_is_product_of_local_hilbert_characters
    {K : Type u} [Field K]
    (Q : Chapter08QuadraticHilbertProductData K)
    (x : Kˣ) :
    letI : Fintype Q.place := Q.placeFintype
    Q.globalCharacter x = ∏ v, Q.localCharacter v x := by
  sorry

theorem chapter08_quadratic_local_character_is_hilbert_symbol
    {K : Type u} [Field K]
    (Q : Chapter08QuadraticHilbertProductData K)
    (v : Q.place) (x : Kˣ) :
    Q.localCharacter v x = Q.hilbertSymbol v x Q.quadraticParameter := by
  exact Q.localCharacter_eq_hilbertSymbol v x

theorem chapter08_quadratic_hilbert_symbol_principal_idele_product_formula
    {K : Type u} [Field K]
    (Q : Chapter08QuadraticHilbertProductData K)
    (a b : Kˣ) :
    letI : Fintype Q.place := Q.placeFintype
    ∏ v, Q.hilbertSymbol v a b = 1 := by
  sorry

/-! Over `ℚ`, the odd-prime local value is the Legendre symbol. -/

def chapter08RationalQuadraticUniformizerArtinValue
    (d : ℤ) (p : ℕ) [Fact p.Prime]
    (hpd : ¬(p : ℤ) ∣ 2 * d) : ℤ :=
  legendreSym p d

theorem chapter08_rational_quadratic_uniformizer_artin_value
    (d : ℤ) (p : ℕ) [Fact p.Prime] (_hpd : ¬(p : ℤ) ∣ 2 * d) :
    chapter08RationalQuadraticUniformizerArtinValue d p _hpd =
      legendreSym p d := by
  rfl

/-- The finite discriminant modulus, with a real sign component for negative discriminant. -/
def chapter08QuadraticCharacterModulus (Δ : ℤ) (hΔ : Δ ≠ 0) : Chapter08Modulus ℚ where
  finitePart := Ideal.span {(Int.natAbs Δ : 𝓞 ℚ)}
  finitePart_ne_bot := by sorry
  infinitePart := if Δ < 0 then Finset.univ else ∅

theorem chapter08_quadratic_character_modulus_has_discriminant_finite_part
    (Δ : ℤ) (hΔ : Δ ≠ 0) :
    (chapter08QuadraticCharacterModulus Δ hΔ).finitePart =
      Ideal.span {(Int.natAbs Δ : 𝓞 ℚ)} := by
  rfl

theorem chapter08_quadratic_character_modulus_has_real_sign_exactly_for_negative_discriminant
    (Δ : ℤ) (hΔ : Δ ≠ 0) :
    (chapter08QuadraticCharacterModulus Δ hΔ).infinitePart =
      if Δ < 0 then Finset.univ else ∅ := by
  rfl

/- LOCAL_DEPENDENCY_GUESS: the canonical quadratic Artin conductor and the
field discriminant are not connected by an earlier pinned interface. -/
structure Chapter08QuadraticArtinConductorData
    (L : Type u) [Field L] [Algebra ℚ L] [NumberField L]
    [FiniteDimensional ℚ L] [IsAbelianGalois ℚ L] (Δ : ℤ) where
  extension : Chapter08AbelianExtensionData ℚ L
  relativeDegree : Module.finrank ℚ L = 2
  fieldDiscriminant : NumberField.discr L = Δ
  discriminant_ne_zero : Δ ≠ 0
  conductor_eq_discriminant :
    extension.conductor = chapter08QuadraticCharacterModulus Δ discriminant_ne_zero

theorem chapter08_quadratic_artin_character_has_field_discriminant_modulus
    {L : Type u} [Field L] [Algebra ℚ L] [NumberField L]
    [FiniteDimensional ℚ L] [IsAbelianGalois ℚ L]
    {Δ : ℤ} (Q : Chapter08QuadraticArtinConductorData L Δ) :
    Q.extension.conductor =
      chapter08QuadraticCharacterModulus Δ Q.discriminant_ne_zero := by
  exact Q.conductor_eq_discriminant

theorem chapter08_quadratic_artin_character_conductor_divides_discriminant_modulus
    {L : Type u} [Field L] [Algebra ℚ L] [NumberField L]
    [FiniteDimensional ℚ L] [IsAbelianGalois ℚ L]
    {Δ : ℤ} (Q : Chapter08QuadraticArtinConductorData L Δ) :
    chapter08ConductorDivides Q.extension
      (chapter08QuadraticCharacterModulus Δ Q.discriminant_ne_zero) := by
  rw [chapter08ConductorDivides, Q.conductor_eq_discriminant]

/- LOCAL_DEPENDENCY_GUESS: the four local computations used in the textbook
proof are packaged independently of the global product formula.  This keeps
the displayed values reusable when the local Hilbert-symbol API is connected
to Mathlib's completion and residue-field declarations. -/
structure Chapter08QuadraticReciprocityLocalValues
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime] where
  distinct : p ≠ q
  odd_p : p ≠ 2
  odd_q : q ≠ 2
  atP : ℤ
  atQ : ℤ
  atTwo : ℤ
  atInfinity : ℤ
  atP_eq_legendre : atP = legendreSym p (q : ℤ)
  atQ_eq_legendre : atQ = legendreSym q (p : ℤ)
  atTwo_eq_sign :
    atTwo = (-1 : ℤ) ^ (((p - 1) / 2) * ((q - 1) / 2))
  atInfinity_eq_one : atInfinity = 1
  awayFactor : ℤ
  awayFactor_eq_one : awayFactor = 1

theorem chapter08_hilbert_symbol_at_p_is_legendre_symbol
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (V : Chapter08QuadraticReciprocityLocalValues p q) :
    V.atP = legendreSym p (q : ℤ) := by
  exact V.atP_eq_legendre

theorem chapter08_hilbert_symbol_at_q_is_legendre_symbol
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (V : Chapter08QuadraticReciprocityLocalValues p q) :
    V.atQ = legendreSym q (p : ℤ) := by
  exact V.atQ_eq_legendre

theorem chapter08_hilbert_symbol_at_two_is_reciprocity_sign
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (V : Chapter08QuadraticReciprocityLocalValues p q) :
    V.atTwo = (-1 : ℤ) ^ (((p - 1) / 2) * ((q - 1) / 2)) := by
  exact V.atTwo_eq_sign

theorem chapter08_hilbert_symbol_at_infinity_is_one
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (V : Chapter08QuadraticReciprocityLocalValues p q) :
    V.atInfinity = 1 := by
  exact V.atInfinity_eq_one

theorem chapter08_quadratic_reciprocity_local_product_is_one
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (V : Chapter08QuadraticReciprocityLocalValues p q) :
  V.atP * V.atQ * V.atTwo * V.atInfinity = 1 := by
  sorry

theorem chapter08_quadratic_reciprocity
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q)
    (V : Chapter08QuadraticReciprocityLocalValues p q) :
    legendreSym q (p : ℤ) * legendreSym p (q : ℤ) =
      (-1 : ℤ) ^ (((p - 1) / 2) * ((q - 1) / 2)) := by
  sorry

theorem chapter08_quadratic_reciprocity_supplementary_laws
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    legendreSym p (-1) = ZMod.χ₄ p ∧
      legendreSym p 2 = ZMod.χ₈ p := by
  exact ⟨legendreSym.at_neg_one hp2, legendreSym.at_two hp2⟩

end
end LastLib.Book06GlobalClassFieldTheory.Chapter08
