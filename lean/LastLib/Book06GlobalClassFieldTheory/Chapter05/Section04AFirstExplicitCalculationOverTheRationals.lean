import LastLib.Book06GlobalClassFieldTheory.Chapter05.Dependencies
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois

namespace LastLib.Book06GlobalClassFieldTheory.Chapter05

noncomputable section

/-! ## 5.4. A first explicit calculation over the rationals -/

open IsCyclotomicExtension

/-- The canonical Galois/action identification for `ℚ(ζₘ)`. -/
noncomputable def chapter05CyclotomicGaloisUnitsEquiv
    (m : ℕ) [NeZero m] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {m} ℚ K] :
    Gal(K / ℚ) ≃* (ZMod m)ˣ :=
  IsCyclotomicExtension.Rat.galEquivZMod m K

theorem chapter05_cyclotomic_galois_action_on_root
    (m : ℕ) [NeZero m] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {m} ℚ K] (σ : Gal(K / ℚ))
    {x : K} (hx : x ^ m = 1) :
    σ x = x ^ (chapter05CyclotomicGaloisUnitsEquiv m K σ).val.val := by
  exact IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq m K σ hx

/-- The unit representing the arithmetic Frobenius at a prime `p ∤ m`. -/
def chapter05CyclotomicFrobeniusUnit
    (m p : ℕ) [NeZero m] (hpm : Nat.Coprime p m) : (ZMod m)ˣ :=
  ZMod.unitOfCoprime p hpm

/-- The cyclotomic Frobenius action on a chosen primitive root. -/
theorem chapter05_cyclotomic_frobenius_action
    (m p : ℕ) [NeZero m] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {m} ℚ K] (hp : Nat.Prime p) (hpm : Nat.Coprime p m)
    (σ : Gal(K / ℚ))
    (hσ : chapter05CyclotomicGaloisUnitsEquiv m K σ =
      chapter05CyclotomicFrobeniusUnit m p hpm) :
    σ (IsCyclotomicExtension.zeta m ℚ K) =
      (IsCyclotomicExtension.zeta m ℚ K) ^ p := by
  sorry

/-- The Frobenius unit is trivial exactly in the split-completely congruence
class. -/
theorem chapter05_cyclotomic_frobenius_unit_eq_one_iff
    (m p : ℕ) [NeZero m] (hpm : Nat.Coprime p m) :
    chapter05CyclotomicFrobeniusUnit m p hpm = 1 ↔ Nat.ModEq m p 1 := by
  sorry

/-- At a prime away from the conductor, the cyclotomic ideal Frobenius is the
class of `p` modulo `m`. -/
def chapter05CyclotomicIdealFrobeniusClass
    (m p : ℕ) [NeZero m] (_hp : Nat.Prime p) (hpm : Nat.Coprime p m) : (ZMod m)ˣ :=
  chapter05CyclotomicFrobeniusUnit m p hpm

theorem chapter05_cyclotomic_split_completely_iff
    (m p : ℕ) [NeZero m] (hp : Nat.Prime p) (hpm : Nat.Coprime p m) :
    chapter05CyclotomicIdealFrobeniusClass m p hp hpm = 1 ↔
      Nat.ModEq m p 1 := by
  exact chapter05_cyclotomic_frobenius_unit_eq_one_iff m p hpm

/-- Ideal Frobenius is only defined in this finite-level model away from the
conductor. -/
def chapter05CyclotomicIdealFrobeniusDefined (m p : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Coprime p m

theorem chapter05_cyclotomic_ideal_frobenius_undefined_at_conductor
    {m p : ℕ} (hp : Nat.Prime p) (hpm : p ∣ m) :
    ¬ chapter05CyclotomicIdealFrobeniusDefined m p := by
  sorry

/-- The three explicit quadratic characters occurring at level `8`. -/
def chapter05QuadraticCharacterMinusOne : MulChar (ZMod 4) ℤ := ZMod.χ₄

def chapter05QuadraticCharacterMinusOneModEight : MulChar (ZMod 8) ℤ :=
  DirichletCharacter.changeLevel (R := ℤ) (by decide : 4 ∣ 8) ZMod.χ₄

def chapter05QuadraticCharacterTwo : MulChar (ZMod 8) ℤ := ZMod.χ₈

def chapter05QuadraticCharacterMinusTwo : MulChar (ZMod 8) ℤ := ZMod.χ₈'

theorem chapter05_quadratic_character_minus_one_is_quadratic :
    chapter05QuadraticCharacterMinusOne.IsQuadratic := by
  exact ZMod.isQuadratic_χ₄

theorem chapter05_quadratic_character_two_is_quadratic :
    chapter05QuadraticCharacterTwo.IsQuadratic := by
  exact ZMod.isQuadratic_χ₈

theorem chapter05_quadratic_character_minus_one_mod_eight_is_quadratic :
    chapter05QuadraticCharacterMinusOneModEight.IsQuadratic := by
  sorry

theorem chapter05_quadratic_character_minus_two_is_quadratic :
    chapter05QuadraticCharacterMinusTwo.IsQuadratic := by
  exact ZMod.isQuadratic_χ₈'

theorem chapter05_quadratic_character_minus_two_product_formula (a : ZMod 8) :
    chapter05QuadraticCharacterMinusTwo a =
      ZMod.χ₄ (ZMod.cast a) * chapter05QuadraticCharacterTwo a := by
  exact ZMod.χ₈'_eq_χ₄_mul_χ₈ a

/-- The fixed field attached to a multiplicative character through the
cyclotomic Galois equivalence. -/
noncomputable def chapter05CyclotomicCharacterFixedField
    (m : ℕ) [NeZero m] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {m} ℚ K] (χ : MulChar (ZMod m) ℤ) :
    IntermediateField ℚ K :=
  IntermediateField.fixedField
    ((χ.toUnitHom.ker).comap
      (chapter05CyclotomicGaloisUnitsEquiv m K).toMonoidHom)

def chapter05GaussianQuadraticField : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {Complex.I}

def chapter05PositiveTwoQuadraticField : IntermediateField ℚ ℝ :=
  IntermediateField.adjoin ℚ {Real.sqrt 2}

def chapter05NegativeTwoQuadraticField : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {Real.sqrt 2 * Complex.I}

local instance chapter05NeZeroRatEight : NeZero (8 : ℚ) :=
  ⟨(Nat.cast_ne_zero (R := ℚ)).mpr (by decide)⟩

local instance chapter05CyclotomicFieldRatEight :
    IsCyclotomicExtension {8} ℚ (CyclotomicField 8 ℚ) :=
  CyclotomicField.isCyclotomicExtension 8 ℚ

/-- The three nontrivial quadratic characters of `(ℤ/8ℤ)ˣ` cut out the three
quadratic fields listed in the text, up to the canonical `ℚ`-algebra
identifications of the corresponding fixed fields. -/
theorem chapter05_mod_eight_quadratic_fields
    : Nonempty
        (chapter05CyclotomicCharacterFixedField 8
            (CyclotomicField 8 ℚ) chapter05QuadraticCharacterMinusOneModEight ≃ₐ[ℚ]
          chapter05GaussianQuadraticField) ∧
      Nonempty
        (chapter05CyclotomicCharacterFixedField 8
            (CyclotomicField 8 ℚ) chapter05QuadraticCharacterTwo ≃ₐ[ℚ]
          chapter05PositiveTwoQuadraticField) ∧
      Nonempty
        (chapter05CyclotomicCharacterFixedField 8
            (CyclotomicField 8 ℚ) chapter05QuadraticCharacterMinusTwo ≃ₐ[ℚ]
          chapter05NegativeTwoQuadraticField) := by
  sorry

end

end LastLib.Book06GlobalClassFieldTheory.Chapter05
