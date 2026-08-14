import LastLib.Book06GlobalClassFieldTheory.Chapter05.Dependencies
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.RootsOfUnity.Complex

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

/-- The unique cyclotomic Galois element corresponding to the arithmetic
Frobenius class of a prime `p ∤ m`. -/
noncomputable def chapter05CyclotomicFrobenius
    (m p : ℕ) [NeZero m] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {m} ℚ K] (_hp : Nat.Prime p)
    (hpm : Nat.Coprime p m) : Gal(K / ℚ) :=
  (chapter05CyclotomicGaloisUnitsEquiv m K).symm
    (chapter05CyclotomicFrobeniusUnit m p hpm)

/-- The cyclotomic Frobenius action on a chosen primitive root. -/
theorem chapter05_cyclotomic_frobenius_action
    (m p : ℕ) [NeZero m] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {m} ℚ K] (hp : Nat.Prime p) (hpm : Nat.Coprime p m)
    (σ : Gal(K / ℚ))
    (hσ : chapter05CyclotomicGaloisUnitsEquiv m K σ =
      chapter05CyclotomicFrobeniusUnit m p hpm) :
    σ (IsCyclotomicExtension.zeta m ℚ K) =
      (IsCyclotomicExtension.zeta m ℚ K) ^ p := by
  by_cases hp0 : p = 0
  · exact (hp.ne_zero hp0).elim
  · rw [chapter05_cyclotomic_galois_action_on_root m K σ
        (IsCyclotomicExtension.zeta_spec m ℚ K).pow_eq_one, hσ]
    apply (IsOfFinOrder.pow_eq_pow_iff_modEq
      ((IsCyclotomicExtension.zeta_spec m ℚ K).isOfFinOrder (NeZero.ne m))).mpr
    rw [← (IsCyclotomicExtension.zeta_spec m ℚ K).eq_orderOf,
      ← ZMod.natCast_eq_natCast_iff]
    change (((ZMod.unitOfCoprime p hpm : ZMod m).val : ℕ) : ZMod m) = (p : ZMod m)
    rw [ZMod.natCast_zmod_val, ZMod.coe_unitOfCoprime]

/-- The canonical cyclotomic Frobenius acts on the chosen root by `p`-th
power, with the arithmetic normalization. -/
theorem chapter05_cyclotomic_frobenius_action_canonical
    (m p : ℕ) [NeZero m] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {m} ℚ K] (hp : Nat.Prime p)
    (hpm : Nat.Coprime p m) :
    chapter05CyclotomicFrobenius m p K hp hpm
        (IsCyclotomicExtension.zeta m ℚ K) =
      (IsCyclotomicExtension.zeta m ℚ K) ^ p := by
  apply chapter05_cyclotomic_frobenius_action m p K hp hpm
    (chapter05CyclotomicFrobenius m p K hp hpm)
  exact (chapter05CyclotomicGaloisUnitsEquiv m K).apply_symm_apply _

/-- The Frobenius unit is trivial exactly in the split-completely congruence
class. -/
theorem chapter05_cyclotomic_frobenius_unit_eq_one_iff
    (m p : ℕ) [NeZero m] (hpm : Nat.Coprime p m) :
    chapter05CyclotomicFrobeniusUnit m p hpm = 1 ↔ Nat.ModEq m p 1 := by
  change ZMod.unitOfCoprime p hpm = 1 ↔ Nat.ModEq m p 1
  constructor
  · intro h
    have hcoe : (ZMod.unitOfCoprime p hpm : ZMod m) = (1 : ZMod m) := by
      exact congrArg (fun u : (ZMod m)ˣ => (u : ZMod m)) h
    rw [ZMod.coe_unitOfCoprime] at hcoe
    apply (ZMod.natCast_eq_natCast_iff p 1 m).mp
    simpa using hcoe
  · intro h
    apply Units.ext
    rw [ZMod.coe_unitOfCoprime]
    simpa using (ZMod.natCast_eq_natCast_iff p 1 m).mpr h

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
chosen modulus. -/
def chapter05CyclotomicIdealFrobeniusDefined (m p : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Coprime p m

theorem chapter05_cyclotomic_ideal_frobenius_undefined_at_conductor
    {m p : ℕ} (hp : Nat.Prime p) (hpm : p ∣ m) :
    ¬ chapter05CyclotomicIdealFrobeniusDefined m p := by
  intro h
  exact (hp.coprime_iff_not_dvd.mp h.2) hpm

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
  intro a
  by_cases ha : IsUnit a
  · rw [show a = (ha.unit : ZMod 8) from (IsUnit.unit_spec ha).symm]
    change (DirichletCharacter.changeLevel (R := ℤ) (by decide : 4 ∣ 8) ZMod.χ₄)
        (ha.unit : ZMod 8) = 0 ∨
      (DirichletCharacter.changeLevel (R := ℤ) (by decide : 4 ∣ 8) ZMod.χ₄)
          (ha.unit : ZMod 8) = 1 ∨
      (DirichletCharacter.changeLevel (R := ℤ) (by decide : 4 ∣ 8) ZMod.χ₄)
          (ha.unit : ZMod 8) = -1
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd
      (χ := ZMod.χ₄) (by decide : 4 ∣ 8) ha.unit]
    exact ZMod.isQuadratic_χ₄ _
  · exact Or.inl (MulChar.map_nonunit _ ha)

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

private theorem chapter05_quadratic_character_two_toUnitHom_range :
    chapter05QuadraticCharacterTwo.toUnitHom.range = ⊤ := by
  apply eq_top_iff.mpr
  intro x hx
  rcases Int.units_eq_one_or x with rfl | rfl
  · exact ⟨1, by simp⟩
  · refine ⟨ZMod.unitOfCoprime 3 (by decide), ?_⟩
    apply Units.ext
    decide

private theorem chapter05_quadratic_character_ker_card
    (χ : MulChar (ZMod 8) ℤ) (hrange : χ.toUnitHom.range = ⊤) :
    Nat.card χ.toUnitHom.ker = 2 := by
  have hcard : Nat.card (ZMod 8)ˣ = 4 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    decide
  have hindex : χ.toUnitHom.ker.index = 2 := by
    rw [Subgroup.index_ker, hrange,
      Subgroup.card_top]
    rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
  have hmul := χ.toUnitHom.ker.card_mul_index
  rw [hindex, hcard] at hmul
  omega

private theorem chapter05_quadratic_character_minus_one_mod_eight_toUnitHom_range :
    chapter05QuadraticCharacterMinusOneModEight.toUnitHom.range = ⊤ := by
  apply eq_top_iff.mpr
  intro x hx
  rcases Int.units_eq_one_or x with rfl | rfl
  · exact ⟨1, by simp⟩
  · refine ⟨ZMod.unitOfCoprime 3 (by decide), ?_⟩
    apply Units.ext
    change (DirichletCharacter.changeLevel (R := ℤ) (by decide : 4 ∣ 8) ZMod.χ₄)
        (ZMod.unitOfCoprime 3 (by decide : Nat.Coprime 3 8) : ZMod 8) = (-1 : ℤ)
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd
      (χ := ZMod.χ₄) (by decide : 4 ∣ 8)]
    decide

private theorem chapter05_quadratic_character_minus_two_toUnitHom_range :
    chapter05QuadraticCharacterMinusTwo.toUnitHom.range = ⊤ := by
  apply eq_top_iff.mpr
  intro x hx
  rcases Int.units_eq_one_or x with rfl | rfl
  · exact ⟨1, by simp⟩
  · refine ⟨ZMod.unitOfCoprime 5 (by decide), ?_⟩
    apply Units.ext
    decide

private theorem chapter05_quadratic_character_two_ker_eq_zpowers :
    chapter05QuadraticCharacterTwo.toUnitHom.ker =
      Subgroup.zpowers (-1 : (ZMod 8)ˣ) := by
  have horder : orderOf (-1 : (ZMod 8)ˣ) = 2 := by
    apply orderOf_eq_prime (p := 2)
    · simp
    · intro h
      have hval : (-1 : ZMod 8) = 1 :=
        congrArg (fun u : (ZMod 8)ˣ => (u : ZMod 8)) h
      exact (by decide : (-1 : ZMod 8) ≠ 1) hval
  symm
  apply Subgroup.eq_of_le_of_card_ge (H := Subgroup.zpowers (-1 : (ZMod 8)ˣ))
    (K := chapter05QuadraticCharacterTwo.toUnitHom.ker)
  · apply Subgroup.zpowers_le_of_mem
    apply MonoidHom.mem_ker.mpr
    apply Units.ext
    decide
  · rw [chapter05_quadratic_character_ker_card chapter05QuadraticCharacterTwo
      chapter05_quadratic_character_two_toUnitHom_range]
    rw [Nat.card_zpowers, horder]

private theorem chapter05_quadratic_character_minus_one_mod_eight_ker_eq_zpowers :
    chapter05QuadraticCharacterMinusOneModEight.toUnitHom.ker =
      Subgroup.zpowers (ZMod.unitOfCoprime 5 (by decide : Nat.Coprime 5 8)) := by
  let u : (ZMod 8)ˣ := ZMod.unitOfCoprime 5 (by decide : Nat.Coprime 5 8)
  have horder : orderOf u = 2 := by
    apply orderOf_eq_prime (p := 2)
    · apply Units.ext
      decide
    · intro h
      have hval : (5 : ZMod 8) = 1 :=
        congrArg (fun v : (ZMod 8)ˣ => (v : ZMod 8)) h
      exact (by decide : (5 : ZMod 8) ≠ 1) hval
  change chapter05QuadraticCharacterMinusOneModEight.toUnitHom.ker =
    Subgroup.zpowers u
  symm
  apply Subgroup.eq_of_le_of_card_ge (H := Subgroup.zpowers u)
    (K := chapter05QuadraticCharacterMinusOneModEight.toUnitHom.ker)
  · apply Subgroup.zpowers_le_of_mem
    apply MonoidHom.mem_ker.mpr
    apply Units.ext
    change (DirichletCharacter.changeLevel (R := ℤ) (by decide : 4 ∣ 8) ZMod.χ₄)
        (ZMod.unitOfCoprime 5 (by decide : Nat.Coprime 5 8) : ZMod 8) = (1 : ℤ)
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd
      (χ := ZMod.χ₄) (by decide : 4 ∣ 8)]
    decide
  · rw [chapter05_quadratic_character_ker_card
      chapter05QuadraticCharacterMinusOneModEight
      chapter05_quadratic_character_minus_one_mod_eight_toUnitHom_range]
    rw [Nat.card_zpowers, horder]

private theorem chapter05_quadratic_character_minus_two_ker_eq_zpowers :
    chapter05QuadraticCharacterMinusTwo.toUnitHom.ker =
      Subgroup.zpowers (ZMod.unitOfCoprime 3 (by decide : Nat.Coprime 3 8)) := by
  let u : (ZMod 8)ˣ := ZMod.unitOfCoprime 3 (by decide : Nat.Coprime 3 8)
  have horder : orderOf u = 2 := by
    apply orderOf_eq_prime (p := 2)
    · apply Units.ext
      decide
    · intro h
      have hval : (3 : ZMod 8) = 1 :=
        congrArg (fun v : (ZMod 8)ˣ => (v : ZMod 8)) h
      exact (by decide : (3 : ZMod 8) ≠ 1) hval
  change chapter05QuadraticCharacterMinusTwo.toUnitHom.ker =
    Subgroup.zpowers u
  symm
  apply Subgroup.eq_of_le_of_card_ge (H := Subgroup.zpowers u)
    (K := chapter05QuadraticCharacterMinusTwo.toUnitHom.ker)
  · apply Subgroup.zpowers_le_of_mem
    apply MonoidHom.mem_ker.mpr
    apply Units.ext
    decide
  · rw [chapter05_quadratic_character_ker_card chapter05QuadraticCharacterMinusTwo
      chapter05_quadratic_character_minus_two_toUnitHom_range]
    rw [Nat.card_zpowers, horder]

private theorem chapter05_zpowers_element_fixes_generator
    (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {8} ℚ K] (g : (ZMod 8)ˣ) (x : K)
    (hgen : (chapter05CyclotomicGaloisUnitsEquiv 8 K).symm g x = x)
    {u : (ZMod 8)ˣ} (hu : u ∈ Subgroup.zpowers g) :
    (chapter05CyclotomicGaloisUnitsEquiv 8 K).symm u x = x := by
  let F : IntermediateField ℚ K := IntermediateField.adjoin ℚ {x}
  have hgenF : (chapter05CyclotomicGaloisUnitsEquiv 8 K).symm g ∈
      F.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    change y ∈ IntermediateField.adjoin ℚ {x} at hy
    change (chapter05CyclotomicGaloisUnitsEquiv 8 K).symm g y = y
    induction hy using IntermediateField.adjoin_induction with
    | mem y hy =>
        rw [Set.mem_singleton_iff] at hy
        subst y
        exact hgen
    | algebraMap q =>
        exact (chapter05CyclotomicGaloisUnitsEquiv 8 K).symm g |>.commutes q
    | add y z hy hz hhy hhz =>
        rw [map_add, hhy, hhz]
    | inv y hy hhy =>
        rw [map_inv₀, hhy]
    | mul y z hy hz hhy hhz =>
        rw [map_mul, hhy, hhz]
  have huF : (chapter05CyclotomicGaloisUnitsEquiv 8 K).symm u ∈ F.fixingSubgroup := by
    have hu' : (chapter05CyclotomicGaloisUnitsEquiv 8 K).symm u ∈
        (Subgroup.zpowers g).map
          (chapter05CyclotomicGaloisUnitsEquiv 8 K).symm.toMonoidHom :=
      Subgroup.mem_map_of_mem _ hu
    rw [MonoidHom.map_zpowers] at hu'
    exact (Subgroup.zpowers_le_of_mem hgenF) hu'
  rw [IntermediateField.mem_fixingSubgroup_iff] at huF
  exact huF x
    (IntermediateField.subset_adjoin ℚ {x} (Set.mem_singleton x))

private theorem chapter05_adjoin_le_character_fixedField
    (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {8} ℚ K] (χ : MulChar (ZMod 8) ℤ) (x : K)
    (hfix : ∀ u : (ZMod 8)ˣ, u ∈ χ.toUnitHom.ker →
      (chapter05CyclotomicGaloisUnitsEquiv 8 K).symm u x = x) :
    IntermediateField.adjoin ℚ {x} ≤
      chapter05CyclotomicCharacterFixedField 8 K χ := by
  apply IntermediateField.adjoin_le_iff.mpr
  intro y hy
  have hyx : y = x := Set.mem_singleton_iff.mp hy
  subst y
  unfold chapter05CyclotomicCharacterFixedField
  change x ∈ IntermediateField.fixedField
    ((χ.toUnitHom.ker).comap (chapter05CyclotomicGaloisUnitsEquiv 8 K).toMonoidHom)
  rw [IntermediateField.mem_fixedField_iff]
  intro σ hσ
  change chapter05CyclotomicGaloisUnitsEquiv 8 K σ ∈ χ.toUnitHom.ker at hσ
  simpa using hfix (chapter05CyclotomicGaloisUnitsEquiv 8 K σ) hσ

private theorem chapter05_character_comap_card
    (χ : MulChar (ZMod 8) ℤ) :
    Nat.card
        ((χ.toUnitHom.ker).comap
          (chapter05CyclotomicGaloisUnitsEquiv 8 (CyclotomicField 8 ℚ)).toMonoidHom) =
      Nat.card χ.toUnitHom.ker := by
  let e := chapter05CyclotomicGaloisUnitsEquiv 8 (CyclotomicField 8 ℚ)
  have hmap :
      ((χ.toUnitHom.ker).comap e.toMonoidHom).map e.toMonoidHom =
        χ.toUnitHom.ker := by
    exact Subgroup.map_comap_eq_self_of_surjective e.surjective _
  calc
    Nat.card ((χ.toUnitHom.ker).comap e.toMonoidHom) =
        Nat.card (((χ.toUnitHom.ker).comap e.toMonoidHom).map e.toMonoidHom) := by
      exact Nat.card_congr
        (Subgroup.equivMapOfInjective _ _ e.injective).toEquiv
    _ = Nat.card χ.toUnitHom.ker := by rw [hmap]

private theorem chapter05_character_fixedField_eq_adjoin
    (χ : MulChar (ZMod 8) ℤ) (x : CyclotomicField 8 ℚ)
    (hx : IsIntegral ℚ x) (hmin : (minpoly ℚ x).natDegree = 2)
    (hcard : Nat.card χ.toUnitHom.ker = 2)
    (hfix : ∀ u : (ZMod 8)ˣ, u ∈ χ.toUnitHom.ker →
      (chapter05CyclotomicGaloisUnitsEquiv 8 (CyclotomicField 8 ℚ)).symm u x = x) :
    chapter05CyclotomicCharacterFixedField 8 (CyclotomicField 8 ℚ) χ =
      IntermediateField.adjoin ℚ {x} := by
  have hle : IntermediateField.adjoin ℚ {x} ≤
      chapter05CyclotomicCharacterFixedField 8 (CyclotomicField 8 ℚ) χ :=
    chapter05_adjoin_le_character_fixedField (CyclotomicField 8 ℚ) χ x hfix
  have h_adjoin : Module.finrank ℚ (IntermediateField.adjoin ℚ {x}) = 2 := by
    rw [IntermediateField.adjoin.finrank hx, hmin]
  have htotal := Module.finrank_mul_finrank ℚ
    (IntermediateField.adjoin ℚ {x}) (CyclotomicField 8 ℚ)
  rw [h_adjoin, IsCyclotomicExtension.Rat.finrank 8] at htotal
  have htotient : Nat.totient 8 = 4 := by decide
  rw [htotient] at htotal
  have h_adjoin_top : Module.finrank (IntermediateField.adjoin ℚ {x})
      (CyclotomicField 8 ℚ) = 2 := by
    omega
  have h_fixed : Module.finrank
      (chapter05CyclotomicCharacterFixedField 8 (CyclotomicField 8 ℚ) χ)
      (CyclotomicField 8 ℚ) = 2 := by
    rw [chapter05CyclotomicCharacterFixedField,
      IntermediateField.finrank_fixedField_eq_card,
      chapter05_character_comap_card, hcard]
  exact (IntermediateField.eq_of_le_of_finrank_eq' hle
    (h_adjoin_top.trans h_fixed.symm)).symm

private theorem chapter05_real_sqrt_two_root :
    Polynomial.aeval (Real.sqrt 2)
      ((Polynomial.X : Polynomial ℚ) ^ 2 - Polynomial.C (2 : ℚ)) = 0 := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C]
  norm_num [Real.sq_sqrt]

private theorem chapter05_real_sqrt_two_integral :
    IsIntegral ℚ (Real.sqrt 2) := by
  refine ⟨(Polynomial.X : Polynomial ℚ) ^ 2 - Polynomial.C (2 : ℚ),
    Polynomial.monic_X_pow_sub_C 2 (by decide), ?_⟩
  exact chapter05_real_sqrt_two_root

private theorem chapter05_irreducible_x_pow_two_sub_two :
    Irreducible ((Polynomial.X : Polynomial ℚ) ^ 2 - Polynomial.C (2 : ℚ)) := by
  apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
  intro q hq
  have hq' : ((q : ℝ) ^ 2) = 2 := by
    exact_mod_cast hq
  have hs : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by
    rw [Real.sq_sqrt]
    norm_num
  exact irrational_sqrt_two <| by
    by_cases hqnonneg : (0 : ℝ) ≤ q
    · refine ⟨q, ?_⟩
      nlinarith [Real.sqrt_nonneg 2]
    · refine ⟨-q, ?_⟩
      have hqnonpos : (q : ℝ) ≤ 0 := le_of_not_ge hqnonneg
      rw [Rat.cast_neg]
      nlinarith [Real.sqrt_nonneg 2]

private theorem chapter05_minpoly_real_sqrt_two :
    minpoly ℚ (Real.sqrt 2) =
      (Polynomial.X : Polynomial ℚ) ^ 2 - Polynomial.C (2 : ℚ) := by
  apply (minpoly.eq_of_irreducible_of_monic
    chapter05_irreducible_x_pow_two_sub_two ?_
    (Polynomial.monic_X_pow_sub_C 2 (by decide))).symm
  exact chapter05_real_sqrt_two_root

private theorem chapter05_complex_sqrt_two_mul_I_root :
    Polynomial.aeval (Real.sqrt 2 * Complex.I)
      ((Polynomial.X : Polynomial ℚ) ^ 2 - Polynomial.C (-2 : ℚ)) = 0 := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C]
  ring_nf
  have hs : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by
    rw [Real.sq_sqrt]
    norm_num
  have hsC : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast hs
  rw [hsC]
  norm_num

private theorem chapter05_complex_sqrt_two_mul_I_integral :
    IsIntegral ℚ (Real.sqrt 2 * Complex.I) := by
  refine ⟨(Polynomial.X : Polynomial ℚ) ^ 2 - Polynomial.C (-2 : ℚ),
    Polynomial.monic_X_pow_sub_C (-2 : ℚ) (by decide), ?_⟩
  exact chapter05_complex_sqrt_two_mul_I_root

private theorem chapter05_irreducible_x_pow_two_sub_neg_two :
    Irreducible ((Polynomial.X : Polynomial ℚ) ^ 2 - Polynomial.C (-2 : ℚ)) := by
  apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
  intro q hq
  nlinarith [sq_nonneg q]

private theorem chapter05_minpoly_complex_sqrt_two_mul_I :
    minpoly ℚ (Real.sqrt 2 * Complex.I) =
      (Polynomial.X : Polynomial ℚ) ^ 2 - Polynomial.C (-2 : ℚ) := by
  apply (minpoly.eq_of_irreducible_of_monic
    chapter05_irreducible_x_pow_two_sub_neg_two ?_
    (Polynomial.monic_X_pow_sub_C (-2 : ℚ) (by decide))).symm
  exact chapter05_complex_sqrt_two_mul_I_root

private theorem chapter05_cyclotomic_unit_action_on_zeta
    (u : (ZMod 8)ˣ) :
    (chapter05CyclotomicGaloisUnitsEquiv 8 (CyclotomicField 8 ℚ)).symm u
        (IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ)) =
      (IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ)) ^ u.val.val := by
  rw [chapter05_cyclotomic_galois_action_on_root 8 (CyclotomicField 8 ℚ)
      _ (IsCyclotomicExtension.zeta_spec 8 ℚ (CyclotomicField 8 ℚ)).pow_eq_one,
    (chapter05CyclotomicGaloisUnitsEquiv 8 (CyclotomicField 8 ℚ)).apply_symm_apply]

private theorem chapter05_gaussian_generator_fixed_by_five :
    (chapter05CyclotomicGaloisUnitsEquiv 8 (CyclotomicField 8 ℚ)).symm
        (ZMod.unitOfCoprime 5 (by decide : Nat.Coprime 5 8))
        ((IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ)) ^ 2) =
      (IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ)) ^ 2 := by
  let z : CyclotomicField 8 ℚ :=
    IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ)
  let u : (ZMod 8)ˣ := ZMod.unitOfCoprime 5 (by decide : Nat.Coprime 5 8)
  rw [map_pow, chapter05_cyclotomic_unit_action_on_zeta u]
  change (z ^ 5) ^ 2 = z ^ 2
  rw [← pow_mul]
  have hz8 : z ^ 8 = 1 := (IsCyclotomicExtension.zeta_spec 8 ℚ _).pow_eq_one
  calc
    z ^ (5 * 2) = z ^ (8 + 2) := by norm_num
    _ = z ^ 8 * z ^ 2 := by rw [pow_add]
    _ = z ^ 2 := by rw [hz8, one_mul]

private theorem chapter05_cyclotomic_zeta_pow_four_eq_neg_one :
    (IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ)) ^ 4 = -1 := by
  let z : CyclotomicField 8 ℚ :=
    IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ)
  have hz : IsPrimitiveRoot z 8 := IsCyclotomicExtension.zeta_spec 8 ℚ _
  have hz8 : z ^ 8 = 1 := hz.pow_eq_one
  have hz4ne : z ^ 4 ≠ 1 := by
    intro h
    exact (by decide : ¬(8 : ℕ) ∣ 4) ((hz.pow_eq_one_iff_dvd 4).mp h)
  have hsq : (z ^ 4) ^ 2 = 1 := by
    rw [← pow_mul, show 4 * 2 = 8 by decide, hz8]
  have hfac : (z ^ 4 - 1) * (z ^ 4 + 1) = 0 := by
    calc
      (z ^ 4 - 1) * (z ^ 4 + 1) = (z ^ 4) ^ 2 - 1 := by ring
      _ = 0 := by rw [hsq, sub_self]
  rcases mul_eq_zero.mp hfac with h | h
  · exact (hz4ne (sub_eq_zero.mp h)).elim
  · exact eq_neg_of_add_eq_zero_left h

private theorem chapter05_positive_two_generator_root :
    Polynomial.aeval
        (IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ) +
          (IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ))⁻¹)
        ((Polynomial.X : Polynomial ℚ) ^ 2 - Polynomial.C (2 : ℚ)) = 0 := by
  let z : CyclotomicField 8 ℚ :=
    IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ)
  have hz4 : z ^ 4 = -1 := by
    simpa [z] using chapter05_cyclotomic_zeta_pow_four_eq_neg_one
  have hz : IsPrimitiveRoot z 8 := IsCyclotomicExtension.zeta_spec 8 ℚ _
  have hzne : z ≠ 0 := hz.ne_zero (by decide)
  change Polynomial.aeval (z + z⁻¹)
      ((Polynomial.X : Polynomial ℚ) ^ 2 - Polynomial.C (2 : ℚ)) = 0
  rw [Polynomial.aeval_def, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C]
  field_simp [hzne]
  ring_nf
  rw [hz4]
  norm_num

private theorem chapter05_negative_two_generator_root :
    Polynomial.aeval
        (IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ) -
          (IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ))⁻¹)
        ((Polynomial.X : Polynomial ℚ) ^ 2 - Polynomial.C (-2 : ℚ)) = 0 := by
  let z : CyclotomicField 8 ℚ :=
    IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ)
  have hz4 : z ^ 4 = -1 := by
    simpa [z] using chapter05_cyclotomic_zeta_pow_four_eq_neg_one
  have hz : IsPrimitiveRoot z 8 := IsCyclotomicExtension.zeta_spec 8 ℚ _
  have hzne : z ≠ 0 := hz.ne_zero (by decide)
  change Polynomial.aeval (z - z⁻¹)
      ((Polynomial.X : Polynomial ℚ) ^ 2 - Polynomial.C (-2 : ℚ)) = 0
  rw [Polynomial.aeval_def, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C]
  field_simp [hzne]
  ring_nf
  rw [hz4]
  norm_num

private theorem chapter05_gaussian_generator_minpoly :
    minpoly ℚ (IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ) ^ 2) =
      minpoly ℚ Complex.I := by
  have hz4 : IsPrimitiveRoot
      (IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ) ^ 2) 4 :=
    (IsCyclotomicExtension.zeta_spec 8 ℚ (CyclotomicField 8 ℚ)).pow_of_dvd
      (by decide) (by decide)
  exact (Polynomial.cyclotomic_eq_minpoly_rat hz4 (by decide)).symm.trans
    (Polynomial.cyclotomic_eq_minpoly_rat Complex.isPrimitiveRoot_I (by decide))

private theorem chapter05_positive_two_generator_minpoly :
    minpoly ℚ
        (IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ) +
          (IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ))⁻¹) =
      minpoly ℚ (Real.sqrt 2) := by
  have hpoly :
      (Polynomial.X : Polynomial ℚ) ^ 2 - Polynomial.C (2 : ℚ) =
        minpoly ℚ
          (IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ) +
            (IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ))⁻¹) :=
    minpoly.eq_of_irreducible_of_monic chapter05_irreducible_x_pow_two_sub_two
      chapter05_positive_two_generator_root
      (Polynomial.monic_X_pow_sub_C 2 (by decide))
  exact hpoly.symm.trans chapter05_minpoly_real_sqrt_two.symm

private theorem chapter05_negative_two_generator_minpoly :
    minpoly ℚ
        (IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ) -
          (IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ))⁻¹) =
      minpoly ℚ (Real.sqrt 2 * Complex.I) := by
  have hpoly :
      (Polynomial.X : Polynomial ℚ) ^ 2 - Polynomial.C (-2 : ℚ) =
        minpoly ℚ
          (IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ) -
            (IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ))⁻¹) :=
    minpoly.eq_of_irreducible_of_monic chapter05_irreducible_x_pow_two_sub_neg_two
      chapter05_negative_two_generator_root
      (Polynomial.monic_X_pow_sub_C (-2 : ℚ) (by decide))
  exact hpoly.symm.trans chapter05_minpoly_complex_sqrt_two_mul_I.symm

private theorem chapter05_complex_I_integral : IsIntegral ℚ Complex.I := by
  refine ⟨(Polynomial.X : Polynomial ℚ) ^ 2 - Polynomial.C (-1 : ℚ),
    Polynomial.monic_X_pow_sub_C (-1 : ℚ) (by decide), ?_⟩
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C]
  norm_num [pow_two, Complex.I_mul_I]

private theorem chapter05_positive_two_generator_fixed_by_neg_one :
    (chapter05CyclotomicGaloisUnitsEquiv 8 (CyclotomicField 8 ℚ)).symm
        (-1 : (ZMod 8)ˣ)
        (IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ) +
          (IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ))⁻¹) =
      IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ) +
        (IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ))⁻¹ := by
  let z : CyclotomicField 8 ℚ :=
    IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ)
  let u : (ZMod 8)ˣ := -1
  rw [map_add, map_inv₀, chapter05_cyclotomic_unit_action_on_zeta u]
  change z ^ 7 + (z ^ 7)⁻¹ = z + z⁻¹
  have hz8 : z ^ 8 = 1 := (IsCyclotomicExtension.zeta_spec 8 ℚ _).pow_eq_one
  have hzne : z ≠ 0 :=
    (IsCyclotomicExtension.zeta_spec 8 ℚ _).ne_zero (by decide)
  have hz7mul : z ^ 7 * z = 1 := by
    rw [← pow_succ, hz8]
  have hz7 : z ^ 7 = z⁻¹ := by
    calc
      z ^ 7 = z ^ 7 * 1 := by rw [mul_one]
      _ = z ^ 7 * (z * z⁻¹) := by rw [mul_inv_cancel₀ hzne]
      _ = (z ^ 7 * z) * z⁻¹ := by rw [mul_assoc]
      _ = z⁻¹ := by rw [hz7mul, one_mul]
  rw [hz7, inv_inv]
  ac_rfl

private theorem chapter05_negative_two_generator_fixed_by_three :
    (chapter05CyclotomicGaloisUnitsEquiv 8 (CyclotomicField 8 ℚ)).symm
        (ZMod.unitOfCoprime 3 (by decide : Nat.Coprime 3 8))
        (IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ) -
          (IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ))⁻¹) =
      IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ) -
        (IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ))⁻¹ := by
  let z : CyclotomicField 8 ℚ :=
    IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ)
  let u : (ZMod 8)ˣ := ZMod.unitOfCoprime 3 (by decide : Nat.Coprime 3 8)
  rw [map_sub, map_inv₀, chapter05_cyclotomic_unit_action_on_zeta u]
  change z ^ 3 - (z ^ 3)⁻¹ = z - z⁻¹
  have hz : IsPrimitiveRoot z 8 := IsCyclotomicExtension.zeta_spec 8 ℚ _
  have hz4 : z ^ 4 = -1 := by
    simpa [z] using chapter05_cyclotomic_zeta_pow_four_eq_neg_one
  have hzne : z ≠ 0 := hz.ne_zero (by decide)
  have hz3 : z ^ 3 = -z⁻¹ := by
    calc
      z ^ 3 = z ^ 3 * 1 := by rw [mul_one]
      _ = z ^ 3 * (z * z⁻¹) := by rw [mul_inv_cancel₀ hzne]
      _ = (z ^ 3 * z) * z⁻¹ := by rw [mul_assoc]
      _ = -z⁻¹ := by rw [← pow_succ, hz4, neg_one_mul]
  rw [hz3]
  rw [inv_neg, inv_inv]
  ring

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
  let z : CyclotomicField 8 ℚ :=
    IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ)
  have hcardI : Nat.card chapter05QuadraticCharacterMinusOneModEight.toUnitHom.ker = 2 :=
    chapter05_quadratic_character_ker_card
      chapter05QuadraticCharacterMinusOneModEight
      chapter05_quadratic_character_minus_one_mod_eight_toUnitHom_range
  have hcardPlus : Nat.card chapter05QuadraticCharacterTwo.toUnitHom.ker = 2 :=
    chapter05_quadratic_character_ker_card chapter05QuadraticCharacterTwo
      chapter05_quadratic_character_two_toUnitHom_range
  have hcardMinus : Nat.card chapter05QuadraticCharacterMinusTwo.toUnitHom.ker = 2 :=
    chapter05_quadratic_character_ker_card chapter05QuadraticCharacterMinusTwo
      chapter05_quadratic_character_minus_two_toUnitHom_range
  have hminI : (minpoly ℚ (z ^ 2)).natDegree = 2 := by
    have hminI' :
        (minpoly ℚ
          (IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ) ^ 2)).natDegree = 2 := by
      rw [chapter05_gaussian_generator_minpoly,
        ← Polynomial.cyclotomic_eq_minpoly_rat Complex.isPrimitiveRoot_I (by decide),
        Polynomial.natDegree_cyclotomic]
      decide
    simpa [z] using hminI'
  have hminPlus :
      (minpoly ℚ
        (z + z⁻¹)).natDegree = 2 := by
    have hminPlus' :
        (minpoly ℚ
          (IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ) +
            (IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ))⁻¹)).natDegree = 2 := by
      rw [chapter05_positive_two_generator_minpoly,
        chapter05_minpoly_real_sqrt_two,
        Polynomial.natDegree_X_pow_sub_C]
    simpa [z] using hminPlus'
  have hminMinus :
      (minpoly ℚ
        (z - z⁻¹)).natDegree = 2 := by
    have hminMinus' :
        (minpoly ℚ
          (IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ) -
            (IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ))⁻¹)).natDegree = 2 := by
      rw [chapter05_negative_two_generator_minpoly,
        chapter05_minpoly_complex_sqrt_two_mul_I,
        Polynomial.natDegree_X_pow_sub_C]
    simpa [z] using hminMinus'
  have hxI : IsIntegral ℚ (z ^ 2) := IsIntegral.of_finite ℚ _
  have hxPlus : IsIntegral ℚ (z + z⁻¹) := IsIntegral.of_finite ℚ _
  have hxMinus : IsIntegral ℚ (z - z⁻¹) := IsIntegral.of_finite ℚ _
  have hfixI : ∀ u : (ZMod 8)ˣ, u ∈
      chapter05QuadraticCharacterMinusOneModEight.toUnitHom.ker →
      (chapter05CyclotomicGaloisUnitsEquiv 8 (CyclotomicField 8 ℚ)).symm u (z ^ 2) = z ^ 2 := by
    intro u hu
    rw [chapter05_quadratic_character_minus_one_mod_eight_ker_eq_zpowers] at hu
    exact chapter05_zpowers_element_fixes_generator
      (CyclotomicField 8 ℚ)
      (ZMod.unitOfCoprime 5 (by decide : Nat.Coprime 5 8)) (z ^ 2)
      (by simpa [z] using chapter05_gaussian_generator_fixed_by_five) hu
  have hfixPlus : ∀ u : (ZMod 8)ˣ, u ∈
      chapter05QuadraticCharacterTwo.toUnitHom.ker →
      (chapter05CyclotomicGaloisUnitsEquiv 8 (CyclotomicField 8 ℚ)).symm u
          (z + z⁻¹) = z + z⁻¹ := by
    intro u hu
    rw [chapter05_quadratic_character_two_ker_eq_zpowers] at hu
    exact chapter05_zpowers_element_fixes_generator
      (CyclotomicField 8 ℚ) (-1 : (ZMod 8)ˣ) (z + z⁻¹)
      (by simpa [z] using chapter05_positive_two_generator_fixed_by_neg_one) hu
  have hfixMinus : ∀ u : (ZMod 8)ˣ, u ∈
      chapter05QuadraticCharacterMinusTwo.toUnitHom.ker →
      (chapter05CyclotomicGaloisUnitsEquiv 8 (CyclotomicField 8 ℚ)).symm u
          (z - z⁻¹) = z - z⁻¹ := by
    intro u hu
    rw [chapter05_quadratic_character_minus_two_ker_eq_zpowers] at hu
    exact chapter05_zpowers_element_fixes_generator
      (CyclotomicField 8 ℚ)
      (ZMod.unitOfCoprime 3 (by decide : Nat.Coprime 3 8)) (z - z⁻¹)
      (by simpa [z] using chapter05_negative_two_generator_fixed_by_three) hu
  have hfieldI :
      chapter05CyclotomicCharacterFixedField 8 (CyclotomicField 8 ℚ)
          chapter05QuadraticCharacterMinusOneModEight =
        IntermediateField.adjoin ℚ {z ^ 2} :=
    chapter05_character_fixedField_eq_adjoin
      chapter05QuadraticCharacterMinusOneModEight (z ^ 2) hxI hminI hcardI hfixI
  have hfieldPlus :
      chapter05CyclotomicCharacterFixedField 8 (CyclotomicField 8 ℚ)
          chapter05QuadraticCharacterTwo =
        IntermediateField.adjoin ℚ {z + z⁻¹} :=
    chapter05_character_fixedField_eq_adjoin
      chapter05QuadraticCharacterTwo (z + z⁻¹) hxPlus hminPlus hcardPlus hfixPlus
  have hfieldMinus :
      chapter05CyclotomicCharacterFixedField 8 (CyclotomicField 8 ℚ)
          chapter05QuadraticCharacterMinusTwo =
        IntermediateField.adjoin ℚ {z - z⁻¹} :=
    chapter05_character_fixedField_eq_adjoin
      chapter05QuadraticCharacterMinusTwo (z - z⁻¹) hxMinus hminMinus hcardMinus hfixMinus
  constructor
  · rw [hfieldI]
    change Nonempty
      (IntermediateField.adjoin ℚ {z ^ 2} ≃ₐ[ℚ]
        IntermediateField.adjoin ℚ {Complex.I})
    refine ⟨?_⟩
    let e : IntermediateField.adjoin ℚ {z ^ 2} ≃ₐ[ℚ]
        IntermediateField.adjoin ℚ {Complex.I} :=
      (IntermediateField.adjoinRootEquivAdjoin ℚ hxI).symm.trans <|
        (AdjoinRoot.algEquivOfEq ℚ _ _
          (by simpa [z] using chapter05_gaussian_generator_minpoly)).trans
          (IntermediateField.adjoinRootEquivAdjoin ℚ
            chapter05_complex_I_integral)
    exact e
  constructor
  · rw [hfieldPlus]
    change Nonempty
      (IntermediateField.adjoin ℚ {z + z⁻¹} ≃ₐ[ℚ]
        IntermediateField.adjoin ℚ {Real.sqrt 2})
    refine ⟨?_⟩
    let e : IntermediateField.adjoin ℚ {z + z⁻¹} ≃ₐ[ℚ]
        IntermediateField.adjoin ℚ {Real.sqrt 2} :=
      (IntermediateField.adjoinRootEquivAdjoin ℚ hxPlus).symm.trans <|
        (AdjoinRoot.algEquivOfEq ℚ _ _
          (by simpa [z] using chapter05_positive_two_generator_minpoly)).trans
          (IntermediateField.adjoinRootEquivAdjoin ℚ chapter05_real_sqrt_two_integral)
    exact e
  · rw [hfieldMinus]
    change Nonempty
      (IntermediateField.adjoin ℚ {z - z⁻¹} ≃ₐ[ℚ]
        IntermediateField.adjoin ℚ {Real.sqrt 2 * Complex.I})
    refine ⟨?_⟩
    let e : IntermediateField.adjoin ℚ {z - z⁻¹} ≃ₐ[ℚ]
        IntermediateField.adjoin ℚ {Real.sqrt 2 * Complex.I} :=
      (IntermediateField.adjoinRootEquivAdjoin ℚ hxMinus).symm.trans <|
        (AdjoinRoot.algEquivOfEq ℚ _ _
          (by simpa [z] using chapter05_negative_two_generator_minpoly)).trans
          (IntermediateField.adjoinRootEquivAdjoin ℚ
            chapter05_complex_sqrt_two_mul_I_integral)
    exact e

end

end LastLib.Book06GlobalClassFieldTheory.Chapter05
