import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.Section06RecognitionThroughAChosenElement

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08

noncomputable section

open scoped WithTop

/-! # 8.7. Changing the uniformizer -/

/-- Multiplication by a unit gives the standard coordinate change of a
uniformizer. -/
def chapter08UnitMultiple {L : Type*} [Mul L] (u π : L) : L := u * π

/-- A higher-order perturbation of a chosen uniformizer. -/
def chapter08HigherOrderPerturbation {L : Type*} [Add L] (π a : L) : L := π + a

/-- Book §8.7: a value-zero unit multiple of a value-one element is again a
value-one element. -/
theorem chapter08_unit_multiple_is_a_uniformizer
    {L : Type*} [Field L]
    (vL : AddValuation L (WithTop ℤ)) (u π : L)
    (hu : vL u = 0) (hπ : vL π = 1) :
    vL (chapter08UnitMultiple u π) = 1 := by
  sorry

/-- Book §8.7: perturbing a uniformizer by an element of value at least two
preserves its value and has the displayed unit factorization. -/
theorem chapter08_higher_order_perturbation_is_a_uniformizer
    {L : Type*} [Field L]
    (vL : AddValuation L (WithTop ℤ)) (π a : L)
    (hπ0 : π ≠ 0) (hπ : vL π = 1) (ha : 2 ≤ vL a) :
    vL (chapter08HigherOrderPerturbation π a) = 1 ∧
      chapter08HigherOrderPerturbation π a = π * (1 + a / π) ∧
      vL (1 + a / π) = 0 := by
  sorry

/-- The intrinsic form of the norm assertion for a uniformizer. -/
def chapter08NormOfUniformizerForm
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ)) (πK : K) (πL : L) : Prop :=
  ∃ u : K, vK u = 0 ∧ Algebra.norm K πL = u * πK

/-- Book §8.7: the norm of a uniformizer in a totally ramified extension is a
unit times a base uniformizer. -/
theorem chapter08_norm_of_totally_ramified_uniformizer
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hval : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL))
    (e : ℕ) (he : 0 < e)
    (hedegree : e = Module.finrank K L)
    (hscale : ∀ x : K, x ≠ 0 →
      vL (algebraMap K L x) = e • vK x)
    (πK : K) (πL : L)
    (hπK : vK πK = 1) (hπL : vL πL = 1)
    (htotal : chapter08TotallyRamified vK vL hval) :
    chapter08NormOfUniformizerForm vK πK πL := by
  sorry

/-- Book §8.7: replacing a generator by an element times it multiplies the
norm by the norm of that element. -/
theorem chapter08_norm_of_unit_multiple
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (a π : L) :
    Algebra.norm K (a * π) = Algebra.norm K a * Algebra.norm K π := by
  sorry

/-- The subgroup of base-field units obtained as norms of extension-field
units.  Its construction is canonical but not needed by the statement pass.
-/
noncomputable def chapter08UnitNormSubgroup
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Subgroup Kˣ := by
  sorry

/-- The unit factor of a norm, modulo norms of extension units. -/
abbrev chapter08NormUnitFactorClass
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Type _ :=
  Kˣ ⧸ chapter08UnitNormSubgroup K L

/-- Book §8.7: the unit factor in the norm of a uniformizer is coordinate
dependent, but its class modulo the unit norm subgroup is unchanged. -/
theorem chapter08_norm_unit_factor_class_is_coordinate_invariant
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (πK : K) (π₁ π₂ : L) (u₁ u₂ : Kˣ) (a : Lˣ)
    (h₁ : Algebra.norm K π₁ = (u₁ : K) * πK)
    (h₂ : Algebra.norm K π₂ = (u₂ : K) * πK)
    (hchange : π₂ = (a : L) * π₁) :
    QuotientGroup.mk (s := chapter08UnitNormSubgroup K L) u₁ =
      QuotientGroup.mk (s := chapter08UnitNormSubgroup K L) u₂ := by
  sorry

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08
