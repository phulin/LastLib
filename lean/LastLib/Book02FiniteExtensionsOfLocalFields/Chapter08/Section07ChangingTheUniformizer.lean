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
  rw [chapter08UnitMultiple, AddValuation.map_mul, hu, hπ, zero_add]

/-- Book §8.7: perturbing a uniformizer by an element of value at least two
preserves its value and has the displayed unit factorization. -/
theorem chapter08_higher_order_perturbation_is_a_uniformizer
    {L : Type*} [Field L]
    (vL : AddValuation L (WithTop ℤ)) (π a : L)
    (hπ : vL π = 1) (ha : 2 ≤ vL a) :
    vL (chapter08HigherOrderPerturbation π a) = 1 ∧
      chapter08HigherOrderPerturbation π a = π * (1 + a / π) ∧
      vL (1 + a / π) = 0 := by
  have hπ0 : π ≠ 0 := by
    intro hzero
    subst π
    simp at hπ
  have hlt : vL π < vL a := by
    rw [hπ]
    exact lt_of_lt_of_le (by norm_num) ha
  have hvalue : vL (chapter08HigherOrderPerturbation π a) = 1 := by
    rw [chapter08HigherOrderPerturbation]
    exact (AddValuation.map_add_eq_of_lt_left vL hlt).trans hπ
  have hfactor : chapter08HigherOrderPerturbation π a = π * (1 + a / π) := by
    unfold chapter08HigherOrderPerturbation
    field_simp [hπ0]
  have hdiv : (1 : WithTop ℤ) ≤ vL (a / π) := by
    rw [AddValuation.map_div, hπ]
    by_cases htop : vL a = ⊤
    · simp [htop]
    · obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.mp htop
      rw [← hz] at ha
      rw [← hz]
      change (↑(1 : ℤ) : WithTop ℤ) ≤
        (↑z : WithTop ℤ) - (↑(1 : ℤ) : WithTop ℤ)
      rw [← WithTop.LinearOrderedAddCommGroup.coe_sub]
      have hz2 : (2 : ℤ) ≤ z := by
        apply WithTop.coe_le_coe.mp
        simpa using ha
      exact_mod_cast (show (1 : ℤ) ≤ z - 1 by omega)
  have hunit : vL (1 + a / π) = 0 := by
    have hlt' : vL (1 : L) < vL (a / π) := by
      rw [vL.map_one]
      exact lt_of_lt_of_le (by norm_num) hdiv
    exact (AddValuation.map_add_eq_of_lt_left vL hlt').trans vL.map_one
  exact ⟨hvalue, hfactor, hunit⟩

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
  unfold chapter08NormOfUniformizerForm
  have hnorm := chapter08_uniformizer_norm_has_value_one
    vK vL hval e he hedegree hscale htotal πL hπL
  have hπK0 : πK ≠ 0 := by
    intro hzero
    subst πK
    simp at hπK
  refine ⟨Algebra.norm K πL / πK, ?_, ?_⟩
  · rw [AddValuation.map_div, hnorm, hπK]
    norm_num
  · field_simp [hπK0]

/-- Book §8.7: replacing a generator by an element times it multiplies the
norm by the norm of that element. -/
theorem chapter08_norm_of_unit_multiple
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (a : Lˣ) (π : L) :
    Algebra.norm K ((a : L) * π) = Algebra.norm K (a : L) * Algebra.norm K π := by
  rw [map_mul]

/-- The subgroup of base-field units obtained as norms of extension-field
units.  Its construction is canonical but not needed by the statement pass.
-/
noncomputable def chapter08UnitNormSubgroup
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Subgroup Kˣ :=
  Subgroup.map (Units.map (Algebra.norm K (S := L))) ⊤

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
    (hchange : π₂ = (a : L) * π₁)
    (hπK : πK ≠ 0) (hπ₁ : π₁ ≠ 0) :
    QuotientGroup.mk (s := chapter08UnitNormSubgroup K L) u₁ =
      QuotientGroup.mk (s := chapter08UnitNormSubgroup K L) u₂ := by
  let na : Kˣ := Units.map (Algebra.norm K (S := L)) a
  have hnorm : Algebra.norm K π₂ =
      Algebra.norm K (a : L) * Algebra.norm K π₁ := by
    rw [hchange, chapter08_norm_of_unit_multiple]
  have hcoe : (u₂ : K) * πK = (na : K) * ((u₁ : K) * πK) := by
    calc
      (u₂ : K) * πK = Algebra.norm K π₂ := h₂.symm
      _ = Algebra.norm K (a : L) * Algebra.norm K π₁ := hnorm
      _ = (na : K) * ((u₁ : K) * πK) := by rw [h₁]; rfl
  have hucoe : (u₂ : K) = (na : K) * (u₁ : K) := by
    apply (mul_right_cancel₀ hπK)
    simpa [mul_assoc] using hcoe
  have hu : u₂ = na * u₁ := by
    apply Units.ext
    exact hucoe
  have hna : na ∈ chapter08UnitNormSubgroup K L := by
    change na ∈ Subgroup.map (Units.map (Algebra.norm K (S := L))) ⊤
    exact ⟨a, trivial, rfl⟩
  rw [hu, QuotientGroup.mk_mul]
  rw [((QuotientGroup.eq_one_iff na).2 hna)]
  exact (one_mul
    (QuotientGroup.mk (s := chapter08UnitNormSubgroup K L) u₁)).symm

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08
