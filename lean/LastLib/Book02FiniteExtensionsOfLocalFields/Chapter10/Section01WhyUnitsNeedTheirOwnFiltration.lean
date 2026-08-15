import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Dependencies
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.Section02EquivalentCharacterizations

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10

noncomputable section

open Ideal IsLocalRing
open scoped BigOperators Topology

/-! ## 10.1. Why units need their own filtration -/

/--
For a normalized rank-one discrete valuation, a chosen uniformizer separates
the integer-valued magnitude from the unit in the valuation ring.  The
conclusion is stated both as an explicit factorization and as the resulting
group-coordinate equivalence.
-/
theorem chapter10_valuation_unit_decomposition
    {L Γ₀ : Type*} [Field L]
    [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation L Γ₀) [Valuation.IsRankOneDiscrete v]
    (π : L) (hπ : v π = Valuation.IsRankOneDiscrete.generator v) :
    (∀ x : L, x ≠ 0 →
      ∃ n : ℤ, ∃ u : v.valuationSubringˣ,
        x = π ^ n * ((u : v.valuationSubring) : L)) ∧
      Nonempty
        (Lˣ ≃* (Multiplicative ℤ × v.valuationSubringˣ)) := by
  classical
  let A := v.valuationSubring
  have hgenlt : Valuation.IsRankOneDiscrete.generator v < (1 : Γ₀) :=
    Valuation.IsRankOneDiscrete.generator_lt_one v
  let πA : A :=
    ⟨π, by
      change v π ≤ 1
      rw [hπ]
      exact hgenlt.le⟩
  have hπu : v.IsUniformizer πA := by
    change v (πA : L) = Valuation.IsRankOneDiscrete.generator v
    simpa [πA] using hπ
  have hπne : π ≠ 0 := by
    intro h
    apply hπu.ne_zero
    simpa [πA] using h
  have hπA_ne : πA ≠ 0 := by
    intro h
    apply hπu.ne_zero
    simpa using congrArg Subtype.val h
  have hπchapter :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.Chapter04Uniformizer A πA :=
    ⟨hπA_ne, hπu.is_generator⟩
  have normal_form (x : L) (hx : x ≠ 0) :
      ∃ n : ℤ, ∃ u : Aˣ,
        x = π ^ n * ((u : A) : L) ∧
          ∀ m : ℤ, ∀ w : Aˣ,
            x = π ^ m * ((w : A) : L) → m = n ∧ w = u := by
    obtain ⟨n, u, hxu, hu⟩ :=
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.dvr_fraction_field_unique_normal_form
        A L hπchapter hx
    refine ⟨n, u, ?_, ?_⟩
    · simpa [Units.smul_def, Algebra.smul_def, ValuationSubring.algebraMap_apply,
        πA, mul_comm] using hxu
    · intro m w hmw
      apply hu m w
      simpa [Units.smul_def, Algebra.smul_def, ValuationSubring.algebraMap_apply,
        πA, mul_comm] using hmw
  constructor
  · intro x hx
    obtain ⟨n, u, hxu, _⟩ := normal_form x hx
    exact ⟨n, u, hxu⟩
  · choose n u hfactor hunique using
      fun x : Lˣ => normal_form (x : L) x.ne_zero
    let f : Lˣ →* (Multiplicative ℤ × Aˣ) :=
      { toFun := fun x => (Multiplicative.ofAdd (n x), u x)
        map_one' := by
          have h := hunique 1 0 1 (by simp)
          apply Prod.ext
          · change n 1 = 0
            exact h.1.symm
          · exact h.2.symm
        map_mul' := by
          intro x y
          have hxy :
              ((x * y : Lˣ) : L) =
                π ^ (n x + n y) * (((u x * u y : Aˣ) : A) : L) := by
            change (x : L) * (y : L) = _
            rw [hfactor x, hfactor y]
            simp only [Units.val_mul]
            calc
              π ^ n x * (((u x : A) : L)) *
                    (π ^ n y * (((u y : A) : L))) =
                  (π ^ n x * π ^ n y) *
                    ((((u x : A) : L) * ((u y : A) : L))) := by ring
              _ = π ^ (n x + n y) *
                    ((((u x : A) : L) * ((u y : A) : L))) := by
                rw [← zpow_add₀ hπne]
              _ = π ^ (n x + n y) * (((u x * u y : Aˣ) : A) : L) := by
                rfl
          have h := hunique (x * y) (n x + n y) (u x * u y) hxy
          apply Prod.ext
          · change n (x * y) = n x + n y
            exact h.1.symm
          · exact h.2.symm }
    let g : (Multiplicative ℤ × Aˣ) →* Lˣ :=
      { toFun := fun z =>
          Units.mk0
            (π ^ (Multiplicative.toAdd z.1) * (((z.2 : A) : L))) (by
              have hz : ((z.2 : A) : L) ≠ 0 := by
                intro hz
                apply z.2.ne_zero
                apply Subtype.ext
                exact hz
              exact mul_ne_zero (zpow_ne_zero _ hπne) hz)
        map_one' := by
          apply Units.ext
          simp
        map_mul' := by
          intro z w
          apply Units.ext
          change
            π ^ (Multiplicative.toAdd z.1 + Multiplicative.toAdd w.1) *
                (((z.2 * w.2 : Aˣ) : A) : L) =
              (π ^ Multiplicative.toAdd z.1 * (((z.2 : A) : L))) *
                (π ^ Multiplicative.toAdd w.1 * (((w.2 : A) : L)))
          rw [zpow_add₀ hπne]
          simp only [Units.val_mul]
          change
            (π ^ Multiplicative.toAdd z.1 * π ^ Multiplicative.toAdd w.1) *
                ((((z.2 : A) : L) * ((w.2 : A) : L))) =
              (π ^ Multiplicative.toAdd z.1 * (((z.2 : A) : L))) *
                (π ^ Multiplicative.toAdd w.1 * (((w.2 : A) : L)))
          ring }
    have hfg : ∀ x : Lˣ, g (f x) = x := by
      intro x
      apply Units.ext
      change π ^ n x * (((u x : A) : L)) = (x : L)
      exact (hfactor x).symm
    have hgf : ∀ z : Multiplicative ℤ × Aˣ, f (g z) = z := by
      intro z
      have hz :
          ((g z : Lˣ) : L) =
            π ^ (Multiplicative.toAdd z.1) * (((z.2 : A) : L)) := by
        rfl
      have h := hunique (g z) (Multiplicative.toAdd z.1) z.2 hz
      apply Prod.ext
      · change n (g z) = Multiplicative.toAdd z.1
        exact h.1.symm
      · exact h.2.symm
    let e : Lˣ ≃* (Multiplicative ℤ × Aˣ) :=
      { toFun := fun x => f x
        invFun := fun z => g z
        left_inv := hfg
        right_inv := hgf
        map_mul' := by
          intro x y
          exact f.map_mul x y }
    exact ⟨e⟩

/-- The zeroth congruence subgroup is the full unit group of the valuation ring. -/
theorem chapter10_unit_filtration_zero
    {L : Type*} [Field L] (A : ValuationSubring L) :
    chapter10UnitFiltration A 0 = ⊤ := by
  ext u
  simp [chapter10UnitFiltration, chapter10IdealUnitFiltration]

/-- The product calculation behind closure of `1 + 𝔪ⁿ`. -/
theorem chapter10_unit_product_formula
    {L : Type*} [Field L] (A : ValuationSubring L) (n : ℕ)
    (x y : A) (hx : x ∈ (IsLocalRing.maximalIdeal A) ^ n)
    (hy : y ∈ (IsLocalRing.maximalIdeal A) ^ n) :
    (1 + x) * (1 + y) = 1 + (x + y + x * y) ∧
      x + y + x * y ∈ (IsLocalRing.maximalIdeal A) ^ n := by
  constructor
  · ring
  · exact add_mem (add_mem hx hy)
      (Ideal.mul_mem_left _ _ hy)

/-- Inverses stay in every congruence subgroup. -/
theorem chapter10_unit_filtration_inverse
    {L : Type*} [Field L] (A : ValuationSubring L) (n : ℕ)
    {u : Aˣ} (hu : u ∈ chapter10UnitFiltration A n) :
    u⁻¹ ∈ chapter10UnitFiltration A n := by
  exact (chapter10UnitFiltration A n).inv_mem hu

/-- The congruence filtration is descending. -/
theorem chapter10_unit_filtration_descending
    (A : Type*) [CommRing A] [IsLocalRing A] :
    ∀ n : ℕ, chapter10UnitFiltration A (n + 1) ≤ chapter10UnitFiltration A n := by
  intro n u hu
  change ((u : A) - 1) ∈ (IsLocalRing.maximalIdeal A) ^ (n + 1) at hu
  change ((u : A) - 1) ∈ (IsLocalRing.maximalIdeal A) ^ n
  exact (Ideal.pow_le_pow_right n.le_succ) hu

/--
The field-level zeroth and first groups agree with the valuation-subring unit
group and Mathlib's principal-unit group, respectively.
-/
theorem chapter10_field_filtration_zero_one
    {L : Type*} [Field L] (A : ValuationSubring L) :
    chapter10FieldUnitFiltration A 0 = A.unitGroup ∧
      chapter10FieldUnitFiltration A 1 = A.principalUnitGroup := by
  constructor
  · rw [chapter10FieldUnitFiltration, chapter10_unit_filtration_zero]
    ext x
    constructor
    · rintro ⟨u, -, rfl⟩
      rw [ValuationSubring.mem_unitGroup_iff]
      change A.valuation ((Units.map A.subtype.toMonoidHom u : Lˣ)) = 1
      simp
    · intro hx
      let x' : A.unitGroup := ⟨x, hx⟩
      refine ⟨A.unitGroupMulEquiv x', trivial, ?_⟩
      apply Units.ext
      change (((A.unitGroupMulEquiv x' : Aˣ) : A) : L) = (x : L)
      exact A.coe_unitGroupMulEquiv_apply x'
  · rw [chapter10FieldUnitFiltration]
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [ValuationSubring.mem_principalUnitGroup_iff]
      change (u : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ 1 at hu
      rw [pow_one] at hu
      exact (ValuationSubring.valuation_lt_one_iff A ((u : A) - 1)).1 hu
    · intro hx
      let x' : A.unitGroup := ⟨x, A.principal_units_le_units hx⟩
      refine ⟨A.unitGroupMulEquiv x', ?_, ?_⟩
      · change ((A.unitGroupMulEquiv x' : Aˣ) : A) - 1 ∈
          (IsLocalRing.maximalIdeal A) ^ 1
        rw [pow_one]
        exact (ValuationSubring.valuation_lt_one_iff A _).2
          (by
            have hx' : A.valuation ((x : L) - 1) < 1 :=
              (ValuationSubring.mem_principalUnitGroup_iff A x).1 hx
            simpa [A.coe_unitGroupMulEquiv_apply x'] using hx')
      · apply Units.ext
        change (((A.unitGroupMulEquiv x' : Aˣ) : A) : L) = (x : L)
        exact A.coe_unitGroupMulEquiv_apply x'

/-- A separated valuation-ring topology makes the unit filtration Hausdorff. -/
theorem chapter10_unit_filtration_separated
    {L : Type*} [Field L] (A : ValuationSubring L)
    (hseparated : ∀ x : A,
      (∀ n : ℕ, x ∈ (IsLocalRing.maximalIdeal A) ^ n) → x = 0) :
    ⨅ n : ℕ, chapter10UnitFiltration A n = ⊥ := by
  ext u
  constructor
  · intro hu
    have hu' : ∀ n : ℕ, u ∈ chapter10UnitFiltration A n := by
      intro n
      exact (Subgroup.mem_iInf.mp hu) n
    have hzero : (u : A) - 1 = 0 := hseparated ((u : A) - 1) (by
      intro n
      exact hu' n)
    simp only [Subgroup.mem_bot]
    apply Units.ext
    change (u : A) = 1
    exact sub_eq_zero.mp hzero
  · intro hu
    simp only [Subgroup.mem_bot] at hu
    subst u
    refine (Subgroup.mem_iInf).2 ?_
    intro n
    exact (chapter10UnitFiltration A n).one_mem

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10
