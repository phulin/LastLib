import LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.Section01BoundedElements

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter03

open Set
open scoped BigOperators WithZero LaurentSeries PowerSeries

/-!
# Chapter 3: Valuation rings and divisibility

Mathlib uses multiplicative valuations, so bounded elements are written `v x ≤ 1`.
The additive convention in the book is recorded below with `AddValuation`; under the
usual sign change, `v x ≤ 1` is the same assertion as `0 ≤ v x`.
-/

universe u v w

/-! # Book 1, Chapter 3, Section 3.2: The Intrinsic Characterization
-/

section IntrinsicCriterion

variable {K : Type*} [Field K]

/-! ### 3.2. The intrinsic characterization -/

/-- A subring is a valuation ring of some valuation on its fraction field. -/
def IsValuationRingSubring (V : Subring K) : Prop :=
  ∃ A : ValuationSubring K, V = A.toSubring

/-- The second condition in the valuation-ring criterion. -/
def HasValuationSubringCriterion (V : Subring K) : Prop :=
  ∀ x : K, x ∈ V ∨ x⁻¹ ∈ V

/- A principal fractional ideal `xV`, represented as a subset of the field. -/
def principalFractionalSet (V : Subring K) (x : K) : Set K :=
  {z | ∃ a : V, z = (a : K) * x}

/- Total comparability of principal fractional ideals. -/
def PrincipalFractionalIdealsComparable (V : Subring K) : Prop :=
  ∀ x y : K, x ≠ 0 → y ≠ 0 →
    principalFractionalSet V x ⊆ principalFractionalSet V y ∨
      principalFractionalSet V y ⊆ principalFractionalSet V x

theorem principalFractionalSet_le_iff (V : Subring K) {x y : K} (hy : y ≠ 0) :
    principalFractionalSet V x ⊆ principalFractionalSet V y ↔ x / y ∈ V := by
  constructor
  · intro h
    have hmem : x ∈ principalFractionalSet V y := by
      apply h
      exact ⟨1, by simp⟩
    rcases hmem with ⟨a, ha⟩
    change x = (a : K) * y at ha
    have hxy : x / y = (a : K) := by
      rw [ha]
      field_simp [hy]
    rw [hxy]
    exact a.property
  · intro h z hz
    rcases hz with ⟨a, rfl⟩
    refine ⟨⟨(a : K) * (x / y), V.mul_mem a.property h⟩, ?_⟩
    field_simp [hy]

theorem principalFractionalSet_comparison_iff (V : Subring K) {x y : K}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    principalFractionalSet V x ⊆ principalFractionalSet V y ∨
        principalFractionalSet V y ⊆ principalFractionalSet V x ↔
      x / y ∈ V ∨ y / x ∈ V := by
  rw [principalFractionalSet_le_iff V hy, principalFractionalSet_le_iff V hx]

theorem valuationRingCriterion_tfae (V : Subring K) :
    List.TFAE
      [IsValuationRingSubring V,
        HasValuationSubringCriterion V,
        PrincipalFractionalIdealsComparable V] := by
  tfae_have 1 ↔ 2 := by
    constructor
    · rintro ⟨A, rfl⟩ x
      exact A.mem_or_inv_mem x
    · intro hV
      let A := ValuationSubring.ofSubring V hV
      refine ⟨A, ?_⟩
      rfl
  tfae_have 2 ↔ 3 := by
    constructor
    · intro hV x y hx hy
      apply (principalFractionalSet_comparison_iff V hx hy).2
      rcases hV (x / y) with h | h
      · exact Or.inl h
      · exact Or.inr (by simpa [div_eq_mul_inv] using h)
    · intro hC x
      by_cases hx : x = 0
      · exact Or.inl (by simp [hx])
      rcases hC x 1 hx one_ne_zero with h | h
      · exact Or.inl (by simpa using
          (principalFractionalSet_le_iff V one_ne_zero).1 h)
      · exact Or.inr (by simpa [one_div] using
          (principalFractionalSet_le_iff V hx).1 h)
  tfae_finish

theorem valuationRingCriterion (V : Subring K) :
    IsValuationRingSubring V ↔ HasValuationSubringCriterion V ∧
      PrincipalFractionalIdealsComparable V := by
  have hT := valuationRingCriterion_tfae V
  have h12 : IsValuationRingSubring V ↔ HasValuationSubringCriterion V :=
    hT.out 0 1
  have h23 : HasValuationSubringCriterion V ↔
      PrincipalFractionalIdealsComparable V := hT.out 1 2
  constructor
  · intro h
    exact ⟨h12.mp h, h23.mp (h12.mp h)⟩
  · rintro ⟨hV, _⟩
    exact h12.mpr hV

/- Reconstruction by quotienting the multiplicative group by the unit group. -/

def criterionValuationSubring (V : Subring K) (hV : HasValuationSubringCriterion V) :
    ValuationSubring K :=
  ValuationSubring.ofSubring V hV

abbrev criterionValueGroup (V : Subring K) (hV : HasValuationSubringCriterion V) :=
  (criterionValuationSubring V hV).ValueGroup

noncomputable def criterionReconstructedValuation (V : Subring K)
    (hV : HasValuationSubringCriterion V) :
    Valuation K (criterionValueGroup V hV) :=
  (criterionValuationSubring V hV).valuation

theorem criterionReconstructedValuation_integer (V : Subring K)
    (hV : HasValuationSubringCriterion V) :
    (criterionReconstructedValuation V hV).integer = V := by
  change (criterionValuationSubring V hV).valuation.integer =
    (criterionValuationSubring V hV).toSubring
  exact ValuationSubring.integer_valuation (criterionValuationSubring V hV)

def criterionUnitSubgroup (V : Subring K) : Subgroup Kˣ :=
  (Units.map V.subtype.toMonoidHom).range

abbrev criterionUnitQuotient (V : Subring K) :=
  Kˣ ⧸ criterionUnitSubgroup V

noncomputable def criterionValueGroup_is_quotient_by_units (V : Subring K)
    (hV : HasValuationSubringCriterion V) :
    (criterionValueGroup V hV)ˣ ≃* criterionUnitQuotient V := by
  classical
  let A := criterionValuationSubring V hV
  let φ : Kˣ →* (A.ValueGroup)ˣ :=
    Units.map A.valuation.toMonoidWithZeroHom.toMonoidHom
  have hφ : Function.Surjective φ := by
    intro u
    obtain ⟨x, hx⟩ := Quotient.exists_rep (u : A.ValueGroup)
    have hx0 : x ≠ 0 := by
      intro hx0
      apply u.ne_zero
      rw [← hx, hx0]
      rfl
    refine ⟨Units.mk0 x hx0, ?_⟩
    apply Units.ext
    change A.valuation x = (u : A.ValueGroup)
    exact hx
  have hker : φ.ker = criterionUnitSubgroup V := by
    ext a
    constructor
    · intro ha
      have hφa : φ a = 1 := MonoidHom.mem_ker.mp ha
      have hval : A.valuation (a : K) = 1 := by
        have hv := congrArg Units.val hφa
        simpa [φ] using hv
      have haA : (a : K) ∈ A :=
        A.mem_of_valuation_le_one (a : K) hval.le
      have haV : (a : K) ∈ V := by
        apply (ValuationSubring.mem_ofSubring V hV (a : K)).mp
        simpa [A, criterionValuationSubring] using haA
      have hainvval : A.valuation (a⁻¹ : K) = 1 := by
        rw [map_inv₀, hval, inv_one]
      have hainvA : (a⁻¹ : K) ∈ A :=
        A.mem_of_valuation_le_one (a⁻¹ : K) hainvval.le
      have hainvV : (a⁻¹ : K) ∈ V := by
        apply (ValuationSubring.mem_ofSubring V hV (a⁻¹ : K)).mp
        simpa [A, criterionValuationSubring] using hainvA
      let u : Vˣ :=
        { val := ⟨(a : K), haV⟩
          inv := ⟨(a⁻¹ : K), hainvV⟩
          val_inv := by apply Subtype.ext; simp
          inv_val := by apply Subtype.ext; simp }
      change a ∈ (Units.map V.subtype.toMonoidHom).range
      exact ⟨u, by apply Units.ext; rfl⟩
    · intro ha
      change a ∈ (Units.map V.subtype.toMonoidHom).range at ha
      rcases ha with ⟨u, rfl⟩
      have huA : (u : K) ∈ A := by
        apply (ValuationSubring.mem_ofSubring V hV (u : K)).mpr
        exact u.val.property
      have huinv : (u⁻¹ : K) = (u.inv : K) := by
        exact (eq_inv_of_mul_eq_one_left
          (congrArg (fun z : V => (z : K)) u.inv_val)).symm
      have huinvA : (u⁻¹ : K) ∈ A := by
        rw [huinv]
        apply (ValuationSubring.mem_ofSubring V hV (u.inv : K)).mpr
        exact u.inv.property
      let uA : Aˣ :=
        { val := ⟨(u : K), huA⟩
          inv := ⟨(u⁻¹ : K), huinvA⟩
          val_inv := by apply Subtype.ext; simp
          inv_val := by apply Subtype.ext; simp }
      change φ (Units.map V.subtype.toMonoidHom u) = 1
      apply Units.ext
      have huval : A.valuation (u : K) = 1 := by
        simpa [uA] using A.valuation_unit uA
      simpa [φ] using huval
  let e := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  exact e.symm.trans (QuotientGroup.quotientMulEquivOfEq hker)

def criterionComparison (V : Subring K) (_hV : HasValuationSubringCriterion V)
    (x y : K) : Prop :=
  x / y ∈ V

theorem criterionComparison_iff_reconstructedValuation_le
    (V : Subring K) (hV : HasValuationSubringCriterion V) {x y : K} (hy : y ≠ 0) :
    criterionComparison V hV x y ↔
      criterionReconstructedValuation V hV x ≤ criterionReconstructedValuation V hV y := by
  change x / y ∈ V ↔ _
  change x / y ∈ criterionValuationSubring V hV ↔ _
  change x / y ∈ criterionValuationSubring V hV ↔
    (criterionValuationSubring V hV).valuation x ≤
      (criterionValuationSubring V hV).valuation y
  constructor
  · intro h
    have hv := (ValuationSubring.valuation_le_one_iff
      (criterionValuationSubring V hV) (x / y)).mpr h
    rw [map_div₀, div_le_one₀
      ((criterionValuationSubring V hV).valuation.pos_iff.mpr hy)] at hv
    exact hv
  · intro h
    apply (ValuationSubring.valuation_le_one_iff
      (criterionValuationSubring V hV) (x / y)).mp
    rw [map_div₀, div_le_one₀
      ((criterionValuationSubring V hV).valuation.pos_iff.mpr hy)]
    exact h

theorem criterionComparison_unit_invariant (V : Subring K)
    (hV : HasValuationSubringCriterion V) (x y : K) (a b : Vˣ) :
    criterionComparison V hV
        (((a : V) : K) * x) (((b : V) : K) * y) ↔
      criterionComparison V hV x y := by
  classical
  change (((a : V) : K) * x) / (((b : V) : K) * y) ∈ V ↔ x / y ∈ V
  have ha0 : ((a : V) : K) ≠ 0 := by
    intro h
    apply a.ne_zero
    exact Subtype.ext h
  have hb0 : ((b : V) : K) ≠ 0 := by
    intro h
    apply b.ne_zero
    exact Subtype.ext h
  have habV : ((a : V) : K) / ((b : V) : K) ∈ V := by
    have hmem : (((a : V) * ((b⁻¹ : Vˣ) : V) : V) : K) ∈ V :=
      SetLike.coe_mem _
    change ((a : V) : K) * (((b⁻¹ : Vˣ) : V) : K) ∈ V at hmem
    have hbinv : (((b⁻¹ : Vˣ) : V) : K) * ((b : V) : K) = 1 := by
      exact congrArg (fun z : V => (z : K)) b.inv_val
    rw [eq_inv_of_mul_eq_one_left hbinv] at hmem
    simpa [div_eq_mul_inv] using hmem
  have hbaV : ((b : V) : K) / ((a : V) : K) ∈ V := by
    have hmem : (((b : V) * ((a⁻¹ : Vˣ) : V) : V) : K) ∈ V :=
      SetLike.coe_mem _
    change ((b : V) : K) * (((a⁻¹ : Vˣ) : V) : K) ∈ V at hmem
    have hainv : (((a⁻¹ : Vˣ) : V) : K) * ((a : V) : K) = 1 := by
      exact congrArg (fun z : V => (z : K)) a.inv_val
    rw [eq_inv_of_mul_eq_one_left hainv] at hmem
    simpa [div_eq_mul_inv] using hmem
  constructor
  · intro h
    have hxy : x / y = (((b : V) : K) / ((a : V) : K)) *
        ((((a : V) : K) * x) / (((b : V) : K) * y)) := by
      field_simp [ha0, hb0]
    rw [hxy]
    exact V.mul_mem hbaV h
  · intro h
    have hxy : (((a : V) : K) * x) / (((b : V) : K) * y) =
        (((a : V) : K) / ((b : V) : K)) * (x / y) := by
      field_simp [ha0, hb0]
    rw [hxy]
    exact V.mul_mem habV h

theorem criterionComparison_total (V : Subring K)
    (hV : HasValuationSubringCriterion V) (x y : K) :
    criterionComparison V hV x y ∨ criterionComparison V hV y x := by
  change x / y ∈ V ∨ y / x ∈ V
  rcases hV (x / y) with h | h
  · exact Or.inl h
  · exact Or.inr (by simpa [div_eq_mul_inv] using h)

theorem criterionReconstructedValuation_addition_inequality (V : Subring K)
    (hV : HasValuationSubringCriterion V) (x y : K) :
    criterionReconstructedValuation V hV (x + y) ≤
      max (criterionReconstructedValuation V hV x)
        (criterionReconstructedValuation V hV y) := by
  exact map_add_le_max (criterionReconstructedValuation V hV) x y

theorem criterionNormalizedAddition (V : Subring K)
    (hV : HasValuationSubringCriterion V) {x y : K} (hx : x ≠ 0)
    (hle : criterionReconstructedValuation V hV y ≤
      criterionReconstructedValuation V hV x) :
    (x + y) / x = 1 + y / x ∧
      (x + y) / x ∈ V := by
  constructor
  · field_simp [hx]
  · have hyx : criterionReconstructedValuation V hV (y / x) ≤ 1 := by
      rw [map_div₀, div_le_one₀
        ((criterionReconstructedValuation V hV).pos_iff.mpr hx)]
      exact hle
    have hyxV : y / x ∈ V := by
      change y / x ∈ criterionValuationSubring V hV
      exact (ValuationSubring.valuation_le_one_iff
        (criterionValuationSubring V hV) (y / x)).mp hyx
    rw [show (x + y) / x = 1 + y / x by field_simp [hx]]
    exact V.add_mem V.one_mem hyxV

theorem valuationRing_determines_equivalence
    {Γ₁ Γ₂ : Type*} [LinearOrderedCommGroupWithZero Γ₁]
    [LinearOrderedCommGroupWithZero Γ₂]
    (v₁ : Valuation K Γ₁) (v₂ : Valuation K Γ₂)
    (h : v₁.integer = v₂.integer) : v₁.IsEquiv v₂ := by
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  rw [← v₁.mem_integer_iff x, h, v₂.mem_integer_iff x]

theorem valuationRing_determines_additive_equivalence
    {A₁ A₂ : Type*} [LinearOrderedAddCommGroupWithTop A₁]
    [LinearOrderedAddCommGroupWithTop A₂]
    (v₁ : AddValuation K A₁) (v₂ : AddValuation K A₂)
    (h : additiveValuationRingOf v₁ = additiveValuationRingOf v₂) :
    v₁.IsEquiv v₂ := by
  change (AddValuation.toValuation v₁).IsEquiv (AddValuation.toValuation v₂)
  apply valuationRing_determines_equivalence
  simpa [additiveValuationRingOf] using h

end IntrinsicCriterion

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter03
