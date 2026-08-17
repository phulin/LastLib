import LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.Section02TheIntrinsicCharacterization

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

/-! # Book 1, Chapter 3, Section 3.3: Ideals Are Ordered
-/

section OrderedIdeals

variable {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]

/-! ### 3.3. Ideals are ordered -/

theorem ideals_totally_ordered : @Std.Total (Ideal R) (· ≤ ·) := by
  exact PreValuationRing.iff_ideal_total.mp inferInstance

theorem ideals_comparable_from_principal_ideals (I J : Ideal R) :
    I ≤ J ∨ J ≤ I := by
  exact ideals_totally_ordered.total I J

omit [IsDomain R] [ValuationRing R] in
theorem noncomparable_ideals_choose_crossing_elements (I J : Ideal R)
    (hIJ : ¬ I ≤ J) (hJI : ¬ J ≤ I) :
    ∃ x ∈ I, x ∉ J ∧ ∃ y ∈ J, y ∉ I := by
  have hIJ' : ∃ x, x ∈ I ∧ x ∉ J := by
    by_contra h
    apply hIJ
    intro x hx
    by_contra hxJ
    exact h ⟨x, hx, hxJ⟩
  have hJI' : ∃ y, y ∈ J ∧ y ∉ I := by
    by_contra h
    apply hJI
    intro y hy
    by_contra hyI
    exact h ⟨y, hy, hyI⟩
  exact ⟨hIJ'.choose, hIJ'.choose_spec.1, hIJ'.choose_spec.2,
    hJI'.choose, hJI'.choose_spec.1, hJI'.choose_spec.2⟩

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem principal_ideal_order_reverses_valuation (v : Valuation K Γ)
    (x y : valuationRingOf v) :
    Ideal.span ({x} : Set (valuationRingOf v)) ≤ Ideal.span {y} ↔
      v (x : K) ≤ v (y : K) := by
  rw [Ideal.span_singleton_le_span_singleton]
  exact (Valuation.integer.integers v).le_iff_dvd.symm

theorem valuationRingOf_isBezout (v : Valuation K Γ) :
    IsBezout (valuationRingOf v) := by
  infer_instance

theorem valuationRingOf_finitely_generated_ideal_is_principal (v : Valuation K Γ)
    (I : Ideal (valuationRingOf v)) (hI : I.FG) : I.IsPrincipal := by
  exact IsBezout.isPrincipal_of_FG I hI

theorem valuationRingOf_need_not_be_principal_ideal_ring (v : Valuation K Γ)
    (I : Ideal (valuationRingOf v)) (hI : ¬ I.IsPrincipal) :
    ¬ IsPrincipalIdealRing (valuationRingOf v) := by
  intro hPIR
  let : IsPrincipalIdealRing (valuationRingOf v) := hPIR
  exact hI (IsPrincipalIdealRing.principal I)

/- Value sets of ideals, in the additive sign convention. -/

variable {A : Type*} [AddCommGroup A] [LinearOrder A]
  [IsOrderedAddMonoid A]

def additiveValueSet (v : AddValuation K (WithTop A))
    (I : Ideal (additiveValuationRingOf v)) : Set A :=
  {γ | ∃ x : additiveValuationRingOf v,
      x ∈ I ∧ x ≠ 0 ∧ v (x : K) = (γ : WithTop A)}

def hasLeastValue (S : Set A) : Prop :=
  ∃ γ, γ ∈ S ∧ ∀ δ, δ ∈ S → γ ≤ δ

theorem additiveValueSet_nonnegative (v : AddValuation K (WithTop A))
    (I : Ideal (additiveValuationRingOf v)) :
    additiveValueSet v I ⊆ Set.Ici 0 := by
  rintro γ ⟨x, hxI, hx0, hv⟩
  have hnon : 0 ≤ v (x : K) :=
    (mem_additiveValuationRingOf_iff v (x : K)).1 x.property
  rw [hv] at hnon
  simpa using hnon

theorem additiveValueSet_upward_closed_on_realized_values
    (v : AddValuation K (WithTop A)) (I : Ideal (additiveValuationRingOf v))
    {γ δ : A} (hγ : γ ∈ additiveValueSet v I)
    (hδ : ∃ z : K, z ≠ 0 ∧ v z = (δ : WithTop A)) (hγδ : γ ≤ δ) :
    δ ∈ additiveValueSet v I := by
  rcases hγ with ⟨x, hxI, hx0, hxv⟩
  rcases hδ with ⟨z, hz0, hzv⟩
  have hzx : 0 ≤ v (z / (x : K)) := by
    rw [AddValuation.map_div, hzv, hxv,
      ← WithTop.LinearOrderedAddCommGroup.coe_sub]
    norm_cast
    exact sub_nonneg.mpr hγδ
  let c : additiveValuationRingOf v :=
    ⟨z / (x : K), (mem_additiveValuationRingOf_iff v _).2 hzx⟩
  have hγ0 : 0 ≤ γ := by
    have hxnon : 0 ≤ v (x : K) :=
      (mem_additiveValuationRingOf_iff v (x : K)).1 x.property
    rw [hxv] at hxnon
    exact WithTop.coe_nonneg.mp hxnon
  have hδ0 : 0 ≤ δ := hγ0.trans hγδ
  let z' : additiveValuationRingOf v :=
    ⟨z, (mem_additiveValuationRingOf_iff v _).2 (by
      rw [hzv]
      exact WithTop.coe_nonneg.mpr hδ0)⟩
  have hz'0 : z' ≠ 0 := by
    intro h
    apply hz0
    exact congrArg Subtype.val h
  refine ⟨z', ?_, hz'0, hzv⟩
  have hmul := I.mul_mem_left c hxI
  have hcx : c * x = z' := by
    apply Subtype.ext
    change (z / (x : K)) * (x : K) = z
    field_simp [hx0]
  rw [← hcx]
  exact hmul

/- An upward-closed, nonnegative value cut and the ideal it determines. -/

structure AdditiveValueCut (A : Type*) [AddCommGroup A] [LinearOrder A]
    [IsOrderedAddMonoid A] where
  carrier : Set A
  nonnegative : ∀ {γ}, γ ∈ carrier → 0 ≤ γ
  upward : ∀ {γ δ}, γ ∈ carrier → γ ≤ δ → δ ∈ carrier
  add_nonnegative : ∀ {γ δ}, γ ∈ carrier → 0 ≤ δ → γ + δ ∈ carrier

noncomputable def idealOfValueCut (v : AddValuation K (WithTop A))
    (S : AdditiveValueCut A) : Ideal (additiveValuationRingOf v) :=
  { carrier := {x : additiveValuationRingOf v | x = 0 ∨
        ∃ γ, γ ∈ S.carrier ∧ v (x : K) = (γ : WithTop A)}
    zero_mem' := by
      exact Or.inl rfl
    add_mem' := by
      intro a b ha hb
      change a = 0 ∨ ∃ γ, γ ∈ S.carrier ∧ v (a : K) = (γ : WithTop A) at ha
      change b = 0 ∨ ∃ γ, γ ∈ S.carrier ∧ v (b : K) = (γ : WithTop A) at hb
      rcases ha with rfl | ⟨γ, hγ, hav⟩
      · simpa using hb
      rcases hb with rfl | ⟨δ, hδ, hbv⟩
      · simpa using Or.inr ⟨γ, hγ, hav⟩
      by_cases hab : a + b = 0
      · exact Or.inl hab
      right
      have habK : ((a + b : additiveValuationRingOf v) : K) ≠ 0 := by
        intro hzero
        apply hab
        exact Subtype.ext hzero
      obtain ⟨ε, hε⟩ := WithTop.ne_top_iff_exists.mp
        (v.ne_top_iff.mpr habK)
      rcases AddValuation.map_add' v a b with h | h
      · have hγε : γ ≤ ε := by
          apply WithTop.coe_le_coe.mp
          rw [← hav, hε]
          exact h
        exact ⟨ε, S.upward hγ hγε, hε.symm⟩
      · have hδε : δ ≤ ε := by
          apply WithTop.coe_le_coe.mp
          rw [← hbv, hε]
          exact h
        exact ⟨ε, S.upward hδ hδε, hε.symm⟩
    smul_mem' := by
      intro c a ha
      change a = 0 ∨ ∃ γ, γ ∈ S.carrier ∧ v (a : K) = (γ : WithTop A) at ha
      change c * a = 0 ∨ ∃ γ, γ ∈ S.carrier ∧
        v ((c * a : additiveValuationRingOf v) : K) = (γ : WithTop A)
      rcases ha with rfl | ⟨γ, hγ, hav⟩
      · simp
      by_cases hc : c = 0
      · simp [hc]
      have hcK : (c : K) ≠ 0 := by
        intro hzero
        apply hc
        exact Subtype.ext hzero
      obtain ⟨δ, hδ⟩ := WithTop.ne_top_iff_exists.mp (v.ne_top_iff.mpr hcK)
      have hc0 : 0 ≤ δ := by
        have hcv : 0 ≤ v (c : K) := (mem_additiveValuationRingOf_iff v (c : K)).1 c.property
        rw [← hδ] at hcv
        exact WithTop.coe_nonneg.mp hcv
      right
      refine ⟨γ + δ, S.add_nonnegative hγ hc0, ?_⟩
      change v ((c : K) * (a : K)) = (↑(γ + δ) : WithTop A)
      rw [AddValuation.map_mul, ← hδ, hav, ← WithTop.coe_add]
      simp [add_comm]
  }

theorem idealOfValueCut_mem_iff (v : AddValuation K (WithTop A))
    (S : AdditiveValueCut A)
    (x : additiveValuationRingOf v) :
    x ∈ idealOfValueCut v S ↔
      x = 0 ∨ ∃ γ, γ ∈ S.carrier ∧ v (x : K) = (γ : WithTop A) := by
  rfl

theorem idealOfValueCut_valueSet (v : AddValuation K (WithTop A))
    (S : AdditiveValueCut A)
    (hreal : ∀ {γ}, γ ∈ S.carrier → ∃ x : K, x ≠ 0 ∧
      v x = (γ : WithTop A)) :
    additiveValueSet v (idealOfValueCut v S) = S.carrier := by
  classical
  ext γ
  constructor
  · rintro ⟨x, hxI, hx0, hxv⟩
    rcases (idealOfValueCut_mem_iff v S x).1 hxI with hzero | ⟨δ, hδ, hxδ⟩
    · exact False.elim (hx0 hzero)
    · have hγδ : γ = δ := WithTop.coe_eq_coe.mp (hxv.symm.trans hxδ)
      simpa [hγδ] using hδ
  · intro hγ
    rcases hreal hγ with ⟨z, hz0, hzv⟩
    have hzV : 0 ≤ v z := by
      rw [hzv]
      exact WithTop.coe_nonneg.mpr (S.nonnegative hγ)
    let x : additiveValuationRingOf v := ⟨z, hzV⟩
    refine ⟨x, ?_, ?_, hzv⟩
    · exact (idealOfValueCut_mem_iff v S x).2
        (Or.inr ⟨γ, hγ, hzv⟩)
    · intro hx
      apply hz0
      exact congrArg Subtype.val hx

theorem principal_additiveValueSet_has_least
    (v : AddValuation K (WithTop A)) (x : additiveValuationRingOf v)
    (hx : x ≠ 0) :
    hasLeastValue (additiveValueSet v (Ideal.span ({x} : Set (additiveValuationRingOf v)))) := by
  classical
  have hxK : (x : K) ≠ 0 := by
    intro h
    apply hx
    exact Subtype.ext h
  obtain ⟨γ, hγ⟩ := WithTop.ne_top_iff_exists.mp (v.ne_top_iff.mpr hxK)
  refine ⟨γ, ?_, ?_⟩
  · exact ⟨x, Ideal.mem_span_singleton.mpr ⟨1, by simp⟩, hx, hγ.symm⟩
  · intro δ hδ
    rcases hδ with ⟨z, hzI, hz0, hzv⟩
    rcases Ideal.mem_span_singleton'.mp hzI with ⟨c, hcz⟩
    have hczK : (c : K) * (x : K) = (z : K) :=
      congrArg (fun q : additiveValuationRingOf v => (q : K)) hcz
    have hcv : 0 ≤ v (c : K) :=
      (mem_additiveValuationRingOf_iff v (c : K)).1 c.property
    have hvle : v (x : K) ≤ v (z : K) := by
      rw [← hczK, AddValuation.map_mul]
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right hcv (v (x : K))
    rw [← hγ, hzv] at hvle
    exact WithTop.coe_le_coe.mp hvle

theorem valueCut_without_least_gives_nonprincipal_ideal
    (v : AddValuation K (WithTop A)) (S : AdditiveValueCut A)
    (hreal : ∀ {γ}, γ ∈ S.carrier → ∃ x : K, x ≠ 0 ∧
      v x = (γ : WithTop A)) (hne : S.carrier.Nonempty)
    (hleast : ¬ hasLeastValue S.carrier) :
    ¬ (idealOfValueCut v S).IsPrincipal := by
  classical
  intro hP
  rcases hP with ⟨x, hxI⟩
  have hx0 : x ≠ 0 := by
    intro hx
    obtain ⟨γ, hγ⟩ := hne
    have hγ' : γ ∈ additiveValueSet v (idealOfValueCut v S) := by
      rw [idealOfValueCut_valueSet v S hreal]
      exact hγ
    rcases hγ' with ⟨z, hzI, hz0, _⟩
    rw [hxI, hx] at hzI
    exact hz0 (by simpa using hzI)
  obtain ⟨γ, hγ, hγleast⟩ :=
    principal_additiveValueSet_has_least v x hx0
  apply hleast
  refine ⟨γ, ?_, ?_⟩
  · rw [← idealOfValueCut_valueSet v S hreal]
    rw [hxI]
    exact hγ
  · intro δ hδ
    apply hγleast
    have hδI : δ ∈ additiveValueSet v (idealOfValueCut v S) := by
      rw [idealOfValueCut_valueSet v S hreal]
      exact hδ
    simpa only [hxI] using hδI

theorem integer_upward_closed_nonnegative_set_has_least (S : Set ℤ)
    (hne : S.Nonempty) (hnonneg : S ⊆ Set.Ici 0)
    : hasLeastValue S := by
  classical
  rcases Int.exists_least_of_bdd
      (P := fun z : ℤ => z ∈ S)
      ⟨0, fun z hz => hnonneg hz⟩ hne with ⟨lb, hlb, hleast⟩
  exact ⟨lb, hlb, hleast⟩
theorem discrete_additive_valuation_nonzero_ideal_is_principal
    (v : AddValuation K (WithTop ℤ)) (I : Ideal (additiveValuationRingOf v))
    (hI : I ≠ ⊥) :
    ∃ x : additiveValuationRingOf v, x ≠ 0 ∧
      I = Ideal.span ({x} : Set (additiveValuationRingOf v)) := by
  classical
  have hnonzero : ∃ x : additiveValuationRingOf v, x ∈ I ∧ x ≠ 0 := by
    by_contra h
    apply hI
    ext z
    constructor
    · intro hz
      have hz0 : z = 0 := by
        by_contra hz0
        exact h ⟨z, hz, hz0⟩
      simp [hz0]
    · intro hz
      have hz0 : z = 0 := by simpa using hz
      simp [hz0]
  have hne : (additiveValueSet v I).Nonempty := by
    obtain ⟨x, hxI, hx0⟩ := hnonzero
    obtain ⟨γ, hγ⟩ := WithTop.ne_top_iff_exists.mp
      (v.ne_top_iff.mpr (by
        intro hxK
        apply hx0
        exact Subtype.ext hxK))
    exact ⟨γ, ⟨x, hxI, hx0, hγ.symm⟩⟩
  have hnonneg : additiveValueSet v I ⊆ Set.Ici 0 := by
    intro γ hγ
    rcases hγ with ⟨x, hxI, hx0, hxv⟩
    change 0 ≤ γ
    apply WithTop.coe_nonneg.mp
    rw [← hxv]
    exact (mem_additiveValuationRingOf_iff v (x : K)).1 x.property
  obtain ⟨γ, hγ, hγleast⟩ := Int.exists_least_of_bdd
      (P := fun z : ℤ => z ∈ additiveValueSet v I)
      ⟨0, fun z hz => hnonneg hz⟩ hne
  rcases hγ with ⟨x, hxI, hx0, hxv⟩
  refine ⟨x, hx0, ?_⟩
  apply le_antisymm
  · intro z hzI
    by_cases hz0 : z = 0
    · simp [hz0]
    obtain ⟨δ, hδ⟩ := WithTop.ne_top_iff_exists.mp
      (v.ne_top_iff.mpr (by
        intro hzK
        apply hz0
        exact Subtype.ext hzK))
    have hδmem : δ ∈ additiveValueSet v I := ⟨z, hzI, hz0, hδ.symm⟩
    have hγδ : γ ≤ δ := hγleast δ hδmem
    have hxK : (x : K) ≠ 0 := by
      intro hxK
      apply hx0
      exact Subtype.ext hxK
    have hdiv : 0 ≤ v ((z : K) / (x : K)) := by
      rw [AddValuation.map_div, ← hδ, hxv,
        ← WithTop.LinearOrderedAddCommGroup.coe_sub]
      norm_cast
      exact sub_nonneg.mpr hγδ
    let c : additiveValuationRingOf v :=
      ⟨(z : K) / (x : K), hdiv⟩
    apply Ideal.mem_span_singleton'.mpr
    refine ⟨c, ?_⟩
    apply Subtype.ext
    change ((z : K) / (x : K)) * (x : K) = (z : K)
    exact div_mul_cancel₀ _ hxK
  · exact I.span_singleton_le_iff_mem.mpr hxI

def strictUpperValueCut (α : A) (hα : 0 ≤ α) : AdditiveValueCut A :=
  { carrier := {γ | α < γ}
    nonnegative := by
      intro γ hγ
      exact hα.trans hγ.le
    upward := by
      intro γ δ hγ hγδ
      exact lt_of_lt_of_le hγ hγδ
    add_nonnegative := by
      intro γ δ hγ hδ
      exact lt_of_lt_of_le hγ (le_add_of_nonneg_right hδ) }
theorem dense_strict_cut_has_no_least {A : Type*} [LinearOrder A] [DenselyOrdered A]
    (α : A) :
    ¬ hasLeastValue {γ : A | α < γ} := by
  rintro ⟨γ, hγ, hleast⟩
  obtain ⟨δ, hαδ, hδγ⟩ := exists_between hγ
  exact (not_lt_of_ge (hleast δ hαδ)) hδγ

theorem strictUpperRationalValueCut_is_nonprincipal
    (v : AddValuation K (WithTop ℚ)) (α : ℚ) (hα : 0 ≤ α)
    (hreal : ∀ {γ}, γ ∈ (strictUpperValueCut α hα).carrier → ∃ x : K, x ≠ 0 ∧
      v x = (γ : WithTop ℚ)) :
    ¬ (idealOfValueCut v (strictUpperValueCut α hα)).IsPrincipal := by
  classical
  have hne : ({γ : ℚ | α < γ}).Nonempty := by
    exact ⟨α + 1, by simp⟩
  apply valueCut_without_least_gives_nonprincipal_ideal v
    (strictUpperValueCut α hα) hreal hne
  exact dense_strict_cut_has_no_least α
theorem rational_dense_value_cut_is_nonprincipal
    (v : AddValuation K (WithTop ℚ)) (S : AdditiveValueCut ℚ)
    (hreal : ∀ {γ}, γ ∈ S.carrier → ∃ x : K, x ≠ 0 ∧
      v x = (γ : WithTop ℚ)) (hne : S.carrier.Nonempty)
    (hleast : ¬ hasLeastValue S.carrier) :
    ¬ (idealOfValueCut v S).IsPrincipal := by
  classical
  exact valueCut_without_least_gives_nonprincipal_ideal v S hreal hne hleast

end OrderedIdeals

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter03
