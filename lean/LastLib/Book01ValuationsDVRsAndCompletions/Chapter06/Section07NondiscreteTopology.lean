import LastLib.Book01ValuationsDVRsAndCompletions.Chapter06.Section01BallsAndTheStrongTriangleInequality
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter06

open Set Filter Function
open scoped BigOperators Pointwise Topology WithZero NNReal Valued PowerSeries

noncomputable section

/-! # Book 1, Chapter 6, Section 6.7: Nondiscrete Topology
-/

/-! ### 6.7 Nondiscrete topology -/

section Nondiscrete

variable {K : Type*} [Field K]
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- The real absolute value associated to a rank-one valuation. -/
noncomputable def chapter06RankOneAbsoluteValue
    (v : Valuation K Γ₀) [v.RankOne] : AbsoluteValue K ℝ :=
  { toMulHom :=
      { toFun := v.norm
        map_mul' := by
          intro x y
          simp only [Valuation.norm, ← NNReal.coe_mul, map_mul] }
    nonneg' := v.norm_nonneg
    eq_zero' := by
      intro x
      exact ⟨v.norm_eq_zero, fun hx => by simp [hx, Valuation.norm]⟩
    add_le' := by
      intro x y
      exact (v.norm_add_le x y).trans
        (max_le_add_of_nonneg (v.norm_nonneg x) (v.norm_nonneg y)) }

/-- The absolute value associated to a rank-one valuation is nonarchimedean. -/
theorem chapter06_rank_one_absolute_value_is_nonarchimedean
    (v : Valuation K Γ₀) [v.RankOne] :
    IsNonarchimedean (chapter06RankOneAbsoluteValue v) := by
  intro x y
  change v.norm (x + y) ≤ max (v.norm x) (v.norm y)
  exact v.norm_add_le x y

/-- A dense range of radii for the rank-one norm. -/
def chapter06DenseRankOneValueRange (v : Valuation K Γ₀) [v.RankOne] : Prop :=
  ∀ r s : ℝ, 0 < r → r < s →
    ∃ x : K, x ≠ 0 ∧ r < v.norm x ∧ v.norm x < s

/-- The rank-one valuation ring is the closed unit ball. -/
def chapter06RankOneValuationRingSet (v : Valuation K Γ₀) [v.RankOne] : Set K :=
  {x | v.norm x ≤ 1}

/-- The rank-one maximal ideal is the open unit ball, after coercion to the field. -/
def chapter06RankOneMaximalIdealImage (v : Valuation K Γ₀) [v.RankOne] : Set K :=
  ((fun x : v.valuationSubring => (x : K)) ''
    (IsLocalRing.maximalIdeal v.valuationSubring : Set v.valuationSubring))

/-- Closed-unit-ball and open-unit-ball descriptions of the valuation ring and maximal ideal. -/
theorem chapter06_rank_one_unit_ball_and_maximal_ball
    (v : Valuation K Γ₀) [v.RankOne] :
    (v.valuationSubring : Set K) = chapter06RankOneValuationRingSet v ∧
      chapter06RankOneMaximalIdealImage v = {x | v.norm x < 1} := by
  let : Valued K Γ₀ := Valued.mk' v
  constructor
  · ext x
    change x ∈ v.valuationSubring ↔ v.norm x ≤ 1
    rw [Valuation.mem_valuationSubring_iff]
    exact (Valued.toNormedField.norm_le_one_iff (x := x)).symm
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Valued.toNormedField.norm_lt_one_iff (x := (y : K))).2
        ((Valuation.mem_maximalIdeal_iff (K := K) v).1 hy)
    · intro hx
      have hy : v x ≤ 1 :=
        ((Valued.toNormedField.norm_lt_one_iff (x := x)).1 hx).le
      let y : v.valuationSubring := ⟨x, by
        exact (Valuation.mem_valuationSubring_iff v x).2 hy⟩
      refine ⟨y, ?_, rfl⟩
      exact (Valuation.mem_maximalIdeal_iff (K := K) v).2
        ((Valued.toNormedField.norm_lt_one_iff (x := x)).1 hx)

/-- Valuation neighborhoods inside the valuation ring. -/
def chapter06RankOneValuationNeighborhood
    (v : Valuation K Γ₀) [v.RankOne] (r : ℝ) : Set v.valuationSubring :=
  {x | v.norm (x : K) < r}

/-- Cofinality of powers of the maximal ideal among valuation neighborhoods. -/
def chapter06PowersCofinalAmongValuationNeighborhoods
    (v : Valuation K Γ₀) [v.RankOne] : Prop :=
  ∀ r : ℝ, 0 < r → ∃ n : ℕ,
    (((IsLocalRing.maximalIdeal v.valuationSubring) ^ n :
      Ideal v.valuationSubring) : Set v.valuationSubring) ⊆
      chapter06RankOneValuationNeighborhood v r

/-- A factorization hypothesis expressing divisibility of positive values. -/
def chapter06MaximalIdealFactors
    (v : Valuation K Γ₀) : Prop :=
  ∀ x : v.valuationSubring,
    x ∈ IsLocalRing.maximalIdeal v.valuationSubring →
      ∃ y z : v.valuationSubring,
        y ∈ IsLocalRing.maximalIdeal v.valuationSubring ∧
          z ∈ IsLocalRing.maximalIdeal v.valuationSubring ∧ y * z = x

/-- Factoring every maximal-ideal element gives `𝔪² = 𝔪`. -/
theorem chapter06_maximalIdeal_idempotent_of_factors
    (v : Valuation K Γ₀) (hfactor : chapter06MaximalIdealFactors v) :
    IsLocalRing.maximalIdeal v.valuationSubring ^ 2 =
      IsLocalRing.maximalIdeal v.valuationSubring := by
  let m := IsLocalRing.maximalIdeal v.valuationSubring
  apply le_antisymm
  · simpa [pow_two] using (Ideal.mul_le_left : m * m ≤ m)
  · intro x hx
    obtain ⟨y, z, hy, hz, hxy⟩ := hfactor x hx
    rw [← hxy]
    simpa [pow_two] using (Ideal.mul_mem_mul hy hz)

/-- A value-splitting condition for positive values. -/
def chapter06PositiveValueSplitting (v : Valuation K Γ₀) [v.RankOne] : Prop :=
  ∀ x : K, 0 < v x → v x < 1 →
    ∃ y z : K, 0 < v y ∧ 0 < v z ∧ v y < 1 ∧ v z < 1 ∧ v x = v y * v z

/-- Splitting positive values yields the factorization of maximal-ideal elements. -/
theorem chapter06_positive_value_splitting_implies_maximalIdeal_factors
    (v : Valuation K Γ₀) [v.RankOne]
    (hsplit : chapter06PositiveValueSplitting v) :
    chapter06MaximalIdealFactors v := by
  intro x hx
  by_cases hzero : (x : K) = 0
  · have hx0 : x = 0 := Subtype.ext hzero
    subst x
    refine ⟨0, 0, ?_, ?_, ?_⟩
    · exact (Valuation.mem_maximalIdeal_iff (K := K) v).2 (by simp)
    · exact (Valuation.mem_maximalIdeal_iff (K := K) v).2 (by simp)
    · simp
  · have hxpos : 0 < v (x : K) := (v.pos_iff).2 hzero
    have hxlt : v (x : K) < 1 :=
      (Valuation.mem_maximalIdeal_iff (K := K) v).1 hx
    obtain ⟨y, z, hypos, hzpos, hylt, hzlt, hval⟩ := hsplit (x : K) hxpos hxlt
    have hy0 : y ≠ 0 := (v.pos_iff).mp hypos
    let y' : v.valuationSubring :=
      ⟨y, (Valuation.mem_valuationSubring_iff v y).2 hylt.le⟩
    have hquotval : v ((x : K) / y) = v z := by
      rw [map_div₀, hval]
      field_simp [ne_of_gt hypos]
    let z' : v.valuationSubring :=
      ⟨(x : K) / y, (Valuation.mem_valuationSubring_iff v _).2
        (by rw [hquotval]; exact hzlt.le)⟩
    refine ⟨y', z', ?_, ?_, ?_⟩
    · exact (Valuation.mem_maximalIdeal_iff (K := K) v).2 hylt
    · exact (Valuation.mem_maximalIdeal_iff (K := K) v).2 (by
        rw [hquotval]
        exact hzlt)
    · apply Subtype.ext
      change y * ((x : K) / y) = (x : K)
      field_simp [hy0]

/-- In the value-splitting situation the maximal ideal is idempotent. -/
theorem chapter06_positive_value_splitting_implies_maximalIdeal_idempotent
    (v : Valuation K Γ₀) [v.RankOne]
    (hsplit : chapter06PositiveValueSplitting v) :
    IsLocalRing.maximalIdeal v.valuationSubring ^ 2 =
      IsLocalRing.maximalIdeal v.valuationSubring := by
  exact chapter06_maximalIdeal_idempotent_of_factors v
    (chapter06_positive_value_splitting_implies_maximalIdeal_factors v hsplit)

/-- Idempotent maximal ideals obstruct cofinality of powers in a dense valuation topology. -/
theorem chapter06_idempotent_maximalIdeal_not_power_cofinal
    (v : Valuation K Γ₀) [v.RankOne]
    (hid : IsLocalRing.maximalIdeal v.valuationSubring ^ 2 =
      IsLocalRing.maximalIdeal v.valuationSubring)
    (hnot : ∃ r : ℝ, 0 < r ∧
      ¬ ((IsLocalRing.maximalIdeal v.valuationSubring : Set v.valuationSubring) ⊆
        chapter06RankOneValuationNeighborhood v r)) :
    ¬ chapter06PowersCofinalAmongValuationNeighborhoods v := by
  intro hcofinal
  obtain ⟨r, hr, hmr⟩ := hnot
  obtain ⟨n, hn⟩ := hcofinal r hr
  have hp : ∀ n : ℕ, 0 < n →
      IsLocalRing.maximalIdeal v.valuationSubring ^ n =
        IsLocalRing.maximalIdeal v.valuationSubring := by
    intro n hnpos
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
    induction q with
    | zero => simp
    | succ q ih =>
        rw [pow_succ, ih (Nat.succ_pos q)]
        simpa [pow_two] using hid
  by_cases hnzero : n = 0
  · apply hmr
    subst n
    intro x hx
    exact hn (by
      change x ∈ ((IsLocalRing.maximalIdeal v.valuationSubring ^ 0 :
        Ideal v.valuationSubring) : Set v.valuationSubring)
      simp)
  · apply hmr
    intro x hx
    have : x ∈ ((IsLocalRing.maximalIdeal v.valuationSubring ^ n :
        Ideal v.valuationSubring) : Set v.valuationSubring) := by
      rw [hp n (Nat.pos_of_ne_zero hnzero)]
      exact hx
    exact hn this

/- A dense value range supplies the obstruction required by the idempotence lemma. -/
theorem chapter06_dense_value_range_and_idempotence_obstruct_power_cofinality
    (v : Valuation K Γ₀) [v.RankOne]
    (hdense : chapter06DenseRankOneValueRange v)
    (hid : IsLocalRing.maximalIdeal v.valuationSubring ^ 2 =
      IsLocalRing.maximalIdeal v.valuationSubring) :
    ¬ chapter06PowersCofinalAmongValuationNeighborhoods v := by
  let : Valued K Γ₀ := Valued.mk' v
  have hnot : ∃ r : ℝ, 0 < r ∧
      ¬ ((IsLocalRing.maximalIdeal v.valuationSubring : Set v.valuationSubring) ⊆
        chapter06RankOneValuationNeighborhood v r) := by
    refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
    obtain ⟨x, _hx0, hlow, hhigh⟩ := hdense (1 / 2) 1 (by norm_num) (by norm_num)
    let y : v.valuationSubring :=
      ⟨x, (Valued.toNormedField.norm_le_one_iff (x := x)).mp hhigh.le⟩
    have hy : y ∈ IsLocalRing.maximalIdeal v.valuationSubring := by
      apply (Valuation.mem_maximalIdeal_iff (K := K) v).2
      exact (Valued.toNormedField.norm_lt_one_iff (x := x)).1 hhigh
    intro hsubset
    have hy' := hsubset hy
    change v.norm (y : K) < (1 / 2 : ℝ) at hy'
    exact (not_lt_of_ge hlow.le) hy'
  exact chapter06_idempotent_maximalIdeal_not_power_cofinal v hid hnot

/-- Failure of power cofinality forces the valuation and `𝔪`-adic topologies to differ. -/
theorem chapter06_nondiscrete_madic_topology_not_equal_of_not_power_cofinal
    (v : Valuation K Γ₀) [v.RankOne]
    (hnotcofinal : ¬ chapter06PowersCofinalAmongValuationNeighborhoods v) :
    TopologicalSpace.induced ((↑) : v.valuationSubring → K)
        (chapter06RankOneAbsoluteValue v).uniformSpace.toTopologicalSpace ≠
      (IsLocalRing.maximalIdeal v.valuationSubring).adicTopology := by
  intro heq
  apply hnotcofinal
  intro r hr
  have hopen : @IsOpen K (chapter06RankOneAbsoluteValue v).uniformSpace.toTopologicalSpace
      {x | v.norm x < r} := by
    convert chapter06_openBall_isOpen (chapter06RankOneAbsoluteValue v) 0 r using 1
    ext x
    change v.norm x < r ↔ v.norm (x - 0) < r
    simp
  let : TopologicalSpace v.valuationSubring :=
    TopologicalSpace.induced ((↑) : v.valuationSubring → K)
      (chapter06RankOneAbsoluteValue v).uniformSpace.toTopologicalSpace
  have hopen' : @IsOpen v.valuationSubring
      (TopologicalSpace.induced ((↑) : v.valuationSubring → K)
        (chapter06RankOneAbsoluteValue v).uniformSpace.toTopologicalSpace)
      (chapter06RankOneValuationNeighborhood v r) := by
    refine (isOpen_induced_iff
      (t := (chapter06RankOneAbsoluteValue v).uniformSpace.toTopologicalSpace)
      (f := fun x : v.valuationSubring => (x : K))).2 ?_
    refine ⟨{x | v.norm x < r}, hopen, ?_⟩
    ext x
    rfl
  have hzero : (0 : v.valuationSubring) ∈
      chapter06RankOneValuationNeighborhood v r := by
    change v.norm (0 : K) < r
    simpa [Valuation.norm] using hr
  have hmem := hopen'.mem_nhds hzero
  rw [heq] at hmem
  obtain ⟨n, -, hn⟩ :=
    (IsLocalRing.maximalIdeal v.valuationSubring).hasBasis_nhds_zero_adic.mem_iff.mp hmem
  exact ⟨n, hn⟩

/-- The compatible-family description of the adic completion. -/
theorem chapter06_adic_completion_is_compatible_family
    {A : Type*} [CommRing A] (m : Ideal A) (x : AdicCompletion m A)
    {i j : ℕ} (hij : i ≤ j) :
    AdicCompletion.transitionMap m A hij (x.val j) = x.val i := by
  exact x.property hij

/-- Completion notation for the topology induced by a real absolute value. -/
noncomputable def chapter06ValuationCompletion
    {A : Subring K} (v : AbsoluteValue K ℝ) :=
  @UniformSpace.Completion A
    (UniformSpace.comap ((↑) : A → K) v.uniformSpace)

/-- The inverse-limit topology on compatible families, with discrete coordinates. -/
@[instance_reducible]
def chapter06AdicCompletionTopology
    {A : Type*} [CommRing A] (m : Ideal A) :
    TopologicalSpace (AdicCompletion m A) :=
    TopologicalSpace.induced (fun x : AdicCompletion m A => x.1)
    (@Pi.topologicalSpace ℕ
      (fun n : ℕ => A ⧸ (m ^ n • (⊤ : Submodule A A))) (fun _ => ⊥))

/-- A topological identification of the valuation-ring completion with the adic completion,
    compatible with the dense maps from the original ring. -/
structure Chapter06ValuationCompletionIdentification
    {A : Subring K} (v : AbsoluteValue K ℝ) (m : Ideal A) where
  toEquiv : chapter06ValuationCompletion (A := A) v ≃ AdicCompletion m A
  continuous_toEquiv :
    @Continuous (chapter06ValuationCompletion (A := A) v) (AdicCompletion m A)
      (@UniformSpace.Completion.uniformSpace A
        (UniformSpace.comap ((↑) : A → K) v.uniformSpace)).toTopologicalSpace
      (chapter06AdicCompletionTopology m) toEquiv
  continuous_inv :
    @Continuous (AdicCompletion m A) (chapter06ValuationCompletion (A := A) v)
      (chapter06AdicCompletionTopology m)
      (@UniformSpace.Completion.uniformSpace A
        (UniformSpace.comap ((↑) : A → K) v.uniformSpace)).toTopologicalSpace
      toEquiv.symm
  commutes_with_completion :
    ∀ a : A,
      toEquiv ((a : @UniformSpace.Completion A
        (UniformSpace.comap ((↑) : A → K) v.uniformSpace)) :
        chapter06ValuationCompletion (A := A) v) =
        AdicCompletion.of m A a

/-- A proposition recording an identification of valuation and adic completions. -/
def chapter06ValuationCompletionIsAdic
    {A : Subring K} (v : AbsoluteValue K ℝ) (m : Ideal A) : Prop :=
  Nonempty (Chapter06ValuationCompletionIdentification (A := A) v m)

/-- The discrete/cofinal hypothesis used to compare a valuation completion with an adic one. -/
def chapter06CompletionIdentificationHypothesis
    {A : Subring K} (v : AbsoluteValue K ℝ) (m : Ideal A) : Prop :=
  (∀ x : K, x ∈ (A : Set K) ↔ v x ≤ 1) ∧
    ((IsDiscreteValuationRing A ∧ m.IsMaximal) ∨
      ((∀ r : ℝ, 0 < r → ∃ n : ℕ,
          ((m ^ n : Ideal A) : Set A) ⊆ {x : A | v (x : K) < r}) ∧
        (∀ n : ℕ, ∃ r : ℝ, 0 < r ∧
          {x : A | v (x : K) < r} ⊆ ((m ^ n : Ideal A) : Set A))))

/-- An inverse-limit identification needs a discrete valuation or a cofinal chosen ideal. -/
theorem chapter06_completion_is_inverse_limit_under_discrete_or_cofinal
    {A : Subring K} (v : AbsoluteValue K ℝ) (m : Ideal A)
    (hallowed : chapter06CompletionIdentificationHypothesis v m) :
    chapter06ValuationCompletionIsAdic (A := A) v m := by
  classical
  rcases hallowed with ⟨hA, hcase⟩
  have hcof1 : ∀ r : ℝ, 0 < r → ∃ n : ℕ,
      ((m ^ n : Ideal A) : Set A) ⊆ {x : A | v (x : K) < r} := by
    intro r hr
    rcases hcase with hD | hC
    · have hle : ∀ x y : K, v x ≤ v y → v (x + y) ≤ v y := by
        intro x y hxy
        by_cases hy : y = 0
        · simpa [hy] using hxy
        · have hratio : v (x / y) ≤ 1 := by
            rw [map_div₀, div_le_one₀ (v.pos hy)]
            exact hxy
          have hmem : x / y ∈ (A : Set K) := (hA (x / y)).2 hratio
          have hsum : x / y + 1 ∈ (A : Set K) := A.add_mem hmem A.one_mem
          have hsum_le : v (x / y + 1) ≤ 1 := (hA _).1 hsum
          have hident : x + y = y * (x / y + 1) := by
            field_simp [hy]
          rw [hident, v.map_mul]
          exact (mul_le_mul_of_nonneg_left hsum_le (v.nonneg y)).trans_eq (mul_one _)
      have hna : ∀ x y : K, v (x + y) ≤ max (v x) (v y) := by
        intro x y
        rcases le_total (v x) (v y) with hxy | hyx
        · simpa [max_eq_right hxy] using hle x y hxy
        · simpa [add_comm, max_eq_left hyx] using hle y x hyx
      let w : Valuation K ℝ≥0 :=
        { toMonoidWithZeroHom :=
            { toFun := fun x => ⟨v x, v.nonneg x⟩
              map_one' := by
                apply Subtype.ext
                simp
              map_zero' := by
                apply Subtype.ext
                simp
              map_mul' := by
                intro x y
                apply Subtype.ext
                change v (x * y) = v x * v y
                exact v.map_mul x y }
          map_add_le_max' := by
            intro x y
            change v (x + y) ≤ max (v x) (v y)
            exact hna x y }
      have hw : w.Integers A :=
        { hom_inj := by
            intro a b hab
            apply Subtype.ext
            exact hab
          map_le_one := by
            intro a
            apply NNReal.coe_le_coe.2
            change v (a : K) ≤ 1
            exact (hA (a : K)).1 a.property
          exists_of_le_one := by
            intro x hx
            have hx' : v x ≤ 1 := by
              exact NNReal.coe_le_coe.1 hx
            exact ⟨⟨x, (hA x).2 hx'⟩, rfl⟩ }
      let : IsFractionRing A K := hw.isFractionRing
      let : IsDiscreteValuationRing A := hD.1
      obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
      have hm_eq : m = IsLocalRing.maximalIdeal A :=
        IsLocalRing.eq_maximalIdeal hD.2
      have hm_pow (n : ℕ) : m ^ n = Ideal.span {(π : A) ^ n} := by
        rw [hm_eq, hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
      have hpowset (n : ℕ) :
          ((m ^ n : Ideal A) : Set A) = {x : A | v (x : K) ≤ (v (π : K)) ^ n} := by
        rw [hm_pow, hw.coe_span_singleton_eq_setOfPred_le_v_algebraMap]
        ext x
        change v (x : K) ≤ v ((π : K) ^ n) ↔
          v (x : K) ≤ (v (π : K)) ^ n
        simp
      have hπ0 : (π : K) ≠ 0 := by
        intro h
        apply hπ.ne_zero
        apply Subtype.ext
        exact h
      have hπpos : 0 < v (π : K) := v.pos hπ0
      have hπlt : v (π : K) < 1 := by
        have hπlt' : w (algebraMap A K π) < 1 :=
          hw.valuation_irreducible_lt_one hπ
        change v (π : K) < 1 at hπlt'
        exact hπlt'
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr hπlt
      refine ⟨n, ?_⟩
      intro x hx
      rw [hpowset n] at hx
      exact hx.trans_lt hn
    · exact hC.1 r hr
  have hcof2 : ∀ n : ℕ, ∃ r : ℝ, 0 < r ∧
      {x : A | v (x : K) < r} ⊆ ((m ^ n : Ideal A) : Set A) := by
    intro n
    rcases hcase with hD | hC
    · have hle : ∀ x y : K, v x ≤ v y → v (x + y) ≤ v y := by
        intro x y hxy
        by_cases hy : y = 0
        · simpa [hy] using hxy
        · have hratio : v (x / y) ≤ 1 := by
            rw [map_div₀, div_le_one₀ (v.pos hy)]
            exact hxy
          have hmem : x / y ∈ (A : Set K) := (hA (x / y)).2 hratio
          have hsum : x / y + 1 ∈ (A : Set K) := A.add_mem hmem A.one_mem
          have hsum_le : v (x / y + 1) ≤ 1 := (hA _).1 hsum
          have hident : x + y = y * (x / y + 1) := by
            field_simp [hy]
          rw [hident, v.map_mul]
          exact (mul_le_mul_of_nonneg_left hsum_le (v.nonneg y)).trans_eq (mul_one _)
      have hna : ∀ x y : K, v (x + y) ≤ max (v x) (v y) := by
        intro x y
        rcases le_total (v x) (v y) with hxy | hyx
        · simpa [max_eq_right hxy] using hle x y hxy
        · simpa [add_comm, max_eq_left hyx] using hle y x hyx
      let w : Valuation K ℝ≥0 :=
        { toMonoidWithZeroHom :=
            { toFun := fun x => ⟨v x, v.nonneg x⟩
              map_one' := by
                apply Subtype.ext
                simp
              map_zero' := by
                apply Subtype.ext
                simp
              map_mul' := by
                intro x y
                apply Subtype.ext
                change v (x * y) = v x * v y
                exact v.map_mul x y }
          map_add_le_max' := by
            intro x y
            change v (x + y) ≤ max (v x) (v y)
            exact hna x y }
      have hw : w.Integers A :=
        { hom_inj := by
            intro a b hab
            apply Subtype.ext
            exact hab
          map_le_one := by
            intro a
            apply NNReal.coe_le_coe.2
            change v (a : K) ≤ 1
            exact (hA (a : K)).1 a.property
          exists_of_le_one := by
            intro x hx
            have hx' : v x ≤ 1 := by
              exact NNReal.coe_le_coe.1 hx
            exact ⟨⟨x, (hA x).2 hx'⟩, rfl⟩ }
      let : IsFractionRing A K := hw.isFractionRing
      let : IsDiscreteValuationRing A := hD.1
      obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
      have hm_eq : m = IsLocalRing.maximalIdeal A :=
        IsLocalRing.eq_maximalIdeal hD.2
      have hm_pow (n : ℕ) : m ^ n = Ideal.span {(π : A) ^ n} := by
        rw [hm_eq, hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
      have hpowset (n : ℕ) :
          ((m ^ n : Ideal A) : Set A) = {x : A | v (x : K) ≤ (v (π : K)) ^ n} := by
        rw [hm_pow, hw.coe_span_singleton_eq_setOfPred_le_v_algebraMap]
        ext x
        change v (x : K) ≤ v ((π : K) ^ n) ↔
          v (x : K) ≤ (v (π : K)) ^ n
        simp
      have hπ0 : (π : K) ≠ 0 := by
        intro h
        apply hπ.ne_zero
        apply Subtype.ext
        exact h
      have hπpos : 0 < v (π : K) := v.pos hπ0
      have hπlt : v (π : K) < 1 := by
        have hπlt' : w (algebraMap A K π) < 1 :=
          hw.valuation_irreducible_lt_one hπ
        change v (π : K) < 1 at hπlt'
        exact hπlt'
      refine ⟨(v (π : K)) ^ n, pow_pos hπpos n, ?_⟩
      intro x hx
      rw [hpowset n]
      change v (x : K) < (v (π : K)) ^ n at hx
      exact hx.le
    · exact hC.2 n
  let Q : ℕ → Type _ := fun n =>
    @Quotient (↥A)
      (Submodule.quotientRel (m ^ n • (⊤ : Submodule (↥A) (↥A))))
  let P := ∀ n, Q n
  let C := AdicCompletion m (↥A)
  let (n : ℕ) : TopologicalSpace (Q n) := ⊥
  let (n : ℕ) : UniformSpace (Q n) := ⊥
  let (n : ℕ) : DiscreteTopology (Q n) := by infer_instance
  let : TopologicalSpace P := inferInstance
  let uP : UniformSpace P := Pi.uniformSpace Q
  let : UniformSpace P := uP
  let uC : UniformSpace C := UniformSpace.comap (fun x : C => x.1) uP
  let : TopologicalSpace C := uC.toTopologicalSpace
  let : UniformSpace C := uC
  let uVal : UniformSpace A :=
    UniformSpace.comap ((↑) : A → K) v.uniformSpace
  let f : A → C := AdicCompletion.of m (↥A)
  let S : Set P :=
    {z | ∀ {i j : ℕ} (hij : i ≤ j),
      AdicCompletion.transitionMap m (↥A) hij (z j) = z i}
  have hclosed : @IsClosed P uP.toTopologicalSpace S := by
    rw [show S = ⋂ i : ℕ, ⋂ j : ℕ, ⋂ hij : i ≤ j,
        {z : P | AdicCompletion.transitionMap m (↥A) hij (z j) = z i} by
      ext z
      simp [S]]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_iInter fun hij =>
        isClosed_eq
          (continuous_of_discreteTopology.comp (continuous_apply j))
          (continuous_apply i)
  have hcomplete : @CompleteSpace C uC := by
    change CompleteSpace {z : P // z ∈ S}
    exact hclosed.completeSpace_coe
  have hdense : @DenseRange C uC.toTopologicalSpace A f := by
    rw [denseRange_iff_closure_range]
    apply eq_univ_iff_forall.mpr
    intro x
    rw [mem_closure_iff_nhds]
    intro U hU
    rw [nhds_induced] at hU
    rcases Filter.mem_comap.mp hU with ⟨V, hV, hVU⟩
    rw [nhds_pi] at hV
    rcases Filter.mem_pi'.mp hV with ⟨I, t, ht, hsub⟩
    have hsub' : Set.pi (↑I) (fun i => {x.1 i}) ⊆ V := by
      intro z hz
      apply hsub
      intro i hi
      rw [Set.mem_singleton_iff.mp (hz i hi)]
      exact mem_of_mem_nhds (ht i)
    let N : ℕ := I.sup id
    obtain ⟨a, ha⟩ :=
      Submodule.Quotient.mk_surjective
        (m ^ N • (⊤ : Submodule A A)) (x.1 N)
    have hcoord : ∀ i : ℕ, i ∈ I →
        (AdicCompletion.of m (↥A) a).1 i = x.1 i := by
      intro i hi
      have hiN : i ≤ N := Finset.le_sup (f := id) hi
      calc
        (AdicCompletion.of m (↥A) a).1 i =
            AdicCompletion.transitionMap m (↥A) hiN
              ((AdicCompletion.of m (↥A) a).1 N) := by
                rw [AdicCompletion.of_apply]
                symm
                exact Submodule.factor_mk
                  (Submodule.smul_mono_left (Ideal.pow_le_pow_right hiN)) a
        _ = AdicCompletion.transitionMap m (↥A) hiN (x.1 N) := by
              rw [AdicCompletion.of_apply, Submodule.mkQ_apply, ha]
        _ = x.1 i := x.property hiN
    have haV : (AdicCompletion.of m (↥A) a).1 ∈ V := by
      apply hsub'
      intro i hi
      exact Set.mem_singleton_iff.mpr (hcoord i hi)
    have haU : AdicCompletion.of m (↥A) a ∈ U := hVU haV
    exact ⟨AdicCompletion.of m (↥A) a, ⟨haU, ⟨a, rfl⟩⟩⟩
  have hsmul (n : ℕ) :
      (m ^ n • (⊤ : Submodule A A)) = (m ^ n : Submodule A A) := by
    simp
  have hval :
      (@uniformity A uVal).HasBasis
        (fun r : ℝ => 0 < r)
        (fun r => {p : A × A | v ((p.2 : K) - (p.1 : K)) < r}) := by
    simpa [uVal, uniformity_comap, Prod.map_apply', Set.preimage_ofPred_eq] using
      ((v.hasBasis_uniformity).comap
        (Prod.map ((↑) : A → K) ((↑) : A → K)))
  have hQ (n : ℕ) :
      (@uniformity (Q n) (⊥ : UniformSpace (Q n))).HasBasis
        (fun _ : Unit => True) (fun _ => SetRel.id) := by
    simpa only [bot_uniformity] using
      (Filter.hasBasis_principal (SetRel.id : SetRel (Q n) (Q n)))
  have hP :
      (@uniformity P uP).HasBasis
        (fun I : Set ℕ × (∀ _ : ℕ, Unit) =>
          I.1.Finite ∧ ∀ i ∈ I.1, True)
        (fun I => ⋂ i ∈ I.1,
          {p : P × P | p.1 i = p.2 i}) := by
    rw [Pi.uniformity]
    simpa [SetRel.id] using
      (Filter.HasBasis.iInf' (fun n =>
        (hQ n).comap (fun p : P × P => (p.1 n, p.2 n))))
  have hC :
      (@uniformity C uC).HasBasis
        (fun I : Set ℕ × (∀ _ : ℕ, Unit) => I.1.Finite)
        (fun I => ⋂ i ∈ I.1,
          {p : C × C | p.1.1 i = p.2.1 i}) := by
    change
      (Filter.comap (fun p : C × C => (p.1.1, p.2.1))
          (@uniformity P uP)).HasBasis _ _
    have h := hP.comap (fun p : C × C => (p.1.1, p.2.1))
    have hset :
        (fun I : Set ℕ × (∀ _ : ℕ, Unit) =>
            (fun p : C × C => (p.1.1, p.2.1)) ⁻¹'
              (⋂ i ∈ I.1, {p : P × P | p.1 i = p.2 i})) =
          (fun I : Set ℕ × (∀ _ : ℕ, Unit) =>
            ⋂ i ∈ I.1, {p : C × C | p.1.1 i = p.2.1 i}) := by
      funext I
      ext p
      simp only [Set.mem_preimage, Set.mem_iInter, Set.mem_ofPred_eq]
      constructor
      · intro h i hi
        have hp := h i hi
        change p.1.1 i = p.2.1 i at hp
        exact hp
      · intro h i hi
        change p.1.1 i = p.2.1 i
        exact h i hi
    rw [hset] at h
    simpa using h
  have huf : @IsUniformInducing A C uVal uC f := by
    apply (Filter.HasBasis.isUniformInducing_iff hval hC).2
    constructor
    · intro I hI
      let J : Finset ℕ := hI.toFinset
      let N : ℕ := J.sup id
      obtain ⟨r, hr, hrball⟩ := hcof2 N
      refine ⟨r, hr, ?_⟩
      intro x y hxy
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      intro i hi
      have hiN : i ≤ N := Finset.le_sup (f := id) (hI.mem_toFinset.mpr hi)
      have hdiffN : y - x ∈ ((m ^ N : Ideal A) : Set A) := hrball hxy
      have hdiffi : y - x ∈ ((m ^ i : Ideal A) : Set A) :=
        (Ideal.pow_le_pow_right hiN) hdiffN
      have hdiffi' : x - y ∈ ((m ^ i : Ideal A) : Set A) := by
        simpa [sub_eq_add_neg, add_comm] using (m ^ i).neg_mem hdiffi
      change (AdicCompletion.of m (↥A) x).1 i =
        (AdicCompletion.of m (↥A) y).1 i
      rw [AdicCompletion.of_apply, AdicCompletion.of_apply,
        hsmul i, Submodule.mkQ_apply, Submodule.mkQ_apply,
        Submodule.Quotient.eq]
      exact hdiffi'
    · intro r hr
      obtain ⟨n, hn⟩ := hcof1 r hr
      let I : Set ℕ := {n}
      refine ⟨⟨I, fun _ => ()⟩, finite_singleton n, ?_⟩
      intro x y hxy
      simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hxy
      have hxy' : (AdicCompletion.of m (↥A) x).1 n =
          (AdicCompletion.of m (↥A) y).1 n := by
        exact hxy n (by simp [I])
      have hdiff' : x - y ∈ ((m ^ n : Ideal A) : Set A) := by
        rw [AdicCompletion.of_apply, AdicCompletion.of_apply,
          Submodule.mkQ_apply, Submodule.mkQ_apply,
          Submodule.Quotient.eq] at hxy'
        simpa [hsmul n] using hxy'
      change v ((y : K) - (x : K)) < r
      have hmem := hn (by
        simpa [sub_eq_add_neg, add_comm] using (m ^ n).neg_mem hdiff')
      simpa [sub_eq_add_neg] using hmem
  let : T0Space C := by
    exact
      (isUniformEmbedding_subtype_val (α := P) (p := fun z : P => z ∈ S)).isEmbedding.t0Space
  let pkg : @AbstractCompletion A uVal :=
    { space := C
      coe := f
      uniformStruct := uC
      complete := hcomplete
      separation := by infer_instance
      isUniformInducing := huf
      dense := hdense }
  let cpkg : @AbstractCompletion A uVal :=
    @UniformSpace.Completion.cPkg A uVal
  let : UniformSpace cpkg.space := cpkg.uniformStruct
  let e : cpkg.space ≃ᵤ pkg.space := cpkg.compareEquiv pkg
  have htop : @UniformSpace.toTopologicalSpace C uC =
      chapter06AdicCompletionTopology m := by
    rfl
  refine ⟨{
    toEquiv := e.toEquiv
    continuous_toEquiv := ?_
    continuous_inv := ?_
    commutes_with_completion := by
      intro a
      exact AbstractCompletion.compare_coe cpkg pkg a
  }⟩
  · rw [← htop]
    change @Continuous (UniformSpace.Completion A) C
      (@UniformSpace.Completion.uniformSpace A uVal).toTopologicalSpace
      (@UniformSpace.toTopologicalSpace C uC) e.toEquiv
    exact e.continuous
  · rw [← htop]
    change @Continuous C (UniformSpace.Completion A)
      (@UniformSpace.toTopologicalSpace C uC)
      (@UniformSpace.Completion.uniformSpace A uVal).toTopologicalSpace e.symm.toEquiv
    exact e.symm.continuous


end Nondiscrete

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter06
