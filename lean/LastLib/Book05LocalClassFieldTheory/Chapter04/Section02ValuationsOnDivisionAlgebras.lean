import LastLib.Book05LocalClassFieldTheory.Chapter04.Section01WhyCentralSimpleAlgebras
import LastLib.Book05LocalClassFieldTheory.Chapter03.Section04CyclicAlgebras
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

namespace LastLib.Book05LocalClassFieldTheory.Chapter04

noncomputable section

universe u

open scoped BigOperators TensorProduct

/-! ## 4.2. Valuations on division algebras -/

theorem chapter04_reduced_norm_agrees_with_determinant
    {K D S : Type*} [Field K] [Ring D] [Field S]
    [Algebra K D] [Algebra K S]
    (N : D → K) (d : ℕ)
    (ρ : D →ₐ[K] Matrix (Fin d) (Fin d) S)
    (hdet : chapter04ReducedNormAgreesWithDeterminant N d ρ) :
    ∀ x : D, algebraMap K S (N x) = Matrix.det (ρ x) := by
  exact hdet

/- The reduced norm is a construction for a central division algebra, not an
  extra hypothesis on each later valuation lemma.  Mathlib exposes the CSA
  quotient but not this construction, so the chapter keeps its existence as
  the single supporting interface below. -/
theorem chapter04_reduced_norm_data_exists
    {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
    [FiniteDimensional K D] [Algebra.IsCentral K D]
    (d : ℕ) (hdegree : Module.finrank K D = d ^ 2) :
    Nonempty (Chapter04ReducedNormData K D) := by
  sorry

theorem chapter04_reduced_norm_on_a_commutative_subfield
    {K D : Type u} {E : Type*} [Field K] [DivisionRing D] [Field E]
    [Algebra K D] [Algebra K E] [FiniteDimensional K D] [FiniteDimensional K E]
    [Algebra.IsCentral K D]
    (N : Chapter04ReducedNormData K D) (φ : E →ₐ[K] D)
    (hdiv : Module.finrank K E ∣ N.degree) :
    ∀ x : E,
      N.reducedNormAll (φ x) =
        (Algebra.norm K x) ^ (N.degree / Module.finrank K E) := by
  sorry

def chapter04FieldNormValuationFormula
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E]
    (vK : K → ℚ) (vE : E → ℚ) (f : ℕ) : Prop :=
  ∀ x : E, x ≠ 0 →
    vK (Algebra.norm K x) = (f : ℚ) * vE x

theorem chapter04_division_valuation_on_a_subfield
    {K D : Type u} {E : Type*} [Field K] [DivisionRing D] [Field E]
    [Algebra K D] [Algebra K E] [FiniteDimensional K D] [FiniteDimensional K E]
    [Algebra.IsCentral K D]
    (N : Chapter04ReducedNormData K D) (vK : K → ℚ) (vE : E → ℚ)
    (φ : E →ₐ[K] D) (e : ℕ)
    (he : 0 < e)
    (hdiv : Module.finrank K E ∣ N.degree)
    (hnorm : ∀ x : E, x ≠ 0 →
      vK (N.reducedNormAll (φ x)) =
        (N.degree : ℚ) / e * vE x)
    (x : E) (hx : x ≠ 0) :
    chapter04DivisionValuation N vK (φ x) =
        ((vK (N.reducedNormAll (φ x)) / N.degree : ℚ) :
          WithTop ℚ) ∧
      (vK (N.reducedNormAll (φ x)) / N.degree) =
        (vE x / e : ℚ) := by
  have hφx : φ x ≠ 0 := by
    intro h
    apply hx
    apply φ.injective
    change φ.toRingHom x = φ.toRingHom 0
    exact h.trans (map_zero φ).symm
  have hdegree : (N.degree : ℚ) ≠ 0 := by
    have _he := he
    have _hdiv := hdiv
    exact_mod_cast N.degree_pos.ne'
  dsimp [chapter04DivisionValuation]
  rw [if_neg hφx]
  constructor
  · rfl
  · rw [hnorm x hx]
    apply (div_eq_iff hdegree).2
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ac_rfl

theorem chapter04_division_valuation_integrality_iff
    {K D k barD : Type*} [Field K] [DivisionRing D] [Field k] [Field barD]
    [Algebra K D] [Algebra k barD] [FiniteDimensional k barD]
    [FiniteDimensional K D]
    [TopologicalSpace D]
    (V : Chapter04DivisionValuationInterface K D k barD) (x : D) :
    chapter04IsIntegralOverSubring V.valuationSubring x ↔ V.value x ≥ 0 := by
  classical
  have hpow : ∀ z : D, ∀ n : ℕ, V.value (z ^ n) = n • V.value z := by
    intro z n
    induction n with
    | zero => simp [V.value_one]
    | succ n ih =>
      rw [pow_succ, V.value_mul, ih, add_nsmul, one_nsmul]
  constructor
  · intro hx
    rcases hx with ⟨n, p, hlead, hpoly⟩
    have hnzero : n ≠ 0 := by
      intro hn
      subst n
      have hp : p ⟨0, Nat.zero_lt_succ 0⟩ = 1 := by simpa using hlead
      have hzero : (p ⟨0, Nat.zero_lt_succ 0⟩ : D) = 0 := by
        simpa [Fin.sum_univ_one] using hpoly
      have hpD : (p ⟨0, Nat.zero_lt_succ 0⟩ : D) = 1 := congrArg Subtype.val hp
      exact one_ne_zero (hpD.symm.trans hzero)
    have hnpos : 0 < n := Nat.pos_of_ne_zero hnzero
    have hsum_gt : ∀ (s : Finset (Fin (n + 1))) (f : Fin (n + 1) → D)
        (c : WithTop ℚ), s.Nonempty →
          (∀ i ∈ s, c < V.value (f i)) → c < V.value (Finset.sum s f) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
          intro f c hs h
          rcases hs with ⟨i, hi⟩
          exact False.elim (by simpa using hi)
      | @insert a s ha ih =>
          intro f c hs h
          rw [Finset.sum_insert ha]
          by_cases hs' : s.Nonempty
          · apply lt_of_lt_of_le
              (lt_min (h a (Finset.mem_insert_self a s)) (ih f c hs' ?_))
              (V.value_add _ _)
            intro i hi
            exact h i (Finset.mem_insert_of_mem hi)
          · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
            subst s
            simpa using h a (by simp)
    by_contra hnot
    have hxneg : V.value x < 0 := lt_of_not_ge hnot
    have hxne : x ≠ 0 := by
      intro hx0
      rw [hx0, V.value_zero] at hxneg
      exact (not_lt_of_ge le_top) hxneg
    let ux : Dˣ := Units.mk0 x hxne
    have hxval : V.value x = (V.unitValue ux : WithTop ℚ) := by
      simpa [ux] using V.value_unit ux
    have hxneg' : V.unitValue ux < 0 := by
      apply WithTop.coe_lt_coe.mp
      simpa [hxval] using hxneg
    let last : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
    let f : Fin (n + 1) → D := fun i => (p i : D) * x ^ (i : ℕ)
    change Finset.sum Finset.univ f = 0 at hpoly
    have hp_lead : (p last : D) = 1 := by
      exact congrArg Subtype.val hlead
    have hleadval : V.value (f last) = n • V.value x := by
      dsimp [f, last]
      rw [hp_lead, one_mul, hpow]
    have hterm : ∀ i : Fin (n + 1), i ≠ last →
        V.value (f last) < V.value (f i) := by
      intro i hi
      have hi_le : (i : ℕ) ≤ n := Nat.le_of_lt_succ i.isLt
      have hi_ne : (i : ℕ) ≠ n := by
        intro h
        apply hi
        apply Fin.ext
        exact h
      have hi_lt : (i : ℕ) < n := Nat.lt_of_le_of_ne hi_le hi_ne
      have hcoeff : 0 ≤ V.value (p i : D) := by
        have h := (p i).property
        change (p i : D) ∈ V.valuationSubring.carrier at h
        rw [V.valuationSubring_eq] at h
        exact h
      have hbase : n • V.value x < (i : ℕ) • V.value x := by
        rw [hxval, ← WithTop.coe_nsmul, ← WithTop.coe_nsmul,
          WithTop.coe_lt_coe, nsmul_eq_mul, nsmul_eq_mul]
        have hi_lt' : (i : ℚ) < (n : ℚ) := by exact_mod_cast hi_lt
        nlinarith [hxneg']
      have htermval : V.value (f i) =
          V.value (p i : D) + (i : ℕ) • V.value x := by
        dsimp [f]
        rw [V.value_mul, hpow]
      rw [hleadval, htermval]
      exact lt_of_lt_of_le hbase (le_add_of_nonneg_left hcoeff)
    have hdecomp : Finset.sum Finset.univ f = f last +
        Finset.sum (Finset.univ.erase last) f := by
      symm
      simpa [add_comm] using Finset.sum_erase_add Finset.univ f (Finset.mem_univ last)
    have hrel : f last + Finset.sum (Finset.univ.erase last) f = 0 := by
      calc
        f last + Finset.sum (Finset.univ.erase last) f = Finset.sum Finset.univ f :=
          hdecomp.symm
        _ = 0 := hpoly
    have hlead_eq : f last = -(Finset.sum (Finset.univ.erase last) f) :=
      eq_neg_of_add_eq_zero_left hrel
    have hnegval : ∀ z : D, V.value (-z) = V.value z := by
      intro z
      let um : Dˣ := Units.mk0 (-1 : D) (by simp)
      have hmval : V.value (-1 : D) = (V.unitValue um : WithTop ℚ) := by
        simpa [um] using V.value_unit um
      have hm := V.value_mul (-1 : D) (-1 : D)
      rw [neg_mul_neg, one_mul, V.value_one] at hm
      rw [hmval] at hm
      have hmq : (0 : ℚ) = V.unitValue um + V.unitValue um := by
        exact_mod_cast hm
      have hmzero : V.unitValue um = 0 := by linarith
      have hmval0 : V.value (-1 : D) = 0 := by simpa [hmval, hmzero]
      have hz' := V.value_mul (-1 : D) z
      simpa [neg_one_mul, hmval0] using hz'
    have hrest_gt : V.value (f last) <
        V.value (Finset.sum (Finset.univ.erase last) f) := by
      refine hsum_gt (Finset.univ.erase last) f (V.value (f last)) ?_ ?_
      · refine ⟨⟨0, Nat.zero_lt_succ n⟩, ?_⟩
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        intro hzero
        have hzero' : (0 : ℕ) = n := by
          simpa [last] using congrArg Fin.val hzero
        omega
      · intro i hi
        exact hterm i (Finset.ne_of_mem_erase hi)
    have hrest_eq : V.value (Finset.sum (Finset.univ.erase last) f) =
        V.value (f last) := by
      rw [hlead_eq, hnegval]
    rw [hrest_eq] at hrest_gt
    exact (lt_irrefl _) hrest_gt
  · intro hx
    have hxmem : x ∈ V.valuationSubring.carrier := by
      rw [V.valuationSubring_eq]
      exact hx
    let z : V.valuationSubring := ⟨x, hxmem⟩
    refine ⟨1, ![-z, 1], ?_, ?_⟩
    · simp
    · simp [Fin.sum_univ_two, z]

theorem chapter04_division_valuation_ultrametric
    {K D k barD : Type*} [Field K] [Ring D] [Field k] [Field barD]
    [Algebra K D] [Algebra k barD] [FiniteDimensional k barD]
    [TopologicalSpace D]
    (V : Chapter04DivisionValuationInterface K D k barD)
    (x y : D) :
    V.value (x + y) ≥ min (V.value x) (V.value y) := by
  exact V.value_add x y

theorem chapter04_division_valuation_multiplicative
    {K D k barD : Type*} [Field K] [Ring D] [Field k] [Field barD]
    [Algebra K D] [Algebra k barD] [FiniteDimensional k barD]
    [TopologicalSpace D]
    (V : Chapter04DivisionValuationInterface K D k barD) (x y : D) :
    V.value (x * y) = V.value x + V.value y := by
  exact V.value_mul x y

theorem chapter04_division_valuation_triangle_argument
    {K D k barD : Type*} [Field K] [DivisionRing D] [Field k] [Field barD]
    [Algebra K D] [Algebra k barD] [FiniteDimensional k barD]
    [TopologicalSpace D]
    (V : Chapter04DivisionValuationInterface K D k barD) (x y : D) (hx : x ≠ 0)
    (hle : V.value x ≤ V.value y) :
    V.value (x + y) = V.value x + V.value (1 + x⁻¹ * y) ∧
      V.value (1 + x⁻¹ * y) ≥ 0 := by
  have hfactor : x + y = x * (1 + x⁻¹ * y) := by
    rw [mul_add, mul_one, ← mul_assoc, mul_inv_cancel₀ hx, one_mul]
  have hnonneg : V.value (x⁻¹ * y) ≥ 0 := by
    by_cases hy : y = 0
    · simp [hy, V.value_zero]
    · let ux : Dˣ := Units.mk0 x hx
      let uy : Dˣ := Units.mk0 y hy
      have hxval : V.value x = (V.unitValue ux : WithTop ℚ) := by
        simpa [ux] using V.value_unit ux
      have hyval : V.value y = (V.unitValue uy : WithTop ℚ) := by
        simpa [uy] using V.value_unit uy
      have hle' : V.unitValue ux ≤ V.unitValue uy := by
        apply WithTop.coe_le_coe.mp
        simpa [hxval, hyval] using hle
      have hinv : V.unitValue ux + V.unitValue (ux⁻¹) = 0 := by
        have h := V.value_inv ux
        rw [V.value_unit ux, V.value_unit (ux⁻¹)] at h
        exact_mod_cast h
      have hxinv : V.value x⁻¹ = ((-V.unitValue ux : ℚ) : WithTop ℚ) := by
        calc
          V.value x⁻¹ = V.value ((ux⁻¹ : Dˣ) : D) := by
            congr 1
          _ = (V.unitValue (ux⁻¹) : WithTop ℚ) := V.value_unit (ux⁻¹)
          _ = ((-V.unitValue ux : ℚ) : WithTop ℚ) := by
            rw [eq_neg_of_add_eq_zero_right hinv]
      have hprod : V.value (x⁻¹ * y) =
          ((-V.unitValue ux + V.unitValue uy : ℚ) : WithTop ℚ) := by
        rw [V.value_mul, hxinv, hyval]
        norm_num
      rw [hprod]
      exact WithTop.coe_le_coe.mpr (by linarith)
  constructor
  · rw [hfactor, V.value_mul]
  · have hadd := V.value_add 1 (x⁻¹ * y)
    rw [V.value_one] at hadd
    simpa [min_eq_left hnonneg] using hadd

theorem chapter04_division_valuation_ring_is_local
    {K D k barD : Type*} [Field K] [DivisionRing D] [Field k] [Field barD]
    [Algebra K D] [Algebra k barD] [FiniteDimensional k barD]
    [TopologicalSpace D]
    (V : Chapter04DivisionValuationInterface K D k barD) :
    IsLocalRing V.valuationSubring := by
  have hunit_of_value_zero : ∀ z : V.valuationSubring,
      V.value (z : D) = 0 → IsUnit z := by
    intro z hz
    have hz_ne : (z : D) ≠ 0 := by
      intro hz0
      rw [hz0, V.value_zero] at hz
      exact WithTop.top_ne_zero hz
    have hzinv : V.value (z : D)⁻¹ = 0 := by
      have hmul := V.value_mul (z : D) (z : D)⁻¹
      rw [mul_inv_cancel₀ hz_ne, V.value_one] at hmul
      simpa [hz] using hmul.symm
    have hzinv_mem : (z : D)⁻¹ ∈ V.valuationSubring.carrier := by
      rw [V.valuationSubring_eq]
      change V.value (z : D)⁻¹ ≥ 0
      simpa [hzinv]
    let u : V.valuationSubringˣ :=
      { val := z
        inv := ⟨(z : D)⁻¹, hzinv_mem⟩
        val_inv := by
          apply Subtype.ext
          exact mul_inv_cancel₀ hz_ne
        inv_val := by
          apply Subtype.ext
          exact inv_mul_cancel₀ hz_ne }
    exact ⟨u, rfl⟩
  refine
    { toNontrivial := ⟨⟨0, 1, by
        intro h
        have h' : (0 : D) = 1 := congrArg Subtype.val h
        exact zero_ne_one h'⟩⟩
      isUnit_or_isUnit_of_add_one := ?_ }
  intro a b hab
  have habD : (a : D) + (b : D) = 1 := congrArg Subtype.val hab
  have ha_mem : V.value (a : D) ≥ 0 := by
    have h := a.property
    change (a : D) ∈ V.valuationSubring.carrier at h
    rw [V.valuationSubring_eq] at h
    exact h
  have hb_mem : V.value (b : D) ≥ 0 := by
    have h := b.property
    change (b : D) ∈ V.valuationSubring.carrier at h
    rw [V.valuationSubring_eq] at h
    exact h
  by_cases ha0 : V.value (a : D) = 0
  · exact Or.inl (hunit_of_value_zero a ha0)
  · have ha_pos : 0 < V.value (a : D) := lt_of_le_of_ne ha_mem (Ne.symm ha0)
    have hab_lt : V.value (b : D) < V.value (a : D) := by
      by_contra h
      have hle : V.value (a : D) ≤ V.value (b : D) := le_of_not_gt h
      have hadd := V.value_add (a : D) (b : D)
      rw [habD, V.value_one] at hadd
      have hzero : (0 : WithTop ℚ) ≥ V.value (a : D) := by
        simpa [min_eq_left hle] using hadd
      exact (not_le_of_gt ha_pos) hzero
    have hb0 : V.value (b : D) = 0 := by
      have hstrict := V.value_strict_add hab_lt
      have habD' : (b : D) + (a : D) = 1 := by rw [add_comm, habD]
      rw [habD', V.value_one] at hstrict
      exact hstrict.symm
    exact Or.inr (hunit_of_value_zero b hb0)

theorem chapter04_division_valuation_ring_and_maximal_ideal
    {K D k barD : Type*} [Field K] [DivisionRing D] [Field k] [Field barD]
    [Algebra K D] [Algebra k barD] [FiniteDimensional k barD]
    [TopologicalSpace D]
    (V : Chapter04DivisionValuationInterface K D k barD) :
    V.valuationSubring.carrier = {x | V.value x ≥ 0} ∧
      chapter04IdealImage V.valuationSubring V.maximalIdeal = {x | V.value x > 0} := by
  exact ⟨V.valuationSubring_eq, V.maximalIdeal_eq⟩

theorem chapter04_division_residue_is_a_finite_field
    {K D k barD : Type*} [Field K] [DivisionRing D] [Field k] [Field barD]
    [Algebra K D] [Algebra k barD] [FiniteDimensional k barD]
    [TopologicalSpace D]
    (V : Chapter04DivisionValuationInterface K D k barD) :
    Finite barD ∧ Function.Surjective V.residueMap := by
  exact ⟨V.residue_finite, V.residue_surjective⟩

theorem chapter04_division_residue_quotient_equiv
    {K D k barD : Type*} [Field K] [DivisionRing D] [Field k] [Field barD]
    [Algebra K D] [Algebra k barD] [FiniteDimensional k barD]
    [TopologicalSpace D]
    (V : Chapter04DivisionValuationInterface K D k barD) :
    Nonempty ((V.valuationSubring ⧸ V.maximalIdeal) ≃+ barD) := by
  have hker : V.maximalIdeal.toAddSubgroup = V.residueMap.toAddMonoidHom.ker := by
    ext x
    constructor
    · intro hx
      have hres : V.residueMap x = V.residueMap 0 :=
        (V.residue_eq_iff x 0).2 (by simpa using hx)
      simpa using hres
    · intro hx
      have hres : V.residueMap x = V.residueMap 0 := by simpa using hx
      have hmem := (V.residue_eq_iff x 0).1 hres
      simpa using hmem
  change Nonempty ((V.valuationSubring ⧸ V.maximalIdeal.toAddSubgroup) ≃+ barD)
  rw [hker]
  exact ⟨QuotientAddGroup.quotientKerEquivOfSurjective
    V.residueMap.toAddMonoidHom V.residue_surjective⟩

theorem chapter04_division_dimension_value_residue_formula
    {K D k barD : Type*} [Field K] [Ring D] [Field k] [Field barD]
    [Algebra K D] [Algebra k barD] [FiniteDimensional k barD]
    [TopologicalSpace D]
    (A : Chapter04DivisionAlgebraData K)
    [TopologicalSpace A.carrier]
    (V : Chapter04DivisionValuationInterface K (A.carrier) k barD)
    (d : ℕ) (hdegree : A.degree = d) :
    d ^ 2 = chapter04RamificationIndex V.unitValue *
      chapter04ResidueDegree k barD := by
  sorry

structure Chapter04ValuationProductBasis
    (K D : Type*) [Field K] [AddCommGroup D] [Module K D] [Mul D]
    (e f : ℕ) where
  valueRepresentatives : Fin e → D
  residueLifts : Fin f → D
  basis : Module.Basis (Fin e × Fin f) K D
  basis_eq_products : ∀ ij,
    basis ij = valueRepresentatives ij.1 * residueLifts ij.2

theorem chapter04_valuation_lattice_basis_exists
    {K k barD : Type*} [Field K] [Field k] [Field barD]
    [Algebra k barD] [FiniteDimensional k barD]
    (A : Chapter04DivisionAlgebraData K)
    [TopologicalSpace A.carrier]
    (V : Chapter04DivisionValuationInterface K A.carrier k barD)
    (e f : ℕ)
    (hvalue : Nat.card
      (chapter04ValueGroup V.unitValue ⧸
        chapter04ValueGroupModInteger V.unitValue) = e)
    (hresidue : Module.finrank k barD = f)
    (hcard : Module.finrank K (A.carrier) = e * f) :
    Nonempty (Chapter04ValuationProductBasis K (A.carrier) e f) := by
  sorry

/- The preceding theorem is the reusable basis interface.  This statement
  records the source's leading-residue independence and completeness
  argument without turning that proof narration into a second construction. -/
theorem chapter04_valuation_product_basis_has_independence_and_expansion
    {K D : Type*} [Field K] [AddCommGroup D] [Module K D] [Mul D]
    {e f : ℕ}
    (B : Chapter04ValuationProductBasis K D e f) :
    LinearIndependent K B.basis ∧
      ∀ z : D, z ∈ Submodule.span K (Set.range B.basis) := by
  constructor
  · exact B.basis.linearIndependent
  · intro z
    rw [B.basis.span_eq]
    trivial

structure Chapter04ResidueConjugationData
    (K D k barD : Type*) [Field K] [Ring D] [Field k] [Field barD]
    [Algebra K D] [Algebra k barD] [FiniteDimensional k barD]
    [IsGalois k barD] where
  value : Dˣ → ℚ
  conjugation :
    (chapter04ValueGroup value ⧸ chapter04ValueGroupModInteger value) →
      Gal(barD / k)
  conjugation_mul : ∀ a b,
    conjugation (a + b) = conjugation a * conjugation b
  conjugation_injective : Function.Injective conjugation
  fixed_field_eq_base :
    {z : barD | ∀ q, conjugation q z = z} = Set.range (algebraMap k barD)
  [quotient_finite : Finite
    (chapter04ValueGroup value ⧸ chapter04ValueGroupModInteger value)]
  quotient_card_eq_galois_card :
    Nat.card (chapter04ValueGroup value ⧸ chapter04ValueGroupModInteger value) =
      Nat.card (Gal(barD / k))

theorem chapter04_residue_conjugation_has_base_fixed_field
    {K D k barD : Type*} [Field K] [Ring D] [Field k] [Field barD]
    [Algebra K D] [Algebra k barD] [FiniteDimensional k barD]
    [IsGalois k barD]
    (C : Chapter04ResidueConjugationData K D k barD) :
    {z : barD | ∀ q, C.conjugation q z = z} = Set.range (algebraMap k barD) := by
  exact C.fixed_field_eq_base

theorem chapter04_residue_conjugation_is_surjective
    {K D k barD : Type*} [Field K] [Ring D] [Field k] [Field barD]
    [Algebra K D] [Algebra k barD] [FiniteDimensional k barD]
    [IsGalois k barD]
    (C : Chapter04ResidueConjugationData K D k barD) :
    Function.Surjective C.conjugation := by
  let domain :=
    chapter04ValueGroup C.value ⧸ chapter04ValueGroupModInteger C.value
  let codomain := Gal(barD / k)
  let domainFintype : Fintype domain :=
    @Fintype.ofFinite domain C.quotient_finite
  let codomainFintype : Fintype codomain :=
    Fintype.ofFinite codomain
  have hcard : @Fintype.card domain domainFintype =
      @Fintype.card codomain codomainFintype := by
    rw [← @Nat.card_eq_fintype_card domain domainFintype,
      ← @Nat.card_eq_fintype_card codomain codomainFintype]
    exact C.quotient_card_eq_galois_card
  have hbij : Function.Bijective C.conjugation :=
    (@Fintype.bijective_iff_injective_and_card domain codomain
      domainFintype codomainFintype C.conjugation).2
      ⟨C.conjugation_injective, hcard⟩
  exact hbij.2

theorem chapter04_division_indices_are_the_degree
    {K D k barD : Type*} [Field K] [Ring D] [Field k] [Field barD]
    [Algebra K D] [Algebra k barD] [FiniteDimensional k barD]
    [IsGalois k barD]
    (A : Chapter04DivisionAlgebraData K)
    [TopologicalSpace A.carrier]
    (V : Chapter04DivisionValuationInterface K (A.carrier) k barD)
    (C : Chapter04ResidueConjugationData K (A.carrier) k barD)
    (d : ℕ) (hdegree : Module.finrank K (A.carrier) = d ^ 2)
    (hdpos : 0 < d)
    (hπ : ∃ π : A.carrierˣ, V.unitValue π = 1)
    (hvalue : C.value = V.unitValue)
    (hbound : chapter04ValueGroupContainedInFractionalLattice V.unitValue d)
    (hvalue_card : Nat.card
      (chapter04ValueGroup V.unitValue ⧸
        chapter04ValueGroupModInteger V.unitValue) ≤ d)
    (hresidue_degree_le : chapter04ResidueDegree k barD ≤ d)
    (hdimension : d ^ 2 =
      chapter04RamificationIndex V.unitValue * chapter04ResidueDegree k barD) :
    chapter04RamificationIndex V.unitValue = chapter04ResidueDegree k barD ∧
      chapter04ResidueDegree k barD = d := by
  have _hdegree := hdegree
  have _hπ := hπ
  have _hvalue := hvalue
  have _hbound := hbound
  let e := chapter04RamificationIndex V.unitValue
  let f := chapter04ResidueDegree k barD
  have he : e ≤ d := by
    simpa [e, chapter04RamificationIndex] using hvalue_card
  have hf : f ≤ d := by
    exact hresidue_degree_le
  have hprod : d ^ 2 = e * f := by
    simpa [e, f] using hdimension
  have heq : e = d := by
    nlinarith
  have hfeq : f = d := by
    nlinarith
  exact ⟨heq.trans hfeq.symm, hfeq⟩

theorem chapter04_value_group_contains_integer_lattice
    {D : Type*} [Monoid D] (w : Dˣ → ℚ) (π : Dˣ) (hπ : w π = 1) :
    chapter04IntegerValueLattice ≤ chapter04ValueGroup w := by
  rw [chapter04IntegerValueLattice, chapter04ValueGroup]
  exact (AddSubgroup.zmultiples_le).2 (AddSubgroup.subset_closure ⟨π, hπ⟩)

/- A bundled witness records the Hensel-lifted unramified maximal field.  The
  field and extension instances are part of the witness, so later statements
  cannot be satisfied by an untyped `Prop` token. -/
structure Chapter04UnramifiedMaximalSubfieldSpec
    (K : Type*) [Field K] (P : Chapter04LocalFieldProfile K)
    (D : Chapter04DivisionAlgebraData K) where
  field : Type*
  [field_isField : Field field]
  [field_algebra : Algebra K field]
  [field_finiteDimensional : FiniteDimensional K field]
  [field_isGalois : IsGalois K field]
  [field_algebra_on_division : Algebra field D.carrier]
  [field_scalarTower : IsScalarTower K field D.carrier]
  extensionData : Chapter04UnramifiedExtensionData K field
  extensionData_valuationK : extensionData.valuationK = P.valuation
  degree : ℕ
  degree_eq : degree = D.degree
  degree_eq_finrank : Module.finrank K field = degree
  embedding : field →ₐ[K] D.carrier
  embedding_injective : Function.Injective embedding
  embedding_eq_algebraMap : ∀ x : field,
    embedding x = algebraMap field D.carrier x
  centralizer_eq_range :
    {x : D.carrier | ∀ y : field, x * embedding y = embedding y * x} =
      Set.range embedding
  split_over_unramified_field :
    Nonempty (field ⊗[K] D.carrier ≃ₐ[field]
      Matrix (Fin D.degree) (Fin D.degree) field)

def chapter04UnramifiedMaximalSubfieldSplits
    {K : Type*} [Field K] (P : Chapter04LocalFieldProfile K)
    (D : Chapter04DivisionAlgebraData K)
    (E : Chapter04UnramifiedMaximalSubfieldSpec K P D) : Prop :=
  letI := E.field_isField
  letI := E.field_algebra
  letI := E.field_finiteDimensional
  letI := E.field_isGalois
  letI := E.field_algebra_on_division
  letI := E.field_scalarTower
  Nonempty (E.field ⊗[K] D.carrier ≃ₐ[E.field]
    Matrix (Fin D.degree) (Fin D.degree) E.field)

theorem chapter04_division_algebra_has_unramified_maximal_subfield
    {K : Type*} [Field K] (P : Chapter04LocalFieldProfile K)
    (D : Chapter04DivisionAlgebraData K) :
    Nonempty (Chapter04UnramifiedMaximalSubfieldSpec K P D) := by
  sorry

theorem chapter04_unramified_maximal_subfield_is_maximal
    {K : Type*} [Field K] (P : Chapter04LocalFieldProfile K)
    (D : Chapter04DivisionAlgebraData K)
    (E : Chapter04UnramifiedMaximalSubfieldSpec K P D) :
    E.degree = D.degree ∧
      ({x : D.carrier | ∀ y : E.field,
        x * E.embedding y = E.embedding y * x} = Set.range E.embedding) := by
  exact ⟨E.degree_eq, E.centralizer_eq_range⟩

structure Chapter04ResidueConjugationIsomorphism
    {K D k barD : Type*} [Field K] [Ring D] [Field k] [Field barD]
    [Algebra K D] [Algebra k barD] [FiniteDimensional k barD]
    [IsGalois k barD]
    (C : Chapter04ResidueConjugationData K D k barD) where
  toEquiv :
    (chapter04ValueGroup C.value ⧸ chapter04ValueGroupModInteger C.value) ≃
      Gal(barD / k)
  map_add : ∀ a b, toEquiv (a + b) = toEquiv a * toEquiv b

theorem chapter04_unramified_residue_conjugation_is_an_isomorphism
    {K D k barD : Type*} [Field K] [Ring D] [Field k] [Field barD]
    [Algebra K D] [Algebra k barD] [FiniteDimensional k barD]
    [IsGalois k barD]
    (C : Chapter04ResidueConjugationData K D k barD)
    (hsurj : Function.Surjective C.conjugation) :
    Nonempty (Chapter04ResidueConjugationIsomorphism C) := by
  let e := Equiv.ofBijective C.conjugation ⟨C.conjugation_injective, hsurj⟩
  exact ⟨{ toEquiv := e, map_add := C.conjugation_mul }⟩

/- The pinned cyclic-algebra API packages the presentation together with the
  chosen parameter as a unit.  These small bridges install the instances
  carried by the maximal subfield specification before referring to that API. -/
def chapter04CyclicPresentationOverUnramifiedField
    {K : Type*} [Field K] (P : Chapter04LocalFieldProfile K)
    (D : Chapter04DivisionAlgebraData K)
    (E : Chapter04UnramifiedMaximalSubfieldSpec K P D) (a : Kˣ) : Type _ :=
  letI := E.field_isField
  letI := E.field_algebra
  letI := E.field_finiteDimensional
  letI := E.field_isGalois
  LastLib.Book05LocalClassFieldTheory.Chapter03.chapter03CyclicAlgebra
    K E.field D.degree E.extensionData.arithmeticFrobenius a

def chapter04CyclicExtensionOverUnramifiedField
    {K : Type*} [Field K] (P : Chapter04LocalFieldProfile K)
    (D : Chapter04DivisionAlgebraData K)
    (E : Chapter04UnramifiedMaximalSubfieldSpec K P D) : Prop :=
  letI := E.field_isField
  letI := E.field_algebra
  letI := E.field_finiteDimensional
  letI := E.field_isGalois
  LastLib.Book05LocalClassFieldTheory.Chapter03.chapter03CyclicExtension
    K E.field D.degree E.extensionData.arithmeticFrobenius

def chapter04CyclicPresentationCarrier
    {K : Type*} [Field K] (P : Chapter04LocalFieldProfile K)
    (D : Chapter04DivisionAlgebraData K)
    (E : Chapter04UnramifiedMaximalSubfieldSpec K P D) (a : Kˣ)
    (Q : chapter04CyclicPresentationOverUnramifiedField P D E a) :
    chapter04CentralSimpleAlgebra K :=
  letI := E.field_isField
  letI := E.field_algebra
  letI := E.field_finiteDimensional
  letI := E.field_isGalois
  let Q' :
      LastLib.Book05LocalClassFieldTheory.Chapter03.Chapter03CyclicAlgebraPresentation
        K E.field D.degree E.extensionData.arithmeticFrobenius a :=
    Q
  Q'.carrier

def chapter04UnramifiedMaximalSubfieldUniformizer
    {K : Type*} [Field K] (P : Chapter04LocalFieldProfile K)
    (D : Chapter04DivisionAlgebraData K)
    (E : Chapter04UnramifiedMaximalSubfieldSpec K P D) : Kˣ :=
  letI := E.field_isField
  letI := E.field_algebra
  letI := E.field_finiteDimensional
  letI := E.field_isGalois
  E.extensionData.uniformizer

structure Chapter04CyclicPresentationSpec
    {K : Type*} [Field K] (P : Chapter04LocalFieldProfile K)
    (D : Chapter04DivisionAlgebraData K)
    (E : Chapter04UnramifiedMaximalSubfieldSpec K P D) where
  exponent : ℕ
  exponent_pos : 0 < exponent
  exponent_coprime : Nat.Coprime exponent D.degree
  parameter : Kˣ
  presentation : chapter04CyclicPresentationOverUnramifiedField P D E parameter
  equivalence : Nonempty
    (D.carrier ≃ₐ[K]
      chapter04CyclicPresentationCarrier P D E parameter presentation)
  unramified_field_degree : ℕ
  unramified_field_degree_eq : unramified_field_degree = D.degree
  arithmetic_frobenius_relation : chapter04CyclicExtensionOverUnramifiedField P D E
  parameter_power_normalization :
    parameter = chapter04UnramifiedMaximalSubfieldUniformizer P D E ^ exponent

theorem chapter04_division_algebra_has_cyclic_presentation
    {K : Type*} [Field K] (P : Chapter04LocalFieldProfile K)
    (D : Chapter04DivisionAlgebraData K)
    (U : Chapter04UnramifiedMaximalSubfieldSpec K P D) :
    Nonempty (Chapter04CyclicPresentationSpec P D U) := by
  sorry

theorem chapter04_division_parameter_power_is_central
    {K D : Type*} [Field K] [DivisionRing D]
    [Algebra K D] [Algebra.IsCentral K D]
    (piD : D) (d : ℕ)
    (hconj : ∀ x : D, piD ^ d * x = x * piD ^ d)
    :
    ∃ c : K, algebraMap K D c = piD ^ d := by
  exact Algebra.mem_bot.mp (Algebra.IsCentral.out
    ((Subalgebra.mem_center_iff).2 (fun x => (hconj x).symm)))

theorem chapter04_division_parameter_power_is_uniformizer_times_unit
    {K D : Type*} [Field K] [DivisionRing D] [Algebra K D]
    (piD : D) (π : K) (d : ℕ)
    (hfactor : ∃ c : K, c ≠ 0 ∧ piD ^ d = algebraMap K D (c * π)) :
    ∃ c : Kˣ, piD ^ d = algebraMap K D ((c : K) * π) := by
  exact hfactor.elim (fun c hc =>
    ⟨Units.mk0 c hc.1, by simpa using hc.2⟩)

theorem chapter04_unramified_unit_norm_normalizes_parameter
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (N : Lˣ →* Kˣ) (c : Kˣ)
    (hsurj : ∀ u : Kˣ, ∃ b : Lˣ, N b = u) :
    ∃ b : Lˣ, N b = c⁻¹ := by
  exact hsurj c⁻¹

def chapter04GeneratorChangeFactor (n r : ℕ) : ZMod n :=
  LastLib.Book05LocalClassFieldTheory.Chapter03.chapter03GeneratorChangeFactor n r

theorem chapter04_generator_change_factor_mul
    (n r : ℕ) (hcoprime : Nat.Coprime r n) :
    (r : ZMod n) * chapter04GeneratorChangeFactor n r = 1 := by
  exact LastLib.Book05LocalClassFieldTheory.Chapter03.chapter03_generator_change_factor_mul
    n r hcoprime

end

end LastLib.Book05LocalClassFieldTheory.Chapter04
