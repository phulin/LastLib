import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter02.Dependencies
import Mathlib.Algebra.Regular.Basic
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.RingTheory.Adjoin.Polynomial.Basic

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter02

universe u v

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators DirectSum
open Polynomial

/-! ## 2.1. Recording all powers of an ideal -/

/-- Homogeneity of an element of the Rees algebra in degree `n`. -/
def chapter02ReesHomogeneous
    {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ)
    (p : Chapter02ReesAlgebra R I) : Prop :=
  ∀ j, j ≠ n → p.1.coeff j = 0

/-- The canonical degree-`n` submodule of the Rees algebra inside `R[X]`. -/
def chapter02ReesComponent
    {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) :
    Submodule R (Chapter02ReesAlgebra R I) where
  carrier := {p | chapter02ReesHomogeneous I n p}
  zero_mem' := by
    intro j hj
    simp
  add_mem' := by
    intro p q hp hq j hj
    simp only [chapter02ReesHomogeneous] at hp hq ⊢
    simpa [map_add] using congrArg₂ (· + ·) (hp j hj) (hq j hj)
  smul_mem' := by
    intro r p hp j hj
    simp only [chapter02ReesHomogeneous] at hp ⊢
    simpa [smul_eq_mul] using congrArg (r * ·) (hp j hj)

/-- The grading certificate for the coefficientwise Rees construction. -/
structure Chapter02ReesGradingData
    {R : Type u} [CommRing R] (I : Ideal R) where
  component : ℕ → Submodule R (Chapter02ReesAlgebra R I)
  graded : GradedAlgebra component
  component_spec :
    ∀ n (p : Chapter02ReesAlgebra R I),
      p ∈ component n ↔ chapter02ReesHomogeneous I n p
  degreeZeroEquiv : R ≃+* component 0
  degreeZeroEquiv_algebraMap :
    ∀ r, algebraMap R (Chapter02ReesAlgebra R I) r =
      (degreeZeroEquiv r : Chapter02ReesAlgebra R I)

/- LOCAL_DEPENDENCY_GUESS: the coefficientwise homogeneous pieces form the canonical internal
grading on Mathlib's Rees subalgebra. -/
theorem chapter02_rees_grading_exists
    {R : Type u} [CommRing R] (I : Ideal R) :
    Nonempty (Chapter02ReesGradingData I) := by
  classical
  let component := chapter02ReesComponent I
  have hgm : SetLike.GradedMonoid component := by
    refine { one_mem := ?_, mul_mem := ?_ }
    · change chapter02ReesHomogeneous I 0 1
      intro j hj
      simp [Polynomial.coeff_one, hj]
    · intro m n p q hp hq
      change chapter02ReesHomogeneous I (m + n) (p * q)
      have hp' : p.1 = Polynomial.monomial m (p.1.coeff m) := by
        ext j
        by_cases hj : j = m
        · subst j
          simp
        · simpa [Polynomial.coeff_monomial, hj, Ne.symm hj] using hp j hj
      have hq' : q.1 = Polynomial.monomial n (q.1.coeff n) := by
        ext j
        by_cases hj : j = n
        · subst j
          simp
        · simpa [Polynomial.coeff_monomial, hj, Ne.symm hj] using hq j hj
      intro j hj
      change (p.1 * q.1).coeff j = 0
      rw [hp', hq', Polynomial.monomial_mul_monomial]
      simp [Polynomial.coeff_monomial, Ne.symm hj]
  have hcoe_coeff (x : DirectSum ℕ (fun n => component n)) (n : ℕ) :
      (DirectSum.coeAddMonoidHom component x : Chapter02ReesAlgebra R I).1.coeff n =
        (x n : Chapter02ReesAlgebra R I).1.coeff n := by
    induction x using DFinsupp.induction with
    | h0 => simp
    | ha i b x hxi hb ih =>
        rw [map_add]
        change
          ((DirectSum.coeAddMonoidHom component (DFinsupp.single i b)).1 +
              (DirectSum.coeAddMonoidHom component x).1).coeff n =
            (((DFinsupp.single i b + x : DirectSum ℕ (fun n => component n)) n : component n) :
              Chapter02ReesAlgebra R I).1.coeff n
        rw [Polynomial.coeff_add]
        have hsingle :
            DirectSum.coeAddMonoidHom component (DFinsupp.single i b) =
              (b : Chapter02ReesAlgebra R I) := by
          exact DirectSum.coeAddMonoidHom_of component i b
        rw [hsingle]
        by_cases hin : i = n
        · subst n
          rw [DFinsupp.add_apply, DFinsupp.single_eq_same, hxi, add_zero]
          simp [ih, hxi]
        · have hbi := b.2 n (Ne.symm hin)
          rw [DFinsupp.add_apply, DFinsupp.single_eq_of_ne (Ne.symm hin), zero_add]
          simp [hbi, ih]
  have hspan : iSup component = ⊤ := by
    apply le_antisymm le_top
    intro p hp
    have hp_eq : p = ∑ n ∈ p.1.support,
        (⟨Polynomial.monomial n (p.1.coeff n),
            reesAlgebra.monomial_mem.mpr ((mem_reesAlgebra_iff I p.1).1 p.2 n)⟩ :
          Chapter02ReesAlgebra R I) := by
      apply Subtype.ext
      simp only [AddSubmonoidClass.coe_finsetSum]
      exact p.1.as_sum_support
    rw [hp_eq]
    apply Submodule.sum_mem
    intro n hn
    let hncomp : component n :=
      ⟨⟨Polynomial.monomial n (p.1.coeff n),
        reesAlgebra.monomial_mem.mpr ((mem_reesAlgebra_iff I p.1).1 p.2 n)⟩, by
        intro j hj
        simp [Polynomial.coeff_monomial, Ne.symm hj]⟩
    exact Submodule.mem_iSup_of_mem n hncomp.property
  have hinternal : DirectSum.IsInternal component :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top component).2
      ⟨by
        rw [iSupIndep_iff_dfinsupp_lsum_injective]
        intro x y hxy
        apply DirectSum.ext
        intro n
        have hcoeff := congrArg
          (fun z : Chapter02ReesAlgebra R I => z.1.coeff n) hxy
        apply Subtype.ext
        apply Subtype.ext
        ext j
        by_cases hj : j = n
        · subst j
          exact (hcoe_coeff x n).symm.trans (hcoeff.trans (hcoe_coeff y n))
        · exact ((x n).2 j hj).trans ((y n).2 j hj).symm
        
      , hspan⟩
  let graded : GradedAlgebra component :=
    @DirectSum.IsInternal.gradedAlgebra R _ (Chapter02ReesAlgebra R I) _ _ ℕ _ _ component hgm
      hinternal
  let e0 : R →+* component 0 :=
    { toFun := fun r =>
        ⟨⟨Polynomial.C r, reesAlgebra.monomial_mem.mpr (by simp)⟩, by
          intro j hj
          simp [Polynomial.coeff_C, hj]⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        simp
      map_mul' := by
        intro r s
        apply Subtype.ext
        apply Subtype.ext
        simp
      map_zero' := by
        apply Subtype.ext
        apply Subtype.ext
        simp
      map_add' := by
        intro r s
        apply Subtype.ext
        apply Subtype.ext
        simp }
  have he0bij : Function.Bijective e0 := by
    constructor
    · intro r s hrs
      have hcoeff := congrArg (fun z : component 0 => z.1.1.coeff 0) hrs
      simpa [e0, Polynomial.coeff_C] using hcoeff
    · intro p
      refine ⟨p.1.1.coeff 0, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      ext j
      by_cases hj : j = 0
      · subst j
        simp [e0]
      · have hpj := p.2 j hj
        simpa [e0, Polynomial.coeff_C, hj, Ne.symm hj] using hpj.symm
  let e : R ≃+* component 0 := RingEquiv.ofBijective e0 he0bij
  let data : Chapter02ReesGradingData I :=
    { component := component
      graded := graded
      component_spec := by
        intro n p
        rfl
      degreeZeroEquiv := e
      degreeZeroEquiv_algebraMap := by
        intro r
        apply Subtype.ext
        simp [e, e0, component] }
  exact ⟨data⟩

noncomputable def chapter02ReesGradingData
    {R : Type u} [CommRing R] (I : Ideal R) :
    Chapter02ReesGradingData I :=
  Classical.choice (chapter02_rees_grading_exists I)

@[simp] theorem chapter02_rees_component_mem_iff
    {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ)
    (p : Chapter02ReesAlgebra R I) :
    p ∈ (chapter02ReesGradingData I).component n ↔
      chapter02ReesHomogeneous I n p := by
  exact (chapter02ReesGradingData I).component_spec n p

/-- The affine projective spectrum of the Rees algebra. -/
noncomputable def chapter02ReesProj
    {R : Type u} [CommRing R] (I : Ideal R) : Scheme.{u} := by
  let G := chapter02ReesGradingData I
  letI := G.graded
  exact AlgebraicGeometry.«Proj» G.component

theorem chapter02_mem_reesAlgebra_iff
    {R : Type u} [CommRing R] (I : Ideal R) (p : Polynomial R) :
    p ∈ Chapter02ReesAlgebra R I ↔ ∀ n, p.coeff n ∈ I ^ n := by
  exact mem_reesAlgebra_iff I p

theorem chapter02_mem_reesAlgebra_iff_support
    {R : Type u} [CommRing R] (I : Ideal R) (p : Polynomial R) :
    p ∈ Chapter02ReesAlgebra R I ↔
      ∀ n ∈ p.support, p.coeff n ∈ I ^ n := by
  exact mem_reesAlgebra_iff_support I p

theorem chapter02_rees_monomial_mem_iff
    {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) (r : R) :
    Polynomial.monomial n r ∈ Chapter02ReesAlgebra R I ↔ r ∈ I ^ n := by
  exact reesAlgebra.monomial_mem

theorem chapter02_ideal_power_mul
    {R : Type u} [CommRing R] (I : Ideal R) (m n : ℕ) :
    I ^ m * I ^ n = I ^ (m + n) := by
  rw [pow_add]

theorem chapter02_ideal_power_succ_le
    {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) :
    I ^ (n + 1) ≤ I ^ n := by
  exact Ideal.pow_le_pow_right (Nat.le_succ n)

/-- The linear map sending an element of `I^n` to its homogeneous Rees monomial. -/
def chapter02ReesDegreeNMap
    {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) :
    (I ^ n : Submodule R R) →ₗ[R] chapter02ReesComponent I n where
  toFun r :=
    ⟨⟨Polynomial.monomial n (r : R), reesAlgebra.monomial_mem.mpr r.2⟩, by
      intro j hj
      simp [Polynomial.coeff_monomial, Ne.symm hj]⟩
  map_add' r s := by
    apply Subtype.ext
    apply Subtype.ext
    ext j
    by_cases h : n = j <;> simp [Polynomial.coeff_monomial, h]
  map_smul' a r := by
    apply Subtype.ext
    apply Subtype.ext
    ext j
    by_cases h : n = j <;> simp [Polynomial.coeff_monomial, h]

noncomputable def chapter02ReesDegreeNEquiv
    {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) :
    (I ^ n : Submodule R R) ≃ₗ[R] chapter02ReesComponent I n := by
  let f := chapter02ReesDegreeNMap I n
  have hbij : Function.Bijective f := by
    constructor
    · intro r s hrs
      apply Subtype.ext
      have hcoeff := congrArg
        (fun z : chapter02ReesComponent I n => z.1.1.coeff n) hrs
      simpa [f, chapter02ReesDegreeNMap, Polynomial.coeff_monomial] using hcoeff
    · intro p
      let r : (I ^ n : Submodule R R) :=
        ⟨p.1.1.coeff n,
          (chapter02_mem_reesAlgebra_iff I p.1.1).1 p.1.2 n⟩
      refine ⟨r, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      ext j
      by_cases hj : j = n
      · subst j
        simp [f, chapter02ReesDegreeNMap, r]
      · have hp := p.2 j hj
        simpa [f, chapter02ReesDegreeNMap, Polynomial.coeff_monomial, hj,
          Ne.symm hj] using hp.symm
  exact LinearEquiv.ofBijective f hbij

/-- The degree-zero map from the coefficient ring into the Rees algebra. -/
def chapter02ReesDegreeZeroMap
    {R : Type u} [CommRing R] (I : Ideal R) :
    R →ₗ[R] chapter02ReesComponent I 0 where
  toFun r :=
    ⟨⟨Polynomial.monomial 0 r, reesAlgebra.monomial_mem.mpr (by simp)⟩, by
      intro j hj
      simp [Polynomial.coeff_C, hj]⟩
  map_add' r s := by
    apply Subtype.ext
    apply Subtype.ext
    ext j
    by_cases h : 0 = j <;> simp [Polynomial.coeff_C, h]
  map_smul' a r := by
    apply Subtype.ext
    apply Subtype.ext
    ext j
    by_cases h : 0 = j <;> simp [Polynomial.coeff_C, h]

noncomputable def chapter02ReesDegreeZeroEquiv
    {R : Type u} [CommRing R] (I : Ideal R) :
    R ≃ₗ[R] chapter02ReesComponent I 0 := by
  let f := chapter02ReesDegreeZeroMap I
  have hbij : Function.Bijective f := by
    constructor
    · intro r s hrs
      have hcoeff := congrArg
        (fun z : chapter02ReesComponent I 0 => z.1.1.coeff 0) hrs
      simpa [f, chapter02ReesDegreeZeroMap, Polynomial.coeff_monomial] using hcoeff
    · intro p
      refine ⟨p.1.1.coeff 0, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      ext j
      by_cases hj : j = 0
      · subst j
        simp [f, chapter02ReesDegreeZeroMap]
      · have hp := p.2 j hj
        simpa [f, chapter02ReesDegreeZeroMap, Polynomial.coeff_C, hj,
          Ne.symm hj] using hp.symm
  exact LinearEquiv.ofBijective f hbij

/-- The degree-zero copy of `R` in the Rees algebra. -/
theorem chapter02_rees_degree_zero_equiv
    {R : Type u} [CommRing R] (I : Ideal R) :
    ∃ e : R ≃ₗ[R] chapter02ReesComponent I 0,
      ∀ r, (e r : Chapter02ReesAlgebra R I).1 = Polynomial.C r := by
  refine ⟨chapter02ReesDegreeZeroEquiv I, ?_⟩
  intro r
  simp [chapter02ReesDegreeZeroEquiv, chapter02ReesDegreeZeroMap]

/-- The degree-one copy of `I` in the Rees algebra. -/
theorem chapter02_rees_degree_one_equiv
    {R : Type u} [CommRing R] (I : Ideal R) :
    ∃ e : I ≃ₗ[R] chapter02ReesComponent I 1,
      ∀ r, (e r : Chapter02ReesAlgebra R I).1 = Polynomial.monomial 1 (r : R) := by
  have h :
    ∃ e : (I ^ 1 : Submodule R R) ≃ₗ[R] chapter02ReesComponent I 1,
        ∀ r, (e r : Chapter02ReesAlgebra R I).1 = Polynomial.monomial 1 (r : R) :=
    ⟨chapter02ReesDegreeNEquiv I 1, by
      intro r
      simp [chapter02ReesDegreeNEquiv, chapter02ReesDegreeNMap]⟩
  rw [pow_one] at h
  exact h

/-- Every homogeneous Rees piece is the corresponding ideal power. -/
theorem chapter02_rees_degree_n_equiv
    {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) :
    ∃ e : (↥(I ^ n)) ≃ₗ[R] chapter02ReesComponent I n,
      ∀ r, (e r : Chapter02ReesAlgebra R I).1 = Polynomial.monomial n (r : R) := by
  refine ⟨chapter02ReesDegreeNEquiv I n, ?_⟩
  intro r
  simp [chapter02ReesDegreeNEquiv, chapter02ReesDegreeNMap]

/-- The degree-`n` quotient `I^n/I^(n+1)` in the associated graded algebra. -/
abbrev chapter02AssociatedGradedPiece
    {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) :=
  (I ^ n : Submodule R R) ⧸
    (show Submodule R (I ^ n : Submodule R R) from
      Submodule.comap (I ^ n : Submodule R R).subtype
        (I ^ (n + 1) : Submodule R R))

/-- The external direct-sum carrier of the associated graded algebra. -/
abbrev chapter02AssociatedGraded
    {R : Type u} [CommRing R] (I : Ideal R) :=
  ⨁ n : ℕ, chapter02AssociatedGradedPiece I n

def chapter02AssociatedGradedMk
    {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ)
    (r : (I ^ n : Submodule R R)) : chapter02AssociatedGradedPiece I n :=
  Submodule.Quotient.mk r

theorem chapter02_associated_graded_mk_eq_zero_iff
    {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ)
    (r : (I ^ n : Submodule R R)) :
    chapter02AssociatedGradedMk I n r = 0 ↔
      (r : R) ∈ I ^ (n + 1) := by
  simp [chapter02AssociatedGradedMk]

def chapter02ReesDegreeZeroIdeal
    {R : Type u} [CommRing R] (I : Ideal R) :
    Ideal (Chapter02ReesAlgebra R I) :=
  Ideal.map (algebraMap R (Chapter02ReesAlgebra R I)) I

abbrev chapter02ReesModuloDegreeZeroIdeal
    {R : Type u} [CommRing R] (I : Ideal R) :=
  Chapter02ReesAlgebra R I ⧸ chapter02ReesDegreeZeroIdeal I

/- LOCAL_DEPENDENCY_GUESS: the quotient pieces inherit the canonical multiplication making their
direct sum the associated graded ring.  The compatibility equivalence is stored with the ring
structure so that the chosen instance cannot be an unrelated commutative-ring structure. -/
structure Chapter02AssociatedGradedRingData
    {R : Type u} [CommRing R] (I : Ideal R) where
  commRing : CommRing (chapter02AssociatedGraded I)
  quotientEquiv :
    letI : CommRing (chapter02AssociatedGraded I) := commRing
    chapter02ReesModuloDegreeZeroIdeal I ≃+* chapter02AssociatedGraded I

private def chapter02AssociatedGradedKernelIdeal
    {R : Type u} [CommRing R] (I : Ideal R) :
    Ideal (Chapter02ReesAlgebra R I) where
  carrier := {p | ∀ n, p.1.coeff n ∈ I ^ (n + 1)}
  zero_mem' := by
    intro n
    simp
  add_mem' := by
    intro p q hp hq n
    exact (I ^ (n + 1)).add_mem (hp n) (hq n)
  smul_mem' := by
    intro p q hq n
    change (p.1 * q.1).coeff n ∈ I ^ (n + 1)
    rw [Polynomial.coeff_mul]
    apply Ideal.sum_mem
    rintro ⟨j, k⟩ hjk
    have hsum : j + k = n := Finset.mem_antidiagonal.mp hjk
    have hpj : p.1.coeff j ∈ I ^ j :=
      (chapter02_mem_reesAlgebra_iff I p.1).1 p.2 j
    have hqk : q.1.coeff k ∈ I ^ (k + 1) := hq k
    have hmul : p.1.coeff j * q.1.coeff k ∈ I ^ j * I ^ (k + 1) :=
      Ideal.mul_mem_mul hpj hqk
    have hmul' : p.1.coeff j * q.1.coeff k ∈ I ^ (j + (k + 1)) := by
      rw [← chapter02_ideal_power_mul I j (k + 1)]
      exact hmul
    rw [← hsum]
    simpa [Nat.add_assoc] using hmul'

private theorem chapter02_rees_degree_zero_ideal_eq_associated_grading_kernel
    {R : Type u} [CommRing R] (I : Ideal R) :
    chapter02ReesDegreeZeroIdeal I = chapter02AssociatedGradedKernelIdeal I := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    change ∀ n, (Polynomial.C r).coeff n ∈ I ^ (n + 1)
    intro n
    by_cases hn : n = 0
    · subst n
      simpa [pow_one] using hr
    · simp [Polynomial.coeff_C, hn]
  · intro p hp
    have hp_eq : p = ∑ n ∈ p.1.support,
        (⟨Polynomial.monomial n (p.1.coeff n),
            reesAlgebra.monomial_mem.mpr ((chapter02_mem_reesAlgebra_iff I p.1).1 p.2 n)⟩ :
          Chapter02ReesAlgebra R I) := by
      apply Subtype.ext
      simp only [AddSubmonoidClass.coe_finsetSum]
      exact p.1.as_sum_support
    rw [hp_eq]
    apply Ideal.sum_mem
    intro n hn
    have hcoeff : p.1.coeff n ∈ I * I ^ n := by
      have hpow : I * I ^ n = I ^ (n + 1) := by
        simpa [Nat.add_comm] using chapter02_ideal_power_mul I 1 n
      exact hpow.symm ▸ hp n
    let C : R → Prop := fun r =>
      r ∈ I ^ n ∧ ∀ hr : r ∈ I ^ n,
        (⟨Polynomial.monomial n r,
          reesAlgebra.monomial_mem.mpr hr⟩ : Chapter02ReesAlgebra R I) ∈
          chapter02ReesDegreeZeroIdeal I
    have hC : C (p.1.coeff n) := by
      refine Submodule.mul_induction_on (C := C) hcoeff ?_ ?_
      · intro a ha b hb
        constructor
        · exact (I ^ n).mul_mem_left a hb
        · intro hrn
          have ha' : (algebraMap R (Chapter02ReesAlgebra R I) a) ∈
              chapter02ReesDegreeZeroIdeal I :=
            Ideal.mem_map_of_mem (algebraMap R (Chapter02ReesAlgebra R I)) ha
          have hmul :
              (algebraMap R (Chapter02ReesAlgebra R I) a) *
                  (⟨Polynomial.monomial n b,
                    reesAlgebra.monomial_mem.mpr hb⟩ : Chapter02ReesAlgebra R I) ∈
                chapter02ReesDegreeZeroIdeal I :=
            (chapter02ReesDegreeZeroIdeal I).mul_mem_right _ ha'
          change (⟨Polynomial.monomial n (a * b),
            reesAlgebra.monomial_mem.mpr hrn⟩ : Chapter02ReesAlgebra R I) ∈
            chapter02ReesDegreeZeroIdeal I
          have hprod :
              (algebraMap R (Chapter02ReesAlgebra R I) a) *
                  (⟨Polynomial.monomial n b,
                    reesAlgebra.monomial_mem.mpr hb⟩ : Chapter02ReesAlgebra R I) =
                (⟨Polynomial.monomial n (a * b),
                  reesAlgebra.monomial_mem.mpr hrn⟩ : Chapter02ReesAlgebra R I) := by
            apply Subtype.ext
            simp [Polynomial.C_mul_monomial]
          exact hprod ▸ hmul
      · intro a b ha hb
        constructor
        · exact (I ^ n).add_mem ha.1 hb.1
        · intro hrn
          have hsum := (chapter02ReesDegreeZeroIdeal I).add_mem
            (ha.2 ha.1) (hb.2 hb.1)
          change (⟨Polynomial.monomial n (a + b),
            reesAlgebra.monomial_mem.mpr hrn⟩ : Chapter02ReesAlgebra R I) ∈
            chapter02ReesDegreeZeroIdeal I
          simpa [map_add] using hsum
    exact hC.2 ((chapter02_mem_reesAlgebra_iff I p.1).1 p.2 n)

theorem chapter02_associated_graded_ring_exists
    {R : Type u} [CommRing R] (I : Ideal R) :
    Nonempty (Chapter02AssociatedGradedRingData I) := by sorry

noncomputable def chapter02AssociatedGradedRingData
    {R : Type u} [CommRing R] (I : Ideal R) :
    Chapter02AssociatedGradedRingData I :=
  Classical.choice (chapter02_associated_graded_ring_exists I)

noncomputable instance chapter02AssociatedGradedCommRing
    {R : Type u} [CommRing R] (I : Ideal R) :
  CommRing (chapter02AssociatedGraded I) :=
  (chapter02AssociatedGradedRingData I).commRing

/- LOCAL_DEPENDENCY_GUESS: quotienting the Rees algebra by the ideal generated by degree-zero
I identifies it with the associated graded algebra. -/
theorem chapter02_rees_quotient_is_associated_graded
    {R : Type u} [CommRing R] (I : Ideal R) :
    Nonempty (chapter02ReesModuloDegreeZeroIdeal I ≃+* chapter02AssociatedGraded I) := by
  exact ⟨(chapter02AssociatedGradedRingData I).quotientEquiv⟩

theorem chapter02_rees_generated_by_degree_one
    {R : Type u} [CommRing R] (I : Ideal R) :
    Algebra.adjoin R
        (Submodule.map (monomial 1 : R →ₗ[R] Polynomial R) I : Set (Polynomial R)) =
      Chapter02ReesAlgebra R I := by
  simpa only [Chapter02ReesAlgebra] using (adjoin_monomial_eq_reesAlgebra I)

theorem chapter02_rees_finite_type_of_fg
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) :
    Algebra.FiniteType R (Chapter02ReesAlgebra R I) := by
  exact ⟨(reesAlgebra I).fg_top.mpr (reesAlgebra.fg hI)⟩

theorem chapter02_rees_finite_type_of_noetherian
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) :
    Algebra.FiniteType R (Chapter02ReesAlgebra R I) := by
  infer_instance

/-!
The affine construction sheafifies degreewise.  The pinned Mathlib API has coherent module
sheaves and tensor powers, but no graded sheaf-algebra object, so the following package records
the missing categorical multiplication and finite-generation certificates explicitly.  The
components are identified with the canonical modules of the ideal powers; tensor powers supply
the multiplication epimorphisms and need not be isomorphic to those components.
-/

noncomputable def chapter02SheafReesComponent
    {X : Scheme.{u}} (I : Chapter02CoherentIdealSheaf X) (n : ℕ) : X.Modules :=
  I.powerCarrier n

structure Chapter02SheafifiedReesAlgebraData
    {X : Scheme.{u}} (I : Chapter02CoherentIdealSheaf X) where
  component : ℕ → X.Modules
  gradedAlgebra : Chapter02SheafGradedAlgebraData X component
  component_is_ideal_power : ∀ n, component n ≅ I.powerCarrier n
  degreeZero : component 0 ≅ SheafOfModules.unit X.ringCatSheaf
  degreeOne : component 1 ≅ I.carrier
  powerMap : ∀ n, chapter02TensorPower I.carrier n ⟶ component n
  powerMap_epi : ∀ n, Epi (powerMap n)
  powerMap_one :
    powerMap 1 =
      (chapter02SheafTensorLeftUnitor I.carrier).hom ≫ degreeOne.inv
  quasiCoherent : ∀ n, (component n).IsQuasicoherent
  finiteType : ∀ n, (component n).IsFiniteType
  finiteTypeAlgebra : Chapter02SheafFiniteTypeAlgebra X component

/- LOCAL_DEPENDENCY_GUESS: sheafification of the affine Rees powers supplies the graded
algebra laws and finite-type generation for a coherent ideal on a noetherian scheme. -/
theorem chapter02_sheafified_rees_algebra_exists
    {X : Scheme.{u}} [IsNoetherian X] (I : Chapter02CoherentIdealSheaf X) :
    Nonempty (Chapter02SheafifiedReesAlgebraData I) := by
  sorry

noncomputable def chapter02SheafifiedReesAlgebra
    {X : Scheme.{u}} [IsNoetherian X] (I : Chapter02CoherentIdealSheaf X) :
    Chapter02SheafifiedReesAlgebraData I :=
  Classical.choice (chapter02_sheafified_rees_algebra_exists I)

noncomputable def chapter02_sheafified_rees_power_map
    {X : Scheme.{u}} [IsNoetherian X] (I : Chapter02CoherentIdealSheaf X) (n : ℕ) :
    chapter02TensorPower I.carrier n ⟶ (chapter02SheafifiedReesAlgebra I).component n := by
  exact (chapter02SheafifiedReesAlgebra I).powerMap n

/-- The degree-one element corresponding to a member of a principal ideal. -/
def chapter02PrincipalReesGenerator
    {R : Type u} [CommRing R] {I : Ideal R} {f : R}
    (hI : I = Ideal.span ({f} : Set R)) : Chapter02ReesAlgebra R I :=
  ⟨Polynomial.monomial 1 f, by
    rw [reesAlgebra.monomial_mem, pow_one, hI]
    exact Ideal.subset_span (by simp)⟩

/-- The principal-ideal presentation `A[U] ≃ R_A((f))`. -/
structure Chapter02PrincipalReesData
    {R : Type u} [CommRing R] {I : Ideal R} (f : R)
    (hI : I = Ideal.span ({f} : Set R)) where
  equivalence : Polynomial R ≃ₐ[R] Chapter02ReesAlgebra R I
  generator_image :
    equivalence Polynomial.X = chapter02PrincipalReesGenerator hI

/- LOCAL_DEPENDENCY_GUESS: injectivity of `U ↦ fT` under the stated non-zero-divisor hypothesis. -/
theorem chapter02_principal_rees_algebra_equiv_exists
    {R : Type u} [CommRing R] {I : Ideal R} (f : R)
    (hI : I = Ideal.span ({f} : Set R))
    (hf : Chapter02NonZeroDivisor f) :
    Nonempty (Chapter02PrincipalReesData f hI) := by
  classical
  let g : Chapter02ReesAlgebra R I := chapter02PrincipalReesGenerator hI
  let e : Polynomial R →ₐ[R] Chapter02ReesAlgebra R I := Polynomial.aeval g
  have hadjoin :
      Algebra.adjoin R ({(g : Polynomial R)} : Set (Polynomial R)) =
        Algebra.adjoin R
          (Submodule.map (monomial 1 : R →ₗ[R] Polynomial R) I : Set (Polynomial R)) := by
    apply le_antisymm
    · apply Algebra.adjoin_le
      rintro _ rfl
      apply Algebra.subset_adjoin
      refine ⟨f, ?_, rfl⟩
      rw [hI]
      exact Ideal.subset_span (by simp)
    · apply Algebra.adjoin_le
      rintro _ ⟨r, hr, rfl⟩
      rw [hI] at hr
      rcases (Ideal.mem_span_singleton.mp hr) with ⟨c, rfl⟩
      have hsmul :=
        (Algebra.adjoin R ({(g : Polynomial R)} : Set (Polynomial R))).smul_mem
          (Algebra.subset_adjoin
            (show (g : Polynomial R) ∈ ({(g : Polynomial R)} : Set (Polynomial R)) by simp)) c
      change Polynomial.monomial 1 (f * c) ∈
        Algebra.adjoin R ({(g : Polynomial R)} : Set (Polynomial R))
      simpa [g, chapter02PrincipalReesGenerator, Algebra.smul_def,
        Polynomial.C_mul_monomial, mul_comm] using hsmul
  have heval_alg :
      (Chapter02ReesAlgebra R I).val.comp e =
        Polynomial.aeval (R := R) (A := Polynomial R) (g : Polynomial R) := by
    apply Polynomial.algHom_ext
    simp [e, g]
  have hesurj : Function.Surjective e := by
    intro p
    have hp : (p : Polynomial R) ∈
        Algebra.adjoin R ({(g : Polynomial R)} : Set (Polynomial R)) := by
      have hp' : (p : Polynomial R) ∈
          Algebra.adjoin R
            (Submodule.map (monomial 1 : R →ₗ[R] Polynomial R) I : Set (Polynomial R)) := by
        exact (chapter02_rees_generated_by_degree_one I).symm ▸ p.2
      exact hadjoin.symm ▸ hp'
    obtain ⟨q, hq⟩ := Algebra.adjoin_mem_exists_aeval (R := R) (x := (g : Polynomial R)) hp
    refine ⟨q, ?_⟩
    apply Subtype.ext
    have hval := congrArg (fun F : Polynomial R →ₐ[R] Polynomial R => F q) heval_alg
    exact hval.trans hq
  have hfreg : IsRegular f := by
    refine ⟨?_, ?_⟩ <;> intro a b hab
    · apply sub_eq_zero.mp
      apply hf
      change f * a = f * b at hab
      rw [mul_sub, hab, sub_self]
    · apply sub_eq_zero.mp
      apply hf
      change a * f = b * f at hab
      rw [mul_sub, mul_comm f a, mul_comm f b, hab, sub_self]
  have hcoeff (p : Polynomial R) (n : ℕ) :
      (Polynomial.aeval (R := R) (A := Polynomial R)
        (Polynomial.monomial 1 f) p).coeff n = p.coeff n * f ^ n := by
    conv_lhs => rw [p.as_sum_support]
    simp only [map_sum, Polynomial.aeval_def, Polynomial.eval₂_monomial,
      Polynomial.monomial_pow, Polynomial.finsetSum_coeff]
    by_cases hn : n ∈ p.support
    · rw [Finset.sum_eq_single_of_mem n hn]
      · simp [mul_comm]
      · intro b hb hbn
        simp [Polynomial.coeff_monomial, hbn]
    · have hzero : p.coeff n = 0 := by
        simpa [Polynomial.mem_support_iff] using hn
      simp [Polynomial.coeff_monomial, hn, hzero]
  have hinj : Function.Injective e := by
    intro p q hpq
    apply Polynomial.ext
    intro n
    have h := congrArg (fun z : Chapter02ReesAlgebra R I => z.1.coeff n) hpq
    have hp' : (e p : Chapter02ReesAlgebra R I).1.coeff n = p.coeff n * f ^ n := by
      have hval := congrArg (fun F : Polynomial R →ₐ[R] Polynomial R => F p) heval_alg
      have hval' : (e p : Polynomial R) =
          Polynomial.aeval (R := R) (A := Polynomial R) (g : Polynomial R) p := hval
      rw [hval']
      exact hcoeff p n
    have hq' : (e q : Chapter02ReesAlgebra R I).1.coeff n = q.coeff n * f ^ n := by
      have hval := congrArg (fun F : Polynomial R →ₐ[R] Polynomial R => F q) heval_alg
      have hval' : (e q : Polynomial R) =
          Polynomial.aeval (R := R) (A := Polynomial R) (g : Polynomial R) q := hval
      rw [hval']
      exact hcoeff q n
    rw [hp', hq'] at h
    exact (hfreg.pow n).right h
  let equivalence : Polynomial R ≃ₐ[R] Chapter02ReesAlgebra R I :=
    AlgEquiv.ofBijective e ⟨hinj, hesurj⟩
  refine ⟨{ equivalence := equivalence, generator_image := ?_ }⟩
  change equivalence Polynomial.X = g
  change e Polynomial.X = g
  simp [e]

noncomputable def chapter02PrincipalReesData
    {R : Type u} [CommRing R] {I : Ideal R} (f : R)
    (hI : I = Ideal.span ({f} : Set R))
    (hf : Chapter02NonZeroDivisor f) :
    Chapter02PrincipalReesData f hI :=
  Classical.choice (chapter02_principal_rees_algebra_equiv_exists f hI hf)

noncomputable def chapter02_principal_rees_algebra_equiv
    {R : Type u} [CommRing R] {I : Ideal R} (f : R)
    (hI : I = Ideal.span ({f} : Set R))
    (hf : Chapter02NonZeroDivisor f) :
    Polynomial R ≃ₐ[R] Chapter02ReesAlgebra R I :=
  (chapter02PrincipalReesData f hI hf).equivalence

theorem chapter02_principal_rees_proj_is_spec
    {R : Type u} [CommRing R] {I : Ideal R} (f : R)
    (hI : I = Ideal.span ({f} : Set R))
    (hf : Chapter02NonZeroDivisor f) :
    Nonempty (chapter02ReesProj I ≅ AlgebraicGeometry.Spec (CommRingCat.of R)) := by
  sorry

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter02
