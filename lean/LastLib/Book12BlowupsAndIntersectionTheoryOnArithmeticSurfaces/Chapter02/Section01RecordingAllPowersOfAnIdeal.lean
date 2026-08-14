import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter02.Dependencies

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter02

universe u v

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators
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
    simp [chapter02ReesHomogeneous]
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

/- LOCAL_DEPENDENCY_GUESS: the coefficientwise homogeneous pieces form the canonical internal
grading on Mathlib's Rees subalgebra. -/
theorem chapter02_rees_grading_exists
    {R : Type u} [CommRing R] (I : Ideal R) :
    Nonempty (Chapter02ReesGradingData I) := by
  sorry

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

/-- The degree-zero copy of `R` in the Rees algebra. -/
theorem chapter02_rees_degree_zero_equiv
    {R : Type u} [CommRing R] (I : Ideal R) :
    ∃ e : R ≃ₗ[R] chapter02ReesComponent I 0,
      ∀ r, (e r : Chapter02ReesAlgebra R I).1 = Polynomial.C r := by
  sorry

/-- The degree-one copy of `I` in the Rees algebra. -/
theorem chapter02_rees_degree_one_equiv
    {R : Type u} [CommRing R] (I : Ideal R) :
    ∃ e : I ≃ₗ[R] chapter02ReesComponent I 1,
      ∀ r, (e r : Chapter02ReesAlgebra R I).1 = Polynomial.monomial 1 (r : R) := by
  sorry

/-- The degree-`n` quotient `I^n/I^(n+1)` in the associated graded algebra. -/
abbrev chapter02AssociatedGradedPiece
    {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) :=
  (I ^ n : Submodule R R) ⧸
    (I ^ (n + 1) : Submodule R R).comap (I ^ n : Submodule R R).subtype

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
  sorry

/- LOCAL_DEPENDENCY_GUESS: the quotient pieces inherit the canonical multiplication making their
direct sum the associated graded ring. -/
structure Chapter02AssociatedGradedRingData
    {R : Type u} [CommRing R] (I : Ideal R) where
  commRing : CommRing (chapter02AssociatedGraded I)

theorem chapter02_associated_graded_ring_exists
    {R : Type u} [CommRing R] (I : Ideal R) :
    Nonempty (Chapter02AssociatedGradedRingData I) := by
  sorry

noncomputable def chapter02AssociatedGradedRingData
    {R : Type u} [CommRing R] (I : Ideal R) :
    Chapter02AssociatedGradedRingData I :=
  Classical.choice (chapter02_associated_graded_ring_exists I)

noncomputable instance chapter02AssociatedGradedCommRing
    {R : Type u} [CommRing R] (I : Ideal R) :
    CommRing (chapter02AssociatedGraded I) :=
  (chapter02AssociatedGradedRingData I).commRing

def chapter02ReesDegreeZeroIdeal
    {R : Type u} [CommRing R] (I : Ideal R) :
    Ideal (Chapter02ReesAlgebra R I) :=
  Ideal.map (algebraMap R (Chapter02ReesAlgebra R I)) I

abbrev chapter02ReesModuloDegreeZeroIdeal
    {R : Type u} [CommRing R] (I : Ideal R) :=
  Chapter02ReesAlgebra R I ⧸ chapter02ReesDegreeZeroIdeal I

/- LOCAL_DEPENDENCY_GUESS: quotienting the Rees algebra by the ideal generated by degree-zero
I identifies it with the associated graded algebra. -/
theorem chapter02_rees_quotient_is_associated_graded
    {R : Type u} [CommRing R] (I : Ideal R) :
    Nonempty (chapter02ReesModuloDegreeZeroIdeal I ≃+* chapter02AssociatedGraded I) := by
  sorry

theorem chapter02_rees_generated_by_degree_one
    {R : Type u} [CommRing R] (I : Ideal R) :
    Algebra.adjoin R
        (Submodule.map (monomial 1 : R →ₗ[R] Polynomial R) I : Set (Polynomial R)) =
      Chapter02ReesAlgebra R I := by
  exact adjoin_monomial_eq_reesAlgebra

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
the missing categorical multiplication and finite-generation certificates explicitly.
-/

noncomputable def chapter02SheafReesComponent
    {X : Scheme.{u}} (I : Chapter02CoherentIdealSheaf X) (n : ℕ) : X.Modules :=
  chapter02TensorPower I.carrier n

structure Chapter02SheafifiedReesAlgebraData
    {X : Scheme.{u}} (I : Chapter02CoherentIdealSheaf X) where
  component : ℕ → X.Modules
  component_iso : ∀ n, component n ≅ chapter02SheafReesComponent I n
  gradedAlgebra : Chapter02SheafGradedAlgebraData X component
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

@[simp] theorem chapter02_sheafified_rees_component_iso
    {X : Scheme.{u}} [IsNoetherian X] (I : Chapter02CoherentIdealSheaf X) (n : ℕ) :
    (chapter02SheafifiedReesAlgebra I).component n ≅ chapter02SheafReesComponent I n := by
  exact (chapter02SheafifiedReesAlgebra I).component_iso n

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
  sorry

noncomputable def chapter02PrincipalReesData
    {R : Type u} [CommRing R] {I : Ideal R} (f : R)
    (hI : I = Ideal.span ({f} : Set R))
    (hf : Chapter02NonZeroDivisor f) :
    Chapter02PrincipalReesData f hI :=
  Classical.choice (chapter02_principal_rees_algebra_equiv_exists f hI hf)

theorem chapter02_principal_rees_algebra_equiv
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
