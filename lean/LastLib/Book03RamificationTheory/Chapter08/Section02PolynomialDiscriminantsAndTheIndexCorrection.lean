import LastLib.Book03RamificationTheory.Chapter08.Dependencies

namespace LastLib.Book03RamificationTheory.Chapter08

noncomputable section

open Ideal Matrix Polynomial
open scoped BigOperators Polynomial nonZeroDivisors

/-! ## 8.2. Polynomial discriminants and the index correction -/

/-- The field trace Gram matrix attached to a family in `L`. -/
def chapter08FieldTraceGramMatrix
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    {ι : Type*} (b : ι → L) : Matrix ι ι K :=
  fun i j => Algebra.trace K L (b i * b j)

/-- The discriminant of a power basis, in the field containing the extension. -/
noncomputable def chapter08PowerBasisDiscriminant
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (pb : PowerBasis K L) : K :=
  Algebra.discr K pb.basis

@[simp]
theorem chapter08_powerBasis_discriminant_eq_gram_det
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (pb : PowerBasis K L) :
    chapter08PowerBasisDiscriminant K L pb =
      (chapter08FieldTraceGramMatrix K L pb.basis).det := by
  rfl

/-- The sign appearing in the power-basis derivative formula. -/
def chapter08DiscriminantSign (n : ℕ) : ℤ :=
  (-1 : ℤ) ^ (n * (n - 1) / 2)

/-- The polynomial discriminant, kept distinct from an algebra discriminant. -/
noncomputable def chapter08PolynomialDiscriminant
    (R : Type*) [CommRing R] (f : R[X]) : R :=
  Polynomial.discr f

@[simp]
theorem chapter08PolynomialDiscriminant_eq_discr
    (R : Type*) [CommRing R] (f : R[X]) :
    chapter08PolynomialDiscriminant R f = Polynomial.discr f := by
  rfl

theorem chapter08_power_basis_discriminant_eq_norm_derivative
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (pb : PowerBasis K L) :
    chapter08PowerBasisDiscriminant K L pb =
      (chapter08DiscriminantSign pb.dim : K) *
        Algebra.norm K
          (aeval pb.gen (minpoly K pb.gen).derivative) := by
  rw [← pb.finrank]
  simpa [chapter08PowerBasisDiscriminant, chapter08DiscriminantSign] using
    (Algebra.discr_powerBasis_eq_norm K pb)

theorem chapter08_minpoly_polynomial_discriminant_eq_power_basis_discriminant
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (pb : PowerBasis K L) :
    chapter08PolynomialDiscriminant K (minpoly K pb.gen) =
      chapter08PowerBasisDiscriminant K L pb := by
  sorry

/- The minimal polynomial and the power basis are kept separate: the first is
   a polynomial over the base field, while the latter is the finite family
   whose trace Gram determinant is taken. -/
theorem chapter08_power_basis_polynomial_discriminant_formula
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (pb : PowerBasis K L) :
    Algebra.discr K pb.basis =
      (-1 : K) ^ (Module.finrank K L * (Module.finrank K L - 1) / 2) *
        Algebra.norm K
          (aeval pb.gen (minpoly K pb.gen).derivative) := by
  simpa using (Algebra.discr_powerBasis_eq_norm K pb)

/-- The monogenic integral presentation used to identify a polynomial basis with `B`. -/
def chapter08MonogenicIntegralExtension
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] (α : B) : Prop :=
  IsIntegral A α ∧
    Algebra.adjoin A ({α} : Set B) = ⊤ ∧
    Algebra.adjoin K ({algebraMap B L α} : Set L) = ⊤

@[simp]
theorem chapter08MonogenicIntegralExtension_iff
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] (α : B) :
    chapter08MonogenicIntegralExtension A B K L α ↔
      IsIntegral A α ∧
        Algebra.adjoin A ({α} : Set B) = ⊤ ∧
        Algebra.adjoin K ({algebraMap B L α} : Set L) = ⊤ := Iff.rfl

/- The canonical Mathlib constructor packages the field-side part of the
   monogenic hypothesis as a `PowerBasis`. -/
noncomputable def chapter08MonogenicPowerBasis
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (α : L) (hα : IsIntegral K α)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤) : PowerBasis K L :=
  PowerBasis.ofAdjoinEqTop hα hgen

@[simp]
theorem chapter08MonogenicPowerBasis_gen
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (α : L) (hα : IsIntegral K α)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤) :
    (chapter08MonogenicPowerBasis K L α hα hgen).gen = α := by
  rfl

/-- The determinant of the inclusion of a chosen order basis into an integral basis. -/
def chapter08OrderIndexDeterminant
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (O : Subalgebra A B) (bO : Module.Basis ι A O) (bB : Module.Basis ι A B) : A :=
  bB.det (fun i => (bO i : B))

/-- The discriminant of the order basis, computed in the ambient integral algebra. -/
noncomputable def chapter08OrderDiscriminant
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (O : Subalgebra A B) (bO : Module.Basis ι A O) : A :=
  Algebra.discr A (fun i => (bO i : B))

/-- The discriminant of the full integral basis. -/
noncomputable def chapter08FieldDiscriminant
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bB : Module.Basis ι A B) : A :=
  Algebra.discr A bB

/- The polynomial-basis family is kept as a genuine construction, so the
   passage from a minimal polynomial to an order discriminant does not remain
   only a prose convention. -/
def chapter08MonogenicPowerFamily
    (B : Type*) [CommRing B] (α : B) (n : ℕ) : Fin n → B :=
  fun i => α ^ (i : ℕ)

noncomputable def chapter08PowerFamilyDiscriminantElement
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (α : B) (n : ℕ) : A :=
  Algebra.discr A (chapter08MonogenicPowerFamily B α n)

theorem chapter08_power_family_discriminant_eq_field_discriminant_of_power_basis
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (α : B) (n : ℕ) (b : Module.Basis (Fin n) A B)
    (hpower : b = chapter08MonogenicPowerFamily B α n) :
    chapter08PowerFamilyDiscriminantElement A B α n =
      chapter08FieldDiscriminant A B b := by
  sorry

/-- The index ideal of an order inside the full integral algebra. -/
noncomputable def chapter08IndexIdeal
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (O : Subalgebra A B) (bO : Module.Basis ι A O) (bB : Module.Basis ι A B) : Ideal A :=
  Ideal.span ({chapter08OrderIndexDeterminant A B O bO bB} : Set A)

theorem chapter08_order_discriminant_index_correction
    (A B : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Algebra A B] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (O : Subalgebra A B) (bO : Module.Basis ι A O) (bB : Module.Basis ι A B) :
    chapter08OrderDiscriminant A B O bO =
      chapter08FieldDiscriminant A B bB *
        chapter08OrderIndexDeterminant A B O bO bB ^ 2 := by
  sorry

theorem chapter08_order_discriminant_ideal_index_correction
    (A B : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Algebra A B] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (O : Subalgebra A B) (bO : Module.Basis ι A O) (bB : Module.Basis ι A B) :
    Ideal.span ({chapter08OrderDiscriminant A B O bO} : Set A) =
      Ideal.span ({chapter08FieldDiscriminant A B bB} : Set A) *
        chapter08IndexIdeal A B O bO bB ^ 2 := by
  sorry

def chapter08ProperOrder
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (O : Subalgebra A B) : Prop :=
  O ≠ ⊤

theorem chapter08_proper_order_has_nonunit_index
    (A B : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [IsDiscreteValuationRing A] [Algebra A B]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (O : Subalgebra A B) (bO : Module.Basis ι A O) (bB : Module.Basis ι A B)
    (hproper : chapter08ProperOrder A B O) :
    ¬ IsUnit (chapter08OrderIndexDeterminant A B O bO bB) := by
  sorry

/- The polynomial discriminant is the order discriminant when the power basis
   is integral and spans the full order. -/
theorem chapter08_power_family_discriminant_is_field_discriminant_of_full_order
    (A B K L : Type*) [CommRing A] [CommRing B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra K L]
    [Algebra B L] [Algebra A L] [IsScalarTower A K L]
    [IsScalarTower A B L] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsIntegralClosure B A L]
    [IsDedekindDomain A] [IsDedekindDomain B]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B] (α : B) (n : ℕ)
    (b : Module.Basis (Fin n) A B)
    (_hmono : chapter08MonogenicIntegralExtension A B K L α)
    (hpower : b = chapter08MonogenicPowerFamily B α n) :
    chapter08PowerFamilyDiscriminantElement A B α n =
      chapter08FieldDiscriminant A B b := by
  exact chapter08_power_family_discriminant_eq_field_discriminant_of_power_basis
    A B α n b hpower

/-- The binomial Eisenstein polynomial used for the tame example. -/
def chapter08BinomialPolynomial
    (A : Type*) [CommRing A] (e : ℕ) (πK : A) : A[X] :=
  X ^ e - C πK

theorem chapter08_binomial_derivative_eval
    (A L : Type*) [CommRing A] [CommRing L] [Algebra A L]
    (e : ℕ) (πK : A) (πL : L) :
    aeval πL (derivative (chapter08BinomialPolynomial A e πK)) =
      (e : L) * πL ^ (e - 1) := by
  sorry

theorem chapter08_tame_binomial_different_exponent
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [IsDedekindDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra K L]
    [Algebra B L] [Algebra A L] [IsScalarTower A K L]
    [IsScalarTower A B L] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsIntegralClosure B A L] [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B]
    [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (p e : ℕ) [CharP (IsLocalRing.ResidueField A) p]
    (πK : A) (πL : B)
    (hπ : Ideal.span ({πK} : Set A) = IsLocalRing.maximalIdeal A)
    (hE : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt
      πK (chapter08BinomialPolynomial A e πK))
    (hroot : aeval (algebraMap B L πL)
      (chapter08BinomialPolynomial A e πK) = 0)
    (hgen : Algebra.adjoin K ({algebraMap B L πL} : Set L) = ⊤)
    (hdegree : Module.finrank K L = e) (hcoprime : Nat.Coprime e p)
    (hD : ∃! d : ℕ,
      chapter08DifferentIdeal A B = (IsLocalRing.maximalIdeal B) ^ d) :
    chapter08UniqueIdealExponent (IsLocalRing.maximalIdeal B)
        (chapter08DifferentIdeal A B) hD = e - 1 := by
  sorry

/- A concrete dyadic polynomial and the valuation statements used in the
   `Q₂(√2)` example. -/
def chapter08SqrtTwoPolynomial : (ℚ_[2])[X] :=
  chapter08BinomialPolynomial ℚ_[2] 2 (2 : ℚ_[2])

theorem chapter08_sqrt_two_polynomial_derivative :
    derivative chapter08SqrtTwoPolynomial = (C (2 : ℚ_[2]) : (ℚ_[2])[X]) * X := by
  sorry

theorem chapter08_sqrt_two_derivative_value
    (L : Type*) [Field L] [Algebra ℚ_[2] L]
    (α : L) (vL : AddValuation L (WithTop ℤ))
    (hroot : α ^ 2 = algebraMap ℚ_[2] L (2 : ℚ_[2]))
    (hα : vL α = (1 : WithTop ℤ))
    (h2 : vL (algebraMap ℚ_[2] L (2 : ℚ_[2])) = (2 : WithTop ℤ)) :
    vL (aeval α (derivative chapter08SqrtTwoPolynomial)) =
      (3 : WithTop ℤ) := by
  sorry

noncomputable def chapter08SqrtTwoPolynomialDiscriminant : ℚ_[2] :=
  Polynomial.discr chapter08SqrtTwoPolynomial

theorem chapter08_sqrt_two_polynomial_discriminant_is_eight :
    chapter08SqrtTwoPolynomialDiscriminant = (8 : ℚ_[2]) := by
  sorry

theorem chapter08_sqrt_two_polynomial_discr_is_eight :
    Polynomial.discr chapter08SqrtTwoPolynomial = (8 : ℚ_[2]) := by
  simpa [chapter08SqrtTwoPolynomialDiscriminant] using
    chapter08_sqrt_two_polynomial_discriminant_is_eight

theorem chapter08_sqrt_two_polynomial_discriminant_valuation :
    Padic.addValuation (p := 2) chapter08SqrtTwoPolynomialDiscriminant =
      (3 : WithTop ℤ) := by
  sorry

end

end LastLib.Book03RamificationTheory.Chapter08
