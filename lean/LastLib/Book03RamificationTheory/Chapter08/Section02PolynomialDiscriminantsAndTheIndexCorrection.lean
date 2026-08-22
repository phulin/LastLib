import LastLib.Book03RamificationTheory.Chapter08.Dependencies
import LastLib.Book03RamificationTheory.Chapter07.Section03TheDerivativeFormula

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
  let E := AlgebraicClosure K
  let f := minpoly K pb.gen
  let φ : K →+* E := algebraMap K E
  have hfdeg : 0 < f.degree := by
    exact minpoly.degree_pos pb.isIntegral_gen
  have hfm : f.Monic := minpoly.monic pb.isIntegral_gen
  have hsplit : (f.map φ).Splits := by
    exact IsAlgClosed.splits _
  have hφ : Function.Injective φ := FaithfulSMul.algebraMap_injective K E
  have hroots : ∀ σ : L →ₐ[K] E, σ pb.gen ∈ (f.map φ).roots := by
    intro σ
    have hmapf0 : (f.map φ) ≠ 0 := Polynomial.map_monic_ne_zero hfm
    rw [Polynomial.mem_roots, Polynomial.IsRoot.def,
      Polynomial.eval_map_algebraMap, Polynomial.aeval_algHom_apply]
    · simpa [f] using congrArg σ (minpoly.aeval : aeval pb.gen (minpoly K pb.gen) = 0)
    · exact hmapf0
  have hnodup : (f.map φ).roots.Nodup := by
    exact Polynomial.nodup_roots
      (Polynomial.Separable.map (Algebra.IsSeparable.isSeparable K pb.gen))
  have hres :
      φ ((-1 : K) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.discr) =
        ((f.map φ).roots.map (f.derivative.map φ).eval).prod := by
    calc
      φ ((-1 : K) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.discr) =
          resultant (f.map φ) (f.derivative.map φ) f.natDegree
            (f.natDegree - 1) := by
        rw [Polynomial.resultant_map_map]
        simpa [hfm.leadingCoeff] using
          (congrArg φ (Polynomial.resultant_deriv (f := f) hfdeg)).symm
      _ = ((f.map φ).roots.map (f.derivative.map φ).eval).prod := by
        simpa [Polynomial.natDegree_map_eq_of_injective hφ, hfm.leadingCoeff] using
          (Polynomial.resultant_eq_prod_eval (f.map φ) (f.derivative.map φ)
            (f.natDegree - 1) (by
              simpa [Polynomial.natDegree_map_eq_of_injective hφ] using
                Polynomial.natDegree_derivative_le f) hsplit)
  have hprod :
    ((f.map φ).roots.map (f.derivative.map φ).eval).prod =
        ∏ σ : L →ₐ[K] E, σ (aeval pb.gen f.derivative) := by
    letI : DecidableEq E := Classical.decEq E
    have hroot_sub :
        (∏ x : {x // x ∈ f.aroots E}, (f.derivative.map φ).eval x.1) =
          ((f.map φ).roots.map (f.derivative.map φ).eval).prod := by
      have hmem := Finset.prod_mem_multiset
        (f.map φ).roots
        (fun x : {x // x ∈ (f.map φ).roots} => (f.derivative.map φ).eval x.1)
        ((f.derivative.map φ).eval)
        (by intro x; rfl)
      simpa only [Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
        Multiset.dedup_eq_self.mpr hnodup, Multiset.map_id] using hmem
    rw [← hroot_sub]
    change (∏ x : {x // x ∈ f.aroots E},
      (f.derivative.map (algebraMap K E)).eval x.1) = _
    simp_rw [Polynomial.eval_map_algebraMap]
    symm
    refine @Fintype.prod_equiv (L →ₐ[K] E)
      {x : E // x ∈ f.aroots E} _ _ _ _ pb.liftEquiv'
      (fun σ => σ (aeval pb.gen f.derivative))
      (fun x => aeval x.1 f.derivative) ?_
    intro σ
    rw [PowerBasis.liftEquiv'_apply_coe, aeval_algHom_apply]
  change Polynomial.discr f = Algebra.discr K pb.basis
  apply (algebraMap K E).injective
  rw [Algebra.discr_powerBasis_eq_norm K pb, map_mul, map_pow, map_neg, map_one,
    Algebra.norm_eq_prod_embeddings]
  rw [pb.finrank]
  have hres' :
      (-1 : E) ^ (f.natDegree * (f.natDegree - 1) / 2) * φ f.discr =
        ((f.map φ).roots.map (f.derivative.map φ).eval).prod := by
    simpa [map_mul, map_pow, map_neg, map_one] using hres
  have hsign :
      ((-1 : E) ^ (f.natDegree * (f.natDegree - 1) / 2)) ^ 2 = 1 := by
    rw [← pow_mul]
    simp
  have hdisc :
      φ f.discr = (-1 : E) ^ (f.natDegree * (f.natDegree - 1) / 2) *
        ((f.map φ).roots.map (f.derivative.map φ).eval).prod := by
    calc
      φ f.discr = 1 * φ f.discr := by simp
      _ = ((-1 : E) ^ (f.natDegree * (f.natDegree - 1) / 2)) ^ 2 * φ f.discr := by
        rw [hsign]
      _ = (-1 : E) ^ (f.natDegree * (f.natDegree - 1) / 2) *
          (((-1 : E) ^ (f.natDegree * (f.natDegree - 1) / 2)) * φ f.discr) := by
        ring
      _ = (-1 : E) ^ (f.natDegree * (f.natDegree - 1) / 2) *
          ((f.map φ).roots.map (f.derivative.map φ).eval).prod := by
        rw [hres']
  have hdisc' :
      φ f.discr = (-1 : E) ^ (f.natDegree * (f.natDegree - 1) / 2) *
        (∏ σ : L →ₐ[K] E, σ (aeval pb.gen f.derivative)) := by
    calc
      φ f.discr = (-1 : E) ^ (f.natDegree * (f.natDegree - 1) / 2) *
          ((f.map φ).roots.map (f.derivative.map φ).eval).prod := hdisc
      _ = (-1 : E) ^ (f.natDegree * (f.natDegree - 1) / 2) *
          (∏ σ : L →ₐ[K] E, σ (aeval pb.gen f.derivative)) := by rw [hprod]
  simpa [f, φ, chapter08DiscriminantSign, pb.natDegree_minpoly] using hdisc'

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
  change Algebra.discr A (chapter08MonogenicPowerFamily B α n) = Algebra.discr A b
  rw [← hpower]

/-- The index ideal of an order inside the full integral algebra. -/
noncomputable def chapter08IndexIdeal
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (O : Subalgebra A B) (bO : Module.Basis ι A O) (bB : Module.Basis ι A B) : Ideal A :=
  Ideal.span ({chapter08OrderIndexDeterminant A B O bO bB} : Set A)

theorem chapter08_order_discriminant_index_correction
    (A B : Type*) [CommRing A] [CommRing B]
    [Algebra A B] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (O : Subalgebra A B) (bO : Module.Basis ι A O) (bB : Module.Basis ι A B) :
    chapter08OrderDiscriminant A B O bO =
      chapter08FieldDiscriminant A B bB *
        chapter08OrderIndexDeterminant A B O bO bB ^ 2 := by
  change Algebra.discr A (fun i => (bO i : B)) =
    Algebra.discr A bB * (bB.det (fun i => (bO i : B))) ^ 2
  conv_lhs => rw [← bB.toMatrix_map_vecMul (fun i => (bO i : B))]
  rw [Algebra.discr_of_matrix_vecMul, bB.det_apply]
  ac_rfl

theorem chapter08_order_discriminant_ideal_index_correction
    (A B : Type*) [CommRing A] [CommRing B]
    [Algebra A B] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (O : Subalgebra A B) (bO : Module.Basis ι A O) (bB : Module.Basis ι A B) :
    Ideal.span ({chapter08OrderDiscriminant A B O bO} : Set A) =
      Ideal.span ({chapter08FieldDiscriminant A B bB} : Set A) *
        chapter08IndexIdeal A B O bO bB ^ 2 := by
  have hdisc := chapter08_order_discriminant_index_correction A B O bO bB
  rw [hdisc]
  change Ideal.span ({chapter08FieldDiscriminant A B bB *
      chapter08OrderIndexDeterminant A B O bO bB ^ 2} : Set A) =
    Ideal.span ({chapter08FieldDiscriminant A B bB} : Set A) *
      (Ideal.span ({chapter08OrderIndexDeterminant A B O bO bB} : Set A)) ^ 2
  rw [Ideal.span_singleton_pow]
  change Ideal.span ({chapter08FieldDiscriminant A B bB *
      chapter08OrderIndexDeterminant A B O bO bB ^ 2} : Set A) =
    Ideal.span ({chapter08FieldDiscriminant A B bB} : Set A) *
      Ideal.span ({chapter08OrderIndexDeterminant A B O bO bB ^ 2} : Set A)
  rw [← Ideal.span_singleton_mul_span_singleton]

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
  intro hunit
  change IsUnit (bB.det (fun i => (bO i : B))) at hunit
  have hbasis :
      LinearIndependent A (fun i => (bO i : B)) ∧
        Submodule.span A (Set.range (fun i => (bO i : B))) = ⊤ :=
    (bB.is_basis_iff_det).mpr hunit
  have hspan :
      Submodule.span A (Set.range (fun i => (bO i : B))) ≤ O.toSubmodule := by
    rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact (bO i).property
  have htop : (⊤ : Submodule A B) ≤ O.toSubmodule := by
    rw [← hbasis.2]
    exact hspan
  have hO : O.toSubmodule = (⊤ : Submodule A B) := top_unique htop
  apply hproper
  exact Subalgebra.toSubmodule_injective hO

/- The polynomial discriminant is the order discriminant when the power basis
   is integral and spans the full order. -/
theorem chapter08_power_family_discriminant_is_field_discriminant_of_full_order
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (α : B) (n : ℕ)
    (b : Module.Basis (Fin n) A B)
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
  simp [chapter08BinomialPolynomial, derivative_sub, derivative_X_pow]

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
    (_hroot : aeval (algebraMap B L πL)
      (chapter08BinomialPolynomial A e πK) = 0)
    (hgen : Algebra.adjoin K ({algebraMap B L πL} : Set L) = ⊤)
    (_hdegree : Module.finrank K L = e) (hcoprime : Nat.Coprime e p)
    (hD : ∃! d : ℕ,
      chapter08DifferentIdeal A B = (IsLocalRing.maximalIdeal B) ^ d) :
    chapter08UniqueIdealExponent (IsLocalRing.maximalIdeal B)
        (chapter08DifferentIdeal A B) hD = e - 1 := by
  let f : A[X] := chapter08BinomialPolynomial A e πK
  have hspan : Ideal.span ({πK} : Set A) = IsLocalRing.maximalIdeal A := hE.2.2.2.2
  let _ : (Ideal.span ({πK} : Set A)).IsPrime := by
    rw [hspan]
    infer_instance
  have hE_f : f.IsEisensteinAt (Ideal.span ({πK} : Set A)) := by
    apply hE.1.isEisensteinAt_of_mem_of_notMem
    · rw [hspan]
      exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
    · intro i hi
      exact hE.2.2.1 i hi
    · simpa [Ideal.span_singleton_pow] using hE.2.2.2.1
  have hdegree_f : f.natDegree = e := by
    change (X ^ e - C πK).natDegree = e
    exact natDegree_X_pow_sub_C
  have hrootB : aeval πL f = 0 := by
    apply IsFractionRing.injective B L
    rw [aeval_def, hom_eval₂]
    change eval₂ ((algebraMap B L).comp (algebraMap A B))
      (algebraMap B L πL) f = (algebraMap B L) 0
    rw [← IsScalarTower.algebraMap_eq A B L]
    simpa [aeval_def] using _hroot
  have hclosure :
      (integralClosure A L : Set L) =
        (Algebra.adjoin A ({algebraMap B L πL} : Set L) : Set L) :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.eisenstein_integral_closure_is_root_order
        πK f (algebraMap B L πL)
        hE (by simpa [f] using _hroot) hdegree_f hgen
  have hgenA : Algebra.adjoin A ({πL} : Set B) = ⊤ := by
    apply top_unique
    intro b hb
    have hbL : algebraMap B L b ∈
        Algebra.adjoin A ({algebraMap B L πL} : Set L) := by
      change algebraMap B L b ∈
        (Algebra.adjoin A ({algebraMap B L πL} : Set L) : Set L)
      have hbint : IsIntegral A (algebraMap B L b) :=
        (IsIntegralClosure.isIntegral_iff (R := A) (A := B) (B := L)).mpr
          ⟨b, rfl⟩
      rw [← hclosure]
      exact hbint
    have hmap_adjoin :
        (Algebra.adjoin A ({πL} : Set B)).map
            (IsScalarTower.toAlgHom A B L) =
          Algebra.adjoin A ({algebraMap B L πL} : Set L) := by
      rw [AlgHom.map_adjoin]
      simp
    have hbmap : algebraMap B L b ∈
        (Algebra.adjoin A ({πL} : Set B)).map
          (IsScalarTower.toAlgHom A B L) := by
      rw [hmap_adjoin]
      exact hbL
    rcases hbmap with ⟨c, hc, hcb⟩
    have hcb' : c = b :=
      IsIntegralClosure.algebraMap_injective B A L hcb
    simpa [hcb'] using hc
  have hPiIntegral : IsIntegral A πL := ⟨f, hE.1, hrootB⟩
  have hirrA : Irreducible f :=
    hE_f.irreducible inferInstance hE.1.isPrimitive hE.2.1
  have hprimitive : f.IsPrimitive := hE.1.isPrimitive
  have hirrK : Irreducible (f.map (algebraMap A K)) :=
    (hprimitive.irreducible_iff_irreducible_map_fraction_map).mp hirrA
  have hrootK : aeval (algebraMap B L πL) (f.map (algebraMap A K)) = 0 := by
    simpa only [aeval_map_algebraMap, IsScalarTower.algebraMap_eq A K L] using _hroot
  have hminK : f.map (algebraMap A K) =
      minpoly K (algebraMap B L πL) :=
    minpoly.eq_of_irreducible_of_monic hirrK hrootK
      (hE.1.map (algebraMap A K))
  have hmono : LastLib.Book03RamificationTheory.Chapter07.chapter07MonogenicPresentation
      A B K L πL f :=
    ⟨hPiIntegral, hgenA, hE.1, hrootB, hminK⟩
  let hmap : A[X] →ₐ[A] B := aeval πL
  have hsurj : Function.Surjective hmap := by
    apply (AlgHom.range_eq_top hmap).mp
    rw [← Algebra.adjoin_singleton_eq_range_aeval]
    exact hgenA
  have hker : RingHom.ker hmap = Ideal.span ({f} : Set A[X]) := by
    ext q
    rw [RingHom.mem_ker, Ideal.mem_span_singleton]
    constructor
    · intro hq
      have hqL : aeval (algebraMap B L πL)
          (q.map (algebraMap A K)) = 0 := by
        rw [Polynomial.aeval_map_algebraMap,
          Polynomial.aeval_algebraMap_apply L πL q, hq, map_zero]
      have hdiv := minpoly.dvd K (algebraMap B L πL) hqL
      rw [← hminK] at hdiv
      exact (Polynomial.map_dvd_map (algebraMap A K)
        (FaithfulSMul.algebraMap_injective A K) hE.1).mp hdiv
    · rintro ⟨r, rfl⟩
      rw [map_mul]
      have hf0 : hmap f = 0 := by
        simpa [hmap] using hrootB
      rw [hf0, zero_mul]
  let har : IsAdjoinRootMonic B f :=
    { map := hmap
      map_surjective := hsurj
      ker_map := hker
      monic := hE.1 }
  have hdiff : chapter08DifferentIdeal A B =
      Ideal.span ({aeval πL (derivative f)} : Set B) :=
    LastLib.Book03RamificationTheory.Chapter07.chapter07_different_eq_derivative_ideal
      A B K L πL f hmono
  have hpow : πL ^ e = algebraMap A B πK := by
    have h := hrootB
    simp [f, chapter08BinomialPolynomial, aeval_def] at h
    exact sub_eq_zero.mp h
  have hπKmemA : πK ∈ IsLocalRing.maximalIdeal A := by
    rw [← hπ]
    exact Ideal.mem_span_singleton_self πK
  let _ : IsLocalHom (algebraMap A B) := inferInstance
  have hπKmemB : algebraMap A B πK ∈ IsLocalRing.maximalIdeal B := by
    rw [← Ideal.mem_comap, IsLocalRing.maximalIdeal_comap]
    exact hπKmemA
  have heunitA : IsUnit (e : A) := by
    apply (IsLocalRing.notMem_maximalIdeal).mp
    intro hem
    have hezero : (e : IsLocalRing.ResidueField A) = 0 := by
      exact (IsLocalRing.residue_eq_zero_iff _).mpr hem
    have hcop : IsCoprime (e : IsLocalRing.ResidueField A)
        (p : IsLocalRing.ResidueField A) := hcoprime.cast
    have hpzero : (p : IsLocalRing.ResidueField A) = 0 :=
      CharP.cast_eq_zero (IsLocalRing.ResidueField A) p
    have hcopzero : IsCoprime (e : IsLocalRing.ResidueField A) 0 := by
      simpa [hpzero] using hcop
    exact (isCoprime_zero_right.mp hcopzero).ne_zero hezero
  have heunitB : IsUnit (e : B) := by
    simpa only [map_natCast] using heunitA.map (algebraMap A B)
  have hpowmem : πL ^ e ∈ IsLocalRing.maximalIdeal B := by
    rw [hpow]
    exact hπKmemB
  have hπLmem : πL ∈ IsLocalRing.maximalIdeal B := by
    exact (show (IsLocalRing.maximalIdeal B).IsPrime from inferInstance).mem_of_pow_mem
      e hpowmem
  have hepos : 0 < e := by
    rw [← hdegree_f]
    exact hE.2.1
  have hspanL : Ideal.span ({πL} : Set B) = IsLocalRing.maximalIdeal B := by
    apply le_antisymm
    · exact Ideal.span_le.2 (by simpa using hπLmem)
    · intro b hb
      let q : A[X] := har.modByMonicHom b
      have hqdiv : X ∣ q - C (q.coeff 0) := by
        rw [Polynomial.X_dvd_iff]
        simp
      rcases hqdiv with ⟨r, hr⟩
      have hqdecomp : q = C (q.coeff 0) + X * r := by
        have hq' := (sub_eq_iff_eq_add).mp hr
        simpa [add_comm] using hq'
      have hbq : b = algebraMap A B (q.coeff 0) + πL * hmap r := by
        calc
          b = har.map q := (har.map_modByMonicHom b).symm
          _ = algebraMap A B (q.coeff 0) + πL * hmap r := by
            rw [hqdecomp]
            simp [har, hmap]
      have hterm : πL * hmap r ∈ IsLocalRing.maximalIdeal B :=
        by simpa [mul_comm] using
          (Ideal.mul_mem_left (IsLocalRing.maximalIdeal B) (hmap r) hπLmem)
      have hcmemB : algebraMap A B (q.coeff 0) ∈
          IsLocalRing.maximalIdeal B := by
        have hsub : b - πL * hmap r ∈ IsLocalRing.maximalIdeal B :=
          (IsLocalRing.maximalIdeal B).sub_mem hb hterm
        simpa [hbq] using hsub
      have hcmemA : q.coeff 0 ∈ IsLocalRing.maximalIdeal A := by
        have hcmemB' : q.coeff 0 ∈
            (IsLocalRing.maximalIdeal B).comap (algebraMap A B) := hcmemB
        rw [IsLocalRing.maximalIdeal_comap] at hcmemB'
        exact hcmemB'
      have hcspan : q.coeff 0 ∈ Ideal.span ({πK} : Set A) := by
        rw [hπ]
        exact hcmemA
      rcases (Ideal.mem_span_singleton.mp hcspan) with ⟨d, hd⟩
      have hpowmem' : πL ^ e ∈ Ideal.span ({πL} : Set B) := by
        rw [show e = (e - 1) + 1 by omega, pow_succ]
        exact Ideal.mul_mem_left _ (πL ^ (e - 1))
          (Ideal.mem_span_singleton_self πL)
      have hcmap : algebraMap A B (q.coeff 0) ∈
          Ideal.span ({πL} : Set B) := by
        rw [hd, map_mul, ← hpow]
        simpa [mul_comm] using
          (Ideal.mul_mem_left (Ideal.span ({πL} : Set B))
            (algebraMap A B d) hpowmem')
      have hterm' : πL * hmap r ∈ Ideal.span ({πL} : Set B) := by
        simpa [mul_comm] using
          (Ideal.mul_mem_left (Ideal.span ({πL} : Set B)) (hmap r)
            (Ideal.mem_span_singleton_self πL))
      rw [hbq]
      exact add_mem hcmap hterm'
  have hderiv : aeval πL (derivative f) = (e : B) * πL ^ (e - 1) := by
    simpa [f] using chapter08_binomial_derivative_eval A B e πK πL
  have htarget : chapter08DifferentIdeal A B =
      (IsLocalRing.maximalIdeal B) ^ (e - 1) := by
    rw [hdiff, hderiv, ← Ideal.span_singleton_mul_span_singleton]
    rw [Ideal.span_singleton_eq_top.mpr heunitB, top_mul]
    rw [← Ideal.span_singleton_pow, hspanL]
  exact (hD.unique htarget (chapter08UniqueIdealExponent_spec
    (IsLocalRing.maximalIdeal B) (chapter08DifferentIdeal A B) hD)).symm

/- A concrete dyadic polynomial and the valuation statements used in the
   `Q₂(√2)` example. -/
def chapter08SqrtTwoPolynomial : (ℚ_[2])[X] :=
  chapter08BinomialPolynomial ℚ_[2] 2 (2 : ℚ_[2])

theorem chapter08_sqrt_two_polynomial_derivative :
    derivative chapter08SqrtTwoPolynomial = (C (2 : ℚ_[2]) : (ℚ_[2])[X]) * X := by
  norm_num [chapter08SqrtTwoPolynomial, chapter08BinomialPolynomial, derivative_sub,
    derivative_X_pow]

theorem chapter08_sqrt_two_derivative_value
    (L : Type*) [Field L] [Algebra ℚ_[2] L]
    (α : L) (vL : AddValuation L (WithTop ℤ))
    (_hroot : α ^ 2 = algebraMap ℚ_[2] L (2 : ℚ_[2]))
    (hα : vL α = (1 : WithTop ℤ))
    (h2 : vL (algebraMap ℚ_[2] L (2 : ℚ_[2])) = (2 : WithTop ℤ)) :
    vL (aeval α (derivative chapter08SqrtTwoPolynomial)) =
      (3 : WithTop ℤ) := by
  norm_num [chapter08_sqrt_two_polynomial_derivative, aeval_def, eval₂_at_apply,
    eval₂_mul, eval₂_C, eval₂_X, AddValuation.map_mul, h2, hα]

noncomputable def chapter08SqrtTwoPolynomialDiscriminant : ℚ_[2] :=
  Polynomial.discr chapter08SqrtTwoPolynomial

theorem chapter08_sqrt_two_polynomial_discriminant_is_eight :
    chapter08SqrtTwoPolynomialDiscriminant = (8 : ℚ_[2]) := by
  change (X ^ 2 - C (2 : ℚ_[2])).discr = (8 : ℚ_[2])
  rw [Polynomial.discr_of_degree_eq_two]
  · norm_num
  · apply (degree_eq_iff_natDegree_eq
      (monic_X_pow_sub_C (R := ℚ_[2]) (2 : ℚ_[2]) (n := 2) (by norm_num)).ne_zero).2
    exact
      (natDegree_X_pow_sub_C (R := ℚ_[2]) (n := 2) (r := (2 : ℚ_[2])))

theorem chapter08_sqrt_two_polynomial_discr_is_eight :
    Polynomial.discr chapter08SqrtTwoPolynomial = (8 : ℚ_[2]) := by
  simpa [chapter08SqrtTwoPolynomialDiscriminant] using
    chapter08_sqrt_two_polynomial_discriminant_is_eight

theorem chapter08_sqrt_two_polynomial_discriminant_valuation :
    Padic.addValuation (p := 2) chapter08SqrtTwoPolynomialDiscriminant =
      (3 : WithTop ℤ) := by
  rw [chapter08_sqrt_two_polynomial_discriminant_is_eight]
  norm_num [Padic.addValuation, AddValuation.of_apply, Padic.addValuationDef,
    Padic.valuation_ofNat]
  have hpv : padicValNat 2 8 = 3 := by
    convert padicValNat_base_pow (p := 2) (by norm_num) 3 using 1
  exact_mod_cast hpv

end

end LastLib.Book03RamificationTheory.Chapter08
