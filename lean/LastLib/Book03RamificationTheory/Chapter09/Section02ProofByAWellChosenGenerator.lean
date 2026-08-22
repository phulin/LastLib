import LastLib.Book03RamificationTheory.Chapter09.Section01TheFormulaAndItsHypotheses

namespace LastLib.Book03RamificationTheory.Chapter09

noncomputable section

open LastLib.Book03RamificationTheory.Chapter07
open Polynomial
open scoped Classical
open scoped BigOperators Polynomial

/-! ## 9.2. Proof by a well-chosen generator -/

def chapter09ResidueMoving
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    (w : AddValuation L (WithTop ℤ))
    (σ : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
      F w.toValuation.valuationSubring)
    (θ : w.toValuation.valuationSubring) : Prop :=
  IsLocalRing.residue w.toValuation.valuationSubring (σ • θ) ≠
    IsLocalRing.residue w.toValuation.valuationSubring θ

def chapter09InertialAutomorphism
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    (w : AddValuation L (WithTop ℤ))
    (σ : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
      F w.toValuation.valuationSubring) : Prop :=
  σ ∈ LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05InertiaGroup
    F w.toValuation.valuationSubring

def chapter09DisplacementValue
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    (w : AddValuation L (WithTop ℤ))
    (σ : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
      F w.toValuation.valuationSubring)
    (x : w.toValuation.valuationSubring) : WithTop ℤ :=
  w ((σ : Gal(L / F)) (x : L) - (x : L))

theorem chapter09_residue_moving_displacement_zero
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    (w : AddValuation L (WithTop ℤ))
    [Valuation.IsRankOneDiscrete w.toValuation]
    (σ : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
      F w.toValuation.valuationSubring)
    (θ : w.toValuation.valuationSubring)
    (hmove : chapter09ResidueMoving w σ θ) :
    chapter09DisplacementValue w σ θ = 0 := by
  change w ((σ : Gal(L / F)) (θ : L) - (θ : L)) = 0
  have hresdiff :
      IsLocalRing.residue w.toValuation.valuationSubring ((σ • θ) - θ) ≠ 0 := by
    intro hzero
    apply hmove
    apply sub_eq_zero.mp
    simpa only [map_sub] using hzero
  have hunit : IsUnit ((σ • θ) - θ) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit ((σ • θ) - θ)).mp hresdiff
  have hcast :
      (((σ • θ) - θ : w.toValuation.valuationSubring) : L) =
        (σ : Gal(L / F)) (θ : L) - (θ : L) := by
    rfl
  have hval_sub :
      w.toValuation (((σ • θ) - θ : w.toValuation.valuationSubring) : L) = 1 := by
    exact (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.valuationSubring.integers w.toValuation)).mp hunit
  have hval :
      w.toValuation ((σ : Gal(L / F)) (θ : L) - (θ : L)) = 1 := by
    rw [← hcast]
    exact hval_sub
  have hval' :
      Multiplicative.ofAdd (OrderDual.toDual
        (w ((σ : Gal(L / F)) (θ : L) - (θ : L)))) =
        1 := by
    simpa only [AddValuation.toValuation_apply] using hval
  have hdual :
      OrderDual.toDual
          (w ((σ : Gal(L / F)) (θ : L) - (θ : L))) =
        OrderDual.toDual (0 : WithTop ℤ) := by
    apply Multiplicative.ofAdd.injective
    simpa using hval'
  change w ((σ : Gal(L / F)) (θ : L) - (θ : L)) = 0 at hdual
  exact hdual

theorem chapter09_inertial_mixed_displacement
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    (w : AddValuation L (WithTop ℤ))
    (σ : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
      F w.toValuation.valuationSubring)
    (θ πL : w.toValuation.valuationSubring)
    (_hinertial : chapter09InertialAutomorphism w σ)
    (hθfixed : (σ : Gal(L / F)) (θ : L) = (θ : L)) :
    chapter09DisplacementValue w σ (θ + πL) =
      chapter09DisplacementValue w σ πL := by
  simp [chapter09DisplacementValue, hθfixed]

def chapter09MixedGenerator
    {B : Type*} [AddCommMonoid B] (θ πL : B) : B :=
  θ + πL

@[simp] theorem chapter09_mixed_generator_apply
    {B : Type*} [AddCommMonoid B] (θ πL : B) :
    chapter09MixedGenerator θ πL = θ + πL :=
  rfl

theorem chapter09_mixed_generator_recovers_uniformizer
    {B : Type*} [AddCommGroup B] (θ πL : B) :
    chapter09MixedGenerator θ πL - θ = πL := by
  simp [chapter09MixedGenerator]

def chapter09ResidueGenerator
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    (θbar : l) : Prop :=
  Algebra.adjoin k ({θbar} : Set l) = ⊤

theorem chapter09_separable_residue_extension_has_generator
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] [Algebra.IsSeparable k l] :
    ∃ θbar : l, chapter09ResidueGenerator k l θbar := by
  obtain ⟨θbar, hθbar⟩ := Field.exists_primitive_element k l
  refine ⟨θbar, ?_⟩
  unfold chapter09ResidueGenerator
  apply Algebra.adjoin_eq_top_of_intermediateField (S := ({θbar} : Set l))
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact IsAlgebraic.of_finite k θbar
  · exact hθbar

def chapter09SeparatingLift
    (A B k l : Type*) [CommRing A] [CommRing B]
    [Field k] [Field l] [Algebra k l] [Algebra A B]
    (ρA : A →+* k) (ρB : B →+* l) (θ : B) : Prop :=
  Function.Surjective ρA ∧ Function.Surjective ρB ∧
    (∀ a : A,
      ρB (algebraMap A B a) = algebraMap k l (ρA a)) ∧
    chapter09ResidueGenerator k l (ρB θ)

def chapter09IntegralGeneratorCertificate
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (α : B) : Prop :=
  IsIntegral A α ∧ Algebra.adjoin A ({α} : Set B) = ⊤

/- The separating residue generator and the uniformizer are kept as a single
   certificate.  The residue-field maps make the phrase "lift of a
   separating generator" precise without introducing a second copy of the
   unramified intermediate field. -/
structure Chapter09MixedGeneratorChoice
    (A B k l L : Type*) [CommRing A] [CommRing B]
    [Field k] [Field l] [Field L] [Algebra A B] [Algebra k l]
    [Algebra B L] [Algebra A L] [IsScalarTower A B L]
    (vL : AddValuation L (WithTop ℤ)) where
  θ : B
  πL : B
  ρA : A →+* k
  ρB : B →+* l
  residue_lift : chapter09SeparatingLift A B k l ρA ρB θ
  theta_integral : IsIntegral A θ
  pi_integral : IsIntegral A πL
  uniformizer : vL (algebraMap B L πL) = (1 : WithTop ℤ)
  alpha : B
  alpha_eq : alpha = chapter09MixedGenerator θ πL
  integral_generator : chapter09IntegralGeneratorCertificate A B alpha

theorem chapter09_mixed_generator_is_integral
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (θ πL : B) (hθ : IsIntegral A θ) (hπL : IsIntegral A πL) :
    IsIntegral A (chapter09MixedGenerator θ πL) := by
  exact hθ.add hπL

theorem chapter09_mixed_generator_choice_recovers_uniformizer
    {A B k l L : Type*} [CommRing A] [CommRing B]
    [Field k] [Field l] [Field L] [Algebra A B] [Algebra k l]
    [Algebra B L] [Algebra A L] [IsScalarTower A B L]
    (vL : AddValuation L (WithTop ℤ))
    (C : Chapter09MixedGeneratorChoice A B k l L vL) :
    C.alpha - C.θ = C.πL := by
  rw [C.alpha_eq]
  exact chapter09_mixed_generator_recovers_uniformizer C.θ C.πL

theorem chapter09_mixed_generator_choice_is_integrally_monogenic
    {A B k l L : Type*} [CommRing A] [CommRing B]
    [Field k] [Field l] [Field L] [Algebra A B] [Algebra k l]
    [Algebra B L] [Algebra A L] [IsScalarTower A B L]
    (vL : AddValuation L (WithTop ℤ))
    (C : Chapter09MixedGeneratorChoice A B k l L vL) :
    chapter09IntegralGeneratorCertificate A B C.alpha :=
  C.integral_generator

theorem chapter09_generator_certificate
    {A B K L : Type*}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDedekindDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsIntegralClosure B A L] [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B] [Finite (Gal(L / K))]
    [Fintype (Gal(L / K))]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    [Algebra (chapter09ResidueField vK) (chapter09ResidueField vL)]
    [FiniteDimensional (chapter09ResidueField vK)
      (chapter09ResidueField vL)]
    (S : Chapter09HilbertFormulaSetup A B K L vK vL) :
    chapter09IntegralGeneratorCertificate A B S.α := by
  exact ⟨S.monogenic.1, S.monogenic.2.1⟩

theorem chapter09_generator_polynomial_is_minimal
    {A B K L : Type*}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDedekindDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsIntegralClosure B A L] [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B] [Finite (Gal(L / K))]
    [Fintype (Gal(L / K))]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    [Algebra (chapter09ResidueField vK) (chapter09ResidueField vL)]
    [FiniteDimensional (chapter09ResidueField vK)
      (chapter09ResidueField vL)]
    (S : Chapter09HilbertFormulaSetup A B K L vK vL) :
    S.f.map (algebraMap A K) = minpoly K (algebraMap B L S.α) := by
  exact S.monogenic.2.2.2.2

theorem chapter09_conjugate_product_is_monic
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Fintype (Gal(L / K))] (α : L) :
    (chapter09ConjugateProductPolynomial (K := K) (L := L) α).Monic := by
  exact Polynomial.monic_prod_of_monic (Finset.univ : Finset (Gal(L / K)))
    (fun σ => Polynomial.X - Polynomial.C (σ α))
    (fun σ _ => Polynomial.monic_X_sub_C _)

theorem chapter09_conjugate_product_derivative_at_root
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Fintype (Gal(L / K))] (α : L)
    (_horbit : ∀ {σ : Gal(L / K)}, σ α = α → σ = 1) :
    eval α (chapter09ConjugateProductPolynomial (K := K) (L := L) α).derivative =
      ∏ σ ∈ (Finset.univ.erase (1 : Gal(L / K))), (α - σ α) := by
  classical
  have hroot :
      Polynomial.eval α (Polynomial.derivative
        (Finset.prod (Finset.univ : Finset (Gal(L / K)))
          (fun σ => Polynomial.X - Polynomial.C (σ α)))) =
        Finset.prod (Finset.univ.erase (1 : Gal(L / K)))
          (fun σ => α - σ α) := by
    have hd :
        Polynomial.derivative
            (Finset.prod (Finset.univ : Finset (Gal(L / K)))
              (fun σ => Polynomial.X - Polynomial.C (σ α))) =
          Finset.sum (Finset.univ : Finset (Gal(L / K))) (fun σ =>
            Finset.prod (Finset.univ.erase σ)
                (fun τ => Polynomial.X - Polynomial.C (τ α)) *
              (Polynomial.X - Polynomial.C (σ α)).derivative) := by
      change Polynomial.derivative
          ((Multiset.map (fun σ => Polynomial.X - Polynomial.C (σ α))
            (Finset.univ : Finset (Gal(L / K))).1).prod) = _
      rw [Polynomial.derivative_prod]
      rfl
    rw [hd, Polynomial.eval_finsetSum]
    have hsum := Finset.sum_erase_add
      (s := (Finset.univ : Finset (Gal(L / K))))
      (f := fun σ => Polynomial.eval α
        (Finset.prod (Finset.univ.erase σ)
            (fun τ => Polynomial.X - Polynomial.C (τ α)) *
          (Polynomial.X - Polynomial.C (σ α)).derivative))
      (Finset.mem_univ (1 : Gal(L / K)))
    rw [← hsum]
    rw [Finset.sum_eq_zero]
    · simp only [zero_add]
      rw [Polynomial.eval_mul, Polynomial.eval_prod]
      simp
    · intro σ hσ
      rw [Polynomial.eval_mul, Polynomial.eval_prod]
      have hone : (1 : Gal(L / K)) ∈ Finset.univ.erase σ := by
        rw [Finset.mem_erase]
        exact ⟨Ne.symm (Finset.mem_erase.mp hσ |>.1), Finset.mem_univ _⟩
      have hzero :
          Polynomial.eval α
              (Polynomial.X - Polynomial.C ((1 : Gal(L / K)) α)) = 0 := by
        simp
      rw [Finset.prod_eq_zero hone hzero]
      simp
  simpa [chapter09ConjugateProductPolynomial] using hroot

theorem chapter09_generator_derivative_eq_conjugate_difference_product
    {A B K L : Type*}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDedekindDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsIntegralClosure B A L] [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B] [Finite (Gal(L / K))]
    [Fintype (Gal(L / K))]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    [Algebra (chapter09ResidueField vK) (chapter09ResidueField vL)]
    [FiniteDimensional (chapter09ResidueField vK)
      (chapter09ResidueField vL)]
    (S : Chapter09HilbertFormulaSetup A B K L vK vL) :
    algebraMap B L (chapter07DerivativeAt A B S.f S.α) =
      ∏ σ ∈ (Finset.univ.erase (1 : Gal(L / K))),
        (algebraMap B L S.α - σ (algebraMap B L S.α)) := by
  classical
  let αL : L := algebraMap B L S.α
  have hmap_eval :
      algebraMap B L (chapter07DerivativeAt A B S.f S.α) =
        Polynomial.eval αL (S.f.derivative.map (algebraMap A L)) := by
    rw [chapter07DerivativeAt]
    rw [Polynomial.map_aeval_eq_aeval_map (φ := algebraMap A L)
      (ψ := algebraMap B L) (by
        ext x
        simp only [RingHom.comp_apply]
        simp [IsScalarTower.algebraMap_apply A B L])]
    simp [αL, Polynomial.aeval_def]
  have hfactor :
      Polynomial.derivative (S.f.map (algebraMap A L)) =
        Polynomial.derivative (chapter09ConjugateProductPolynomial
          (K := K) (L := L) αL) := by
    apply congrArg (fun p : Polynomial L => p.derivative)
    simpa [αL] using S.conjugate_factorization
  calc
    algebraMap B L (chapter07DerivativeAt A B S.f S.α) =
        Polynomial.eval αL (S.f.derivative.map (algebraMap A L)) := hmap_eval
    _ = Polynomial.eval αL (Polynomial.derivative
        (S.f.map (algebraMap A L))) := by
      rw [Polynomial.derivative_map]
    _ = Polynomial.eval αL (Polynomial.derivative
        (chapter09ConjugateProductPolynomial (K := K) (L := L) αL)) := by
      rw [hfactor]
    _ = ∏ σ ∈ (Finset.univ.erase (1 : Gal(L / K))),
        (αL - σ αL) := by
      apply chapter09_conjugate_product_derivative_at_root αL
      intro σ hσ
      apply S.orbit_separates
      simpa [αL] using hσ
    _ = ∏ σ ∈ (Finset.univ.erase (1 : Gal(L / K))),
        (algebraMap B L S.α - σ (algebraMap B L S.α)) := by
      simp [αL]

theorem chapter09_generator_derivative_value_eq_displacement_sum
    {A B K L : Type*}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDedekindDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsIntegralClosure B A L] [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B] [Finite (Gal(L / K))]
    [Fintype (Gal(L / K))]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    [Algebra (chapter09ResidueField vK) (chapter09ResidueField vL)]
    [FiniteDimensional (chapter09ResidueField vK)
      (chapter09ResidueField vL)]
    (S : Chapter09HilbertFormulaSetup A B K L vK vL) :
    vL (algebraMap B L (chapter07DerivativeAt A B S.f S.α)) =
      (chapter09DisplacementSum S.profile : WithTop ℤ) := by
  calc
    vL (algebraMap B L (chapter07DerivativeAt A B S.f S.α)) =
        (S.d : WithTop ℤ) := S.different_derivative_value
    _ = (chapter09DisplacementSum S.profile : WithTop ℤ) := by
      exact_mod_cast (chapter09_hilbert_different_formula vK vL S).1

theorem chapter09_generator_derivative_value_eq_different_exponent
    {A B K L : Type*}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDedekindDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsIntegralClosure B A L] [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B] [Finite (Gal(L / K))]
    [Fintype (Gal(L / K))]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    [Algebra (chapter09ResidueField vK) (chapter09ResidueField vL)]
    [FiniteDimensional (chapter09ResidueField vK)
      (chapter09ResidueField vL)]
    (S : Chapter09HilbertFormulaSetup A B K L vK vL) :
    vL (algebraMap B L (chapter07DerivativeAt A B S.f S.α)) =
      (S.d : WithTop ℤ) := by
  exact S.different_derivative_value

theorem chapter09_different_exponent_eq_displacement_sum_in_value_group
    {A B K L : Type*}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDedekindDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsIntegralClosure B A L] [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B] [Finite (Gal(L / K))]
    [Fintype (Gal(L / K))]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    [Algebra (chapter09ResidueField vK) (chapter09ResidueField vL)]
    [FiniteDimensional (chapter09ResidueField vK)
      (chapter09ResidueField vL)]
    (S : Chapter09HilbertFormulaSetup A B K L vK vL) :
    (S.d : WithTop ℤ) =
      (chapter09DisplacementSum S.profile : WithTop ℤ) := by
  rw [← chapter09_generator_derivative_value_eq_different_exponent vK vL S]
  exact chapter09_generator_derivative_value_eq_displacement_sum vK vL S

theorem chapter09_different_exponent_eq_displacement_sum
    {A B K L : Type*}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDedekindDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsIntegralClosure B A L] [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B] [Finite (Gal(L / K))]
    [Fintype (Gal(L / K))]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    [Algebra (chapter09ResidueField vK) (chapter09ResidueField vL)]
    [FiniteDimensional (chapter09ResidueField vK)
      (chapter09ResidueField vL)]
    (S : Chapter09HilbertFormulaSetup A B K L vK vL) :
    S.d = chapter09DisplacementSum S.profile := by
  exact (chapter09_hilbert_different_formula vK vL S).1

end

end LastLib.Book03RamificationTheory.Chapter09
