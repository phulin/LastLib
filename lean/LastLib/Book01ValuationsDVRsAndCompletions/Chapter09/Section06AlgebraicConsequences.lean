import LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.Section05WorkedLifts

namespace LastLib.Book01ValuationsDVRsAndCompletions
namespace Chapter09

universe u uK uL uΓ uA uH uC uI

open scoped BigOperators Polynomial WithZeroTopology
open Ideal IsLocalRing Polynomial

noncomputable section

local instance chapter09FactPrime7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
local instance chapter09FactPrime2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩

/-! # Chapter 9: Hensel lifting

This file is a statement-generation pass for Chapter 9 of Book 1.  The
declarations deliberately keep the hypotheses visible: in particular, a
complete DVR means adic completeness, while the valuation form is stated for
an arbitrary additive valuation.
-/

/-! # Book 1, Chapter 9, Section 9.6: Algebraic Consequences
-/

/-! ## 9.6 Algebraic consequences -/

/-- A polynomial has a repeated residue root when it and its derivative vanish there. -/
def HasRepeatedResidueRoot {R : Type*} [CommRing R] (f : R[X]) : Prop :=
  ∃ a : R, f.eval a = 0 ∧ f.derivative.eval a = 0

/-- Coefficients of a polynomial are integral over a base ring. -/
def PolynomialCoefficientsIntegralOver {A K : Type*} [CommRing A] [CommRing K]
    [Algebra A K] (f : K[X]) : Prop :=
  ∀ n : ℕ, IsIntegral A (f.coeff n)

/-- A monic factor of a monic polynomial over a fraction field has integral coefficients. -/
theorem monic_factor_coefficients_are_integral {A K : Type*} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K]
    (f : A[X]) (g h : K[X]) (hf : f.Monic) (hg : g.Monic) (hh : h.Monic)
    (hfac : Polynomial.map (algebraMap A K) f = g * h) :
    PolynomialCoefficientsIntegralOver (A := A) (K := K) g ∧ PolynomialCoefficientsIntegralOver (A := A) (K := K) h := by
  constructor
  · intro n
    apply Polynomial.isIntegral_coeff_of_dvd f g hf hg
    exact ⟨h, hfac⟩
  · intro n
    apply Polynomial.isIntegral_coeff_of_dvd f h hf hh
    refine ⟨g, ?_⟩
    rw [mul_comm]
    exact hfac

/-- Integral closedness descends a monic factorization from the fraction field to the DVR. -/
theorem monic_factorization_descends_to_integrally_closed_domain
    {A K : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (f : A[X]) (g h : K[X]) (hf : f.Monic) (hg : g.Monic) (hh : h.Monic)
    (hfac : Polynomial.map (algebraMap A K) f = g * h) :
    ∃ gA hA : A[X],
      gA.Monic ∧ hA.Monic ∧
        Polynomial.map (algebraMap A K) gA = g ∧
        Polynomial.map (algebraMap A K) hA = h ∧ f = gA * hA := by
  have hgdiv : g ∣ Polynomial.map (algebraMap A K) f := ⟨h, hfac⟩
  have hhdiv : h ∣ Polynomial.map (algebraMap A K) f := by
    refine ⟨g, ?_⟩
    rw [mul_comm]
    exact hfac
  obtain ⟨gA, hgA⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K hf hgdiv
  obtain ⟨hA, hhA⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K hf hhdiv
  have hmapg : Polynomial.map (algebraMap A K) gA = g := by
    simpa [hg.leadingCoeff] using hgA
  have hmaph : Polynomial.map (algebraMap A K) hA = h := by
    simpa [hh.leadingCoeff] using hhA
  have hmonicg : gA.Monic := by
    apply Polynomial.monic_of_injective (IsFractionRing.injective A K)
    simpa [hmapg] using hg
  have hmonich : hA.Monic := by
    apply Polynomial.monic_of_injective (IsFractionRing.injective A K)
    simpa [hmaph] using hh
  refine ⟨gA, hA, hmonicg, hmonich, hmapg, hmaph, ?_⟩
  apply Polynomial.map_injective (algebraMap A K) (IsFractionRing.injective A K)
  simpa [Polynomial.map_mul, hmapg, hmaph] using hfac

/-- A monic polynomial with irreducible reduction is irreducible over the fraction field. -/
theorem irreducible_of_irreducible_residue_reduction
    {A K : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K]
    (f : A[X]) (hf : f.Monic)
    (hred : Irreducible (residuePolynomial f)) :
    Irreducible (Polynomial.map (algebraMap A K) f) := by
  have hfa : Irreducible f := by
    apply Polynomial.Monic.irreducible_of_irreducible_map
      (residueMap A) f hf
    simpa [residuePolynomial] using hred
  exact (hf.irreducible_iff_irreducible_map_fraction_map).mp hfa

/-- The converse fails: an irreducible polynomial can acquire a repeated reduction. -/
theorem padic_x_sq_sub_p_irreducible_but_reduction_repeated (p : ℕ) [Fact p.Prime] :
    Irreducible
        (Polynomial.map (algebraMap (ℤ_[p]) (ℚ_[p]))
          (quadraticPolynomial (p : ℤ_[p]))) ∧
      HasRepeatedResidueRoot (quadraticPolynomial (p : ZMod p)) := by
  constructor
  · apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
      (p := Polynomial.map (algebraMap (ℤ_[p]) (ℚ_[p]))
        (quadraticPolynomial (p : ℤ_[p])))
      (by
        have hnd :
            (Polynomial.map (algebraMap (ℤ_[p]) (ℚ_[p]))
              (quadraticPolynomial (p : ℤ_[p]))).natDegree = 2 := by
          simp only [quadraticPolynomial, Polynomial.map_sub, Polynomial.map_pow,
            Polynomial.map_C, Polynomial.map_X]
          rw [natDegree_sub_C, natDegree_X_pow]
        rw [hnd]
        norm_num)
    intro x hx
    apply padic_x_sq_sub_p_has_no_root p
    refine ⟨x, ?_⟩
    have hx' : x ^ 2 = (p : ℚ_[p]) := by
      apply sub_eq_zero.mp
      simpa [quadraticPolynomial] using hx
    exact hx'
  · refine ⟨0, ?_, ?_⟩
    · simp [quadraticPolynomial]
    · simp [quadraticPolynomial]

/-- Henselianity is the hypothesis needed to lift a coprime residue factorization. -/
theorem henselianity_lifts_coprime_residue_factorization
    {A : Type*} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    (f : A[X]) (g₀ h₀ : Polynomial (ResidueRing A))
    (hf : f.Monic) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcop : IsCoprime g₀ h₀) (hred : residuePolynomial f = g₀ * h₀) :
    ∃! gh : A[X] × A[X], IsFactorizationLift f g₀ h₀ gh.1 gh.2 := by
  have hsimple : SimpleResidueRootLiftingProperty A :=
    (henselian_iff_simple_residue_root_lifting (A := A)).mp
      (show IsHenselianLocalRingChapter09 A from by
        change HenselianLocalRing A
        exact inferInstance)
  exact (henselian_factorization_by_successive_linear_lifts hsimple)
    f g₀ h₀ hf hg₀ hh₀ hcop hred

/-- A prime of an extension ring lying above the maximal ideal. -/
def PrimeAboveMaximal {A B : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B] (P : Ideal B) : Prop :=
  P.IsPrime ∧ P.comap (algebraMap A B) = IsLocalRing.maximalIdeal A

/-- A valuation on `L` extends the valuation on `K` up to Mathlib's equivalence relation. -/
def IsValuationExtension {K L ΓK ΓL : Type*} [Field K] [Field L]
    [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL]
    [Algebra K L]
    (vK : Valuation K ΓK) (vL : Valuation L ΓL) : Prop :=
  vK.IsEquiv (vL.comap (algebraMap K L))

/- A valuation extension may require a genuinely larger ordered value group. -/
structure Chapter09ValuationExtension
    {K : Type uK} {L : Type uL} {ΓK : Type uΓ} [Field K] [Field L]
    [LinearOrderedCommGroupWithZero ΓK] [Algebra K L]
    (vK : Valuation K ΓK) where
  ΓL : Type (max (max uK uL) uΓ)
  [valueGroup : LinearOrderedCommGroupWithZero ΓL]
  valuation : Valuation L ΓL
  isExtension : IsValuationExtension vK valuation

def Chapter09ValuationExtensionEquivalent
    {K L ΓK : Type*} [Field K] [Field L]
    [LinearOrderedCommGroupWithZero ΓK] [Algebra K L]
    (vK : Valuation K ΓK)
    (w₁ w₂ : Chapter09ValuationExtension (L := L) vK) : Prop := by
  letI := w₁.valueGroup
  letI := w₂.valueGroup
  exact w₁.valuation.IsEquiv w₂.valuation

def Chapter09ValuationExtensionSetoid
    {K L ΓK : Type*} [Field K] [Field L]
    [LinearOrderedCommGroupWithZero ΓK] [Algebra K L]
    (vK : Valuation K ΓK) : Setoid (Chapter09ValuationExtension (L := L) vK) where
  r := Chapter09ValuationExtensionEquivalent (L := L) vK
  iseqv := by
    constructor
    · intro w
      unfold Chapter09ValuationExtensionEquivalent
      exact fun _ _ => Iff.rfl
    · intro w₁ w₂ h
      unfold Chapter09ValuationExtensionEquivalent at h ⊢
      exact fun x y => Iff.symm (h x y)
    · intro w₁ w₂ w₃ h₁₂ h₂₃
      unfold Chapter09ValuationExtensionEquivalent at h₁₂ h₂₃ ⊢
      exact fun x y => Iff.trans (h₁₂ x y) (h₂₃ x y)

abbrev Chapter09ValuationExtensionClass
    {K L ΓK : Type*} [Field K] [Field L]
    [LinearOrderedCommGroupWithZero ΓK] [Algebra K L]
    (vK : Valuation K ΓK) : Type _ :=
  Quotient (Chapter09ValuationExtensionSetoid (L := L) vK)
/-- The prime/valuation correspondence, expressed as an equivalence of the two parameter spaces. -/
def ExtensionPrimeCorrespondence {A B K L ΓK : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B] [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK] (vK : Valuation K ΓK) : Prop :=
  Nonempty
    ((Chapter09ValuationExtensionClass (L := L) vK ≃
        {P : Ideal B // PrimeAboveMaximal (A := A) (B := B) P}))

/-- There is exactly one extension valuation in the chosen value group. -/
def HasUniqueValuationExtension {K L ΓK : Type*} [Field K] [Field L]
    [LinearOrderedCommGroupWithZero ΓK] [Algebra K L]
    (vK : Valuation K ΓK) : Prop :=
  ∃ w : Chapter09ValuationExtension (L := L) vK,
    ∀ w' : Chapter09ValuationExtension (L := L) vK,
      Chapter09ValuationExtensionEquivalent (L := L) vK w w'

/-- There is exactly one prime of the extension ring above the maximal ideal. -/
def HasUniquePrimeAbove {A B : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B] : Prop :=
  ∃! P : Ideal B, PrimeAboveMaximal (A := A) (B := B) P

/-- A valued field is henselian when its valuation ring is a henselian local ring. -/
def IsHenselianValuedField {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (vK : Valuation K Γ) : Prop :=
  HenselianLocalRing vK.valuationSubring

/-- For a finite extension, primes above the maximal ideal correspond to valuation extensions.
The base ring is required to be the ring of integers of the chosen valuation. -/
theorem finite_extension_prime_valuation_correspondence
    {A B K L Γ : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    [ValuationRing A] [IsIntegrallyClosed A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra A L] [IsScalarTower A K L]
    [CommRing B] [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    [LinearOrderedCommGroupWithZero Γ] (vK : Valuation K Γ)
    (hA : vK.Integers A) :
    ExtensionPrimeCorrespondence (A := A) (B := B) (L := L) vK := by
  sorry

/-- The correspondence transfers uniqueness of a prime to uniqueness of the extension valuation. -/
theorem unique_prime_iff_unique_valuation_extension
    {A B K L Γ : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B] [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ] (vK : Valuation K Γ)
    (hcor : ExtensionPrimeCorrespondence (A := A) (B := B) (L := L) vK) :
    (HasUniquePrimeAbove (A := A) (B := B) ↔
      HasUniqueValuationExtension (L := L) vK) := by
  obtain ⟨e⟩ := hcor
  constructor
  · rintro ⟨P, hP, hPuniq⟩
    let y₀ : {P : Ideal B // PrimeAboveMaximal (A := A) (B := B) P} := ⟨P, hP⟩
    obtain ⟨q₀, hq₀⟩ := e.surjective y₀
    obtain ⟨w₀, hw₀⟩ := Quotient.exists_rep q₀
    have hy₀ : e (Quotient.mk (Chapter09ValuationExtensionSetoid (L := L) vK) w₀) = y₀ := by
      exact (congrArg e hw₀).trans hq₀
    refine ⟨w₀, ?_⟩
    intro w
    have hy :
        e (Quotient.mk (Chapter09ValuationExtensionSetoid (L := L) vK) w) =
          e (Quotient.mk (Chapter09ValuationExtensionSetoid (L := L) vK) w₀) := by
      apply Subtype.ext
      exact (hPuniq _ (e (Quotient.mk (Chapter09ValuationExtensionSetoid (L := L) vK) w)).property).trans
        (hPuniq _ (e (Quotient.mk (Chapter09ValuationExtensionSetoid (L := L) vK) w₀)).property).symm
    have hq :
        Quotient.mk (Chapter09ValuationExtensionSetoid (L := L) vK) w =
          Quotient.mk (Chapter09ValuationExtensionSetoid (L := L) vK) w₀ := e.injective hy
    have hrel : Chapter09ValuationExtensionEquivalent (L := L) vK w₀ w := by
      exact (Chapter09ValuationExtensionSetoid (L := L) vK).iseqv.symm
        (Quotient.exact hq)
    exact hrel
  · rintro ⟨w₀, hw₀⟩
    let y₀ := e (Quotient.mk (Chapter09ValuationExtensionSetoid (L := L) vK) w₀)
    refine ⟨y₀.1, y₀.2, ?_⟩
    intro P hP
    let y : {P : Ideal B // PrimeAboveMaximal (A := A) (B := B) P} := ⟨P, hP⟩
    obtain ⟨q, hq⟩ := e.surjective y
    obtain ⟨w, hw⟩ := Quotient.exists_rep q
    have hrel := hw₀ w
    have hqeq :
        Quotient.mk (Chapter09ValuationExtensionSetoid (L := L) vK) w₀ =
          Quotient.mk (Chapter09ValuationExtensionSetoid (L := L) vK) w := by
      exact Quotient.sound hrel
    have hy :
        y₀ = e (Quotient.mk (Chapter09ValuationExtensionSetoid (L := L) vK) w) :=
      congrArg e hqeq
    have hwy :
        e (Quotient.mk (Chapter09ValuationExtensionSetoid (L := L) vK) w) = y :=
      (congrArg e hw).trans hq
    have hyy : y₀ = y := hy.trans hwy
    exact congrArg Subtype.val hyy.symm

/-- A henselian valued field has one prime above the maximal ideal in every finite extension.
The base ring is required to be the ring of integers of the chosen valuation. -/
theorem henselian_valued_field_has_unique_prime_and_extension
    {A B K L Γ : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    [ValuationRing A] [IsIntegrallyClosed A]
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra A K] [IsFractionRing A K]
    [CommRing B] [Algebra A B] [Algebra B L]
    [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    [LinearOrderedCommGroupWithZero Γ] (vK : Valuation K Γ)
    (hA : vK.Integers A)
    (hH : IsHenselianValuedField vK) :
    HasUniquePrimeAbove (A := A) (B := B) ∧ HasUniqueValuationExtension (L := L) vK := by
  sorry

/-- The finite integral extension has a finite nonempty set of primes above the maximal ideal. -/
theorem finite_extension_primes_above_are_finite
    {A B : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]
    [IsIntegralClosure B A B] [FaithfulSMul A B] :
    Set.Finite {P : Ideal B | PrimeAboveMaximal (A := A) (B := B) P} ∧
      Nonempty {P : Ideal B // PrimeAboveMaximal (A := A) (B := B) P} := by
  let m : Ideal A := IsLocalRing.maximalIdeal A
  have heq : {P : Ideal B | PrimeAboveMaximal (A := A) (B := B) P} =
      m.primesOver B := by
    ext P
    constructor
    · rintro ⟨hprime, hcomap⟩
      exact ⟨hprime, ⟨hcomap.symm⟩⟩
    · rintro ⟨hprime, hover⟩
      exact ⟨hprime, hover.over.symm⟩
  constructor
  · rw [heq]
    exact Algebra.QuasiFinite.finite_primesOver m
  · obtain ⟨P, hPmax, hPover⟩ :=
      exists_maximal_ideal_liesOver_of_isIntegral (S := B) m
    refine ⟨⟨P, ?_⟩⟩
    exact ⟨hPmax.isPrime, hPover.over.symm⟩

/-- A complete rank-one valued field has a henselian valuation ring. -/
theorem complete_valued_field_is_henselian
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ)
    [Valuation.RankOne vK]
    (hcomplete : @CompleteSpace K (Valued.mk' vK).toUniformSpace) :
    IsHenselianValuedField vK := by
  change HenselianLocalRing vK.valuationSubring
  let v : AddValuation K (Additive Γ)ᵒᵈ := Valuation.toAddValuation vK
  have hv_equiv : vK.IsEquiv v.toValuation := by
    rw [Valuation.isEquiv_iff_val_le_one]
    intro x
    rfl
  let hrank : Valuation.RankOne v.toValuation :=
    { hom' := (Valuation.RankOne.hom vK).comp
        hv_equiv.orderMonoidIso.symm.toMonoidWithZeroHom
      strictMono' := (Valuation.RankOne.strictMono vK).comp
        hv_equiv.orderMonoidIso.symm.strictMono
      exists_val_nontrivial := by
        obtain ⟨r, hr0, hr1⟩ := Valuation.RankOne.nontrivial vK
        refine ⟨r, ?_, ?_⟩
        · intro hr
          exact hr0 ((hv_equiv.eq_zero).mpr hr)
        · intro hr
          exact hr1 ((hv_equiv.eq_one_iff_eq_one).mpr hr) }
  have hA : IsValuationSubring vK.valuationSubring.toSubring v := by
    intro x
    change x ∈ vK.valuationSubring ↔ v x ≥ 0
    rw [Valuation.mem_valuationSubring_iff]
    rfl
  have hcomplete' : Chapter09NonarchimedeanComplete v := by
    have hforward : @UniformContinuous K K
        (Valued.mk' vK).toUniformSpace (Valued.mk' v.toValuation).toUniformSpace
        (id : K → K) := hv_equiv.symm.uniformContinuous
    have hback : @UniformContinuous K K
        (Valued.mk' v.toValuation).toUniformSpace (Valued.mk' vK).toUniformSpace
        (id : K → K) := hv_equiv.uniformContinuous
    have hind : @IsUniformInducing K K
        (Valued.mk' vK).toUniformSpace (Valued.mk' v.toValuation).toUniformSpace
        (id : K → K) :=
      @IsUniformInducing.of_comp K K K
        (Valued.mk' vK).toUniformSpace
        (Valued.mk' v.toValuation).toUniformSpace
        (Valued.mk' vK).toUniformSpace
        (id : K → K) (id : K → K) hforward hback
        (@IsUniformInducing.id K (Valued.mk' vK).toUniformSpace)
    have hc : @CompleteSpace K (Valued.mk' v.toValuation).toUniformSpace :=
      (@IsUniformInducing.completeSpace_congr K K
        (Valued.mk' vK).toUniformSpace (Valued.mk' v.toValuation).toUniformSpace
        (id : K → K) hind (Function.surjective_id)).mp hcomplete
    exact hc
  refine { is_henselian := ?_ }
  intro f hf a₀ hfa hunit
  let fK : K[X] := f.map (Subring.subtype vK.valuationSubring.toSubring)
  have hfK : fK.Monic := by
    exact hf.map (Subring.subtype vK.valuationSubring.toSubring)
  have hfcoeff : PolynomialCoefficientsInSubring
      vK.valuationSubring.toSubring fK := by
    intro n
    change (f.map (Subring.subtype vK.valuationSubring.toSubring)).coeff n ∈
      vK.valuationSubring.toSubring
    rw [Polynomial.coeff_map]
    exact (f.coeff n).property
  have hfa_eval : fK.eval (a₀ : K) = ((f.eval a₀ : vK.valuationSubring) : K) := by
    change (f.map (Subring.subtype vK.valuationSubring.toSubring)).eval
        ((Subring.subtype vK.valuationSubring.toSubring) a₀) =
      (Subring.subtype vK.valuationSubring.toSubring) (f.eval a₀)
    exact Polynomial.eval_map_apply
      (Subring.subtype vK.valuationSubring.toSubring) a₀
  have hderiv_eval : fK.derivative.eval (a₀ : K) =
      ((f.derivative.eval a₀ : vK.valuationSubring) : K) := by
    rw [show fK.derivative =
        f.derivative.map (Subring.subtype vK.valuationSubring.toSubring) by
      simp [fK]]
    change (f.derivative.map (Subring.subtype vK.valuationSubring.toSubring)).eval
        ((Subring.subtype vK.valuationSubring.toSubring) a₀) =
      (Subring.subtype vK.valuationSubring.toSubring) (f.derivative.eval a₀)
    exact Polynomial.eval_map_apply
      (Subring.subtype vK.valuationSubring.toSubring) a₀
  have hfa_val : v (fK.eval (a₀ : K)) > 0 := by
    have hlt : vK ((f.eval a₀ : vK.valuationSubring) : K) < 1 :=
      (Valuation.mem_maximalIdeal_iff (v := vK)).mp hfa
    rw [hfa_eval]
    change 0 < OrderDual.toDual
      (Additive.ofMul (vK ((f.eval a₀ : vK.valuationSubring) : K)))
    exact hlt
  have hderiv_val : v ((f.derivative.eval a₀ : vK.valuationSubring) : K) = 0 := by
    obtain ⟨u, hu⟩ := isUnit_iff_exists_inv.mp hunit
    have hmul : ((f.derivative.eval a₀ : vK.valuationSubring) : K) * (u : K) = 1 := by
      exact congrArg (fun z : vK.valuationSubring => (z : K)) hu
    have hnonneg : 0 ≤ v ((f.derivative.eval a₀ : vK.valuationSubring) : K) :=
      (hA _).mp (f.derivative.eval a₀).property
    have hunonneg : 0 ≤ v (u : K) := (hA _).mp u.property
    have hsum : v ((f.derivative.eval a₀ : vK.valuationSubring) : K) + v (u : K) = 0 := by
      rw [← v.map_mul, hmul, v.map_one]
    apply le_antisymm
    · calc
        v ((f.derivative.eval a₀ : vK.valuationSubring) : K) =
            v ((f.derivative.eval a₀ : vK.valuationSubring) : K) + 0 := by simp
        _ ≤ v ((f.derivative.eval a₀ : vK.valuationSubring) : K) + v (u : K) :=
          add_le_add (le_refl _) hunonneg
        _ = 0 := hsum
    · exact hnonneg
  have hineq : v (fK.eval (a₀ : K)) >
      v (fK.derivative.eval (a₀ : K)) + v (fK.derivative.eval (a₀ : K)) := by
    have hderivK_val : v (fK.derivative.eval (a₀ : K)) = 0 := by
      rw [hderiv_eval, hderiv_val]
    rw [hfa_eval, hderivK_val]
    have hfa_val' := hfa_val
    rw [hfa_eval] at hfa_val'
    simpa only [add_zero] using hfa_val'
  obtain ⟨a, ha, _⟩ := @hensel_newton_form K (Additive Γ)ᵒᵈ _ _ v hrank
    vK.valuationSubring.toSubring hA fK hfcoeff (a₀ : K) a₀.property hineq hcomplete'
  have hroot := ha.1
  have hstrict := ha.2.1
  have hderivK_val : v (fK.derivative.eval (a₀ : K)) = 0 := by
    rw [hderiv_eval, hderiv_val]
  have ha_val : v a ≥ 0 := by
    have hdiff : v (a - (a₀ : K)) ≥ 0 :=
      le_of_lt (by simpa [hderivK_val] using hstrict)
    have hsum := valuation_strong_triangle v (a - (a₀ : K)) (a₀ : K)
    have hmin : 0 ≤ min (v (a - (a₀ : K))) (v (a₀ : K)) :=
      le_min hdiff ((hA _).mp a₀.property)
    exact hmin.trans (by simpa [sub_add_cancel] using hsum)
  let a' : vK.valuationSubring := ⟨a, (hA _).mpr ha_val⟩
  refine ⟨a', ?_, ?_⟩
  · apply Subtype.ext
    change ((f.eval a' : vK.valuationSubring) : K) = 0
    have heval : fK.eval (a : K) =
        ((f.eval a' : vK.valuationSubring) : K) := by
      change (f.map (Subring.subtype vK.valuationSubring.toSubring)).eval
          ((Subring.subtype vK.valuationSubring.toSubring) a') =
        (Subring.subtype vK.valuationSubring.toSubring) (f.eval a')
      exact Polynomial.eval_map_apply
        (Subring.subtype vK.valuationSubring.toSubring) a'
    rw [← heval]
    exact hroot
  · rw [Valuation.mem_maximalIdeal_iff]
    have hdiff : v (a - (a₀ : K)) > 0 := by
      simpa [hderivK_val] using hstrict
    have hdiffK : vK (a - (a₀ : K)) < 1 := by
      change 0 < OrderDual.toDual (Additive.ofMul (vK (a - (a₀ : K)))) at hdiff
      exact hdiff
    simpa [a'] using hdiffK

end
end Chapter09
end LastLib.Book01ValuationsDVRsAndCompletions
