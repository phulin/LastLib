import LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.Section03LiftingFactorizations

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

/-! # Book 1, Chapter 9, Section 9.4: Henselian Local Rings
-/

/-! ## 9.4 Henselian local rings -/

/-- Chapter-specific name for Mathlib's henselian local-ring class. -/
def IsHenselianLocalRingChapter09 (A : Type*) [CommRing A] : Prop :=
  HenselianLocalRing A

/-- The simple-residue-root lifting property. -/
def SimpleResidueRootLiftingProperty (A : Type*) [CommRing A] [IsLocalRing A] : Prop :=
  ∀ (f : A[X]) (a₀ : ResidueRing A), f.Monic →
    (residuePolynomial f).eval a₀ = 0 →
    IsUnit ((residuePolynomial f).derivative.eval a₀) →
    ∃! a : A, f.eval a = 0 ∧ residueClass a = a₀

/-- The coprime-factorization lifting property. -/
def HenselianFactorizationProperty (A : Type*) [CommRing A] [IsLocalRing A] : Prop :=
  ∀ (f : A[X]) (g₀ h₀ : Polynomial (ResidueRing A)), f.Monic →
    g₀.Monic → h₀.Monic → IsCoprime g₀ h₀ → residuePolynomial f = g₀ * h₀ →
    ∃! gh : A[X] × A[X], IsFactorizationLift f g₀ h₀ gh.1 gh.2

/-- A residue root is the linear factor `X-ā`. -/
theorem simple_residue_root_iff_linear_factor {A : Type*} [CommRing A] [IsLocalRing A]
    (f : A[X]) (a₀ : ResidueRing A) :
    (residuePolynomial f).eval a₀ = 0 ↔
      ∃ q : Polynomial (ResidueRing A),
        residuePolynomial f = (X - C a₀) * q := by
  constructor
  · intro hroot
    have hdvd : X - C a₀ ∣ residuePolynomial f := by
      rw [Polynomial.dvd_iff_isRoot]
      simpa [Polynomial.IsRoot] using hroot
    rcases hdvd with ⟨q, hq⟩
    exact ⟨q, hq⟩
  · rintro ⟨q, hq⟩
    have hdvd : X - C a₀ ∣ residuePolynomial f := ⟨q, hq⟩
    have hroot := (Polynomial.dvd_iff_isRoot.mp hdvd)
    simpa [Polynomial.IsRoot] using hroot

/-- Simple-residue-root lifting implies coprime factorization lifting. -/
theorem henselian_factorization_by_successive_linear_lifts
    {A : Type*} [CommRing A] [IsLocalRing A]
    (hroot : SimpleResidueRootLiftingProperty A) :
    HenselianFactorizationProperty A := by
  sorry

/-- Conversely, a factorization lift applied to `X-ā` gives simple-root lifting. -/
theorem simple_root_lifting_by_linear_factorization
    {A : Type*} [CommRing A] [IsLocalRing A]
    (hfactor : HenselianFactorizationProperty A) :
    SimpleResidueRootLiftingProperty A := by
  intro f a₀ hf hroot hsimple
  let g₀ : Polynomial (ResidueRing A) := X - C a₀
  let h₀ : Polynomial (ResidueRing A) := residuePolynomial f /ₘ g₀
  have hg₀ : g₀.Monic := by
    simpa [g₀] using monic_X_sub_C a₀
  have hred : residuePolynomial f = g₀ * h₀ := by
    simpa [g₀, h₀, modByMonic_X_sub_C_eq_C_eval, hroot] using
      (X_sub_C_mul_divByMonic_eq_sub_modByMonic (residuePolynomial f) a₀).symm
  have hcop : IsCoprime g₀ h₀ := by
    change IsCoprime (X - C a₀) (residuePolynomial f /ₘ (X - C a₀))
    have hsimple_ne : (residuePolynomial f).derivative.eval a₀ ≠ 0 :=
      hsimple.ne_zero
    exact isCoprime_of_is_root_of_eval_derivative_ne_zero
      (K := IsLocalRing.ResidueField A) (residuePolynomial f) a₀ hsimple_ne
  have hprodmonic : (g₀ * h₀).Monic := by
    rw [← hred]
    exact hf.map (residueMap A)
  have hh₀ : h₀.Monic := hg₀.of_mul_monic_left hprodmonic
  obtain ⟨gh, hgh, _⟩ := hfactor f g₀ h₀ hf hg₀ hh₀ hcop hred
  rcases hgh with ⟨hg, hh, hng, hnh, hrg, hrh, hfac⟩
  have hng' : gh.1.natDegree = 1 := by
    simpa [g₀] using hng
  let a : A := -gh.1.coeff 0
  have hpoly : gh.1 = X - C a := by
    rw [hg.eq_X_add_C hng']
    simp [a, sub_neg_eq_add]
  have hfa : f.eval a = 0 := by
    rw [hfac, eval_mul, hpoly]
    simp
  have hresa : residueClass a = a₀ := by
    have hcoeff := congrArg (fun P : Polynomial (ResidueRing A) => P.coeff 0) hrg
    simp [residuePolynomial, g₀] at hcoeff
    change residueMap A (-gh.1.coeff 0) = a₀
    rw [map_neg, hcoeff]
    simp
  obtain ⟨a₀', ha₀'⟩ := Ideal.Quotient.mk_surjective a₀
  have hunit : IsUnit (f.derivative.eval a₀') := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    change residueMap A (f.derivative.eval a₀') ≠ 0
    have hsimple' : (residuePolynomial f).derivative.eval a₀ ≠ 0 :=
      hsimple.ne_zero
    rw [← ha₀'] at hsimple'
    change ((f.map (residueMap A)).derivative).eval (residueMap A a₀') ≠ 0 at hsimple'
    rw [Polynomial.derivative_map, Polynomial.eval_map_apply] at hsimple'
    exact hsimple'
  have hca : CongruentModIdeal (IsLocalRing.maximalIdeal A) a a₀' := by
    unfold CongruentModIdeal
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change residueMap A (a - a₀') = 0
    have hres : residueMap A a = residueMap A a₀' := by
      calc
        residueMap A a = a₀ := by simpa [residueClass, residueMap] using hresa
        _ = residueMap A a₀' := ha₀'.symm
    rw [map_sub, hres]
    simp
  refine ⟨a, ⟨hfa, hresa⟩, ?_⟩
  intro b hb
  have hcb : CongruentModIdeal (IsLocalRing.maximalIdeal A) b a₀' := by
    unfold CongruentModIdeal
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change residueMap A (b - a₀') = 0
    have hres : residueMap A b = residueMap A a₀' := by
      calc
        residueMap A b = a₀ := by simpa [residueClass, residueMap] using hb.2
        _ = residueMap A a₀' := ha₀'.symm
    rw [map_sub, hres]
    simp
  have hunit_a : IsUnit (f.derivative.eval a) :=
    derivative_unit_on_residue_class f hca hunit
  have habmem : a - b ∈ IsLocalRing.maximalIdeal A := by
    unfold CongruentModIdeal at hca hcb
    have h := (IsLocalRing.maximalIdeal A).sub_mem hca hcb
    simpa [sub_eq_add_neg, add_assoc] using h
  have habunit : ¬ IsUnit (a - b) := by
    intro hab
    exact (notMem_maximalIdeal.mpr hab) habmem
  exact (IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub
    (f := f) (a := a) (b := b) hfa hb.1 habunit hunit_a).symm

/-- Mathlib's henselian local-ring property is equivalent to simple-root lifting. -/
theorem henselian_iff_simple_residue_root_lifting {A : Type*} [CommRing A]
    [IsLocalRing A] :
    IsHenselianLocalRingChapter09 A ↔ SimpleResidueRootLiftingProperty A := by
  constructor
  · intro hH
    change HenselianLocalRing A at hH
    intro f a₀ hf hroot hsimple
    obtain ⟨a₀', ha₀'⟩ := Ideal.Quotient.mk_surjective a₀
    have hfa : f.eval a₀' ∈ IsLocalRing.maximalIdeal A := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      change residueMap A (f.eval a₀') = 0
      have hroot' := hroot
      rw [← ha₀'] at hroot'
      change (f.map (residueMap A)).eval (residueMap A a₀') = 0 at hroot'
      rw [Polynomial.eval_map_apply] at hroot'
      exact hroot'
    have hunit : IsUnit (f.derivative.eval a₀') := by
      apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
      change residueMap A (f.derivative.eval a₀') ≠ 0
      have hsimple' : (residuePolynomial f).derivative.eval a₀ ≠ 0 :=
        hsimple.ne_zero
      rw [← ha₀'] at hsimple'
      change ((f.map (residueMap A)).derivative).eval (residueMap A a₀') ≠ 0 at hsimple'
      rw [Polynomial.derivative_map, Polynomial.eval_map_apply] at hsimple'
      exact hsimple'
    obtain ⟨a, ha, hres⟩ := hH.is_henselian f hf a₀' hfa hunit
    have hares : residueClass a = a₀ := by
      unfold residueClass residueMap
      rw [← ha₀']
      rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact hres
    refine ⟨a, ⟨ha, hares⟩, ?_⟩
    intro b hb
    have hbc : CongruentModIdeal (IsLocalRing.maximalIdeal A) b a₀' := by
      unfold CongruentModIdeal
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      change residueMap A (b - a₀') = 0
      have hresb : residueMap A b = residueMap A a₀' := by
        calc
          residueMap A b = a₀ := by simpa [residueClass, residueMap] using hb.2
          _ = residueMap A a₀' := ha₀'.symm
      rw [map_sub, hresb]
      simp
    have hca : CongruentModIdeal (IsLocalRing.maximalIdeal A) a a₀' := hres
    have hunit_a : IsUnit (f.derivative.eval a) :=
      derivative_unit_on_residue_class f hca hunit
    have habmem : a - b ∈ IsLocalRing.maximalIdeal A := by
      unfold CongruentModIdeal at hca hbc
      have h := (IsLocalRing.maximalIdeal A).sub_mem hca hbc
      simpa [sub_eq_add_neg, add_assoc] using h
    have habunit : ¬ IsUnit (a - b) := by
      intro hab
      exact (notMem_maximalIdeal.mpr hab) habmem
    exact (IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub
      (f := f) (a := a) (b := b) ha hb.1 habunit hunit_a).symm
  · intro hroot
    change HenselianLocalRing A
    refine { toIsLocalRing := inferInstance, is_henselian := ?_ }
    intro f hf a₀ hfa hunit
    have hroot' : (residuePolynomial f).eval (residueClass a₀) = 0 := by
      change (f.map (residueMap A)).eval (residueMap A a₀) = 0
      rw [Polynomial.eval_map_apply]
      change (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) (f.eval a₀) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hfa
    have hsimple : IsUnit ((residuePolynomial f).derivative.eval (residueClass a₀)) := by
      simpa only [residueClass, residuePolynomial, Polynomial.derivative_map,
        Polynomial.eval_map_apply] using hunit.map (residueMap A)
    obtain ⟨a, ha, _⟩ := hroot f (residueClass a₀) hf hroot' hsimple
    refine ⟨a, ha.1, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change residueMap A (a - a₀) = 0
    have hres : residueMap A a = residueMap A a₀ := by
      simpa only [residueClass] using ha.2
    rw [map_sub, hres]
    simp

/-- Factorization-form and simple-root henselianity agree for local rings. -/
theorem henselian_iff_factorization_lifting {A : Type*} [CommRing A]
    [IsLocalRing A] :
    IsHenselianLocalRingChapter09 A ↔ HenselianFactorizationProperty A := by
  constructor
  · intro hH
    exact henselian_factorization_by_successive_linear_lifts
      ((henselian_iff_simple_residue_root_lifting (A := A)).mp hH)
  · intro hfactor
    exact (henselian_iff_simple_residue_root_lifting (A := A)).mpr
      (simple_root_lifting_by_linear_factorization hfactor)

/-- Complete and separated maximal-ideal-adic local rings. -/
def IsMaximalIdealAdicallyCompleteSeparated (A : Type*) [CommRing A] [IsLocalRing A] : Prop :=
  IsAdicComplete (IsLocalRing.maximalIdeal A) A

/-- Completeness and separatedness imply henselianity. -/
theorem complete_separated_local_ring_is_henselian {A : Type*} [CommRing A]
    [IsLocalRing A] (hA : IsMaximalIdealAdicallyCompleteSeparated A) :
    IsHenselianLocalRingChapter09 A := by
  unfold IsMaximalIdealAdicallyCompleteSeparated at hA
  have hring : HenselianRing A (IsLocalRing.maximalIdeal A) :=
    @IsAdicComplete.henselianRing A _ (IsLocalRing.maximalIdeal A) hA
  let hH : HenselianLocalRing A :=
    { is_henselian := by
        intro f hf a₀ hfa hunit
        have hmap : IsUnit
            (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)
              (f.derivative.eval a₀)) :=
          IsUnit.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) hunit
        obtain ⟨a, ha, hres⟩ := hring.is_henselian f hf a₀ hfa hmap
        exact ⟨a, ha, hres⟩ }
  exact hH

/-- Complete DVRs are henselian. -/
theorem complete_DVR_is_henselian {A : Type*} [CommRing A] [IsDomain A]
    [CompleteDVR A] : IsHenselianLocalRingChapter09 A := by
  apply complete_separated_local_ring_is_henselian
  unfold IsMaximalIdealAdicallyCompleteSeparated
  infer_instance

/-- The algebraic property of being henselian without the topological completeness property. -/
def IsHenselianButNotComplete (A : Type*) [CommRing A] [IsLocalRing A] : Prop :=
  HenselianLocalRing A ∧ ¬ IsMaximalIdealAdicallyCompleteSeparated A

/-- A henselian DVR need not be complete; this records an actual example interface. -/
structure Chapter09HenselianNoncompleteDVRExample where
  A : Type*
  [commRing : CommRing A]
  [domain : IsDomain A]
  [dvr : IsDiscreteValuationRing A]
  henselian : IsHenselianLocalRingChapter09 A
  not_adically_complete : ¬ IsMaximalIdealAdicallyCompleteSeparated A

theorem henselian_DVR_need_not_be_complete
    : Nonempty Chapter09HenselianNoncompleteDVRExample.{u} := by
  sorry
/-- A minimal local interface for the henselization of a local ring. -/
def IsHenselizationOf {A H : Type*} [CommRing A] [IsLocalRing A]
    [CommRing H] [IsLocalRing H] [Algebra A H] : Prop :=
  HenselianLocalRing H ∧ IsLocalHom (algebraMap A H) ∧
    Function.Injective (algebraMap A H) ∧
    (∀ x : H, IsIntegral A x) ∧
    ∀ (B : Type*) [CommRing B] [IsLocalRing B] [Algebra A B]
      [HenselianLocalRing B],
      ∃! φ : H →+* B, IsLocalHom φ ∧ φ.comp (algebraMap A H) = algebraMap A B
/-- The universal-property part of henselization: maps to henselian local rings are unique. -/
def HasHenselizationUniversalProperty {A H : Type*} [CommRing A] [IsLocalRing A]
    [CommRing H] [IsLocalRing H] [Algebra A H] : Prop :=
  ∀ (B : Type*) [CommRing B] [IsLocalRing B] [Algebra A B]
    [HenselianLocalRing B],
    ∃! φ : H →+* B, IsLocalHom φ ∧ φ.comp (algebraMap A H) = algebraMap A B

/-- An adic completion interface, kept abstract so the chapter remains self-contained. -/
def IsAdicCompletionOf {A C : Type*} [CommRing A] [IsLocalRing A]
    [CommRing C] [Algebra A C] : Prop :=
  IsAdicComplete (IsLocalRing.maximalIdeal A) C ∧
    Function.Injective (algebraMap A C)
    ∧ ∀ (B : Type*) [CommRing B] [IsLocalRing B] [Algebra A B]
      [IsAdicComplete
        ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) B],
      ∃! φ : C →+* B, IsLocalHom φ ∧ φ.comp (algebraMap A C) = algebraMap A B

/-- A strict embedding records that an algebraic henselization can be smaller than its completion. -/
def IsStrictRingEmbedding {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    (φ : R →+* S) : Prop :=
  Function.Injective φ ∧ ¬ Function.Surjective φ

/-- Henselization elements are algebraic over the original local ring. -/
theorem henselization_adds_algebraic_solutions {A H : Type*} [CommRing A] [IsLocalRing A]
    [CommRing H] [IsLocalRing H] [Algebra A H]
    (hH : IsHenselizationOf (A := A) (H := H)) :
    HenselianLocalRing H ∧ ∀ x : H, IsIntegral A x := by
  rcases hH with ⟨hHens, hlocal, hinj, hint, hUniversal⟩
  exact ⟨hHens, hint⟩

end
end Chapter09
end LastLib.Book01ValuationsDVRsAndCompletions
