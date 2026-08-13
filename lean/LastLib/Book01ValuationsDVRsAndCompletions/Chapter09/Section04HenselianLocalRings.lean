import LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.Section03LiftingFactorizations
import Mathlib.RingTheory.Algebraic.Defs

namespace LastLib.Book01ValuationsDVRsAndCompletions
namespace Chapter09

universe u uK uL uΓ uA uH uC uI

open scoped BigOperators Polynomial WithZeroTopology
open Ideal IsLocalRing Polynomial

noncomputable section

local instance chapter09Section04FactPrime7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
local instance chapter09Section04FactPrime2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩

/-! # Chapter 9: Hensel lifting

This file is a statement-generation pass for Chapter 9 of Book 1.  The
declarations deliberately keep the hypotheses visible: in particular, a
complete DVR means adic completeness, while the valuation form is stated for
an arbitrary additive valuation.
-/

/-! # Book 1, Chapter 9, Section 9.4: Henselian Local Rings
-/

/-! ## 9.4 Henselian local rings -/

/-- The simple-residue-root lifting property. -/
def SimpleResidueRootLiftingProperty (A : Type*) [CommRing A] [IsLocalRing A] : Prop :=
  ∀ (f : A[X]) (a₀ : ResidueRing A), f.Monic →
    (residuePolynomial f).eval a₀ = 0 →
    IsUnit ((residuePolynomial f).derivative.eval a₀) →
    ∃! a : A, f.eval a = 0 ∧ residueClass a = a₀

/-- The coprime-factorization lifting property used as the book's primary
definition of henselianity. -/
def HenselianFactorizationProperty (A : Type*) [CommRing A] [IsLocalRing A] : Prop :=
  ∀ (f : A[X]) (g₀ h₀ : Polynomial (ResidueRing A)), f.Monic →
    g₀.Monic → h₀.Monic → IsCoprime g₀ h₀ → residuePolynomial f = g₀ * h₀ →
    ∃! gh : A[X] × A[X], IsFactorizationLift f g₀ h₀ gh.1 gh.2

/-- The chapter's book-facing henselian predicate. -/
abbrev IsHenselianLocalRingChapter09 (A : Type*) [CommRing A] [IsLocalRing A] : Prop :=
  HenselianFactorizationProperty A

/-- Complete and separated maximal-ideal-adic local rings. -/
def IsMaximalIdealAdicallyCompleteSeparated (A : Type*) [CommRing A] [IsLocalRing A] : Prop :=
  IsAdicComplete (IsLocalRing.maximalIdeal A) A

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

/-- A factorization lift applied to `X-ā` gives simple-root lifting. -/
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

/-- Mathlib's henselian local-ring class is equivalent to simple-root lifting. -/
theorem mathlib_henselian_iff_simple_residue_root_lifting {A : Type*} [CommRing A]
    [IsLocalRing A] :
    HenselianLocalRing A ↔ SimpleResidueRootLiftingProperty A := by
  constructor
  · intro hH
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

/-- Book-henselian rings satisfy Mathlib's simple-root interface.

The converse is intentionally absent: it is the missing generic factorization
theorem that previously made Chapter 9 depend on an unproved Mathlib TODO. -/
theorem factorization_henselian_implies_mathlib_henselian
    {A : Type*} [CommRing A] [IsLocalRing A]
    (hfactor : IsHenselianLocalRingChapter09 A) :
    HenselianLocalRing A :=
  (mathlib_henselian_iff_simple_residue_root_lifting (A := A)).mpr
    (simple_root_lifting_by_linear_factorization hfactor)

/-- The chapter-specific henselian predicate is definitionally the
factorization-lifting property. -/
theorem henselian_iff_factorization_lifting {A : Type*} [CommRing A]
    [IsLocalRing A] :
    IsHenselianLocalRingChapter09 A ↔ HenselianFactorizationProperty A := by
  rfl

/-- Adic completeness supplies Mathlib's simple-root henselian class. -/
theorem complete_separated_local_ring_has_simple_root_henselianity
    {A : Type*} [CommRing A]
    [IsLocalRing A] (hA : IsMaximalIdealAdicallyCompleteSeparated A) :
    HenselianLocalRing A := by
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

/-- Complete separated local rings satisfy the book's factorization form of
Hensel's lemma.  Its eventual proof should run the coefficientwise correction
argument in the adic topology; it must not be obtained from an assumed generic
simple-root-to-factorization bridge. -/
theorem complete_separated_local_ring_is_henselian
    {A : Type*} [CommRing A] [IsLocalRing A]
    (hA : IsMaximalIdealAdicallyCompleteSeparated A) :
    IsHenselianLocalRingChapter09 A := by
  sorry

/-- Complete DVRs satisfy the book's factorization-form definition directly
by the successive-precision theorem of Section 9.3. -/
theorem complete_DVR_is_henselian {A : Type*} [CommRing A] [IsDomain A]
    [CompleteDVR A] : IsHenselianLocalRingChapter09 A := by
  intro f g₀ h₀ hf hg₀ hh₀ hcop hred
  exact hensel_factorization f g₀ h₀ hf hg₀ hh₀ hcop hred

end
end Chapter09
end LastLib.Book01ValuationsDVRsAndCompletions
