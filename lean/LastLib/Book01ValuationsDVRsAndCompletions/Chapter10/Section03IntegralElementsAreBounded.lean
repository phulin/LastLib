import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section02ExistenceByMaximalDomination
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Ideal.GoingUp

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter10

universe u10K u10L u10Γ

open scoped BigOperators TensorProduct WithZero PowerSeries
open Polynomial

noncomputable section

/-!
# Chapter 10: Extensions of valuations

This file is a statement-generation formalization of Sections 10.1--10.7 of
Book 1.  The declarations deliberately keep the valuation-theoretic data
explicit: this makes the extension, residue, and ramification assertions
usable independently of the other generated chapters.
-/

/-! # Book 1, Chapter 10, Section 10.3: Integral Elements Are Bounded
-/

/-! ## 10.2--10.3. Integral elements and boundedness -/

/-- An element integral over a valuation ring lies in every extending ring. -/
theorem chapter10_integral_elements_are_bounded
    {K L Γ₀ Δ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    [LinearOrderedCommGroupWithZero Δ₀]
    (v : Valuation K Γ₀) (w : Valuation L Δ₀)
    [h : Valuation.HasExtension v w]
    {x : L} (hx : IsIntegral v.valuationSubring x) :
    x ∈ w.valuationSubring := by
  change x ∈ w.valuationSubring.toSubring
  apply LocalSubring.mem_of_isMax_of_isIntegral
    (R := w.valuationSubring.toLocalSubring) w.valuationSubring.isMax_toLocalSubring
  exact (show IsIntegral w.valuationSubring x from hx.tower_top)

/-- One inclusion in the valuative description of the integral closure. -/
theorem chapter10_integral_closure_subset_bounded
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) (E : Set (Chapter10ValuationOnField L))
    (hE : ∀ W, W ∈ E ↔ v.IsEquiv (W.valuation.comap (algebraMap K L))) :
    Chapter10IntegralElements v.valuationSubring L ⊆
      Chapter10BoundedAtValuations E := by
  intro x hx W hW
  change IsIntegral v.valuationSubring x at hx
  have hExt := (hE W).mp hW
  let : Valuation.HasExtension v W.valuation := ⟨hExt⟩
  exact chapter10_integral_elements_are_bounded v W.valuation hx

/-- The field-theoretic valuative criterion for integrality.

The wrapper is instantiated with the canonical value group in the universe of
`L`.  Every valuation ring on `L` has an equivalent canonical valuation with
this universe-level choice, so this avoids omitting any bounded elements while
keeping the field-theoretic intersection criterion usable.
-/
theorem chapter10_integral_closure_valuative_criterion
    {K : Type u10K} {L : Type u10L} {Γ₀ : Type u10Γ}
    [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) :
    Chapter10IntegralElements v.valuationSubring L =
      {x : L | ∀ (W : Chapter10ValuationOnField.{u10L, u10L} L),
        v.IsEquiv (W.valuation.comap (algebraMap K L)) →
          x ∈ W.valuation.valuationSubring} := by
  set_option maxHeartbeats 1000000 in
    ext x
    change IsIntegral v.valuationSubring x ↔
      ∀ (W : Chapter10ValuationOnField.{u10L, u10L} L),
        v.IsEquiv (W.valuation.comap (algebraMap K L)) →
          x ∈ W.valuation.valuationSubring
    constructor
    · intro hx W hW
      let : Valuation.HasExtension v W.valuation := ⟨hW⟩
      exact chapter10_integral_elements_are_bounded v W.valuation hx
    · intro hx
      by_contra hxint
      have hx0 : x ≠ 0 := by
        intro hx0
        exact hxint (hx0 ▸ isIntegral_zero)
      let : Invertible x := invertibleOfNonzero hx0
      let f : v.valuationSubring →+* L :=
        (algebraMap K L).comp v.valuationSubring.subtype
      have hf : Function.Injective f := by
        intro a b hab
        apply Subtype.ext
        apply FaithfulSMul.algebraMap_injective K L
        exact hab
      let B₀ : Subring L := f.range
      let e : v.valuationSubring ≃+* B₀ :=
        RingEquiv.ofBijective f.rangeRestrict
          ⟨fun a b h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
      have he : (algebraMap B₀ L).comp e.toRingHom =
          algebraMap v.valuationSubring L := by
        ext a
        rfl
      have hI₀ : (IsLocalRing.maximalIdeal v.valuationSubring).map e.toRingHom ≠
          (⊤ : Ideal B₀) := by
        intro htop
        have hmax : (IsLocalRing.maximalIdeal v.valuationSubring).IsMaximal :=
          IsLocalRing.maximalIdeal.isMaximal v.valuationSubring
        exact hmax.ne_top ((Ideal.map_eq_top_of_bijective e.toRingHom e.bijective).mp htop)
      let I : Ideal B₀ := (IsLocalRing.maximalIdeal v.valuationSubring).map e.toRingHom
      let S : Subalgebra B₀ L := Algebra.adjoin B₀ ({x⁻¹} : Set L)
      let xinv : S := ⟨x⁻¹, Algebra.subset_adjoin rfl⟩
      have hI : I.map (algebraMap B₀ S) + Ideal.span {xinv} ≠ ⊤ := by
        intro htop
        have htop' : I.map (algebraMap B₀ S) ⊔ Ideal.span {xinv} = ⊤ := by
          rw [← Ideal.add_eq_sup]
          exact htop
        have hp_exists :=
          (set_option maxHeartbeats 1000000 in
            Algebra.exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top
              (x⁻¹) I hI₀ htop')
        obtain ⟨p, hp, hpx⟩ := hp_exists
        have hunit : IsUnit p.leadingCoeff := by
          apply of_not_not
          intro hlead
          have hlead' : ¬ IsUnit (e.symm p.leadingCoeff) := by
            intro hlead'
            exact hlead (by simpa using hlead'.map e.toRingHom)
          have hleadM : e.symm p.leadingCoeff ∈
              IsLocalRing.maximalIdeal v.valuationSubring := by
            rw [IsLocalRing.mem_maximalIdeal]
            exact hlead'
          have hleadI : p.leadingCoeff ∈ I := by
            change p.leadingCoeff ∈
              (IsLocalRing.maximalIdeal v.valuationSubring).map e.toRingHom
            rw [← e.apply_symm_apply p.leadingCoeff]
            exact (Ideal.apply_mem_of_equiv_iff).2 hleadM
          have hone : (1 : B₀) ∈ I := by
            simpa using sub_mem hleadI hp
          exact hI₀ (I.eq_top_iff_one.mpr hone)
        have hpoly : IsIntegral B₀ x := by
          refine ⟨.C hunit.unit⁻¹.1 * p, ?_, ?_⟩
          · simp [Polynomial.Monic]
          · have hroot :
                eval₂ (algebraMap B₀ L) x p = 0 := by
              simpa [aeval_def] using hpx
            rw [eval₂_mul, eval₂_C, hroot, mul_zero]
        exact hxint ((RingEquiv.isIntegral_iff e he x).mpr hpoly)
      obtain ⟨W, hW⟩ :=
        (set_option maxHeartbeats 1000000 in
          Ideal.image_subset_nonunits_valuationSubring (A := S.toSubring)
            (I.map (algebraMap B₀ S) + Ideal.span {xinv}) hI)
      have hxW : x ∉ W := by
        intro hxin
        exact ((W.inv_mem_nonunits_iff.mp <|
          hW.2 ⟨xinv, le_add_self (α := Ideal S) (Ideal.subset_span rfl), rfl⟩).resolve_left hx0) hxin
      let W' : Chapter10ValuationOnField.{u10L, u10L} L :=
        { valueGroup := W.ValueGroup
          valuation := W.valuation }
      have hW' : v.IsEquiv (W'.valuation.comap (algebraMap K L)) := by
        apply Valuation.isEquiv_of_val_le_one
        intro y
        rw [← Valuation.mem_valuationSubring_iff,
          ← Valuation.mem_valuationSubring_iff]
        change y ∈ v.valuationSubring ↔
          algebraMap K L y ∈ W'.valuation.valuationSubring
        rw [ValuationSubring.valuationSubring_valuation]
        constructor
        · intro hy
          apply hW.1
          have he_y := congrArg (fun g : v.valuationSubring →+* L =>
            g ⟨y, hy⟩) he
          have he_y' : algebraMap B₀ L (e ⟨y, hy⟩) = algebraMap K L y := by
            calc
              algebraMap B₀ L (e ⟨y, hy⟩) =
                  algebraMap v.valuationSubring L ⟨y, hy⟩ := by simpa using he_y
              _ = algebraMap K L y := by
                rw [IsScalarTower.algebraMap_apply v.valuationSubring K L]
                rfl
          have hS_y : algebraMap B₀ L (e ⟨y, hy⟩) ∈ S :=
            S.algebraMap_mem (e ⟨y, hy⟩)
          rw [he_y'] at hS_y
          exact hS_y
        · intro hy
          by_contra hyV
          have hyinv : y⁻¹ ∈ v.valuationSubring :=
            (v.valuationSubring.mem_or_inv_mem y).resolve_left hyV
          have hyinvM : (e ⟨y⁻¹, hyinv⟩ : B₀) ∈ I := by
            exact (Ideal.apply_mem_of_equiv_iff).2 (by
              rw [IsLocalRing.mem_maximalIdeal]
              intro hunit
              obtain ⟨a, ha⟩ := isUnit_iff_exists_inv.mp hunit
              have hay : (a : K) = y :=
                (eq_of_inv_mul_eq_one (congrArg Subtype.val ha)).symm
              exact hyV (hay ▸ a.property))
          have he_yinv := congrArg (fun g : v.valuationSubring →+* L =>
            g ⟨y⁻¹, hyinv⟩) he
          have he_yinv' : algebraMap B₀ L (e ⟨y⁻¹, hyinv⟩) =
              algebraMap K L y⁻¹ := by
            calc
              algebraMap B₀ L (e ⟨y⁻¹, hyinv⟩) =
                  algebraMap v.valuationSubring L ⟨y⁻¹, hyinv⟩ := by
                simpa using he_yinv
              _ = algebraMap K L y⁻¹ := by
                rw [IsScalarTower.algebraMap_apply v.valuationSubring K L]
                rfl
          have hmemS :
              (algebraMap B₀ S) (e ⟨y⁻¹, hyinv⟩) ∈
                I.map (algebraMap B₀ S) + Ideal.span {xinv} := by
            apply (le_self_add (α := Ideal S))
            exact Ideal.mem_map_of_mem (algebraMap B₀ S) hyinvM
          have hnon' : algebraMap K L y⁻¹ ∈ W.nonunits := by
            apply hW.2
            refine ⟨algebraMap B₀ S (e ⟨y⁻¹, hyinv⟩), hmemS, ?_⟩
            change algebraMap B₀ L (e ⟨y⁻¹, hyinv⟩) = algebraMap K L y⁻¹
            exact he_yinv'
          have hy0L : algebraMap K L y ≠ 0 := by
            simpa using (RingHom.injective (algebraMap K L)).ne (show y ≠ 0 by
              intro hy0
              exact hyV (hy0 ▸ v.valuationSubring.zero_mem))
          have hnon'' : (algebraMap K L y)⁻¹ ∈ W.nonunits := by
            rw [← map_inv₀]
            exact hnon'
          exact ((W.inv_mem_nonunits_iff.mp hnon'').resolve_left hy0L) hy
      apply hxW
      have hxW' := hx W' hW'
      rw [ValuationSubring.valuationSubring_valuation] at hxW'
      exact hxW'

/-- Equivalent set notation for the intersection of all extending valuation rings. -/
theorem chapter10_integral_closure_is_intersection
    {K : Type u10K} {L : Type u10L} {Γ₀ : Type u10Γ}
    [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) :
    (Chapter10IntegralClosure v.valuationSubring L).toSubring =
      ⨅ (W : Chapter10ValuationOnField.{u10L, u10L} L)
        (_ : v.IsEquiv (W.valuation.comap (algebraMap K L))),
        W.valuation.valuationSubring.toSubring := by
  ext x
  change IsIntegral v.valuationSubring x ↔
    x ∈ ⨅ (W : Chapter10ValuationOnField.{u10L, u10L} L)
      (_ : v.IsEquiv (W.valuation.comap (algebraMap K L))),
      W.valuation.valuationSubring.toSubring
  rw [Subring.mem_iInf]
  simpa [Chapter10IntegralElements] using
    (Set.ext_iff.mp (chapter10_integral_closure_valuative_criterion v) x)

/-- If the extension is unique, the integral closure itself is a valuation ring. -/
theorem chapter10_unique_extension_makes_integral_closure_valuation_ring
    {K : Type u10K} {L : Type u10L} {Γ₀ : Type u10Γ}
    [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    [Algebra.IsAlgebraic K L]
    (v : Valuation K Γ₀)
    (hunique : ∀ (W₁ W₂ : Chapter10ValuationOnField.{u10L, u10L} L),
      v.IsEquiv (W₁.valuation.comap (algebraMap K L)) →
      v.IsEquiv (W₂.valuation.comap (algebraMap K L)) →
      W₁.valuation.IsEquiv W₂.valuation) :
    Chapter10ValuationRingCriterion
      (Chapter10IntegralClosure v.valuationSubring L).toSubring := by
  obtain ⟨W₀, hW₀⟩ :=
    chapter10_algebraic_valuation_extension_exists (K := K) (L := L) (Γ₀ := Γ₀) v
  let W₀' : Chapter10ValuationOnField.{u10L, u10L} L :=
    { valueGroup := W₀.ValueGroup
      valuation := W₀.valuation }
  have hW₀' : v.IsEquiv (W₀'.valuation.comap (algebraMap K L)) := by
    apply Valuation.isEquiv_of_val_le_one
    intro x
    change x ∈ v.valuationSubring ↔ W₀.valuation (algebraMap K L x) ≤ 1
    constructor
    · intro hx
      exact (ValuationSubring.valuation_le_one_iff W₀ _).mpr ((hW₀ x).mpr hx)
    · intro hx
      exact (hW₀ x).mp ((ValuationSubring.valuation_le_one_iff W₀ _).mp hx)
  intro x hx
  rcases W₀.mem_or_inv_mem x with hxW₀ | hxW₀
  · left
    change x ∈ Chapter10IntegralElements v.valuationSubring L
    rw [chapter10_integral_closure_valuative_criterion v]
    intro W hW
    have hEq : W₀'.valuation.valuationSubring = W.valuation.valuationSubring :=
      (Valuation.isEquiv_iff_valuationSubring W₀'.valuation W.valuation).mp
        (hunique W₀' W hW₀' hW)
    have hxW₀' : x ∈ W₀'.valuation.valuationSubring := by
      rw [Valuation.mem_valuationSubring_iff]
      exact (ValuationSubring.valuation_le_one_iff W₀ x).mpr hxW₀
    rw [hEq] at hxW₀'
    exact hxW₀'
  · right
    change x⁻¹ ∈ Chapter10IntegralElements v.valuationSubring L
    rw [chapter10_integral_closure_valuative_criterion v]
    intro W hW
    have hEq : W₀'.valuation.valuationSubring = W.valuation.valuationSubring :=
      (Valuation.isEquiv_iff_valuationSubring W₀'.valuation W.valuation).mp
        (hunique W₀' W hW₀' hW)
    have hxW₀' : x⁻¹ ∈ W₀'.valuation.valuationSubring := by
      rw [Valuation.mem_valuationSubring_iff]
      exact (ValuationSubring.valuation_le_one_iff W₀ x⁻¹).mpr hxW₀
    rw [hEq] at hxW₀'
    exact hxW₀'

/-! ### Extension centers

These results belong here, after maximal domination and the valuative
criterion.  They used to be forward declarations in Chapter 9. -/

/-- Finite-dimensional integral closure gives the extension-center
correspondence between valuation classes and primes over the base center. -/
theorem chapter10_finite_extension_prime_valuation_correspondence
    {A B : Type*} {K : Type u10K} {L : Type u10L} {Γ : Type u10Γ}
    [CommRing A] [IsDomain A] [ValuationRing A]
    [IsIntegrallyClosed A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra A L] [IsScalarTower A K L]
    [CommRing B] [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    [LinearOrderedCommGroupWithZero Γ] (vK : Valuation K Γ)
    (hA : vK.Integers A) :
    Chapter10ExtensionPrimeCorrespondence (A := A) (B := B) (L := L) vK := by
  sorry

/-- Factorization-form henselianity makes the center over the base maximal
ideal unique in every finite integral extension. -/
theorem chapter10_henselian_valuation_ring_has_unique_prime_above
    {A B : Type*} {K : Type u10K} {L : Type u10L} {Γ : Type u10Γ}
    [CommRing A] [IsDomain A] [ValuationRing A] [IsIntegrallyClosed A]
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra A K] [IsFractionRing A K]
    [CommRing B] [Algebra A B] [Algebra B L]
    [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    [LinearOrderedCommGroupWithZero Γ] (vK : Valuation K Γ)
    (hA : vK.Integers A)
    (hH : Chapter10IsHenselianValuedField vK) :
    Chapter10HasUniquePrimeAbove (A := A) (B := B) := by
  sorry

/-- The correspondence transfers uniqueness between its two parameter
spaces. -/
theorem chapter10_unique_prime_iff_unique_valuation_extension
    {A B : Type*} {K : Type u10K} {L : Type u10L} {Γ : Type u10Γ}
    [CommRing A] [IsDomain A] [ValuationRing A]
    [IsIntegrallyClosed A]
    [Field K] [Field L]
    [CommRing B] [Algebra A B] [Algebra B L] [Algebra A L]
    [IsScalarTower A B L] [IsIntegralClosure B A L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [FiniteDimensional K L]
    [IsScalarTower A K L]
    [LinearOrderedCommGroupWithZero Γ] (vK : Valuation K Γ)
    (hcor : Chapter10ExtensionPrimeCorrespondence
      (A := A) (B := B) (L := L) vK) :
    (Chapter10HasUniquePrimeAbove (A := A) (B := B) ↔
      Chapter10HasUniqueValuationExtension (L := L) vK) := by
  obtain ⟨e⟩ := hcor
  constructor
  · rintro ⟨P, hP, hPuniq⟩
    let y₀ : {P : Ideal B // Chapter10PrimeAboveMaximal (A := A) (B := B) P} :=
      ⟨P, hP⟩
    obtain ⟨W₀, hW₀⟩ := Quotient.exists_rep (e.symm y₀)
    refine ⟨⟨W₀⟩, ?_⟩
    intro W₁ W₂
    have hq :
        Quotient.mk (Chapter10ValuationExtensionSetoid (L := L) vK) W₁ =
          Quotient.mk (Chapter10ValuationExtensionSetoid (L := L) vK) W₂ := by
      apply e.injective
      apply Subtype.ext
      exact
        (hPuniq _ (e (Quotient.mk (Chapter10ValuationExtensionSetoid (L := L) vK) W₁)).property).trans
          (hPuniq _ (e (Quotient.mk (Chapter10ValuationExtensionSetoid (L := L) vK) W₂)).property).symm
    exact Quotient.exact hq
  · rintro ⟨⟨W₀⟩, hWuniq⟩
    let y₀ := e (Quotient.mk (Chapter10ValuationExtensionSetoid (L := L) vK) W₀)
    refine ⟨y₀.1, y₀.2, ?_⟩
    intro P hP
    let y : {P : Ideal B // Chapter10PrimeAboveMaximal (A := A) (B := B) P} :=
      ⟨P, hP⟩
    obtain ⟨q, hq⟩ := e.surjective y
    obtain ⟨W, hW⟩ := Quotient.exists_rep q
    have qeq : q = Quotient.mk (Chapter10ValuationExtensionSetoid (L := L) vK) W₀ :=
      hW.symm.trans (Quotient.sound (hWuniq W W₀))
    exact congrArg Subtype.val (hq.symm.trans (congrArg e qeq))

/-- A henselian valued field has a unique center and hence a unique valuation
branch in every finite extension. -/
theorem chapter10_henselian_valued_field_has_unique_prime_and_extension
    {A B : Type*} {K : Type u10K} {L : Type u10L} {Γ : Type u10Γ}
    [CommRing A] [IsDomain A] [ValuationRing A]
    [IsIntegrallyClosed A]
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra A K] [IsFractionRing A K]
    [CommRing B] [Algebra A B] [Algebra B L]
    [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    [LinearOrderedCommGroupWithZero Γ] (vK : Valuation K Γ)
    (hA : vK.Integers A)
    (hH : Chapter10IsHenselianValuedField vK) :
    Chapter10HasUniquePrimeAbove (A := A) (B := B) ∧
      Chapter10HasUniqueValuationExtension (L := L) vK := by
  have hcor := chapter10_finite_extension_prime_valuation_correspondence
    (A := A) (B := B) (K := K) (L := L) vK hA
  have hprime := chapter10_henselian_valuation_ring_has_unique_prime_above
    (A := A) (B := B) (K := K) (L := L) vK hA hH
  exact ⟨hprime,
    (chapter10_unique_prime_iff_unique_valuation_extension vK hcor).mp hprime⟩

/-- A finite integral extension has finitely many nonempty centers above the
base maximal ideal. -/
theorem chapter10_finite_extension_primes_above_are_finite
    {A B : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]
    [Algebra.IsIntegral A B] [FaithfulSMul A B] :
    Set.Finite {P : Ideal B |
      Chapter10PrimeAboveMaximal (A := A) (B := B) P} ∧
      Nonempty {P : Ideal B //
        Chapter10PrimeAboveMaximal (A := A) (B := B) P} := by
  let m : Ideal A := IsLocalRing.maximalIdeal A
  have heq : {P : Ideal B | Chapter10PrimeAboveMaximal (A := A) (B := B) P} =
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
      Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := B) m
    exact ⟨⟨P, hPmax.isPrime, hPover.over.symm⟩⟩

/-- Algebraic uniqueness is proved here from finite-subextension centers. -/
theorem chapter10_henselian_valuation_has_unique_branch
    {K : Type u10K} {L : Type u10L} {Γ₀ : Type u10Γ}
    {Γ₁ Γ₂ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    [LinearOrderedCommGroupWithZero Γ₁]
    [LinearOrderedCommGroupWithZero Γ₂] [Algebra.IsAlgebraic K L]
    (v : Valuation K Γ₀) (hH : Chapter10IsHenselianValuedField v)
    (w₁ : Valuation L Γ₁) (w₂ : Valuation L Γ₂)
    (h₁ : v.IsEquiv (w₁.comap (algebraMap K L)))
    (h₂ : v.IsEquiv (w₂.comap (algebraMap K L))) :
    w₁.IsEquiv w₂ := by
  sorry

/-- All coefficients of the characteristic polynomial, trace, and norm are integral. -/
def Chapter10CharacteristicPolynomialIntegral
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Module.Finite K L]
    (x : L) (R : Subring K) : Prop :=
  (∀ i, (LinearMap.charpoly (Algebra.lmul K L x)).coeff i ∈ R) ∧
    Algebra.trace K L x ∈ R ∧ Algebra.norm K x ∈ R

/-- Integral elements pass the finite discretely valued norm test. -/
theorem chapter10_integral_element_characteristic_data
    {K L A : Type*} [Field K] [Field L] [CommRing A]
    [Algebra K L] [Algebra A L] [Algebra A K]
    [IsScalarTower A K L]
    [FiniteDimensional K L]
    (R : Subring K)
    {x : L} (hx : IsIntegral A x)
    (hAtoR : ∀ z : K, IsIntegral A z → z ∈ R) :
    Chapter10CharacteristicPolynomialIntegral x R := by
  classical
  let f : Module.End K L := Algebra.lmul K L x
  let Ω := AlgebraicClosure K
  let p : A[X] := minpoly A x
  let pK : K[X] := p.map (algebraMap A K)
  let pΩ : Ω[X] := pK.map (algebraMap K Ω)
  have hpK : Polynomial.aeval x pK = 0 := by
    dsimp [pK]
    rw [Polynomial.aeval_map_algebraMap]
    change Polynomial.aeval x (minpoly A x) = 0
    exact minpoly.aeval A x
  have hpf : Polynomial.aeval f pK = 0 := by
    rw [Polynomial.aeval_algHom_apply (Algebra.lmul K L) x]
    simp [hpK]
  let F : Module.End Ω (Ω ⊗[K] L) := f.baseChange Ω
  have hpfΩ : Polynomial.aeval F pΩ = 0 := by
    have hcompat :
        (algebraMap Ω (Module.End Ω (Ω ⊗[K] L))).comp (algebraMap K Ω) =
          (Module.End.baseChangeHom K Ω L).toRingHom.comp
            (algebraMap K (Module.End K L)) := by
      ext z
      simp [Module.End.baseChangeHom]
    have hmap := Polynomial.map_aeval_eq_aeval_map hcompat pK f
    have hbase :
        (Module.End.baseChangeHom K Ω L).toRingHom f = f.baseChange Ω := rfl
    change Polynomial.aeval (f.baseChange Ω) (pK.map (algebraMap K Ω)) = 0
    rw [← hbase, ← hmap, hpf]
    simp
  have hcoeff : ∀ i, IsIntegral A ((LinearMap.charpoly f).coeff i) := by
    intro i
    let q : Ω[X] := (LinearMap.charpoly f).map (algebraMap K Ω)
    have hqmonic : q.Monic := by
      exact (LinearMap.charpoly_monic f).map _
    have hqsplits : q.Splits := IsAlgClosed.splits q
    have hqroot : ∀ y : Ω, q.IsRoot y → IsIntegral A y := by
      intro y hy
      have hyF : F.charpoly.IsRoot y := by
        change (f.baseChange Ω).charpoly.IsRoot y
        rw [LinearMap.charpoly_baseChange]
        exact hy
      have hyeig : F.HasEigenvalue y :=
        (Module.End.hasEigenvalue_iff_isRoot_charpoly F y).mpr hyF
      obtain ⟨v, hv⟩ := hyeig.exists_hasEigenvector
      have hpy : pΩ.eval y = 0 := by
        have hzero : pΩ.eval y • v = 0 := by
          rw [← Module.End.aeval_apply_of_hasEigenvector hv]
          rw [hpfΩ]
          simp
        exact (smul_eq_zero.mp hzero).resolve_right hv.2
      refine ⟨p, minpoly.monic hx, ?_⟩
      simpa [pΩ, pK, Polynomial.aeval_def, Polynomial.eval₂_map,
        IsScalarTower.algebraMap_eq A K Ω] using hpy
    have hiΩ : IsIntegral A (q.coeff i) :=
      Polynomial.isIntegral_coeff_of_factors q
        (by rw [hqmonic.leadingCoeff]; exact isIntegral_one) hqsplits hqroot i
    apply (isIntegral_algebraMap_iff (algebraMap K Ω).injective).mp
    simpa [q] using hiΩ
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact hAtoR _ (hcoeff i)
  · exact hAtoR _ (Algebra.isIntegral_trace (R := A) (L := K) (F := L) hx)
  · exact hAtoR _ (Algebra.isIntegral_norm (R := A) K hx)

/-- A cancellation example witnessing that the norm alone is not a converse. -/
structure Chapter10NormCancellationExample
    (A K L : Type*) [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] where
  x : L
  norm_mem : ∃ a : A, Algebra.norm K x = algebraMap A K a
  not_integral : ¬ IsIntegral A x

/-- A concrete finite-field-extension witness that the norm condition is not a
converse to integrality.  The witness is intentionally packaged separately
from the generic counterexample schema above, so the negative statement below
does not merely assume that a witness has been supplied by a caller. -/
theorem chapter10_concrete_norm_cancellation_example :
    Nonempty (Chapter10NormCancellationExample ℤ ℝ ℂ) := by
  sorry

theorem chapter10_norm_alone_is_not_a_converse
    {A K L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L]
    (exampleData : Chapter10NormCancellationExample A K L) :
    ¬ (∀ x : L, (∃ a : A, Algebra.norm K x = algebraMap A K a) →
      IsIntegral A x) := by
  intro h
  exact exampleData.not_integral (h exampleData.x exampleData.norm_mem)

/-- The norm-only integrality test fails already for `ℤ ⊂ ℝ ⊂ ℂ`. -/
theorem chapter10_norm_alone_is_not_a_converse_concrete :
    ¬ (∀ x : ℂ, (∃ a : ℤ, Algebra.norm ℝ x = algebraMap ℤ ℝ a) →
      IsIntegral ℤ x) := by
  exact chapter10_norm_alone_is_not_a_converse
    (exampleData := Classical.choice chapter10_concrete_norm_cancellation_example)

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter10
