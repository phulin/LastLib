import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section01SeparatingBranchesByCompletion
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section03IntegralElementsAreBounded
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.Section01FromOneLocalRingToSeveral
import Mathlib.Algebra.Module.PID

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter12

noncomputable section

open Function Ideal IsLocalRing Polynomial
open Filter Topology
open scoped BigOperators TensorProduct WithZero Polynomial

universe u

/-! # Chapter 12: Completion and finite extensions

This file is a statement-generation pass for §§12.1--12.8 of Book 1.  The
declarations deliberately record the interfaces and relationships used in the
chapter; proofs are postponed.
-/

/-! # Book 1, Chapter 12, Section 12.2: The Completed Product Theorem
-/

/-- A ring-theoretic formulation of “the completed product is an algebra product”. -/
def hasCompletedRingProduct (A B Ahat : Type*) [CommRing A] [CommRing B]
    [CommRing Ahat] [Algebra A B] [Algebra A Ahat] {ι : Type*}
    (C : ι → Type*) [∀ i, CommRing (C i)] : Prop :=
  Nonempty (B ⊗[A] Ahat ≃+* (∀ i, C i))

/-- The same product assertion, remembering the `Ahat`-algebra structures. -/
def hasCompletedAlgebraProduct (A B Ahat : Type*) [CommRing A] [CommRing B]
    [CommRing Ahat] [Algebra A B] [Algebra A Ahat]
    {ι : Type*}
    (C : ι → Type*) [∀ i, CommRing (C i)] [∀ i, Algebra Ahat (C i)] : Prop :=
  letI : Algebra Ahat (B ⊗[A] Ahat) := Algebra.TensorProduct.rightAlgebra
  Nonempty (B ⊗[A] Ahat ≃ₐ[Ahat] (∀ i, C i))

/-! Ramification labels used in the completed degree formula. -/
def chapterRamificationIndex
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (P : Ideal B) : ℕ :=
  P.ramificationIdx A

def chapterResidueDegree
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (P : Ideal B) : ℕ :=
  P.inertiaDeg A

/--
The completed product decomposition from Theorem 12.1.  The branch factors
are the completions of the localizations at the primes `P i`.
-/
theorem completed_product_decomposition
    {A B : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsIntegrallyClosed B]
    [IsDiscreteValuationRing A] [Algebra A B] [Algebra.IsIntegral A B]
    {g : ℕ} (m : Ideal A) (π : A) (P : Fin g → Ideal B) (e : Fin g → ℕ)
    [m.IsMaximal] [hprime : ∀ i, (P i).IsPrime]
    [hmax : ∀ i, (P i).IsMaximal]
    (huniformizer : m = Ideal.span {π})
    (hfinite : Module.Finite A B) (hfree : Module.Free A B)
    (hfactor : ∀ n : ℕ,
      extendedPrincipalPowerIdeal A B π n = ⨅ i, P i ^ (n * e i))
    (he : ∀ i, 0 < e i)
    (hpair : pairwiseCoprimeIdeals P)
    (hP : ∀ i, (P i).LiesOver m)
    (hP_exhaustive :
      ∀ (q : Ideal B), q.IsPrime → q.LiesOver m → ∃ i, P i = q)
    (hP_distinct : Function.Injective P)
    [∀ i, Algebra A (branchCompletion B (P i))]
    [∀ i, Algebra (AdicCompletion m A) (branchCompletion B (P i))]
    [∀ i, IsScalarTower A B (branchCompletion B (P i))]
    [∀ i, IsScalarTower A (AdicCompletion m A) (branchCompletion B (P i))] :
    hasCompletedAlgebraProduct A B (AdicCompletion m A)
      (fun i => branchCompletion B (P i)) := by
  sorry

/-- Each finite quotient remembers the `i`th branch to precision `n * e i`. -/
theorem finite_precision_branch_indexing
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {g : ℕ} (π : A) (P : Fin g → Ideal B) (e : Fin g → ℕ) (n : ℕ)
    (hfactor : extendedPrincipalPowerIdeal A B π n = ⨅ i, P i ^ (n * e i))
    (hpair : pairwiseCoprimeIdeals P) :
    Nonempty
      ((B ⧸ extendedPrincipalPowerIdeal A B π n) ≃+*
        (∀ i, B ⧸ P i ^ (n * e i))) := by
  have hpow : Pairwise (fun i j => IsCoprime (P i ^ (n * e i)) (P j ^ (n * e j))) := by
    intro i j hij
    exact (hpair hij).pow
  rw [hfactor]
  exact ⟨Ideal.quotientInfRingEquivPiQuotient (fun i => P i ^ (n * e i)) hpow⟩


/-- The inverse-limit CRT equivalence supplies orthogonal branch projectors. -/
theorem compatible_branch_projector_idempotents
    {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (I : Ideal R) (J : ι → Ideal R)
    (hcrt : Chapter12CompatibleCRTSystem I J) :
    ∃ e : ι → IdempotentElement (AdicCompletion I R),
      (∀ i j, i ≠ j → (e i).1 * (e j).1 = 0) ∧
        (∑ i, (e i).1) = 1 ∧
        (∀ n i,
          hcrt.equiv n (AdicCompletion.evalₐ I n (e i).1) =
            (fun j => if j = i then 1 else 0)) := by
  classical
  let qeq (n : ℕ) :
      (R ⧸ (I ^ n • (⊤ : Ideal R))) ≃+* R ⧸ I ^ n :=
    (Ideal.quotientEquivAlgOfEq R (by
      ext x
      simp)).toRingEquiv
  have hqfactor {m n : ℕ} (hmn : m ≤ n) (x : R ⧸ I ^ n) :
      qeq m (AdicCompletion.transitionMap I R hmn ((qeq n).symm x)) =
        Ideal.Quotient.factorPow I hmn x := by
    induction x using Quotient.inductionOn' with
    | _ r => rfl
  have hcrt_nat {m n : ℕ} (hmn : m ≤ n) (z : R ⧸ I ^ n) :
      hcrt.equiv m (Ideal.Quotient.factorPow I hmn z) =
        fun i => Ideal.Quotient.factorPow (J i) hmn ((hcrt.equiv n z) i) := by
    induction z using Quotient.inductionOn' with
    | _ r =>
      change hcrt.equiv m (Ideal.Quotient.factorPow I hmn
          (Ideal.Quotient.mk (I ^ n) r)) =
        fun i => Ideal.Quotient.factorPow (J i) hmn
          ((hcrt.equiv n (Ideal.Quotient.mk (I ^ n) r)) i)
      rw [hcrt.compatible n r]
      convert hcrt.compatible m r using 1 <;> rfl
  have hcrt_nat_symm {m n : ℕ} (hmn : m ≤ n)
      (z : ∀ i, R ⧸ (J i) ^ n) :
      Ideal.Quotient.factorPow I hmn ((hcrt.equiv n).symm z) =
        (hcrt.equiv m).symm (fun i =>
          Ideal.Quotient.factorPow (J i) hmn (z i)) := by
    apply (hcrt.equiv m).injective
    calc
      hcrt.equiv m (Ideal.Quotient.factorPow I hmn ((hcrt.equiv n).symm z)) =
          fun i => Ideal.Quotient.factorPow (J i) hmn
            ((hcrt.equiv n ((hcrt.equiv n).symm z)) i) :=
        hcrt_nat hmn ((hcrt.equiv n).symm z)
      _ = fun i => Ideal.Quotient.factorPow (J i) hmn (z i) := by simp
      _ = hcrt.equiv m ((hcrt.equiv m).symm (fun i =>
          Ideal.Quotient.factorPow (J i) hmn (z i))) := by simp
  let delta (i : ι) (n : ℕ) : ∀ j, R ⧸ (J j) ^ n :=
    fun j => if j = i then 1 else 0
  let z (i : ι) : AdicCompletion I R :=
    ⟨fun n => (qeq n).symm ((hcrt.equiv n).symm (delta i n)), by
      intro m n hmn
      apply (qeq m).injective
      rw [hqfactor, hcrt_nat_symm hmn]
      simp [delta]⟩
  have hz (i : ι) (n : ℕ) :
      AdicCompletion.evalₐ I n (z i) = (hcrt.equiv n).symm (delta i n) := by
    change qeq n ((z i).val n) = _
    change qeq n ((qeq n).symm ((hcrt.equiv n).symm (delta i n))) = _
    exact (qeq n).apply_symm_apply _
  let e : ι → IdempotentElement (AdicCompletion I R) := fun i =>
    ⟨z i, by
      apply AdicCompletion.ext_evalₐ
      intro n
      rw [map_mul, hz]
      apply (hcrt.equiv n).injective
      funext j
      by_cases hji : j = i
      · simp [delta, hji]
      · simp [delta, hji]⟩
  refine ⟨e, ?_, ?_, ?_⟩
  · intro i j hij
    apply AdicCompletion.ext_evalₐ
    intro n
    change AdicCompletion.evalₐ I n (z i * z j) = 0
    rw [map_mul, hz i n, hz j n]
    apply (hcrt.equiv n).injective
    funext k
    have hji : j ≠ i := Ne.symm hij
    rcases eq_or_ne k i with rfl | hki
    · simp [delta, hij]
    · rcases eq_or_ne k j with rfl | hkj
      · simp [delta, hji]
      · simp [delta, hki, hkj]
  · apply AdicCompletion.ext_evalₐ
    intro n
    change AdicCompletion.evalₐ I n (∑ i, z i) = AdicCompletion.evalₐ I n 1
    rw [map_sum]
    simp only [map_one]
    apply (hcrt.equiv n).injective
    rw [map_sum, map_one]
    funext j
    simp [hz, delta]
  · intro n i
    rw [hz]
    exact (hcrt.equiv n).apply_symm_apply (delta i n)

/-- A complete DVR factor, with the structural typeclasses carried as data. -/
structure Chapter12CompleteDVRData (R : Type*) [CommRing R] where
  [localRing : IsLocalRing R]
  [domain : IsDomain R]
  [dvr : IsDiscreteValuationRing R]
  complete : IsAdicComplete (IsLocalRing.maximalIdeal R) R

def isCompleteDVR (R : Type*) [CommRing R] : Prop :=
  Nonempty (Chapter12CompleteDVRData R)

/-- The completed branch factors are complete DVRs and finite free over the
    completed base.  Normality records that `B` is the finite normalization. -/
theorem completed_branch_factors_are_complete_DVR_and_finite_free
    {A B : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsIntegrallyClosed B] [IsDiscreteValuationRing A] [Algebra A B]
    [Algebra.IsIntegral A B]
    {g : ℕ} (m : Ideal A) (π : A) (P : Fin g → Ideal B) (e : Fin g → ℕ)
    [m.IsMaximal] [hprime : ∀ i, (P i).IsPrime]
    [hmax : ∀ i, (P i).IsMaximal]
    (huniformizer : m = Ideal.span {π})
    (hfinite : Module.Finite A B) (hfree : Module.Free A B)
    (hfactor : ∀ n : ℕ,
      extendedPrincipalPowerIdeal A B π n = ⨅ i, P i ^ (n * e i))
    (he : ∀ i, 0 < e i)
    (hpair : pairwiseCoprimeIdeals P)
    (hP : ∀ i, (P i).LiesOver m)
    (hP_exhaustive :
      ∀ (q : Ideal B), q.IsPrime → q.LiesOver m → ∃ i, P i = q)
    (hP_distinct : Function.Injective P)
    [Algebra (AdicCompletion m A) (B ⊗[A] AdicCompletion m A)]
    [∀ i, Algebra (AdicCompletion m A) (branchCompletion B (P i))]
    [hbranchLocal : ∀ i, IsLocalRing (branchCompletion B (P i))]
    [∀ i, IsScalarTower A B (branchCompletion B (P i))]
    [∀ i, IsScalarTower A (AdicCompletion m A) (branchCompletion B (P i))] :
    ∀ i, isCompleteDVR (branchCompletion B (P i)) ∧
    Module.Finite (AdicCompletion m A) (branchCompletion B (P i)) ∧
    Module.Free (AdicCompletion m A) (branchCompletion B (P i)) ∧
    chapterRamificationIndex (AdicCompletion m A) (branchCompletion B (P i))
        (IsLocalRing.maximalIdeal (branchCompletion B (P i))) = e i ∧
    chapterResidueDegree (AdicCompletion m A) (branchCompletion B (P i))
        (IsLocalRing.maximalIdeal (branchCompletion B (P i))) =
      chapterResidueDegree A B (P i) := by
  let hNoeth : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  let hDedekind : IsDedekindDomain B := by
    let hNoeth : IsNoetherianRing B := hNoeth
    exact (isDedekindDomain_iff (A := B) (FractionRing B)).2
      ⟨inferInstance, inferInstance, Ring.DimensionLEOne.of_isIntegral A B,
        (isIntegrallyClosed_iff (FractionRing B)).1 inferInstance⟩
  intro i
  let hDedekind : IsDedekindDomain B := hDedekind
  let hfree : Module.Free A B := hfree
  have hmapinj : Function.Injective (algebraMap A B) := by
    intro a b hab
    have hs : a • (1 : B) = b • (1 : B) := by
      simpa only [Algebra.smul_def, mul_one] using hab
    exact smul_left_injective A (M := B) one_ne_zero hs
  have hP0 : P i ≠ (⊥ : Ideal B) := by
    intro hzero
    have hcomap : (P i).comap (algebraMap A B) = m := (hP i).1.symm
    rw [hzero, Ideal.comap_bot_of_injective _ hmapinj] at hcomap
    have hm0 : m ≠ (⊥ : Ideal A) := by
      rw [IsLocalRing.eq_maximalIdeal (inferInstance : m.IsMaximal)]
      exact IsDiscreteValuationRing.not_a_field A
    exact hm0 hcomap.symm
  let hDVR : IsDiscreteValuationRing (branchLocalization B (P i)) :=
    by
      exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hP0
        (Localization.AtPrime (P i))
  sorry

/-- The fraction-field decomposition after inverting the base uniformizer.
    Normality records that the branch localizations are the normalized ones. -/
theorem completed_product_field_decomposition
    {A B : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsIntegrallyClosed B] [IsDiscreteValuationRing A] [Algebra A B]
    [Algebra.IsIntegral A B]
    {g : ℕ} (m : Ideal A) (π : A) (P : Fin g → Ideal B) (e : Fin g → ℕ)
    [m.IsMaximal] [hprime : ∀ i, (P i).IsPrime]
    [hmax : ∀ i, (P i).IsMaximal]
    (huniformizer : m = Ideal.span {π})
    (hfinite : Module.Finite A B) (hfree : Module.Free A B)
    (hfactor : ∀ n : ℕ,
      extendedPrincipalPowerIdeal A B π n = ⨅ i, P i ^ (n * e i))
    (he : ∀ i, 0 < e i)
    (hpair : pairwiseCoprimeIdeals P)
    (hP : ∀ i, (P i).LiesOver m)
    (hP_exhaustive :
      ∀ (q : Ideal B), q.IsPrime → q.LiesOver m → ∃ i, P i = q)
    (hP_distinct : Function.Injective P)
    [Algebra (AdicCompletion m A) (B ⊗[A] AdicCompletion m A)]
    [∀ i, Algebra A (branchCompletion B (P i))]
    [∀ i, Algebra (AdicCompletion m A) (branchCompletion B (P i))]
    [∀ i, IsScalarTower A B (branchCompletion B (P i))]
    [∀ i, IsScalarTower A (AdicCompletion m A) (branchCompletion B (P i))]
    [Algebra (FractionRing A) (FractionRing B)]
    [Algebra A (FractionRing B)]
    [IsScalarTower A B (FractionRing B)]
    [IsScalarTower A (FractionRing A) (FractionRing B)]
    [Algebra (FractionRing A) (completionFractionField A m)]
    :
    Nonempty
      (FractionRing B ⊗[FractionRing A] completionFractionField A m ≃+*
        (∀ i, branchFractionField B (P i))) := by
  sorry

/-- If a finite product of fields is a domain, it has only one factor. -/
theorem complete_base_has_one_completed_factor
    {g : ℕ} {L : Fin g → Type*} [∀ i, Field (L i)]
    (hdomain : IsDomain (∀ i, L i)) (hg : 0 < g) : g = 1 := by
  let _ : IsDomain (∀ i, L i) := hdomain
  have hsub : ∀ i j : Fin g, i = j := by
    intro i j
    by_contra hij
    let x : ∀ k, L k := fun k => if k = i then 1 else 0
    let y : ∀ k, L k := fun k => if k = j then 1 else 0
    have hxy : x * y = 0 := by
      funext k
      by_cases hki : k = i
      · subst k
        by_cases hkj : i = j
        · exact (hij hkj).elim
        · simp [x, y, hkj]
      · simp [x, y, hki]
    have hx : x ≠ 0 := by
      intro hx
      have := congrFun hx i
      simp [x] at this
    have hy : y ≠ 0 := by
      intro hy
      have := congrFun hy j
      simp [y] at this
    exact (mul_ne_zero hx hy) hxy
  have hcard : Fintype.card (Fin g) ≤ 1 :=
    Fintype.card_le_one_iff_subsingleton.mpr ⟨hsub⟩
  have hle : g ≤ 1 := by simpa using hcard
  omega

/-- In the one-branch complete case the defectless equality is `[L : K] = e f`. -/
theorem complete_one_branch_fundamental_equality
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ)
    (w : Valuation L Γ) [v.HasExtension w]
    (e f : ℕ)
    (he : chapterRamificationIndex v.valuationSubring w.valuationSubring
      (IsLocalRing.maximalIdeal w.valuationSubring) = e)
    (hf : chapterResidueDegree v.valuationSubring w.valuationSubring
      (IsLocalRing.maximalIdeal w.valuationSubring) = f)
    [Valuation.IsRankOneDiscrete v] [Valuation.IsRankOneDiscrete w]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal v.valuationSubring)
      v.valuationSubring) :
    Module.finrank K L = e * f := by
  have hfinite : Module.Finite v.valuationSubring w.valuationSubring := by
    let : Chapter09.CompleteDVR v.valuationSubring :=
      { toIsDiscreteValuationRing := inferInstance
        isAdicComplete' := hcomplete }
    have hH : Chapter10.Chapter10IsHenselianValuedField v :=
      Chapter09.complete_DVR_is_henselian
    have hEqVal (W : Chapter10.Chapter10ValuationOnField L)
        (hW : v.IsEquiv (W.valuation.comap (algebraMap K L))) :
        W.valuation.IsEquiv w :=
      Chapter10.chapter10_henselian_valuation_has_unique_branch v hH W.valuation w hW
        (Valuation.HasExtension.val_isEquiv_comap (vR := v) (vA := w))
    obtain ⟨W₀, hW₀⟩ :=
      Chapter10.chapter10_algebraic_valuation_extension_exists
        (K := K) (L := L) (Γ₀ := Γ) v
    let W₀' : Chapter10.Chapter10ValuationOnField L :=
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
    have hclosure : (w.valuationSubring : Set L) =
        {x : L | IsIntegral v.valuationSubring x} := by
      ext x
      change x ∈ w.valuationSubring ↔ IsIntegral v.valuationSubring x
      rw [show IsIntegral v.valuationSubring x ↔
          ∀ (W : Chapter10.Chapter10ValuationOnField L),
            v.IsEquiv (W.valuation.comap (algebraMap K L)) →
              x ∈ W.valuation.valuationSubring by
            simpa [Chapter10.Chapter10IntegralElements] using
              (Set.ext_iff.mp (Chapter10.chapter10_integral_closure_valuative_criterion v) x)]
      constructor
      · intro hx W hW
        have hEq : W.valuation.valuationSubring = w.valuationSubring :=
          (Valuation.isEquiv_iff_valuationSubring W.valuation w).mp (hEqVal W hW)
        rw [hEq]
        exact hx
      · intro hx
        have hxW := hx W₀' hW₀'
        have hEq : W₀'.valuation.valuationSubring = w.valuationSubring :=
          (Valuation.isEquiv_iff_valuationSubring W₀'.valuation w).mp
            (hEqVal W₀' hW₀')
        rw [← hEq]
        exact hxW
    have hnorm : Module.Finite v.valuationSubring (integralClosure v.valuationSubring L) := by
      let hcdvr : Chapter11.chapter11IsCompleteDVR v.valuationSubring :=
        { isAdicComplete := hcomplete }
      exact Chapter11.chapter11_complete_dvr_valuation_ring_is_finite
        v.valuationSubring K L hcdvr
    let e' : (integralClosure v.valuationSubring L) ≃ₗ[v.valuationSubring]
        w.valuationSubring :=
      { toFun := fun x =>
          ⟨x.1, (Set.ext_iff.mp hclosure x.1).mpr x.2⟩
        invFun := fun x =>
          ⟨x.1, (Set.ext_iff.mp hclosure x.1).mp x.2⟩
        left_inv := by intro x; apply Subtype.ext; rfl
        right_inv := by intro x; apply Subtype.ext; rfl
        map_add' := by intro x y; apply Subtype.ext; rfl
        map_smul' := by intro c x; apply Subtype.ext; rfl }
    let : Module.Finite v.valuationSubring (integralClosure v.valuationSubring L) := hnorm
    exact Module.Finite.equiv e'
  let : Module.Finite v.valuationSubring w.valuationSubring := hfinite
  let : Module.IsTorsionFree v.valuationSubring w.valuationSubring := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro a x hax
    rcases eq_or_ne a 0 with rfl | ha
    · exact Or.inl rfl
    · exact Or.inr (mul_left_cancel₀
        (show algebraMap v.valuationSubring w.valuationSubring a ≠ 0 by
          intro h
          have hz : algebraMap v.valuationSubring w.valuationSubring a =
              algebraMap v.valuationSubring w.valuationSubring (0 : v.valuationSubring) := by
            simpa using h
          exact ha ((Valuation.HasExtension.algebraMap_injective
            (vK := v) (vA := w)) hz))
        (by simpa [Algebra.smul_def] using hax))
  let : Module.Free v.valuationSubring w.valuationSubring := by infer_instance
  let : FaithfulSMul v.valuationSubring w.valuationSubring :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (Valuation.HasExtension.algebraMap_injective (vK := v) (vA := w))
  let : Fintype ((IsLocalRing.maximalIdeal v.valuationSubring).primesOver
      w.valuationSubring) :=
    Set.Finite.fintype (Algebra.QuasiFinite.finite_primesOver
      (IsLocalRing.maximalIdeal v.valuationSubring))
  have hq_eq (q : (IsLocalRing.maximalIdeal v.valuationSubring).primesOver
      w.valuationSubring) :
      q.1 = IsLocalRing.maximalIdeal w.valuationSubring := by
    exact IsLocalRing.eq_maximalIdeal
      (q.2.1.isMaximal (Ideal.ne_bot_of_mem_primesOver
        (IsDiscreteValuationRing.not_a_field v.valuationSubring) q.2))
  let : Unique ((IsLocalRing.maximalIdeal v.valuationSubring).primesOver
      w.valuationSubring) :=
    { default := Ideal.primesOver.mk
        (IsLocalRing.maximalIdeal v.valuationSubring)
        (IsLocalRing.maximalIdeal w.valuationSubring)
      uniq := fun q => Subtype.ext (hq_eq q) }
  have hdefault :
      (default : (IsLocalRing.maximalIdeal v.valuationSubring).primesOver
        w.valuationSubring).1 = IsLocalRing.maximalIdeal w.valuationSubring :=
    hq_eq default
  have hfinrank : Module.finrank v.valuationSubring w.valuationSubring =
      Module.finrank K L := by
    exact (IsFractionRing.finrank_eq v.valuationSubring K
      w.valuationSubring L).symm
  have hsum :=
    Ideal.sum_ramification_inertia_eq_finrank
      (p := IsLocalRing.maximalIdeal v.valuationSubring)
      (S := w.valuationSubring)
  rw [Fintype.sum_unique, hfinrank] at hsum
  have hprod :
      chapterRamificationIndex v.valuationSubring w.valuationSubring
          (IsLocalRing.maximalIdeal w.valuationSubring) *
        chapterResidueDegree v.valuationSubring w.valuationSubring
          (IsLocalRing.maximalIdeal w.valuationSubring) = Module.finrank K L := by
    simpa only [chapterRamificationIndex, chapterResidueDegree, hdefault] using hsum
  calc
    Module.finrank K L =
        chapterRamificationIndex v.valuationSubring w.valuationSubring
          (IsLocalRing.maximalIdeal w.valuationSubring) *
        chapterResidueDegree v.valuationSubring w.valuationSubring
          (IsLocalRing.maximalIdeal w.valuationSubring) := hprod.symm
    _ = e * f := by rw [he, hf]

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter12
