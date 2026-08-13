import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section01SeparatingBranchesByCompletion

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
    [Algebra Ahat (B ⊗[A] Ahat)] {ι : Type*}
    (C : ι → Type*) [∀ i, CommRing (C i)] [∀ i, Algebra Ahat (C i)] : Prop :=
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
    [Algebra (AdicCompletion m A) (B ⊗[A] AdicCompletion m A)]
    [∀ i, Algebra (AdicCompletion m A) (branchCompletion B (P i))] :
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
    (hcrt : Chapter12CompatibleCRTSystem I J)
    (_hcofinal : ∀ i, adicFiltrationsCofinal I (J i)) :
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
    completed base. -/
theorem completed_branch_factors_are_complete_DVR_and_finite_free
    {A B : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
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
    [Algebra (AdicCompletion m A) (B ⊗[A] AdicCompletion m A)]
    [∀ i, Algebra (AdicCompletion m A) (branchCompletion B (P i))] :
    ∀ i, isCompleteDVR (branchCompletion B (P i)) ∧
    Module.Finite (AdicCompletion m A) (branchCompletion B (P i)) ∧
    Module.Free (AdicCompletion m A) (branchCompletion B (P i)) := by
  sorry

/-- The fraction-field decomposition after inverting the base uniformizer.
    Normality records that the branch localizations are the normalized ones. -/
theorem completed_product_field_decomposition
    {A B : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
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
    [Algebra (AdicCompletion m A) (B ⊗[A] AdicCompletion m A)]
    [∀ i, Algebra (AdicCompletion m A) (branchCompletion B (P i))]
    [Algebra (FractionRing A) (FractionRing B)]
    [Algebra (FractionRing A) (completionFractionField A m)]
    :
    Nonempty
      (FractionRing B ⊗[FractionRing A] completionFractionField A m ≃+*
        (∀ i, branchFractionField B (P i))) := by
  sorry

/-- If the base is already complete, the tensor product has only one branch. -/
theorem complete_base_has_one_completed_factor
    {g : ℕ} {L : Fin g → Type*} [∀ i, Field (L i)]
    (hfield : IsField (∀ i, L i)) (hg : 0 < g) : g = 1 := by
  let _ : IsField (∀ i, L i) := hfield
  let _ : IsDomain (∀ i, L i) := hfield.isDomain
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
  sorry

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter12
