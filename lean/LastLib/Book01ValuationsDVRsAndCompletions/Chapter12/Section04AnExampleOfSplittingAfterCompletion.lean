import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Dependencies

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

/-! # Book 1, Chapter 12, Section 12.4: An Example of Splitting After Completion
-/

/-! ## 12.4. Primitive elements, factorization, and projectors -/

/-- The completed polynomial quotient associated to a polynomial over a field. -/
abbrev completedPolynomialQuotient
    {K Khat : Type*} [Field K] [Field Khat] [Algebra K Khat]
    (f : K[X]) : Type _ :=
  Khat[X] ⧸ Ideal.span {f.map (algebraMap K Khat)}

/-- A tensor product with a primitive polynomial quotient is a completed polynomial quotient. -/
theorem primitive_tensor_polynomial_model
    {K Khat : Type*} [Field K] [Field Khat] [Algebra K Khat]
    (f : K[X]) :
    Nonempty
      ((K[X] ⧸ Ideal.span {f}) ⊗[K] Khat ≃+*
        completedPolynomialQuotient (Khat := Khat) f) := by
  let eK : MvPolynomial Unit K ≃ₐ[K] K[X] :=
    MvPolynomial.uniqueAlgEquiv K Unit
  let eKhat : MvPolynomial Unit Khat ≃ₐ[Khat] Khat[X] :=
    MvPolynomial.uniqueAlgEquiv Khat Unit
  let t : K[X] ⊗[K] Khat ≃+* Khat[X] :=
    (Algebra.TensorProduct.comm K K[X] Khat).toRingEquiv.trans
      ((Algebra.TensorProduct.congr
          (AlgEquiv.refl : Khat ≃ₐ[Khat] Khat) eK.symm).toRingEquiv.trans
        ((MvPolynomial.algebraTensorAlgEquiv K Khat).toRingEquiv.trans
          eKhat.toRingEquiv))
  have ht (p : K[X]) :
      t (algebraMap K[X] (K[X] ⊗[K] Khat) p) =
        p.map (algebraMap K Khat) := by
    have hring :
        t.toRingHom.comp (algebraMap K[X] (K[X] ⊗[K] Khat)) =
          Polynomial.mapRingHom (algebraMap K Khat) := by
      apply Polynomial.ringHom_ext
      · intro a
        simp [t, eK, eKhat]
      · simp [t, eK, eKhat]
    have := congrArg (fun h : K[X] →+* Khat[X] => h p) hring
    exact this
  have hIJ :
      Ideal.span ({f.map (algebraMap K Khat)} : Set Khat[X]) =
        (Ideal.span ({f} : Set K[X])).map
          (t.toRingHom.comp (algebraMap K[X] (K[X] ⊗[K] Khat))) := by
    rw [Ideal.map_span]
    simp only [Set.image_singleton, RingHom.coe_comp, Function.comp_apply]
    change Ideal.span ({f.map (algebraMap K Khat)} : Set Khat[X]) =
      Ideal.span ({t (algebraMap K[X] (K[X] ⊗[K] Khat) f)} : Set Khat[X])
    rw [← ht f]
  have hIJ' :
      Ideal.span ({f.map (algebraMap K Khat)} : Set Khat[X]) =
        ((Ideal.span ({f} : Set K[X])).map
          (algebraMap K[X] (K[X] ⊗[K] Khat))).map t.toRingHom := by
    simpa only [Ideal.map_map] using hIJ
  let qeq :=
    Algebra.TensorProduct.quotientTensorEquiv (R := K) K Khat K[X]
      (Ideal.span ({f} : Set K[X]))
  refine ⟨qeq.toRingEquiv.trans (Ideal.quotientEquiv _ _ t hIJ')⟩

/-- Coprime completed factors give a product of completed polynomial fields. -/
theorem completed_polynomial_factorization_product
    {K : Type*} [Field K] {g : ℕ} (f : K[X]) (factors : Fin g → K[X])
    (hfactor : f = ∏ i, factors i)
    (hpair : Pairwise (fun i j => IsCoprime (factors i) (factors j))) :
    Nonempty
      ((K[X] ⧸ Ideal.span {f}) ≃+*
        (∀ i, K[X] ⧸ Ideal.span {factors i})) := by
  have hcop : Pairwise (fun i j => IsCoprime (Ideal.span {factors i})
      (Ideal.span {factors j})) := by
    intro i j hij
    exact (Ideal.isCoprime_span_singleton_iff _ _).2 (hpair hij)
  have hspan : (⨅ i, Ideal.span ({factors i} : Set K[X])) =
      Ideal.span {∏ i, factors i} := Ideal.iInf_span_singleton hpair
  rw [hfactor, ← hspan]
  exact ⟨Ideal.quotientInfRingEquivPiQuotient
    (fun i => Ideal.span ({factors i} : Set K[X])) hcop⟩


/-- Each irreducible completed polynomial factor is a field. -/
theorem irreducible_completed_factor_is_field
    {K : Type*} [Field K] {f : K[X]} (hf : Irreducible f) :
    IsField (K[X] ⧸ Ideal.span {f}) := by
  let _ : (Ideal.span ({f} : Set K[X])).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hf
  let _ : Field (K[X] ⧸ Ideal.span {f}) :=
    Ideal.Quotient.field (Ideal.span ({f} : Set K[X]))
  exact Field.toIsField _


/-- The split quadratic algebra used for the explicit idempotent example. -/
abbrev quadraticSplitAlgebra (R : Type*) [CommRing R] (_a _b : R) : Type _ :=
  R × R

/-- The polynomial quotient whose two distinct roots give the split factors. -/
abbrev quadraticSplitQuotient (R : Type*) [CommRing R] (a b : R) : Type _ :=
  R[X] ⧸ Ideal.span {(X - C a) * (X - C b)}

/-- The image of the polynomial coordinate in the split quadratic algebra. -/
def quadraticCoordinate (R : Type*) [CommRing R] (a b : R) :
    quadraticSplitAlgebra R a b :=
  (a, b)

/-- The two concrete projectors from the split quadratic algebra. -/
def quadraticProjectorA {R : Type*} [Field R] (a b : R) (_h : a ≠ b) :
    quadraticSplitAlgebra R a b :=
  (1, 0)

def quadraticProjectorB {R : Type*} [Field R] (a b : R) (_h : a ≠ b) :
    quadraticSplitAlgebra R a b :=
  (0, 1)

/-- The quotient representative of `(X-b)/(a-b)`. -/
def quadraticQuotientProjectorA {R : Type*} [Field R] (a b : R) (_h : a ≠ b) :
    quadraticSplitQuotient R a b :=
  Ideal.Quotient.mk _ ((a - b)⁻¹ • (X - C b))

/-- The quotient representative of `(X-a)/(b-a)`. -/
def quadraticQuotientProjectorB {R : Type*} [Field R] (a b : R) (_h : a ≠ b) :
    quadraticSplitQuotient R a b :=
  Ideal.Quotient.mk _ ((b - a)⁻¹ • (X - C a))

/-- The quotient projector identities `e_a²=e_a`, `e_b²=e_b`, `e_ae_b=0`,
    and `e_a+e_b=1`. -/
theorem quadratic_projector_relations
    {R : Type*} [Field R] (a b : R) (h : a ≠ b) :
    let ea := quadraticQuotientProjectorA a b h
    let eb := quadraticQuotientProjectorB a b h
    ea * ea = ea ∧ eb * eb = eb ∧ ea * eb = 0 ∧ ea + eb = 1 := by
  let I : Ideal R[X] := Ideal.span {X - C a}
  let J : Ideal R[X] := Ideal.span {X - C b}
  have hcop : IsCoprime I J := by
    dsimp [I, J]
    exact (Ideal.isCoprime_span_singleton_iff _ _).2
      (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr h).isUnit)
  have hmul : I * J =
      Ideal.span {((X - C a) * (X - C b) : R[X])} := by
    dsimp [I, J]
    rw [Ideal.span_singleton_mul_span_singleton]
  let e : quadraticSplitQuotient R a b ≃+* R × R :=
    (Ideal.quotEquivOfEq hmul.symm).trans
      ((Ideal.quotientMulEquivQuotientProd I J hcop).trans
        (RingEquiv.prodCongr
          (Polynomial.quotientSpanXSubCAlgEquiv a).toRingEquiv
          (Polynomial.quotientSpanXSubCAlgEquiv b).toRingEquiv))
  have heval (p : R[X]) :
      e (Ideal.Quotient.mk
          (Ideal.span {((X - C a) * (X - C b) : R[X])}) p) =
        (p.eval a, p.eval b) := by
    simp [e, I, J, Prod.map,
      Ideal.quotientMulEquivQuotientProd_fst,
      Ideal.quotientMulEquivQuotientProd_snd]
  have hea : e (quadraticQuotientProjectorA a b h) = (1, 0) := by
    rw [quadraticQuotientProjectorA, heval]
    apply Prod.ext
    · rw [Polynomial.eval_smul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C]
      simpa [smul_eq_mul] using inv_mul_cancel₀ (sub_ne_zero.mpr h)
    · rw [Polynomial.eval_smul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C]
      simp
  have heb : e (quadraticQuotientProjectorB a b h) = (0, 1) := by
    rw [quadraticQuotientProjectorB, heval]
    apply Prod.ext
    · rw [Polynomial.eval_smul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C]
      simp
    · rw [Polynomial.eval_smul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C]
      simpa [smul_eq_mul] using inv_mul_cancel₀ (sub_ne_zero.mpr h.symm)
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply e.injective
    simp [map_mul, hea]
  · apply e.injective
    simp [map_mul, heb]
  · apply e.injective
    simp [map_mul, hea, heb]
  · apply e.injective
    simp [map_add, hea, heb]


/-- The explicit projectors identify the two factors of the split quadratic algebra. -/
theorem quadratic_projectors_are_factor_projectors
    {R : Type*} [Field R] (a b : R) (h : a ≠ b) :
    Nonempty (quadraticSplitQuotient R a b ≃+* R × R) := by
  let I : Ideal R[X] := Ideal.span {X - C a}
  let J : Ideal R[X] := Ideal.span {X - C b}
  have hcop : IsCoprime I J := by
    dsimp [I, J]
    exact (Ideal.isCoprime_span_singleton_iff _ _).2
      (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr h).isUnit)
  have hmul : I * J =
      Ideal.span {((X - C a) * (X - C b) : R[X])} := by
    dsimp [I, J]
    rw [Ideal.span_singleton_mul_span_singleton]
  let crt : R[X] ⧸ (I * J) ≃+* R × R :=
    (Ideal.quotientMulEquivQuotientProd I J hcop).trans
      (RingEquiv.prodCongr
        (Polynomial.quotientSpanXSubCAlgEquiv a).toRingEquiv
        (Polynomial.quotientSpanXSubCAlgEquiv b).toRingEquiv)
  exact ⟨(Ideal.quotEquivOfEq hmul.symm).trans crt⟩

/-- Under the splitting equivalence, the quotient projectors are the two coordinate idempotents. -/
theorem quadratic_quotient_projectors_are_coordinates
    {R : Type*} [Field R] (a b : R) (h : a ≠ b) :
    ∃ e : quadraticSplitQuotient R a b ≃+* R × R,
      e (quadraticQuotientProjectorA a b h) = (1, 0) ∧
        e (quadraticQuotientProjectorB a b h) = (0, 1) := by
  let I : Ideal R[X] := Ideal.span {X - C a}
  let J : Ideal R[X] := Ideal.span {X - C b}
  have hcop : IsCoprime I J := by
    dsimp [I, J]
    exact (Ideal.isCoprime_span_singleton_iff _ _).2
      (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr h).isUnit)
  have hmul : I * J =
      Ideal.span {((X - C a) * (X - C b) : R[X])} := by
    dsimp [I, J]
    rw [Ideal.span_singleton_mul_span_singleton]
  let e : quadraticSplitQuotient R a b ≃+* R × R :=
    (Ideal.quotEquivOfEq hmul.symm).trans
      ((Ideal.quotientMulEquivQuotientProd I J hcop).trans
        (RingEquiv.prodCongr
          (Polynomial.quotientSpanXSubCAlgEquiv a).toRingEquiv
          (Polynomial.quotientSpanXSubCAlgEquiv b).toRingEquiv))
  have heval (p : R[X]) :
      e (Ideal.Quotient.mk
          (Ideal.span {((X - C a) * (X - C b) : R[X])}) p) =
        (p.eval a, p.eval b) := by
    simp [e, I, J, Prod.map,
      Ideal.quotientMulEquivQuotientProd_fst,
      Ideal.quotientMulEquivQuotientProd_snd]
  have hA :
      (((a - b)⁻¹ • (X - C b)).eval a,
        ((a - b)⁻¹ • (X - C b)).eval b) = (1, 0) := by
    apply Prod.ext
    · rw [Polynomial.eval_smul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C]
      simpa [smul_eq_mul] using inv_mul_cancel₀ (sub_ne_zero.mpr h)
    · rw [Polynomial.eval_smul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C]
      simp
  have hB :
      (((b - a)⁻¹ • (X - C a)).eval a,
        ((b - a)⁻¹ • (X - C a)).eval b) = (0, 1) := by
    apply Prod.ext
    · rw [Polynomial.eval_smul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C]
      simp
    · rw [Polynomial.eval_smul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C]
      simpa [smul_eq_mul] using inv_mul_cancel₀ (sub_ne_zero.mpr h.symm)
  refine ⟨e, ?_, ?_⟩
  · rw [quadraticQuotientProjectorA, heval]
    exact hA
  · rw [quadraticQuotientProjectorB, heval]
    exact hB


/-- A repeated factorization supplies a square divisor. -/
theorem repeated_polynomial_factor_has_square_divisor
    {A : Type*} [CommRing A] (f : A[X])
    (hrepeated : ∃ g : A[X], g ≠ 0 ∧ g * g ∣ f) :
    ∃ g q : A[X], g ≠ 0 ∧ f = g * g * q := by
  rcases hrepeated with ⟨g, hg, hdiv⟩
  rcases hdiv with ⟨q, hq⟩
  exact ⟨g, q, hg, hq⟩


/-- Concrete maps in the branch-language chain. -/
structure Chapter12BranchLanguageData
    {B L : Type*} [CommRing B] [Field L] [Algebra B L]
    (P : Ideal B) [P.IsPrime] {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ) where
  center : ∀ x : B, x ∈ P ↔ w (algebraMap B L x) < 1
  valuationMap : B →+* w.valuationSubring
  valuationMap_spec : ∀ x : B, (valuationMap x : L) = algebraMap B L x
  localizationMap : B →+* branchLocalization B P
  localizationMap_spec : localizationMap = algebraMap B (branchLocalization B P)
  completionMap : branchLocalization B P →+* branchCompletion B P
  completionMap_spec :
    completionMap = algebraMap (branchLocalization B P) (branchCompletion B P)
  fractionFieldMap : branchCompletion B P →+* branchFractionField B P
  fractionFieldMap_spec :
    fractionFieldMap = algebraMap (branchCompletion B P) (branchFractionField B P)

/-- A branch can be tracked through prime, localization, valuation, completion, and field. -/
theorem branch_language_chain
    {B L : Type*} [CommRing B] [Field L] [Algebra B L]
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (P : Ideal B) [P.IsPrime] (w : Valuation L Γ)
    (hcenter : ∀ x : B, x ∈ P ↔ w (algebraMap B L x) < 1)
    (hbounded : ∀ x : B, w (algebraMap B L x) ≤ 1) :
    ∃ d : Chapter12BranchLanguageData P w, d.center = hcenter := by
  let valuationMap : B →+* w.valuationSubring :=
    { toFun := fun x => ⟨algebraMap B L x, hbounded x⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  refine ⟨{
    center := hcenter
    valuationMap := valuationMap
    valuationMap_spec := by intro x; rfl
    localizationMap := algebraMap B (branchLocalization B P)
    localizationMap_spec := rfl
    completionMap := algebraMap (branchLocalization B P) (branchCompletion B P)
    completionMap_spec := rfl
    fractionFieldMap := algebraMap (branchCompletion B P) (branchFractionField B P)
    fractionFieldMap_spec := rfl
  }, ?_⟩
  rfl


/-- The `e` and `f` labels are unchanged along the branch-language chain. -/
theorem branch_language_chain_preserves_ef
    {A B Ahat Bhat : Type*} [CommRing A] [CommRing B]
    [CommRing Ahat] [CommRing Bhat] [Algebra A B] [Algebra Ahat Bhat]
    (p : Ideal A) (P : Ideal B) (phat : Ideal Ahat) (Phat : Ideal Bhat)
    (transport : Chapter12BranchInvariantTransport p P phat Phat) :
    chapterRamificationIndex Ahat Bhat Phat = chapterRamificationIndex A B P ∧
      chapterResidueDegree Ahat Bhat Phat = chapterResidueDegree A B P := by
  exact completed_branch_preserves_ef p P phat Phat transport
    (chapterRamificationIndex A B P) (chapterResidueDegree A B P) rfl rfl


end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter12
