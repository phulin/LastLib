import LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.Section03SemilocalDedekindStructure

universe u v

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter11

noncomputable section

open Ideal IsLocalRing
open Polynomial
open scoped BigOperators TensorProduct WithZero Polynomial nonZeroDivisors

/-! # Chapter 11: several places above one place

This file is a statement-only formalization of sections 11.1--11.9 of Book 1.
The declarations are intentionally local to this namespace because the chapters
are generated independently.
-/

/-! # Book 1, Chapter 11, Section 11.4: Factorization of the Maximal Ideal
-/

/-! ## 11.4. Ramification, residue degree, and factorization -/

/-- Mathlib's intrinsic ramification index, named for chapter traceability. -/
def chapter11RamificationIndex (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (P : Ideal B) : ℕ :=
  P.ramificationIdx A

/-- Mathlib's intrinsic inertia/residue degree, named for chapter traceability. -/
def chapter11InertiaDegree (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (P : Ideal B) : ℕ :=
  P.inertiaDeg A

/-- The local factorization `π B_P = P_P^e`. -/
theorem chapter11_local_uniformizer_factorization
    (A B : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Algebra A B] [IsDedekindDomain B] (m : Ideal A) (π : A)
    (hπ : chapter11IsUniformizer A m π) (P : Ideal B) [P.IsPrime] [P.LiesOver m]
    (_hm0 : m ≠ ⊥) (hP0 : P ≠ ⊥)
    (hI0 : Ideal.map (algebraMap A (Localization.AtPrime P)) m ≠ ⊥) :
    Ideal.map (algebraMap A (Localization.AtPrime P)) (Ideal.span {π}) =
      (Ideal.map (algebraMap B (Localization.AtPrime P)) P) ^ P.ramificationIdx A := by
  have : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hP0
      (Localization.AtPrime P)
  let I : Ideal (Localization.AtPrime P) :=
    Ideal.map (algebraMap A (Localization.AtPrime P)) m
  obtain ⟨n, hIn⟩ :=
    exists_maximalIdeal_pow_eq_of_principal (Localization.AtPrime P)
      (IsPrincipalIdealRing.principal (IsLocalRing.maximalIdeal (Localization.AtPrime P))) I hI0
  have hlen : (Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ I)).toNat = n := by
    rw [hIn, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
    rfl
  have he : P.ramificationIdx A = n := by
    rw [Ideal.ramificationIdx_eq m P]
    change (Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ I)).toNat = n
    exact hlen
  rw [← hπ]
  change I = (Ideal.map (algebraMap B (Localization.AtPrime P)) P) ^ P.ramificationIdx A
  rw [hIn, he, Localization.AtPrime.map_eq_maximalIdeal]

/-- The global factorization `mB = ∏ P_i^{e_i}`. -/
theorem chapter11_global_ideal_factorization
    (A B : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Algebra A B] [IsDedekindDomain B] [Algebra.IsIntegral A B]
    [Module.IsTorsionFree A B] (m : Ideal A) [m.IsMaximal] (hm0 : m ≠ ⊥) :
    Ideal.map (algebraMap A B) m =
      ∏ P ∈ m.primesOver B, P ^ P.ramificationIdx A := by
  exact Ideal.map_algebraMap_eq_finsetProd_pow hm0

/-- Distinct branches are pairwise comaximal. -/
theorem chapter11_branch_ideals_pairwise_comaximal
    (B : Type*) [CommRing B] {ι : Type*} [Fintype ι]
    (P : ι → Ideal B) (hmax : ∀ i, (P i).IsMaximal) (hinj : Function.Injective P) :
    ∀ ⦃i j : ι⦄, i ≠ j → IsCoprime (P i) (P j) := by
  intro i j hij
  rw [isCoprime_iff_sup_eq]
  exact (hmax i).coprime_of_ne (hmax j) (by
    intro heq
    exact hij (hinj heq))

/-- The Chinese-remainder decomposition of `B / πB`. -/
theorem chapter11_chinese_remainder_decomposition
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    {ι : Type*} [Fintype ι] (m : Ideal A) (P : ι → Ideal B) (e : ι → ℕ)
    (hfactor : Ideal.map (algebraMap A B) m = ∏ i, (P i) ^ e i)
    (hcoprime : ∀ ⦃i j : ι⦄, i ≠ j → IsCoprime (P i) (P j)) :
    Nonempty
      (B ⧸ Ideal.map (algebraMap A B) m ≃+*
        (∀ i, B ⧸ (P i) ^ e i)) := by
  classical
  let J : ι → Ideal B := fun i ↦ (P i) ^ e i
  have hp : Pairwise (fun i j => IsCoprime (J i) (J j)) := by
    intro i j hij
    exact (hcoprime hij).pow
  have hprod : (∏ i, J i) = ⨅ i, J i := by
    have hset : (↑(Finset.univ : Finset ι) : Set ι).Pairwise
        (fun i j => IsCoprime (J i) (J j)) := by
      intro i _hi j _hj hij
      exact hp hij
    simpa using
      (Ideal.prod_eq_iInf_of_pairwise_isCoprime (s := Finset.univ) (J := J) hset)
  have hEq : Ideal.map (algebraMap A B) m = ⨅ i, J i := by
    simpa [J] using hfactor.trans hprod
  exact ⟨(Ideal.quotEquivOfEq hEq).trans
    (Ideal.quotientInfRingEquivPiQuotient J hp)⟩

/-- The `i`th prime-power filtration layer is represented as a nested submodule quotient. -/
abbrev chapter11SubmoduleQuotient
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (p : Submodule R M) : Type _ := M ⧸ p

abbrev chapter11PrimePowerLayer (B : Type*) [CommRing B] (P : Ideal B) (i : ℕ) : Type _ :=
  (P ^ i : Ideal B) ⧸ (P • ⊤ : Submodule B (P ^ i : Ideal B))

/-- When the branch ideal is principal, each nonzero prime-power layer is one
copy of the residue field. -/
theorem chapter11_prime_power_layer_is_a_residue_line
    (B : Type*) [CommRing B] [IsDedekindDomain B] (P : Ideal B)
    [P.IsPrime] [P.IsMaximal] [P.IsPrincipal] (e i : ℕ) (_hi : i < e)
    (hP0 : P ≠ ⊥) :
    Nonempty
      (chapter11PrimePowerLayer B P i ≃+
        (B ⧸ P)) := by
  exact ⟨(Ideal.quotEquivPowQuotPowSucc
    (by infer_instance) hP0 i).symm.toAddEquiv⟩

/-- The quotient `B / πB` has one `k`-dimension for every residue-degree layer. -/
theorem chapter11_residue_quotient_dimension_sum
    (A B : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Algebra A B] [Module.Finite A B] [Module.Free A B]
    [Algebra.IsIntegral A B] [Module.IsTorsionFree A B] [IsDedekindDomain B]
    (m : Ideal A) [m.IsPrime] [m.IsMaximal] :
    Module.finrank (A ⧸ m) (B ⧸ Ideal.map (algebraMap A B) m) =
      ∑ q : m.primesOver B, q.1.ramificationIdx A * q.1.inertiaDeg A := by
  let eκ : (A ⧸ m) ≃ₐ[A ⧸ m] m.ResidueField := by
    letI : Field (A ⧸ m) := Ideal.Quotient.field m
    exact IsFractionRing.algEquivOfAlgEquiv (R := A ⧸ m) (A := A ⧸ m)
      (K := A ⧸ m) (B := A ⧸ m) (L := m.ResidueField) .refl
  calc
    Module.finrank (A ⧸ m) (B ⧸ Ideal.map (algebraMap A B) m) =
        Module.finrank (A ⧸ m) ((A ⧸ m) ⊗[A] B) :=
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B m).toLinearEquiv.finrank_eq
    _ = Module.finrank (A ⧸ m) (m.Fiber B) :=
      (Algebra.TensorProduct.congr eκ (AlgEquiv.refl : B ≃ₐ[A] B)).toLinearEquiv.finrank_eq
    _ = Module.finrank m.ResidueField (m.Fiber B) := by
      apply Algebra.finrank_eq_of_equiv_equiv (R₀ := A ⧸ m)
        (S₀ := m.Fiber B) (R₁ := m.ResidueField) (S₁ := m.Fiber B)
        eκ.toRingEquiv (RingEquiv.refl _)
      ext a
      have heκ : eκ (Ideal.Quotient.mk m a) =
          algebraMap (A ⧸ m) m.ResidueField (Ideal.Quotient.mk m a) := by
        change eκ (algebraMap (A ⧸ m) (A ⧸ m) (Ideal.Quotient.mk m a)) =
          algebraMap (A ⧸ m) m.ResidueField (Ideal.Quotient.mk m a)
        exact eκ.commutes (Ideal.Quotient.mk m a)
      simp only [RingHom.comp_apply]
      change algebraMap m.ResidueField (m.Fiber B) (eκ (Ideal.Quotient.mk m a)) =
        algebraMap (A ⧸ m) (m.Fiber B) (Ideal.Quotient.mk m a)
      rw [heκ, ← IsScalarTower.algebraMap_apply (A ⧸ m) m.ResidueField
        (m.Fiber B)]
    _ = ∑ q : m.primesOver B, q.1.ramificationIdx A * q.1.inertiaDeg A :=
      (Ideal.sum_ramification_inertia_eq_finrank_fiber m B).symm

/-- Under finite freeness, the sum of `e_i f_i` is the field degree. -/
theorem chapter11_sum_ramification_times_inertia_is_degree
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra B L] [Algebra A L]
    [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing A K]
    [IsFractionRing B L] [Module.Finite A B] [Module.Free A B]
    [Algebra.IsIntegral A B] [Module.IsTorsionFree A B] [IsDedekindDomain B]
    (m : Ideal A) [m.IsPrime] [m.IsMaximal] :
    ∑ q : m.primesOver B, q.1.ramificationIdx A * q.1.inertiaDeg A =
      Module.finrank K L := by
  calc
    ∑ q : m.primesOver B, q.1.ramificationIdx A * q.1.inertiaDeg A =
        Module.finrank A B := Ideal.sum_ramification_inertia_eq_finrank m B
    _ = Module.finrank K L := (IsFractionRing.finrank_eq A K B L).symm

/-- A subfamily of the finite-normalization branches satisfies the fundamental
inequality.  The finiteness assumptions are explicit because the displayed
finite sum and the finite-length degree computation require them. -/
theorem chapter11_fundamental_inequality_for_branch_subfamily
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra B L]
    [Algebra A L] [Algebra K L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [IsIntegralClosure B A L] [Module.Finite A B] [Module.Free A B]
    [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]
    {iota : Type*} [Fintype iota] (m : Ideal A) (P : iota → Ideal B)
    [m.IsMaximal] (_hm0 : m ≠ ⊥)
    (hbranch : ∀ i, chapter11Branch A B m (P i))
    (hinj : Function.Injective P) :
    ∑ i, (P i).ramificationIdx A * (P i).inertiaDeg A ≤ Module.finrank K L := by
  let : Fintype (m.primesOver B) :=
    Set.Finite.fintype (Algebra.QuasiFinite.finite_primesOver m)
  let g : iota → m.primesOver B := fun i =>
    ⟨P i, (hbranch i).1, (hbranch i).2.2⟩
  have hg : Function.Injective g := by
    intro i j hij
    apply hinj
    exact congrArg Subtype.val hij
  have himage :
      (∑ i, (P i).ramificationIdx A * (P i).inertiaDeg A) =
        ∑ q ∈ (Finset.univ.image g), q.1.ramificationIdx A * q.1.inertiaDeg A := by
    rw [Finset.sum_image hg.injOn]
  have hsubset : (Finset.univ.image g : Finset (m.primesOver B)) ⊆ Finset.univ := by
    intro q hq
    exact Finset.mem_univ q
  have hle :
      (∑ q ∈ (Finset.univ.image g), q.1.ramificationIdx A * q.1.inertiaDeg A) ≤
        ∑ q : m.primesOver B, q.1.ramificationIdx A * q.1.inertiaDeg A := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun q hq hq' => Nat.zero_le _)
  calc
    ∑ i, (P i).ramificationIdx A * (P i).inertiaDeg A =
        ∑ q ∈ (Finset.univ.image g), q.1.ramificationIdx A * q.1.inertiaDeg A := himage
    _ ≤ ∑ q : m.primesOver B, q.1.ramificationIdx A * q.1.inertiaDeg A := hle
    _ = Module.finrank A B := Ideal.sum_ramification_inertia_eq_finrank m B
    _ = Module.finrank K L := (IsFractionRing.finrank_eq A K B L).symm

end
end LastLib.Book01ValuationsDVRsAndCompletions.Chapter11
