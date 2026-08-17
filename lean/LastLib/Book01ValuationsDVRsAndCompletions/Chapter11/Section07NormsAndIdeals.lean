import LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.Section06LocalizationAndResidues
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.Section04FactorizationOfTheMaximalIdeal
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.Section01SuccessivePrecision
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.Section03WhatShouldCountAsIntegral
import Mathlib.Data.ENat.BigOperators
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Trace.Quotient

universe u v

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter11

noncomputable section

open Ideal IsLocalRing
open Module
open Module.Basis
open Polynomial
open UniqueFactorizationMonoid
open scoped BigOperators TensorProduct WithZero Polynomial nonZeroDivisors

/-! # Chapter 11: several places above one place

This file is a statement-only formalization of sections 11.1--11.9 of Book 1.
The declarations are intentionally local to this namespace because the chapters
are generated independently.
-/

/-! # Book 1, Chapter 11, Section 11.7: Norms and Ideals
-/

/-! ## 11.7. Norms and the sum over branches -/

/-- The field norm, defined by the determinant of multiplication. -/
def chapter11FieldNorm (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (x : L) : K :=
  Algebra.norm K x

/-- The field trace, defined by the trace of multiplication. -/
def chapter11FieldTrace (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (x : L) : K :=
  Algebra.trace K L x

/-! The reduction maps in the finite-DVR trace and norm formulas are kept
explicit.  This avoids silently identifying arbitrary quotient presentations
with the canonical residue fields, which is especially important in mixed
characteristic. -/

/-- A ring homomorphism exhibiting a field as the residue field modulo `m`. -/
def chapter11ResidueMap
    (R k : Type*) [CommRing R] [Field k] (m : Ideal R)
    (ρ : R →+* k) : Prop :=
  Function.Surjective ρ ∧ ∀ x : R, ρ x = 0 ↔ x ∈ m

@[simp] theorem chapter11ResidueMap_iff
    (R k : Type*) [CommRing R] [Field k] (m : Ideal R)
    (ρ : R →+* k) :
    chapter11ResidueMap R k m ρ ↔
      Function.Surjective ρ ∧ ∀ x : R, ρ x = 0 ↔ x ∈ m := Iff.rfl

/-- The two finite-DVR residue shadows of integral trace and norm. -/
def chapter11DvrResidueTraceNormStatement
    (A B k l : Type*) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [CommRing B] [IsDomain B]
    [IsIntegrallyClosed B] [Algebra A B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B] [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l]
    (redA : A →+* k) (redB : B →+* l) (e : ℕ)
    (t n : B) : Prop :=
  redA (Algebra.intTrace A B t) =
      (e : k) * Algebra.trace k l (redB t) ∧
    redA (Algebra.intNorm A B n) = Algebra.norm k (redB n) ^ e

@[simp] theorem chapter11DvrResidueTraceNormStatement_iff
    (A B k l : Type*) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [CommRing B] [IsDomain B]
    [IsIntegrallyClosed B] [Algebra A B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B] [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l]
    (redA : A →+* k) (redB : B →+* l) (e : ℕ)
    (t n : B) :
    chapter11DvrResidueTraceNormStatement A B k l redA redB e t n ↔
      redA (Algebra.intTrace A B t) =
          (e : k) * Algebra.trace k l (redB t) ∧
        redA (Algebra.intNorm A B n) = Algebra.norm k (redB n) ^ e := Iff.rfl

private theorem chapter11_dvr_maximalIdeal_map_eq_pow_ramificationIdx
    (A B : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Algebra A B]
    [Algebra.IsIntegral A B] [Module.IsTorsionFree A B] [Module.Finite A B] :
    Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
      (IsLocalRing.maximalIdeal B) ^
        (IsLocalRing.maximalIdeal B).ramificationIdx A := by
  classical
  let m : Ideal A := IsLocalRing.maximalIdeal A
  let P : Ideal B := IsLocalRing.maximalIdeal B
  have hm0 : m ≠ (⊥ : Ideal A) := by
    exact IsDiscreteValuationRing.not_a_field A
  have hmap_le : Ideal.map (algebraMap A B) m ≤ P := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    simpa [P, IsLocalRing.mem_maximalIdeal] using
      map_nonunit (algebraMap A B) a
        (by simpa [m] using ha)
  have hmap0 : Ideal.map (algebraMap A B) m ≠ (⊥ : Ideal B) :=
    Ideal.map_ne_bot_of_ne_bot hm0
  obtain ⟨n, hPn⟩ :=
    exists_maximalIdeal_pow_eq_of_principal B
      (IsPrincipalIdealRing.principal P)
      (Ideal.map (algebraMap A B) m) hmap0
  have hram : P.ramificationIdx A = n := by
    let _ : IsDiscreteValuationRing (Localization.AtPrime P) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B
        (IsDiscreteValuationRing.not_a_field B) (Localization.AtPrime P)
    rw [Ideal.ramificationIdx_eq m P]
    change (Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸
        Ideal.map (algebraMap A (Localization.AtPrime P)) m)).toNat = n
    have hPn' := congrArg
      (Ideal.map (algebraMap B (Localization.AtPrime P))) hPn
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq A B
      (Localization.AtPrime P), Ideal.map_pow,
      Localization.AtPrime.map_eq_maximalIdeal] at hPn'
    rw [hPn', IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
    rfl
  simpa [m, P, hram] using hPn

private theorem chapter11_residue_map_quotient_equiv
    (R k : Type*) [CommRing R] [Field k] (m : Ideal R)
    (ρ : R →+* k) (hρ : chapter11ResidueMap R k m ρ) :
    Nonempty ((R ⧸ m) ≃+* k) := by
  have hker : RingHom.ker ρ = m := by
    ext x
    rw [RingHom.mem_ker]
    exact hρ.2 x
  let e : (R ⧸ m) ≃+* k :=
    (Ideal.quotEquivOfEq hker.symm).trans
      (RingHom.quotientKerEquivOfSurjective hρ.1)
  exact ⟨e⟩

/- The determinant calculation behind the following interface is the finite
   local calculation `B / m_A B`, whose `e` successive residue layers all
   carry the same multiplication operator on `B / m_B`. -/
private theorem chapter11_trace_eq_trace_restrict_add_trace_quotient
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (W : Submodule k V) [Module.Free k W] [Module.Finite k W]
    [Module.Free k (V ⧸ W)] [Module.Finite k (V ⧸ W)]
    (f : V →ₗ[k] V) (hf : W ≤ W.comap f) :
    LinearMap.trace k V f =
      LinearMap.trace k W (f.restrict hf) +
        LinearMap.trace k (V ⧸ W) (W.mapQ W f hf) := by
  let m := Module.Free.ChooseBasisIndex k W
  let bW : Basis m k W := Module.Free.chooseBasis k W
  let n := Module.Free.ChooseBasisIndex k (V ⧸ W)
  let bQ : Basis n k (V ⧸ W) := Module.Free.chooseBasis k (V ⧸ W)
  let b := sumQuot bW bQ
  let A : Matrix m m k := LinearMap.toMatrix bW bW (f.restrict hf)
  let B : Matrix m n k := Matrix.of fun i l ↦
    ((sumQuot bW bQ).repr (f ((sumQuot bW bQ) (Sum.inr l)))) (Sum.inl i)
  let D : Matrix n n k := LinearMap.toMatrix bQ bQ (W.mapQ W f hf)
  have hmatrix : LinearMap.toMatrix b b f = Matrix.fromBlocks A B 0 D := by
    ext u v
    cases u with
    | inl i =>
      cases v with
      | inl k =>
        simp only [b, sumQuot_inl, Matrix.fromBlocks_apply₁₁, A, LinearMap.toMatrix_apply]
        apply sumQuot_repr_inl_of_mem
      | inr l =>
        simp [b, LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, B]
    | inr j =>
      cases v with
      | inl k =>
        suffices W.mkQ (f (bW k)) = 0 by simp [LinearMap.toMatrix_apply, b, this]
        rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
        exact hf (Submodule.coe_mem (bW k))
      | inr l =>
        simp only [LinearMap.toMatrix_apply, sumQuot_repr_inr,
          Matrix.fromBlocks_apply₂₂, b, D]
        rw [← sumQuot_inr bW bQ l, W.mapQ_apply]
        simp
  rw [LinearMap.trace_eq_matrix_trace k b, hmatrix]
  simp [Matrix.trace, Matrix.fromBlocks, A, D]
  rw [LinearMap.trace_eq_matrix_trace k bW,
    LinearMap.trace_eq_matrix_trace k bQ]
  rfl

private theorem chapter11_trace_chain
    {k L : Type*} [Field k] [AddCommGroup L] [Module k L]
    [FiniteDimensional k L]
    (n : ℕ)
    (V : ℕ → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, FiniteDimensional k (V i)]
    (f : ∀ i, V i →ₗ[k] V i) (g : L →ₗ[k] L)
    (W : ∀ i, i < n → Submodule k (V (i + 1)))
    (q : ∀ (i : ℕ) (hi : i < n),
      (V (i + 1) ⧸ W i hi) ≃ₗ[k] V i)
    (w : ∀ (i : ℕ) (hi : i < n), L ≃ₗ[k] W i hi)
    (hstable : ∀ (i : ℕ) (hi : i < n),
      W i hi ≤ (W i hi).comap (f (i + 1)))
    (hquot : ∀ (i : ℕ) (hi : i < n),
      (q i hi).conj ((W i hi).mapQ (W i hi) (f (i + 1)) (hstable i hi)) = f i)
    (hlayer : ∀ (i : ℕ) (hi : i < n),
      (w i hi).conj g = (f (i + 1)).restrict (hstable i hi)) :
    ∀ i, i ≤ n → LinearMap.trace k (V i) (f i) =
      LinearMap.trace k (V 0) (f 0) +
        i • LinearMap.trace k L g := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
      intro hi
      have hi' : i < n := Nat.lt_of_succ_le hi
      calc
        LinearMap.trace k (V (i + 1)) (f (i + 1)) =
            LinearMap.trace k (W i hi')
                ((f (i + 1)).restrict (hstable i hi')) +
              LinearMap.trace k (V (i + 1) ⧸ W i hi')
                ((W i hi').mapQ (W i hi') (f (i + 1)) (hstable i hi')) :=
          chapter11_trace_eq_trace_restrict_add_trace_quotient
            (W i hi') (f (i + 1)) (hstable i hi')
        _ = LinearMap.trace k L g +
              LinearMap.trace k (V i) (f i) := by
          rw [← hlayer i hi', LinearMap.trace_conj' g (w i hi'),
            ← LinearMap.trace_conj'
              ((W i hi').mapQ (W i hi') (f (i + 1)) (hstable i hi'))
              (q i hi'), hquot i hi']
        _ = LinearMap.trace k (V 0) (f 0) +
              (i + 1) • LinearMap.trace k L g := by
          rw [ih (Nat.le_trans (Nat.le_succ i) hi)]
          ring

private theorem chapter11_det_chain
    {k L : Type*} [Field k] [AddCommGroup L] [Module k L]
    [FiniteDimensional k L]
    (n : ℕ)
    (V : ℕ → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, FiniteDimensional k (V i)]
    (f : ∀ i, V i →ₗ[k] V i) (g : L →ₗ[k] L)
    (W : ∀ i, i < n → Submodule k (V (i + 1)))
    (q : ∀ (i : ℕ) (hi : i < n),
      (V (i + 1) ⧸ W i hi) ≃ₗ[k] V i)
    (w : ∀ (i : ℕ) (hi : i < n), L ≃ₗ[k] W i hi)
    (hstable : ∀ (i : ℕ) (hi : i < n),
      W i hi ≤ (W i hi).comap (f (i + 1)))
    (hquot : ∀ (i : ℕ) (hi : i < n),
      (q i hi).conj ((W i hi).mapQ (W i hi) (f (i + 1)) (hstable i hi)) = f i)
    (hlayer : ∀ (i : ℕ) (hi : i < n),
      (w i hi).conj g = (f (i + 1)).restrict (hstable i hi)) :
    ∀ i, i ≤ n → LinearMap.det (f i) =
      LinearMap.det (f 0) * LinearMap.det g ^ i := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
      intro hi
      have hi' : i < n := Nat.lt_of_succ_le hi
      have hdet := LinearMap.det_eq_det_mul_det
        (W i hi') (f (i + 1)) (hstable i hi')
      calc
        LinearMap.det (f (i + 1)) =
            LinearMap.det ((f (i + 1)).restrict (hstable i hi')) *
              LinearMap.det ((W i hi').mapQ (W i hi') (f (i + 1)) (hstable i hi')) := hdet
        _ = LinearMap.det g * LinearMap.det (f i) := by
          have hwdet :
              LinearMap.det ((f (i + 1)).restrict (hstable i hi')) =
                LinearMap.det g := by
            rw [← hlayer i hi']
            simpa only [LinearEquiv.conj_apply, LinearMap.comp_assoc] using
              (LinearMap.det_conj g (w i hi'))
          have hqdet :
              LinearMap.det ((W i hi').mapQ (W i hi') (f (i + 1)) (hstable i hi')) =
                LinearMap.det (f i) := by
            calc
              LinearMap.det ((W i hi').mapQ (W i hi') (f (i + 1)) (hstable i hi')) =
                  LinearMap.det ((q i hi').conj
                    ((W i hi').mapQ (W i hi') (f (i + 1)) (hstable i hi'))) := by
                symm
                simpa only [LinearEquiv.conj_apply, LinearMap.comp_assoc] using
                  (LinearMap.det_conj
                    ((W i hi').mapQ (W i hi') (f (i + 1)) (hstable i hi')) (q i hi'))
              _ = LinearMap.det (f i) := by rw [hquot i hi']
          rw [hwdet, hqdet]
        _ = LinearMap.det (f 0) * LinearMap.det g ^ (i + 1) := by
          rw [ih (Nat.le_trans (Nat.le_succ i) hi), pow_succ]
          ring

private theorem chapter11_norm_quotient_mk
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [Module.Free R S] [Module.Finite R S] (x : S) :
    Algebra.norm (R ⧸ IsLocalRing.maximalIdeal R)
        (Ideal.Quotient.mk
          (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) x) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (Algebra.norm R x) := by
  let ι := Module.Free.ChooseBasisIndex R S
  let b : Module.Basis ι R S := Module.Free.chooseBasis R S
  rw [Algebra.norm_eq_matrix_det b,
    Algebra.norm_eq_matrix_det (basisQuotient b), RingHom.map_det]
  congr 1
  ext i j
  simp only [Algebra.leftMulMatrix_apply, Algebra.coe_lmul_eq_mul, LinearMap.toMatrix_apply,
    basisQuotient_apply, LinearMap.mul_apply',
    RingHom.mapMatrix_apply, Matrix.map_apply, ← map_mul,
    basisQuotient_repr]

private def chapter11_ringEquiv_toLinearEquiv
    {k R S : Type*} [CommRing R] [CommRing S] [Field k]
    [Algebra k R] [Algebra k S]
    (e : R ≃+* S)
    (he : ∀ c : k, e (algebraMap k R c) = algebraMap k S c) :
    R ≃ₗ[k] S :=
  { e.toAddEquiv with
    map_smul' := by
      intro c x
      simp only [Algebra.smul_def, RingHom.id_apply]
      calc
        e.toFun (algebraMap k R c * x) =
            e.toFun (algebraMap k R c) * e.toFun x := e.map_mul _ _
        _ = algebraMap k S c * e.toFun x :=
          congrArg (fun z => z * e.toFun x) (he c) }

private theorem chapter11_quotient_scalar_tower
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (m : Ideal A) (I : Ideal B)
    (h : m ≤ Ideal.comap (algebraMap A B) I)
    [Field (A ⧸ m)] :
    letI : Algebra (A ⧸ m) (B ⧸ I) :=
      Ideal.Quotient.algebraQuotientOfLEComap h
    IsScalarTower A (A ⧸ m) (B ⧸ I) := by
  let : Algebra (A ⧸ m) (B ⧸ I) :=
    Ideal.Quotient.algebraQuotientOfLEComap h
  apply IsScalarTower.of_algebraMap_eq'
  ext a
  change Ideal.Quotient.mk I (algebraMap A B a) =
    Ideal.Quotient.mk I (algebraMap A B a)
  rfl

theorem chapter11_finite_dvr_residue_trace_and_norm
    (A B k l : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsIntegrallyClosed A]
    [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [IsDiscreteValuationRing B] [Algebra A B]
    [Algebra.IsIntegral A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [Module.Free A B]
    [Field k] [Field l] [Algebra k l] [FiniteDimensional k l]
    (redA : A →+* k) (redB : B →+* l)
    (hredA : chapter11ResidueMap A k (IsLocalRing.maximalIdeal A) redA)
    (hredB : chapter11ResidueMap B l (IsLocalRing.maximalIdeal B) redB)
    (hcompat : ∀ a : A,
      redB (algebraMap A B a) = algebraMap k l (redA a))
    (e : ℕ) (t n : B)
    (he : e = (IsLocalRing.maximalIdeal B).ramificationIdx A) :
    chapter11DvrResidueTraceNormStatement A B k l redA redB e t n := by
  let m : Ideal A := IsLocalRing.maximalIdeal A
  let P : Ideal B := IsLocalRing.maximalIdeal B
  let e0 : ℕ := P.ramificationIdx A
  have hm0 : m ≠ (⊥ : Ideal A) := IsDiscreteValuationRing.not_a_field A
  have hP0 : P ≠ (⊥ : Ideal B) := IsDiscreteValuationRing.not_a_field B
  have he0pos : 0 < e0 := by
    dsimp [e0]
    exact Ideal.ramificationIdx_pos P A
  have hfactor : Ideal.map (algebraMap A B) m = P ^ e0 := by
    dsimp [m, P, e0]
    exact chapter11_dvr_maximalIdeal_map_eq_pow_ramificationIdx A B
  have hmapPower : ∀ i : ℕ,
      m ≤ Ideal.comap (algebraMap A B) (P ^ min i e0) := by
    intro i
    rw [← Ideal.map_le_iff_le_comap, hfactor]
    exact Ideal.pow_le_pow_right (I := P) (Nat.min_le_right i e0)
  have hmapL : m ≤ Ideal.comap (algebraMap A B) P := by
    rw [← Ideal.map_le_iff_le_comap, hfactor]
    exact Ideal.pow_le_self he0pos.ne'
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  let V : ℕ → Type _ := fun i => B ⧸ P ^ min i e0
  let : ∀ i : ℕ, Algebra (A ⧸ m) (V i) := fun i =>
    Ideal.Quotient.algebraQuotientOfLEComap (hmapPower i)
  let : ∀ i : ℕ, IsScalarTower A (A ⧸ m) (V i) := fun i =>
    chapter11_quotient_scalar_tower A B m (P ^ min i e0) (hmapPower i)
  have hVFiniteA : ∀ i : ℕ, Module.Finite A (V i) := by
    intro i
    dsimp [V]
    exact Module.Finite.quotient A _
  have hVFinite : ∀ i : ℕ, Module.Finite (A ⧸ m) (V i) := by
    intro i
    exact Module.Finite.of_restrictScalars_finite A (A ⧸ m) (V i)
  let L : Type _ := B ⧸ P
  let : Algebra (A ⧸ m) L :=
    Ideal.Quotient.algebraQuotientOfLEComap hmapL
  let : IsScalarTower A (A ⧸ m) L :=
    chapter11_quotient_scalar_tower A B m P hmapL
  have hLFiniteA : Module.Finite A L := by
    dsimp [L]
    exact Module.Finite.quotient A _
  let W : ∀ i : ℕ, i < e0 → Submodule (A ⧸ m) (V (i + 1)) :=
    fun i hi => (Ideal.map
      (Ideal.Quotient.mk (P ^ min (i + 1) e0)) (P ^ min i e0)).restrictScalars (A ⧸ m)
  have hqexist : ∀ (i : ℕ) (hi : i < e0), ∃ qi :
      (V (i + 1) ⧸ W i hi) ≃ₗ[A ⧸ m] V i,
      ∀ x : B, qi (Submodule.Quotient.mk
        (Ideal.Quotient.mk (P ^ min (i + 1) e0) x)) =
        Ideal.Quotient.mk (P ^ min i e0) x := by
    intro i hi
    have hpowexp : min i e0 ≤ min (i + 1) e0 :=
      min_le_min (Nat.le_succ i) le_rfl
    have hpow : P ^ min (i + 1) e0 ≤ P ^ min i e0 :=
      Ideal.pow_le_pow_right hpowexp
    let er := DoubleQuot.quotQuotEquivQuotOfLE hpow
    let el := Submodule.Quotient.restrictScalarsEquiv (A ⧸ m)
      (Ideal.map (Ideal.Quotient.mk (P ^ min (i + 1) e0))
        (P ^ min i e0))
    have hel : ∀ c : A ⧸ m, er (algebraMap (A ⧸ m) _ c) =
        algebraMap (A ⧸ m) _ c := by
      rintro ⟨a⟩
      rfl
    let qi := el.trans (chapter11_ringEquiv_toLinearEquiv er hel)
    refine ⟨qi, ?_⟩
    intro x
    simpa [qi, el, er, W, chapter11_ringEquiv_toLinearEquiv,
      DoubleQuot.quotQuotMk] using
      (DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk
        (I := P ^ min (i + 1) e0) (J := P ^ min i e0) x
        (Ideal.pow_le_pow_right
          (min_le_min (Nat.le_succ i) le_rfl)))
  let f : ∀ i : ℕ, V i →ₗ[A ⧸ m] V i :=
    fun i => Algebra.lmul (A ⧸ m) (V i)
      (Ideal.Quotient.mk (P ^ min i e0) t)
  have hstable : ∀ (i : ℕ) (hi : i < e0),
      W i hi ≤ (W i hi).comap (f (i + 1)) := by
    intro i hi x hx
    change (Ideal.Quotient.mk (P ^ min (i + 1) e0) t) * x ∈
      Ideal.map (Ideal.Quotient.mk (P ^ min (i + 1) e0))
        (P ^ min i e0)
    exact (Ideal.map (Ideal.Quotient.mk (P ^ min (i + 1) e0))
      (P ^ min i e0)).mul_mem_left _ hx
  have hqmk : ∀ (i : ℕ) (hi : i < e0) (x : B),
      (Classical.choose (hqexist i hi)) (Submodule.Quotient.mk
        (Ideal.Quotient.mk (P ^ min (i + 1) e0) x)) =
      Ideal.Quotient.mk (P ^ min i e0) x := by
    intro i hi x
    exact Classical.choose_spec (hqexist i hi) x
  have hquot : ∀ (i : ℕ) (hi : i < e0),
      (Classical.choose (hqexist i hi)).conj
        ((W i hi).mapQ (W i hi) (f (i + 1)) (hstable i hi)) =
        f i := by
    intro i hi
    generalize hqi : Classical.choose (hqexist i hi) = qi
    have hqmk' : ∀ x : B, qi (Submodule.Quotient.mk
        (Ideal.Quotient.mk (P ^ min (i + 1) e0) x)) =
        Ideal.Quotient.mk (P ^ min i e0) x := by
      intro x
      rw [← hqi]
      exact Classical.choose_spec (hqexist i hi) x
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hqsymm :
        qi.symm (Ideal.Quotient.mk (P ^ min i e0) x) =
          Submodule.Quotient.mk
            (Ideal.Quotient.mk (P ^ min (i + 1) e0) x) := by
      have h := congrArg qi.symm (hqmk' x)
      simpa only [LinearEquiv.symm_apply_apply] using h.symm
    calc
      (qi.conj
          ((W i hi).mapQ (W i hi) (f (i + 1)) (hstable i hi)))
          (Ideal.Quotient.mk (P ^ min i e0) x) =
        qi
          ((W i hi).mapQ (W i hi) (f (i + 1)) (hstable i hi)
            (qi.symm (Ideal.Quotient.mk (P ^ min i e0) x))) :=
        LinearEquiv.conj_apply_apply _ _ _
      _ = qi
          ((W i hi).mapQ (W i hi) (f (i + 1)) (hstable i hi)
            (Submodule.Quotient.mk
              (Ideal.Quotient.mk (P ^ min (i + 1) e0) x))) := by
        rw [hqsymm]
      _ = qi
          (Submodule.Quotient.mk
            ((Ideal.Quotient.mk (P ^ min (i + 1) e0) t) *
              (Ideal.Quotient.mk (P ^ min (i + 1) e0) x))) := by
        rw [(W i hi).mapQ_apply]
        simp only [f, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply_apply]
      _ = Ideal.Quotient.mk (P ^ min i e0) (t * x) := by
        exact hqmk' (t * x)
      _ = (f i) (Ideal.Quotient.mk (P ^ min i e0) x) := by
        simp only [f, Algebra.coe_lmul_eq_mul]
        rfl
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hPspan : P = Ideal.span ({π} : Set B) := by
    simpa [P] using hπ.maximalIdeal_eq
  have hPpow (j : ℕ) : P ^ j = Ideal.span ({π ^ j} : Set B) := by
    rw [hPspan, Ideal.span_singleton_pow]
  have hcancel : ∀ (i : ℕ) {x : B},
      x * π ^ i ∈ P ^ (i + 1) → x ∈ P := by
    intro i x hx
    rw [hPspan]
    apply LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.chapter_uniformizer_layer_cancellation
      (A := B) π hπ i
    simpa [mul_comm] using (hPpow (i + 1)).symm ▸ hx
  have hlayerB : ∀ (i : ℕ) (hi : i < e0),
      ∃ qi : L ≃ₗ[B]
        (Ideal.map (Ideal.Quotient.mk (P ^ (i + 1))) (P ^ i)).restrictScalars B,
        ∀ x : B,
          qi (Ideal.Quotient.mk P x) =
            ⟨Ideal.Quotient.mk (P ^ (i + 1)) (π ^ i * x), by
              apply Ideal.mem_map_of_mem
              rw [hPpow i]
              simpa [mul_comm] using Ideal.mul_mem_left _ x
                (Ideal.mem_span_singleton_self (π ^ i))⟩ := by
    intro i hi
    let Wb : Submodule B (B ⧸ P ^ (i + 1)) :=
      (Ideal.map (Ideal.Quotient.mk (P ^ (i + 1))) (P ^ i)).restrictScalars B
    let F : B →ₗ[B] (B ⧸ P ^ (i + 1)) :=
      (LinearMap.mulLeft B (Ideal.Quotient.mk (P ^ (i + 1)) (π ^ i))).comp
        (Ideal.Quotient.mkₐ B (P ^ (i + 1))).toLinearMap
    have hmem : ∀ x : B, F x ∈ Wb := by
      intro x
      change Ideal.Quotient.mk (P ^ (i + 1)) (π ^ i * x) ∈ Wb
      apply Ideal.mem_map_of_mem
      rw [hPpow i]
      simpa [mul_comm] using Ideal.mul_mem_left _ x
        (Ideal.mem_span_singleton_self (π ^ i))
    let G : B →ₗ[B] Wb := F.codRestrict Wb hmem
    have hker : (P : Submodule B B) ≤ G.ker := by
      intro x hx
      apply Subtype.ext
      change Ideal.Quotient.mk (P ^ (i + 1)) (π ^ i * x) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      have hxpow : π ^ i * x ∈ P ^ (i + 1) := by
        rw [pow_succ]
        have hpi : π ^ i ∈ P ^ i := by
          rw [hPpow i]
          exact Ideal.mem_span_singleton_self _
        exact Ideal.mul_mem_mul hpi hx
      exact hxpow
    let Q : L →ₗ[B] Wb :=
      (P : Submodule B B).liftQ G hker
    have hQmk (x : B) : Q (Ideal.Quotient.mk P x) =
        ⟨Ideal.Quotient.mk (P ^ (i + 1)) (π ^ i * x), hmem x⟩ := by
      rfl
    have hQinj : Function.Injective Q := by
      intro x y hxy
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      have hxy' :
          Ideal.Quotient.mk (P ^ (i + 1)) (π ^ i * x) =
            Ideal.Quotient.mk (P ^ (i + 1)) (π ^ i * y) := by
        rw [hQmk x, hQmk y] at hxy
        exact congrArg Subtype.val hxy
      have hmem' : π ^ i * (x - y) ∈ P ^ (i + 1) := by
        have hzq :
            Ideal.Quotient.mk (P ^ (i + 1)) (π ^ i * x - π ^ i * y) = 0 := by
          rw [map_sub]
          exact sub_eq_zero.mpr hxy'
        have hz := Ideal.Quotient.eq_zero_iff_mem.mp hzq
        simpa [mul_sub] using hz
      apply (Ideal.Quotient.eq).2
      exact hcancel i (by simpa [mul_comm] using hmem')
    have hQsurj : Function.Surjective Q := by
      intro z
      have hz : (z : B ⧸ P ^ (i + 1)) ∈
          Ideal.map (Ideal.Quotient.mk (P ^ (i + 1))) (P ^ i) := z.property
      obtain ⟨y, hy, hzy⟩ :=
        (Ideal.mem_map_iff_of_surjective
          (Ideal.Quotient.mk (P ^ (i + 1)))
          Ideal.Quotient.mk_surjective).mp hz
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp ((hPpow i).symm ▸ hy)
      refine ⟨Ideal.Quotient.mk P a, ?_⟩
      calc
        Q (Ideal.Quotient.mk P a) =
            ⟨Ideal.Quotient.mk (P ^ (i + 1)) (π ^ i * a), hmem a⟩ := hQmk a
        _ = z := by
          apply Subtype.ext
          have hzy' := hzy
          rw [ha] at hzy'
          exact hzy'
    refine ⟨LinearEquiv.ofBijective Q ⟨hQinj, hQsurj⟩, ?_⟩
    intro x
    exact hQmk x
  have hlayerA : ∀ (i : ℕ) (hi : i < e0),
      ∃ qi : L ≃ₗ[A ⧸ m] W i hi,
        ∀ x : B, (qi (Ideal.Quotient.mk P x) : V (i + 1)) =
          Ideal.Quotient.mk (P ^ min (i + 1) e0) (π ^ i * x) := by
    intro i hi
    have hmin_i : min i e0 = i := Nat.min_eq_left hi.le
    have hmin_succ : min (i + 1) e0 = i + 1 :=
      Nat.min_eq_left (Nat.succ_le_of_lt hi)
    have hmap_succ : m ≤
        Ideal.comap (algebraMap A B) (P ^ (i + 1)) := by
      simpa [hmin_succ] using hmapPower (i + 1)
    let : Algebra (A ⧸ m) (B ⧸ P ^ (i + 1)) :=
      Ideal.Quotient.algebraQuotientOfLEComap hmap_succ
    let : IsScalarTower A (A ⧸ m) (B ⧸ P ^ (i + 1)) :=
      chapter11_quotient_scalar_tower A B m (P ^ (i + 1)) hmap_succ
    have hdirect : ∃ qi : L ≃ₗ[A ⧸ m]
        (Ideal.map (Ideal.Quotient.mk (P ^ (i + 1))) (P ^ i)).restrictScalars (A ⧸ m),
        ∀ x : B, (qi (Ideal.Quotient.mk P x) : B ⧸ P ^ (i + 1)) =
          Ideal.Quotient.mk (P ^ (i + 1)) (π ^ i * x) := by
      obtain ⟨qB, hqB⟩ := hlayerB i hi
      let qA0 : L →ₗ[A ⧸ m]
          (Ideal.map (Ideal.Quotient.mk (P ^ (i + 1))) (P ^ i)).restrictScalars (A ⧸ m) :=
        { toFun := fun x =>
            ⟨(qB x : B ⧸ P ^ (i + 1)), by
              have hx : (qB x : B ⧸ P ^ (i + 1)) ∈
                  Ideal.map (Ideal.Quotient.mk (P ^ (i + 1))) (P ^ i) := by
                have hx' := (qB x).property
                change (qB x : B ⧸ P ^ (i + 1)) ∈
                  Ideal.map (Ideal.Quotient.mk (P ^ (i + 1))) (P ^ i) at hx'
                exact hx'
              exact hx⟩
          map_add' := by
            intro x y
            apply Subtype.ext
            exact congrArg Subtype.val (qB.map_add x y)
          map_smul' := by
            intro c x
            obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
            obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
            apply Subtype.ext
            simp only [Submodule.coe_smul, Algebra.smul_def]
            change
              (qB ((algebraMap (A ⧸ m) L) (Ideal.Quotient.mk m a) *
                Ideal.Quotient.mk P b) : B ⧸ P ^ (i + 1)) =
                algebraMap (A ⧸ m) (B ⧸ P ^ (i + 1))
                    (Ideal.Quotient.mk m a) *
                  (qB (Ideal.Quotient.mk P b) : B ⧸ P ^ (i + 1))
            have hmapL :
                (algebraMap (A ⧸ m) L) (Ideal.Quotient.mk m a) =
                  Ideal.Quotient.mk P (algebraMap A B a) := by
              rfl
            have hmapV :
                (algebraMap (A ⧸ m) (B ⧸ P ^ (i + 1)))
                    (Ideal.Quotient.mk m a) =
                  Ideal.Quotient.mk (P ^ (i + 1)) (algebraMap A B a) := by
              rfl
            have hsource :
                (Ideal.Quotient.mk m a) • (Ideal.Quotient.mk P b) =
                  Ideal.Quotient.mk P (algebraMap A B a * b) := by
              rw [Algebra.smul_def, hmapL]
              simp
            have hqB_mul :
                (qB (Ideal.Quotient.mk P (algebraMap A B a * b)) :
                    B ⧸ P ^ (i + 1)) =
                  Ideal.Quotient.mk (P ^ (i + 1))
                    (π ^ i * (algebraMap A B a * b)) :=
              congrArg Subtype.val (hqB (algebraMap A B a * b))
            have hqB_b :
                (qB (Ideal.Quotient.mk P b) : B ⧸ P ^ (i + 1)) =
                  Ideal.Quotient.mk (P ^ (i + 1)) (π ^ i * b) :=
              congrArg Subtype.val (hqB b)
            have hprod :
                Ideal.Quotient.mk P (algebraMap A B a) * Ideal.Quotient.mk P b =
                  Ideal.Quotient.mk P (algebraMap A B a * b) := by
              rw [map_mul]
            rw [hmapL, hmapV, hprod, hqB_mul, hqB_b]
            simp [mul_comm, mul_left_comm] }
      have hqAinj : Function.Injective qA0 := by
        intro x y hxy
        apply qB.injective
        apply Subtype.ext
        exact congrArg Subtype.val hxy
      have hqAsurj : Function.Surjective qA0 := by
        intro z
        have hz : (z : B ⧸ P ^ (i + 1)) ∈
            Ideal.map (Ideal.Quotient.mk (P ^ (i + 1))) (P ^ i) := z.property
        let zB : (Ideal.map (Ideal.Quotient.mk (P ^ (i + 1))) (P ^ i)).restrictScalars B :=
          ⟨z, hz⟩
        obtain ⟨x, hx⟩ := qB.surjective zB
        refine ⟨x, ?_⟩
        apply Subtype.ext
        exact congrArg Subtype.val hx
      let qA := LinearEquiv.ofBijective qA0 ⟨hqAinj, hqAsurj⟩
      refine ⟨qA, ?_⟩
      intro x
      have h := hqB x
      change (qB (Ideal.Quotient.mk P x) : B ⧸ P ^ (i + 1)) =
        Ideal.Quotient.mk (P ^ (i + 1)) (π ^ i * x)
      exact congrArg Subtype.val h
    obtain ⟨qD, hqD⟩ := hdirect
    have hEq : P ^ (i + 1) = P ^ min (i + 1) e0 := by
      rw [hmin_succ]
    let er : (B ⧸ P ^ (i + 1)) ≃+* (B ⧸ P ^ min (i + 1) e0) :=
      Ideal.quotEquivOfEq hEq
    have her : ∀ c : A ⧸ m,
        er (algebraMap (A ⧸ m) (B ⧸ P ^ (i + 1)) c) =
          algebraMap (A ⧸ m) (B ⧸ P ^ min (i + 1) e0) c := by
      rintro ⟨a⟩
      rfl
    let erlin := chapter11_ringEquiv_toLinearEquiv er her
    have her_mk (y : B) :
        er (Ideal.Quotient.mk (P ^ (i + 1)) y) =
          Ideal.Quotient.mk (P ^ min (i + 1) e0) y := by
      rfl
    let qA0 : L →ₗ[A ⧸ m] W i hi :=
      { toFun := fun x =>
          ⟨er (qD x : B ⧸ P ^ (i + 1)), by
            have hx := (qD x).property
            change (qD x : B ⧸ P ^ (i + 1)) ∈
              Ideal.map (Ideal.Quotient.mk (P ^ (i + 1))) (P ^ i) at hx
            obtain ⟨y, hy, hxy⟩ :=
              (Ideal.mem_map_iff_of_surjective
                (Ideal.Quotient.mk (P ^ (i + 1)))
                Ideal.Quotient.mk_surjective).mp hx
            have hy' : y ∈ P ^ min i e0 := by
              simpa [hmin_i] using hy
            have hmem := Ideal.mem_map_of_mem
              (Ideal.Quotient.mk (P ^ min (i + 1) e0)) hy'
            rw [← hxy, her_mk]
            exact hmem⟩
        map_add' := by
          intro x y
          apply Subtype.ext
          change er (qD (x + y) : B ⧸ P ^ (i + 1)) =
            er (qD x : B ⧸ P ^ (i + 1)) +
              er (qD y : B ⧸ P ^ (i + 1))
          calc
            er (qD (x + y) : B ⧸ P ^ (i + 1)) =
                er ((qD x + qD y : _ ) : B ⧸ P ^ (i + 1)) := by
              exact congrArg
                (fun z : (Ideal.map (Ideal.Quotient.mk (P ^ (i + 1))) (P ^ i)).restrictScalars
                    (A ⧸ m) => er (z : B ⧸ P ^ (i + 1))) (qD.map_add x y)
            _ = er (qD x : B ⧸ P ^ (i + 1)) +
                er (qD y : B ⧸ P ^ (i + 1)) := er.map_add _ _
        map_smul' := by
          intro c x
          apply Subtype.ext
          simp only [Submodule.coe_smul]
          change er (qD (c • x) : B ⧸ P ^ (i + 1)) =
            c • er (qD x : B ⧸ P ^ (i + 1))
          calc
            er (qD (c • x) : B ⧸ P ^ (i + 1)) =
                er (c • (qD x : B ⧸ P ^ (i + 1))) := by
              congr 1
              exact congrArg Subtype.val (qD.map_smul c x)
            _ = erlin (c • (qD x : B ⧸ P ^ (i + 1))) := rfl
            _ = c • erlin (qD x : B ⧸ P ^ (i + 1)) :=
              erlin.map_smul c (qD x : B ⧸ P ^ (i + 1))
            _ = c • er (qD x : B ⧸ P ^ (i + 1)) := rfl }
    have hqAinj : Function.Injective qA0 := by
      intro x y hxy
      apply qD.injective
      apply Subtype.ext
      apply erlin.injective
      exact congrArg Subtype.val hxy
    have hqAsurj : Function.Surjective qA0 := by
      intro z
      let zD : B ⧸ P ^ (i + 1) :=
        erlin.symm (z : B ⧸ P ^ min (i + 1) e0)
      have hzD : zD ∈ Ideal.map (Ideal.Quotient.mk (P ^ (i + 1))) (P ^ i) := by
        obtain ⟨y, hy, hzy⟩ :=
          (Ideal.mem_map_iff_of_surjective
            (Ideal.Quotient.mk (P ^ min (i + 1) e0))
            Ideal.Quotient.mk_surjective).mp z.property
        have hy' : y ∈ P ^ i := by
          simpa [hmin_i] using hy
        have hmem := Ideal.mem_map_of_mem
          (Ideal.Quotient.mk (P ^ (i + 1))) hy'
        change er.symm (z : B ⧸ P ^ min (i + 1) e0) ∈
          Ideal.map (Ideal.Quotient.mk (P ^ (i + 1))) (P ^ i)
        rw [← hzy]
        change Ideal.Quotient.mk (P ^ (i + 1)) y ∈
          Ideal.map (Ideal.Quotient.mk (P ^ (i + 1))) (P ^ i)
        exact hmem
      let zD' : (Ideal.map (Ideal.Quotient.mk (P ^ (i + 1))) (P ^ i)).restrictScalars B :=
        ⟨zD, hzD⟩
      obtain ⟨x, hx⟩ := qD.surjective zD'
      refine ⟨x, ?_⟩
      apply Subtype.ext
      change erlin (qD x : B ⧸ P ^ (i + 1)) =
        (z : B ⧸ P ^ min (i + 1) e0)
      calc
        erlin (qD x : B ⧸ P ^ (i + 1)) = erlin (zD' : B ⧸ P ^ (i + 1)) := by
          rw [congrArg Subtype.val hx]
        _ = z := erlin.apply_symm_apply (z : B ⧸ P ^ min (i + 1) e0)
    let qA := LinearEquiv.ofBijective qA0 ⟨hqAinj, hqAsurj⟩
    refine ⟨qA, ?_⟩
    intro x
    change erlin (qD (Ideal.Quotient.mk P x) : B ⧸ P ^ (i + 1)) =
      Ideal.Quotient.mk (P ^ min (i + 1) e0) (π ^ i * x)
    exact calc
      erlin (qD (Ideal.Quotient.mk P x) : B ⧸ P ^ (i + 1)) =
          erlin (Ideal.Quotient.mk (P ^ (i + 1)) (π ^ i * x)) := by
            rw [hqD x]
      _ = Ideal.Quotient.mk (P ^ min (i + 1) e0) (π ^ i * x) := her_mk _
  let g : L →ₗ[A ⧸ m] L :=
    Algebra.lmul (A ⧸ m) L (Ideal.Quotient.mk P t)
  have hlayer : ∀ (i : ℕ) (hi : i < e0),
      (Classical.choose (hlayerA i hi)).conj g =
        (f (i + 1)).restrict (hstable i hi) := by
    intro i hi
    generalize hqi : Classical.choose (hlayerA i hi) = qi
    have hqmk : ∀ x : B,
        (qi (Ideal.Quotient.mk P x) : V (i + 1)) =
          Ideal.Quotient.mk (P ^ min (i + 1) e0) (π ^ i * x) := by
      intro x
      rw [← hqi]
      exact Classical.choose_spec (hlayerA i hi) x
    apply LinearMap.ext
    intro z
    obtain ⟨y, rfl⟩ := qi.surjective z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    calc
      qi.conj g (qi (Ideal.Quotient.mk P x)) =
          qi (g (Ideal.Quotient.mk P x)) :=
        by
          rw [LinearEquiv.conj_apply_apply]
          simp only [LinearEquiv.symm_apply_apply]
      _ = qi (Ideal.Quotient.mk P (t * x)) := by
        simp only [g, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply_apply]
        exact congrArg (fun z : L => qi z)
          (map_mul (Ideal.Quotient.mk P) t x).symm
      _ = (f (i + 1)).restrict (hstable i hi)
          (qi (Ideal.Quotient.mk P x)) := by
        apply Subtype.ext
        change (qi (Ideal.Quotient.mk P (t * x)) : V (i + 1)) =
          (Ideal.Quotient.mk (P ^ min (i + 1) e0) t) *
            (qi (Ideal.Quotient.mk P x) : V (i + 1))
        rw [hqmk (t * x), hqmk x]
        calc
          Ideal.Quotient.mk (P ^ min (i + 1) e0) (π ^ i * (t * x)) =
              Ideal.Quotient.mk (P ^ min (i + 1) e0) (t * (π ^ i * x)) := by
                congr 1
                ac_rfl
          _ = (Ideal.Quotient.mk (P ^ min (i + 1) e0) t) *
              Ideal.Quotient.mk (P ^ min (i + 1) e0) (π ^ i * x) := by
                rw [map_mul]
  let : ∀ i : ℕ, FiniteDimensional (A ⧸ m) (V i) := fun i => hVFinite i
  let : Module.Finite A L := hLFiniteA
  let : FiniteDimensional (A ⧸ m) L :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ m) L
  have htrace := chapter11_trace_chain e0 V f g W
    (fun i hi => Classical.choose (hqexist i hi))
    (fun i hi => Classical.choose (hlayerA i hi))
    hstable hquot hlayer e0 (le_refl e0)
  have hdet := chapter11_det_chain e0 V f g W
    (fun i hi => Classical.choose (hqexist i hi))
    (fun i hi => Classical.choose (hlayerA i hi))
    hstable hquot hlayer e0 (le_refl e0)
  have htrace0 : LinearMap.trace (A ⧸ m) (V 0) (f 0) = 0 := by
    let : Subsingleton (V 0) := by
      dsimp [V]
      rw [Nat.min_eq_left (Nat.zero_le e0), pow_zero]
      constructor
      intro x y
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      apply (Ideal.Quotient.eq).2
      simp
    have hf0 : f 0 = 0 := Subsingleton.elim _ _
    rw [hf0]
    exact LinearMap.map_zero (LinearMap.trace (A ⧸ m) (V 0))
  have hdet0 : LinearMap.det (f 0) = 1 := by
    let : Subsingleton (V 0) := by
      dsimp [V]
      rw [Nat.min_eq_left (Nat.zero_le e0), pow_zero]
      constructor
      intro x y
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      apply (Ideal.Quotient.eq).2
      simp
    exact LinearMap.det_eq_one_of_subsingleton (f 0)
  have hkerA : RingHom.ker redA = m := by
    ext a
    rw [RingHom.mem_ker]
    exact hredA.2 a
  have hkerB : RingHom.ker redB = P := by
    ext b
    rw [RingHom.mem_ker]
    exact hredB.2 b
  let eA : (A ⧸ m) ≃+* k :=
    (Ideal.quotEquivOfEq hkerA.symm).trans
      (RingHom.quotientKerEquivOfSurjective hredA.1)
  let eB : (B ⧸ P) ≃+* l :=
    (Ideal.quotEquivOfEq hkerB.symm).trans
      (RingHom.quotientKerEquivOfSurjective hredB.1)
  have heA_mk (a : A) : eA (Ideal.Quotient.mk m a) = redA a := by
    simp [eA, Ideal.quotEquivOfEq_mk,
      RingHom.quotientKerEquivOfSurjective_apply_mk]
  have heB_mk (b : B) : eB (Ideal.Quotient.mk P b) = redB b := by
    simp [eB, Ideal.quotEquivOfEq_mk,
      RingHom.quotientKerEquivOfSurjective_apply_mk]
  have hequot :
      RingHom.comp (algebraMap k l) eA =
        RingHom.comp eB (algebraMap (A ⧸ m) L) := by
    apply RingHom.ext
    intro z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [RingHom.comp_apply, RingHom.comp_apply]
    change (algebraMap k l) (eA (Ideal.Quotient.mk m a)) =
      eB (algebraMap (A ⧸ m) L (Ideal.Quotient.mk m a))
    rw [heA_mk]
    have hquotA :
        algebraMap (A ⧸ m) L (Ideal.Quotient.mk m a) =
          Ideal.Quotient.mk P (algebraMap A B a) := by
      rfl
    rw [hquotA, heB_mk]
    exact (hcompat a).symm
  have htrace_transport :
      eA (Algebra.trace (A ⧸ m) L (Ideal.Quotient.mk P t)) =
        Algebra.trace k l (redB t) := by
    have h := Algebra.trace_eq_of_equiv_equiv eA eB hequot
      (Ideal.Quotient.mk P t)
    rw [heB_mk] at h
    simpa using congrArg eA h
  have hnorm_transport :
      eA (Algebra.norm (A ⧸ m) (Ideal.Quotient.mk P n)) =
        Algebra.norm k (redB n) := by
    have h := Algebra.norm_eq_of_equiv_equiv eA eB hequot
      (Ideal.Quotient.mk P n)
    rw [heB_mk] at h
    simpa using congrArg eA h
  have htrace_chain :
      LinearMap.trace (A ⧸ m) (V e0) (f e0) =
        (e0 : A ⧸ m) * LinearMap.trace (A ⧸ m) L g := by
    calc
      LinearMap.trace (A ⧸ m) (V e0) (f e0) =
          0 + e0 • LinearMap.trace (A ⧸ m) L g := by
        have h := htrace
        rw [htrace0] at h
        exact h
      _ = (e0 : A ⧸ m) * LinearMap.trace (A ⧸ m) L g := by
        rw [zero_add, ← Nat.cast_smul_eq_nsmul (A ⧸ m), smul_eq_mul]
  have htrace_quot :=
    Algebra.trace_quotient_eq_of_isDedekindDomain B m t
  have hfactor0 :
      Ideal.map (algebraMap A B) m = P ^ min e0 e0 := by
    rw [hfactor, min_self]
  let erQuot :
      (B ⧸ Ideal.map (algebraMap A B) m) ≃+* V e0 :=
    Ideal.quotEquivOfEq hfactor0
  have herQuot_mk (x : B) :
      erQuot (Ideal.Quotient.mk (Ideal.map (algebraMap A B) m) x) =
        Ideal.Quotient.mk (P ^ min e0 e0) x := by
    rfl
  have herQuot :
      RingHom.comp (algebraMap (A ⧸ m) (V e0))
          (RingEquiv.refl (A ⧸ m)) =
        RingHom.comp erQuot
          (algebraMap (A ⧸ m) (B ⧸ Ideal.map (algebraMap A B) m)) := by
    apply RingHom.ext
    intro c
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    rfl
  have htrace_equiv :
      Algebra.trace (A ⧸ m) (B ⧸ Ideal.map (algebraMap A B) m)
          (Ideal.Quotient.mk (Ideal.map (algebraMap A B) m) t) =
        Algebra.trace (A ⧸ m) (V e0)
          (Ideal.Quotient.mk (P ^ min e0 e0) t) := by
    have h := Algebra.trace_eq_of_equiv_equiv
      (RingEquiv.refl (A ⧸ m)) erQuot herQuot
      (Ideal.Quotient.mk (Ideal.map (algebraMap A B) m) t)
    rw [herQuot_mk] at h
    simpa using h
  have htrace_quot' :
      Algebra.trace (A ⧸ m) (V e0)
          (Ideal.Quotient.mk (P ^ min e0 e0) t) =
        Ideal.Quotient.mk m (Algebra.intTrace A B t) :=
    htrace_equiv.symm.trans htrace_quot
  have htrace_e0 :
      Algebra.trace (A ⧸ m) (V e0)
          (Ideal.Quotient.mk (P ^ min e0 e0) t) =
        (e0 : A ⧸ m) *
          Algebra.trace (A ⧸ m) L (Ideal.Quotient.mk P t) := by
    rw [Algebra.trace_apply, Algebra.trace_apply]
    simpa [f, V, g] using htrace_chain
  let fn : ∀ i : ℕ, V i →ₗ[A ⧸ m] V i :=
    fun i => Algebra.lmul (A ⧸ m) (V i)
      (Ideal.Quotient.mk (P ^ min i e0) n)
  let gn : L →ₗ[A ⧸ m] L :=
    Algebra.lmul (A ⧸ m) L (Ideal.Quotient.mk P n)
  have hstable_n : ∀ (i : ℕ) (hi : i < e0),
      W i hi ≤ (W i hi).comap (fn (i + 1)) := by
    intro i hi x hx
    change (Ideal.Quotient.mk (P ^ min (i + 1) e0) n) * x ∈
      Ideal.map (Ideal.Quotient.mk (P ^ min (i + 1) e0))
        (P ^ min i e0)
    exact (Ideal.map (Ideal.Quotient.mk (P ^ min (i + 1) e0))
      (P ^ min i e0)).mul_mem_left _ hx
  have hquot_n : ∀ (i : ℕ) (hi : i < e0),
      (Classical.choose (hqexist i hi)).conj
        ((W i hi).mapQ (W i hi) (fn (i + 1)) (hstable_n i hi)) =
        fn i := by
    intro i hi
    generalize hqi : Classical.choose (hqexist i hi) = qi
    have hqmk' : ∀ x : B, qi (Submodule.Quotient.mk
        (Ideal.Quotient.mk (P ^ min (i + 1) e0) x)) =
        Ideal.Quotient.mk (P ^ min i e0) x := by
      intro x
      rw [← hqi]
      exact Classical.choose_spec (hqexist i hi) x
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hqsymm :
        qi.symm (Ideal.Quotient.mk (P ^ min i e0) x) =
          Submodule.Quotient.mk
            (Ideal.Quotient.mk (P ^ min (i + 1) e0) x) := by
      have h := congrArg qi.symm (hqmk' x)
      simpa only [LinearEquiv.symm_apply_apply] using h.symm
    calc
      (qi.conj
          ((W i hi).mapQ (W i hi) (fn (i + 1)) (hstable_n i hi)))
          (Ideal.Quotient.mk (P ^ min i e0) x) =
        qi
          ((W i hi).mapQ (W i hi) (fn (i + 1)) (hstable_n i hi)
            (qi.symm (Ideal.Quotient.mk (P ^ min i e0) x))) :=
        LinearEquiv.conj_apply_apply _ _ _
      _ = qi
          ((W i hi).mapQ (W i hi) (fn (i + 1)) (hstable_n i hi)
            (Submodule.Quotient.mk
              (Ideal.Quotient.mk (P ^ min (i + 1) e0) x))) := by
        rw [hqsymm]
      _ = qi
          (Submodule.Quotient.mk
            ((Ideal.Quotient.mk (P ^ min (i + 1) e0) n) *
              (Ideal.Quotient.mk (P ^ min (i + 1) e0) x))) := by
        rw [(W i hi).mapQ_apply]
        simp only [fn, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply_apply]
      _ = Ideal.Quotient.mk (P ^ min i e0) (n * x) := by
        exact hqmk' (n * x)
      _ = (fn i) (Ideal.Quotient.mk (P ^ min i e0) x) := by
        simp only [fn, Algebra.coe_lmul_eq_mul]
        rfl
  have hlayer_n : ∀ (i : ℕ) (hi : i < e0),
      (Classical.choose (hlayerA i hi)).conj gn =
        (fn (i + 1)).restrict (hstable_n i hi) := by
    intro i hi
    generalize hqi : Classical.choose (hlayerA i hi) = qi
    have hqmk' : ∀ x : B,
        (qi (Ideal.Quotient.mk P x) : V (i + 1)) =
          Ideal.Quotient.mk (P ^ min (i + 1) e0) (π ^ i * x) := by
      intro x
      rw [← hqi]
      exact Classical.choose_spec (hlayerA i hi) x
    apply LinearMap.ext
    intro z
    obtain ⟨y, rfl⟩ := qi.surjective z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    calc
      qi.conj gn (qi (Ideal.Quotient.mk P x)) =
          qi (gn (Ideal.Quotient.mk P x)) := by
        rw [LinearEquiv.conj_apply_apply]
        simp only [LinearEquiv.symm_apply_apply]
      _ = qi (Ideal.Quotient.mk P (n * x)) := by
        simp only [gn, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply_apply]
        exact congrArg (fun z : L => qi z)
          (map_mul (Ideal.Quotient.mk P) n x).symm
      _ = (fn (i + 1)).restrict (hstable_n i hi)
          (qi (Ideal.Quotient.mk P x)) := by
        apply Subtype.ext
        change (qi (Ideal.Quotient.mk P (n * x)) : V (i + 1)) =
          (Ideal.Quotient.mk (P ^ min (i + 1) e0) n) *
            (qi (Ideal.Quotient.mk P x) : V (i + 1))
        rw [hqmk' (n * x), hqmk' x]
        calc
          Ideal.Quotient.mk (P ^ min (i + 1) e0) (π ^ i * (n * x)) =
              Ideal.Quotient.mk (P ^ min (i + 1) e0) (n * (π ^ i * x)) := by
                congr 1
                ac_rfl
          _ = (Ideal.Quotient.mk (P ^ min (i + 1) e0) n) *
              Ideal.Quotient.mk (P ^ min (i + 1) e0) (π ^ i * x) := by
                rw [map_mul]
  have hdet_n := chapter11_det_chain e0 V fn gn W
    (fun i hi => Classical.choose (hqexist i hi))
    (fun i hi => Classical.choose (hlayerA i hi))
    hstable_n hquot_n hlayer_n e0 (le_refl e0)
  have hdet0_n : LinearMap.det (fn 0) = 1 := by
    let : Subsingleton (V 0) := by
      dsimp [V]
      rw [Nat.min_eq_left (Nat.zero_le e0), pow_zero]
      constructor
      intro x y
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      apply (Ideal.Quotient.eq).2
      simp
    exact LinearMap.det_eq_one_of_subsingleton (fn 0)
  have hnorm_chain :
      Algebra.norm (A ⧸ m) (Ideal.Quotient.mk (P ^ min e0 e0) n) =
        Algebra.norm (A ⧸ m) (Ideal.Quotient.mk P n) ^ e0 := by
    have h := hdet_n
    rw [hdet0_n, one_mul] at h
    simpa [Algebra.norm_apply, fn, V, gn] using h
  have hnorm_quot := chapter11_norm_quotient_mk A B n
  have hnorm_equiv :
      Algebra.norm (A ⧸ m)
          (Ideal.Quotient.mk (Ideal.map (algebraMap A B) m) n) =
        Algebra.norm (A ⧸ m) (Ideal.Quotient.mk (P ^ min e0 e0) n) := by
    have h := Algebra.norm_eq_of_equiv_equiv
      (RingEquiv.refl (A ⧸ m)) erQuot herQuot
      (Ideal.Quotient.mk (Ideal.map (algebraMap A B) m) n)
    rw [herQuot_mk] at h
    simpa using h
  have hnorm_quot' :
      Algebra.norm (A ⧸ m) (Ideal.Quotient.mk (P ^ min e0 e0) n) =
        Ideal.Quotient.mk m (Algebra.norm A n) :=
    hnorm_equiv.symm.trans hnorm_quot
  have htrace_res :
      eA (Ideal.Quotient.mk m (Algebra.intTrace A B t)) =
        (e0 : k) * Algebra.trace k l (redB t) := by
    calc
      eA (Ideal.Quotient.mk m (Algebra.intTrace A B t)) =
          eA (Algebra.trace (A ⧸ m) (V e0)
            (Ideal.Quotient.mk (P ^ min e0 e0) t)) := by
        exact congrArg eA htrace_quot'.symm
      _ = eA ((e0 : A ⧸ m) *
          Algebra.trace (A ⧸ m) L (Ideal.Quotient.mk P t)) := by
        rw [htrace_e0]
      _ = (e0 : k) *
          eA (Algebra.trace (A ⧸ m) L (Ideal.Quotient.mk P t)) := by
        rw [map_mul, map_natCast]
      _ = (e0 : k) * Algebra.trace k l (redB t) := by
        rw [htrace_transport]
  have hnorm_res :
      eA (Ideal.Quotient.mk m (Algebra.norm A n)) =
        Algebra.norm k (redB n) ^ e0 := by
    calc
      eA (Ideal.Quotient.mk m (Algebra.norm A n)) =
          eA (Algebra.norm (A ⧸ m) (Ideal.Quotient.mk (P ^ min e0 e0) n)) := by
        exact congrArg eA hnorm_quot'.symm
      _ = eA (Algebra.norm (A ⧸ m) (Ideal.Quotient.mk P n) ^ e0) := by
        rw [hnorm_chain]
      _ = eA (Algebra.norm (A ⧸ m) (Ideal.Quotient.mk P n)) ^ e0 := by
        rw [map_pow]
      _ = Algebra.norm k (redB n) ^ e0 := by
        rw [hnorm_transport]
  have htrace_res' :
      redA (Algebra.intTrace A B t) =
        (e0 : k) * Algebra.trace k l (redB t) := by
    calc
      redA (Algebra.intTrace A B t) =
          eA (Ideal.Quotient.mk m (Algebra.intTrace A B t)) :=
        (heA_mk (Algebra.intTrace A B t)).symm
      _ = (e0 : k) * Algebra.trace k l (redB t) := htrace_res
  have hintNorm : Algebra.intNorm A B n = Algebra.norm A n := by
    rw [Algebra.intNorm_eq_norm]
  have hnorm_res' :
      redA (Algebra.intNorm A B n) =
        Algebra.norm k (redB n) ^ e0 := by
    rw [hintNorm]
    calc
      redA (Algebra.norm A n) =
          eA (Ideal.Quotient.mk m (Algebra.norm A n)) :=
        (heA_mk (Algebra.norm A n)).symm
      _ = Algebra.norm k (redB n) ^ e0 := hnorm_res
  change redA (Algebra.intTrace A B t) =
      (e : k) * Algebra.trace k l (redB t) ∧
    redA (Algebra.intNorm A B n) = Algebra.norm k (redB n) ^ e
  refine ⟨?_, ?_⟩
  · simpa [he, e0, P] using htrace_res'
  · simpa [he, e0, P] using hnorm_res'

/-- The residue field attached to an additive valuation. -/
abbrev chapter11AdditiveResidueField {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) :=
  IsLocalRing.ResidueField v.toValuation.valuationSubring

/-- The actual residue degree of an additive valuation extension. -/
noncomputable def chapter11AdditiveResidueDegree
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AddValuation K (WithTop ℤ)) (w : AddValuation L (WithTop ℤ))
    (h : v.IsEquiv (AddValuation.comap (algebraMap K L) w)) : ℕ := by
  letI : Valuation.HasExtension v.toValuation w.toValuation := ⟨h⟩
  exact Module.finrank (chapter11AdditiveResidueField v)
    (chapter11AdditiveResidueField w)

/-- A valuation with value group `ℤ` is normalized when it attains value one. -/
def chapter11AdditiveValuationNormalized
    {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ)) : Prop :=
  ∃ x : K, v x = (1 : WithTop ℤ)

/-- Finiteness of the residue-field extension attached to an equivalent branch. -/
def chapter11ResidueExtensionFinite
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : AddValuation K (WithTop ℤ)) (w : AddValuation L (WithTop ℤ))
    (h : v.IsEquiv (AddValuation.comap (algebraMap K L) w)) : Prop := by
  letI : Valuation.HasExtension v.toValuation w.toValuation := ⟨h⟩
  exact FiniteDimensional (chapter11AdditiveResidueField v)
    (chapter11AdditiveResidueField w)

/-- A finite indexed family containing every normalized extension of `v`
exactly once, up to equivalence. -/
def chapter11CompleteNormalizedBranchFamily
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    {ι : Type*} [Fintype ι]
  (v : AddValuation K (WithTop ℤ))
  (w : ι → AddValuation L (WithTop ℤ)) : Prop :=
  (∀ i, v.IsEquiv (AddValuation.comap (algebraMap K L) (w i))) ∧
    (∀ i, ∃ e : ℕ, 0 < e ∧
      (∀ z : K, w i (algebraMap K L z) = (e : WithTop ℤ) * v z) ∧
      chapter11AdditiveValuationNormalized (w i)) ∧
    (∀ i, ∃ h : v.IsEquiv (AddValuation.comap (algebraMap K L) (w i)),
      chapter11ResidueExtensionFinite v (w i) h) ∧
    (∀ ⦃i j⦄, (w i).IsEquiv (w j) → i = j) ∧
    ∀ w' : AddValuation L (WithTop ℤ),
      v.IsEquiv (AddValuation.comap (algebraMap K L) w') →
        ∃ i, (w i).IsEquiv w'

/-- The displayed natural numbers are the ramification scalings of the
chosen normalized branch valuations. -/
def chapter11RamificationScaling
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {ι : Type*}
    (v : AddValuation K (WithTop ℤ))
    (w : ι → AddValuation L (WithTop ℤ)) (e : ι → ℕ) : Prop :=
  ∀ i, 0 < e i ∧
    ∀ z : K, w i (algebraMap K L z) = (e i : WithTop ℤ) * v z

/-- Defectless normalized branch data for the norm formula.

The branch correspondences identify the displayed valuations with the
normalization branches.  The degree equality is not assumed as part of this
interface, since it is the fundamental equality supplied by finite
normalization.
The source formula is a statement about the finite normalization of a DVR:
the finiteness hypothesis and the correspondence of the displayed branches
with the primes/localizations of that normalization are therefore part of the
interface, rather than being left implicit in the valuation family.
-/
def chapter11DefectlessNormBranchData
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {ι : Type*} [Fintype ι]
    (v : AddValuation K (WithTop ℤ))
    (w : ι → AddValuation L (WithTop ℤ)) : Prop :=
  chapter11AdditiveValuationNormalized v ∧
    IsDiscreteValuationRing v.valuationSubring ∧
    chapter11NormalizationFinite v.valuationSubring L ∧
    (∀ i, ∃ P : Ideal (chapter11IntegralClosure v.valuationSubring L),
      chapter11Branch v.valuationSubring (chapter11IntegralClosure v.valuationSubring L)
        (IsLocalRing.maximalIdeal v.valuationSubring) P ∧
        Nonempty (Chapter11ValuationBranchCorrespondence
          (chapter11IntegralClosure v.valuationSubring L) L P (w i).toValuation)) ∧
    (∀ P : Ideal (chapter11IntegralClosure v.valuationSubring L),
      chapter11Branch v.valuationSubring (chapter11IntegralClosure v.valuationSubring L)
        (IsLocalRing.maximalIdeal v.valuationSubring) P →
        ∃ i, Nonempty (Chapter11ValuationBranchCorrespondence
          (chapter11IntegralClosure v.valuationSubring L) L P (w i).toValuation))

/-! The next two lemmas make the normalization step in the norm proof explicit.
The first identifies an exactly normalized additive valuation with the DVR
order on nonzero elements.  The second transports that order through a branch
correspondence and its localization equivalence. -/

theorem chapter11_normalized_dvr_ord
    (A K : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (v : AddValuation K (WithTop ℤ))
    (hsub : v.toValuation.valuationSubring.toSubring =
      Subring.map (algebraMap A K) (⊤ : Subring A))
    (hnorm : ∃ z : K, v z = (1 : WithTop ℤ))
    (a : A) (ha0 : a ≠ 0) :
    v (algebraMap A K a) = (Ring.ord A a).toNat := by
  classical
  have hmem (b : A) : algebraMap A K b ∈ v.toValuation.valuationSubring := by
    change algebraMap A K b ∈ v.toValuation.valuationSubring.toSubring
    rw [hsub, Subring.mem_map]
    exact ⟨b, Subring.mem_top _, rfl⟩
  have hzero_of_unit {y : K} (hy : y ≠ 0) (hy0 : 0 ≤ v y)
      (hyi : 0 ≤ v y⁻¹) : v y = 0 := by
    have hytop : v y ≠ ⊤ := (v.ne_top_iff).2 hy
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hytop
    rw [← hn] at hy0
    rw [AddValuation.map_inv, ← hn] at hyi
    have hyn : 0 ≤ n := by exact_mod_cast hy0
    have hyin : 0 ≤ -n := by exact_mod_cast hyi
    have hn0 : n = 0 := by linarith
    rw [hn0] at hn
    simpa using hn.symm
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hunit (u : Aˣ) : v (algebraMap A K (u : A)) = 0 := by
    apply hzero_of_unit (by
      exact (map_ne_zero_iff (algebraMap A K)
        (FaithfulSMul.algebraMap_injective A K)).2 u.ne_zero)
    · exact hmem (u : A)
    · have huinv := hmem ((u⁻¹ : Aˣ) : A)
      change 0 ≤ v (algebraMap A K ((u⁻¹ : Aˣ) : A)) at huinv
      rw [show algebraMap A K ((u⁻¹ : Aˣ) : A) =
        (algebraMap A K (u : A))⁻¹ by simp] at huinv
      exact huinv
  have hpi_pos : 0 < v (algebraMap A K π) := by
    by_contra hnot
    have hpi0 : v (algebraMap A K π) = 0 :=
      le_antisymm (not_lt.mp hnot) (hmem π)
    have hinv : (algebraMap A K π)⁻¹ ∈ v.toValuation.valuationSubring := by
      change 0 ≤ v ((algebraMap A K π)⁻¹)
      rw [AddValuation.map_inv, hpi0]
      exact le_rfl
    change (algebraMap A K π)⁻¹ ∈ v.toValuation.valuationSubring.toSubring at hinv
    rw [hsub, Subring.mem_map] at hinv
    obtain ⟨b, -, hb⟩ := hinv
    have hprod : π * b = 1 := by
      apply (FaithfulSMul.algebraMap_injective A K)
      rw [map_mul, map_one, hb]
      exact mul_inv_cancel₀ (by
        exact (map_ne_zero_iff (algebraMap A K)
          (FaithfulSMul.algebraMap_injective A K)).2 hπ.ne_zero)
    exact hπ.not_isUnit (by
      rw [isUnit_iff_exists_inv]
      exact ⟨b, hprod⟩)
  obtain ⟨z, hz⟩ := hnorm
  have hzmem : z ∈ v.toValuation.valuationSubring := by
    change 0 ≤ v z
    rw [hz]
    exact zero_le_one
  change z ∈ v.toValuation.valuationSubring.toSubring at hzmem
  rw [hsub, Subring.mem_map] at hzmem
  obtain ⟨b, -, hb⟩ := hzmem
  have hb0 : b ≠ 0 := by
    intro hb0
    have hz0 : z = 0 := by simpa [hb0] using hb.symm
    have hzero : v 0 = 1 := hz0 ▸ hz
    simp at hzero
  obtain ⟨n, u, ha⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hπ
  have hpi_top : v (algebraMap A K π) ≠ ⊤ :=
    (v.ne_top_iff).2 (by
      exact (map_ne_zero_iff (algebraMap A K)
        (FaithfulSMul.algebraMap_injective A K)).2 hπ.ne_zero)
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hpi_top
  have hmpos : 0 < m := by
    have hpi_pos' : (0 : WithTop ℤ) < (m : WithTop ℤ) := by simpa [hm] using hpi_pos
    exact_mod_cast hpi_pos'
  have hnm : n * m = 1 := by
    have hv := hz
    rw [← hb, ha] at hv
    rw [map_mul, AddValuation.map_mul, map_pow, AddValuation.map_pow] at hv
    rw [hunit, ← hm] at hv
    simp at hv
    exact_mod_cast hv
  have hn1z : (n : ℤ) = 1 :=
    Int.eq_one_of_mul_eq_one_right (by exact_mod_cast (Nat.zero_le n)) hnm
  have hm1 : m = 1 :=
    Int.eq_one_of_mul_eq_one_left (by linarith [hmpos]) hnm
  have hn1 : n = 1 := by exact_mod_cast hn1z
  have hpi1 : v (algebraMap A K π) = 1 := by
    rw [← hm, hm1]
    norm_num
  obtain ⟨n, u, ha⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hπ
  calc
    v (algebraMap A K a) =
        v (algebraMap A K ((u : A) * π ^ n)) := by rw [ha]
    _ = (n : WithTop ℤ) := by
      simp only [map_mul, AddValuation.map_mul, map_pow, AddValuation.map_pow]
      rw [hunit, hpi1]
      simp
    _ = (Ring.ord A a).toNat := by
      have hord : Ring.ord A a = n := by
        rw [Ring.ord_eq_addVal]
        exact IsDiscreteValuationRing.addVal_def a u hπ n ha
      rw [hord]
      norm_num

theorem chapter11_correspondence_valuationSubring
    (B L : Type*) [CommRing B] [Field L] [Algebra B L]
    (P : Ideal B) [P.IsPrime]
    {vL : Valuation L (Multiplicative (WithTop ℤ)ᵒᵈ)}
    (c : Chapter11ValuationBranchCorrespondence B L P vL) :
    vL.valuationSubring.toSubring =
      Subring.map (vL.valuationSubring.subtype.comp c.localizationEquiv.toRingHom)
        (⊤ : Subring (Localization.AtPrime P)) := by
  apply Subring.ext
  intro z
  constructor
  · intro hz
    rcases c.localizationEquiv.surjective ⟨z, hz⟩ with ⟨s, hs⟩
    refine ⟨s, Subring.mem_top _, ?_⟩
    simpa using congrArg (fun t : vL.valuationSubring => (t : L)) hs
  · intro hz
    rcases hz with ⟨s, -, hs⟩
    change ((c.localizationEquiv s : vL.valuationSubring) : L) = z at hs
    change z ∈ vL.valuationSubring
    rw [← hs]
    exact (c.localizationEquiv s).property

theorem chapter11_local_length_eq_emultiplicity
    (B : Type*) [CommRing B] [IsDedekindDomain B]
    (P : Ideal B) [P.IsPrime] [P.IsMaximal] (hP0 : P ≠ (⊥ : Ideal B))
    (b : B) (hb0 : b ≠ 0) :
    chapter11LocalLengthValue B P b =
      (emultiplicity P (Ideal.span ({b} : Set B))).toNat := by
  let S := Localization.AtPrime P
  let : IsDiscreteValuationRing S :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hP0 S
  have hbS : algebraMap B S b ≠ 0 := by
    exact (map_ne_zero_iff (algebraMap B S)
      (IsLocalization.injective S P.primeCompl_le_nonZeroDivisors)).2 hb0
  have hmax0 : IsLocalRing.maximalIdeal S ≠ (⊥ : Ideal S) := by
    rw [← (Localization.AtPrime.map_eq_maximalIdeal (I := P))]
    exact (Ideal.map_eq_bot_iff_of_injective
      (IsLocalization.injective S P.primeCompl_le_nonZeroDivisors)).not.mpr hP0
  have hlen : (Module.length S
      (S ⧸ Ideal.span {algebraMap B S b})).toNat =
      (Ring.ord S (algebraMap B S b)).toNat := by
    rfl
  have hadd : Ring.ord S (algebraMap B S b) =
      emultiplicity (IsLocalRing.maximalIdeal S)
        (Ideal.span ({algebraMap B S b} : Set S)) := by
    rw [Ring.ord_eq_addVal]
    have hp : Prime (Classical.choose (IsDiscreteValuationRing.exists_prime S)) :=
      Classical.choose_spec (IsDiscreteValuationRing.exists_prime S)
    rw [IsDiscreteValuationRing.addVal, multiplicity_addValuation_apply]
    rw [← Ideal.emultiplicity_eq_emultiplicity_span]
    simp only [hp.irreducible.maximalIdeal_eq]
  have hram : Ideal.ramificationIdx' P (IsLocalRing.maximalIdeal S) = 1 := by
    apply Ideal.ramificationIdx'_eq_one_of_map_localization
      (p := P) (P := IsLocalRing.maximalIdeal S)
    · rw [← (Localization.AtPrime.map_eq_maximalIdeal (I := P))]
    · exact hmax0
    · exact (IsLocalRing.maximalIdeal S).primeCompl_le_nonZeroDivisors
    · rw [IsScalarTower.algebraMap_eq B S
          (Localization.AtPrime (IsLocalRing.maximalIdeal S)),
        ← Ideal.map_map, ← (Localization.AtPrime.map_eq_maximalIdeal
          (I := IsLocalRing.maximalIdeal S)), Localization.AtPrime.map_eq_maximalIdeal]
  have hmult := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul
    (I := Ideal.span ({b} : Set B)) (h := by simp [hb0])
    (Ideal.prime_of_isPrime hP0 (inferInstance : P.IsPrime)).irreducible
    (Ideal.prime_of_isPrime hmax0 (IsLocalRing.maximalIdeal.isMaximal S).isPrime).irreducible
    hmax0
  rw [Ideal.map_span] at hmult
  have hmult' : emultiplicity (IsLocalRing.maximalIdeal S)
      (Ideal.span ({algebraMap B S b} : Set S)) =
      (emultiplicity P (Ideal.span ({b} : Set B))) := by
    simpa [hram] using hmult
  have hmultord : Ring.ord S (algebraMap B S b) =
      emultiplicity P (Ideal.span ({b} : Set B)) := hadd.trans hmult'
  change (Module.length S
      (S ⧸ Ideal.span {algebraMap B S b})).toNat = _
  rw [hlen]
  exact congrArg ENat.toNat hmultord

/-! The relative norm order is obtained by factoring a principal ideal and
grouping its normalized factors by the prime below them. -/
open UniqueFactorizationMonoid

theorem chapter11_norm_integral_emultiplicity
    (A B K : Type*) [CommRing A] [IsDedekindDomain A]
    [CommRing B] [IsDedekindDomain B]
    [Field K] [Algebra A K] [IsFractionRing A K] [PerfectField K]
    [Algebra A B] [Module.Finite A B] [Module.Free A B]
    [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (m : Ideal A) [m.IsMaximal] (hm0 : m ≠ (⊥ : Ideal A))
    (y : B) (hy : y ≠ 0) :
    emultiplicity m
        (Ideal.span ({Algebra.intNorm A B y} : Set A)) =
      ∑ q : m.primesOver B,
        (q.1.inertiaDeg A : ℕ∞) *
          emultiplicity q.1 (Ideal.span ({y} : Set B)) := by
  classical
  let : PerfectField (FractionRing A) :=
    PerfectField.of_ringEquiv (FractionRing.algEquiv A K).symm.toRingEquiv
  let F := normalizedFactors (Ideal.span ({y} : Set B))
  have hI0 : Ideal.span ({y} : Set B) ≠ (⊥ : Ideal B) := by
    simp [hy]
  have hrel : Ideal.relNorm A (Ideal.span ({y} : Set B)) =
      Ideal.span ({Algebra.intNorm A B y} : Set A) := by
    exact Ideal.relNorm_singleton A y
  have hmprime : Prime m := Ideal.prime_of_isPrime hm0
    (inferInstance : m.IsMaximal).isPrime
  have hsum_map : ∀ (s : Multiset (Ideal B)),
        emultiplicity m (Multiset.map (Ideal.relNorm A) s).prod =
          (Multiset.map (fun Q => emultiplicity m (Ideal.relNorm A Q)) s).sum := by
    intro s
    induction s using Multiset.induction_on with
    | empty =>
      change emultiplicity m (1 : Ideal A) = 0
      apply emultiplicity_eq_zero.mpr
      intro hdiv
      apply (inferInstance : m.IsMaximal).ne_top
      exact top_unique (by simpa [Ideal.one_eq_top] using (Ideal.dvd_iff_le).mp hdiv)
    | @cons Q s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
      rw [emultiplicity_mul hmprime, ih]
  have hsum_rel :
      emultiplicity m (Ideal.relNorm A (Ideal.span ({y} : Set B))) =
        ∑ Q ∈ F.toFinset,
          F.count Q • emultiplicity m (Ideal.relNorm A Q) := by
    rw [← Ideal.prod_normalizedFactors_eq_self hI0, map_multiset_prod]
    rw [hsum_map F, Finset.sum_multiset_map_count]
  have hfactor : ∀ Q : Ideal B, Q ∈ F →
      emultiplicity m (Ideal.relNorm A Q) =
        if hQ : Q.LiesOver m then (Q.inertiaDeg A : ℕ∞) else 0 := by
    intro Q hQ
    have hQ0 : Q ≠ (⊥ : Ideal B) := ne_zero_of_mem_normalizedFactors hQ
    have hQprime : Q.IsPrime :=
      Ideal.isPrime_of_prime (prime_of_normalized_factor Q hQ)
    have hQmax : Q.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hQ0 hQprime
    by_cases hQo : Q.LiesOver m
    · let : Q.LiesOver m := hQo
      simp only [dif_pos hQo]
      rw [Ideal.relNorm_eq_pow_of_isMaximal Q m]
      have hmp : Prime m := Ideal.prime_of_isPrime hm0
        (inferInstance : m.IsMaximal).isPrime
      exact emultiplicity_pow_self_of_prime hmp (Q.inertiaDeg A)
    · simp only [dif_neg hQo]
      have hundermax : (Ideal.comap (algebraMap A B) Q).IsMaximal :=
        Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q
      let : (Ideal.comap (algebraMap A B) Q).IsMaximal := hundermax
      let : Q.LiesOver (Ideal.comap (algebraMap A B) Q) :=
        Ideal.over_under (A := A) (P := Q)
      rw [Ideal.relNorm_eq_pow_of_isMaximal Q (Ideal.comap (algebraMap A B) Q)]
      apply emultiplicity_eq_zero.mpr
      intro hdiv
      have hne : (Ideal.comap (algebraMap A B) Q) ≠ m := by
        intro heq
        exact hQo ⟨heq.symm⟩
      have htop : m ⊔ (Ideal.comap (algebraMap A B) Q) = ⊤ :=
        (inferInstance : m.IsMaximal).coprime_of_ne
          (inferInstance : (Ideal.comap (algebraMap A B) Q).IsMaximal) hne.symm
      have htop_pow := Ideal.sup_pow_eq_top' (n := Q.inertiaDeg A) htop
      apply (inferInstance : m.IsMaximal).ne_top
      rw [← htop_pow]
      exact (sup_eq_left.mpr ((Ideal.dvd_iff_le).mp hdiv)).symm
  rw [hrel] at hsum_rel
  let T : Finset (Ideal B) := F.toFinset.filter (fun Q => Q.LiesOver m)
  have hsum_factor :
      emultiplicity m (Ideal.span ({Algebra.intNorm A B y} : Set A)) =
        ∑ Q ∈ T, F.count Q • (Q.inertiaDeg A : ℕ∞) := by
    calc
      emultiplicity m (Ideal.span ({Algebra.intNorm A B y} : Set A)) =
          ∑ Q ∈ F.toFinset,
            F.count Q • emultiplicity m (Ideal.relNorm A Q) := hsum_rel
      _ = ∑ Q ∈ F.toFinset,
            F.count Q • (if hQ : Q.LiesOver m then
              (Q.inertiaDeg A : ℕ∞) else 0) := by
        apply Finset.sum_congr rfl
        intro Q hQ
        rw [hfactor Q (Multiset.mem_toFinset.mp hQ)]
      _ = ∑ Q ∈ T, F.count Q • (Q.inertiaDeg A : ℕ∞) := by
        rw [show T = F.toFinset.filter (fun Q => Q.LiesOver m) by rfl,
          Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro Q hQ
        by_cases hQo : Q.LiesOver m <;> simp [hQo]
  have hcount_q (q : m.primesOver B) :
      emultiplicity q.1 (Ideal.span ({y} : Set B)) =
        (F.count q.1 : ℕ∞) := by
    have hq0 : q.1 ≠ (⊥ : Ideal B) :=
      Ideal.ne_bot_of_mem_primesOver hm0 q.2
    have hqprime : Prime q.1 :=
      Ideal.prime_of_isPrime hq0 (Ideal.primesOver.isPrime m q)
    rw [UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors
      hqprime.irreducible hI0]
    simp [F, normalize_eq]
  let U : Finset (m.primesOver B) :=
    Finset.univ.filter (fun q => q.1 ∈ F.toFinset)
  have hsum_q_filter :
      (∑ q : m.primesOver B,
        (q.1.inertiaDeg A : ℕ∞) *
          emultiplicity q.1 (Ideal.span ({y} : Set B))) =
        ∑ q ∈ U,
          (q.1.inertiaDeg A : ℕ∞) *
            emultiplicity q.1 (Ideal.span ({y} : Set B)) := by
    rw [show U = Finset.univ.filter (fun q : m.primesOver B =>
      q.1 ∈ F.toFinset) by rfl, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hqF : q.1 ∈ F.toFinset
    · simp [hqF]
    · have hcount0 : F.count q.1 = 0 :=
        Multiset.count_eq_zero.mpr (by
          exact fun hmem => hqF (Multiset.mem_toFinset.mpr hmem))
      rw [hcount_q q, hcount0]
      simp
  have hsum_bij :
      (∑ q ∈ U,
        (q.1.inertiaDeg A : ℕ∞) *
          emultiplicity q.1 (Ideal.span ({y} : Set B))) =
        ∑ Q ∈ T, F.count Q • (Q.inertiaDeg A : ℕ∞) := by
    apply Finset.sum_bij (s := U) (t := T)
      (fun q _ => q.1)
    · intro q hq
      exact Finset.mem_filter.mpr ⟨
        (Finset.mem_filter.mp hq).2,
        Ideal.primesOver.liesOver m q⟩
    · intro q₁ hq₁ q₂ hq₂ heq
      exact Subtype.ext heq
    · intro Q hQ
      have hQF : Q ∈ F :=
        Multiset.mem_toFinset.mp (Finset.mem_filter.mp hQ).1
      have hQo : Q.LiesOver m := Finset.mem_filter.mp hQ |>.2
      let : Q.IsPrime := Ideal.isPrime_of_prime
        (prime_of_normalized_factor Q hQF)
      let : Q.LiesOver m := hQo
      refine ⟨⟨Q, inferInstance, inferInstance⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Multiset.mem_toFinset.mpr hQF⟩
    · intro q hq
      rw [hcount_q q]
      simp [nsmul_eq_mul, mul_comm]
  exact hsum_factor.trans (hsum_q_filter.trans hsum_bij).symm

set_option maxHeartbeats 1000000 in
theorem chapter11_branch_value_eq_local_length
    (B L : Type*) [CommRing B] [IsDedekindDomain B]
    [Field L] [Algebra B L] [IsFractionRing B L]
    (P : Ideal B) [P.IsPrime] [P.IsMaximal] (hP0 : P ≠ (⊥ : Ideal B))
    (vL : AddValuation L (WithTop ℤ))
    (c : Chapter11ValuationBranchCorrespondence B L P vL.toValuation)
    (hnorm : ∃ z : L, vL z = (1 : WithTop ℤ))
    (b : B) (hb0 : b ≠ 0) :
    vL (algebraMap B L b) =
      (chapter11LocalLengthValue B P b : WithTop ℤ) := by
  let S := Localization.AtPrime P
  let φ : S →+* L :=
    vL.toValuation.valuationSubring.subtype.comp c.localizationEquiv.toRingHom
  let : Algebra S L := φ.toAlgebra
  let : IsScalarTower B S L := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro b
    change algebraMap B L b = φ (algebraMap B S b)
    dsimp [φ]
    rw [show algebraMap B S b =
      Localization.mk b ⟨1, P.primeCompl.one_mem⟩ by rfl,
      c.localizationEquiv_on_B b]
    exact (c.embedding_compatible b).symm
  let : IsFractionRing S L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl S L
  let : IsDiscreteValuationRing S :=
    chapter11_branch_localization_is_dvr B P hP0
  have hφ : algebraMap S L = φ := RingHom.algebraMap_toAlgebra φ
  have hsub : vL.toValuation.valuationSubring.toSubring =
      Subring.map (algebraMap S L) (⊤ : Subring S) := by
    rw [hφ]
    exact chapter11_correspondence_valuationSubring B L P c
  have hbS : algebraMap B S b ≠ 0 := by
    exact (map_ne_zero_iff (algebraMap B S)
      (IsLocalization.injective S P.primeCompl_le_nonZeroDivisors)).2 hb0
  have hv := chapter11_normalized_dvr_ord S L vL hsub hnorm
    (algebraMap B S b) hbS
  change vL (algebraMap B L b) =
      (Ring.ord S (algebraMap B S b)).toNat
  simpa only [IsScalarTower.algebraMap_apply B S L] using hv

/-! The determinant computation used by the norm formula.  Smith normal form
reduces the cokernel of multiplication by a nonzero integral element to the
cyclic quotients appearing in the determinant. -/
theorem chapter11_ord_norm_eq_length_quotient
    (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [Algebra A B]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    (y : B) (hy : y ≠ 0) :
    Ring.ord A (Algebra.norm A y) =
      Module.length A (B ⧸ Ideal.span ({y} : Set B)) := by
  classical
  let ι := Module.Free.ChooseBasisIndex A B
  let b : Basis ι A B := Module.Free.chooseBasis A B
  let hI : (Ideal.span ({y} : Set B) : Ideal B) ≠ ⊥ := by
    simp [hy]
  have hsmith : Associated (Algebra.norm A y)
      (∏ i, Ideal.smithCoeffs b (Ideal.span ({y} : Set B)) hI i) := by
    exact associated_norm_prod_smith b hy
  have horders : Ring.ord A (Algebra.norm A y) =
      ∑ i, Ring.ord A (Ideal.smithCoeffs b
        (Ideal.span ({y} : Set B)) hI i) := by
    have hprod : Ring.ord A
        (∏ i, Ideal.smithCoeffs b (Ideal.span ({y} : Set B)) hI i) =
        ∑ i, Ring.ord A (Ideal.smithCoeffs b
          (Ideal.span ({y} : Set B)) hI i) := by
      induction (Finset.univ : Finset ι) using Finset.induction_on with
      | empty => simp
      | @insert i s his ih =>
          rw [Finset.prod_insert his, Finset.sum_insert his,
            Ring.ord_mul' A
              (mem_nonZeroDivisors_of_ne_zero
                (Ideal.smithCoeffs_ne_zero b (Ideal.span ({y} : Set B)) hI i)), ih]
    exact ((Ring.ord_eq_iff_associated _ _).2 hsmith).trans hprod
  rw [show Module.length A (B ⧸ Ideal.span ({y} : Set B)) =
      Module.length A (∀ i, A ⧸ Ideal.span
        ({Ideal.smithCoeffs b (Ideal.span ({y} : Set B)) hI i} : Set A)) by
        exact (Ideal.quotientEquivPiSpan (Ideal.span ({y} : Set B)) b hI).length_eq]
  rw [Module.length_pi_of_fintype]
  simpa [Ring.ord] using horders

theorem chapter11_length_prime_power_over_base
    (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Algebra.IsIntegral A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    (m : Ideal A) [m.IsMaximal] (hm0 : m ≠ (⊥ : Ideal A))
    (P : Ideal B) [P.IsPrime] [P.IsMaximal] [P.LiesOver m] (n : ℕ) :
    Module.length A (B ⧸ P ^ n) = (n * P.inertiaDeg A : ℕ∞) := by
  let S := Localization.AtPrime P
  let _ := Localization.AtPrime.algebraOfLiesOver m P
  have hm : m = IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal inferInstance
  let _ : P.LiesOver (IsLocalRing.maximalIdeal A) := by
    rw [← hm]
    infer_instance
  let _ : IsDiscreteValuationRing S :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B
      (Ideal.ne_bot_of_mem_primesOver hm0
        (⟨P, inferInstance, inferInstance⟩ : m.primesOver B).2) S
  let _ : IsLocalHom (algebraMap A S) := by
    apply ((IsLocalRing.local_hom_TFAE (algebraMap A S)).out 4 0).mp
    change (IsLocalRing.maximalIdeal S).under A = IsLocalRing.maximalIdeal A
    rw [← Ideal.under_under (B := B), Localization.AtPrime.under_maximalIdeal]
    exact (P.over_def (IsLocalRing.maximalIdeal A)).symm
  let M := S ⧸ IsLocalRing.maximalIdeal S ^ n
  have hres : Module.length (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField S) = P.inertiaDeg A := by
    let e : (B ⧸ P) ≃+* (IsLocalRing.ResidueField S) :=
      IsLocalization.AtPrime.equivQuotMaximalIdeal P S
    let eA : (A ⧸ IsLocalRing.maximalIdeal A) ≃+*
        (IsLocalRing.ResidueField A) := RingEquiv.refl _
    let _ : Module.Finite (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ P) := inferInstance
    let _ : Module.Finite (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField S) := by
      apply Module.Finite.of_equiv_equiv eA e
      apply RingHom.ext
      intro a
      exact Quotient.inductionOn' a (fun a => rfl)
    have hfin : Module.finrank (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ P) =
        Module.finrank (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField S) := by
      apply Algebra.finrank_eq_of_equiv_equiv eA e
      apply RingHom.ext
      intro a
      exact Quotient.inductionOn' a (fun a => rfl)
    rw [Module.length_eq_finrank, hfin.symm,
      (Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal A) P).symm]
  have hlength : Module.length A M =
      Module.length S M * Module.length (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField S) :=
    IsLocalRing.length_restrictScalars A S M
  have hM : Module.length S M = n := by
    dsimp [M]
    exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal S n
  have heq : Module.length A (B ⧸ P ^ n) = Module.length A M := by
    let e := IsLocalization.AtPrime.equivQuotMaximalIdealPow P S n
    exact ((e.restrictScalars A).toLinearEquiv.length_eq)
  rw [heq, hlength, hM, hres]

theorem chapter11_length_quotient_eq_inertia_sum
    (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Algebra.IsIntegral A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    (m : Ideal A) [m.IsMaximal] (hm0 : m ≠ (⊥ : Ideal A))
    (y : B) (hy : y ≠ 0) :
    Module.length A (B ⧸ Ideal.span ({y} : Set B)) =
      ∑ q : m.primesOver B,
        (q.1.inertiaDeg A : ℕ∞) *
          emultiplicity q.1 (Ideal.span ({y} : Set B)) := by
  classical
  let I : Ideal B := Ideal.span ({y} : Set B)
  let F : Multiset (Ideal B) := factors I
  have hI : I ≠ (⊥ : Ideal B) := by
    simp [I, hy]
  have hfactor_branch : ∀ Q : Ideal B, Q ∈ F.toFinset →
      Q.IsPrime ∧ Q.IsMaximal ∧ Q.LiesOver m := by
    intro Q hQ
    have hQmem : Q ∈ F := Multiset.mem_toFinset.mp hQ
    have hQprime : Q.IsPrime :=
      Ideal.isPrime_of_prime (prime_of_factor Q hQmem)
    let _ : Q.IsPrime := hQprime
    have hQ0 : Q ≠ (⊥ : Ideal B) := (prime_of_factor Q hQmem).ne_zero
    have hQunder0 : Q.under A ≠ (⊥ : Ideal A) :=
      Ideal.under_ne_bot A hQ0
    have hQundermax : (Q.under A).IsMaximal :=
      Ring.DimensionLEOne.maximalOfPrime hQunder0 inferInstance
    have hQover : Q.LiesOver m := by
      refine ⟨?_⟩
      calc
        m = IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal inferInstance
        _ = Q.under A := (IsLocalRing.eq_maximalIdeal hQundermax).symm
    let _ : Q.LiesOver m := hQover
    have hQmax : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q m
    exact ⟨hQprime, hQmax, hQover⟩
  have hpow : ∀ Q : Ideal B, Q ∈ F.toFinset →
      Module.length A (B ⧸ Q ^ F.count Q) =
        ((F.count Q * Q.inertiaDeg A : ℕ) : ℕ∞) := by
    intro Q hQ
    obtain ⟨hQprime, hQmax, hQover⟩ := hfactor_branch Q hQ
    let _ : Q.IsPrime := hQprime
    let _ : Q.IsMaximal := hQmax
    let _ : Q.LiesOver m := hQover
    simpa [Nat.cast_mul] using
      (chapter11_length_prime_power_over_base A B m hm0 Q (F.count Q))
  have hlen_pi : Module.length A (B ⧸ I) =
      Module.length A
        (∀ Q : F.toFinset, B ⧸ (Q : Ideal B) ^ F.count (Q : Ideal B)) := by
    let e₀ := IsDedekindDomain.quotientEquivPiFactors hI
    let e : (B ⧸ I) ≃ₐ[A]
        (∀ Q : F.toFinset, B ⧸ (Q : Ideal B) ^ F.count (Q : Ideal B)) :=
      AlgEquiv.ofRingEquiv (f := e₀) (by intro a; rfl)
    exact e.toLinearEquiv.length_eq
  have hlen_sum : Module.length A (B ⧸ I) =
      ∑ Q ∈ F.toFinset,
        ((F.count Q * Q.inertiaDeg A : ℕ) : ℕ∞) := by
    rw [hlen_pi, Module.length_pi_of_fintype]
    let g : Ideal B → ℕ∞ := fun Q => Module.length A (B ⧸ Q ^ F.count Q)
    calc
      _ = ∑ Q ∈ F.toFinset, g Q := by
        simpa [g] using (Finset.sum_coe_sort F.toFinset g)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro Q hQ
        exact hpow Q hQ
  have hemult_count : ∀ Q : Ideal B, Q.IsPrime → Q ≠ (⊥ : Ideal B) →
      emultiplicity Q I = (F.count Q : ℕ∞) := by
    intro Q hQprime hQ0
    let _ : Q.IsPrime := hQprime
    have hQprime' : Prime Q := Ideal.prime_of_isPrime hQ0 hQprime
    change emultiplicity Q I = ((factors I).count Q : ℕ∞)
    rw [factors_eq_normalizedFactors]
    simpa [normalize_eq] using
      (emultiplicity_eq_count_normalizedFactors hQprime'.irreducible hI)
  have hsum_filter :
      (∑ q : m.primesOver B,
        (q.1.inertiaDeg A : ℕ∞) *
          emultiplicity q.1 I) =
        ∑ q ∈ (Finset.univ.filter (fun q : m.primesOver B =>
          q.1 ∈ F.toFinset)),
          (q.1.inertiaDeg A : ℕ∞) * emultiplicity q.1 I := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hqF : q.1 ∈ F.toFinset
    · simp [hqF]
    · have hcount : F.count q.1 = 0 :=
        Multiset.count_eq_zero.mpr (by
          intro hmem
          exact hqF (Multiset.mem_toFinset.mpr hmem))
      have hq0 : q.1 ≠ (⊥ : Ideal B) :=
        Ideal.ne_bot_of_mem_primesOver hm0 q.2
      rw [hemult_count q.1 q.2.1 hq0]
      simp [hcount]
  have hsum_bij :
      (∑ q ∈ (Finset.univ.filter (fun q : m.primesOver B =>
          q.1 ∈ F.toFinset)),
        (q.1.inertiaDeg A : ℕ∞) * emultiplicity q.1 I) =
        ∑ Q ∈ F.toFinset,
          ((F.count Q * Q.inertiaDeg A : ℕ) : ℕ∞) := by
    apply Finset.sum_bij (s := Finset.univ.filter (fun q : m.primesOver B =>
        q.1 ∈ F.toFinset)) (t := F.toFinset)
      (fun q _ => q.1)
    · intro q hq
      exact (Finset.mem_filter.mp hq).2
    · intro q₁ hq₁ q₂ hq₂ heq
      exact Subtype.ext heq
    · intro Q hQ
      obtain ⟨hQprime, hQmax, hQover⟩ := hfactor_branch Q hQ
      let _ : Q.IsPrime := hQprime
      let _ : Q.IsMaximal := hQmax
      let _ : Q.LiesOver m := hQover
      refine ⟨⟨Q, inferInstance, inferInstance⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQ⟩
    · intro q hq
      have hq0 : q.1 ≠ (⊥ : Ideal B) :=
        Ideal.ne_bot_of_mem_primesOver hm0 q.2
      rw [hemult_count q.1 q.2.1 hq0]
      simp [mul_comm]
  simpa [I, F, mul_comm, Nat.cast_mul] using
    hlen_sum.trans (hsum_bij.symm.trans hsum_filter.symm)

set_option maxHeartbeats 5000000 in
/-- The norm valuation formula v(N(x)) = Σ f_i w_i(x).

The finite-normalization branch data identify the displayed valuations with all
normalization branches.  The degree equality is obtained from that finite
normalization rather than assumed in the norm interface.
-/
theorem chapter11_norm_valuation_formula
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    {ι : Type*} [Fintype ι] (v : AddValuation K (WithTop ℤ))
    (w : ι → AddValuation L (WithTop ℤ)) (f : ι → ℕ)
    (hbranches : chapter11CompleteNormalizedBranchFamily v w)
    (hf : ∀ i, f i = chapter11AdditiveResidueDegree v (w i) (hbranches.1 i))
    (hdefectless : chapter11DefectlessNormBranchData v w)
    (x : L) (hx : x ≠ 0) :
    v (Algebra.norm K x) =
      ∑ i, (f i : WithTop ℤ) * w i x := by
  classical
  have : IsLocalHom (algebraMap K L) := by
    refine { map_nonunit := ?_ }
    intro a ha
    exact (isUnit_iff_ne_zero).2 ((map_ne_zero_iff (algebraMap K L)
      (FaithfulSMul.algebraMap_injective K L)).1 (isUnit_iff_ne_zero.1 ha))
  rcases hdefectless with ⟨hvnorm, hAdvr, hfinite, hPfori, hPall⟩
  let A := v.toValuation.valuationSubring
  let B := chapter11IntegralClosure A L
  let _ : IsDiscreteValuationRing A := hAdvr
  let _ : Module.Finite A B := by
    change Module.Finite A (chapter11IntegralClosure A L)
    exact hfinite
  let _ : IsIntegralClosure B A L := by
    change IsIntegralClosure (integralClosure A L) A L
    infer_instance
  let _ : IsDomain B := (IsIntegralClosure.algebraMap_injective B A L).isDomain
  let _ : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L
  let _ : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  let _ : IsDedekindDomain B :=
    chapter11_finite_normalization_is_dedekind A K L B hfinite
  let _ : Module.Free A B :=
    chapter11_finite_torsion_free_over_pid_is_free A B
  let _ : Module.IsTorsionFree A B := by infer_instance
  have hsub : v.toValuation.valuationSubring.toSubring =
      Subring.map (algebraMap A K) (⊤ : Subring A) := by
    apply Subring.ext
    intro z
    constructor
    · intro hz
      exact ⟨⟨z, hz⟩, Subring.mem_top _, rfl⟩
    · rintro ⟨a, -, ha⟩
      rw [← ha]
      exact a.property
  have hcorrespondence_equiv
      {P : Ideal B} {v₁ v₂ : AddValuation L (WithTop ℤ)}
      (c₁ : Chapter11ValuationBranchCorrespondence B L P v₁.toValuation)
      (c₂ : Chapter11ValuationBranchCorrespondence B L P v₂.toValuation) :
      v₁.IsEquiv v₂ := by
    let _ : P.IsPrime := c₁.prime
    have hφ :
        v₁.toValuation.valuationSubring.subtype.comp c₁.localizationEquiv.toRingHom =
          v₂.toValuation.valuationSubring.subtype.comp c₂.localizationEquiv.toRingHom := by
      apply IsLocalization.ringHom_ext P.primeCompl
      apply RingHom.ext
      intro b
      change ((c₁.localizationEquiv
          (Localization.mk b ⟨1, P.primeCompl.one_mem⟩) :
            v₁.toValuation.valuationSubring) : L) =
        ((c₂.localizationEquiv
          (Localization.mk b ⟨1, P.primeCompl.one_mem⟩) :
            v₂.toValuation.valuationSubring) : L)
      rw [c₁.localizationEquiv_on_B, c₂.localizationEquiv_on_B,
        c₁.embedding_compatible, c₂.embedding_compatible]
    apply (Valuation.isEquiv_iff_valuationSubring v₁.toValuation v₂.toValuation).2
    apply ValuationSubring.ext
    intro z
    change z ∈ v₁.toValuation.valuationSubring.toSubring ↔
      z ∈ v₂.toValuation.valuationSubring.toSubring
    rw [chapter11_correspondence_valuationSubring B L P c₁,
      chapter11_correspondence_valuationSubring B L P c₂, hφ]
  have hresidue_degree
      {P : Ideal B}
      (hP : chapter11Branch A B (IsLocalRing.maximalIdeal A) P)
      {vL : AddValuation L (WithTop ℤ)}
      (c : Chapter11ValuationBranchCorrespondence B L P vL.toValuation)
      (hext : v.IsEquiv (AddValuation.comap (algebraMap K L) vL)) :
      chapter11AdditiveResidueDegree v vL hext = P.inertiaDeg A := by
    let _ : P.IsPrime := hP.1
    let _ : P.IsMaximal := hP.2.1
    let _ : P.LiesOver (IsLocalRing.maximalIdeal A) := hP.2.2
    have : Valuation.HasExtension v.toValuation vL.toValuation := ⟨hext⟩
    let : Algebra A vL.toValuation.valuationSubring :=
      Valuation.HasExtension.instAlgebra_valuationSubring
        v.toValuation vL.toValuation
    have : IsLocalHom (algebraMap A vL.toValuation.valuationSubring) :=
      Valuation.HasExtension.instIsLocalHomValuationInteger
        (vR := v.toValuation) (vS := vL.toValuation)
    let eS : IsLocalRing.ResidueField (Localization.AtPrime P) ≃+*
        IsLocalRing.ResidueField vL.toValuation.valuationSubring :=
      IsLocalRing.ResidueField.mapEquiv c.localizationEquiv
    let eP : (B ⧸ P) ≃+* IsLocalRing.ResidueField (Localization.AtPrime P) :=
      IsLocalization.AtPrime.equivQuotMaximalIdeal P (Localization.AtPrime P)
    let eB : (B ⧸ P) ≃+*
        IsLocalRing.ResidueField vL.toValuation.valuationSubring := eP.trans eS
    let eA : (A ⧸ IsLocalRing.maximalIdeal A) ≃+*
        IsLocalRing.ResidueField A := RingEquiv.refl _
    have hlocal (b : B) :
        c.localizationEquiv (algebraMap B (Localization.AtPrime P) b) = c.embedding b := by
      change c.localizationEquiv
          (Localization.mk b ⟨1, P.primeCompl.one_mem⟩) = c.embedding b
      exact c.localizationEquiv_on_B b
    have hemb (a : A) :
        c.embedding (algebraMap A B a) =
          algebraMap A vL.toValuation.valuationSubring a := by
      apply Subtype.ext
      calc
        (c.embedding (algebraMap A B a) : L) =
            algebraMap B L (algebraMap A B a) := c.embedding_compatible _
        _ = algebraMap A L a := by
          rw [IsScalarTower.algebraMap_apply A B L]
        _ = (algebraMap A vL.toValuation.valuationSubring a : L) := by
          calc
            algebraMap A L a = algebraMap K L (a : K) := by
              rw [IsScalarTower.algebraMap_apply A K L]
              rfl
            _ = (algebraMap A vL.toValuation.valuationSubring a : L) := by
              simp [A]
    let : Algebra (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ P) :=
      Ideal.Quotient.algebraOfLiesOver P (IsLocalRing.maximalIdeal A)
    let : IsScalarTower A (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ P) :=
      Ideal.Quotient.isScalarTower_of_liesOver A P (IsLocalRing.maximalIdeal A)
    let : Module.Finite A (B ⧸ P) := Module.Finite.quotient A P
    let : Algebra (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField vL.toValuation.valuationSubring) := inferInstance
    let : Module.Finite (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ P) :=
      Module.Finite.of_restrictScalars_finite A
        (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ P)
    let : Module.Finite (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField vL.toValuation.valuationSubring) := by
      apply Module.Finite.of_equiv_equiv
        (A₁ := A ⧸ IsLocalRing.maximalIdeal A) (B₁ := B ⧸ P)
        (A₂ := IsLocalRing.ResidueField A)
        (B₂ := IsLocalRing.ResidueField vL.toValuation.valuationSubring) eA eB
      apply RingHom.ext
      intro a
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      change (algebraMap (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField vL.toValuation.valuationSubring))
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a) =
        eB (algebraMap (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ P)
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a))
      rw [Ideal.Quotient.algebraMap_mk_of_liesOver]
      change (algebraMap (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField vL.toValuation.valuationSubring))
          (IsLocalRing.residue A a) =
        eB (Ideal.Quotient.mk P (algebraMap A B a))
      rw [IsLocalRing.ResidueField.algebraMap_residue]
      change IsLocalRing.residue vL.toValuation.valuationSubring
          (algebraMap A vL.toValuation.valuationSubring a) =
        IsLocalRing.residue vL.toValuation.valuationSubring
          (c.localizationEquiv
            (algebraMap B (Localization.AtPrime P) (algebraMap A B a)))
      rw [hlocal, hemb]
    have hfin : Module.finrank (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ P) =
        Module.finrank (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField vL.toValuation.valuationSubring) := by
      apply Algebra.finrank_eq_of_equiv_equiv eA eB
      apply RingHom.ext
      intro a
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      change (algebraMap (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField vL.toValuation.valuationSubring))
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a) =
        eB (algebraMap (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ P)
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a))
      rw [Ideal.Quotient.algebraMap_mk_of_liesOver]
      change (algebraMap (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField vL.toValuation.valuationSubring))
          (IsLocalRing.residue A a) =
        eB (Ideal.Quotient.mk P (algebraMap A B a))
      rw [IsLocalRing.ResidueField.algebraMap_residue]
      change IsLocalRing.residue vL.toValuation.valuationSubring
          (algebraMap A vL.toValuation.valuationSubring a) =
        IsLocalRing.residue vL.toValuation.valuationSubring
          (c.localizationEquiv
            (algebraMap B (Localization.AtPrime P) (algebraMap A B a)))
      rw [hlocal, hemb]
    change Module.finrank (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField vL.toValuation.valuationSubring) = _
    exact hfin.symm.trans
      (Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal A) P).symm
  have hord (y : B) (hy : y ≠ 0) :
      v (Algebra.norm K (algebraMap B L y)) =
        (Module.length A (B ⧸ Ideal.span ({y} : Set B))).toNat := by
    rw [← Algebra.algebraMap_intNorm (A := A) (B := B) (K := K) (L := L) y]
    rw [Algebra.intNorm_eq_norm]
    rw [chapter11_normalized_dvr_ord A K v hsub hvnorm]
    rw [chapter11_ord_norm_eq_length_quotient A B y hy]
    exact (Algebra.norm_ne_zero_iff.mpr hy)
  have hlength_nat (y : B) (hy : y ≠ 0) :
      (Module.length A (B ⧸ Ideal.span ({y} : Set B))).toNat =
        ∑ q : (IsLocalRing.maximalIdeal A).primesOver B,
          q.1.inertiaDeg A *
            (emultiplicity q.1 (Ideal.span ({y} : Set B))).toNat := by
    have hq_emult_ne_top (q : (IsLocalRing.maximalIdeal A).primesOver B) :
        emultiplicity q.1 (Ideal.span ({y} : Set B)) ≠ ⊤ := by
      have hq0 : q.1 ≠ (⊥ : Ideal B) :=
        Ideal.ne_bot_of_mem_primesOver (IsDiscreteValuationRing.not_a_field A) q.2
      rw [emultiplicity_eq_count_normalizedFactors
        (Ideal.prime_of_isPrime hq0 q.2.1).irreducible (by simp [hy])]
      simp
    rw [chapter11_length_quotient_eq_inertia_sum A B
      (IsLocalRing.maximalIdeal A) (IsDiscreteValuationRing.not_a_field A) y hy]
    have htoNat :
        (∑ q : (IsLocalRing.maximalIdeal A).primesOver B,
          (q.1.inertiaDeg A : ℕ∞) *
            emultiplicity q.1 (Ideal.span ({y} : Set B))).toNat =
          ∑ q : (IsLocalRing.maximalIdeal A).primesOver B,
            ((q.1.inertiaDeg A : ℕ∞) *
              emultiplicity q.1 (Ideal.span ({y} : Set B))).toNat := by
      apply ENat.toNat_sum
      intro q hq
      exact WithTop.mul_ne_top (ENat.natCast_ne_top _) (hq_emult_ne_top q)
    simpa [ENat.toNat_mul] using htoNat

  have hbranch_of_q
      (q : (IsLocalRing.maximalIdeal A).primesOver B) :
      chapter11Branch A B (IsLocalRing.maximalIdeal A) q.1 := by
    let _ : q.1.IsPrime := q.2.1
    let _ : q.1.LiesOver (IsLocalRing.maximalIdeal A) := q.2.2
    have hqmax : q.1.IsMaximal :=
      Ideal.IsMaximal.of_liesOver_isMaximal q.1 (IsLocalRing.maximalIdeal A)
    exact ⟨q.2.1, hqmax, q.2.2⟩

  let qIndex : (IsLocalRing.maximalIdeal A).primesOver B → ι := fun q =>
    Classical.choose (hPall q.1 (hbranch_of_q q))
  let qCorr (q : (IsLocalRing.maximalIdeal A).primesOver B) :
      Chapter11ValuationBranchCorrespondence B L q.1
        (w (qIndex q)).toValuation :=
    Classical.choice (Classical.choose_spec (hPall q.1 (hbranch_of_q q)))

  have hq_val (q : (IsLocalRing.maximalIdeal A).primesOver B)
      (y : B) (hy : y ≠ 0) :
      w (qIndex q) (algebraMap B L y) =
        (emultiplicity q.1 (Ideal.span ({y} : Set B))).toNat := by
    let _ : q.1.IsPrime := q.2.1
    let _ : q.1.IsMaximal := (hbranch_of_q q).2.1
    have hq0 : q.1 ≠ (⊥ : Ideal B) :=
      Ideal.ne_bot_of_mem_primesOver (IsDiscreteValuationRing.not_a_field A) q.2
    obtain ⟨e, he, hscale, hnorm⟩ := hbranches.2.1 (qIndex q)
    rw [chapter11_branch_value_eq_local_length B L q.1 hq0
      (w (qIndex q)) (qCorr q) hnorm y hy]
    rw [chapter11_local_length_eq_emultiplicity B q.1 hq0 y hy]

  have hq_degree (q : (IsLocalRing.maximalIdeal A).primesOver B) :
      chapter11AdditiveResidueDegree v (w (qIndex q))
          (hbranches.1 (qIndex q)) = q.1.inertiaDeg A := by
    exact hresidue_degree (hbranch_of_q q) (qCorr q) (hbranches.1 (qIndex q))

  have hq_center_eq
      {q₁ q₂ : (IsLocalRing.maximalIdeal A).primesOver B}
      (hqi : qIndex q₁ = qIndex q₂) :
      q₁.1 = q₂.1 := by
    have hcomap :
        (IsLocalRing.maximalIdeal (w (qIndex q₁)).toValuation.valuationSubring).comap
            (qCorr q₁).embedding =
          (IsLocalRing.maximalIdeal (w (qIndex q₂)).toValuation.valuationSubring).comap
            (qCorr q₂).embedding := by
      apply Ideal.ext
      intro b
      constructor
      · intro hb
        have hmax₁ :
            (qCorr q₁).embedding b ∈
              IsLocalRing.maximalIdeal (w (qIndex q₁)).toValuation.valuationSubring := hb
        have hlt₁ :=
          (LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.additive_valuation_subring_maximalIdeal_iff_positive
            (w (qIndex q₁)) ((qCorr q₁).embedding b)).mp hmax₁
        have hlt₁' : (0 : WithTop ℤ) < w (qIndex q₁) (algebraMap B L b) := by
          simpa [(qCorr q₁).embedding_compatible b] using hlt₁
        have hval :
            w (qIndex q₁) (algebraMap B L b) =
              w (qIndex q₂) (algebraMap B L b) := by
          rw [hqi]
        have hlt₂' : (0 : WithTop ℤ) < w (qIndex q₂) (algebraMap B L b) := by
          rw [← hval]
          exact hlt₁'
        have hmax₂ :
            (qCorr q₂).embedding b ∈
              IsLocalRing.maximalIdeal (w (qIndex q₂)).toValuation.valuationSubring := by
          apply (LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.additive_valuation_subring_maximalIdeal_iff_positive
            (w (qIndex q₂)) ((qCorr q₂).embedding b)).mpr
          simpa [(qCorr q₂).embedding_compatible b] using hlt₂'
        exact hmax₂
      · intro hb
        have hmax₂ :
            (qCorr q₂).embedding b ∈
              IsLocalRing.maximalIdeal (w (qIndex q₂)).toValuation.valuationSubring := hb
        have hlt₂ :=
          (LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.additive_valuation_subring_maximalIdeal_iff_positive
            (w (qIndex q₂)) ((qCorr q₂).embedding b)).mp hmax₂
        have hlt₂' : (0 : WithTop ℤ) < w (qIndex q₂) (algebraMap B L b) := by
          simpa [(qCorr q₂).embedding_compatible b] using hlt₂
        have hval :
            w (qIndex q₁) (algebraMap B L b) =
              w (qIndex q₂) (algebraMap B L b) := by
          rw [hqi]
        have hlt₁' : (0 : WithTop ℤ) < w (qIndex q₁) (algebraMap B L b) := by
          rw [hval]
          exact hlt₂'
        have hmax₁ :
            (qCorr q₁).embedding b ∈
              IsLocalRing.maximalIdeal (w (qIndex q₁)).toValuation.valuationSubring := by
          apply (LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.additive_valuation_subring_maximalIdeal_iff_positive
            (w (qIndex q₁)) ((qCorr q₁).embedding b)).mpr
          simpa [(qCorr q₁).embedding_compatible b] using hlt₁'
        exact hmax₁
    calc
      q₁.1 = (IsLocalRing.maximalIdeal (w (qIndex q₁)).toValuation.valuationSubring).comap
          (qCorr q₁).embedding := (qCorr q₁).center
      _ = (IsLocalRing.maximalIdeal (w (qIndex q₂)).toValuation.valuationSubring).comap
          (qCorr q₂).embedding := hcomap
      _ = q₂.1 := (qCorr q₂).center.symm

  have hq_inj {q₁ q₂ : (IsLocalRing.maximalIdeal A).primesOver B}
      (hqi : qIndex q₁ = qIndex q₂) : q₁ = q₂ := by
    apply Subtype.ext
    exact hq_center_eq hqi

  have hq_surj (i : ι) :
      ∃ q : (IsLocalRing.maximalIdeal A).primesOver B, qIndex q = i := by
    obtain ⟨P, hP, ⟨c⟩⟩ := hPfori i
    let q : (IsLocalRing.maximalIdeal A).primesOver B :=
      ⟨P, ⟨hP.1, hP.2.2⟩⟩
    have heq : (w (qIndex q)).IsEquiv (w i) :=
      hcorrespondence_equiv (qCorr q) c
    exact ⟨q, hbranches.2.2.2.1 heq⟩

  have hq_sum (y : B) (hy : y ≠ 0) :
      (∑ q : (IsLocalRing.maximalIdeal A).primesOver B,
        (q.1.inertiaDeg A : WithTop ℤ) *
          ((emultiplicity q.1 (Ideal.span ({y} : Set B))).toNat : WithTop ℤ)) =
        ∑ i, (f i : WithTop ℤ) * w i (algebraMap B L y) := by
    apply Finset.sum_bij (s := Finset.univ) (t := Finset.univ)
      (fun q _ => qIndex q)
    · intro q hq
      exact Finset.mem_univ _
    · intro q₁ hq₁ q₂ hq₂ heq
      exact hq_inj heq
    · intro i hi
      obtain ⟨q, hq⟩ := hq_surj i
      exact ⟨q, Finset.mem_univ _, hq⟩
    · intro q hq
      rw [hf (qIndex q), hq_degree q, hq_val q y hy]

  have hlength_cast (y : B) (hy : y ≠ 0) :
      ((Module.length A (B ⧸ Ideal.span ({y} : Set B))).toNat : WithTop ℤ) =
        ∑ q : (IsLocalRing.maximalIdeal A).primesOver B,
          (q.1.inertiaDeg A : WithTop ℤ) *
            ((emultiplicity q.1 (Ideal.span ({y} : Set B))).toNat : WithTop ℤ) := by
    rw [hlength_nat y hy, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro q hq
    symm
    change (((q.1.inertiaDeg A : ℤ) : WithTop ℤ) *
        (((emultiplicity q.1 (Ideal.span ({y} : Set B))).toNat : ℤ) : WithTop ℤ)) =
      (((q.1.inertiaDeg A *
        (emultiplicity q.1 (Ideal.span ({y} : Set B))).toNat : ℕ) : ℤ) : WithTop ℤ)
    rw [← WithTop.coe_mul]
    congr 1

  have h_integral (y : B) (hy : y ≠ 0) :
      v (Algebra.norm K (algebraMap B L y)) =
        ∑ i, (f i : WithTop ℤ) * w i (algebraMap B L y) := by
    calc
      v (Algebra.norm K (algebraMap B L y)) =
          ((Module.length A (B ⧸ Ideal.span ({y} : Set B))).toNat : WithTop ℤ) :=
        hord y hy
      _ = ∑ q : (IsLocalRing.maximalIdeal A).primesOver B,
          (q.1.inertiaDeg A : WithTop ℤ) *
            ((emultiplicity q.1 (Ideal.span ({y} : Set B))).toNat : WithTop ℤ) :=
        hlength_cast y hy
      _ = ∑ i, (f i : WithTop ℤ) * w i (algebraMap B L y) :=
        hq_sum y hy

  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective B x
  have ha : a ≠ 0 := by
    intro ha0
    subst a
    simp at hx
  have hnorm_div :
      v (Algebra.norm K ((algebraMap B L a) / (algebraMap B L b))) =
        v (Algebra.norm K (algebraMap B L a)) -
          v (Algebra.norm K (algebraMap B L b)) := by
    rw [div_eq_mul_inv, map_mul, Algebra.norm_inv,
      AddValuation.map_mul, AddValuation.map_inv]
    simp only [sub_eq_add_neg]
  have hw_div (i : ι) :
      w i ((algebraMap B L a) / (algebraMap B L b)) =
        w i (algebraMap B L a) - w i (algebraMap B L b) := by
    rw [div_eq_mul_inv, AddValuation.map_mul, AddValuation.map_inv]
    simp only [sub_eq_add_neg]
  calc
    v (Algebra.norm K ((algebraMap B L a) / (algebraMap B L b))) =
        v (Algebra.norm K (algebraMap B L a)) -
          v (Algebra.norm K (algebraMap B L b)) := hnorm_div
    _ = (∑ i, (f i : WithTop ℤ) * w i (algebraMap B L a)) -
          ∑ i, (f i : WithTop ℤ) * w i (algebraMap B L b) := by
        rw [h_integral a ha, h_integral b (nonZeroDivisors.ne_zero hb)]
    _ = ∑ i, (f i : WithTop ℤ) *
          (w i (algebraMap B L a) - w i (algebraMap B L b)) := by
        have hmul_sub (n : ℕ) (a b : WithTop ℤ) (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
            (n : WithTop ℤ) * (a - b) =
              (n : WithTop ℤ) * a - (n : WithTop ℤ) * b := by
          obtain ⟨a, rfl⟩ := WithTop.ne_top_iff_exists.mp ha
          obtain ⟨b, rfl⟩ := WithTop.ne_top_iff_exists.mp hb
          norm_cast
          ring
        have haL : algebraMap B L a ≠ 0 :=
          (map_ne_zero_iff (algebraMap B L)
            (IsIntegralClosure.algebraMap_injective B A L)).2 ha
        have hbL : algebraMap B L b ≠ 0 :=
          (map_ne_zero_iff (algebraMap B L)
            (IsIntegralClosure.algebraMap_injective B A L)).2
            (nonZeroDivisors.ne_zero hb)
        have hsum_sub (g h : ι → WithTop ℤ)
            (hg : ∀ i, g i ≠ ⊤) (hh : ∀ i, h i ≠ ⊤) :
            (∑ i, g i) - ∑ i, h i = ∑ i, (g i - h i) := by
          choose g' hg' using fun i => WithTop.ne_top_iff_exists.mp (hg i)
          choose h' hh' using fun i => WithTop.ne_top_iff_exists.mp (hh i)
          let G : ℤ := ∑ i, g' i
          let H : ℤ := ∑ i, h' i
          let D : ℤ := ∑ i, (g' i - h' i)
          have hg_sum :
              (∑ i, g i) = (G : WithTop ℤ) := by
            calc
              (∑ i, g i) = ∑ i, (g' i : WithTop ℤ) := by
                apply Finset.sum_congr rfl
                intro i hi
                exact (hg' i).symm
              _ = (G : WithTop ℤ) := by
                dsimp [G]
                exact (WithTop.coe_sum (Finset.univ : Finset ι) g').symm
          have hh_sum :
              (∑ i, h i) = (H : WithTop ℤ) := by
            calc
              (∑ i, h i) = ∑ i, (h' i : WithTop ℤ) := by
                apply Finset.sum_congr rfl
                intro i hi
                exact (hh' i).symm
              _ = (H : WithTop ℤ) := by
                dsimp [H]
                exact (WithTop.coe_sum (Finset.univ : Finset ι) h').symm
          have hterm (i : ι) :
              g i - h i = ((g' i - h' i : ℤ) : WithTop ℤ) := by
            rw [← hg' i, ← hh' i, WithTop.LinearOrderedAddCommGroup.coe_sub]
          have hsum_term :
              (∑ i, (g i - h i)) =
                (D : WithTop ℤ) := by
            calc
              (∑ i, (g i - h i)) =
                  ∑ i, ((g' i - h' i : ℤ) : WithTop ℤ) := by
                apply Finset.sum_congr rfl
                intro i hi
                exact hterm i
              _ = (D : WithTop ℤ) := by
                dsimp [D]
                exact (WithTop.coe_sum (Finset.univ : Finset ι)
                  (fun i => g' i - h' i)).symm
          calc
            (∑ i, g i) - ∑ i, h i =
                (G : WithTop ℤ) - (H : WithTop ℤ) := by rw [hg_sum, hh_sum]
            _ = ((G - H : ℤ) : WithTop ℤ) := by
              rw [WithTop.LinearOrderedAddCommGroup.coe_sub]
            _ = (D : WithTop ℤ) := by
              apply congrArg (fun z : ℤ => (z : WithTop ℤ))
              dsimp [G, H, D]
              simp
            _ = ∑ i, (g i - h i) := hsum_term.symm
        calc
          (∑ i, (f i : WithTop ℤ) * w i (algebraMap B L a)) -
              ∑ i, (f i : WithTop ℤ) * w i (algebraMap B L b) =
              ∑ i, ((f i : WithTop ℤ) * w i (algebraMap B L a) -
                (f i : WithTop ℤ) * w i (algebraMap B L b)) := by
            exact hsum_sub _ _
              (fun i => WithTop.mul_ne_top (WithTop.natCast_ne_top _)
                ((AddValuation.ne_top_iff (w i)).2 haL))
              (fun i => WithTop.mul_ne_top (WithTop.natCast_ne_top _)
                ((AddValuation.ne_top_iff (w i)).2 hbL))
          _ = ∑ i, (f i : WithTop ℤ) *
              (w i (algebraMap B L a) - w i (algebraMap B L b)) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact (hmul_sub (f i) _ _
              ((AddValuation.ne_top_iff (w i)).2 haL)
              ((AddValuation.ne_top_iff (w i)).2 hbL)).symm
    _ = ∑ i, (f i : WithTop ℤ) *
          w i ((algebraMap B L a) / (algebraMap B L b)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hw_div i]


/-! A one-branch interface is useful to later chapters that work with a
single chosen extension rather than the full normalization.  The explicit
unique-extension and degree hypotheses are the numerical form of the
branch-correspondence and defectlessness assumptions used above. -/

/-- The norm valuation formula for a single normalized branch.

The restriction factor `e`, residue degree `f`, uniqueness of the branch,
and the degree equality are stated explicitly so this theorem can be used
without reconstructing the finite normalization in every later chapter. -/
theorem chapter11_single_branch_norm_valuation_formula
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {vK : AddValuation K (WithTop ℤ)}
    {vL : AddValuation L (WithTop ℤ)} (e f : ℕ)
    [Valuation.IsRankOneDiscrete vK.toValuation]
    [Valuation.IsRankOneDiscrete vL.toValuation]
    (hext : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL))
    (he : 0 < e)
    (hrestrict : ∀ y : K,
      vL (algebraMap K L y) = (e : WithTop ℤ) * vK y)
    (hf : f = chapter11AdditiveResidueDegree vK vL hext)
    (hunique : ∀ w : AddValuation L (WithTop ℤ),
      vK.IsEquiv (AddValuation.comap (algebraMap K L) w) →
        vL.IsEquiv w)
    (hdegree : Module.finrank K L = e * f) (x : L) (hx : x ≠ 0) :
    vK (Algebra.norm K x) = (f : WithTop ℤ) * vL x := by
  sorry


/-- If the branch values of an element are the specified `e_i`, the norm sees
`Σ e_i f_i`. -/
theorem chapter11_norm_from_branch_values
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    {ι : Type*} [Fintype ι] (v : AddValuation K (WithTop ℤ))
    (w : ι → AddValuation L (WithTop ℤ)) (e f : ι → ℕ) (π : K)
    (hbranches : chapter11CompleteNormalizedBranchFamily v w)
    (hf : ∀ i, f i = chapter11AdditiveResidueDegree v (w i) (hbranches.1 i))
    (hdefectless : chapter11DefectlessNormBranchData v w)
    (hπ : ∀ i, w i (algebraMap K L π) = (e i : WithTop ℤ))
    (hπ_ne : π ≠ 0) :
    v (Algebra.norm K (algebraMap K L π)) =
      ∑ i, (f i : WithTop ℤ) * (e i : WithTop ℤ) := by
  have hnorm := chapter11_norm_valuation_formula K L v w f hbranches hf hdefectless
    (algebraMap K L π)
      ((map_ne_zero_iff (algebraMap K L)
        (FaithfulSMul.algebraMap_injective K L)).2 hπ_ne)
  simpa [hπ] using hnorm

/-- The same formula extends from integral elements to fractions by division. -/
theorem chapter11_norm_valuation_on_fractions
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (v : AddValuation K (WithTop ℤ)) (x y : L) (_hy : y ≠ 0) :
    v (Algebra.norm K (x / y)) =
      v (Algebra.norm K x) - v (Algebra.norm K y) := by
  rw [div_eq_mul_inv, map_mul, Algebra.norm_inv,
    AddValuation.map_mul, AddValuation.map_inv]
  simp only [sub_eq_add_neg]

/-- The uniformizer computation agrees with the degree formula. -/
theorem chapter11_norm_uniformizer_consistency
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    {ι : Type*} [Fintype ι] (v : AddValuation K (WithTop ℤ))
    (w : ι → AddValuation L (WithTop ℤ)) (e f : ι → ℕ) (π : K)
    (hbranches : chapter11CompleteNormalizedBranchFamily v w)
    (hf : ∀ i, f i = chapter11AdditiveResidueDegree v (w i) (hbranches.1 i))
    (hdefectless : chapter11DefectlessNormBranchData v w)
    (hπbase : v π = (1 : WithTop ℤ))
    (hπ : ∀ i, w i (algebraMap K L π) = (e i : WithTop ℤ))
    (hdegree : Module.finrank K L = ∑ i, e i * f i) :
    v (Algebra.norm K (algebraMap K L π)) =
      (Module.finrank K L : WithTop ℤ) := by
  have hπ_ne : π ≠ 0 := by
    intro h
    subst π
    simp at hπbase
  have hnorm := chapter11_norm_valuation_formula K L v w f hbranches hf hdefectless
    (algebraMap K L π)
    ((map_ne_zero_iff (algebraMap K L)
      (FaithfulSMul.algebraMap_injective K L)).2 hπ_ne)
  rw [hnorm]
  simp_rw [hπ]
  have hpoint : ∀ i : ι,
      (f i : WithTop ℤ) * (e i : WithTop ℤ) =
        ((e i * f i : ℕ) : WithTop ℤ) := by
    intro i
    change ((f i : ℤ) : WithTop ℤ) * ((e i : ℤ) : WithTop ℤ) =
      ((e i * f i : ℤ) : WithTop ℤ)
    rw [← WithTop.coe_mul]
    congr 1
    exact mul_comm (f i : ℤ) (e i : ℤ)
  calc
    ∑ i, (f i : WithTop ℤ) * (e i : WithTop ℤ) =
        ∑ i, ((e i * f i : ℕ) : WithTop ℤ) := by
          exact Finset.sum_congr rfl (fun i hi => hpoint i)
    _ = (∑ i, e i * f i : ℕ) := by
      symm
      exact Nat.cast_sum (R := WithTop ℤ) Finset.univ (fun i => e i * f i)
    _ = (Module.finrank K L : WithTop ℤ) := by
      exact congrArg (fun n : ℕ => (n : WithTop ℤ)) hdegree.symm

end
end LastLib.Book01ValuationsDVRsAndCompletions.Chapter11
