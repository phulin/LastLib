import Mathlib.Algebra.Module.PID
import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Norm.Defs

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter05

open IsLocalRing
open scoped BigOperators DirectSum Pointwise nonZeroDivisors

noncomputable section

/-!
# Chapter 5: The valuation filtration

This file records the module, lattice, elementary-divisor, and determinant
interfaces used in Section 5.4 of *Valuations, DVRs, and Completions*.
-/

/-! # Book 1, Chapter 5, Section 5.4: Filtered Modules and Elementary Divisors -/

section FilteredModulesAndElementaryDivisors

variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable (π : A) (hπ : Irreducible π)

/-- The `π`-adic filtration on an `A`-module, written as a submodule. -/
def chapterModuleFiltration
    (M : Type*) [AddCommGroup M] [Module A M] (n : ℕ) : Submodule A M :=
  Submodule.span A (Set.range (fun x : M => (π ^ n) • x))

/-- The denominator submodule used to form the `n`th module-filtration layer. -/
def chapterModuleFiltrationDenominator
    (M : Type*) [AddCommGroup M] [Module A M] (n : ℕ) :
    Submodule A (↥(chapterModuleFiltration A π M n)) :=
  Submodule.comap (chapterModuleFiltration A π M n).subtype
    (chapterModuleFiltration A π M (n + 1))

/-- The successive quotient `π^n M / π^(n+1) M`. -/
abbrev chapterModuleFiltrationLayer
    (M : Type*) [AddCommGroup M] [Module A M] (n : ℕ) : Type _ :=
  (↥(chapterModuleFiltration A π M n)) ⧸
    chapterModuleFiltrationDenominator A π M n

omit [IsDiscreteValuationRing A] in
include hπ in
/-- Every filtration layer of a finite free module is one copy of `M / πM`. -/
theorem chapter_module_filtration_layer_equiv_quotient
    (M : Type*) [AddCommGroup M] [Module A M]
    [Module.Free A M] [Module.Finite A M] (n : ℕ) :
    Nonempty
      (chapterModuleFiltrationLayer A π M n ≃ₗ[A]
        M ⧸ chapterModuleFiltration A π M 1) := by
  classical
  have hfiltration (k : ℕ) :
      chapterModuleFiltration A π M k =
        (π ^ k) • (⊤ : Submodule A M) := by
    rw [chapterModuleFiltration]
    apply le_antisymm
    · apply Submodule.span_le.2
      rintro _ ⟨x, rfl⟩
      exact Submodule.smul_mem_pointwise_smul x (π ^ k) ⊤ trivial
    · intro x hx
      obtain ⟨y, hy, rfl⟩ :=
        (Submodule.mem_smul_pointwise_iff_exists x (π ^ k) (⊤ : Submodule A M)).mp hx
      exact Submodule.subset_span ⟨y, rfl⟩
  have hφ_injective (k : ℕ) :
      Function.Injective (LinearMap.lsmul A M (π ^ k)) := by
    exact LinearMap.lsmul_injective (pow_ne_zero _ hπ.ne_zero)
  have hφ_mem (k : ℕ) (x : M) :
      LinearMap.lsmul A M (π ^ k) x ∈ chapterModuleFiltration A π M k := by
    rw [hfiltration]
    exact Submodule.smul_mem_pointwise_smul x (π ^ k) ⊤ trivial
  let e : M ≃ₗ[A] chapterModuleFiltration A π M n :=
    LinearEquiv.ofBijective
      ((LinearMap.lsmul A M (π ^ n)).codRestrict
        (chapterModuleFiltration A π M n) (hφ_mem n))
      ⟨(by
          intro x y hxy
          apply hφ_injective n
          exact congrArg (fun z : chapterModuleFiltration A π M n => (z : M)) hxy),
        (by
          intro z
          have hz : (z : M) ∈ (π ^ n) • (⊤ : Submodule A M) := by
            rw [← hfiltration n]
            exact z.property
          obtain ⟨y, hy, hzy⟩ :=
            (Submodule.mem_smul_pointwise_iff_exists (z : M) (π ^ n)
              (⊤ : Submodule A M)).mp hz
          refine ⟨y, ?_⟩
          apply Subtype.ext
          exact hzy)⟩
  have hmap :
      (chapterModuleFiltration A π M 1).map
          (e : M →ₗ[A] chapterModuleFiltration A π M n) =
        chapterModuleFiltrationDenominator A π M n := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      change ((e x : chapterModuleFiltration A π M n) : M) ∈
        chapterModuleFiltration A π M (n + 1)
      rw [hfiltration 1, pow_one] at hx
      obtain ⟨y, hy, hxy⟩ :=
        (Submodule.mem_smul_pointwise_iff_exists x π (⊤ : Submodule A M)).mp hx
      have he_apply : (e x : M) = (π ^ n) • x := rfl
      rw [he_apply, ← hxy, hfiltration (n + 1), smul_smul, ← pow_succ]
      exact Submodule.smul_mem_pointwise_smul y (π ^ (n + 1)) ⊤ trivial
    · intro hz
      change (z : M) ∈ chapterModuleFiltration A π M (n + 1) at hz
      rw [hfiltration (n + 1)] at hz
      obtain ⟨y, hy, hzy⟩ :=
        (Submodule.mem_smul_pointwise_iff_exists (z : M) (π ^ (n + 1))
          (⊤ : Submodule A M)).mp hz
      refine ⟨π • y, ?_, ?_⟩
      · rw [hfiltration 1, pow_one]
        exact Submodule.smul_mem_pointwise_smul y π ⊤ trivial
      · apply Subtype.ext
        have he_apply : (e (π • y) : M) = (π ^ n) • (π • y) := rfl
        calc
          (e (π • y) : M) = (π ^ n) • (π • y) := he_apply
          _ = (π ^ (n + 1)) • y := by rw [smul_smul, ← pow_succ]
          _ = (z : M) := hzy
  exact ⟨(Submodule.Quotient.equiv
    (chapterModuleFiltration A π M 1)
    (chapterModuleFiltrationDenominator A π M n) e hmap).symm⟩

include hπ in
/-- The length of the finite-precision quotient of a free rank-`r` module. -/
theorem chapter_module_filtration_quotient_length
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Free A M]
    (r : ℕ) (b : Module.Basis (Fin r) A M) (n : ℕ) :
    Module.length A (M ⧸ chapterModuleFiltration A π M n) =
      (n : ℕ∞) * (r : ℕ∞) := by
  classical
  have hfiltration (k : ℕ) :
      chapterModuleFiltration A π M k =
        (Ideal.span {π ^ k} : Ideal A) • (⊤ : Submodule A M) := by
    rw [chapterModuleFiltration, Submodule.ideal_span_singleton_smul]
    apply le_antisymm
    · apply Submodule.span_le.2
      rintro _ ⟨x, rfl⟩
      exact Submodule.smul_mem_pointwise_smul x (π ^ k) ⊤ trivial
    · intro x hx
      obtain ⟨y, hy, rfl⟩ :=
        (Submodule.mem_smul_pointwise_iff_exists x (π ^ k) (⊤ : Submodule A M)).mp hx
      exact Submodule.subset_span ⟨y, rfl⟩
  have hpi (I : Ideal A) :
      I • (⊤ : Submodule A (Fin r → A)) =
        Submodule.pi Set.univ (fun _ : Fin r => I) := by
    apply le_antisymm
    · refine Submodule.smul_le.2 ?_
      intro a ha x hx
      rw [Submodule.mem_pi]
      intro i hi
      simpa [Pi.smul_apply, smul_eq_mul, mul_comm] using I.mul_mem_left (x i) ha
    · rw [← Submodule.iSup_map_single]
      refine iSup_le fun i => ?_
      rw [Submodule.map_le_iff_le_comap]
      intro a ha
      have ha' : (a : A) • (Pi.single i (1 : A)) ∈
          I • (⊤ : Submodule A (Fin r → A)) :=
        Submodule.smul_mem_smul (I := I)
          (N := (⊤ : Submodule A (Fin r → A))) ha trivial
      change Pi.single i a ∈ I • (⊤ : Submodule A (Fin r → A))
      have hsingle : Pi.single i a = a • Pi.single i (1 : A) := by
        ext j
        by_cases hji : j = i
        · subst j
          simp
        · simp [hji]
      rw [hsingle]
      exact ha'
  let e : M ≃ₗ[A] (Fin r → A) := b.equivFun
  have hmap :
      (chapterModuleFiltration A π M n).map
          (e : M →ₗ[A] (Fin r → A)) =
        Submodule.pi Set.univ (fun _ : Fin r => Ideal.span {π ^ n}) := by
    have herange : (e : M →ₗ[A] (Fin r → A)).range = ⊤ :=
      LinearMap.range_eq_top.mpr e.surjective
    rw [hfiltration, Submodule.map_smul'', Submodule.map_top, herange, hpi]
  let eqv : (M ⧸ chapterModuleFiltration A π M n) ≃ₗ[A]
      ((Fin r → A) ⧸ Submodule.pi Set.univ
        (fun _ : Fin r => Ideal.span {π ^ n})) :=
    Submodule.Quotient.equiv _ _ e hmap
  let eqv' : ((Fin r → A) ⧸ Submodule.pi Set.univ
      (fun _ : Fin r => Ideal.span {π ^ n})) ≃ₗ[A]
      (∀ i : Fin r, A ⧸ (Ideal.span {π ^ n} : Ideal A)) :=
    Submodule.quotientPi _
  rw [(eqv.trans eqv').length_eq, Module.length_pi_of_fintype]
  have hlen : Module.length A (A ⧸ (Ideal.span {π ^ n} : Ideal A)) = (n : ℕ∞) := by
    rw [← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq,
      IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
  simp_rw [hlen]
  simp [mul_comm]

include hπ in
/-- The finite free module filtration is separated. -/
theorem chapter_module_filtration_iInf_eq_bot
    (M : Type*) [AddCommGroup M] [Module A M]
    [Module.Free A M] [Module.Finite A M] :
    ⨅ n : ℕ, chapterModuleFiltration A π M n = (⊥ : Submodule A M) := by
  have hfiltration (n : ℕ) :
      chapterModuleFiltration A π M n =
        (Ideal.span {π ^ n} : Ideal A) • (⊤ : Submodule A M) := by
    rw [chapterModuleFiltration, Submodule.ideal_span_singleton_smul]
    apply le_antisymm
    · apply Submodule.span_le.2
      rintro _ ⟨x, rfl⟩
      exact Submodule.smul_mem_pointwise_smul x (π ^ n) ⊤ trivial
    · intro x hx
      obtain ⟨y, hy, rfl⟩ :=
        (Submodule.mem_smul_pointwise_iff_exists x (π ^ n) (⊤ : Submodule A M)).mp hx
      exact Submodule.subset_span ⟨y, rfl⟩
  simp_rw [hfiltration, ← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq]
  exact Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := M)
    (IsLocalRing.maximalIdeal A) (maximalIdeal.isMaximal A).ne_top

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- An `A`-linear map preserves every level of the `π`-adic filtration. -/
theorem chapter_linear_map_preserves_module_filtration
    {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (T : M →ₗ[A] N) (n : ℕ) :
    (chapterModuleFiltration A π M n).map T ≤
      chapterModuleFiltration A π N n := by
  rw [chapterModuleFiltration, chapterModuleFiltration, Submodule.map_span]
  apply Submodule.span_le.2
  rintro _ ⟨x, ⟨y, rfl⟩, rfl⟩
  rw [T.map_smul]
  exact Submodule.subset_span ⟨T y, rfl⟩

section Lattices

variable {K E : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
  [AddCommGroup E] [Module A E] [Module K E] [IsScalarTower A K E]

/-- A finitely generated `A`-submodule spanning `E` over `K`. -/
def chapterFullLattice (M : Submodule A E) : Prop :=
  Module.Finite A M ∧ Submodule.span K (M : Set E) = ⊤

/-- Scaling a lattice by a field element. -/
def chapterLatticeScale (a : K) (M : Submodule A E) : Set E :=
  {x | ∃ y : E, y ∈ M ∧ a • y = x}

include hπ in
/-- Any two full lattices differ by a bounded power of the uniformizer. -/
theorem chapter_full_lattices_commensurable
    (M N : Submodule A E)
    (hM : chapterFullLattice (A := A) (K := K) M)
    (hN : chapterFullLattice (A := A) (K := K) N) :
    ∃ r : ℕ,
      chapterLatticeScale (A := A) (K := K) (E := E)
          (algebraMap A K (π ^ r)) M ⊆ (N : Set E) ∧
        (N : Set E) ⊆
          chapterLatticeScale (A := A) (K := K) (E := E)
            ((algebraMap A K (π ^ r))⁻¹) M := by
  classical
  have hclear (P Q : Submodule A E) [Module.Finite A P] [Module.Finite A Q]
      (hQ : Submodule.span K (Q : Set E) = ⊤) :
      ∃ r : ℕ, ∀ x : P,
        (algebraMap A K (π ^ r)) • (x : E) ∈ Q := by
    obtain ⟨m, p, hp⟩ := Module.Finite.exists_fin (R := A) (M := P)
    obtain ⟨q, qgen, hq⟩ := Module.Finite.exists_fin (R := A) (M := Q)
    have hspanq :
        Submodule.span K (Set.range (fun j : Fin q => (qgen j : E))) = ⊤ := by
      apply top_unique
      rw [← hQ]
      apply Submodule.span_le.2
      intro x hx
      have hx' :
          (⟨x, hx⟩ : Q) ∈ Submodule.span A (Set.range qgen) := by
        rw [hq]
        trivial
      have hspanq' : ∀ y : Q, y ∈ Submodule.span A (Set.range qgen) →
          (y : E) ∈ Submodule.span K (Set.range (fun j : Fin q => (qgen j : E))) := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem z hz =>
            obtain ⟨j, rfl⟩ := hz
            exact Submodule.subset_span ⟨j, rfl⟩
        | zero => exact Submodule.zero_mem _
        | add z w hz hw hzp hwp => exact Submodule.add_mem _ hzp hwp
        | smul a z hz hzp =>
            simpa [Algebra.smul_def] using
              Submodule.smul_mem _ (algebraMap A K a) hzp
      exact hspanq' ⟨x, hx⟩ hx'
    have hcoeff (i : Fin m) :
        ∃ c : Fin q →₀ K,
          c.sum (fun j a => a • (qgen j : E)) = (p i : E) := by
      apply (Finsupp.mem_span_range_iff_exists_finsupp.mp ?_)
      rw [hspanq]
      trivial
    let c : Fin m → Fin q →₀ K := fun i => (hcoeff i).choose
    have hc (i : Fin m) :
        (c i).sum (fun j a => a • (qgen j : E)) = (p i : E) :=
      (hcoeff i).choose_spec
    obtain ⟨d, hd⟩ :=
      IsLocalization.exist_integer_multiples_of_finite
        (M := nonZeroDivisors A) (S := K)
        (fun ij : Fin m × Fin q => c ij.1 ij.2)
    obtain ⟨r, u, hdu⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        (nonZeroDivisors.ne_zero d.2) hπ
    have hci (i : Fin m) (j : Fin q) :
        ∃ a : A,
          algebraMap A K a =
            (algebraMap A K (π ^ r)) • c i j := by
      have hdi : IsLocalization.IsInteger A
          ((d : A) • c i j) := hd (i, j)
      have hdi' : IsLocalization.IsInteger A
          ((↑(u⁻¹) : A) • ((d : A) • c i j)) :=
        IsLocalization.isInteger_smul hdi
      rcases hdi' with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      rw [ha]
      have huK : algebraMap A K (u : A) ≠ 0 := by
        intro h
        have hprodA : (u : A) * (↑(u⁻¹) : A) = 1 := u.val_inv
        have hprod :
            algebraMap A K (u : A) * algebraMap A K (↑(u⁻¹) : A) = (1 : K) := by
          rw [← map_mul, hprodA, map_one]
        rw [h, zero_mul] at hprod
        exact zero_ne_one hprod
      simp [Algebra.smul_def, hdu, map_mul]
      simp only [mul_assoc]
      rw [← mul_assoc, inv_mul_cancel₀ huK, one_mul]
    have hpgen (i : Fin m) :
        (algebraMap A K (π ^ r)) • (p i : E) ∈ Q := by
      rw [← hc i]
      simp only [Finsupp.sum]
      rw [Finset.smul_sum]
      apply Submodule.sum_mem
      intro j hj
      have hj' := hci i j
      obtain ⟨a, ha⟩ := hj'
      rw [smul_smul]
      have hcoeffeq :
          algebraMap A K (π ^ r) * c i j = algebraMap A K a := by
        simpa only [smul_eq_mul] using ha.symm
      rw [hcoeffeq]
      rw [IsScalarTower.algebraMap_smul (A := K)]
      exact Q.smul_mem a (qgen j).property
    refine ⟨r, ?_⟩
    intro x
    have hx : (x : P) ∈ Submodule.span A (Set.range p) := by
      rw [hp]
      trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
        rcases hy with ⟨i, rfl⟩
        exact hpgen i
    | zero => simp
    | add x y hx hy hxp hyp => simpa [smul_add] using Q.add_mem hxp hyp
    | smul a x hx hxp =>
        have hxp' : (π ^ r) • (x : E) ∈ Q := by
          simpa only [IsScalarTower.algebraMap_smul (A := K)] using hxp
        rw [IsScalarTower.algebraMap_smul (A := K)]
        change (π ^ r) • (a • (x : E)) ∈ Q
        rw [smul_comm]
        exact Q.smul_mem a hxp'
  obtain ⟨r₁, hr₁⟩ := @hclear M N hM.1 hN.1 hN.2
  obtain ⟨r₂, hr₂⟩ := @hclear N M hN.1 hM.1 hM.2
  have hpow12 (x : E) :
      (algebraMap A K (π ^ (r₁ + r₂))) • x =
        (algebraMap A K (π ^ r₂)) •
          ((algebraMap A K (π ^ r₁)) • x) := by
    rw [map_pow, pow_add, map_pow, map_pow, mul_comm, mul_smul]
  have hpow21 (x : E) :
      (algebraMap A K (π ^ (r₁ + r₂))) • x =
        (algebraMap A K (π ^ r₁)) •
          ((algebraMap A K (π ^ r₂)) • x) := by
    rw [map_pow, pow_add, map_pow, map_pow, mul_smul]
  refine ⟨r₁ + r₂, ?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    rw [hpow12]
    change _ ∈ N
    simpa only [IsScalarTower.algebraMap_smul (A := K)] using
      N.smul_mem (π ^ r₂) (hr₁ ⟨y, hy⟩)
  · intro x hx
    refine ⟨(algebraMap A K (π ^ (r₁ + r₂))) • x, ?_, ?_⟩
    · rw [hpow21]
      simpa only [IsScalarTower.algebraMap_smul (A := K)] using
        M.smul_mem (π ^ r₁) (hr₂ ⟨x, hx⟩)
    · apply inv_smul_smul₀
      intro hzero
      have hzero' : π ^ (r₁ + r₂) = 0 :=
        (IsFractionRing.injective A K) (by simpa using hzero)
      exact pow_ne_zero _ hπ.ne_zero hzero'

end Lattices

/-- The diagonal submodule associated to a basis and valuation exponents. -/
def chapterDiagonalSubmodule
    (M : Type*) [AddCommGroup M] [Module A M]
    (r : ℕ) (b : Module.Basis (Fin r) A M) (a : Fin r → ℕ) :
    Submodule A M :=
  Submodule.span A (Set.range (fun i => (π ^ a i) • b i))

include hπ in
/-- Elementary divisors for a finite torsion quotient of a finite free module. -/
theorem chapter_elementary_divisor_decomposition
    (M : Type*) [AddCommGroup M] [Module A M]
    [Module.Free A M] [Module.Finite A M]
    (N : Submodule A M) [Module.Finite A (M ⧸ N)]
    (hN : Module.IsTorsion A (M ⧸ N)) :
    ∃ (r : ℕ) (b : Module.Basis (Fin r) A M) (a : Fin r → ℕ),
      N = chapterDiagonalSubmodule A π M r b a ∧
      Nonempty
        ((M ⧸ N) ≃ₗ[A] (⨁ i : Fin r,
          A ⧸ (Ideal.span {π ^ a i} : Ideal A))) ∧
      Module.length A (M ⧸ N) = ∑ i : Fin r, (a i : ℕ∞) := by
  classical
  have hquot : Module.finrank A (M ⧸ N) = 0 := hN.finrank_eq_zero
  have hsum := N.finrank_quotient_add_finrank
  have hfin : Module.finrank A N = Module.finrank A M := by
    rw [hquot, zero_add] at hsum
    exact hsum
  let r := Module.finrank A M
  let b : Module.Basis (Fin r) A M := Module.finBasis A M
  let c : Fin r → A := Submodule.smithNormalFormCoeffs b hfin
  let btop : Module.Basis (Fin r) A M :=
    Submodule.smithNormalFormTopBasis b hfin
  let bbot : Module.Basis (Fin r) A N :=
    Submodule.smithNormalFormBotBasis b hfin
  have hcne (i : Fin r) : c i ≠ 0 := by
    change Submodule.smithNormalFormCoeffs b hfin i ≠ 0
    exact Submodule.smithNormalFormCoeffs_ne_zero b hfin i
  have hfactor (i : Fin r) : ∃ (n : ℕ) (u : Aˣ), c i = u * π ^ n := by
    exact IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hcne i) hπ
  choose a u hcu using hfactor
  have hbot_span :
      Submodule.span A (Set.range (fun i : Fin r => (bbot i : M))) = N := by
    apply (Submodule.span_range_subtype_eq_top_iff N
      (s := fun i : Fin r => (bbot i : M)) (fun i => (bbot i).property)).mp
    exact bbot.span_eq
  have hdiag (i : Fin r) :
      (bbot i : M) = c i • btop i := by
    change (Submodule.smithNormalFormBotBasis b hfin i : M) =
      Submodule.smithNormalFormCoeffs b hfin i •
        Submodule.smithNormalFormTopBasis b hfin i
    exact Submodule.smithNormalFormBotBasis_def b hfin i
  have hNdiag :
      N = chapterDiagonalSubmodule A π M r btop a := by
    rw [← hbot_span, chapterDiagonalSubmodule]
    apply le_antisymm
    · apply Submodule.span_le.2
      rintro _ ⟨i, rfl⟩
      change (bbot i : M) ∈
        Submodule.span A (Set.range (fun i : Fin r => (π ^ a i) • btop i))
      rw [hdiag i, hcu i, mul_smul]
      exact Submodule.smul_mem _ (↑(u i) : A) (Submodule.subset_span ⟨i, rfl⟩)
    · apply Submodule.span_le.2
      rintro _ ⟨i, rfl⟩
      change (π ^ a i) • btop i ∈
        Submodule.span A (Set.range (fun i : Fin r => (bbot i : M)))
      have hi :
          (π ^ a i) • btop i =
            (↑((u i)⁻¹) : A) • (c i • btop i) := by
        rw [hcu i, mul_smul]
        simp [smul_smul]
      rw [hi, ← hdiag i]
      exact Submodule.smul_mem _ (↑((u i)⁻¹) : A)
        (Submodule.subset_span ⟨i, rfl⟩)
  have hI (i : Fin r) :
      Ideal.span ({c i} : Set A) = Ideal.span {π ^ a i} := by
    rw [hcu i, Ideal.span_singleton_mul_left_unit (u i).isUnit]
  let qi (i : Fin r) :
      (A ⧸ (Ideal.span {c i} : Ideal A)) ≃ₗ[A]
        A ⧸ (Ideal.span {π ^ a i} : Ideal A) :=
    Submodule.Quotient.equiv _ _ (LinearEquiv.refl A A) (by
      simpa using hI i)
  let e : (M ⧸ N) ≃ₗ[A]
      (∀ i : Fin r, A ⧸ (Ideal.span {c i} : Ideal A)) := by
    simpa [c] using N.quotientEquivPiSpan b hfin
  let ep :
      (∀ i : Fin r, A ⧸ (Ideal.span {c i} : Ideal A)) ≃ₗ[A]
        (∀ i : Fin r, A ⧸ (Ideal.span {π ^ a i} : Ideal A)) :=
    LinearEquiv.piCongrRight qi
  let et := e.trans ep
  have hlen (i : Fin r) :
      Module.length A (A ⧸ (Ideal.span {π ^ a i} : Ideal A)) = (a i : ℕ∞) := by
    rw [← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq,
      IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
  refine ⟨r, btop, a, hNdiag, ?_, ?_⟩
  · exact ⟨et.trans
      (DirectSum.linearEquivFunOnFintype A (Fin r)
        (fun i => A ⧸ (Ideal.span {π ^ a i} : Ideal A))).symm⟩
  · rw [et.length_eq, Module.length_pi_of_fintype]
    simp_rw [hlen]

/-- The normalized valuation of the determinant of an endomorphism. -/
def chapterDeterminantValuation
    (M : Type*) [AddCommGroup M] [Module A M]
    [Module.Free A M] [Module.Finite A M] (T : M →ₗ[A] M) : ℕ∞ :=
  IsDiscreteValuationRing.addVal A (LinearMap.det T)

/-- The determinant valuation is the length of the quotient by an injective map. -/
theorem chapter_injective_endomorphism_length_eq_determinant_valuation
    (M : Type*) [AddCommGroup M] [Module A M]
    [Module.Free A M] [Module.Finite A M] (T : M →ₗ[A] M)
    (hT : Function.Injective T) :
    Module.length A (M ⧸ LinearMap.range T) =
      chapterDeterminantValuation A M T := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hfin : Module.finrank A (LinearMap.range T) = Module.finrank A M :=
    LinearMap.finrank_range_of_inj hT
  let r := Module.finrank A M
  let b : Module.Basis (Fin r) A M := Module.finBasis A M
  let c : Fin r → A :=
    Submodule.smithNormalFormCoeffs (N := LinearMap.range T) b hfin
  let btop : Module.Basis (Fin r) A M :=
    Submodule.smithNormalFormTopBasis (N := LinearMap.range T) b hfin
  let bbot : Module.Basis (Fin r) A (LinearMap.range T) :=
    Submodule.smithNormalFormBotBasis (N := LinearMap.range T) b hfin
  have hcne (i : Fin r) : c i ≠ 0 := by
    change Submodule.smithNormalFormCoeffs (N := LinearMap.range T) b hfin i ≠ 0
    exact Submodule.smithNormalFormCoeffs_ne_zero b hfin i
  have hfactor (i : Fin r) : ∃ (n : ℕ) (u : Aˣ), c i = u * ϖ ^ n := by
    exact IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hcne i) hϖ
  choose a u hcu using hfactor
  have hI (i : Fin r) :
      Ideal.span ({c i} : Set A) = Ideal.span {ϖ ^ a i} := by
    rw [hcu i, Ideal.span_singleton_mul_left_unit (u i).isUnit]
  let qi (i : Fin r) :
      (A ⧸ (Ideal.span {c i} : Ideal A)) ≃ₗ[A]
        A ⧸ (Ideal.span {ϖ ^ a i} : Ideal A) :=
    Submodule.Quotient.equiv _ _ (LinearEquiv.refl A A) (by
      simpa using hI i)
  let e : (M ⧸ LinearMap.range T) ≃ₗ[A]
      (∀ i : Fin r, A ⧸ (Ideal.span {c i} : Ideal A)) := by
    simpa [c] using
      (Submodule.quotientEquivPiSpan (N := LinearMap.range T) b hfin)
  let ep :
      (∀ i : Fin r, A ⧸ (Ideal.span {c i} : Ideal A)) ≃ₗ[A]
        (∀ i : Fin r, A ⧸ (Ideal.span {ϖ ^ a i} : Ideal A)) :=
    LinearEquiv.piCongrRight qi
  let et := e.trans ep
  have hlen (i : Fin r) :
      Module.length A (A ⧸ (Ideal.span {c i} : Ideal A)) = (a i : ℕ∞) := by
      rw [(qi i).length_eq, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq,
      IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
  have hlenpow (i : Fin r) :
      Module.length A (A ⧸ (Ideal.span {ϖ ^ a i} : Ideal A)) = (a i : ℕ∞) := by
    rw [← (qi i).length_eq]
    exact hlen i
  have hlength : Module.length A (M ⧸ LinearMap.range T) =
      ∑ i : Fin r, (a i : ℕ∞) := by
    rw [et.length_eq, Module.length_pi_of_fintype]
    simp_rw [hlenpow]
  let eRange : M ≃ₗ[A] LinearMap.range T :=
    LinearEquiv.ofBijective
      (T.codRestrict (LinearMap.range T) (fun x => ⟨x, rfl⟩))
      ⟨(by
          intro x y hxy
          apply hT
          exact congrArg (fun z : LinearMap.range T => (z : M)) hxy),
        (by
          intro z
          rcases z.property with ⟨x, hx⟩
          refine ⟨x, ?_⟩
          apply Subtype.ext
          exact hx)⟩
  let bdom : Module.Basis (Fin r) A M := bbot.map eRange.symm
  have hTdom (i : Fin r) : T (bdom i) = (bbot i : M) := by
    change T (eRange.symm (bbot i)) = (bbot i : M)
    exact congrArg (fun z : LinearMap.range T => (z : M))
      (eRange.apply_symm_apply (bbot i))
  have hdiag (i : Fin r) :
      (bbot i : M) = c i • btop i := by
    change (Submodule.smithNormalFormBotBasis (N := LinearMap.range T) b hfin i : M) =
      Submodule.smithNormalFormCoeffs (N := LinearMap.range T) b hfin i •
        Submodule.smithNormalFormTopBasis (N := LinearMap.range T) b hfin i
    exact Submodule.smithNormalFormBotBasis_def b hfin i
  have hmatrix :
      btop.toMatrix (fun i : Fin r => T (bdom i)) = Matrix.diagonal c := by
    ext i j
    rw [Module.Basis.toMatrix_apply, hTdom j, hdiag j]
    by_cases hij : i = j
    · subst i
      simp
    · simp [hij]
  have hdetvec :
      btop.det (fun i : Fin r => T (bdom i)) = ∏ i : Fin r, c i := by
    rw [Module.Basis.det_apply, hmatrix, Matrix.det_diagonal]
  have hdetprod :
      LinearMap.det T * btop.det bdom = ∏ i : Fin r, c i := by
    calc
      LinearMap.det T * btop.det bdom =
          btop.det (fun i : Fin r => T (bdom i)) := by
            symm
            exact Module.Basis.det_comp btop T (fun i : Fin r => bdom i)
      _ = ∏ i : Fin r, c i := hdetvec
  have hunit : IsUnit (btop.det bdom) := btop.isUnit_det bdom
  have hunitval : IsDiscreteValuationRing.addVal A (btop.det bdom) = 0 := by
    obtain ⟨v, hv⟩ := hunit
    rw [← hv, IsDiscreteValuationRing.addVal_eq_zero_of_unit]
  have hprodval (s : Finset (Fin r)) :
      IsDiscreteValuationRing.addVal A (∏ i ∈ s, c i) =
        ∑ i ∈ s, IsDiscreteValuationRing.addVal A (c i) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.prod_insert hi, Finset.sum_insert hi,
          IsDiscreteValuationRing.addVal_mul, ih]
  have hcval (i : Fin r) :
      IsDiscreteValuationRing.addVal A (c i) = (a i : ℕ∞) := by
    rw [hcu i, IsDiscreteValuationRing.addVal_def' (u i) hϖ (a i)]
  have hdetval :
      IsDiscreteValuationRing.addVal A (LinearMap.det T) =
        ∑ i : Fin r, (a i : ℕ∞) := by
    have h := congrArg (IsDiscreteValuationRing.addVal A) hdetprod
    rw [IsDiscreteValuationRing.addVal_mul, hunitval, add_zero,
      hprodval (Finset.univ : Finset (Fin r))] at h
    simpa [hcval] using h
  exact hlength.trans hdetval.symm

/- The determinant of multiplication is the field norm; the equality is
   recorded in the canonical linear-algebra orientation. -/
theorem chapter_multiplication_determinant_eq_norm
    (K E : Type*) [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] (x : E) :
    Algebra.norm K x = LinearMap.det (Algebra.lmul K E x) := by
  rfl

section LatticeNorm

variable {K E : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
  [Field E] [Algebra K E] [Module A E] [IsScalarTower A K E]
  [FiniteDimensional K E]

/-- Book §5.4: multiplication by an element of a finite field extension has
the field norm as the determinant of its restriction to any full stable
`A`-lattice. -/
theorem chapter_lattice_multiplication_determinant_eq_norm
    (M : Submodule A E) [Module.Free A M] [Module.Finite A M]
    (hM : chapterFullLattice (A := A) (K := K) M) (x : E)
    (T : M →ₗ[A] M)
    (hT : ∀ y : M, (T y : E) = x * (y : E)) :
    algebraMap A K (LinearMap.det T) = Algebra.norm K x := by
  classical
  let r := Module.finrank A M
  let b : Module.Basis (Fin r) A M := Module.finBasis A M
  have hbA : LinearIndependent A (fun i : Fin r => (b i : E)) := by
    change LinearIndependent A (M.subtype ∘ b)
    exact b.linearIndependent.map' M.subtype M.ker_subtype
  have hbspanK :
      Submodule.span K (Set.range (fun i : Fin r => (b i : E))) = (⊤ : Submodule K E) := by
    apply top_unique
    rw [← hM.2]
    apply Submodule.span_le.2
    intro x hx
    have hx' : (⟨x, hx⟩ : M) ∈ Submodule.span A (Set.range b) := by
      rw [b.span_eq]
      trivial
    have hmapspan : ∀ y : M, y ∈ Submodule.span A (Set.range b) →
        (y : E) ∈ Submodule.span K (Set.range (fun i : Fin r => (b i : E))) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem z hz =>
          obtain ⟨i, rfl⟩ := hz
          exact Submodule.subset_span ⟨i, rfl⟩
      | zero => exact Submodule.zero_mem _
      | add z w hz hw hzp hwp => exact Submodule.add_mem _ hzp hwp
      | smul a z hz hzp =>
          change a • (z : E) ∈
            Submodule.span K (Set.range (fun i : Fin r => (b i : E)))
          rw [← IsScalarTower.algebraMap_smul (A := K) a (z : E)]
          exact Submodule.smul_mem _ (algebraMap A K a) hzp
    exact hmapspan ⟨x, hx⟩ hx'
  have hbK : LinearIndependent K (fun i : Fin r => (b i : E)) :=
    (LinearIndependent.iff_fractionRing A K).mp hbA
  let e : Module.Basis (Fin r) K E := Module.Basis.mk hbK hbspanK.ge
  have heapply (i : Fin r) : e i = (b i : E) := by
    exact Module.Basis.mk_apply hbK hbspanK.ge i
  let P : Submodule A E :=
    Submodule.span A (Set.range (fun i : Fin r => (e i : E)))
  let bP : Module.Basis (Fin r) A P := e.restrictScalars A
  let q : M ≃ₗ[A] P := b.equiv bP (Equiv.refl (Fin r))
  have hq_basis (i : Fin r) : (q (b i) : E) = (b i : E) := by
    rw [Module.Basis.equiv_apply]
    change (bP i : E) = (b i : E)
    rw [Module.Basis.restrictScalars_apply]
    exact heapply i
  have hqE :
      P.subtype.comp q.toLinearMap = M.subtype := by
    apply b.ext
    intro i
    exact hq_basis i
  have hq (m : M) : (q m : E) = (m : E) := by
    exact LinearMap.congr_fun hqE m
  have hqsymm (y : P) : ((q.symm y : M) : E) = (y : E) := by
    have := hq (q.symm y)
    simpa using this.symm
  let TP : P →ₗ[A] P :=
    (q : M →ₗ[A] P) ∘ₗ T ∘ₗ (q.symm : P →ₗ[A] M)
  have hTP (y : P) : (TP y : E) = x * (y : E) := by
    change (q (T (q.symm y)) : E) = x * (y : E)
    rw [hq, hT, hqsymm]
  have hdetq :
      LinearMap.det TP = LinearMap.det T := by
    exact LinearMap.det_conj T q
  have hmatrix :
      (algebraMap A K).mapMatrix
          (bP.toMatrix (fun i : Fin r => TP (bP i))) =
        e.toMatrix (fun i : Fin r => Algebra.lmul K E x (e i)) := by
    have h := Module.Basis.restrictScalars_toMatrix A e
      (fun i : Fin r => TP (bP i))
    calc
      (algebraMap A K).mapMatrix
          (bP.toMatrix (fun i : Fin r => TP (bP i))) =
          e.toMatrix (fun i : Fin r => (TP (bP i) : E)) := by
            simpa only [bP] using h
      _ = e.toMatrix (fun i : Fin r => x * (e i)) := by
            congr 1
            funext i
            rw [hTP, Module.Basis.restrictScalars_apply]
      _ = e.toMatrix (fun i : Fin r => Algebra.lmul K E x (e i)) := by
            congr 1
  have hdetP :
      bP.det (fun i : Fin r => TP (bP i)) = LinearMap.det TP := by
    change bP.det (TP ∘ bP) = _
    rw [Module.Basis.det_comp, Module.Basis.det_self, mul_one]
  have hdetE :
      e.det (fun i : Fin r => Algebra.lmul K E x (e i)) =
        LinearMap.det (Algebra.lmul K E x) := by
    change e.det ((Algebra.lmul K E x) ∘ e) = _
    rw [Module.Basis.det_comp, Module.Basis.det_self, mul_one]
  have hdetbase :
      algebraMap A K (LinearMap.det TP) =
        LinearMap.det (Algebra.lmul K E x) := by
    calc
      algebraMap A K (LinearMap.det TP) =
          algebraMap A K (bP.det (fun i : Fin r => TP (bP i))) := by
            rw [hdetP]
      _ = Matrix.det
          ((algebraMap A K).mapMatrix
            (bP.toMatrix (fun i : Fin r => TP (bP i)))) := by
            rw [Module.Basis.det_apply, RingHom.map_det]
      _ = Matrix.det
          (e.toMatrix (fun i : Fin r => Algebra.lmul K E x (e i))) := by
            rw [hmatrix]
      _ = e.det (fun i : Fin r => Algebra.lmul K E x (e i)) := by
            rw [Module.Basis.det_apply]
      _ = LinearMap.det (Algebra.lmul K E x) := hdetE
  have hnormdet :
      Algebra.norm K x = LinearMap.det (Algebra.lmul K E x) := by
    let c : Module.Basis (Fin (Module.finrank K E)) K E :=
      Module.finBasis K E
    rw [Algebra.norm_eq_matrix_det c x, Algebra.leftMulMatrix_apply,
      LinearMap.det_toMatrix]
  calc
    algebraMap A K (LinearMap.det T) =
        algebraMap A K (LinearMap.det TP) := by rw [hdetq]
    _ = LinearMap.det (Algebra.lmul K E x) := hdetbase
    _ = Algebra.norm K x := hnormdet.symm

end LatticeNorm

end FilteredModulesAndElementaryDivisors

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter05
