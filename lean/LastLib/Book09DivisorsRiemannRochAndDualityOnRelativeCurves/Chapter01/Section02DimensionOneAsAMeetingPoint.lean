import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Field.ULift
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Topology.LocallyConstant.Basic
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01.Section01TheAbsoluteAndRelativeSettings

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open scoped AlgebraicGeometry BigOperators

universe u v

/-! ### Codimension one and local equations -/

def chapter01CodimensionOnePoint (X : Scheme.{u}) (x : X) : Prop :=
  Order.coheight x = 1

def chapter01PrincipalIdealAt {R : Type u} [CommRing R] (a : R) : Ideal R :=
  Ideal.span ({a} : Set R)

def chapter01SingleEquationSubspace {R : Type u} [CommRing R] (a : R) : Type u :=
  R ⧸ chapter01PrincipalIdealAt a

def chapter01RegularCurveAt (X : Scheme.{u}) (x : X) : Prop :=
  IsRegularLocalRing (X.presheaf.stalk x)

def chapter01DVRAt (X : Scheme.{u}) (x : X)
    [IsDomain (X.presheaf.stalk x)] : Prop :=
  IsDiscreteValuationRing (X.presheaf.stalk x)

theorem chapter01_regular_codimensionOne_isDVR
    {X : Scheme.{u}} (x : X) (hregular : chapter01RegularCurveAt X x)
    (hcodim : chapter01CodimensionOnePoint X x)
    [IsDomain (X.presheaf.stalk x)] :
    chapter01DVRAt X x := by
  change IsRegularLocalRing (X.presheaf.stalk x) at hregular
  change Order.coheight x = 1 at hcodim
  have hdim : ringKrullDim (X.presheaf.stalk x) = 1 := by
    simpa only [ringKrullDim_stalk_eq_coheight] using
      (show (↑(Order.coheight x) : WithBot ℕ∞) = 1 by
        exact_mod_cast hcodim)
  have hcot := (IsRegularLocalRing.iff_finrank_cotangentSpace _).mp hregular
  rw [hdim] at hcot
  apply (IsLocalRing.finrank_CotangentSpace_eq_one_iff).mp
  exact_mod_cast hcot

theorem chapter01_normal_oneDimensional_local_isDVR
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsDomain R] (hnormal : IsIntegrallyClosed R)
    (hdim : ringKrullDim R = 1) : IsDiscreteValuationRing R := by
  have hdimLE : Ring.KrullDimLE 1 R := by
    rw [Ring.krullDimLE_iff]
    exact hdim.le
  have hDimOne : Ring.DimensionLEOne R :=
    ⟨fun {p} hp hprime =>
      @Ideal.IsPrime.isMaximal_of_ne_bot R _ _ hdimLE p hprime hp⟩
  have hDed : IsDedekindDomain R :=
    (isDedekindDomain_iff (A := R) (FractionRing R)).mpr
      ⟨inferInstance, inferInstance, hDimOne,
        fun {_} hx => (isIntegrallyClosed_iff (FractionRing R)).mp hnormal hx⟩
  have hnf : ¬ IsField R := by
    intro hF
    exact one_ne_zero (by rw [← hdim, ringKrullDim_eq_zero_of_isField hF])
  exact ((IsDiscreteValuationRing.TFAE R hnf).out 0 2).mpr hDed

/-! The cusp is a convenient explicit singular curve for the warning below.  These
helpers are kept private because they only witness the existential statement. -/

private def chapter01CuspRelation (k : Type u) [CommRing k] :
    Ideal (MvPolynomial (Fin 2) k) :=
  Ideal.span ({MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3} :
    Set (MvPolynomial (Fin 2) k))

private abbrev Chapter01CuspRing (k : Type u) [CommRing k] :=
  MvPolynomial (Fin 2) k ⧸ chapter01CuspRelation k

private def chapter01CuspQuotientMap (k : Type u) [CommRing k] :
    MvPolynomial (Fin 2) k →+* Chapter01CuspRing k :=
  Ideal.Quotient.mk (chapter01CuspRelation k)

private def chapter01CuspX (k : Type u) [CommRing k] : Chapter01CuspRing k :=
  chapter01CuspQuotientMap k (MvPolynomial.X 0)

private def chapter01CuspY (k : Type u) [CommRing k] : Chapter01CuspRing k :=
  chapter01CuspQuotientMap k (MvPolynomial.X 1)

private def chapter01CuspMaximalIdeal (k : Type u) [CommRing k] :
    Ideal (Chapter01CuspRing k) :=
  (Ideal.span ({MvPolynomial.X 0, MvPolynomial.X 1} :
    Set (MvPolynomial (Fin 2) k))).map (chapter01CuspQuotientMap k)

private theorem chapter01_cusp_ring_isDomain (k : Type u) [Field k] :
    IsDomain (Chapter01CuspRing k) := by
  classical
  let A := Polynomial k
  let K := FractionRing A
  have hnot_square : ∀ b : K, b ^ 2 ≠ algebraMap A K (Polynomial.X ^ 3) := by
    intro b hb
    obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective A b
    have hs0 : s ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hs
    have hsK : algebraMap A K s ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
    have hb0 :
        (algebraMap A K a) ^ 2 / (algebraMap A K s) ^ 2 =
          algebraMap A K (Polynomial.X ^ 3) := by
      rw [← div_pow]
      exact hb
    have hb' :
        (algebraMap A K a) ^ 2 =
          algebraMap A K (Polynomial.X ^ 3) * (algebraMap A K s) ^ 2 :=
      (div_eq_iff (pow_ne_zero 2 hsK)).mp hb0
    have hbpoly : a ^ 2 = Polynomial.X ^ 3 * s ^ 2 := by
      apply (IsFractionRing.injective A K)
      calc
        algebraMap A K (a ^ 2) = (algebraMap A K a) ^ 2 := by rw [map_pow]
        _ = algebraMap A K (Polynomial.X ^ 3) * (algebraMap A K s) ^ 2 := hb'
        _ = algebraMap A K (Polynomial.X ^ 3 * s ^ 2) := by
          simp only [map_mul, map_pow]
    have ha : a ≠ 0 := by
      intro ha
      subst a
      have hzero : Polynomial.X ^ 3 * s ^ 2 = 0 := by
        simpa only [zero_pow (by norm_num : (2 : Nat) ≠ 0)] using hbpoly.symm
      rcases mul_eq_zero.mp hzero with hX | hs2
      · exact (pow_ne_zero 3 (by simp)) hX
      · exact hs0 (eq_zero_of_pow_eq_zero hs2)
    have hdeg := congrArg Polynomial.natDegree hbpoly
    rw [Polynomial.natDegree_pow,
        Polynomial.natDegree_mul
          (pow_ne_zero 3 (by simp)) (pow_ne_zero 2 hs0)] at hdeg
    rw [Polynomial.natDegree_pow] at hdeg
    rw [Polynomial.natDegree_X] at hdeg
    rw [Polynomial.natDegree_pow] at hdeg
    omega
  let p : Polynomial (Polynomial k) :=
    Polynomial.X ^ 2 - Polynomial.C (Polynomial.X ^ 3)
  have hpK0 :=
    X_pow_sub_C_irreducible_of_prime (K := K) (p := 2)
      (a := algebraMap A K (Polynomial.X ^ 3)) Nat.prime_two hnot_square
  have hmap_p :
      (Polynomial.X ^ 2 - Polynomial.C (Polynomial.X ^ 3) :
        Polynomial (Polynomial k)).map (algebraMap A K) =
          Polynomial.X ^ 2 - Polynomial.C (algebraMap A K (Polynomial.X ^ 3)) := by
    simp
  have hpA : Irreducible p := by
    refine (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map
      (R := A) (K := K) ?_).mpr ?_
    · dsimp [p]
      exact Polynomial.monic_X_pow_sub_C _ (by norm_num)
    · change Irreducible ((Polynomial.X ^ 2 - Polynomial.C (Polynomial.X ^ 3) :
        Polynomial (Polynomial k)).map (algebraMap A K))
      rw [hmap_p]
      exact hpK0
  have hpprime : Prime p := hpA.prime
  have hJprime : (Ideal.span ({p} : Set (Polynomial (Polynomial k)))).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime hpprime
  let e := Polynomial.Bivariate.equivMvPolynomial k
  have he : e p = MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3 := by
    simp [e, p]
  have hmap :
      (Ideal.span ({p} : Set (Polynomial (Polynomial k)))).map
          (e : Polynomial (Polynomial k) →+* MvPolynomial (Fin 2) k) =
        chapter01CuspRelation k := by
    rw [chapter01CuspRelation, Ideal.map_span, Set.image_singleton]
    change Ideal.span ({e p} : Set (MvPolynomial (Fin 2) k)) =
      Ideal.span ({MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3} :
        Set (MvPolynomial (Fin 2) k))
    rw [he]
  have hIprime : (chapter01CuspRelation k).IsPrime := by
    let _ : (Ideal.span ({p} : Set (Polynomial (Polynomial k)))).IsPrime := hJprime
    rw [← hmap]
    exact Ideal.map_isPrime_of_equiv e
  rw [Ideal.Quotient.isDomain_iff_prime]
  exact hIprime

private theorem chapter01_cusp_maximalIdeal_isMaximal (k : Type u) [Field k] :
    (chapter01CuspMaximalIdeal k).IsMaximal := by
  have hM : (Ideal.span ({MvPolynomial.X 0, MvPolynomial.X 1} :
      Set (MvPolynomial (Fin 2) k))).IsMaximal := by
    rw [Ideal.isMaximal_iff]
    constructor
    · intro h1
      rw [show ({MvPolynomial.X 0, MvPolynomial.X 1} :
          Set (MvPolynomial (Fin 2) k)) =
          MvPolynomial.X '' ({0, 1} : Set (Fin 2)) by
        ext z
        constructor
        · intro hz
          rcases hz with rfl | rfl <;> simp
        · intro hz
          rcases hz with ⟨i, hi, rfl⟩
          fin_cases i <;> simp_all] at h1
      rw [MvPolynomial.mem_ideal_span_X_image] at h1
      simp at h1
    · intro J p hMJ hp hJ
      have hdiff : p - MvPolynomial.C (MvPolynomial.constantCoeff p) ∈
          Ideal.span ({MvPolynomial.X 0, MvPolynomial.X 1} :
            Set (MvPolynomial (Fin 2) k)) := by
        rw [show ({MvPolynomial.X 0, MvPolynomial.X 1} :
            Set (MvPolynomial (Fin 2) k)) =
            MvPolynomial.X '' ({0, 1} : Set (Fin 2)) by
          ext z
          constructor
          · intro hz
            rcases hz with rfl | rfl <;> simp
          · intro hz
            rcases hz with ⟨i, hi, rfl⟩
            fin_cases i <;> simp_all]
        rw [MvPolynomial.mem_ideal_span_X_image]
        intro m hm
        have hm0 : m ≠ 0 := by
          intro hm0
          subst m
          have hm' := MvPolynomial.mem_support_iff.mp hm
          change MvPolynomial.coeff 0
            (p - MvPolynomial.C (MvPolynomial.coeff 0 p)) ≠ 0 at hm'
          simp at hm'
        obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hm0
        exact ⟨i, by fin_cases i <;> simp, Finsupp.mem_support_iff.mp hi⟩
      have hc : MvPolynomial.C (MvPolynomial.constantCoeff p) ∈ J := by
        simpa [sub_sub] using J.sub_mem hJ (hMJ hdiff)
      have hcp : MvPolynomial.constantCoeff p ≠ 0 := by
        intro hcp
        apply hp
        simpa [hcp] using hdiff
      have hunit : IsUnit (MvPolynomial.C (MvPolynomial.constantCoeff p)) :=
        IsUnit.map (MvPolynomial.C : k →+* MvPolynomial (Fin 2) k) hcp.isUnit
      rw [J.eq_top_of_isUnit_mem hc hunit]
      exact Submodule.mem_top
  let _ : (Ideal.span ({MvPolynomial.X 0, MvPolynomial.X 1} :
      Set (MvPolynomial (Fin 2) k))).IsMaximal := hM
  have hker : RingHom.ker (chapter01CuspQuotientMap k) ≤
      Ideal.span ({MvPolynomial.X 0, MvPolynomial.X 1} :
        Set (MvPolynomial (Fin 2) k)) := by
    change RingHom.ker (Ideal.Quotient.mk (chapter01CuspRelation k)) ≤
      Ideal.span ({MvPolynomial.X 0, MvPolynomial.X 1} :
        Set (MvPolynomial (Fin 2) k))
    rw [Ideal.mk_ker]
    exact Ideal.span_le.2 (by
      intro z hz
      rcases hz with rfl
      let M := Ideal.span ({MvPolynomial.X 0, MvPolynomial.X 1} :
        Set (MvPolynomial (Fin 2) k))
      have hx : MvPolynomial.X 0 ∈ M := Ideal.subset_span (by simp)
      have hy : MvPolynomial.X 1 ∈ M := Ideal.subset_span (by simp)
      exact sub_mem
        (by simpa [pow_two] using mul_mem hy hy)
        (by simpa [pow_succ, pow_two] using mul_mem (mul_mem hx hx) hx))
  simpa [chapter01CuspMaximalIdeal] using
    (Ideal.IsMaximal.map_of_surjective_of_ker_le
      (f := chapter01CuspQuotientMap k) Ideal.Quotient.mk_surjective hker)

private instance chapter01CuspMaximalIdeal_isPrime (k : Type u) [Field k] :
    (chapter01CuspMaximalIdeal k).IsPrime :=
  (chapter01_cusp_maximalIdeal_isMaximal k).isPrime

private instance chapter01CuspMaximalIdeal_isMaximal (k : Type u) [Field k] :
    (chapter01CuspMaximalIdeal k).IsMaximal :=
  chapter01_cusp_maximalIdeal_isMaximal k

private abbrev Chapter01CuspLocalRing (k : Type u) [Field k] :=
  Localization.AtPrime (chapter01CuspMaximalIdeal k)

private theorem chapter01_cusp_local_maximalIdeal_not_principal (k : Type u) [Field k] :
    ¬ (IsLocalRing.maximalIdeal (Chapter01CuspLocalRing k)).IsPrincipal := by
  classical
  let R := Chapter01CuspRing k
  let S := Chapter01CuspLocalRing k
  let q : MvPolynomial (Fin 2) k →+* R := chapter01CuspQuotientMap k
  let l : R →+* S := algebraMap R S
  let x : S := l (chapter01CuspX k)
  let y : S := l (chapter01CuspY k)
  have hlocal :
      IsLocalRing.maximalIdeal S =
        Ideal.map l (chapter01CuspMaximalIdeal k) := by
    rw [IsLocalization.AtPrime.map_eq_maximalIdeal
      (chapter01CuspMaximalIdeal k) S]
  have hspan : IsLocalRing.maximalIdeal S = Ideal.span ({x, y} : Set S) := by
    rw [hlocal]
    change Ideal.map l
        ((Ideal.span ({MvPolynomial.X 0, MvPolynomial.X 1} :
          Set (MvPolynomial (Fin 2) k))).map q) = _
    rw [Ideal.map_map, Ideal.map_span, Set.image_pair]
    rfl
  let f : MvPolynomial (Fin 2) k →+* DualNumber k :=
    MvPolynomial.eval₂Hom (algebraMap k (DualNumber k))
      (fun i => if i = 0 then DualNumber.eps else 0)
  have hfX0 : f (MvPolynomial.X 0) = (DualNumber.eps : DualNumber k) := by
    simp [f]
  have hfX1 : f (MvPolynomial.X 1) = 0 := by
    simp [f]
  have hm0sqker :
      (Ideal.span ({MvPolynomial.X 0, MvPolynomial.X 1} :
        Set (MvPolynomial (Fin 2) k))) ^ 2 ≤ RingHom.ker f := by
    rw [pow_two, Ideal.span_pair_mul_span_pair]
    apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    all_goals
      change f _ = 0
      simp [map_mul, hfX0, hfX1]
  have heps : (DualNumber.eps : DualNumber k) ≠ 0 := by
    intro h
    have hs := congrArg TrivSqZeroExt.snd h
    simp at hs
  have hX0not : MvPolynomial.X 0 ∉
      (Ideal.span ({MvPolynomial.X 0, MvPolynomial.X 1} :
        Set (MvPolynomial (Fin 2) k))) ^ 2 := by
    intro h
    have hfzero := hm0sqker h
    rw [RingHom.mem_ker] at hfzero
    exact heps (hfX0.symm.trans hfzero)
  let : IsDomain R := chapter01_cusp_ring_isDomain k
  have hqX : chapter01CuspX k ≠ 0 := by
    intro hx
    change chapter01CuspQuotientMap k (MvPolynomial.X 0) = 0 at hx
    have hm : MvPolynomial.X 0 ∈ chapter01CuspRelation k :=
      Ideal.Quotient.eq_zero_iff_mem.mp hx
    rcases (Ideal.mem_span_singleton').mp hm with ⟨p, hp⟩
    have heval :=
      congrArg (MvPolynomial.eval (fun _ : Fin 2 => (1 : k))) hp
    simp [MvPolynomial.eval_mul] at heval
  have hlinj : Function.Injective l :=
    IsLocalization.injective S
      (chapter01CuspMaximalIdeal k).primeCompl_le_nonZeroDivisors
  have hx : x ≠ 0 := by
    intro hxzero
    apply hqX
    apply hlinj
    simpa [x, l] using hxzero
  let m₀ : Ideal (MvPolynomial (Fin 2) k) :=
    Ideal.span ({MvPolynomial.X 0, MvPolynomial.X 1} :
      Set (MvPolynomial (Fin 2) k))
  have hkerq : RingHom.ker q ≤ m₀ ^ 2 := by
    change RingHom.ker (Ideal.Quotient.mk (chapter01CuspRelation k)) ≤ m₀ ^ 2
    rw [Ideal.mk_ker]
    rw [chapter01CuspRelation]
    apply Ideal.span_le.2
    intro z hz
    rcases hz with rfl
    have hX0 : MvPolynomial.X 0 ∈ m₀ := Ideal.subset_span (by simp)
    have hX1 : MvPolynomial.X 1 ∈ m₀ := Ideal.subset_span (by simp)
    have hX1sq : MvPolynomial.X 1 ^ 2 ∈ m₀ ^ 2 := by
      simpa [pow_two] using Ideal.mul_mem_mul hX1 hX1
    have hX0sq : MvPolynomial.X 0 ^ 2 ∈ m₀ ^ 2 := by
      simpa [pow_two] using Ideal.mul_mem_mul hX0 hX0
    have hX0cu : MvPolynomial.X 0 ^ 3 ∈ m₀ ^ 2 := by
      simpa [pow_succ, pow_two, mul_comm, mul_left_comm, mul_assoc] using
        (m₀ ^ 2).mul_mem_left (MvPolynomial.X 0) hX0sq
    exact sub_mem hX1sq hX0cu
  have hmRpow :
      chapter01CuspMaximalIdeal k ^ 2 = Ideal.map q (m₀ ^ 2) := by
    change (m₀.map q) ^ 2 = _
    rw [← Ideal.map_pow]
  have hqXnot : chapter01CuspX k ∉ chapter01CuspMaximalIdeal k ^ 2 := by
    intro h
    rw [hmRpow] at h
    have hpre : MvPolynomial.X 0 ∈
        (Ideal.map q (m₀ ^ 2)).comap q := h
    rw [Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective] at hpre
    rcases Submodule.mem_sup.mp hpre with ⟨u, hu, v, hv, huv⟩
    have hv' : v ∈ RingHom.ker q := hv
    apply hX0not
    have hsum : u + v ∈ m₀ ^ 2 := add_mem hu (hkerq hv')
    convert hsum using 1
    exact huv.symm
  have hxnot : x ∉ (IsLocalRing.maximalIdeal S) ^ 2 := by
    intro h
    have hx' : l (chapter01CuspX k) ∈
        (IsLocalRing.maximalIdeal S) ^ 2 := by
      simpa [x] using h
    have hunder :
        ((IsLocalRing.maximalIdeal S) ^ 2).under R =
          chapter01CuspMaximalIdeal k ^ 2 :=
      IsLocalization.AtPrime.under_maximalIdeal_pow
        (chapter01CuspMaximalIdeal k) S 2
    have hbase : chapter01CuspX k ∈ chapter01CuspMaximalIdeal k ^ 2 := by
      rw [← hunder]
      exact hx'
    exact hqXnot hbase
  rintro ⟨a, ha⟩
  have hxm : x ∈ IsLocalRing.maximalIdeal S := by
    rw [hspan]
    exact Ideal.subset_span (by simp)
  have hxa : x ∈ Ideal.span ({a} : Set S) := by
    change x ∈ S ∙ a
    rw [← ha]
    exact hxm
  obtain ⟨r, hr⟩ := (Ideal.mem_span_singleton').mp hxa
  have hrm : r ∉ IsLocalRing.maximalIdeal S := by
    intro hrm
    have ham : a ∈ IsLocalRing.maximalIdeal S := by
      rw [ha]
      exact Ideal.subset_span (by simp)
    apply hxnot
    rw [← hr]
    simpa [pow_two] using Ideal.mul_mem_mul hrm ham
  have hru : IsUnit r := IsLocalRing.notMem_maximalIdeal.mp hrm
  have hax : a ∈ Ideal.span ({x} : Set S) := by
    rw [← Ideal.unit_mul_mem_iff_mem _ hru]
    rw [hr]
    exact Ideal.subset_span (Set.mem_singleton x)
  have hspanx : IsLocalRing.maximalIdeal S = Ideal.span ({x} : Set S) := by
    apply le_antisymm
    · rw [ha]
      exact Ideal.span_le.2 (by
        intro z hz
        rcases hz with rfl
        exact hax)
    · exact Ideal.span_le.2 (by
        intro z hz
        rcases hz with rfl
        exact hxm)
  have hyx : y ∈ Ideal.span ({x} : Set S) := by
    rw [← hspanx, hspan]
    exact Ideal.subset_span (by simp)
  obtain ⟨z, hz⟩ := (Ideal.mem_span_singleton').mp hyx
  have hrel0 : (chapter01CuspY k) ^ 2 - (chapter01CuspX k) ^ 3 = 0 := by
    change q (MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (by simp))
  have hrel : y ^ 2 = x ^ 3 := by
    have hrel' := congrArg l hrel0
    have hrel'' : y ^ 2 - x ^ 3 = 0 := by
      simpa [x, y] using hrel'
    exact sub_eq_zero.mp hrel''
  have hsq : z ^ 2 = x := by
    have hzy : (z * x) ^ 2 = x ^ 3 := by
      calc
        (z * x) ^ 2 = y ^ 2 := by rw [hz]
        _ = x ^ 3 := hrel
    have hzy' : x ^ 2 * z ^ 2 = x ^ 2 * x := by
      calc
        x ^ 2 * z ^ 2 = (z * x) ^ 2 := by ring
        _ = x ^ 3 := hzy
        _ = x ^ 2 * x := by ring
    exact mul_left_cancel₀ (pow_ne_zero 2 hx) hzy'
  have hxnotunit : ¬ IsUnit x := by
    rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]
    exact hxm
  have hzm : z ∈ IsLocalRing.maximalIdeal S := by
    by_contra hzn
    have hzu : IsUnit z := IsLocalRing.notMem_maximalIdeal.mp hzn
    apply hxnotunit
    rw [← hsq]
    exact hzu.pow 2
  apply hxnot
  have hzsq : z ^ 2 ∈ (IsLocalRing.maximalIdeal S) ^ 2 := by
    simpa [pow_two] using Ideal.mul_mem_mul hzm hzm
  simpa [hsq] using hzsq

private theorem chapter01_cusp_maximalIdeal_height (k : Type u) [Field k] :
    (chapter01CuspMaximalIdeal k).height = 1 := by
  classical
  let : IsDomain (Chapter01CuspRing k) := chapter01_cusp_ring_isDomain k
  have hr :
      (MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3 :
        MvPolynomial (Fin 2) k) ∈ nonZeroDivisors (MvPolynomial (Fin 2) k) := by
    apply mem_nonZeroDivisors_of_ne_zero
    apply sub_ne_zero.mpr
    intro h
    have hd := congrArg MvPolynomial.totalDegree h
    simp at hd
  have hq := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr
  have hp : ringKrullDim (MvPolynomial (Fin 2) k) = 2 := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing]
    norm_num
  have hq' : ringKrullDim (Chapter01CuspRing k) + 1 ≤ 2 := by
    change ringKrullDim (MvPolynomial (Fin 2) k ⧸
      Ideal.span {MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3}) + 1 ≤ 2
    rw [← hp]
    exact hq
  have hdim : ringKrullDim (Chapter01CuspRing k) ≤ 1 := by
    have htwo : (2 : WithBot ℕ∞) = 1 + 1 := by norm_num
    rw [htwo] at hq'
    exact (ENat.WithBot.add_le_add_one_right_iff).mp hq'
  have hXne : chapter01CuspX k ≠ 0 := by
    intro hx
    change chapter01CuspQuotientMap k (MvPolynomial.X 0) = 0 at hx
    have hm : MvPolynomial.X 0 ∈ chapter01CuspRelation k :=
      Ideal.Quotient.eq_zero_iff_mem.mp hx
    rcases (Ideal.mem_span_singleton').mp hm with ⟨q, hq⟩
    have heval := congrArg
      (MvPolynomial.eval (fun _ : Fin 2 => (1 : k))) hq
    simp [MvPolynomial.eval_mul] at heval
  have hMnebot : chapter01CuspMaximalIdeal k ≠ ⊥ := by
    intro hM
    have hxM : chapter01CuspX k ∈ chapter01CuspMaximalIdeal k := by
      rw [chapter01CuspMaximalIdeal]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span (by simp))
    have : chapter01CuspX k = 0 := by simpa [hM] using hxM
    exact hXne this
  have hle : (chapter01CuspMaximalIdeal k).height ≤
      ringKrullDim (Chapter01CuspRing k) :=
    Ideal.height_le_ringKrullDim_of_isPrime
  have hle1' : (↑(chapter01CuspMaximalIdeal k).height : WithBot ℕ∞) ≤
      (1 : WithBot ℕ∞) := hle.trans hdim
  have hle1 : (chapter01CuspMaximalIdeal k).height ≤ 1 :=
    WithBot.coe_le_coe.mp hle1'
  have hnezero : (chapter01CuspMaximalIdeal k).height ≠ 0 := by
    intro hzero
    exact hMnebot ((Ideal.height_eq_zero_iff_eq_bot).mp hzero)
  have hge1 : 1 ≤ (chapter01CuspMaximalIdeal k).height :=
    (Order.one_le_iff_ne_zero).2 hnezero
  exact le_antisymm hle1 hge1

private theorem chapter01_cusp_localRing_dim (k : Type u) [Field k] :
    ringKrullDim (Chapter01CuspLocalRing k) = 1 := by
  calc
    ringKrullDim (Chapter01CuspLocalRing k) =
        (↑(chapter01CuspMaximalIdeal k).height : WithBot ℕ∞) :=
      IsLocalization.AtPrime.ringKrullDim_eq_height
        (chapter01CuspMaximalIdeal k) (Chapter01CuspLocalRing k)
    _ = 1 := by
      exact_mod_cast chapter01_cusp_maximalIdeal_height k

private theorem chapter01_cusp_local_scheme_pureDimensionOne (k : Type u) [Field k] :
    Chapter01PureDimensionOne
      (Spec (CommRingCat.of (Chapter01CuspLocalRing k))) := by
  classical
  let S := Chapter01CuspLocalRing k
  let : IsDomain (Chapter01CuspRing k) := chapter01_cusp_ring_isDomain k
  let : IsDomain S := inferInstance
  intro Z
  have hZ : Z.1 = (Set.univ : Set (Spec (CommRingCat.of S))) := by
    have hZmem : Z.1 ∈ irreducibleComponents (Spec (CommRingCat.of S)) := Z.2
    simpa [irreducibleComponents_eq_singleton] using hZmem
  rw [hZ]
  have heq : topologicalKrullDim (Set.univ : Set (Spec (CommRingCat.of S))) =
      topologicalKrullDim (Spec (CommRingCat.of S)) :=
    IsHomeomorph.topologicalKrullDim_eq _
      (Homeomorph.Set.univ (Spec (CommRingCat.of S))).isHomeomorph
  rw [heq]
  change topologicalKrullDim (PrimeSpectrum S) = 1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact chapter01_cusp_localRing_dim k

theorem chapter01_regular_local_ring_is_factorial
    {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] :
    UniqueFactorizationMonoid R := by
  sorry

/-! The order, cycle, local-equation, and pole descriptions are held together by a
  reusable dictionary rather than by silently identifying Weil and Cartier divisors
  on singular curves. -/
structure Chapter01CodimensionOneDictionary (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] where
  order : {x : X // chapter01CodimensionOnePoint X x} → ℤ
  cycle : Chapter01Divisor X
  localEquation :
    ∀ x : X, chapter01CodimensionOnePoint X x → Chapter01RationalFunction X
  localEquation_ne_zero :
    ∀ (x : X) (hx : chapter01CodimensionOnePoint X x),
      localEquation x hx ≠ 0
  localEquation_order :
    ∀ (x : X) (hx : chapter01CodimensionOnePoint X x),
      chapter01OrderAt x (localEquation x hx) = order ⟨x, hx⟩
  polePrescription : ∀ x : X, chapter01CodimensionOnePoint X x → ℤ
  order_eq_cycleCoefficient :
    ∀ (x : X) (hx : chapter01CodimensionOnePoint X x),
      cycle x = order ⟨x, hx⟩
  order_eq_polePrescription :
    ∀ (x : X) (hx : chapter01CodimensionOnePoint X x),
      order ⟨x, hx⟩ = polePrescription x hx

def chapter01DivisorOfOrder
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (D : Chapter01CodimensionOneDictionary X) : Chapter01Divisor X :=
  D.cycle

def chapter01FiniteExceptionalOrderData {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X]
    (f : Chapter01RationalFunction X) : Prop :=
  ∃ E : Finset X, ∀ x : X, x ∉ E → chapter01OrderZeroAt f x

theorem chapter01_order_is_zero_away_from_exceptional
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (f : Chapter01RationalFunction X) (_hf : f ≠ 0)
    (hE : (chapter01ExceptionalPoints f).Finite) :
    chapter01FiniteExceptionalOrderData f := by
  classical
  refine ⟨hE.toFinset, ?_⟩
  intro x hx
  by_contra hzero
  apply hx
  exact hE.mem_toFinset.mpr hzero

/-! Codimension-one cycles need not be Cartier on a singular curve, and normality in
  higher dimension does not force every height-one prime to be principal. -/
def chapter01CodimensionOneCycleNotLocallyPrincipal (X : Scheme.{u}) : Prop :=
  ∃ x : X, Chapter01PureDimensionOne X ∧ chapter01CodimensionOnePoint X x ∧
    chapter01ClosedPoint X x ∧ IsNoetherianRing (X.presheaf.stalk x) ∧
    ¬ chapter01RegularCurveAt X x ∧
    ¬ (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).IsPrincipal

def chapter01DimensionAtLeastTwo (X : Scheme.{u}) : Prop :=
  ∃ Z : irreducibleComponents X, 2 ≤ topologicalKrullDim Z.1

def chapter01HeightOnePrimeIdeal {R : Type u} [CommRing R] (I : Ideal R) : Prop :=
  I.IsPrime ∧ Order.height I = 1

def chapter01NormalHigherDimensionalNonCartierExample : Prop :=
  ∃ (X : Scheme.{u}) (x : X) (I : Ideal (X.presheaf.stalk x)),
    chapter01DimensionAtLeastTwo X ∧
      IsNoetherianRing (X.presheaf.stalk x) ∧
      IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) ∧
    ¬ chapter01RegularCurveAt X x ∧
      chapter01HeightOnePrimeIdeal I ∧ ¬ I.IsPrincipal

theorem chapter01_singular_curve_cycle_need_not_be_Cartier :
    ∃ (X : Scheme.{u}), chapter01CodimensionOneCycleNotLocallyPrincipal X := by
  classical
  let S := Chapter01CuspLocalRing (k := ULift.{u} ℚ)
  let X : Scheme := Spec (CommRingCat.of S)
  let x : X := IsLocalRing.closedPoint S
  let T := X.presheaf.stalk x
  have he : T ≃+* S := by
    simpa [X, x, T] using
      (stalkClosedPointIso (CommRingCat.of S)).commRingCatIsoToRingEquiv
  have hstalkdim : ringKrullDim T = 1 := by
    calc
      ringKrullDim T = ringKrullDim S :=
        ringKrullDim_eq_of_ringEquiv he
      _ = 1 := chapter01_cusp_localRing_dim (k := ULift.{u} ℚ)
  have hNoeth : IsNoetherianRing T := by
    exact isNoetherianRing_of_ringEquiv S he.symm
  let : IsNoetherianRing T := hNoeth
  have hnotprincipal :
      ¬ (IsLocalRing.maximalIdeal T).IsPrincipal := by
    intro h
    refine (chapter01_cusp_local_maximalIdeal_not_principal
      (k := ULift.{u} ℚ)) ?_
    rcases h with ⟨a, ha⟩
    refine ⟨he a, ?_⟩
    apply le_antisymm
    · intro z hz
      have hzT : he.symm z ∈ IsLocalRing.maximalIdeal T := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hzunit
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hz
        apply hz
        simpa using IsUnit.map he.toMonoidHom hzunit
      have hza : he.symm z ∈ Ideal.span ({a} : Set T) := by
        change he.symm z ∈ (↑T) ∙ a
        rw [← ha]
        exact hzT
      obtain ⟨r, hr⟩ := (Ideal.mem_span_singleton').mp hza
      apply Ideal.mem_span_singleton'.mpr
      refine ⟨he r, ?_⟩
      simpa using congrArg he hr
    · intro z hz
      rw [Ideal.mem_span_singleton'] at hz
      obtain ⟨r, hr⟩ := hz
      have haT : a ∈ IsLocalRing.maximalIdeal T := by
        rw [ha]
        exact Ideal.subset_span (Set.mem_singleton a)
      have haS : he a ∈ IsLocalRing.maximalIdeal S := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro haunit
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at haT
        apply haT
        simpa using IsUnit.map he.symm.toMonoidHom haunit
      rw [← hr]
      exact (IsLocalRing.maximalIdeal S).mul_mem_left r haS
  have hnotregular : ¬ chapter01RegularCurveAt X x := by
    intro hregular
    change IsRegularLocalRing T at hregular
    have hcot :=
      (IsRegularLocalRing.iff_finrank_cotangentSpace _).mp hregular
    rw [hstalkdim] at hcot
    have hcot' :
        Module.finrank (IsLocalRing.ResidueField T)
            (IsLocalRing.CotangentSpace T) = 1 := by
      exact_mod_cast hcot
    have hprincipal :=
      (IsLocalRing.finrank_cotangentSpace_le_one_iff
        (R := T)).mp (le_of_eq hcot')
    exact hnotprincipal hprincipal
  have hcodim : chapter01CodimensionOnePoint X x := by
    change Order.coheight x = 1
    have hdim' : (↑(Order.coheight x) : WithBot ℕ∞) = 1 := by
      simpa only [ringKrullDim_stalk_eq_coheight, T] using hstalkdim
    exact_mod_cast hdim'
  have hclosed : chapter01ClosedPoint X x := by
    change IsClosed ({x} : Set X)
    change @IsClosed (PrimeSpectrum S) PrimeSpectrum.zariskiTopology
      {IsLocalRing.closedPoint S}
    exact IsLocalRing.isClosed_singleton_closedPoint S
  have hpure : Chapter01PureDimensionOne X := by
    simpa [X] using
      chapter01_cusp_local_scheme_pureDimensionOne (k := ULift.{u} ℚ)
  refine ⟨X, x, hpure, hcodim, hclosed, hNoeth, hnotregular, hnotprincipal⟩

theorem chapter01_normal_higher_dimensional_prime_need_not_be_Cartier :
    chapter01NormalHigherDimensionalNonCartierExample := by
  sorry

/-! ### Two-term cohomology and duality -/

def chapter01CohomologyGroup {X : Scheme.{u}} (F : X.Modules) (i : ℕ) :
    AddCommGrpCat.{u + 1} :=
  chapter04Cohomology F i

def chapter01CohomologyVanishesAboveOne {X : Scheme.{u}} (F : X.Modules) : Prop :=
  ∀ i, 2 ≤ i → chapter04CohomologyVanishes F i

/- LOCAL_DEPENDENCY_GUESS: Book 8 exposes canonical cohomology objects as
  additive groups, but the pinned API does not yet package their field-module
  structures.  This realization records a chosen compatible module structure
  and a linear finite-dimensional bridge without changing the underlying object. -/
structure Chapter01FiniteDimensionalRealization (k : Type u) [Field k]
    (G : AddCommGrpCat.{u + 1}) where
  V : Type u
  [addCommGroup : AddCommGroup V]
  [module : Module k V]
  finite : FiniteDimensional k V
  [moduleG : Module k G]
  linearEquiv : V ≃ₗ[k] G

structure Chapter01CohomologyDimensions (k : Type u) [Field k]
    (X : Scheme.{u}) where
  structureMap : X ⟶ Spec (CommRingCat.of k)
  realization :
    ∀ (F : X.Modules), chapter04FiniteTypeQuasiCoherent F → ∀ i : ℕ,
      Chapter01FiniteDimensionalRealization k (chapter01CohomologyGroup F i)

/- LOCAL_DEPENDENCY_GUESS: the pinned cohomology API exposes the degree-zero
  object only as an additive group.  This bridge records the canonical
  structure-sheaf comparison needed to read its dimension as the dimension of
  global functions over the chosen field structure. -/
structure Chapter01DegreeZeroCohomologyGlobalSectionsBridge
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    (D : Chapter01CohomologyDimensions k X)
    (hO : chapter04FiniteTypeQuasiCoherent
      (SheafOfModules.unit X.ringCatSheaf)) where
  structureMap_eq : D.structureMap = f
  linearEquiv :
    let V := D.realization (SheafOfModules.unit X.ringCatSheaf) hO 0
    letI := V.addCommGroup
    letI := V.module
    letI : Module k Γ(X, ⊤) :=
      Module.compHom _ (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom)
    V.V ≃ₗ[k] Γ(X, ⊤)

noncomputable def chapter01Hi {k : Type u} [Field k] {X : Scheme.{u}}
    (D : Chapter01CohomologyDimensions k X) (F : X.Modules)
    (hF : chapter04FiniteTypeQuasiCoherent F) (i : ℕ) : ℕ := by
  let V := D.realization F hF i
  letI := V.addCommGroup
  letI := V.module
  exact Module.finrank k V.V

def chapter01h0 {k : Type u} [Field k] {X : Scheme.{u}}
    (D : Chapter01CohomologyDimensions k X) (F : X.Modules)
    (hF : chapter04FiniteTypeQuasiCoherent F) : ℕ :=
  chapter01Hi D F hF 0

def chapter01h1 {k : Type u} [Field k] {X : Scheme.{u}}
    (D : Chapter01CohomologyDimensions k X) (F : X.Modules)
    (hF : chapter04FiniteTypeQuasiCoherent F) : ℕ :=
  chapter01Hi D F hF 1

def chapter01Chi {k : Type u} [Field k] {X : Scheme.{u}}
    (D : Chapter01CohomologyDimensions k X) (F : X.Modules)
    (hF : chapter04FiniteTypeQuasiCoherent F) : ℤ :=
  chapter01EulerCharacteristic (chapter01h0 D F hF) (chapter01h1 D F hF)

structure Chapter01ProperCurveCohomology (k : Type u) [Field k]
    (C : Chapter01ProperCurveOverField k) where
  dimensions : Chapter01CohomologyDimensions k C.carrier
  dimensions_structureMap : dimensions.structureMap = C.structureMap
  vanishesAboveOne :
    ∀ (F : C.carrier.Modules), chapter04FiniteTypeQuasiCoherent F →
      chapter01CohomologyVanishesAboveOne F

theorem chapter01_proper_curve_cohomology_vanishes_above_one
    {k : Type u} [Field k] {C : Chapter01ProperCurveOverField k}
    (H : Chapter01ProperCurveCohomology k C) (F : C.carrier.Modules)
    (hF : chapter04FiniteTypeQuasiCoherent F) :
    chapter01CohomologyVanishesAboveOne F := by
  exact H.vanishesAboveOne F hF

structure Chapter01FiniteDimensionalDualityPair (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (F dualF : X.Modules) where
  sheaf : X.Modules
  sheaf_eq : sheaf = F
  H0 : Type u
  [H0AddCommGroup : AddCommGroup H0]
  [H0Module : Module k H0]
  H1 : Type u
  [H1AddCommGroup : AddCommGroup H1]
  [H1Module : Module k H1]
  H0Dual : Type u
  [H0DualAddCommGroup : AddCommGroup H0Dual]
  [H0DualModule : Module k H0Dual]
  H1Dual : Type u
  [H1DualAddCommGroup : AddCommGroup H1Dual]
  [H1DualModule : Module k H1Dual]
  finiteH0 : FiniteDimensional k H0
  finiteH1 : FiniteDimensional k H1
  finiteH0Dual : FiniteDimensional k H0Dual
  finiteH1Dual : FiniteDimensional k H1Dual
  H0Represents : Nonempty (H0 ≃+ chapter01CohomologyGroup F 0)
  H1Represents : Nonempty (H1 ≃+ chapter01CohomologyGroup F 1)
  H0DualRepresents : Nonempty (H0Dual ≃+ chapter01CohomologyGroup dualF 0)
  H1DualRepresents : Nonempty (H1Dual ≃+ chapter01CohomologyGroup dualF 1)
  degreeZeroExchange : H0 ≃ₗ[k] Module.Dual k H1Dual
  degreeOneExchange : H1 ≃ₗ[k] Module.Dual k H0Dual

/- LOCAL_DEPENDENCY_GUESS: the pinned cohomology API does not yet expose the
  sheaf-level dualizing functor or its comparison with the additive cohomology
  objects, so the finite-dimensional exchange is kept as an explicit bridge. -/
structure Chapter01SerreDualityInterface (k : Type u) [Field k]
    (X : Scheme.{u}) where
  structureMap : X ⟶ Spec (CommRingCat.of k)
  dualizingSheaf : X.Modules
  dualSheaf : X.Modules → X.Modules
  dualizingSheaf_eq : dualizingSheaf = dualSheaf (SheafOfModules.unit X.ringCatSheaf)
  exchange : ∀ (F : X.Modules), chapter04FiniteTypeQuasiCoherent F →
    Chapter01FiniteDimensionalDualityPair k structureMap F (dualSheaf F)

def chapter01CohomologyIsTwoTerm {X : Scheme.{u}} (F : X.Modules) : Prop :=
  chapter01CohomologyVanishesAboveOne F

def chapter01EulerDifference (h₀ h₁ : ℕ) : ℤ :=
  (h₀ : ℤ) - h₁

theorem chapter01Euler_difference_eq_chi (h₀ h₁ : ℕ) :
    chapter01EulerDifference h₀ h₁ = chapter01EulerCharacteristic h₀ h₁ := by
  rfl

/-! ### Local/global balance and exact sequences -/

/- The weight records residue-field degrees (or another chosen numerical
   multiplicity) when an order sum is used as a degree calculation. -/
def chapter01WeightedOrderSum {X : Type u} (E : Finset X)
    (ord weight : X → ℤ) : ℤ :=
  Finset.sum E (fun x => weight x * ord x)

structure Chapter01ProperBalanceStatement (X : Type u) where
  exceptional : Finset X
  order : X → ℤ
  weight : X → ℤ
  unitAway : ∀ x : X, x ∉ exceptional → order x = 0
  globalBalance : chapter01WeightedOrderSum exceptional order weight = 0

def chapter01UncompensatedBoundaryPole {X : Type u}
    (boundary : Set X) (order : X → ℤ) : Prop :=
  ∃ x ∈ boundary, order x < 0 ∧ ∀ y, y ∉ boundary → 0 ≤ order y

def chapter01SupportedOnFiniteSet {X : Scheme.{u}} (Q : X.Modules) : Prop :=
  ∃ E : Finset X, ∀ x : X, x ∉ E → Subsingleton (Q.presheaf.stalk x)

def chapter01FiniteSupportLength {X : Scheme.{u}} (Q : X.Modules) (E : Finset X) : ℕ∞ :=
  Finset.sum E (fun x =>
    Module.length (TopCat.Presheaf.stalk (C := RingCat) X.ringCatSheaf.obj x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) Q.val.presheaf x))

structure Chapter01FiniteSupportExactSequence (X : Scheme.{u}) where
  A : X.Modules
  B : X.Modules
  Q : X.Modules
  inclusion : A ⟶ B
  quotient : B ⟶ Q
  comp_zero : inclusion ≫ quotient = 0
  exact : (ShortComplex.mk inclusion quotient comp_zero).Exact
  finiteSupport : chapter01SupportedOnFiniteSet Q

/-! On a proper curve the affine/local and global computations are connected by
    exact sequences whose quotient is supported on finitely many points. -/
structure Chapter01LocalGlobalBalanceInterface (X : Scheme.{u}) where
  affineTerm : X.Modules
  properTerm : X.Modules
  boundaryQuotient : X.Modules
  sequence : ShortComplex X.Modules
  sequence_eq : sequence.X₁ = affineTerm ∧ sequence.X₂ = properTerm ∧
    sequence.X₃ = boundaryQuotient
  exact : sequence.Exact
  finiteSupport : chapter01SupportedOnFiniteSet boundaryQuotient

/-! ### Relative two-term presentations -/

/- A genuine relative two-term model is a single map between finite free
  modules over the base ring.  Choosing bases writes those modules as finite
  coordinate modules; the fiberwise profile below records the resulting
  kernel and cokernel dimensions. -/
structure Chapter01RelativeTwoTermModel (A : Type u) [CommRing A] where
  rank₀ : ℕ
  rank₁ : ℕ
  differential :
    (Fin rank₀ → A) →ₗ[A] (Fin rank₁ → A)

structure Chapter01FiniteFreePresentation (k : Type u) [Field k] where
  F₀ : Type u
  F₁ : Type u
  [F₀AddCommGroup : AddCommGroup F₀]
  [F₀Module : Module k F₀]
  [F₁AddCommGroup : AddCommGroup F₁]
  [F₁Module : Module k F₁]
  finiteF₀ : FiniteDimensional k F₀
  finiteF₁ : FiniteDimensional k F₁
  differential : F₀ →ₗ[k] F₁

def chapter01KernelDimension {k : Type u} [Field k]
    (P : Chapter01FiniteFreePresentation k) : ℕ := by
  letI := P.F₀AddCommGroup
  letI := P.F₀Module
  letI := P.F₁AddCommGroup
  letI := P.F₁Module
  exact Module.finrank k P.differential.ker

def chapter01CokernelDimension {k : Type u} [Field k]
    (P : Chapter01FiniteFreePresentation k) : ℕ := by
  letI := P.F₀AddCommGroup
  letI := P.F₀Module
  letI := P.F₁AddCommGroup
  letI := P.F₁Module
  exact Module.finrank k (P.F₁ ⧸ LinearMap.range P.differential)

def chapter01PresentationIndex {k : Type u} [Field k]
    (P : Chapter01FiniteFreePresentation k) : ℤ :=
  (chapter01KernelDimension P : ℤ) - chapter01CokernelDimension P

def chapter01RankFunctionMayJump {S : Type u} (h : S → ℕ) : Prop :=
  ∃ s t : S, h s ≠ h t

def chapter01UpperSemicontinuous {S : Type u} [TopologicalSpace S]
    (h : S → ℕ) : Prop :=
  ∀ n : ℕ, IsClosed {s | n ≤ h s}

/- The following is deliberately a fiberwise profile over a topological
  parameter space; Chapter01RelativeTwoTermModel is the base-ring-level
  presentation and this record packages its possible rank behavior. -/
structure Chapter01RelativeTwoTermPresentation (k : Type u) [Field k]
    (S : Type u) [TopologicalSpace S] where
  presentation : S → Chapter01FiniteFreePresentation k
  index : S → ℤ
  kernelDimension : S → ℕ
  cokernelDimension : S → ℕ
  kernelDimension_formula :
    ∀ s, kernelDimension s = chapter01KernelDimension (presentation s)
  cokernelDimension_formula :
    ∀ s, cokernelDimension s = chapter01CokernelDimension (presentation s)
  kernelDimension_upperSemicontinuous :
    chapter01UpperSemicontinuous kernelDimension
  cokernelDimension_upperSemicontinuous :
    chapter01UpperSemicontinuous cokernelDimension
  index_formula : ∀ s, index s = (kernelDimension s : ℤ) - cokernelDimension s
  indexLocallyConstant : IsLocallyConstant index

def chapter01IndexBaseChangeCompatible {S T : Type u}
    (g : T → S) (indexS : S → ℤ) (indexT : T → ℤ) : Prop :=
  ∀ t, indexT t = indexS (g t)

def chapter01RelativeRiemannRochFormulaAt {S : Type u}
    (χ degree genus : S → ℤ) : Prop :=
  ∀ s, χ s = degree s + 1 - genus s

def chapter01RankJumpProfile {S : Type u} [TopologicalSpace S] (h₀ h₁ : S → ℕ) : Prop :=
  IsLocallyConstant (fun s => (h₀ s : ℤ) - h₁ s)

theorem chapter01_relative_index_is_euler_characteristic
    {k : Type u} [Field k] {S : Type u} [TopologicalSpace S]
    (P : Chapter01RelativeTwoTermPresentation k S) :
    IsLocallyConstant P.index ∧
      ∀ s, P.index s = (P.kernelDimension s : ℤ) - P.cokernelDimension s := by
  exact ⟨P.indexLocallyConstant, P.index_formula⟩

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01
