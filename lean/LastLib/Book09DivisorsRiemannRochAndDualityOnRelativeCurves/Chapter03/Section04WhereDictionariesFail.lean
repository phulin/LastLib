import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.RingTheory.Polynomial.GaussLemma
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03.Section03NormalCurvesAndRegularModels

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open scoped AlgebraicGeometry BigOperators

noncomputable section

universe u

/-! ## 3.4. Where the dictionaries fail -/

/-- The affine nodal equation `xy = 0`. -/
def chapter03NodeRelation (k : Type u) [CommRing k] :
    Ideal (MvPolynomial (Fin 2) k) :=
  Ideal.span ({MvPolynomial.X 0 * MvPolynomial.X 1} :
    Set (MvPolynomial (Fin 2) k))

/-- The nodal affine ring `k[x,y]/(xy)`. -/
abbrev Chapter03NodeRing (k : Type u) [CommRing k] :=
  MvPolynomial (Fin 2) k ⧸ chapter03NodeRelation k

def chapter03NodeQuotientMap (k : Type u) [CommRing k] :
    MvPolynomial (Fin 2) k →+* Chapter03NodeRing k :=
  Ideal.Quotient.mk (chapter03NodeRelation k)

def chapter03NodeIdeal (k : Type u) [CommRing k] : Ideal (Chapter03NodeRing k) :=
  (Ideal.span ({MvPolynomial.X 0, MvPolynomial.X 1} :
    Set (MvPolynomial (Fin 2) k))).map (chapter03NodeQuotientMap k)

def chapter03NodeComponentX (k : Type u) [CommRing k] : Ideal (Chapter03NodeRing k) :=
  (Ideal.span ({MvPolynomial.X 0} : Set (MvPolynomial (Fin 2) k))).map
    (chapter03NodeQuotientMap k)

def chapter03NodeComponentY (k : Type u) [CommRing k] : Ideal (Chapter03NodeRing k) :=
  (Ideal.span ({MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) k))).map
    (chapter03NodeQuotientMap k)

def Chapter03NodeComponentCodimensionZero
    {R : Type u} [CommRing R] (I : Ideal R) : Prop :=
  I.IsPrime ∧ ∀ J : Ideal R, J.IsPrime → J ≤ I → J = I

theorem chapter03_node_ideal_isMaximal (k : Type u) [Field k] :
    (chapter03NodeIdeal k).IsMaximal := by
  have hM : (Ideal.span ({MvPolynomial.X 0, MvPolynomial.X 1} :
      Set (MvPolynomial (Fin 2) k))).IsMaximal := by
    rw [Ideal.isMaximal_iff]
    constructor
    · intro h1
      rw [show ({MvPolynomial.X 0, MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) k)) =
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
        rw [show ({MvPolynomial.X 0, MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) k)) =
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
  have hker : RingHom.ker (chapter03NodeQuotientMap k) ≤
      Ideal.span ({MvPolynomial.X 0, MvPolynomial.X 1} :
        Set (MvPolynomial (Fin 2) k)) := by
    change RingHom.ker (Ideal.Quotient.mk (chapter03NodeRelation k)) ≤
      Ideal.span ({MvPolynomial.X 0, MvPolynomial.X 1} :
        Set (MvPolynomial (Fin 2) k))
    rw [Ideal.mk_ker]
    exact Ideal.span_le.2 (by
      intro z hz
      rcases hz with rfl
      exact mul_mem (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp)))
  simpa [chapter03NodeIdeal] using
    (Ideal.IsMaximal.map_of_surjective_of_ker_le
      (f := chapter03NodeQuotientMap k) Ideal.Quotient.mk_surjective hker)

theorem chapter03_node_ideal_isPrime (k : Type u) [Field k] :
    (chapter03NodeIdeal k).IsPrime := by
  exact (chapter03_node_ideal_isMaximal k).isPrime

instance chapter03NodeIdeal_isPrime_instance (k : Type u) [Field k] :
    (chapter03NodeIdeal k).IsPrime :=
  chapter03_node_ideal_isPrime k

theorem chapter03_node_componentX_is_codimensionZero (k : Type u) [Field k] :
    Chapter03NodeComponentCodimensionZero (chapter03NodeComponentX k) := by
  classical
  let P : Ideal (Polynomial k) :=
    Ideal.span ({Polynomial.X} : Set (Polynomial k))
  have hP : P.IsPrime := by
    dsimp [P]
    exact (Ideal.span_singleton_prime Polynomial.X_ne_zero).2 Polynomial.prime_X
  let hdomain : IsDomain
      (Polynomial (Polynomial k) ⧸
        (Ideal.map (Polynomial.C : Polynomial k →+* Polynomial (Polynomial k)) P)) :=
    Ideal.isDomain_map_C_quotient hP
  have hQ : (Ideal.map (Polynomial.C : Polynomial k →+* Polynomial (Polynomial k)) P).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp hdomain
  let _ : (Ideal.map (Polynomial.C : Polynomial k →+* Polynomial (Polynomial k)) P).IsPrime := hQ
  let e : Polynomial (Polynomial k) ≃+* MvPolynomial (Fin 2) k :=
    (Polynomial.Bivariate.equivMvPolynomial k).toRingEquiv
  have hsource :
      (Ideal.span ({MvPolynomial.X 0} : Set (MvPolynomial (Fin 2) k))).IsPrime := by
    have hmap :
        (Ideal.map e (Ideal.map (Polynomial.C : Polynomial k →+* Polynomial (Polynomial k)) P)).IsPrime :=
      inferInstance
    simpa [P, Ideal.map_span, Set.image_singleton, e] using hmap
  have hker : RingHom.ker (chapter03NodeQuotientMap k) ≤
      Ideal.span ({MvPolynomial.X 0} : Set (MvPolynomial (Fin 2) k)) := by
    change RingHom.ker (Ideal.Quotient.mk (chapter03NodeRelation k)) ≤
      Ideal.span ({MvPolynomial.X 0} : Set (MvPolynomial (Fin 2) k))
    rw [Ideal.mk_ker]
    exact Ideal.span_le.2 (by
      intro z hz
      rcases hz with rfl
      simpa [mul_comm] using
        (Ideal.span ({MvPolynomial.X 0} : Set (MvPolynomial (Fin 2) k))).mul_mem_left
          (MvPolynomial.X 1) (Ideal.subset_span (by simp)))
  have hcomp : (chapter03NodeComponentX k).IsPrime := by
    change (Ideal.span ({MvPolynomial.X 0} : Set (MvPolynomial (Fin 2) k))).map
      (chapter03NodeQuotientMap k) |>.IsPrime
    exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  refine ⟨hcomp, ?_⟩
  intro J hJ hle
  apply le_antisymm hle
  have hcomap :
      (chapter03NodeComponentX k).comap (chapter03NodeQuotientMap k) =
        Ideal.span ({MvPolynomial.X 0} : Set (MvPolynomial (Fin 2) k)) := by
    change Ideal.comap (Ideal.Quotient.mk (chapter03NodeRelation k))
      (Ideal.map (Ideal.Quotient.mk (chapter03NodeRelation k))
        (Ideal.span ({MvPolynomial.X 0} : Set (MvPolynomial (Fin 2) k)))) =
      Ideal.span ({MvPolynomial.X 0} : Set (MvPolynomial (Fin 2) k))
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot]
    apply sup_eq_left.mpr
    simpa [chapter03NodeQuotientMap] using hker
  have hxzero :
      chapter03NodeQuotientMap k (MvPolynomial.X 0) *
        chapter03NodeQuotientMap k (MvPolynomial.X 1) = 0 := by
    rw [← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton _))
  have hy_not :
      chapter03NodeQuotientMap k (MvPolynomial.X 1) ∉ J := by
    intro hyJ
    have hyI := hle hyJ
    have hyI' : MvPolynomial.X 1 ∈
        (chapter03NodeComponentX k).comap (chapter03NodeQuotientMap k) := hyI
    rw [hcomap] at hyI'
    have hyspan_not : MvPolynomial.X 1 ∉
        Ideal.span ({MvPolynomial.X 0} : Set (MvPolynomial (Fin 2) k)) := by
      intro h
      rw [show ({MvPolynomial.X 0} : Set (MvPolynomial (Fin 2) k)) =
          MvPolynomial.X '' ({0} : Set (Fin 2)) by
        ext z
        constructor
        · intro hz
          rcases hz with rfl
          simp
        · intro hz
          rcases hz with ⟨i, hi, rfl⟩
          fin_cases i <;> simp_all] at h
      rw [MvPolynomial.mem_ideal_span_X_image] at h
      have hs := h (Finsupp.single (1 : Fin 2) 1) (by
        simp [MvPolynomial.support_X])
      rcases hs with ⟨i, hi, hne⟩
      fin_cases i <;> simp_all
    exact hyspan_not hyI'
  have hxJ : chapter03NodeQuotientMap k (MvPolynomial.X 0) ∈ J := by
    have hxzeroJ : chapter03NodeQuotientMap k (MvPolynomial.X 0) *
        chapter03NodeQuotientMap k (MvPolynomial.X 1) ∈ J := by
      rw [hxzero]
      exact J.zero_mem
    exact (hJ.mem_or_mem hxzeroJ).resolve_right hy_not
  rw [chapter03NodeComponentX, Ideal.map_le_iff_le_comap]
  exact Ideal.span_le.2 (by
    intro z hz
    rcases hz with rfl
    exact hxJ)

theorem chapter03_node_componentY_is_codimensionZero (k : Type u) [Field k] :
    Chapter03NodeComponentCodimensionZero (chapter03NodeComponentY k) := by
  classical
  let e : Polynomial (Polynomial k) ≃+* MvPolynomial (Fin 2) k :=
    (Polynomial.Bivariate.equivMvPolynomial k).toRingEquiv
  have hsource :
      (Ideal.span ({Polynomial.X} : Set (Polynomial (Polynomial k)))).IsPrime := by
    exact (Ideal.span_singleton_prime Polynomial.X_ne_zero).2 Polynomial.prime_X
  have hmap :
      (Ideal.map e (Ideal.span ({Polynomial.X} : Set (Polynomial (Polynomial k))))).IsPrime :=
    inferInstance
  have hsource' :
      (Ideal.span ({MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) k))).IsPrime := by
    simpa [Ideal.map_span, Set.image_singleton, e] using hmap
  have hker : RingHom.ker (chapter03NodeQuotientMap k) ≤
      Ideal.span ({MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) k)) := by
    change RingHom.ker (Ideal.Quotient.mk (chapter03NodeRelation k)) ≤
      Ideal.span ({MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) k))
    rw [Ideal.mk_ker]
    exact Ideal.span_le.2 (by
      intro z hz
      rcases hz with rfl
      have hmem : MvPolynomial.X 1 ∈
          Ideal.span ({MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) k)) :=
        Ideal.subset_span (by simp)
      simpa [mul_comm] using
        (Ideal.span ({MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) k))).mul_mem_left
          (MvPolynomial.X 0) hmem)
  have hcomp : (chapter03NodeComponentY k).IsPrime := by
    change (Ideal.span ({MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) k))).map
      (chapter03NodeQuotientMap k) |>.IsPrime
    exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  refine ⟨hcomp, ?_⟩
  intro J hJ hle
  apply le_antisymm hle
  have hcomap :
      (chapter03NodeComponentY k).comap (chapter03NodeQuotientMap k) =
        Ideal.span ({MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) k)) := by
    change Ideal.comap (Ideal.Quotient.mk (chapter03NodeRelation k))
      (Ideal.map (Ideal.Quotient.mk (chapter03NodeRelation k))
        (Ideal.span ({MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) k)))) =
      Ideal.span ({MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) k))
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot]
    apply sup_eq_left.mpr
    simpa [chapter03NodeQuotientMap] using hker
  have hxyzero :
      chapter03NodeQuotientMap k (MvPolynomial.X 0) *
        chapter03NodeQuotientMap k (MvPolynomial.X 1) = 0 := by
    rw [← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton _))
  have hx_not :
      chapter03NodeQuotientMap k (MvPolynomial.X 0) ∉ J := by
    intro hxJ
    have hxI := hle hxJ
    have hxI' : MvPolynomial.X 0 ∈
        (chapter03NodeComponentY k).comap (chapter03NodeQuotientMap k) := hxI
    rw [hcomap] at hxI'
    have hxspan_not : MvPolynomial.X 0 ∉
        Ideal.span ({MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) k)) := by
      intro h
      rw [show ({MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) k)) =
          MvPolynomial.X '' ({1} : Set (Fin 2)) by
        ext z
        constructor
        · intro hz
          rcases hz with rfl
          simp
        · intro hz
          rcases hz with ⟨i, hi, rfl⟩
          fin_cases i <;> simp_all] at h
      rw [MvPolynomial.mem_ideal_span_X_image] at h
      have hs := h (Finsupp.single (0 : Fin 2) 1) (by
        simp [MvPolynomial.support_X])
      rcases hs with ⟨i, hi, hne⟩
      fin_cases i <;> simp_all
    exact hxspan_not hxI'
  have hyJ : chapter03NodeQuotientMap k (MvPolynomial.X 1) ∈ J := by
    have hxyJ : chapter03NodeQuotientMap k (MvPolynomial.X 0) *
        chapter03NodeQuotientMap k (MvPolynomial.X 1) ∈ J := by
      rw [hxyzero]
      exact J.zero_mem
    exact (hJ.mem_or_mem hxyJ).resolve_left hx_not
  rw [chapter03NodeComponentY, Ideal.map_le_iff_le_comap]
  exact Ideal.span_le.2 (by
    intro z hz
    rcases hz with rfl
    exact hyJ)

def chapter03NodePoint (k : Type u) [Field k] : PrimeSpectrum (Chapter03NodeRing k) :=
  ⟨chapter03NodeIdeal k, chapter03_node_ideal_isPrime k⟩

theorem chapter03_node_point_is_codimensionOne (k : Type u) [Field k] :
    Order.coheight (chapter03NodePoint k) = 1 := by
  sorry

theorem chapter03_node_ring_not_a_domain (k : Type u) [Field k] :
    ¬ IsDomain (Chapter03NodeRing k) := by
  intro hdom
  let x : Chapter03NodeRing k := chapter03NodeQuotientMap k (MvPolynomial.X 0)
  let y : Chapter03NodeRing k := chapter03NodeQuotientMap k (MvPolynomial.X 1)
  have hxne : x ≠ 0 := by
    intro hx
    change chapter03NodeQuotientMap k (MvPolynomial.X 0) = 0 at hx
    have hm : MvPolynomial.X 0 ∈ chapter03NodeRelation k :=
      Ideal.Quotient.eq_zero_iff_mem.mp hx
    rcases (Ideal.mem_span_singleton').mp hm with ⟨q, hq⟩
    have heval := congrArg
      (MvPolynomial.eval (fun i : Fin 2 => if i = 0 then 1 else 0)) hq
    simp [MvPolynomial.eval_mul] at heval
  have hyne : y ≠ 0 := by
    intro hy
    change chapter03NodeQuotientMap k (MvPolynomial.X 1) = 0 at hy
    have hm : MvPolynomial.X 1 ∈ chapter03NodeRelation k :=
      Ideal.Quotient.eq_zero_iff_mem.mp hy
    rcases (Ideal.mem_span_singleton').mp hm with ⟨q, hq⟩
    have heval := congrArg
      (MvPolynomial.eval (fun i : Fin 2 => if i = 1 then 1 else 0)) hq
    simp [MvPolynomial.eval_mul] at heval
  have hxy : x * y = 0 := by
    change chapter03NodeQuotientMap k (MvPolynomial.X 0) *
      chapter03NodeQuotientMap k (MvPolynomial.X 1) = 0
    rw [← map_mul]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (Set.mem_singleton (MvPolynomial.X 0 * MvPolynomial.X 1))
  rcases eq_zero_or_eq_zero_of_mul_eq_zero hxy with hzero | hzero
  · exact hxne hzero
  · exact hyne hzero

abbrev Chapter03NodeLocalRing (k : Type u) [Field k] :=
  Localization.AtPrime (chapter03NodeIdeal k)

theorem chapter03_node_localRing_not_a_domain (k : Type u) [Field k] :
    ¬ IsDomain (Chapter03NodeLocalRing k) := by
  intro hdom
  let _ : IsDomain (Chapter03NodeLocalRing k) := hdom
  let b₁ : MvPolynomial (Fin 2) k →+* Polynomial k :=
    MvPolynomial.eval₂Hom (algebraMap k (Polynomial k))
      (fun i => if i = (0 : Fin 2) then Polynomial.X else 0)
  have hb₁ : chapter03NodeRelation k ≤ RingHom.ker b₁ := by
    rw [chapter03NodeRelation]
    exact Ideal.span_le.2 (by
      intro z hz
      rcases hz with rfl
      simp [b₁])
  let q₁ : Chapter03NodeRing k →+* Polynomial k :=
    Ideal.Quotient.lift (chapter03NodeRelation k) b₁ (fun a ha => hb₁ ha)
  let e₀ : Polynomial k →+* k :=
    Polynomial.eval₂RingHom (RingHom.id k) 0
  let r : MvPolynomial (Fin 2) k →+* k :=
    MvPolynomial.eval₂Hom (RingHom.id k) (fun _ => 0)
  have her : e₀.comp b₁ = r := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [e₀, b₁, r]
    · intro i
      fin_cases i <;> simp [e₀, b₁, r]
  let qres : Chapter03NodeRing k →+* k :=
    e₀.comp q₁
  have hqres_comp : qres.comp (chapter03NodeQuotientMap k) = r := by
    change (e₀.comp q₁).comp (chapter03NodeQuotientMap k) = r
    rw [← her]
    apply RingHom.ext
    intro z
    change e₀ (q₁ (chapter03NodeQuotientMap k z)) = e₀ (b₁ z)
    rfl
  have hqresker : RingHom.ker qres ≤ chapter03NodeIdeal k := by
    intro s hs
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective s
    have hz0 : qres (chapter03NodeQuotientMap k z) = 0 := by
      exact hs
    have hz : r z = 0 := by
      rw [← hqres_comp]
      exact hz0
    have hz' : MvPolynomial.constantCoeff z = 0 := by
      simpa [r] using hz
    have hdiff : z - MvPolynomial.C (MvPolynomial.constantCoeff z) ∈
        Ideal.span ({MvPolynomial.X 0, MvPolynomial.X 1} :
          Set (MvPolynomial (Fin 2) k)) := by
      rw [show ({MvPolynomial.X 0, MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) k)) =
          MvPolynomial.X '' ({0, 1} : Set (Fin 2)) by
        ext w
        constructor
        · intro hw
          rcases hw with rfl | rfl <;> simp
        · intro hw
          rcases hw with ⟨i, hi, rfl⟩
          fin_cases i <;> simp_all]
      rw [MvPolynomial.mem_ideal_span_X_image]
      intro m hm
      have hm0 : m ≠ 0 := by
        intro hm0
        subst m
        have hm' := MvPolynomial.mem_support_iff.mp hm
        change MvPolynomial.coeff 0
          (z - MvPolynomial.C (MvPolynomial.coeff 0 z)) ≠ 0 at hm'
        simp at hm'
      obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hm0
      exact ⟨i, by fin_cases i <;> simp, Finsupp.mem_support_iff.mp hi⟩
    have hzM : z ∈ Ideal.span ({MvPolynomial.X 0, MvPolynomial.X 1} :
        Set (MvPolynomial (Fin 2) k)) := by
      simpa [hz'] using hdiff
    change chapter03NodeQuotientMap k z ∈
      Ideal.map (chapter03NodeQuotientMap k)
        (Ideal.span ({MvPolynomial.X 0, MvPolynomial.X 1} :
          Set (MvPolynomial (Fin 2) k)))
    exact Ideal.mem_map_of_mem _ hzM
  have hq₁x :
      q₁ (chapter03NodeQuotientMap k (MvPolynomial.X 0)) = Polynomial.X := by
    simp [q₁, chapter03NodeQuotientMap, b₁]
  have hxloc :
      algebraMap (Chapter03NodeRing k) (Chapter03NodeLocalRing k)
        (chapter03NodeQuotientMap k (MvPolynomial.X 0)) ≠ 0 := by
    intro hx
    obtain ⟨s, hs⟩ :=
      (IsLocalization.map_eq_zero_iff (chapter03NodeIdeal k).primeCompl
        (Chapter03NodeLocalRing k)
        (chapter03NodeQuotientMap k (MvPolynomial.X 0))).mp hx
    have hs' :
        q₁ (s : Chapter03NodeRing k) *
          q₁ (chapter03NodeQuotientMap k (MvPolynomial.X 0)) = 0 := by
      simpa only [map_mul, map_zero] using congrArg q₁ hs
    rw [hq₁x] at hs'
    rcases mul_eq_zero.mp hs' with hs₁ | hsX
    · have hqreszero : qres (s : Chapter03NodeRing k) = 0 := by
        simp [qres, hs₁]
      exact s.2 (hqresker hqreszero)
    · exact (Polynomial.X_ne_zero hsX).elim
  let b₂ : MvPolynomial (Fin 2) k →+* Polynomial k :=
    MvPolynomial.eval₂Hom (algebraMap k (Polynomial k))
      (fun i => if i = (1 : Fin 2) then Polynomial.X else 0)
  have hb₂ : chapter03NodeRelation k ≤ RingHom.ker b₂ := by
    rw [chapter03NodeRelation]
    exact Ideal.span_le.2 (by
      intro z hz
      rcases hz with rfl
      simp [b₂])
  let q₂ : Chapter03NodeRing k →+* Polynomial k :=
    Ideal.Quotient.lift (chapter03NodeRelation k) b₂ (fun a ha => hb₂ ha)
  let r₂ : MvPolynomial (Fin 2) k →+* k :=
    MvPolynomial.eval₂Hom (RingHom.id k) (fun _ => 0)
  have her₂ : e₀.comp b₂ = r₂ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [e₀, b₂, r₂]
    · intro i
      fin_cases i <;> simp [e₀, b₂, r₂]
  let qres₂ : Chapter03NodeRing k →+* k :=
    e₀.comp q₂
  have hqres_comp₂ : qres₂.comp (chapter03NodeQuotientMap k) = r₂ := by
    change (e₀.comp q₂).comp (chapter03NodeQuotientMap k) = r₂
    rw [← her₂]
    apply RingHom.ext
    intro z
    change e₀ (q₂ (chapter03NodeQuotientMap k z)) = e₀ (b₂ z)
    rfl
  have hqresker₂ : RingHom.ker qres₂ ≤ chapter03NodeIdeal k := by
    intro s hs
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective s
    have hz0 : qres₂ (chapter03NodeQuotientMap k z) = 0 := by
      exact hs
    have hz : r₂ z = 0 := by
      rw [← hqres_comp₂]
      exact hz0
    have hz' : MvPolynomial.constantCoeff z = 0 := by
      simpa [r₂] using hz
    have hdiff : z - MvPolynomial.C (MvPolynomial.constantCoeff z) ∈
        Ideal.span ({MvPolynomial.X 0, MvPolynomial.X 1} :
          Set (MvPolynomial (Fin 2) k)) := by
      rw [show ({MvPolynomial.X 0, MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) k)) =
          MvPolynomial.X '' ({0, 1} : Set (Fin 2)) by
        ext w
        constructor
        · intro hw
          rcases hw with rfl | rfl <;> simp
        · intro hw
          rcases hw with ⟨i, hi, rfl⟩
          fin_cases i <;> simp_all]
      rw [MvPolynomial.mem_ideal_span_X_image]
      intro m hm
      have hm0 : m ≠ 0 := by
        intro hm0
        subst m
        have hm' := MvPolynomial.mem_support_iff.mp hm
        change MvPolynomial.coeff 0
          (z - MvPolynomial.C (MvPolynomial.coeff 0 z)) ≠ 0 at hm'
        simp at hm'
      obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hm0
      exact ⟨i, by fin_cases i <;> simp, Finsupp.mem_support_iff.mp hi⟩
    have hzM : z ∈ Ideal.span ({MvPolynomial.X 0, MvPolynomial.X 1} :
        Set (MvPolynomial (Fin 2) k)) := by
      simpa [hz'] using hdiff
    change chapter03NodeQuotientMap k z ∈
      Ideal.map (chapter03NodeQuotientMap k)
        (Ideal.span ({MvPolynomial.X 0, MvPolynomial.X 1} :
          Set (MvPolynomial (Fin 2) k)))
    exact Ideal.mem_map_of_mem _ hzM
  have hq₂y :
      q₂ (chapter03NodeQuotientMap k (MvPolynomial.X 1)) = Polynomial.X := by
    simp [q₂, chapter03NodeQuotientMap, b₂]
  have hyloc :
      algebraMap (Chapter03NodeRing k) (Chapter03NodeLocalRing k)
        (chapter03NodeQuotientMap k (MvPolynomial.X 1)) ≠ 0 := by
    intro hy
    obtain ⟨s, hs⟩ :=
      (IsLocalization.map_eq_zero_iff (chapter03NodeIdeal k).primeCompl
        (Chapter03NodeLocalRing k)
        (chapter03NodeQuotientMap k (MvPolynomial.X 1))).mp hy
    have hs' :
        q₂ (s : Chapter03NodeRing k) *
          q₂ (chapter03NodeQuotientMap k (MvPolynomial.X 1)) = 0 := by
      simpa only [map_mul, map_zero] using congrArg q₂ hs
    rw [hq₂y] at hs'
    rcases mul_eq_zero.mp hs' with hs₂ | hsX
    · have hqreszero : qres₂ (s : Chapter03NodeRing k) = 0 := by
        simp [qres₂, hs₂]
      exact s.2 (hqresker₂ hqreszero)
    · exact (Polynomial.X_ne_zero hsX).elim
  have hxy :
      algebraMap (Chapter03NodeRing k) (Chapter03NodeLocalRing k)
          (chapter03NodeQuotientMap k (MvPolynomial.X 0)) *
        algebraMap (Chapter03NodeRing k) (Chapter03NodeLocalRing k)
          (chapter03NodeQuotientMap k (MvPolynomial.X 1)) = 0 := by
    rw [← map_mul]
    rw [show chapter03NodeQuotientMap k (MvPolynomial.X 0) *
        chapter03NodeQuotientMap k (MvPolynomial.X 1) = 0 by
      rw [← map_mul]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_singleton _))]
    simp
  rcases eq_zero_or_eq_zero_of_mul_eq_zero hxy with hzero | hzero
  · exact hxloc hzero
  · exact hyloc hzero

/- The node has codimension-one point data but fails the integral-domain
  hypothesis required by the normal-integral order-of-vanishing API. -/
theorem chapter03_node_normal_integral_divisor_dictionary_unavailable
    (k : Type u) [Field k] :
    ¬ IsDomain (Chapter03NodeLocalRing k) :=
  chapter03_node_localRing_not_a_domain k

/-- The integral cusp equation `y² = x³`. -/
def chapter03CuspRelation (k : Type u) [CommRing k] :
    Ideal (MvPolynomial (Fin 2) k) :=
  Ideal.span ({MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3} :
    Set (MvPolynomial (Fin 2) k))

/-- The cusp ring `k[x,y]/(y²-x³)`. -/
abbrev Chapter03CuspRing (k : Type u) [CommRing k] :=
  MvPolynomial (Fin 2) k ⧸ chapter03CuspRelation k

/- The cusp is integral, even though its singular point is not Cartier. -/
theorem chapter03_cusp_ring_isDomain (k : Type u) [Field k] :
    IsDomain (Chapter03CuspRing k) := by
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
        chapter03CuspRelation k := by
    rw [chapter03CuspRelation, Ideal.map_span, Set.image_singleton]
    change Ideal.span ({e p} : Set (MvPolynomial (Fin 2) k)) =
      Ideal.span ({MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3} :
        Set (MvPolynomial (Fin 2) k))
    rw [he]
  have hIprime : (chapter03CuspRelation k).IsPrime := by
    let _ : (Ideal.span ({p} : Set (Polynomial (Polynomial k)))).IsPrime := hJprime
    rw [← hmap]
    exact Ideal.map_isPrime_of_equiv e
  rw [Ideal.Quotient.isDomain_iff_prime]
  exact hIprime

def chapter03CuspQuotientMap (k : Type u) [CommRing k] :
    MvPolynomial (Fin 2) k →+* Chapter03CuspRing k :=
  Ideal.Quotient.mk (chapter03CuspRelation k)

def chapter03CuspX (k : Type u) [CommRing k] : Chapter03CuspRing k :=
  chapter03CuspQuotientMap k (MvPolynomial.X 0)

def chapter03CuspY (k : Type u) [CommRing k] : Chapter03CuspRing k :=
  chapter03CuspQuotientMap k (MvPolynomial.X 1)

def chapter03CuspMaximalIdeal (k : Type u) [CommRing k] :
    Ideal (Chapter03CuspRing k) :=
  (Ideal.span ({MvPolynomial.X 0, MvPolynomial.X 1} :
    Set (MvPolynomial (Fin 2) k))).map (chapter03CuspQuotientMap k)

theorem chapter03_cusp_maximalIdeal_isMaximal (k : Type u) [Field k] :
    (chapter03CuspMaximalIdeal k).IsMaximal := by
  have hM : (Ideal.span ({MvPolynomial.X 0, MvPolynomial.X 1} :
      Set (MvPolynomial (Fin 2) k))).IsMaximal := by
    rw [Ideal.isMaximal_iff]
    constructor
    · intro h1
      rw [show ({MvPolynomial.X 0, MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) k)) =
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
        rw [show ({MvPolynomial.X 0, MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) k)) =
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
  have hker : RingHom.ker (chapter03CuspQuotientMap k) ≤
      Ideal.span ({MvPolynomial.X 0, MvPolynomial.X 1} :
        Set (MvPolynomial (Fin 2) k)) := by
    change RingHom.ker (Ideal.Quotient.mk (chapter03CuspRelation k)) ≤
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
      exact sub_mem (by simpa [pow_two] using mul_mem hy hy)
        (by simpa [pow_succ, pow_two] using mul_mem (mul_mem hx hx) hx))
  simpa [chapter03CuspMaximalIdeal] using
    (Ideal.IsMaximal.map_of_surjective_of_ker_le
      (f := chapter03CuspQuotientMap k) Ideal.Quotient.mk_surjective hker)

theorem chapter03_cusp_maximalIdeal_isPrime (k : Type u) [Field k] :
    (chapter03CuspMaximalIdeal k).IsPrime := by
  exact (chapter03_cusp_maximalIdeal_isMaximal k).isPrime

instance chapter03CuspMaximalIdeal_isPrime_instance (k : Type u) [Field k] :
    (chapter03CuspMaximalIdeal k).IsPrime :=
  chapter03_cusp_maximalIdeal_isPrime k

def chapter03CuspPoint (k : Type u) [Field k] :
    PrimeSpectrum (Chapter03CuspRing k) :=
  ⟨chapter03CuspMaximalIdeal k, chapter03_cusp_maximalIdeal_isPrime k⟩

theorem chapter03_cusp_point_is_codimensionOne (k : Type u) [Field k] :
    Order.coheight (chapter03CuspPoint k) = 1 := by
  sorry

theorem chapter03_cusp_point_defines_codimensionOne_cycle (k : Type u) [Field k] :
    ∃ P : Chapter03PrimeDivisor
      (Spec (CommRingCat.of (Chapter03CuspRing k))),
      P.genericPoint = chapter03CuspPoint k := by
  classical
  let : IsDomain (Chapter03CuspRing k) := chapter03_cusp_ring_isDomain k
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
  have hq' : ringKrullDim (Chapter03CuspRing k) + 1 ≤ 2 := by
    change ringKrullDim (MvPolynomial (Fin 2) k ⧸
      Ideal.span {MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3}) + 1 ≤ 2
    rw [← hp]
    exact hq
  have hdim : ringKrullDim (Chapter03CuspRing k) ≤ 1 := by
    have htwo : (2 : WithBot ℕ∞) = 1 + 1 := by norm_num
    rw [htwo] at hq'
    exact (ENat.WithBot.add_le_add_one_right_iff).mp hq'
  let : (chapter03CuspMaximalIdeal k).IsPrime :=
    chapter03_cusp_maximalIdeal_isPrime k
  have hXne : chapter03CuspX k ≠ 0 := by
    intro hx
    change chapter03CuspQuotientMap k (MvPolynomial.X 0) = 0 at hx
    have hm : MvPolynomial.X 0 ∈ chapter03CuspRelation k :=
      Ideal.Quotient.eq_zero_iff_mem.mp hx
    rcases (Ideal.mem_span_singleton').mp hm with ⟨q, hq⟩
    have heval := congrArg
      (MvPolynomial.eval (fun _ : Fin 2 => (1 : k))) hq
    simp [MvPolynomial.eval_mul] at heval
  have hMnebot : chapter03CuspMaximalIdeal k ≠ ⊥ := by
    intro hM
    have hxM : chapter03CuspX k ∈ chapter03CuspMaximalIdeal k := by
      rw [chapter03CuspMaximalIdeal]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span (by simp))
    have : chapter03CuspX k = 0 := by simpa [hM] using hxM
    exact hXne this
  have hle : (chapter03CuspMaximalIdeal k).height ≤
      ringKrullDim (Chapter03CuspRing k) :=
    Ideal.height_le_ringKrullDim_of_isPrime
  have hle1' : (↑(chapter03CuspMaximalIdeal k).height :
      WithBot ℕ∞) ≤ (1 : WithBot ℕ∞) :=
    hle.trans hdim
  have hle1 : (chapter03CuspMaximalIdeal k).height ≤ 1 :=
    WithBot.coe_le_coe.mp hle1'
  have hnezero : (chapter03CuspMaximalIdeal k).height ≠ 0 := by
    intro hzero
    exact hMnebot ((Ideal.height_eq_zero_iff_eq_bot).mp hzero)
  have hge1 : 1 ≤ (chapter03CuspMaximalIdeal k).height :=
    (Order.one_le_iff_ne_zero).2 hnezero
  have hheight : (chapter03CuspMaximalIdeal k).height = 1 :=
    le_antisymm hle1 hge1
  let x : Spec (CommRingCat.of (Chapter03CuspRing k)) := chapter03CuspPoint k
  have hx : Order.coheight x = 1 := by
    calc
      Order.coheight x = x.asIdeal.height :=
        (AlgebraicGeometry.idealHeight_eq_coheight
          (CommRingCat.of (Chapter03CuspRing k)) x).symm
      _ = 1 := by simpa [x, chapter03CuspPoint] using hheight
  obtain ⟨P, hP⟩ :=
    chapter03_primeDivisor_exists_of_codimensionOnePoint
      (X := Spec (CommRingCat.of (Chapter03CuspRing k))) ⟨x, hx⟩
  exact ⟨P, by simpa [x] using hP⟩

abbrev Chapter03CuspLocalRing (k : Type u) [Field k] :=
  Localization.AtPrime (chapter03CuspMaximalIdeal k)

def chapter03CuspLocalMaximalIdeal (k : Type u) [Field k] :
    Ideal (Chapter03CuspLocalRing k) :=
  IsLocalRing.maximalIdeal (Chapter03CuspLocalRing k)

theorem chapter03_cusp_local_maximalIdeal_not_principal (k : Type u) [Field k] :
    ¬ ∃ a : Chapter03CuspLocalRing k,
      chapter03CuspLocalMaximalIdeal k = Ideal.span ({a} : Set (Chapter03CuspLocalRing k)) := by
  classical
  let R := Chapter03CuspRing k
  let S := Chapter03CuspLocalRing k
  let q : MvPolynomial (Fin 2) k →+* R := chapter03CuspQuotientMap k
  let l : R →+* S := algebraMap R S
  let x : S := l (chapter03CuspX k)
  let y : S := l (chapter03CuspY k)
  have hmax : (chapter03CuspMaximalIdeal k).IsMaximal :=
    chapter03_cusp_maximalIdeal_isMaximal k
  have hlocal :
      chapter03CuspLocalMaximalIdeal k =
        Ideal.map l (chapter03CuspMaximalIdeal k) := by
    rw [chapter03CuspLocalMaximalIdeal,
      IsLocalization.AtPrime.map_eq_maximalIdeal
        (chapter03CuspMaximalIdeal k) S]
  have hspan :
      chapter03CuspLocalMaximalIdeal k = Ideal.span ({x, y} : Set S) := by
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
  let : IsDomain R := chapter03_cusp_ring_isDomain k
  have hqX : chapter03CuspX k ≠ 0 := by
    intro hx
    change chapter03CuspQuotientMap k (MvPolynomial.X 0) = 0 at hx
    have hm : MvPolynomial.X 0 ∈ chapter03CuspRelation k :=
      Ideal.Quotient.eq_zero_iff_mem.mp hx
    rcases (Ideal.mem_span_singleton').mp hm with ⟨p, hp⟩
    have heval :=
      congrArg (MvPolynomial.eval (fun _ : Fin 2 => (1 : k))) hp
    simp [MvPolynomial.eval_mul] at heval
  have hlinj : Function.Injective l :=
    IsLocalization.injective S
      (chapter03CuspMaximalIdeal k).primeCompl_le_nonZeroDivisors
  have hx : x ≠ 0 := by
    intro hxzero
    apply hqX
    apply hlinj
    simpa [x, l] using hxzero
  let m₀ : Ideal (MvPolynomial (Fin 2) k) :=
    Ideal.span ({MvPolynomial.X 0, MvPolynomial.X 1} :
      Set (MvPolynomial (Fin 2) k))
  have hkerq : RingHom.ker q ≤ m₀ ^ 2 := by
    change RingHom.ker (Ideal.Quotient.mk (chapter03CuspRelation k)) ≤ m₀ ^ 2
    rw [Ideal.mk_ker]
    rw [chapter03CuspRelation]
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
      chapter03CuspMaximalIdeal k ^ 2 = Ideal.map q (m₀ ^ 2) := by
    change (m₀.map q) ^ 2 = _
    rw [← Ideal.map_pow]
  have hqXnot : chapter03CuspX k ∉ chapter03CuspMaximalIdeal k ^ 2 := by
    intro h
    rw [hmRpow] at h
    have hpre : MvPolynomial.X 0 ∈
        Ideal.comap q (Ideal.map q (m₀ ^ 2)) := h
    rw [Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective] at hpre
    rcases Submodule.mem_sup.mp hpre with ⟨u, hu, v, hv, huv⟩
    have hv' : v ∈ RingHom.ker q := hv
    apply hX0not
    have hsum : u + v ∈ m₀ ^ 2 := add_mem hu (hkerq hv')
    convert hsum using 1
    exact huv.symm
  have hxnot : x ∉ (chapter03CuspLocalMaximalIdeal k) ^ 2 := by
    intro h
    have hx' : l (chapter03CuspX k) ∈
        (chapter03CuspLocalMaximalIdeal k) ^ 2 := by
      simpa [x] using h
    have hunder :
        ((chapter03CuspLocalMaximalIdeal k) ^ 2).under R =
          chapter03CuspMaximalIdeal k ^ 2 :=
      IsLocalization.AtPrime.under_maximalIdeal_pow
        (chapter03CuspMaximalIdeal k) S 2
    have hbase : chapter03CuspX k ∈
        chapter03CuspMaximalIdeal k ^ 2 := by
      rw [← hunder]
      exact hx'
    exact hqXnot hbase
  rintro ⟨a, ha⟩
  have hxm : x ∈ chapter03CuspLocalMaximalIdeal k := by
    rw [hspan]
    exact Ideal.subset_span (by simp)
  have hxa : x ∈ Ideal.span ({a} : Set S) := by
    rw [← ha]
    exact hxm
  obtain ⟨r, hr⟩ := (Ideal.mem_span_singleton').mp hxa
  have hrm : r ∉ chapter03CuspLocalMaximalIdeal k := by
    intro hrm
    have ham : a ∈ chapter03CuspLocalMaximalIdeal k := by
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
  have hspanx : chapter03CuspLocalMaximalIdeal k = Ideal.span ({x} : Set S) := by
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
  have hrel0 : (chapter03CuspY k) ^ 2 - (chapter03CuspX k) ^ 3 = 0 := by
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
  have hzm : z ∈ chapter03CuspLocalMaximalIdeal k := by
    by_contra hzn
    have hzu : IsUnit z := IsLocalRing.notMem_maximalIdeal.mp hzn
    apply hxnotunit
    rw [← hsq]
    exact hzu.pow 2
  apply hxnot
  have hzsq : z ^ 2 ∈ (chapter03CuspLocalMaximalIdeal k) ^ 2 := by
    simpa [pow_two] using Ideal.mul_mem_mul hzm hzm
  simpa [hsq] using hzsq

/-- The local effective-Cartier condition at the cusp point. -/
def chapter03CuspPointIsEffectiveCartier (k : Type u) [Field k] : Prop :=
  ∃ a : Chapter03CuspLocalRing k,
    chapter03CuspLocalMaximalIdeal k = Ideal.span ({a} : Set (Chapter03CuspLocalRing k)) ∧
      IsRegular a

theorem chapter03_cusp_point_not_effectiveCartier (k : Type u) [Field k] :
    ¬ chapter03CuspPointIsEffectiveCartier k := by
  rintro ⟨a, ha, _⟩
  exact chapter03_cusp_local_maximalIdeal_not_principal k ⟨a, ha⟩

/-- The normalization parameter equations `x ↦ t²`, `y ↦ t³`. -/
def chapter03CuspParametrization
    (k : Type u) [CommRing k]
    (φ : Chapter03CuspRing k →+* Polynomial k) : Prop :=
  φ (chapter03CuspX k) = Polynomial.X ^ 2 ∧
    φ (chapter03CuspY k) = Polynomial.X ^ 3 ∧
    Function.Injective φ

def chapter03CuspNormalizationOriginIdeal (k : Type u) [CommRing k] : Ideal (Polynomial k) :=
  Ideal.span ({Polynomial.X} : Set (Polynomial k))

theorem chapter03_cusp_parametrization_exists (k : Type u) [Field k] :
    ∃ φ : Chapter03CuspRing k →+* Polynomial k,
      chapter03CuspParametrization k φ ∧
        Ideal.comap φ (chapter03CuspNormalizationOriginIdeal k) =
          chapter03CuspMaximalIdeal k := by
  classical
  let e : Polynomial (Polynomial k) ≃+* MvPolynomial (Fin 2) k :=
    (Polynomial.Bivariate.equivMvPolynomial k).toRingEquiv
  let p : Polynomial (Polynomial k) :=
    Polynomial.X ^ 2 - Polynomial.C (Polynomial.X ^ 3)
  have he : e p = MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3 := by
    simp [e, p]
  have hmap :
      (Ideal.span ({p} : Set (Polynomial (Polynomial k)))).map
          (e : Polynomial (Polynomial k) →+* MvPolynomial (Fin 2) k) =
        chapter03CuspRelation k := by
    rw [chapter03CuspRelation, Ideal.map_span, Set.image_singleton]
    change Ideal.span ({e p} : Set (MvPolynomial (Fin 2) k)) =
      Ideal.span ({MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3} :
        Set (MvPolynomial (Fin 2) k))
    rw [he]
  let E : Chapter03CuspRing k ≃+* AdjoinRoot p :=
    (Ideal.quotientEquiv (Ideal.span ({p} : Set (Polynomial (Polynomial k))))
      (chapter03CuspRelation k)
      e hmap.symm).symm
  let b : Polynomial k →+* Polynomial k := (Polynomial.expand k 2).toRingHom
  have hb : Function.Injective b := Polynomial.expand_injective (by norm_num)
  have hpmonic : p.Monic := by
    dsimp [p]
    exact Polynomial.monic_X_pow_sub_C _ (by norm_num)
  have hroot : p.eval₂ b (Polynomial.X ^ 3) = 0 := by
    simp only [p, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, b, map_pow]
    have hbX : (Polynomial.expand k 2).toRingHom (Polynomial.X : Polynomial k) =
        Polynomial.X ^ 2 := by
      change (Polynomial.expand k 2) Polynomial.X = _
      exact Polynomial.expand_X 2
    rw [hbX]
    ring
  let ψ : AdjoinRoot p →+* Polynomial k :=
    (AdjoinRoot.isAdjoinRoot p).lift b (Polynomial.X ^ 3) hroot
  let : IsDomain (Chapter03CuspRing k) := chapter03_cusp_ring_isDomain k
  let : IsDomain (AdjoinRoot p) := E.isDomain_iff.mp (chapter03_cusp_ring_isDomain k)
  have hInt : (algebraMap (Polynomial k) (AdjoinRoot p)).IsIntegral := by
    exact Polynomial.Monic.quotient_isIntegral hpmonic
      (Ideal.subset_span (by simp))
  let : Algebra.IsIntegral (Polynomial k) (AdjoinRoot p) :=
    algebraMap_isIntegral_iff.mp hInt
  have hcomp : ψ.comp (algebraMap (Polynomial k) (AdjoinRoot p)) = b := by
    apply RingHom.ext
    intro z
    simpa [ψ] using
      (AdjoinRoot.isAdjoinRoot p).lift_algebraMap hroot z
  have hKcomap :
      (RingHom.ker ψ).comap (algebraMap (Polynomial k) (AdjoinRoot p)) = ⊥ := by
    rw [RingHom.ker_eq_comap_bot ψ, Ideal.comap_comap, hcomp]
    exact Ideal.comap_bot_of_injective _ hb
  have hK : RingHom.ker ψ = ⊥ :=
    Ideal.eq_bot_of_comap_eq_bot hKcomap
  have hψ : Function.Injective ψ :=
    (RingHom.injective_iff_ker_eq_bot ψ).2 hK
  let φ : Chapter03CuspRing k →+* Polynomial k := ψ.comp E.toRingHom
  have hφ : Function.Injective φ := hψ.comp E.injective
  have hEX0 : E (chapter03CuspX k) =
      Ideal.Quotient.mk (Ideal.span ({p} : Set (Polynomial (Polynomial k))))
        (Polynomial.C Polynomial.X) := by
    change (Ideal.quotientEquiv
      (Ideal.span ({p} : Set (Polynomial (Polynomial k))))
      (chapter03CuspRelation k)
      e hmap.symm).symm
      (Ideal.Quotient.mk (chapter03CuspRelation k) (MvPolynomial.X 0)) = _
    rw [Ideal.quotientEquiv_symm_mk]
    have he0 : e.symm (MvPolynomial.X 0) = Polynomial.C Polynomial.X := by
      apply e.injective
      simp [e]
    rw [he0]
  have hEX1 : E (chapter03CuspY k) =
      Ideal.Quotient.mk (Ideal.span ({p} : Set (Polynomial (Polynomial k))))
        Polynomial.X := by
    change (Ideal.quotientEquiv
      (Ideal.span ({p} : Set (Polynomial (Polynomial k))))
      (chapter03CuspRelation k)
      e hmap.symm).symm
      (Ideal.Quotient.mk (chapter03CuspRelation k) (MvPolynomial.X 1)) = _
    rw [Ideal.quotientEquiv_symm_mk]
    have he1 : e.symm (MvPolynomial.X 1) = Polynomial.X := by
      apply e.injective
      simp [e]
    rw [he1]
  have hφX : φ (chapter03CuspX k) = Polynomial.X ^ 2 := by
    change ψ (E (chapter03CuspX k)) = _
    rw [hEX0]
    change ψ (algebraMap (Polynomial k) (AdjoinRoot p) Polynomial.X) = _
    simpa [ψ, b] using
      (AdjoinRoot.isAdjoinRoot p).lift_algebraMap hroot Polynomial.X
  have hφY : φ (chapter03CuspY k) = Polynomial.X ^ 3 := by
    change ψ (E (chapter03CuspY k)) = _
    rw [hEX1]
    change ψ ((AdjoinRoot.isAdjoinRoot p).root) = _
    simpa [ψ] using (AdjoinRoot.isAdjoinRoot p).lift_root hroot
  let J : Ideal (Polynomial k) :=
    Ideal.span ({Polynomial.X} : Set (Polynomial k))
  have hXT : Polynomial.X ∈ J := by
    exact Ideal.subset_span (by simp)
  have hX2 : (Polynomial.X : Polynomial k) ^ 2 ∈ J := by
    change Polynomial.X ^ 2 ∈ Ideal.span ({Polynomial.X} : Set (Polynomial k))
    apply (Ideal.mem_span_singleton').2
    exact ⟨Polynomial.X, by ring⟩
  have hX3 : (Polynomial.X : Polynomial k) ^ 3 ∈ J := by
    change Polynomial.X ^ 3 ∈ Ideal.span ({Polynomial.X} : Set (Polynomial k))
    apply (Ideal.mem_span_singleton').2
    exact ⟨Polynomial.X ^ 2, by ring⟩
  have hle : chapter03CuspMaximalIdeal k ≤ Ideal.comap φ J := by
    change (Ideal.span ({MvPolynomial.X 0, MvPolynomial.X 1} :
      Set (MvPolynomial (Fin 2) k))).map (chapter03CuspQuotientMap k) ≤
      Ideal.comap φ J
    rw [Ideal.map_le_iff_le_comap]
    apply Ideal.span_le.2
    intro z hz
    rcases hz with rfl | rfl
    · change φ (chapter03CuspX k) ∈ J
      rw [hφX]
      exact hX2
    · change φ (chapter03CuspY k) ∈ J
      rw [hφY]
      exact hX3
  have hpre_ne_top : Ideal.comap φ J ≠ ⊤ := by
    intro htop
    have h1 : (1 : Polynomial k) ∈ J := by
      have h1' : (1 : Chapter03CuspRing k) ∈ Ideal.comap φ J := by
        rw [htop]
        exact Submodule.mem_top
      simpa [Ideal.mem_comap, J, φ] using h1'
    apply (show (Ideal.span ({Polynomial.X} : Set (Polynomial k)) :
        Ideal (Polynomial k)) ≠ ⊤ from
      Ideal.span_singleton_ne_top Polynomial.not_isUnit_X)
    exact (Ideal.span ({Polynomial.X} : Set (Polynomial k))).eq_top_iff_one.mpr h1
  have hcomap :
      Ideal.comap φ (chapter03CuspNormalizationOriginIdeal k) =
        chapter03CuspMaximalIdeal k := by
    change Ideal.comap φ J = _
    exact (chapter03_cusp_maximalIdeal_isMaximal k).eq_of_le hpre_ne_top hle |>.symm
  refine ⟨φ, ?_, hcomap⟩
  exact ⟨hφX, hφY, hφ⟩

noncomputable def chapter03CuspParametrizationMap (k : Type u) [Field k] :
    Chapter03CuspRing k →+* Polynomial k :=
  Classical.choose (chapter03_cusp_parametrization_exists k)

theorem chapter03_cusp_parametrization_map_eq_parametrization (k : Type u) [Field k] :
    chapter03CuspParametrization k (chapter03CuspParametrizationMap k) := by
  exact (Classical.choose_spec (chapter03_cusp_parametrization_exists k)).1

theorem chapter03_cusp_parametrization_map_preimage_origin (k : Type u) [Field k] :
    Ideal.comap (chapter03CuspParametrizationMap k)
        (chapter03CuspNormalizationOriginIdeal k) = chapter03CuspMaximalIdeal k := by
  exact (Classical.choose_spec (chapter03_cusp_parametrization_exists k)).2

theorem chapter03_cusp_parametrization_map_injective (k : Type u) [Field k] :
    Function.Injective (chapter03CuspParametrizationMap k) := by
  exact (chapter03_cusp_parametrization_map_eq_parametrization k).2.2

/- The scheme-theoretic inverse image of the cusp point under the normalization
   map is the effective Cartier divisor `2[0]`, not the reduced point. -/
theorem chapter03_cusp_parametrization_map_inverseImage_origin_is_effectiveCartier
    (k : Type u) [Field k] :
    Ideal.map (chapter03CuspParametrizationMap k) (chapter03CuspMaximalIdeal k) =
        Ideal.span ({Polynomial.X ^ 2} : Set (Polynomial k)) ∧
      IsRegular ((Polynomial.X : Polynomial k) ^ 2) := by
  have h := chapter03_cusp_parametrization_map_eq_parametrization k
  have hx : (chapter03CuspParametrizationMap k).comp (chapter03CuspQuotientMap k)
      (MvPolynomial.X 0) = Polynomial.X ^ 2 := by
    simpa [chapter03CuspParametrization, chapter03CuspX, RingHom.comp_apply] using h.1
  have hy : (chapter03CuspParametrizationMap k).comp (chapter03CuspQuotientMap k)
      (MvPolynomial.X 1) = Polynomial.X ^ 3 := by
    simpa [chapter03CuspParametrization, chapter03CuspY, RingHom.comp_apply] using h.2.1
  constructor
  · rw [chapter03CuspMaximalIdeal, Ideal.map_map, Ideal.map_span, Set.image_pair, hx, hy]
    simp [pow_succ]
  · exact IsRegular.of_ne_zero' (by simp)

/-- A normal scheme with a local point of dimension at least two can have a
Weil prime whose local equation does not exist. -/
def Chapter03NormalSurfaceNonCartierPrime
    {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X] [Chapter03Normal X]
    [Chapter03CartierDivisorTheory X] : Prop :=
  (∃ x : X, 2 ≤ ringKrullDim (X.presheaf.stalk x)) ∧
    ∃ P : Chapter03PrimeDivisor X,
      ¬ ∃ D : Chapter03CartierDivisor X,
        chapter03CartierDivisorToWeil X D = chapter03PrimeDivisorCycle P 1

theorem chapter03_normal_surface_nonCartierPrime_of_not_locallyFactorial
    {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X] [Chapter03Normal X]
    [Chapter03CartierDivisorTheory X]
    (hDim : ∃ x : X, 2 ≤ ringKrullDim (X.presheaf.stalk x))
    (h : ¬ Chapter03LocallyFactorial X) :
    Chapter03NormalSurfaceNonCartierPrime (X := X) := by
  exact ⟨hDim, chapter03_normal_nonCartier_prime_exists h⟩

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03
