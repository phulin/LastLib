import LastLib.Book03RamificationTheory.Chapter03.Dependencies
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.Section04WorkedEisensteinExtensions
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.Section06ResiduesAndLeadingCoefficients
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section07ConcreteFiniteExtensions
import Mathlib.FieldTheory.Finite.Valuation
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.SplittingField.IsSplittingField
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

namespace LastLib.Book03RamificationTheory.Chapter03

noncomputable section

open Polynomial
open scoped BigOperators LaurentSeries

/-! ## 3.3. An equal-characteristic wild extension -/

/- The Artin--Schreier equation used throughout this section. -/
def chapter03ArtinSchreierEquation
    (K : Type*) [Field K] (p m : ℕ) (t y : K) : Prop :=
  y ^ p - y = t ^ (-(m : ℤ))

/- The polynomial form of an Artin--Schreier equation. -/
def chapter03ArtinSchreierPolynomial
    {K : Type*} [CommRing K] (p : ℕ) (a : K) : K[X] :=
  X ^ p - X - C a

def chapter03ArtinSchreierRootSet
    {K : Type*} [Field K] (p : ℕ) (a : K) : Set K :=
  {z | z ^ p - z = a}

/- The equation and generation data for `y^p-y=t^{-m}`. -/
structure Chapter03ArtinSchreierExtensionData
    {k L : Type*} [Field k] [Field L]
    [Algebra (LaurentSeries k) L]
    [FiniteDimensional (LaurentSeries k) L]
    (p m : ℕ) [Fact p.Prime] [CharP k p] where
  y : L
  positive_exponent : 0 < m
  prime_to_characteristic : Nat.Coprime m p
  equation :
    chapter03ArtinSchreierEquation L p m
      (algebraMap (LaurentSeries k) L
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.laurentSeriesUniformizer k)) y
  generated : Algebra.adjoin (LaurentSeries k) ({y} : Set L) = ⊤

theorem chapter03_artin_schreier_derivative
    {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (a : K) :
    (chapter03ArtinSchreierPolynomial p a).derivative = -1 := by
  simp [chapter03ArtinSchreierPolynomial, Polynomial.derivative_sub,
    Polynomial.derivative_X_pow, Polynomial.derivative_X,
    Polynomial.derivative_C, CharP.cast_eq_zero]

theorem chapter03_artin_schreier_no_root_in_laurent_series
    (k : Type*) [Field k] (p m : ℕ) [Fact p.Prime] [CharP k p]
    (hm : Nat.Coprime m p) :
    ∀ z : LaurentSeries k,
      z ^ p - z ≠
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.laurentSeriesUniformizer k) ^
          (-(m : ℤ)) := by
  intro z hEq
  let t : LaurentSeries k :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.laurentSeriesUniformizer k
  change z ^ p - z = t ^ (-(m : ℤ)) at hEq
  have ht : t ≠ 0 := by
    dsimp [t]
    exact HahnSeries.single_ne_zero one_ne_zero
  have hright_ne : t ^ (-(m : ℤ)) ≠ 0 := zpow_ne_zero _ ht
  have hmpos : 0 < m := by
    by_contra hm'
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm'
    subst m
    have hp1 : p = 1 := (Nat.coprime_zero_left p).mp hm
    exact (Fact.out : Nat.Prime p).ne_one hp1
  have hright_order : (t ^ (-(m : ℤ))).order = -(m : ℤ) := by
    dsimp [t]
    change (HahnSeries.single (1 : ℤ) (1 : k) ^ (-(m : ℤ))).order = -(m : ℤ)
    rw [← RatFunc.single_zpow]
    exact HahnSeries.order_single one_ne_zero
  have hleft_ne : z ^ p - z ≠ 0 := by
    intro hzero
    apply hright_ne
    rw [← hEq, hzero]
  have hz0 : z ≠ 0 := by
    intro hz
    apply hright_ne
    rw [← hEq, hz]
    simp [(Fact.out : Nat.Prime p).ne_zero]
  have hpn_lt : p • z.order < z.order := by
    have hpz : (1 : ℤ) < (p : ℤ) := by
      exact_mod_cast (Fact.out : Nat.Prime p).one_lt
    have hnz : z.order < 0 := by
      by_contra hnz'
      have hnz'' : 0 ≤ z.order := le_of_not_gt hnz'
      have hmin := HahnSeries.min_order_le_order_add (x := z ^ p) (y := -z)
        (by simpa [sub_eq_add_neg] using hleft_ne)
      rw [HahnSeries.order_pow, HahnSeries.order_neg] at hmin
      have hmin' : min (p • z.order) z.order ≤ (z ^ p - z).order := by
        simpa [sub_eq_add_neg] using hmin
      have hnonneg : 0 ≤ (z ^ p - z).order :=
        le_trans (le_min (nsmul_nonneg hnz'' p) hnz'') hmin'
      have hord := congrArg (fun f : LaurentSeries k => f.order) hEq
      rw [hord, hright_order] at hnonneg
      omega
    have hmul : (p : ℤ) * z.order < (1 : ℤ) * z.order :=
      mul_lt_mul_of_neg_right hpz hnz
    simpa [nsmul_eq_mul] using hmul
  have hstrict : (z ^ p).order < (-z).order := by
    simpa [HahnSeries.order_pow, HahnSeries.order_neg] using hpn_lt
  have hleft_order : (z ^ p - z).order = p • z.order := by
    have htop : (z ^ p - z).orderTop = (z ^ p).orderTop := by
      rw [sub_eq_add_neg]
      apply HahnSeries.orderTop_add_eq_left
      rw [← HahnSeries.order_eq_orderTop_of_ne_zero (pow_ne_zero p hz0),
        ← HahnSeries.order_eq_orderTop_of_ne_zero (neg_ne_zero.mpr hz0)]
      exact_mod_cast hstrict
    have horder_coe :
        (z ^ p - z).order = (z ^ p).order := by
      apply WithTop.coe_eq_coe.mp
      calc
        ((z ^ p - z).order : WithTop ℤ) = (z ^ p - z).orderTop :=
          HahnSeries.order_eq_orderTop_of_ne_zero hleft_ne
        _ = (z ^ p).orderTop := htop
        _ = ((z ^ p).order : WithTop ℤ) :=
          (HahnSeries.order_eq_orderTop_of_ne_zero (pow_ne_zero p hz0)).symm
    calc
      (z ^ p - z).order = (z ^ p).order := horder_coe
      _ = p • z.order := by simp [HahnSeries.order_pow]
  have hord := congrArg (fun f : LaurentSeries k => f.order) hEq
  rw [hleft_order, hright_order] at hord
  have hEqInt : p • z.order = -(m : ℤ) := hord
  have hdvdZ : (p : ℤ) ∣ (m : ℤ) := by
    refine ⟨-z.order, ?_⟩
    have hEqInt' : (p : ℤ) * z.order = -(m : ℤ) := by
      simpa [nsmul_eq_mul] using hEqInt
    calc
      (m : ℤ) = -(-(m : ℤ)) := by ring
      _ = -((p : ℤ) * z.order) := by rw [hEqInt']
      _ = (p : ℤ) * (-z.order) := by ring
  have hdvd : p ∣ m := Int.natCast_dvd_natCast.mp hdvdZ
  exact ((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp hm.symm) hdvd

theorem chapter03_artin_schreier_translation
    {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (a y z : K) (hroot : y ^ p - y = a) :
    (y - z) ^ p - (y - z) = a - (z ^ p - z) := by
  calc
    (y - z) ^ p - (y - z) = (y ^ p - y) - (z ^ p - z) := by
      rw [sub_pow_char]
      ring
    _ = a - (z ^ p - z) := by rw [hroot]

theorem chapter03_artin_schreier_root_set_is_a_translation
    {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (a y : K) (hroot : y ^ p - y = a) :
    chapter03ArtinSchreierRootSet p a =
      {z | ∃ c : K, c ^ p - c = 0 ∧ z = y + c} := by
  ext z
  change z ^ p - z = a ↔ ∃ c : K, c ^ p - c = 0 ∧ z = y + c
  constructor
  · intro hz
    refine ⟨z - y, ?_, by ring⟩
    calc
      (z - y) ^ p - (z - y) = (z ^ p - z) - (y ^ p - y) := by
        rw [sub_pow_char]
        ring
      _ = 0 := by rw [hz, hroot, sub_self]
  · rintro ⟨c, hc, rfl⟩
    calc
      (y + c) ^ p - (y + c) = (y ^ p - y) + (c ^ p - c) := by
        rw [add_pow_char]
        ring
      _ = a := by rw [hroot, hc, add_zero]

theorem chapter03_artin_schreier_irreducible_of_no_root
    {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (a : K)
    (hno_root : ∀ z : K, z ^ p - z ≠ a) :
    Irreducible (chapter03ArtinSchreierPolynomial p a) := by
  let f : K[X] := chapter03ArtinSchreierPolynomial p a
  change Irreducible f
  have hpone : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have hmonic : f.Monic := by
    dsimp [f, chapter03ArtinSchreierPolynomial]
    have hdeg : degree (-(X + C a) : K[X]) < p := by
      rw [degree_neg, degree_X_add_C]
      exact_mod_cast hpone
    have h := monic_X_pow_add (p := (-(X + C a) : K[X])) (n := p) hdeg
    convert h using 1; ring
  have hnat : f.natDegree = p := by
    dsimp [f, chapter03ArtinSchreierPolynomial]
    have hdeg : degree (-(X + C a) : K[X]) < p := by
      rw [degree_neg, degree_X_add_C]
      exact_mod_cast hpone
    have hdeg' : degree (-(X + C a) : K[X]) < (X ^ p : K[X]).degree := by
      simpa [degree_X_pow] using hdeg
    rw [show X ^ p - X - C a = X ^ p + -(X + C a) by ring]
    rw [natDegree_add_eq_left_of_degree_lt hdeg', natDegree_X_pow]
  have hp1 : f ≠ 1 := by
    intro hf
    have := congrArg Polynomial.natDegree hf
    rw [hnat] at this
    have hpzero : p = 0 := by simpa using this
    exact (Nat.ne_of_gt (Fact.out : Nat.Prime p).pos) hpzero
  let : Algebra (ZMod p) K := ZMod.algebra _ _
  have hc0 (c : ZMod p) :
      (algebraMap (ZMod p) K c)^p - algebraMap (ZMod p) K c = 0 := by
    have hc : c ^ p = c := by
      simp
    rw [← map_pow, hc, sub_self]
  have hftrans (c : ZMod p) :
      f.comp (X + C (algebraMap (ZMod p) K c)) = f := by
    have hc' : (algebraMap (ZMod p) K c)^p =
        algebraMap (ZMod p) K c := sub_eq_zero.mp (hc0 c)
    dsimp [f, chapter03ArtinSchreierPolynomial]
    rw [comp_eq_aeval]
    simp only [map_sub, map_pow, aeval_X, aeval_C]
    rw [add_pow_char, ← C_pow, hc', Polynomial.algebraMap_apply,
      Algebra.algebraMap_self_apply]
    ring
  have hperiod_n (g : K[X]) (h : K)
      (hperiod : g.comp (X + C h) = g) :
      ∀ n : ℕ, g.comp (X + C (n • h)) = g := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hcomp :
            (X + C (n • h)).comp (X + C h) =
              X + C ((Nat.succ n) • h) := by
          simp [nsmul_eq_mul, Nat.cast_succ, C_add, add_mul, mul_comm, add_comm]
          ring
        have hh := congrArg (fun r : K[X] => r.comp (X + C h)) ih
        rw [comp_assoc, hcomp] at hh
        simpa [Nat.succ_eq_add_one] using hh.trans hperiod
  have hperiod_all (g : K[X]) (h0 : ZMod p)
      (hperiod : g.comp (X + C (algebraMap (ZMod p) K h0)) = g)
      (hh : h0 ≠ 0) :
      ∀ c : ZMod p, g.comp (X + C (algebraMap (ZMod p) K c)) = g := by
    let : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
    intro c
    let n : ℕ := (c * h0⁻¹).val
    have hc : c = (n : ZMod p) * h0 := by
      dsimp [n]
      calc
        c = (c * h0⁻¹) * h0 := by
          field_simp [hh]
        _ = ((c * h0⁻¹).val : ZMod p) * h0 := by
          rw [ZMod.natCast_zmod_val]
    have hn := hperiod_n g (algebraMap (ZMod p) K h0) hperiod n
    calc
      g.comp (X + C (algebraMap (ZMod p) K c)) =
          g.comp (X + C (algebraMap (ZMod p) K ((n : ZMod p) * h0))) := by
            rw [hc]
      _ = g.comp (X + C ((n : K) * algebraMap (ZMod p) K h0)) := by
        congr 2
        simp
      _ = g := by simpa [nsmul_eq_mul] using hn
  have hno_period (g : K[X]) (hg : Irreducible g) (hdeg : g.natDegree < p)
      (h0 : ZMod p) (hh : h0 ≠ 0)
      (hperiod : g.comp (X + C (algebraMap (ZMod p) K h0)) = g) : False := by
    obtain ⟨α, hα⟩ :=
      IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure K) g
        (degree_pos_of_irreducible hg).ne'
    have hpermall := hperiod_all g h0 hperiod hh
    have hroot (c : ZMod p) :
        aeval (α + algebraMap K (AlgebraicClosure K)
          (algebraMap (ZMod p) K c)) g = 0 := by
      have hc := congrArg
        (fun q : K[X] => aeval α q) (hpermall c)
      simpa [aeval_comp, hα] using hc
    let rootfun : ZMod p → g.rootSet (AlgebraicClosure K) := fun c =>
      ⟨α + algebraMap K (AlgebraicClosure K)
          (algebraMap (ZMod p) K c),
        (Polynomial.mem_rootSet_of_ne hg.ne_zero).2 (hroot c)⟩
    have hinj : Function.Injective rootfun := by
      intro c d hcd
      have hsum := congrArg Subtype.val hcd
      have hmapE :
          algebraMap K (AlgebraicClosure K) (algebraMap (ZMod p) K c) =
            algebraMap K (AlgebraicClosure K) (algebraMap (ZMod p) K d) := by
        exact add_left_cancel hsum
      have hmapK : (algebraMap (ZMod p) K c) =
          algebraMap (ZMod p) K d :=
        (FaithfulSMul.algebraMap_injective K (AlgebraicClosure K)) hmapE
      exact (FaithfulSMul.algebraMap_injective (ZMod p) K) hmapK
    have hcard :
        Fintype.card (ZMod p) ≤ Fintype.card (g.rootSet (AlgebraicClosure K)) :=
      Fintype.card_le_of_injective rootfun hinj
    have hrootcard : Fintype.card (g.rootSet (AlgebraicClosure K)) ≤ g.natDegree := by
      rw [Set.fintypeCard_eq_ncard]
      exact Polynomial.ncard_rootSet_le g (AlgebraicClosure K)
    have hp_le : p ≤ g.natDegree := by
      simpa [ZMod.card] using hcard.trans hrootcard
    exact (Nat.not_lt_of_ge hp_le) hdeg
  have htrans (g : K[X]) (c : K) (hg : Irreducible g) :
      Irreducible (g.comp (X + C c)) := by
    change Irreducible ((algEquivAevalXAddC c) g)
    exact (MulEquiv.irreducible_iff
      (f := (algEquivAevalXAddC c).toMulEquiv) (x := g)).mpr hg
  have hperiod_test (g : K[X]) (c d : K)
      (hEq : g.comp (X + C c) = g.comp (X + C d)) :
      g.comp (X + C (c - d)) = g := by
    have h := congrArg (fun r : K[X] => r.comp (X - C d)) hEq
    simpa [comp_assoc, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
  rw [hmonic.irreducible_iff_lt_natDegree_lt hp1]
  intro q hqmonic hqdeg hqdiv
  have hqdeg' : 0 < q.natDegree ∧ q.natDegree ≤ f.natDegree / 2 :=
    Finset.mem_Ioc.mp hqdeg
  obtain ⟨g, hgmonic, hg, hgdiv⟩ :=
    Polynomial.exists_monic_irreducible_factor q
      (not_isUnit_of_natDegree_pos q hqdeg'.1)
  have hgdivf : g ∣ f := hgdiv.trans hqdiv
  have hgdeg_le : g.natDegree ≤ q.natDegree :=
    natDegree_le_of_dvd hgdiv hqmonic.ne_zero
  have hq_lt : q.natDegree < p := by
    rw [hnat] at hqdeg'
    exact lt_of_le_of_lt hqdeg'.2
      (Nat.div_lt_self (Nat.zero_lt_of_lt hpone) (by decide))
  have hgdeg_lt : g.natDegree < p := hgdeg_le.trans_lt hq_lt
  let gfun (c : ZMod p) : K[X] :=
    g.comp (X + C (algebraMap (ZMod p) K c))
  have hdeg_gfun (c : ZMod p) : (gfun c).natDegree = g.natDegree := by
    simp [gfun, natDegree_comp]
  have hmonic_gfun (c : ZMod p) : (gfun c).Monic := by
    exact hgmonic.comp_X_add_C _
  have hirr_gfun (c : ZMod p) : Irreducible (gfun c) := by
    exact htrans g (algebraMap (ZMod p) K c) hg
  have hdistinct (c d : ZMod p) (hcd : c ≠ d) : gfun c ≠ gfun d := by
    intro heq
    have hperiod := hperiod_test g
      (algebraMap (ZMod p) K c) (algebraMap (ZMod p) K d) (by simpa [gfun] using heq)
    have hperiod' :
        g.comp (X + C (algebraMap (ZMod p) K (c - d))) = g := by
      simpa [map_sub] using hperiod
    exact hno_period g hg hgdeg_lt (c - d) (sub_ne_zero.mpr hcd) hperiod'
  have hcoprime (c d : ZMod p) (hcd : c ≠ d) :
      IsCoprime (gfun c) (gfun d) := by
    apply isCoprime_of_irreducible_dvd
    · exact fun hzero => (hmonic_gfun c).ne_zero hzero.1
    · intro z hz hzc
      have hzg : Associated z (gfun c) :=
        (hz.dvd_irreducible_iff_associated (hirr_gfun c)).mp hzc
      intro hzd
      have hzd' : Associated z (gfun d) :=
        (hz.dvd_irreducible_iff_associated (hirr_gfun d)).mp hzd
      apply hdistinct c d hcd
      exact eq_of_monic_of_associated (hmonic_gfun c) (hmonic_gfun d)
        (hzg.symm.trans hzd')
  have hdivfun (c : ZMod p) : gfun c ∣ f := by
    have hfneg : f.comp (X + C (-(algebraMap (ZMod p) K c))) = f := by
      simpa using hftrans (-c)
    have hleft : g ∣ f.comp (X + C (-(algebraMap (ZMod p) K c))) := by
      rw [hfneg]
      exact hgdivf
    have hright := (dvd_comp_X_add_C_iff g f
      (-(algebraMap (ZMod p) K c))).mp hleft
    simpa [sub_eq_add_neg] using hright
  have hproddiv : (∏ c : ZMod p, gfun c) ∣ f := by
    apply Fintype.prod_dvd_of_coprime
    · intro c d hcd
      exact hcoprime c d hcd
    · exact hdivfun
  have hproddeg : (∏ c : ZMod p, gfun c).natDegree = p * g.natDegree := by
    calc
      (∏ c : ZMod p, gfun c).natDegree =
          ∑ c : ZMod p, (gfun c).natDegree := by
        simpa using (Polynomial.natDegree_prod_of_monic
          (s := Finset.univ) (f := gfun) (by
            intro c hc
            exact hmonic_gfun c))
      _ = p * g.natDegree := by simp [hdeg_gfun]
  have hprod_le : (∏ c : ZMod p, gfun c).natDegree ≤ f.natDegree :=
    natDegree_le_of_dvd hproddiv hmonic.ne_zero
  rw [hproddeg, hnat] at hprod_le
  by_cases hg1 : g.natDegree = 1
  · have hgform : g = X + C (g.coeff 0) := hgmonic.eq_X_add_C hg1
    let z : K := -g.coeff 0
    have hzroot : IsRoot g z := by
      rw [hgform]
      simp [z]
    have hfroot := hzroot.dvd hgdivf
    apply hno_root z
    simpa [f, chapter03ArtinSchreierPolynomial, IsRoot, eval_sub,
      eval_C, eval_X, eval_X_pow, sub_eq_zero] using hfroot
  · have hg_gt_one : 1 < g.natDegree := by
      exact lt_of_le_of_ne hg.natDegree_pos (Ne.symm hg1)
    have hstrict : p < p * g.natDegree := by
      simpa using ((Nat.mul_lt_mul_left (Fact.out : Nat.Prime p).pos).2 hg_gt_one)
    exact (Nat.not_lt_of_ge hprod_le) hstrict

theorem chapter03_artin_schreier_roots_form_a_prime_order_orbit
    {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (a y : K) (hroot : y ^ p - y = a) :
    ∀ z : K, z ^ p - z = a →
      ∃ c : K, c ^ p - c = 0 ∧ z = y + c := by
  intro z hz
  have hz' : z ∈ chapter03ArtinSchreierRootSet p a := by
    simpa [chapter03ArtinSchreierRootSet] using hz
  rw [chapter03_artin_schreier_root_set_is_a_translation p a y hroot] at hz'
  exact hz'

theorem chapter03_artin_schreier_degree_and_cyclic_profile
    {k L : Type*} [Field k] [Field L]
    [Algebra (LaurentSeries k) L]
    [FiniteDimensional (LaurentSeries k) L]
    (p m : ℕ) [Fact p.Prime] [CharP k p]
    (D : Chapter03ArtinSchreierExtensionData (k := k) (L := L) p m)
    (hno_root :
      ∀ z : LaurentSeries k,
        z ^ p - z ≠
            (LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.laurentSeriesUniformizer k) ^
            (-(m : ℤ)))
    (vK : AddValuation (LaurentSeries k) (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hdiscreteK :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vK)
    (hdiscreteL :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vL)
    (hext : vK.IsEquiv (vL.comap (algebraMap (LaurentSeries k) L)))
    (hvalue_t :
      vK (LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.laurentSeriesUniformizer k) = 1) :
    Module.finrank (LaurentSeries k) L = p ∧
      ∃ d : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10HeterogeneousExtensionData
          vK vL hext,
        ∃ q : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10FiniteExtensionProfile,
          LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ProfileRealizedByData d q ∧
            q.degree = p ∧ q.ramificationIndex = p ∧ q.residueDegree = 1 ∧
            LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10TotallyRamified q := by
  let : CharP (LaurentSeries k) p :=
    charP_of_injective_ringHom
      (f := (HahnSeries.C : k →+* LaurentSeries k))
      HahnSeries.C_injective p
  let : CharP L p :=
    charP_of_injective_algebraMap (algebraMap (LaurentSeries k) L).injective p
  let t : LaurentSeries k :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.laurentSeriesUniformizer k
  let a : LaurentSeries k := t ^ (-(m : ℤ))
  have hEq : D.y ^ p - D.y = algebraMap (LaurentSeries k) L a := by
    simpa [a, t, chapter03ArtinSchreierEquation] using D.equation
  have hroot : Polynomial.aeval D.y
      (chapter03ArtinSchreierPolynomial p a) = 0 := by
    rw [Polynomial.aeval_def]
    change (X ^ p - X - C a).eval₂ (algebraMap (LaurentSeries k) L) D.y = 0
    rw [eval₂_sub, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C]
    change D.y ^ p - D.y - algebraMap (LaurentSeries k) L a = 0
    rw [hEq]
    exact sub_self _
  have hf : Irreducible (chapter03ArtinSchreierPolynomial p a) :=
    chapter03_artin_schreier_irreducible_of_no_root p a (by
      intro z hz
      apply hno_root z
      simpa [a, t] using hz)
  have hmin_dvd :
      minpoly (LaurentSeries k) D.y ∣ chapter03ArtinSchreierPolynomial p a :=
    minpoly.dvd (LaurentSeries k) D.y hroot
  have hmonic : (chapter03ArtinSchreierPolynomial p a).Monic := by
    dsimp [chapter03ArtinSchreierPolynomial]
    have hdeg : degree (-(X + C a) : (LaurentSeries k)[X]) < p := by
      rw [degree_neg, degree_X_add_C]
      exact_mod_cast (Fact.out : Nat.Prime p).one_lt
    have h :=
      monic_X_pow_add (p := (-(X + C a) : (LaurentSeries k)[X])) (n := p) hdeg
    have hpoly : X ^ p + -(X + C a) = X ^ p - X - C a := by ring
    rw [← hpoly]
    exact h
  have hnat : (chapter03ArtinSchreierPolynomial p a).natDegree = p := by
    dsimp [chapter03ArtinSchreierPolynomial]
    have hdeg : degree (-(X + C a) : (LaurentSeries k)[X]) < p := by
      rw [degree_neg, degree_X_add_C]
      exact_mod_cast (Fact.out : Nat.Prime p).one_lt
    have hdeg' : degree (-(X + C a) : (LaurentSeries k)[X]) <
        (X ^ p : (LaurentSeries k)[X]).degree := by
      simpa [degree_X_pow] using hdeg
    rw [show X ^ p - X - C a = X ^ p + -(X + C a) by ring]
    rw [natDegree_add_eq_left_of_degree_lt hdeg', natDegree_X_pow]
  have hmin_eq :
      minpoly (LaurentSeries k) D.y = chapter03ArtinSchreierPolynomial p a := by
    exact eq_of_monic_of_associated
      (minpoly.monic (Algebra.IsIntegral.isIntegral D.y)) hmonic
      ((minpoly.irreducible (Algebra.IsIntegral.isIntegral D.y)).associated_of_dvd
        hf hmin_dvd)
  have hgen' : IntermediateField.adjoin (LaurentSeries k) ({D.y} : Set L) =
      (⊤ : IntermediateField (LaurentSeries k) L) :=
    IntermediateField.adjoin_eq_top_of_algebra (LaurentSeries k) ({D.y} : Set L)
      D.generated
  have hminpoly_degree :
      (minpoly (LaurentSeries k) D.y).natDegree = p := by
    rw [hmin_eq]
    exact hnat
  have hadjfin :
      Module.finrank (LaurentSeries k)
          (IntermediateField.adjoin (LaurentSeries k) ({D.y} : Set L)) =
        (minpoly (LaurentSeries k) D.y).natDegree :=
    IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral D.y)
  have hfinrank : Module.finrank (LaurentSeries k) L = p := by
    have hadjfin' := hadjfin
    rw [hgen'] at hadjfin'
    have htop : Module.finrank (LaurentSeries k)
        (⊤ : IntermediateField (LaurentSeries k) L) =
        Module.finrank (LaurentSeries k) L :=
      IntermediateField.finrank_top'
    calc
      Module.finrank (LaurentSeries k) L =
          Module.finrank (LaurentSeries k)
            (⊤ : IntermediateField (LaurentSeries k) L) := htop.symm
      _ = (minpoly (LaurentSeries k) D.y).natDegree := hadjfin'
      _ = p := hminpoly_degree
  have ht : t ≠ 0 := by
    dsimp [t]
    exact HahnSeries.single_ne_zero one_ne_zero
  obtain ⟨e, hepos, hscale⟩ :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_normalized_restriction_formula
      vK vL hdiscreteK hdiscreteL hext
  have hvalue_tL :
      vL (algebraMap (LaurentSeries k) L t) = (e : WithTop ℤ) := by
    have h := hscale t ht
    rw [hvalue_t] at h
    simpa using h
  have hpow : ∀ (x : L) (n : ℤ), vL (x ^ n) = n • vL x := by
    intro x n
    cases n with
    | ofNat n => simp [zpow_natCast, vL.map_pow]
    | negSucc n =>
        rw [zpow_negSucc, vL.map_inv, vL.map_pow]
        simp
  have hright :
      vL (algebraMap (LaurentSeries k) L t ^ (-(m : ℤ))) =
        -(m * e : ℤ) := by
    rw [hpow, hvalue_tL]
    have hscalarInt (n x : ℤ) : n • (x : WithTop ℤ) = (n * x : ℤ) := by
      simpa [zsmul_eq_mul] using
        ((WithTop.addHom : ℤ →+ WithTop ℤ).map_zsmul n x).symm
    have hscalarIntNat (n : ℤ) (q : ℕ) :
        n • (q : WithTop ℤ) = (n * (q : ℤ) : ℤ) := by
      simpa using hscalarInt n (q : ℤ)
    rw [hscalarIntNat (-m) e]
    norm_cast
    rw [Nat.cast_mul]
    ring
  have heqv := congrArg vL D.equation
  rw [hright] at heqv
  have hmpos : 0 < m := D.positive_exponent
  have hpone : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have hpe : p ∣ e := by
    by_cases hyneg : vL D.y < 0
    · have hmul : p • vL D.y < vL D.y := by
        have hnegmul : (p - 1) • vL D.y < 0 :=
          nsmul_neg hyneg (Nat.sub_ne_zero_of_lt hpone)
        have hadd : (p - 1) • vL D.y + vL D.y < 0 + vL D.y :=
          WithTop.add_lt_add_right (ne_top_of_lt hyneg) hnegmul
        calc
          p • vL D.y = (p - 1 + 1) • vL D.y := by
            rw [Nat.sub_add_cancel (le_of_lt hpone)]
          _ = (p - 1) • vL D.y + 1 • vL D.y := by rw [add_nsmul]
          _ = (p - 1) • vL D.y + vL D.y := by rw [one_nsmul]
          _ < 0 + vL D.y := hadd
          _ = vL D.y := zero_add _
      have hmul' : vL (D.y ^ p) < vL D.y := by
        simpa [vL.map_pow] using hmul
      have hsub := vL.map_sub_eq_of_lt_left (x := D.y ^ p) (y := D.y) hmul'
      rw [hsub] at heqv
      rw [vL.map_pow] at heqv
      have hvaltop : vL D.y ≠ (⊤ : WithTop ℤ) := ne_top_of_lt hyneg
      let q : ℤ := (vL D.y).untop hvaltop
      have hq : (q : WithTop ℤ) = vL D.y := by
        exact WithTop.coe_untop (vL D.y) hvaltop
      rw [← hq] at heqv
      have hqeq : p • q = -(m * e : ℤ) := by
        apply WithTop.coe_eq_coe.mp
        calc
          ((p • q : ℤ) : WithTop ℤ) = p • (q : WithTop ℤ) :=
            (WithTop.coe_nsmul q p).symm
          _ = -(m * e : ℤ) := heqv
      have hdivZ : (p : ℤ) ∣ (m * e : ℤ) := by
        refine ⟨-q, ?_⟩
        have hqeq' : (p : ℤ) * q = -(m * e : ℤ) := by
          simpa [nsmul_eq_mul] using hqeq
        calc
          (m * e : ℤ) = -(-(m * e : ℤ)) := by ring
          _ = -((p : ℤ) * q) := by rw [hqeq']
          _ = (p : ℤ) * (-q) := by ring
      have hdiv : p ∣ m * e := Int.natCast_dvd_natCast.mp hdivZ
      exact ((D.prime_to_characteristic.symm).dvd_mul_left).mp hdiv
    · have hy_nonneg : 0 ≤ vL D.y := le_of_not_gt hyneg
      have hpow_nonneg : 0 ≤ p • vL D.y := nsmul_nonneg hy_nonneg p
      have hsub_nonneg : 0 ≤ vL (D.y ^ p - D.y) := by
        have hmin := vL.map_sub (D.y ^ p) D.y
        have hpow_nonneg' : 0 ≤ vL (D.y ^ p) := by
          simpa [vL.map_pow] using hpow_nonneg
        exact le_trans (le_min hpow_nonneg' hy_nonneg) hmin
      rw [heqv] at hsub_nonneg
      have hneg : -(m * e : ℤ) < 0 := by
        have hme : 0 < m * e := Nat.mul_pos hmpos hepos
        have hmeZ : 0 < (m * e : ℤ) := by exact_mod_cast hme
        exact neg_lt_zero.mpr hmeZ
      have hbad : (0 : ℤ) ≤ -(m * e : ℤ) := by
        exact_mod_cast hsub_nonneg
      exact (not_le_of_gt hneg hbad).elim
  obtain ⟨d⟩ :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_heterogeneous_extension_data_exists
      vK vL hext
  let : Finite
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vL ⧸
        d.valueGroupMap.range) := d.finite_quotient
  have hri :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_normalized_ramification_index_eq_scale
      vK vL hdiscreteK hdiscreteL hext d e hepos hscale
  have hfund :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_heterogeneous_single_extension_fundamental_inequality
      vK vL hext d
  have hrespos : 0 < d.residueDegree := by
    rw [d.residueDegree_eq]
    unfold LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10HeterogeneousResidueDegree
    let vk : Valuation (LaurentSeries k) (Multiplicative (WithTop ℤ)ᵒᵈ) := vK
    let vl : Valuation L (Multiplicative (WithTop ℤ)ᵒᵈ) := vL
    let : Valuation.HasExtension vk vl := ⟨hext⟩
    let : Algebra vk.valuationSubring vl.valuationSubring :=
      Valuation.HasExtension.instAlgebra_valuationSubring vk vl
    let : IsLocalHom
        (algebraMap vk.valuationSubring vl.valuationSubring) :=
      Valuation.HasExtension.instIsLocalHomValuationInteger
        (vR := vk) (vS := vl)
    let : Algebra
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ResidueField vk)
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ResidueField vl) :=
      inferInstance
    let : Module
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ResidueField vk)
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ResidueField vl) :=
      Algebra.toModule
    let : FiniteDimensional
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ResidueField vk)
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ResidueField vl) :=
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_residue_degree_finite
        vk vl
    change 0 < Module.finrank
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ResidueField vk)
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ResidueField vl)
    exact Module.finrank_pos
  have he_le : e ≤ p := by
    have hprod : e * d.residueDegree ≤ p := by
      simpa [hri.2, hfinrank] using hfund
    calc
      e = e * 1 := by simp
      _ ≤ e * d.residueDegree :=
        Nat.mul_le_mul_left e
          (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hrespos))
      _ ≤ p := hprod
  have hep : p ≤ e := Nat.le_of_dvd hepos hpe
  have hep_eq : e = p := Nat.le_antisymm he_le hep
  have hdres_le : d.residueDegree ≤ 1 := by
    have hprod : p * d.residueDegree ≤ p := by
      simpa [hri.2, hep_eq, hfinrank] using hfund
    apply Nat.le_of_mul_le_mul_left
      (by simpa [Nat.mul_one] using hprod)
    exact (Fact.out : Nat.Prime p).pos
  have hdres : d.residueDegree = 1 := by
    exact Nat.le_antisymm hdres_le
      (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hrespos))
  let q : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10FiniteExtensionProfile :=
    { degree := p, ramificationIndex := p, residueDegree := 1 }
  refine ⟨hfinrank, d, q, ?_, rfl, rfl, rfl, ?_⟩
  · exact ⟨hfinrank.symm, hep_eq.symm.trans hri.2.symm, hdres.symm⟩
  · exact ⟨rfl, rfl⟩

theorem chapter03_artin_schreier_y_has_normalized_value
    {k L : Type*} [Field k] [Field L]
    [Algebra (LaurentSeries k) L]
    [FiniteDimensional (LaurentSeries k) L]
    (p m : ℕ) [Fact p.Prime] [CharP k p]
    (D : Chapter03ArtinSchreierExtensionData (k := k) (L := L) p m)
    (vL : AddValuation L (WithTop ℤ))
    (hvalue_t :
      vL (algebraMap (LaurentSeries k) L
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.laurentSeriesUniformizer k)) = p) :
    vL D.y = -m := by
  have hmpos : 0 < m := D.positive_exponent
  have hpone : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have hright :
      vL (algebraMap (LaurentSeries k) L
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.laurentSeriesUniformizer k) ^
          (-(m : ℤ))) = -(m * p : ℤ) := by
    have hpow : ∀ (x : L) (n : ℤ), vL (x ^ n) = n • vL x := by
      intro x n
      cases n with
      | ofNat n => simp [zpow_natCast, vL.map_pow]
      | negSucc n =>
          rw [zpow_negSucc, vL.map_inv, vL.map_pow]
          simp
    rw [hpow, hvalue_t]
    have hscalarInt (n x : ℤ) : n • (x : WithTop ℤ) = (n * x : ℤ) := by
      simpa [zsmul_eq_mul] using
        ((WithTop.addHom : ℤ →+ WithTop ℤ).map_zsmul n x).symm
    have hscalarIntNat (n : ℤ) (q : ℕ) :
        n • (q : WithTop ℤ) = (n * (q : ℤ) : ℤ) := by
      simpa using hscalarInt n (q : ℤ)
    rw [hscalarIntNat (-m) p]
    norm_cast
    rw [Nat.cast_mul]
    ring_nf
  have heqv := congrArg vL D.equation
  rw [hright] at heqv
  by_cases hyneg : vL D.y < 0
  · have hmul : p • vL D.y < vL D.y := by
      have hnegmul : (p - 1) • vL D.y < 0 :=
        nsmul_neg hyneg (Nat.sub_ne_zero_of_lt hpone)
      have hadd : (p - 1) • vL D.y + vL D.y < 0 + vL D.y :=
        WithTop.add_lt_add_right (ne_top_of_lt hyneg) hnegmul
      calc
        p • vL D.y = (p - 1 + 1) • vL D.y := by
          rw [Nat.sub_add_cancel (le_of_lt hpone)]
        _ = (p - 1) • vL D.y + 1 • vL D.y := by rw [add_nsmul]
        _ = (p - 1) • vL D.y + vL D.y := by rw [one_nsmul]
        _ < 0 + vL D.y := hadd
        _ = vL D.y := zero_add _
    have hmul' : vL (D.y ^ p) < vL D.y := by
      simpa [vL.map_pow] using hmul
    have hsub := vL.map_sub_eq_of_lt_left (x := D.y ^ p) (y := D.y) hmul'
    rw [hsub] at heqv
    rw [vL.map_pow] at heqv
    have hvaltop : vL D.y ≠ (⊤ : WithTop ℤ) := ne_top_of_lt hyneg
    let q : ℤ := (vL D.y).untop hvaltop
    have hq : (q : WithTop ℤ) = vL D.y := by
      exact WithTop.coe_untop (vL D.y) hvaltop
    rw [← hq] at heqv
    have hqeq : p • q = -(m : ℤ) * (p : ℤ) := by
      apply WithTop.coe_eq_coe.mp
      calc
        ((p • q : ℤ) : WithTop ℤ) = p • (q : WithTop ℤ) :=
          (WithTop.coe_nsmul q p).symm
        _ = -(m * p : ℤ) := heqv
        _ = (-(m : ℤ) * (p : ℤ) : ℤ) := by
          simp
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
    have hqval : q = -(m : ℤ) := by
      apply (mul_left_cancel₀ hp0)
      simpa [nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hqeq
    rw [← hq]
    simpa using congrArg (fun x : ℤ => (x : WithTop ℤ)) hqval
  · have hy_nonneg : 0 ≤ vL D.y := le_of_not_gt hyneg
    have hpow_nonneg : 0 ≤ p • vL D.y := nsmul_nonneg hy_nonneg p
    have hsub_nonneg : 0 ≤ vL (D.y ^ p - D.y) := by
      have hmin := vL.map_sub (D.y ^ p) D.y
      have hpow_nonneg' : 0 ≤ vL (D.y ^ p) := by
        simpa [vL.map_pow] using hpow_nonneg
      exact le_trans (le_min hpow_nonneg' hy_nonneg) hmin
    rw [heqv] at hsub_nonneg
    have hneg : -(m * p : ℤ) < 0 := by
      have hmp : 0 < m * p := Nat.mul_pos hmpos (Fact.out : Nat.Prime p).pos
      have hmpZ : 0 < (m * p : ℤ) := by exact_mod_cast hmp
      exact neg_lt_zero.mpr hmpZ
    have hbad : (0 : ℤ) ≤ -(m * p : ℤ) := by
      exact_mod_cast hsub_nonneg
    exact (not_le_of_gt hneg hbad).elim

theorem chapter03_artin_schreier_extension_is_cyclic_galois
    {k L : Type*} [Field k] [Field L]
    [Algebra (LaurentSeries k) L]
    [FiniteDimensional (LaurentSeries k) L]
    (p m : ℕ) [Fact p.Prime] [CharP k p]
    (D : Chapter03ArtinSchreierExtensionData (k := k) (L := L) p m)
    (hno_root :
      ∀ z : LaurentSeries k,
        z ^ p - z ≠
          (LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.laurentSeriesUniformizer k) ^
            (-(m : ℤ))) :
    IsGalois (LaurentSeries k) L ∧
      Module.finrank (LaurentSeries k) L = p ∧
      ∃ γ : L ≃ₐ[LaurentSeries k] L,
        orderOf γ = p ∧
          (∀ σ : L ≃ₐ[LaurentSeries k] L,
            ∃ n : ℤ, γ ^ n = σ) ∧
      (∀ c : L, c ^ p - c = 0 →
            ∃ σ : L ≃ₐ[LaurentSeries k] L, σ D.y = D.y + c) := by
  classical
  let : CharP (LaurentSeries k) p :=
    charP_of_injective_ringHom
      (f := (HahnSeries.C : k →+* LaurentSeries k))
      HahnSeries.C_injective p
  let : CharP L p :=
    charP_of_injective_algebraMap (algebraMap (LaurentSeries k) L).injective p
  let t : LaurentSeries k :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.laurentSeriesUniformizer k
  let a : LaurentSeries k := t ^ (-(m : ℤ))
  let f : (LaurentSeries k)[X] := chapter03ArtinSchreierPolynomial p a
  have hEq : D.y ^ p - D.y = algebraMap (LaurentSeries k) L a := by
    simpa [a, t, chapter03ArtinSchreierEquation] using D.equation
  have hroot : Polynomial.aeval D.y f = 0 := by
    rw [Polynomial.aeval_def]
    change (X ^ p - X - C a).eval₂ (algebraMap (LaurentSeries k) L) D.y = 0
    rw [eval₂_sub, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C]
    change D.y ^ p - D.y - algebraMap (LaurentSeries k) L a = 0
    rw [hEq]
    exact sub_self _
  have hf : Irreducible f := by
    dsimp [f]
    apply chapter03_artin_schreier_irreducible_of_no_root p a
    intro z hz
    apply hno_root z
    simpa [a, t] using hz
  have hmin_dvd : minpoly (LaurentSeries k) D.y ∣ f :=
    minpoly.dvd (LaurentSeries k) D.y hroot
  have hmonic : f.Monic := by
    dsimp [f, chapter03ArtinSchreierPolynomial]
    have hdeg : degree (-(X + C a) : (LaurentSeries k)[X]) < p := by
      rw [degree_neg, degree_X_add_C]
      exact_mod_cast (Fact.out : Nat.Prime p).one_lt
    have h :=
      monic_X_pow_add (p := (-(X + C a) : (LaurentSeries k)[X])) (n := p) hdeg
    have hpoly : X ^ p + -(X + C a) = X ^ p - X - C a := by ring
    rw [← hpoly]
    exact h
  have hnat : f.natDegree = p := by
    dsimp [f, chapter03ArtinSchreierPolynomial]
    have hdeg : degree (-(X + C a) : (LaurentSeries k)[X]) < p := by
      rw [degree_neg, degree_X_add_C]
      exact_mod_cast (Fact.out : Nat.Prime p).one_lt
    have hdeg' : degree (-(X + C a) : (LaurentSeries k)[X]) <
        (X ^ p : (LaurentSeries k)[X]).degree := by
      simpa [degree_X_pow] using hdeg
    rw [show X ^ p - X - C a = X ^ p + -(X + C a) by ring]
    rw [natDegree_add_eq_left_of_degree_lt hdeg', natDegree_X_pow]
  have hmin_eq : minpoly (LaurentSeries k) D.y = f := by
    exact eq_of_monic_of_associated
      (minpoly.monic (Algebra.IsIntegral.isIntegral D.y)) hmonic
      ((minpoly.irreducible (Algebra.IsIntegral.isIntegral D.y)).associated_of_dvd
        hf hmin_dvd)
  have hgen' : IntermediateField.adjoin (LaurentSeries k) ({D.y} : Set L) =
      (⊤ : IntermediateField (LaurentSeries k) L) :=
    IntermediateField.adjoin_eq_top_of_algebra (LaurentSeries k) ({D.y} : Set L)
      D.generated
  have hfinrank : Module.finrank (LaurentSeries k) L = p := by
    have hadjfin :
        Module.finrank (LaurentSeries k)
            (IntermediateField.adjoin (LaurentSeries k) ({D.y} : Set L)) =
          (minpoly (LaurentSeries k) D.y).natDegree :=
      IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral D.y)
    rw [hgen'] at hadjfin
    have htop : Module.finrank (LaurentSeries k)
        (⊤ : IntermediateField (LaurentSeries k) L) =
        Module.finrank (LaurentSeries k) L :=
      IntermediateField.finrank_top'
    calc
      Module.finrank (LaurentSeries k) L =
          Module.finrank (LaurentSeries k)
            (⊤ : IntermediateField (LaurentSeries k) L) := htop.symm
      _ = (minpoly (LaurentSeries k) D.y).natDegree := hadjfin
      _ = f.natDegree := by rw [hmin_eq]
      _ = p := hnat
  let : Algebra (ZMod p) L := ZMod.algebra L p
  have hsplit0 : (X ^ p - X : L[X]).Splits := by
    have hsplitZ :
        ((X ^ p - X : (ZMod p)[X]).map (algebraMap (ZMod p) (ZMod p))).Splits := by
      simpa using (GaloisField.splits_zmod_X_pow_sub_X (p := p))
    have h :=
      hsplitZ.of_algHom (Algebra.ofId (ZMod p) L)
    simpa only [Polynomial.map_sub, Polynomial.map_pow, map_X] using h
  have hEqPoly : f.map (algebraMap (LaurentSeries k) L) =
      (X ^ p - X : L[X]).comp (X - C D.y) := by
    dsimp [f, chapter03ArtinSchreierPolynomial]
    simp [Polynomial.comp, sub_pow_char]
    rw [← hEq, map_sub, ← C.map_pow]
    ring
  have hsplit : (f.map (algebraMap (LaurentSeries k) L)).Splits := by
    rw [hEqPoly]
    exact hsplit0.comp_X_sub_C D.y
  have hyroot : D.y ∈ f.rootSet L := by
    rw [mem_rootSet_of_ne hf.ne_zero]
    exact hroot
  have hadjroot : IntermediateField.adjoin (LaurentSeries k) (f.rootSet L) = ⊤ := by
    apply top_unique
    have hmono := IntermediateField.adjoin.mono (LaurentSeries k) ({D.y} : Set L)
      (f.rootSet L) (Set.singleton_subset_iff.mpr hyroot)
    rw [hgen'] at hmono
    exact hmono
  have hsplitfield : f.IsSplittingField (LaurentSeries k) L :=
    (isSplittingField_iff_intermediateField).2 ⟨hsplit, hadjroot⟩
  let : f.IsSplittingField (LaurentSeries k) L := hsplitfield
  have hderiv : f.derivative = -1 := by
    dsimp [f]
    exact chapter03_artin_schreier_derivative p a
  have hsep : f.Separable := by
    rw [Polynomial.separable_iff_derivative_ne_zero hf, hderiv]
    exact neg_ne_zero.mpr one_ne_zero
  let : IsGalois (LaurentSeries k) L :=
    IsGalois.of_separable_splitting_field hsep
  have hcard : Nat.card (L ≃ₐ[LaurentSeries k] L) = p := by
    rw [IsGalois.card_aut_eq_finrank]
    exact hfinrank
  have hcyc : IsCyclic (L ≃ₐ[LaurentSeries k] L) :=
    isCyclic_of_prime_card hcard
  obtain ⟨γ, hγgen⟩ := hcyc.exists_generator
  have hγorder : orderOf γ = p := by
    calc
      orderOf γ = Nat.card (L ≃ₐ[LaurentSeries k] L) :=
        orderOf_eq_card_of_forall_mem_zpowers hγgen
      _ = p := hcard
  refine ⟨inferInstance, hfinrank, γ, hγorder, ?_, ?_⟩
  · intro σ
    exact Subgroup.mem_zpowers_iff.mp (hγgen σ)
  · intro c hc
    let z : L := D.y + c
    have hzEq : z ^ p - z = algebraMap (LaurentSeries k) L a := by
      dsimp [z]
      rw [add_pow_char]
      calc
        D.y ^ p + c ^ p - (D.y + c) =
            (D.y ^ p - D.y) + (c ^ p - c) := by ring
        _ = algebraMap (LaurentSeries k) L a := by rw [hEq, hc, add_zero]
    have hzroot : Polynomial.aeval z f = 0 := by
      rw [Polynomial.aeval_def]
      change (X ^ p - X - C a).eval₂ (algebraMap (LaurentSeries k) L) z = 0
      rw [eval₂_sub, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C]
      change z ^ p - z - algebraMap (LaurentSeries k) L a = 0
      rw [hzEq]
      exact sub_self _
    have hzmin : Polynomial.aeval z (minpoly (LaurentSeries k) D.y) = 0 := by
      rw [hmin_eq]
      exact hzroot
    obtain ⟨σ₀, hσ₀⟩ :=
      IntermediateField.exists_algHom_of_splits_of_aeval
        (fun x : L =>
          ⟨Algebra.IsIntegral.isIntegral x, IsGalois.splits (LaurentSeries k) x⟩) hzmin
    let σ : L ≃ₐ[LaurentSeries k] L :=
      AlgEquiv.ofBijective σ₀ (σ₀.normal_bijective (LaurentSeries k) L L)
    refine ⟨σ, ?_⟩
    simpa [σ, z] using hσ₀

/- The chosen uniformizer `t^a y^b` in the source calculation. -/
def chapter03ArtinSchreierUniformizer
    {k L : Type*} [Field k] [Field L]
    [Algebra (LaurentSeries k) L]
    (y : L) (a : ℤ) (b : ℕ) : L :=
  algebraMap (LaurentSeries k) L
    ((LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.laurentSeriesUniformizer k) ^ a) * y ^ b

theorem chapter03_artin_schreier_bezout_indices
    (p m : ℕ) [Fact p.Prime] (hm : Nat.Coprime m p) :
    ∃ a : ℤ, ∃ b : ℕ,
      1 ≤ b ∧ b < p ∧ a * p - b * m = 1 := by
  have hp : 1 < p := (Fact.out : Nat.Prime p).one_lt
  obtain ⟨b₀, hb₀p, hmod⟩ :=
    Nat.exists_mul_mod_eq_one_of_coprime (k := p) (n := m) hm hp
  have hb₀pos : 0 < b₀ := by
    by_contra hb₀
    have : b₀ = 0 := Nat.eq_zero_of_not_pos hb₀
    simp [this] at hmod
  have hdecomp : m * b₀ = 1 + p * (m * b₀ / p) := by
    have h := Nat.mod_add_div (m * b₀) p
    rw [hmod] at h
    omega
  refine ⟨(m : ℤ) - (m * b₀ / p : ℕ), p - b₀, ?_, ?_, ?_⟩
  · omega
  · omega
  · rw [Nat.cast_sub (le_of_lt hb₀p)]
    have hdecomp' : (m : ℤ) * (b₀ : ℤ) =
        1 + (p : ℤ) * ((m * b₀ / p : ℕ) : ℤ) := by
      exact_mod_cast hdecomp
    linear_combination hdecomp'

theorem chapter03_artin_schreier_chosen_uniformizer_has_value_one
    {k L : Type*} [Field k] [Field L]
    [Algebra (LaurentSeries k) L]
    (p m : ℕ) [Fact p.Prime] [CharP k p]
    (vL : AddValuation L (WithTop ℤ)) (y : L) (a : ℤ) (b : ℕ)
    (hvalue_t :
      vL (algebraMap (LaurentSeries k) L
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.laurentSeriesUniformizer k)) = p)
    (hvalue_y : vL y = -m)
    (hindices : a * p - b * m = 1) :
    vL (chapter03ArtinSchreierUniformizer (k := k) (L := L) y a b) = 1 := by
  unfold chapter03ArtinSchreierUniformizer
  rw [vL.map_mul, map_zpow₀, vL.map_pow]
  have hpow : ∀ (x : L) (n : ℤ), vL (x ^ n) = n • vL x := by
    intro x n
    cases n with
    | ofNat n => simp [zpow_natCast, vL.map_pow]
    | negSucc n =>
        rw [zpow_negSucc, vL.map_inv, vL.map_pow]
        simp
  rw [hpow, hvalue_t, hvalue_y]
  have hscalarInt (n x : ℤ) : n • (x : WithTop ℤ) = (n * x : ℤ) := by
    simpa [zsmul_eq_mul] using
      ((WithTop.addHom : ℤ →+ WithTop ℤ).map_zsmul n x).symm
  have hscalarNat (n : ℕ) (x : ℤ) : n • (x : WithTop ℤ) = (n * x : ℤ) := by
    simpa [nsmul_eq_mul] using (WithTop.coe_nsmul x n).symm
  have hscalarIntNat (n : ℤ) (q : ℕ) :
      n • (q : WithTop ℤ) = (n * (q : ℤ) : ℤ) := by
    simpa using hscalarInt n (q : ℤ)
  have hscalarNatNeg :
      b • -(m : WithTop ℤ) = (b * (-(m : ℤ)) : ℤ) := by
    simpa [smul_neg] using hscalarNat b (-(m : ℤ))
  rw [hscalarIntNat a p, hscalarNatNeg]
  norm_cast
  calc
    a * (p : ℤ) + (b : ℤ) * -(m : ℤ) = a * p - b * m := by ring
    _ = 1 := hindices

private theorem chapter03_artin_schreier_first_binomial_term_has_value_m_aux
    {L : Type*} [Field L]
    (p m : ℕ) [Fact p.Prime] [CharP L p]
    (vL : AddValuation L (WithTop ℤ)) (y c : L) (b : ℕ)
    (hm : 0 < m) (hvalue_y : vL y = -m) (hvalue_c : vL c = 0)
    (hb : 1 ≤ b) (hbp : b < p) (hc : c ^ p - c = 0) :
    vL ((1 + c / y) ^ b - 1) = m := by
  let : Algebra (ZMod p) L := ZMod.algebra _ _
  have hy : y ≠ 0 := by
    intro hy
    have htop : (-(m : ℤ) : WithTop ℤ) ≠ ⊤ := WithTop.coe_ne_top
    exact htop (by simpa [hy] using hvalue_y.symm)
  have hc0 : c ≠ 0 := by
    intro hc0
    have htop : (0 : WithTop ℤ) ≠ ⊤ := WithTop.coe_ne_top
    exact htop (by simpa [hc0] using hvalue_c.symm)
  have hx : c / y ≠ 0 := div_ne_zero hc0 hy
  have hxval : vL (c / y) = m := by
    rw [vL.map_div, hvalue_c, hvalue_y]
    simp
  have hb0 : (b : L) ≠ 0 := by
    intro hb0
    have hdiv : p ∣ b := (CharP.cast_eq_zero_iff L p b).mp hb0
    have hp_le : p ≤ b := Nat.le_of_dvd (by omega) hdiv
    exact (Nat.not_lt_of_ge hp_le) hbp
  have hbval : vL (b : L) = 0 := by
    have hbz : (b : ZMod p) ≠ 0 := by
      intro hbz
      have hdiv : p ∣ b := (CharP.cast_eq_zero_iff (ZMod p) p b).mp hbz
      have hp_le : p ≤ b := Nat.le_of_dvd (by omega) hdiv
      exact (Nat.not_lt_of_ge hp_le) hbp
    have hmult :=
      FiniteField.valuation_algebraMap_eq_one (vL.toValuation)
        (b : ZMod p) hbz
    simpa [AddValuation.toValuation_apply] using hmult
  have hm' : (0 : WithTop ℤ) < m := by exact_mod_cast hm
  have hxpos : (0 : WithTop ℤ) < vL (c / y) := by
    simpa [hxval] using hm'
  have hA : vL (1 + c / y) = 0 := by
    calc
      vL (1 + c / y) = vL 1 := by
        apply vL.map_add_eq_of_lt_left
        simpa [vL.map_one] using hxpos
      _ = 0 := vL.map_one
  let u : ℕ → L := fun n =>
    ((1 + c / y) ^ n - 1) / (c / y)
  have hu_succ (n : ℕ) : u (n + 1) = u n * (1 + c / y) + 1 := by
    dsimp [u]
    rw [pow_succ]
    field_simp [hx]
    ring
  have hnat_nonneg : ∀ n : ℕ, 0 ≤ vL (n : L) := by
    intro n
    by_cases hn : (n : L) = 0
    · simp [hn]
    · have hnz : (n : ZMod p) ≠ 0 := by
        intro hnz
        have hdiv : p ∣ n := (CharP.cast_eq_zero_iff (ZMod p) p n).mp hnz
        have hzero : (n : L) = 0 :=
          (CharP.cast_eq_zero_iff L p n).mpr hdiv
        exact hn hzero
      have hmult :=
        FiniteField.valuation_algebraMap_eq_one (vL.toValuation)
          (n : ZMod p) hnz
      have hnval : vL (n : L) = 0 := by
        simpa [AddValuation.toValuation_apply] using hmult
      rw [hnval]
  have herror : ∀ n : ℕ, 0 < vL (u n - (n : L)) := by
    intro n
    induction n with
    | zero =>
        dsimp [u]
        simp
    | succ n ih =>
        have hrec :
            u (n + 1) - ((n + 1 : ℕ) : L) =
              (u n - (n : L)) * (1 + c / y) + (n : L) * (c / y) := by
          rw [hu_succ]
          rw [Nat.cast_add, Nat.cast_one]
          ring
        rw [hrec]
        apply vL.map_lt_add
        · rw [vL.map_mul, hA, add_zero]
          exact ih
        · rw [vL.map_mul]
          exact Right.add_pos_of_nonneg_of_pos (hnat_nonneg n) hxpos
  have hU : vL (u b) = 0 := by
    have hsum : u b = (u b - (b : L)) + (b : L) := by ring
    rw [hsum]
    calc
      vL (u b - (b : L) + (b : L)) = vL (b : L) := by
        apply vL.map_add_eq_of_lt_right
        rw [hbval]
        exact herror b
      _ = 0 := hbval
  have hfactor :
      (1 + c / y) ^ b - 1 = (c / y) * u b := by
    calc
      (1 + c / y) ^ b - 1 =
          (c / y) * u b + (c ^ p - c) * 0 := by
        dsimp [u]
        field_simp [hx]
        ring
      _ = (c / y) * u b := by rw [hc]; simp
  rw [hfactor, vL.map_mul, hxval, hU]
  simp

theorem chapter03_artin_schreier_displacement_calculation
    {k L : Type*} [Field k] [Field L]
    [Algebra (LaurentSeries k) L]
    (p m : ℕ) [Fact p.Prime] [CharP k p]
    (vL : AddValuation L (WithTop ℤ)) (y : L) (a : ℤ) (b : ℕ)
    (σ : L ≃ₐ[LaurentSeries k] L) (c : L)
    (hvalue_t :
      vL (algebraMap (LaurentSeries k) L
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.laurentSeriesUniformizer k)) = p)
    (hvalue_y : vL y = -m)
    (hvalue_c : vL c = 0)
    (hindices : a * p - b * m = 1)
    (hb : 1 ≤ b) (hbp : b < p)
    (hc : c ^ p - c = 0) (hσy : σ y = y + c) :
    vL (σ (chapter03ArtinSchreierUniformizer (k := k) (L := L) y a b) -
      chapter03ArtinSchreierUniformizer (k := k) (L := L) y a b) = m + 1 := by
  let : CharP (LaurentSeries k) p :=
    charP_of_injective_ringHom
      (f := (HahnSeries.C : k →+* LaurentSeries k))
      HahnSeries.C_injective p
  let : CharP L p :=
    charP_of_injective_algebraMap (algebraMap (LaurentSeries k) L).injective p
  have hmpos : 0 < m := by
    by_contra hm'
    have hmzero : m = 0 := Nat.eq_zero_of_not_pos hm'
    subst m
    have hdivZ : (p : ℤ) ∣ (1 : ℤ) := by
      refine ⟨a, ?_⟩
      simpa [mul_comm] using hindices.symm
    have hdiv : p ∣ 1 := Int.natCast_dvd_natCast.mp hdivZ
    have hpone : p = 1 := Nat.dvd_one.mp hdiv
    exact (Fact.out : Nat.Prime p).ne_one hpone
  have hy : y ≠ 0 := by
    intro hy
    have htop : (-(m : ℤ) : WithTop ℤ) ≠ ⊤ := WithTop.coe_ne_top
    exact htop (by simpa [hy] using hvalue_y.symm)
  have hbin :=
    chapter03_artin_schreier_first_binomial_term_has_value_m_aux
      p m vL y c b hmpos hvalue_y hvalue_c hb hbp hc
  have hUvalue :=
    chapter03_artin_schreier_chosen_uniformizer_has_value_one
      p m vL y a b hvalue_t hvalue_y hindices
  have hfactor :
      σ (chapter03ArtinSchreierUniformizer (k := k) (L := L) y a b) -
          chapter03ArtinSchreierUniformizer (k := k) (L := L) y a b =
        chapter03ArtinSchreierUniformizer (k := k) (L := L) y a b *
          ((1 + c / y) ^ b - 1) := by
    unfold chapter03ArtinSchreierUniformizer
    simp only [map_mul, map_pow, map_zpow₀, AlgEquiv.commutes]
    rw [hσy]
    have hratio : 1 + c / y = (y + c) / y := by
      field_simp [hy]
    rw [hratio, div_pow]
    field_simp [hy]
  rw [hfactor, vL.map_mul, hUvalue, hbin]
  simp [add_comm]

theorem chapter03_artin_schreier_uniformizer_ratio
    {k L : Type*} [Field k] [Field L]
    [Algebra (LaurentSeries k) L]
    (p m : ℕ) [Fact p.Prime] [CharP k p]
    (y : L) (a : ℤ) (b : ℕ) (σ : L ≃ₐ[LaurentSeries k] L) (c : L)
    (hy : y ≠ 0) (hσy : σ y = y + c) :
    σ (chapter03ArtinSchreierUniformizer (k := k) (L := L) y a b) /
        chapter03ArtinSchreierUniformizer (k := k) (L := L) y a b =
      (1 + c / y) ^ b := by
  unfold chapter03ArtinSchreierUniformizer
  have ht :
      algebraMap (LaurentSeries k) L
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.laurentSeriesUniformizer k) ≠ 0 := by
    exact (map_ne_zero_iff _ (algebraMap (LaurentSeries k) L).injective).2
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.laurentSeriesUniformizer_isUniformizer k).1
  have ht0 :
      (algebraMap (LaurentSeries k) L
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.laurentSeriesUniformizer k)) ^ a ≠ 0 :=
    zpow_ne_zero _ ht
  simp only [map_mul, map_pow, map_zpow₀, AlgEquiv.commutes]
  rw [hσy]
  have hratio : 1 + c / y = (y + c) / y := by
    field_simp [hy]
  rw [hratio, div_pow]
  calc
    _ = (y + c) ^ b / y ^ b + ((m : L) - m) := by
      field_simp [hy, ht0]
      ring
    _ = (y + c) ^ b / y ^ b := by simp

theorem chapter03_artin_schreier_first_binomial_term_has_value_m
    {k L : Type*} [Field k] [Field L]
    [Algebra (LaurentSeries k) L]
    (p m : ℕ) [Fact p.Prime] [CharP k p]
    (vL : AddValuation L (WithTop ℤ)) (y c : L) (b : ℕ)
    (hm : 0 < m) (hvalue_y : vL y = -m) (hvalue_c : vL c = 0)
    (hb : 1 ≤ b) (hbp : b < p) (hc : c ^ p - c = 0) :
    vL ((1 + c / y) ^ b - 1) = m := by
  let : CharP (LaurentSeries k) p :=
    charP_of_injective_ringHom
      (f := (HahnSeries.C : k →+* LaurentSeries k))
      HahnSeries.C_injective p
  let : CharP L p :=
    charP_of_injective_algebraMap (algebraMap (LaurentSeries k) L).injective p
  exact chapter03_artin_schreier_first_binomial_term_has_value_m_aux
    p m vL y c b hm hvalue_y hvalue_c hb hbp hc

theorem chapter03_artin_schreier_lower_groups
    {G : Type*} [Group G] [Finite G]
    (F : Chapter03LowerDisplacementFiltration G) (m : ℕ)
    (hdisp : ∀ {σ : G}, σ ≠ 1 → F.displacement σ = m + 1)
    (hnontrivial : ∃ σ : G, σ ≠ 1) :
    F.lower (-1) = ⊤ ∧
      (∀ n : ℕ, n ≤ m → F.lower (n : ℤ) = ⊤) ∧
      (∀ n : ℕ, m + 1 ≤ n → F.lower (n : ℤ) = ⊥) ∧
      chapter03LowerBreak F m := by
  have hprofile :=
    chapter03_one_break_profile_of_constant_displacement F m hdisp
  have hbreak := chapter03_one_break_is_unique F m hdisp hnontrivial
  exact ⟨F.lower_neg_one, hprofile.1, hprofile.2, hbreak⟩

/- Changing an Artin--Schreier coordinate changes the right side by an
additive coboundary. -/
theorem chapter03_artin_schreier_change_of_variable
    {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (y z a : K) (hroot : y ^ p - y = a) :
    (y - z) ^ p - (y - z) = a - (z ^ p - z) := by
  exact chapter03_artin_schreier_translation p a y z hroot

theorem chapter03_artin_schreier_divisible_exponent_is_a_coboundary
    {K : Type*} [Field K] (p r : ℕ) [CharP K p] (t : K) :
    t ^ (-(p * r : ℤ)) =
      (t ^ (-(r : ℤ))) ^ p := by
  rw [← zpow_natCast, ← zpow_mul]
  congr 1
  ring

/- SOURCE_NOTE (3.3): The restriction `p ∤ m` is a normal-form choice, not a
   restriction on all Artin--Schreier classes.  The preceding change of
   variable and coboundary identity records the precise coordinate operation
   that removes exponents divisible by `p` when the required coefficient is a
   `p`th power. -/

end
end LastLib.Book03RamificationTheory.Chapter03
