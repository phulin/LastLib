import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.LocalRing.Etale
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07.Section01IsolatingResidueGrowth

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07

open Set
open Polynomial

noncomputable section

/-! # Book 2, Chapter 7, §7.2: equivalent characterizations -/

/-- The extension of a base ideal to the integral-extension ring. -/
def Chapter07ExtendedIdeal
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (m : Ideal A) : Ideal B :=
  Ideal.map (algebraMap A B) m

/-- The ideal-theoretic form of `m_L = m_K B`. -/
def Chapter07MaximalIdealExtension
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (m : Ideal A) (P : Ideal B) : Prop :=
  P = Chapter07ExtendedIdeal A B m

/-- Finite étale is written with the standard Mathlib predicates: finite as a
module and étale as an algebra. -/
def Chapter07FiniteEtaleExtension
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] : Prop :=
  Module.Finite A B ∧ Algebra.Etale A B

/--
The fourth criterion in Theorem 7.1.  The ring hom `res` records the chosen
reduction of coefficients.  Both minimal-polynomial equalities are retained,
so a later proof cannot accidentally replace “the reduction of `g`” by an
arbitrary polynomial with the same degree.
-/
structure Chapter07MonogenicResiduePresentation
    (A B K L k l : Type*) [CommRing A] [CommRing B]
    [Field K] [Field L] [Field k] [Field l]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L]
    [Algebra A L] [Algebra k l]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [FiniteDimensional K L] [FiniteDimensional k l] [Module.Finite A B]
    (P : Ideal B) (res : A →+* k) where
  theta : B
  residueTheta : l
  residueMap : B →+* l
  residue_theta_eq : residueMap theta = residueTheta
  residueMap_compatible :
    residueMap.comp (algebraMap A B) =
      (algebraMap k l).comp res
  residueMap_surjective : Function.Surjective residueMap
  residueMap_kernel : RingHom.ker residueMap = P
  polynomial : A[X]
  polynomial_monic : polynomial.Monic
  generic_minpoly :
    minpoly K (algebraMap B L theta) = polynomial.map (algebraMap A K)
  residue_minpoly :
    minpoly k residueTheta = polynomial.map res
  residue_polynomial_separable : (polynomial.map res).Separable
  unit_derivative :
    IsUnit (eval₂ (algebraMap A B) theta polynomial.derivative)
  residue_generates : Algebra.adjoin k ({residueTheta} : Set l) = ⊤
  ring_generates : Algebra.adjoin A ({theta} : Set B) = ⊤

/-! Theorem 7.1.  The hypotheses identify the abstract profile from §7.1
with one finite normalization branch.  Completeness/henselianity is expressed
by `HenselianLocalRing A`, and both residue maps are explicit. -/

/-- The five field/ring/residue criteria for an unramified extension. -/
theorem chapter07_unramified_criteria
    {A B K L k l : Type*} [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [Field K] [Field L] [Field k] [Field l]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L]
    [Algebra A L] [Algebra k l]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [FiniteDimensional k l]
    [IsIntegralClosure B A L] [HenselianLocalRing A]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Module.Finite A B]
    (E : Chapter07FiniteLocalExtensionData K L k l)
    (m : Ideal A) (P : Ideal B) (res : A →+* k)
    (hm : m = IsLocalRing.maximalIdeal A)
    (hP : P = IsLocalRing.maximalIdeal B)
    (hres_surjective : Function.Surjective res)
    (hres_kernel : RingHom.ker res = m)
    (resB : B →+* l)
    (hresB_surjective : Function.Surjective resB)
    (hresB_kernel : RingHom.ker resB = P)
    (hresB_compatible :
      resB.comp (algebraMap A B) = (algebraMap k l).comp res)
    (hE : E.ramificationIndex =
      P.ramificationIdx A)
    (_hf : E.residueDegree =
      P.inertiaDeg A) :
    (Chapter07UnramifiedExtension E ↔
      (Chapter07MaximalIdealExtension A B m P ∧
        Chapter07ResidueExtensionIsSeparable k l)) ∧
      (Chapter07UnramifiedExtension E ↔
        Nonempty (Chapter07MonogenicResiduePresentation A B K L k l P res)) ∧
      (Chapter07UnramifiedExtension E ↔
        Chapter07FiniteEtaleExtension A B) := by
  let : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L
  let : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
  let : Module.IsTorsionFree A B :=
    (Module.isTorsionFree_iff_faithfulSMul).mpr inferInstance
  have hformula :
      Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
        (IsLocalRing.maximalIdeal B) ^
          (IsLocalRing.maximalIdeal B).ramificationIdx A := by
    classical
    let m₀ : Ideal A := IsLocalRing.maximalIdeal A
    let P₀ : Ideal B := IsLocalRing.maximalIdeal B
    have hm₀ : m₀ ≠ (⊥ : Ideal A) := by
      exact IsDiscreteValuationRing.not_a_field A
    have hmap_le : Ideal.map (algebraMap A B) m₀ ≤ P₀ := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      simpa [P₀, IsLocalRing.mem_maximalIdeal] using
        map_nonunit (algebraMap A B) a (by simpa [m₀] using ha)
    have hmap₀ : Ideal.map (algebraMap A B) m₀ ≠ (⊥ : Ideal B) :=
      Ideal.map_ne_bot_of_ne_bot hm₀
    obtain ⟨n, hPn⟩ :=
      exists_maximalIdeal_pow_eq_of_principal B
        (IsPrincipalIdealRing.principal P₀)
        (Ideal.map (algebraMap A B) m₀) hmap₀
    have hram : P₀.ramificationIdx A = n := by
      let _ : IsDiscreteValuationRing (Localization.AtPrime P₀) :=
        IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B
          (IsDiscreteValuationRing.not_a_field B) (Localization.AtPrime P₀)
      rw [Ideal.ramificationIdx_eq m₀ P₀]
      change (Module.length (Localization.AtPrime P₀)
        (Localization.AtPrime P₀ ⧸
          Ideal.map (algebraMap A (Localization.AtPrime P₀)) m₀)).toNat = n
      have hPn' := congrArg
        (Ideal.map (algebraMap B (Localization.AtPrime P₀))) hPn
      rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq A B
        (Localization.AtPrime P₀), Ideal.map_pow,
        Localization.AtPrime.map_eq_maximalIdeal] at hPn'
      rw [hPn', IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
      rfl
    simpa [m₀, P₀, hram] using hPn
  have hP0 : IsLocalRing.maximalIdeal B ≠ (⊥ : Ideal B) := by
    exact IsDiscreteValuationRing.not_a_field B
  have hP1 : IsLocalRing.maximalIdeal B ≠ (1 : Ideal B) := by
    simpa using (IsLocalRing.maximalIdeal.isMaximal B).ne_top
  have hram_iff :
      E.ramificationIndex = 1 ↔
        Chapter07MaximalIdealExtension A B m P := by
    constructor
    · intro he
      unfold Chapter07MaximalIdealExtension Chapter07ExtendedIdeal
      rw [hm, hformula, ← hP, ← hE, he, pow_one]
    · intro hmap
      have hpow : (IsLocalRing.maximalIdeal B) ^
          (IsLocalRing.maximalIdeal B).ramificationIdx A =
          IsLocalRing.maximalIdeal B := by
        rw [← hformula, ← hm, ← hP]
        exact hmap.symm
      have hidx : (IsLocalRing.maximalIdeal B).ramificationIdx A = 1 := by
        apply (IsMulTorsionFree.pow_right_inj₀ hP1 hP0).mp
        simpa using hpow
      have hidxP : P.ramificationIdx A = 1 := by
        simpa [hP] using hidx
      rw [hE]
      exact hidxP
  have hkerA : RingHom.ker res = IsLocalRing.maximalIdeal A :=
    hres_kernel.trans hm
  have hkerB : RingHom.ker resB = IsLocalRing.maximalIdeal B :=
    hresB_kernel.trans hP
  let eA : IsLocalRing.ResidueField A ≃+* k := by
    change (A ⧸ IsLocalRing.maximalIdeal A) ≃+* k
    exact
      (Ideal.quotEquivOfEq hkerA.symm).trans
        (RingHom.quotientKerEquivOfSurjective hres_surjective)
  let eB : IsLocalRing.ResidueField B ≃+* l := by
    change (B ⧸ IsLocalRing.maximalIdeal B) ≃+* l
    exact
      (Ideal.quotEquivOfEq hkerB.symm).trans
        (RingHom.quotientKerEquivOfSurjective hresB_surjective)
  have heA_apply (a : A) :
      eA (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a) = res a := by
    change
      (RingHom.quotientKerEquivOfSurjective hres_surjective)
          (Ideal.quotEquivOfEq hkerA.symm
            (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a)) = res a
    rw [Ideal.quotEquivOfEq_mk]
    exact RingHom.quotientKerEquivOfSurjective_apply_mk hres_surjective a
  have heB_apply (b : B) :
      eB (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B) b) = resB b := by
    change
      (RingHom.quotientKerEquivOfSurjective hresB_surjective)
          (Ideal.quotEquivOfEq hkerB.symm
            (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B) b)) = resB b
    rw [Ideal.quotEquivOfEq_mk]
    exact RingHom.quotientKerEquivOfSurjective_apply_mk hresB_surjective b
  have heq :
      (algebraMap k l).comp eA.toRingHom =
        eB.toRingHom.comp
          (algebraMap (IsLocalRing.ResidueField A)
            (IsLocalRing.ResidueField B)) := by
    apply RingHom.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change algebraMap k l
        (eA (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a)) =
      eB (algebraMap (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField B)
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a))
    rw [heA_apply]
    change algebraMap k l (res a) =
      eB (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B)
        (algebraMap A B a))
    rw [heB_apply]
    exact DFunLike.congr_fun hresB_compatible a |>.symm
  have hsepCanon
      (hsep : Chapter07ResidueExtensionIsSeparable k l) :
      Algebra.IsSeparable (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField B) := by
    let : Algebra.IsSeparable k l := ⟨hsep⟩
    exact (Algebra.IsSeparable.iff_of_equiv_equiv eA eB heq).mpr inferInstance
  have hflat : Module.Flat A B := inferInstance
  have hfp : Module.FinitePresentation A B :=
    Module.finitePresentation_of_finite A B
  let : Module.Flat A B := hflat
  let : Module.FinitePresentation A B := hfp
  let : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_finitePresentation A B
  have hformal :
      Algebra.FormallyUnramified A B ↔
        Algebra.IsSeparable (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField B) ∧
        (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
          IsLocalRing.maximalIdeal B :=
    Algebra.FormallyUnramified.iff_map_maximalIdeal_eq
  have hetale :
      Algebra.Etale A B ↔
        Algebra.FormallyUnramified A B := by
    constructor
    · intro h
      have hhom : (algebraMap A B).Etale :=
        RingHom.etale_algebraMap.mpr h
      exact (RingHom.formallyUnramified_algebraMap).mp hhom.formallyUnramified
    · intro h
      have hflat_hom : (algebraMap A B).Flat :=
        (RingHom.flat_algebraMap_iff).mpr hflat
      have hform_hom : (algebraMap A B).FormallyUnramified :=
        (RingHom.formallyUnramified_algebraMap).mpr h
      have hfp_hom : (algebraMap A B).FinitePresentation :=
        (RingHom.finitePresentation_algebraMap).mpr inferInstance
      have het_hom : (algebraMap A B).Etale :=
        (RingHom.Etale.iff_flat_and_formallyUnramified
          (f := algebraMap A B)).mpr
          ⟨hflat_hom, hform_hom, hfp_hom⟩
      exact (RingHom.etale_algebraMap).mp het_hom
  have hfirst :
      Chapter07UnramifiedExtension E ↔
        (Chapter07MaximalIdealExtension A B m P ∧
          Chapter07ResidueExtensionIsSeparable k l) := by
    unfold Chapter07UnramifiedExtension
    rw [hram_iff]
  have hthird :
      Chapter07UnramifiedExtension E ↔
        Chapter07FiniteEtaleExtension A B := by
    unfold Chapter07FiniteEtaleExtension
    constructor
    · intro hU
      refine ⟨inferInstance, ?_⟩
      have hmap : Chapter07MaximalIdealExtension A B m P :=
        hram_iff.mp hU.1
      have hmapCanon :
          (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
            IsLocalRing.maximalIdeal B := by
        unfold Chapter07MaximalIdealExtension Chapter07ExtendedIdeal at hmap
        rw [hm, hP] at hmap
        exact hmap.symm
      let : Algebra.IsSeparable (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField B) := hsepCanon hU.2
      let : Algebra.FormallyUnramified A B :=
        Algebra.FormallyUnramified.of_map_maximalIdeal hmapCanon
      exact hetale.mpr inferInstance
    · rintro ⟨_, hEtale⟩
      have hform : Algebra.FormallyUnramified A B := hetale.mp hEtale
      let : Algebra.FormallyUnramified A B := hform
      have hcanon := hformal.mp inferInstance
      have hsepClass : Algebra.IsSeparable k l := by
        exact (Algebra.IsSeparable.iff_of_equiv_equiv eA eB heq).mp hcanon.1
      have hsep : Chapter07ResidueExtensionIsSeparable k l := by
        let : Algebra.IsSeparable k l := hsepClass
        intro x
        exact Algebra.IsSeparable.isSeparable k x
      have hmap : Chapter07MaximalIdealExtension A B m P := by
        unfold Chapter07MaximalIdealExtension Chapter07ExtendedIdeal
        rw [hm, hP]
        exact hcanon.2.symm
      exact ⟨hram_iff.mpr hmap, hsep⟩
  have hforward (hU : Chapter07UnramifiedExtension E) :
      Nonempty (Chapter07MonogenicResiduePresentation A B K L k l P res) := by
    have hmap : Chapter07MaximalIdealExtension A B m P :=
      hram_iff.mp hU.1
    have hmapCanon :
        (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
          IsLocalRing.maximalIdeal B := by
      unfold Chapter07MaximalIdealExtension Chapter07ExtendedIdeal at hmap
      rw [hm, hP] at hmap
      exact hmap.symm
    let : Algebra.IsSeparable (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField B) := hsepCanon hU.2
    let : Algebra.FormallyUnramified A B :=
      Algebra.FormallyUnramified.of_map_maximalIdeal hmapCanon
    let : Algebra.Etale A B := hetale.mpr inferInstance
    obtain ⟨theta, htheta⟩ :=
      IsLocalRing.exists_adjoin_eq_top (R := A) (S := B)
    have hthetaInt : IsIntegral A theta :=
      IsIntegralClosure.isIntegral A L theta
    let p : A[X] := minpoly A theta
    have hgeneric :
        minpoly K (algebraMap B L theta) =
          p.map (algebraMap A K) := by
      exact minpoly.isIntegrallyClosed_eq_field_fractions K L hthetaInt
    have hcanon :
        (minpoly A theta).map (IsLocalRing.residue A) =
          minpoly (IsLocalRing.ResidueField A)
            (IsLocalRing.residue B theta) :=
      IsLocalRing.minpoly_map_residue htheta
    have hpoly_equiv :
        Polynomial.map eA
            (minpoly (IsLocalRing.ResidueField A)
              (IsLocalRing.residue B theta)) =
          minpoly k (eB (IsLocalRing.residue B theta)) := by
      exact minpoly.map_eq_of_equiv_equiv
        (R := IsLocalRing.ResidueField A) (A := k)
        (S := IsLocalRing.ResidueField B) (T := l)
        (f := eA) (g := eB) heq (IsLocalRing.residue B theta)
    have hresmin :
        minpoly k (resB theta) = p.map res := by
      rw [← heB_apply]
      change minpoly k (eB (IsLocalRing.residue B theta)) = p.map res
      rw [← hpoly_equiv, ← hcanon, Polynomial.map_map]
      congr 1
    have hresgen :
        Algebra.adjoin k ({resB theta} : Set l) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      obtain ⟨b, rfl⟩ := hresB_surjective x
      have hb : b ∈ Algebra.adjoin A ({theta} : Set B) := by
        rw [htheta]
        trivial
      induction hb using Algebra.adjoin_induction with
      | mem b hb =>
          rcases Set.mem_singleton_iff.mp hb with rfl
          exact Algebra.subset_adjoin (by simp)
      | algebraMap a =>
          rw [show resB (algebraMap A B a) = algebraMap k l (res a) by
            exact DFunLike.congr_fun hresB_compatible a]
          exact (Algebra.adjoin k _).algebraMap_mem _
      | add x y hx hy ihx ihy =>
          simpa only [map_add] using
            (Algebra.adjoin k _).add_mem (ihx trivial) (ihy trivial)
      | mul x y hx hy ihx ihy =>
          simpa only [map_mul] using
            (Algebra.adjoin k _).mul_mem (ihx trivial) (ihy trivial)
    have hunit :
        IsUnit (eval₂ (algebraMap A B) theta
          (minpoly A theta).derivative) := by
      simpa [aeval_def] using
        (IsLocalRing.isUnit_aeval_derivative_minpoly_of_adjoin_eq_top htheta)
    have hpolysep :
        ((minpoly A theta).map res).Separable := by
      rw [← hresmin]
      exact hU.2 (resB theta)
    refine ⟨⟨theta, resB theta, resB, rfl, hresB_compatible,
      hresB_surjective, hresB_kernel, p, ?_, hgeneric, hresmin, hpolysep,
      hunit, hresgen, htheta⟩⟩
    exact minpoly.monic hthetaInt
  have hfinrank_from_p (p : Chapter07MonogenicResiduePresentation A B K L k l P res) :
      Module.finrank A B = p.polynomial.natDegree := by
    have hpoly : p.polynomial = minpoly A p.theta := by
      have hthetaInt : IsIntegral A p.theta :=
        IsIntegralClosure.isIntegral A L p.theta
      have hgeneric :
          minpoly K (algebraMap B L p.theta) =
            (minpoly A p.theta).map (algebraMap A K) :=
        minpoly.isIntegrallyClosed_eq_field_fractions K L hthetaInt
      apply Polynomial.map_injective (algebraMap A K)
        (FaithfulSMul.algebraMap_injective A K)
      calc
        p.polynomial.map (algebraMap A K) =
            minpoly K (algebraMap B L p.theta) := p.generic_minpoly.symm
        _ = (minpoly A p.theta).map (algebraMap A K) := hgeneric
    let hroot : IsAdjoinRootMonic B (minpoly A p.theta) :=
      IsAdjoinRootMonic.mkOfAdjoinEqTop' p.ring_generates
    rw [hpoly]
    exact hroot.finrank
  have hresfinrank_from_p (p : Chapter07MonogenicResiduePresentation A B K L k l P res) :
      Module.finrank k l = p.polynomial.natDegree := by
    let hroot : IsAdjoinRootMonic l (minpoly k p.residueTheta) :=
      IsAdjoinRootMonic.mkOfAdjoinEqTop' <| by
        exact p.residue_generates
    rw [hroot.finrank, p.residue_minpoly]
    exact p.polynomial_monic.natDegree_map res
  have hsep_from_p (p : Chapter07MonogenicResiduePresentation A B K L k l P res) :
      Algebra.IsSeparable k l := by
    have hsepTheta : IsSeparable k p.residueTheta := by
      change (minpoly k p.residueTheta).Separable
      rw [p.residue_minpoly]
      exact p.residue_polynomial_separable
    have hsepS :
        Algebra.IsSeparable k (IntermediateField.adjoin k
          ({p.residueTheta} : Set l)) :=
      (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable k l).mpr hsepTheta
    have htop :
        IntermediateField.adjoin k ({p.residueTheta} : Set l) = ⊤ := by
      apply
        (IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic
          (IsAlgebraic.of_finite k p.residueTheta)).mpr
      exact p.residue_generates
    let e : IntermediateField.adjoin k ({p.residueTheta} : Set l) ≃ₐ[k] l :=
      (IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv
    exact
      (Algebra.IsSeparable.iff_of_equiv_equiv
        (RingEquiv.refl k) e.toRingEquiv (by ext; simp)).mp hsepS
  have hdegree_from_p (p : Chapter07MonogenicResiduePresentation A B K L k l P res) :
      Module.finrank K L = Module.finrank k l := by
    rw [IsFractionRing.finrank_eq A K B L,
      hfinrank_from_p p, hresfinrank_from_p p]
  have hram_from_p (p : Chapter07MonogenicResiduePresentation A B K L k l P res) :
      E.ramificationIndex = 1 := by
    have hprod :
        E.ramificationIndex * Module.finrank k l = Module.finrank k l := by
      calc
        E.ramificationIndex * Module.finrank k l =
            E.ramificationIndex * E.residueDegree := by
              rw [E.residueDegree_eq]
        _ = Module.finrank K L :=
          E.degree_eq_ramification_residue.symm
        _ = Module.finrank k l := hdegree_from_p p
    have hpos : 0 < Module.finrank k l := Module.finrank_pos
    apply Nat.mul_right_cancel hpos
    simpa using hprod
  have hsecond :
      Chapter07UnramifiedExtension E ↔
        Nonempty (Chapter07MonogenicResiduePresentation A B K L k l P res) := by
    constructor
    · intro hU
      exact hforward hU
    · rintro ⟨p⟩
      have hsepClass : Algebra.IsSeparable k l := hsep_from_p p
      have hsep : Chapter07ResidueExtensionIsSeparable k l := by
        let : Algebra.IsSeparable k l := hsepClass
        intro x
        exact Algebra.IsSeparable.isSeparable k x
      exact ⟨hram_from_p p, hsep⟩
  exact ⟨hfirst, hsecond, hthird⟩

/-- The monogenic criterion retains the unit-derivative clause explicitly. -/
theorem chapter07_monogenic_presentation_has_unit_derivative
    {A B K L k l : Type*} [CommRing A] [CommRing B]
    [Field K] [Field L] [Field k] [Field l]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L]
    [Algebra A L] [Algebra k l]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [FiniteDimensional K L] [FiniteDimensional k l] [Module.Finite A B]
    {P : Ideal B} {res : A →+* k}
    (p : Chapter07MonogenicResiduePresentation A B K L k l P res) :
    IsUnit (eval₂ (algebraMap A B) p.theta p.polynomial.derivative) := by
  exact p.unit_derivative

/-- The separable-reduction clause is available directly from a monogenic
presentation. -/
theorem chapter07_unit_derivative_presentation_is_separable
    {A B K L k l : Type*} [CommRing A] [CommRing B]
    [Field K] [Field L] [Field k] [Field l]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L]
    [Algebra A L] [Algebra k l]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [FiniteDimensional K L] [FiniteDimensional k l] [Module.Finite A B]
    {P : Ideal B} {res : A →+* k}
    (p : Chapter07MonogenicResiduePresentation A B K L k l P res) :
    (p.polynomial.map res).Separable := by
  exact p.residue_polynomial_separable

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07
