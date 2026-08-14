import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter06.Section01TheCorrectRelativeNotion
import Mathlib.Algebra.DualNumber

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter06

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11
open RelativeScheme

universe u

/-! ## 6.2. Smooth curves turn points into divisors -/

abbrev Chapter06SmoothRelativeCurve {S : Scheme.{u}}
    (C : RelativeScheme S) : Prop :=
  SmoothOfRelativeDimension 1 C.structuralMap

instance chapter11SmoothQuasiProjectiveCurve_to_chapter06SmoothRelativeCurve
    {S : Scheme.{u}} {C : RelativeScheme S}
    [Chapter11SmoothQuasiProjectiveCurve C] :
    Chapter06SmoothRelativeCurve C :=
  Chapter11SmoothQuasiProjectiveCurve.smooth (C := C)

private theorem chapter06_locally_regular_principal_is_effective_cartier
    {X : Scheme.{u}} (I : Chapter06ClosedSubscheme X)
    (hI : Chapter10LocallyRegularPrincipal I) : I.IsEffectiveCartier := by
  intro U x
  rcases hI x.1 with ⟨W, hxW, a, hWa, ha⟩
  obtain ⟨f, g, hfg, hxf⟩ :=
    exists_basicOpen_le_affine_inter W.2 U.2 x.1 ⟨hxW, x.2⟩
  let V : X.affineOpens := X.affineBasicOpen f
  have hVW : V ≤ W := X.affineBasicOpen_le f
  have hVW' : V.1 ≤ W.1 := hVW
  have hVU : V ≤ U := by
    change X.basicOpen f ≤ U.1
    rw [hfg]
    exact X.basicOpen_le g
  let φ := (X.presheaf.map (homOfLE hVW').op).hom
  have hideal : I.ideal V = Ideal.span ({φ a} : Set Γ(X, V)) := by
    have hmap := I.map_ideal' (U := V) (V := W) (homOfLE hVW').op
    rw [← hmap, hWa]
    rw [Ideal.map_span]
    simp [φ]
  have hregular : IsRegular (φ a) := by
    let _ : Algebra Γ(X, W) Γ(X, V) :=
      (X.presheaf.map (homOfLE hVW').op).hom.toAlgebra
    let _ : IsLocalization.Away f Γ(X, V) :=
      W.2.isLocalization_of_eq_basicOpen f (homOfLE hVW') rfl
    change IsRegular (algebraMap Γ(X, W) Γ(X, V) a)
    apply (isRegular_iff_eq_zero_of_mul).2
    have hsmul : IsSMulRegular Γ(X, V) (algebraMap Γ(X, W) Γ(X, V) a) :=
      IsSMulRegular.of_isLocalization (R := Γ(X, W)) (S := Γ(X, V))
        (p := Submonoid.powers f) ha.isSMulRegular
    constructor
    · intro b hb
      exact hsmul (by simpa [Algebra.smul_def] using hb)
    · intro b hb
      exact hsmul (by simpa [Algebra.smul_def, mul_comm] using hb)
  refine ⟨V, φ a, hxf, hVU, hideal, ?_⟩
  exact isRegular_iff_mem_nonZeroDivisors.mp hregular

theorem chapter06_smooth_curve_finite_flat_family_is_cartier
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [Chapter06SmoothRelativeCurve C]
    (Z : Chapter06FiniteFlatClosedFamily C T d) :
    ∃ D : Chapter06RelativeEffectiveDivisor C T d,
      D.divisor.ideal = Z.ideal := by
  rcases chapter10_smooth_curve_family_is_cartier C.structuralMap T.structuralMap d
      (chapter06FiniteFlatClosedFamilyAsChapter10Family C T d Z) with ⟨D, hD⟩
  refine ⟨⟨{ ideal := D.divisor.ideal,
              isEffectiveCartier :=
                chapter06_locally_regular_principal_is_effective_cartier
                  D.divisor.ideal D.divisor.locallyRegularPrincipal }, ?_⟩, hD⟩
  exact ⟨D.finiteLocallyFree.finite, D.finiteLocallyFree.flat,
    D.finiteLocallyFree.locallyOfFinitePresentation, D.finiteLocallyFree.rank⟩

noncomputable def chapter06FiniteFlatFamilyToRelativeDivisor
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [Chapter06SmoothRelativeCurve C]
    (Z : Chapter06FiniteFlatClosedFamily C T d) :
    Chapter06RelativeEffectiveDivisor C T d :=
  Classical.choose (chapter06_smooth_curve_finite_flat_family_is_cartier C T d Z)

theorem chapter06FiniteFlatFamilyToRelativeDivisor_ideal
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [Chapter06SmoothRelativeCurve C]
    (Z : Chapter06FiniteFlatClosedFamily C T d) :
    (chapter06FiniteFlatFamilyToRelativeDivisor C T d Z).divisor.ideal = Z.ideal :=
  Classical.choose_spec (chapter06_smooth_curve_finite_flat_family_is_cartier C T d Z)

def chapter06RelativeDivisorToFiniteFlatFamily
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    (D : Chapter06RelativeEffectiveDivisor C T d) :
    Chapter06FiniteFlatClosedFamily C T d :=
  { ideal := D.divisor.ideal
    finite_flat_rank := D.finite_flat_rank }

theorem chapter06RelativeDivisorToFiniteFlatFamily_ideal
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    (D : Chapter06RelativeEffectiveDivisor C T d) :
    (chapter06RelativeDivisorToFiniteFlatFamily C T d D).ideal = D.divisor.ideal :=
  rfl

theorem chapter06_relative_divisor_to_family_is_cartier
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    (D : Chapter06RelativeEffectiveDivisor C T d) :
    chapter06IsEffectiveCartierFamily
      (chapter06RelativeDivisorToFiniteFlatFamily C T d D) := by
  exact D.divisor.isEffectiveCartier

noncomputable def chapter06_length_d_family_divisor_equiv
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [Chapter06SmoothRelativeCurve C] :
    Chapter06FiniteFlatClosedFamily C T d ≃
      Chapter06RelativeEffectiveDivisor C T d where
  toFun := chapter06FiniteFlatFamilyToRelativeDivisor C T d
  invFun := chapter06RelativeDivisorToFiniteFlatFamily C T d
  left_inv := by
    intro Z
    apply chapter06FiniteFlatClosedFamily_ext
    exact chapter06FiniteFlatFamilyToRelativeDivisor_ideal C T d Z
  right_inv := by
    intro D
    apply chapter06_relative_effective_divisor_ext
    exact (chapter06FiniteFlatFamilyToRelativeDivisor_ideal C T d
      (chapter06RelativeDivisorToFiniteFlatFamily C T d D)).trans
      (chapter06RelativeDivisorToFiniteFlatFamily_ideal C T d D)

theorem chapter06_smooth_curve_length_and_divisor_functors_agree
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [Chapter06SmoothRelativeCurve C] :
    Nonempty (Chapter06FiniteFlatClosedFamily C T d ≃
      Chapter06RelativeEffectiveDivisor C T d) :=
  ⟨chapter06_length_d_family_divisor_equiv C T d⟩

theorem chapter06_smooth_curve_length_family_is_effective_cartier
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [Chapter06SmoothRelativeCurve C]
    (Z : Chapter06FiniteFlatClosedFamily C T d) :
    ∃ D : Chapter06RelativeEffectiveDivisor C T d,
      D.divisor.ideal = Z.ideal ∧
        chapter06IsEffectiveCartierFamily Z := by
  rcases chapter06_smooth_curve_finite_flat_family_is_cartier C T d Z with ⟨D, hD⟩
  refine ⟨D, hD, ?_⟩
  simpa [chapter06IsEffectiveCartierFamily, hD] using D.divisor.isEffectiveCartier

/-!
The node model is written with the affine coordinate ring used by Book 8;
its localization/completion is the usual local ring `k[[x,y]]/(xy)`.  The
profile records both the finite-flat length-one quotient and failure of local
principality of its ideal.
-/

abbrev Chapter06NodeRing (k : Type u) [Field k] := chapter10NodeRing k

abbrev Chapter06NodeIdeal (k : Type u) [Field k] := chapter10NodeIdeal k

abbrev Chapter06NodePointLengthOneProfile (k : Type u) [Field k] :=
  Chapter10NodePointLengthOneProfile k

theorem chapter06_node_point_has_length_one
    (k : Type u) [Field k] :
    Chapter06NodePointLengthOneProfile k :=
  chapter10_node_point_has_length_one k

theorem chapter06_node_point_ideal_is_not_principal
    (k : Type u) [Field k] :
    ¬ ∃ a : Chapter06NodeRing k,
      Chapter06NodeIdeal k = Ideal.span ({a} : Set (Chapter06NodeRing k)) :=
  chapter10_node_ideal_is_not_principal k

/-!
Global nonprincipality is a useful affine warning, but Cartierness is a local
condition.  Localize at the complement of the node ideal so that the next
statement records the actual stalk obstruction rather than only its global
shadow.
-/
def chapter06NodePointComplement (k : Type u) [Field k] :
    Submonoid (Chapter06NodeRing k) where
  carrier := {a | a ∉ Chapter06NodeIdeal k}
  one_mem' := by
    intro h
    apply chapter10_node_ideal_is_not_principal k
    refine ⟨1, ?_⟩
    rw [Ideal.span_singleton_one]
    exact (Ideal.eq_top_iff_one (chapter10NodeIdeal k)).2 h
  mul_mem' := by
    let R := MvPolynomial (Fin 2) k
    let I : Ideal R :=
      Ideal.span ({MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)} : Set R)
    let J : Ideal R :=
      Ideal.span ({MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)} : Set R)
    have hM : I.IsMaximal := by
      rw [Ideal.isMaximal_iff]
      constructor
      · intro h1
        have hset :
            ({MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)} : Set R) =
              MvPolynomial.X '' ({0, 1} : Set (Fin 2)) := by
          ext z
          constructor
          · intro hz
            rcases hz with rfl | rfl <;> simp
          · intro hz
            rcases hz with ⟨i, hi, rfl⟩
            fin_cases i <;> simp_all
        change 1 ∈ Ideal.span
          ({MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)} : Set R) at h1
        rw [hset] at h1
        rw [MvPolynomial.mem_ideal_span_X_image] at h1
        simp at h1
      · intro K p hIK hp hI
        have hdiff : p - MvPolynomial.C (MvPolynomial.constantCoeff p) ∈ I := by
          have hset :
              ({MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)} : Set R) =
                MvPolynomial.X '' ({0, 1} : Set (Fin 2)) := by
            ext z
            constructor
            · intro hz
              rcases hz with rfl | rfl <;> simp
            · intro hz
              rcases hz with ⟨i, hi, rfl⟩
              fin_cases i <;> simp_all
          change p - MvPolynomial.C (MvPolynomial.constantCoeff p) ∈ Ideal.span
            ({MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)} : Set R)
          rw [hset]
          rw [MvPolynomial.mem_ideal_span_X_image]
          intro m hm
          have hm0 : m ≠ 0 := by
            intro hm0
            subst m
            have hm' := MvPolynomial.mem_support_iff.mp hm
            change MvPolynomial.coeff 0
              (p - MvPolynomial.C (MvPolynomial.constantCoeff p)) ≠ 0 at hm'
            apply hm'
            rw [sub_eq_add_neg, MvPolynomial.coeff_add]
            rw [MvPolynomial.coeff_neg]
            simp [MvPolynomial.constantCoeff_eq]
          obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hm0
          exact ⟨i, by fin_cases i <;> simp, Finsupp.mem_support_iff.mp hi⟩
        have hc : MvPolynomial.C (MvPolynomial.constantCoeff p) ∈ K := by
          simpa [sub_sub] using K.sub_mem hI (hIK hdiff)
        have hcp : MvPolynomial.constantCoeff p ≠ 0 := by
          intro hcp
          apply hp
          simpa [hcp] using hdiff
        have hunit : IsUnit (MvPolynomial.C (MvPolynomial.constantCoeff p)) :=
          IsUnit.map (MvPolynomial.C : k →+* MvPolynomial (Fin 2) k) hcp.isUnit
        rw [K.eq_top_of_isUnit_mem hc hunit]
        exact Submodule.mem_top
    let _ : I.IsMaximal := hM
    have hker : RingHom.ker (Ideal.Quotient.mk J) ≤ I := by
      rw [Ideal.mk_ker]
      exact Ideal.span_le.2 (by
        intro z hz
        rcases hz with rfl
        exact I.mul_mem_left _ (Ideal.subset_span (by simp)))
    have hprime : (Chapter06NodeIdeal k).IsPrime := by
      change (I.map (Ideal.Quotient.mk J)).IsPrime
      exact
        (Ideal.IsMaximal.map_of_surjective_of_ker_le
          (f := Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective hker).isPrime
    exact fun a b ha hb hab => (hprime.mem_or_mem hab).elim ha hb

abbrev Chapter06NodePointLocalRing (k : Type u) [Field k] :=
  Localization (chapter06NodePointComplement k)

def chapter06NodePointLocalIdeal (k : Type u) [Field k] :
    Ideal (Chapter06NodePointLocalRing k) :=
  Ideal.map (algebraMap (Chapter06NodeRing k) (Chapter06NodePointLocalRing k))
    (Chapter06NodeIdeal k)

def Chapter06NodePointCartierObstruction (k : Type u) [Field k] : Prop :=
  ¬ ∃ a : Chapter06NodePointLocalRing k,
    chapter06NodePointLocalIdeal k = Ideal.span ({a} : Set (Chapter06NodePointLocalRing k))

theorem chapter06_node_point_local_ideal_is_not_principal
    (k : Type u) [Field k] :
    Chapter06NodePointCartierObstruction k := by
  classical
  let R := MvPolynomial (Fin 2) k
  let I : Ideal R :=
    Ideal.span ({MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)} : Set R)
  let J : Ideal R :=
    Ideal.span ({MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)} : Set R)
  have hset :
      ({MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)} : Set R) =
        MvPolynomial.X '' ({0, 1} : Set (Fin 2)) := by
    ext z
    constructor
    · intro hz
      rcases hz with rfl | rfl <;> simp
    · intro hz
      rcases hz with ⟨i, hi, rfl⟩
      fin_cases i <;> simp_all
  have hI_iff (z : R) :
      z ∈ I ↔ MvPolynomial.constantCoeff z = 0 := by
    change z ∈ Ideal.span
      ({MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)} : Set R) ↔ _
    rw [hset, MvPolynomial.mem_ideal_span_X_image]
    constructor
    · intro hz
      by_contra hz0
      have hzero : (0 : Fin 2 →₀ ℕ) ∈ z.support := by
        rw [MvPolynomial.mem_support_iff]
        simpa [MvPolynomial.constantCoeff_eq] using hz0
      obtain ⟨i, hi, hmi⟩ := hz 0 hzero
      exact hmi (by simp)
    · intro hz m hm
      by_cases hm0 : m = 0
      · subst m
        exact False.elim <| (MvPolynomial.mem_support_iff.mp hm) <| by
          simpa [MvPolynomial.constantCoeff_eq] using hz
      · obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hm0
        exact ⟨i, by fin_cases i <;> simp, Finsupp.mem_support_iff.mp hi⟩
  let Q : R →+* Chapter06NodeRing k := Ideal.Quotient.mk J
  let S := Chapter06NodePointLocalRing k
  let l : Chapter06NodeRing k →+* S := algebraMap _ _
  let x : S := l (Q (MvPolynomial.X (0 : Fin 2)))
  let y : S := l (Q (MvPolynomial.X (1 : Fin 2)))
  have hlocal : chapter06NodePointLocalIdeal k = Ideal.span ({x, y} : Set S) := by
    rw [chapter06NodePointLocalIdeal]
    change Ideal.map l
      (Ideal.map (Ideal.Quotient.mk J)
        (Ideal.span ({MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)} : Set R))) = _
    rw [Ideal.map_map, Ideal.map_span, Set.image_pair]
    rfl
  let ev (c : k) : R →+* DualNumber k :=
    MvPolynomial.eval₂Hom (TrivSqZeroExt.inlHom k k)
      (fun i => if i = (0 : Fin 2) then TrivSqZeroExt.inr 1
        else if i = (1 : Fin 2) then TrivSqZeroExt.inr c else 0)
  have hev (c : k) : J ≤ RingHom.ker (ev c) := by
    change Ideal.span
        ({MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)} : Set R) ≤
      RingHom.ker (ev c)
    exact Ideal.span_le.2 (by
      intro z hz
      rcases hz with rfl
      change ev c (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)) = 0
      rw [map_mul]
      rw [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
      simp)
  let qev (c : k) : Chapter06NodeRing k →+* DualNumber k :=
    Ideal.Quotient.lift J (ev c) (fun a ha => hev c ha)
  have hqev (c : k) : (qev c).comp Q = ev c := by
    apply RingHom.ext
    intro z
    rfl
  have hfst_ev (c : k) :
      (TrivSqZeroExt.fstHom k k k).toRingHom.comp (ev c) =
        MvPolynomial.constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [ev]
    · intro i
      fin_cases i <;> simp [ev]
  have hunit (c : k) :
      ∀ z : chapter06NodePointComplement k,
        IsUnit (qev c (z : Chapter06NodeRing k)) := by
    intro z
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (z : Chapter06NodeRing k)
    have hpnot : p ∉ I := by
      intro hpi
      apply z.2
      rw [← hp]
      exact Ideal.mem_map_of_mem _ hpi
    have hcp : MvPolynomial.constantCoeff p ≠ 0 := by
      intro hcp
      exact hpnot ((hI_iff p).2 hcp)
    apply TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
    have hqevp : qev c (z : Chapter06NodeRing k) = ev c p := by
      rw [← hp]
      rfl
    rw [hqevp]
    have hfstp : (ev c p).fst = MvPolynomial.constantCoeff p := by
      change ((TrivSqZeroExt.fstHom k k k).toRingHom.comp (ev c)) p = _
      rw [hfst_ev]
    rw [hfstp]
    exact hcp.isUnit
  let rho (c : k) : S →+* DualNumber k :=
    IsLocalization.lift (R := Chapter06NodeRing k) (S := S) (P := DualNumber k)
      (M := chapter06NodePointComplement k) (g := qev c) (hunit c)
  have hrho_comp (c : k) : (rho c).comp l = qev c := by
    apply RingHom.ext
    intro z
    simp [rho, l]
  have hrho_x (c : k) : rho c x = TrivSqZeroExt.inr 1 := by
    change rho c (l (Q (MvPolynomial.X (0 : Fin 2)))) = _
    rw [← RingHom.comp_apply, hrho_comp c]
    change ev c (MvPolynomial.X (0 : Fin 2)) = _
    unfold ev
    rw [MvPolynomial.eval₂Hom_X']
    simp
  have hrho_y (c : k) : rho c y = TrivSqZeroExt.inr c := by
    change rho c (l (Q (MvPolynomial.X (1 : Fin 2)))) = _
    rw [← RingHom.comp_apply, hrho_comp c]
    change ev c (MvPolynomial.X (1 : Fin 2)) = _
    unfold ev
    rw [MvPolynomial.eval₂Hom_X']
    simp
  have hfst_rho (c : k) :
      (TrivSqZeroExt.fstHom k k k).toRingHom.comp (rho c) =
        (TrivSqZeroExt.fstHom k k k).toRingHom.comp (rho 0) := by
    apply IsLocalization.ringHom_ext (R := Chapter06NodeRing k)
      (M := chapter06NodePointComplement k) (S := S) (P := k)
    apply RingHom.ext
    intro z
    change (rho c (l z)).fst = (rho 0 (l z)).fst
    rw [← RingHom.comp_apply, hrho_comp c, ← RingHom.comp_apply, hrho_comp 0]
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective z
    rw [← hp]
    change (ev c p).fst = (ev 0 p).fst
    have hc := congrArg (fun g : R →+* k => g p) (hfst_ev c)
    have h0 := congrArg (fun g : R →+* k => g p) (hfst_ev 0)
    exact hc.trans h0.symm
  rintro ⟨f, hf⟩
  have hfspan : Ideal.span ({x, y} : Set S) = Ideal.span ({f} : Set S) :=
    hlocal.symm.trans hf
  have hxmem : x ∈ Ideal.span ({f} : Set S) := by
    rw [← hfspan]
    exact Ideal.subset_span (by simp)
  have hymem : y ∈ Ideal.span ({f} : Set S) := by
    rw [← hfspan]
    exact Ideal.subset_span (by simp)
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hxmem
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hymem
  have hfmem : f ∈ Ideal.span ({x, y} : Set S) := by
    rw [hfspan]
    exact Ideal.subset_span (by simp)
  have hfstf (c : k) : (rho c f).fst = 0 := by
    have hle : Ideal.span ({x, y} : Set S) ≤
        RingHom.ker ((TrivSqZeroExt.fstHom k k k).toRingHom.comp (rho c)) := by
      refine Ideal.span_le.2 ?_
      intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl | hz
      · change (rho c x).fst = 0
        rw [hrho_x c]
        rfl
      · rcases Set.mem_singleton_iff.mp hz with rfl
        change (rho c y).fst = 0
        rw [hrho_y c]
        rfl
    have h := RingHom.mem_ker.mp (hle hfmem)
    change (rho c f).fst = 0 at h
    exact h
  have hxeq (c : k) :
      TrivSqZeroExt.inr 1 = rho c a * rho c f := by
    have h := congrArg (rho c) ha
    rw [map_mul, hrho_x c] at h
    exact h.symm
  have hyeq (c : k) :
      TrivSqZeroExt.inr c = rho c b * rho c f := by
    have h := congrArg (rho c) hb
    rw [map_mul, hrho_y c] at h
    exact h.symm
  have hbeta0 : (rho 0 f).snd ≠ 0 := by
    intro hzero
    have h := congrArg TrivSqZeroExt.snd (hxeq 0)
    have hone : (1 : k) = 0 := by
      convert h using 1 <;> simp [TrivSqZeroExt.snd_mul, hfstf 0, hzero]
    exact one_ne_zero hone
  have hb0 : (rho 0 b).fst = 0 := by
    have h := congrArg TrivSqZeroExt.snd (hyeq 0)
    have hprod : (rho 0 b).fst * (rho 0 f).snd = 0 := by
      simpa [TrivSqZeroExt.snd_mul, hfstf 0] using h.symm
    exact (mul_eq_zero.mp hprod).resolve_right hbeta0
  have hb1 : (rho 1 b).fst = 0 := by
    have h := congrArg (fun g : S →+* k => g b) (hfst_rho 1)
    change (rho 1 b).fst = (rho 0 b).fst at h
    rw [hb0] at h
    exact h
  have hone : (1 : k) = 0 := by
    have h := congrArg TrivSqZeroExt.snd (hyeq 1)
    convert h using 1 <;> simp [TrivSqZeroExt.snd_mul, hfstf 1, hb1]
  exact one_ne_zero hone

theorem chapter06_node_point_is_length_one_but_not_cartier
    (k : Type u) [Field k] :
    Chapter06NodePointLengthOneProfile k ∧
      Chapter06NodePointCartierObstruction k :=
  ⟨chapter06_node_point_has_length_one k,
    chapter06_node_point_local_ideal_is_not_principal k⟩

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter06
