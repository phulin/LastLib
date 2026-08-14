import Mathlib.RingTheory.MvPolynomial.Ideal
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.Section01TheUniversalRemedyForAnIdeal

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open scoped AlgebraicGeometry

universe u v

/-! ## 7.2. Charts and exceptional curves -/

/- The ratio charts are represented in the appropriate localization, so the notation does not
introduce an unconstrained polynomial variable. -/
def chapter07RatioSubalgebra
    (A : Type u) [CommRing A] (a b : A) :
    Subalgebra A (Localization.Away a) :=
  Algebra.adjoin A
    ({IsLocalization.mk' (Localization.Away a) b
        (⟨a, Submonoid.mem_powers _⟩ : Submonoid.powers a)} :
      Set (Localization.Away a))

def chapter07FirstRatioChart
    (A : Type u) [CommRing A] (a b : A) : Scheme :=
  Spec (.of (chapter07RatioSubalgebra A a b))

def chapter07SecondRatioChart
    (A : Type u) [CommRing A] (a b : A) : Scheme :=
  Spec (.of (chapter07RatioSubalgebra A b a))

def chapter07FirstRatioChartMap
    (A : Type u) [CommRing A] (a b : A) :
    chapter07FirstRatioChart A a b ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (chapter07RatioSubalgebra A a b)))

def chapter07SecondRatioChartMap
    (A : Type u) [CommRing A] (a b : A) :
    chapter07SecondRatioChart A a b ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (chapter07RatioSubalgebra A b a)))

def chapter07FirstRatio
    (A : Type u) [CommRing A] (a b : A) : Localization.Away a :=
  IsLocalization.mk' (Localization.Away a) b
    (⟨a, Submonoid.mem_powers _⟩ : Submonoid.powers a)

def chapter07SecondRatio
    (A : Type u) [CommRing A] (a b : A) : Localization.Away b :=
  IsLocalization.mk' (Localization.Away b) a
    (⟨b, Submonoid.mem_powers _⟩ : Submonoid.powers b)

theorem chapter07_first_ratio_relation
    (A : Type u) [CommRing A] (a b : A) :
    algebraMap A (Localization.Away a) a * chapter07FirstRatio A a b =
      algebraMap A (Localization.Away a) b := by
  exact IsLocalization.mk'_spec'_mk (S := Localization.Away a) b a (Submonoid.mem_powers a)

theorem chapter07_second_ratio_relation
    (A : Type u) [CommRing A] (a b : A) :
    algebraMap A (Localization.Away b) b * chapter07SecondRatio A a b =
      algebraMap A (Localization.Away b) a := by
  exact IsLocalization.mk'_spec'_mk (S := Localization.Away b) a b (Submonoid.mem_powers b)

structure Chapter07TwoGeneratorBlowupCharts
    (A : Type u) [CommRing A]
  (I : Ideal A) (a b : A) (hI : I = Ideal.span {a, b}) where
  blowup : Chapter07Blowup
    (chapter07AffineCoherentIdeal A I (by
      rw [hI]
      exact Submodule.fg_span (by simp)))
  firstOpen : blowup.carrier.Opens
  firstAffine : IsAffineOpen firstOpen
  firstOver :
    Chapter07SchemeIsoOver
      (firstOpen.ι ≫ blowup.projection)
      (chapter07FirstRatioChartMap A a b)
  secondOpen : blowup.carrier.Opens
  secondAffine : IsAffineOpen secondOpen
  secondOver :
    Chapter07SchemeIsoOver
      (secondOpen.ι ≫ blowup.projection)
      (chapter07SecondRatioChartMap A a b)
  cover : firstOpen ⊔ secondOpen = ⊤

theorem chapter07_two_generator_blowup_charts
    (A : Type u) [CommRing A]
    (I : Ideal A) (a b : A) (hI : I = Ideal.span {a, b}) :
    Nonempty (Chapter07TwoGeneratorBlowupCharts A I a b hI) := by
  sorry

theorem chapter07_two_generator_chart_is_subalgebra_of_localization
    (A : Type u) [CommRing A] (a b : A) :
    chapter07RatioSubalgebra A a b =
      Algebra.adjoin A
        ({IsLocalization.mk' (Localization.Away a) b
          (⟨a, Submonoid.mem_powers _⟩ : Submonoid.powers a)} :
          Set (Localization.Away a)) :=
  rfl

/-! ### The affine plane example -/

abbrev chapter07PlaneRing (k : Type u) [CommSemiring k] := MvPolynomial (Fin 2) k

def chapter07PlaneX (k : Type u) [CommRing k] : chapter07PlaneRing k :=
  MvPolynomial.X (R := k) 0

def chapter07PlaneY (k : Type u) [CommRing k] : chapter07PlaneRing k :=
  MvPolynomial.X (R := k) 1

def chapter07PlaneOriginIdeal (k : Type u) [CommRing k] : Ideal (chapter07PlaneRing k) :=
  Ideal.span {chapter07PlaneX k, chapter07PlaneY k}

abbrev chapter07PlaneFirstChartModel (k : Type u) [CommSemiring k] :=
  MvPolynomial (Fin 2) k

abbrev chapter07PlaneSecondChartModel (k : Type u) [CommSemiring k] :=
  MvPolynomial (Fin 2) k

def chapter07PlaneFirstChartX (k : Type u) [CommRing k] : chapter07PlaneFirstChartModel k :=
  MvPolynomial.X (R := k) 0

def chapter07PlaneFirstChartT (k : Type u) [CommRing k] : chapter07PlaneFirstChartModel k :=
  MvPolynomial.X (R := k) 1

def chapter07PlaneFirstChartY (k : Type u) [CommRing k] : chapter07PlaneFirstChartModel k :=
  chapter07PlaneFirstChartX k * chapter07PlaneFirstChartT k

def chapter07PlaneSecondChartS (k : Type u) [CommRing k] : chapter07PlaneSecondChartModel k :=
  MvPolynomial.X (R := k) 0

def chapter07PlaneSecondChartY (k : Type u) [CommRing k] : chapter07PlaneSecondChartModel k :=
  MvPolynomial.X (R := k) 1

def chapter07PlaneSecondChartX (k : Type u) [CommRing k] : chapter07PlaneSecondChartModel k :=
  chapter07PlaneSecondChartS k * chapter07PlaneSecondChartY k

theorem chapter07_plane_first_chart_equation (k : Type u) [CommRing k] :
    chapter07PlaneFirstChartY k =
      chapter07PlaneFirstChartX k * chapter07PlaneFirstChartT k :=
  rfl

theorem chapter07_plane_second_chart_equation (k : Type u) [CommRing k] :
    chapter07PlaneSecondChartX k =
      chapter07PlaneSecondChartS k * chapter07PlaneSecondChartY k :=
  rfl

theorem chapter07_plane_first_chart_is_affine_two_variable_ring
    (k : Type u) [Field k] :
    Nonempty
      (chapter07RatioSubalgebra (chapter07PlaneRing k) (chapter07PlaneX k) (chapter07PlaneY k)
        ≃ₐ[k] chapter07PlaneFirstChartModel k) := by
  let A := chapter07PlaneRing k
  let x : A := chapter07PlaneX k
  let y : A := chapter07PlaneY k
  let L := Localization.Away x
  let r : L := chapter07FirstRatio A x y
  let S : Subalgebra A L := chapter07RatioSubalgebra A x y
  let z : Fin 2 → L := fun i =>
    if i = 0 then algebraMap A L x else r
  let f : A →ₐ[k] L := MvPolynomial.aeval z
  have hfS : ∀ p : A, f p ∈ S := by
    intro p
    apply MvPolynomial.induction_on p
    · intro c
      have hcf : f (MvPolynomial.C c) = algebraMap k L c := MvPolynomial.algHom_C f c
      rw [hcf]
      exact S.algebraMap_mem (algebraMap k A c)
    · intro p q hp hq
      simpa [f] using S.add_mem hp hq
    · intro p i hp
      have hi : f (MvPolynomial.X i) ∈ S := by
        rw [MvPolynomial.aeval_X]
        fin_cases i
        · simp [z, x, chapter07PlaneX]
        · simp [z, r]
          exact Algebra.subset_adjoin (R := A) (s := {r}) (Set.mem_singleton r)
      simpa [f] using S.mul_mem hp hi
  let T : Subalgebra k L := S.restrictScalars k
  let eST : T ≃ₐ[k] S := {
    toFun := fun v => ⟨v.1, v.2⟩
    invFun := fun v => ⟨v.1, v.2⟩
    left_inv := by intro v; rfl
    right_inv := by intro v; rfl
    map_mul' := by intro v w; rfl
    map_add' := by intro v w; rfl
    commutes' := by intro c; rfl }
  let fS : A →ₐ[k] S := eST.toAlgHom.comp (f.codRestrict T hfS)
  let qA : A →ₐ[k] A := MvPolynomial.aeval (fun i =>
    if i = 0 then x else x * y)
  let q : A →ₐ[k] L := (IsScalarTower.toAlgHom k A L).comp qA
  have hfx : f x = algebraMap A L x := by
    change f (MvPolynomial.X (0 : Fin 2)) = _
    rw [MvPolynomial.aeval_X]
    simp [z, x, chapter07PlaneX]
  have hf_x : IsUnit (f x) := by
    rw [hfx]
    exact IsLocalization.map_units L
      (⟨x, Submonoid.mem_powers x⟩ : Submonoid.powers x)
  have hq_x : IsUnit (q x) := by
    have hqx : q x = algebraMap A L x := by
      change q (MvPolynomial.X (0 : Fin 2)) = _
      rw [show q = (IsScalarTower.toAlgHom k A L).comp qA by rfl]
      rw [AlgHom.comp_apply, MvPolynomial.aeval_X]
      simp [x, chapter07PlaneX]
      change (IsScalarTower.toAlgHom k A L) x = algebraMap A L x
      exact IsScalarTower.toAlgHom_apply k A L x
    rw [hqx]
    exact IsLocalization.map_units L
      (⟨x, Submonoid.mem_powers x⟩ : Submonoid.powers x)
  let g : L →ₐ[k] L := IsLocalization.Away.liftAlgHom x (f := f) hf_x
  let h : L →ₐ[k] L := IsLocalization.Away.liftAlgHom x (f := q) hq_x
  have h_alg (a : A) : h (algebraMap A L a) = q a := by
    change IsLocalization.Away.lift x hq_x (algebraMap A L a) = q a
    exact IsLocalization.Away.lift_eq x hq_x a
  have h_ratio : h r = algebraMap A L y := by
    change IsLocalization.Away.lift x hq_x
        (IsLocalization.mk' L y
          (⟨x, Submonoid.mem_powers x⟩ : Submonoid.powers x)) = _
    change IsLocalization.lift (S := L) _
      (IsLocalization.mk' L y
        (⟨x, Submonoid.mem_powers x⟩ : Submonoid.powers x)) = _
    rw [IsLocalization.lift_mk'_spec]
    change q (MvPolynomial.X 1) = q (MvPolynomial.X 0) *
      algebraMap A L (MvPolynomial.X 1)
    change (IsScalarTower.toAlgHom k A L)
        (MvPolynomial.aeval (fun i => if i = 0 then x else x * y)
          (MvPolynomial.X 1)) =
      (IsScalarTower.toAlgHom k A L)
        (MvPolynomial.aeval (fun i => if i = 0 then x else x * y)
          (MvPolynomial.X 0)) * algebraMap A L (MvPolynomial.X 1)
    rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    rw [if_neg (show (1 : Fin 2) ≠ 0 by decide),
      if_pos (show (0 : Fin 2) = 0 by rfl)]
    change (IsScalarTower.toAlgHom k A L) (x * y) =
      (IsScalarTower.toAlgHom k A L) x * algebraMap A L y
    rw [IsScalarTower.toAlgHom_apply k A L (x * y),
      IsScalarTower.toAlgHom_apply k A L x]
    exact map_mul (algebraMap A L) x y
  have hg_comp : g.toRingHom.comp (algebraMap A L) = f.toRingHom := by
    change (IsLocalization.Away.lift x hf_x).comp (algebraMap A L) = f.toRingHom
    exact IsLocalization.Away.lift_comp x hf_x
  have hcomp : h.toRingHom.comp g.toRingHom = RingHom.id L := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers x)
    rw [RingHom.comp_assoc, hg_comp]
    simp only [RingHom.id_comp]
    apply MvPolynomial.ringHom_ext
    · intro c
      change h (f (MvPolynomial.C c)) = algebraMap A L (MvPolynomial.C c)
      rw [MvPolynomial.algHom_C]
      rw [h.commutes c]
      rw [IsScalarTower.algebraMap_eq k A L]
      rfl
    · intro i
      fin_cases i
      · change h (f (MvPolynomial.X 0)) = algebraMap A L (MvPolynomial.X 0)
        rw [show f (MvPolynomial.X 0) = algebraMap A L x by
          rw [MvPolynomial.aeval_X]; simp [z, x, chapter07PlaneX]]
        rw [h_alg]
        change (IsScalarTower.toAlgHom k A L)
            (MvPolynomial.aeval (fun i => if i = 0 then x else x * y)
              (MvPolynomial.X 0)) = algebraMap A L (MvPolynomial.X 0)
        rw [MvPolynomial.aeval_X]
        rw [if_pos (show (0 : Fin 2) = 0 by rfl)]
        change (IsScalarTower.toAlgHom k A L) x = algebraMap A L x
        exact IsScalarTower.toAlgHom_apply k A L x
      · change h (f (MvPolynomial.X 1)) = algebraMap A L (MvPolynomial.X 1)
        rw [show f (MvPolynomial.X 1) = r by
          rw [MvPolynomial.aeval_X]; simp [z, r]]
        simpa [y, chapter07PlaneY] using h_ratio
  have hg_injective : Function.Injective g := by
    intro u v huv
    have hu : h (g u) = u := by
      simpa [RingHom.comp_apply] using congrArg (fun F : L →+* L => F u) hcomp
    have hv : h (g v) = v := by
      simpa [RingHom.comp_apply] using congrArg (fun F : L →+* L => F v) hcomp
    exact hu.symm.trans ((congrArg (fun t : L => h t) huv).trans hv)
  have halg_injective : Function.Injective (algebraMap A L) := by
    have hloc : IsLocalization (Submonoid.powers x) L := by
      change IsLocalization (Submonoid.powers (chapter07PlaneX k))
        (Localization.Away (chapter07PlaneX k))
      infer_instance
    exact @IsLocalization.injective A _ (Submonoid.powers x) L _ _ hloc
      (powers_le_nonZeroDivisors_of_noZeroDivisors (by
        change MvPolynomial.X (R := k) 0 ≠ 0
        exact MvPolynomial.X_ne_zero 0))
  have hf_injective : Function.Injective f := by
    intro p q hpq
    apply halg_injective
    apply hg_injective
    calc
      g (algebraMap A L p) = f p := by
        simpa [RingHom.comp_apply] using congrArg (fun F : A →+* L => F p) hg_comp
      _ = f q := hpq
      _ = g (algebraMap A L q) := by
        symm
        simpa [RingHom.comp_apply] using congrArg (fun F : A →+* L => F q) hg_comp
  have hfS_injective : Function.Injective fS :=
    eST.injective.comp ((AlgHom.injective_codRestrict f T hfS).2 hf_injective)
  have hfq : f.comp qA = IsScalarTower.toAlgHom k A L := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · change f (qA (MvPolynomial.X 0)) =
        (IsScalarTower.toAlgHom k A L) (MvPolynomial.X 0)
      rw [MvPolynomial.aeval_X]
      rw [if_pos (show (0 : Fin 2) = 0 by rfl)]
      rw [hfx]
      change algebraMap A L x = (IsScalarTower.toAlgHom k A L) x
      exact (IsScalarTower.toAlgHom_apply k A L x).symm
    · rw [AlgHom.comp_apply]
      change f
        (MvPolynomial.aeval (fun i => if i = 0 then x else x * y)
          (MvPolynomial.X 1)) = (IsScalarTower.toAlgHom k A L) (MvPolynomial.X 1)
      rw [MvPolynomial.aeval_X]
      rw [if_neg (show (1 : Fin 2) ≠ 0 by decide)]
      rw [map_mul]
      rw [hfx]
      have hfy : f y = r := by
        change f (MvPolynomial.X 1) = r
        rw [MvPolynomial.aeval_X]
        simp [z, r]
      rw [hfy]
      change algebraMap A L x * r = (IsScalarTower.toAlgHom k A L) y
      rw [IsScalarTower.toAlgHom_apply k A L y]
      exact chapter07_first_ratio_relation A x y
  have hrange : ∀ v : L, v ∈ Algebra.adjoin A ({r} : Set L) →
      ∃ p : A, f p = v := by
    intro v hv
    refine Algebra.adjoin_induction (R := A) (s := ({r} : Set L))
      (p := fun v _ => ∃ p : A, f p = v) ?_ ?_ ?_ ?_ hv
    · intro v hv
      rcases hv with ⟨rfl, rfl⟩
      refine ⟨MvPolynomial.X 1, ?_⟩
      change MvPolynomial.aeval z (MvPolynomial.X 1) = r
      rw [MvPolynomial.aeval_X]
      simp [z]
    · intro c
      exact ⟨qA c, congrArg (fun F : A →ₐ[k] L => F c) hfq⟩
    · intro v w hv hw ihv ihw
      rcases ihv with ⟨p, hp⟩
      rcases ihw with ⟨q, hq⟩
      exact ⟨p + q, by simp [f, hp, hq]⟩
    · intro v w hv hw ihv ihw
      rcases ihv with ⟨p, hp⟩
      rcases ihw with ⟨q, hq⟩
      exact ⟨p * q, by simp [f, hp, hq]⟩
  have hfS_surjective : Function.Surjective fS := by
    intro v
    rcases hrange v.1 v.2 with ⟨p, hp⟩
    refine ⟨p, ?_⟩
    apply Subtype.ext
    exact hp
  exact ⟨(AlgEquiv.ofBijective fS ⟨hfS_injective, hfS_surjective⟩).symm⟩

theorem chapter07_plane_second_chart_is_affine_two_variable_ring
    (k : Type u) [Field k] :
    Nonempty
      (chapter07RatioSubalgebra (chapter07PlaneRing k) (chapter07PlaneY k) (chapter07PlaneX k)
        ≃ₐ[k] chapter07PlaneSecondChartModel k) := by
  let A := chapter07PlaneRing k
  let x : A := chapter07PlaneY k
  let y : A := chapter07PlaneX k
  let L := Localization.Away x
  let r : L := chapter07SecondRatio A y x
  let S : Subalgebra A L := chapter07RatioSubalgebra A x y
  let z : Fin 2 → L := fun i =>
    if i = 0 then r else algebraMap A L x
  let f : A →ₐ[k] L := MvPolynomial.aeval z
  have hfS : ∀ p : A, f p ∈ S := by
    intro p
    apply MvPolynomial.induction_on p
    · intro c
      have hcf : f (MvPolynomial.C c) = algebraMap k L c := MvPolynomial.algHom_C f c
      rw [hcf]
      exact S.algebraMap_mem (algebraMap k A c)
    · intro p q hp hq
      simpa [f] using S.add_mem hp hq
    · intro p i hp
      have hi : f (MvPolynomial.X i) ∈ S := by
        rw [MvPolynomial.aeval_X]
        fin_cases i
        · simp [z, r]
          exact Algebra.subset_adjoin (R := A) (s := {r}) (Set.mem_singleton r)
        · simp [z, x, chapter07PlaneY]
      simpa [f] using S.mul_mem hp hi
  let T : Subalgebra k L := S.restrictScalars k
  let eST : T ≃ₐ[k] S := {
    toFun := fun v => ⟨v.1, v.2⟩
    invFun := fun v => ⟨v.1, v.2⟩
    left_inv := by intro v; rfl
    right_inv := by intro v; rfl
    map_mul' := by intro v w; rfl
    map_add' := by intro v w; rfl
    commutes' := by intro c; rfl }
  let fS : A →ₐ[k] S := eST.toAlgHom.comp (f.codRestrict T hfS)
  let qA : A →ₐ[k] A := MvPolynomial.aeval (fun i =>
    if i = 0 then y * x else x)
  let q : A →ₐ[k] L := (IsScalarTower.toAlgHom k A L).comp qA
  have hfx : f x = algebraMap A L x := by
    change f (MvPolynomial.X (1 : Fin 2)) = _
    rw [MvPolynomial.aeval_X]
    simp [z, x, chapter07PlaneY]
  have hfy : f y = r := by
    change f (MvPolynomial.X (0 : Fin 2)) = r
    rw [MvPolynomial.aeval_X]
    simp [z, r]
  have hf_x : IsUnit (f x) := by
    rw [hfx]
    exact IsLocalization.map_units L
      (⟨x, Submonoid.mem_powers x⟩ : Submonoid.powers x)
  have hq_x : IsUnit (q x) := by
    have hqx : q x = algebraMap A L x := by
      change q (MvPolynomial.X (1 : Fin 2)) = _
      rw [show q = (IsScalarTower.toAlgHom k A L).comp qA by rfl]
      rw [AlgHom.comp_apply, MvPolynomial.aeval_X]
      simp [x, chapter07PlaneY]
      change (IsScalarTower.toAlgHom k A L) x = algebraMap A L x
      exact IsScalarTower.toAlgHom_apply k A L x
    rw [hqx]
    exact IsLocalization.map_units L
      (⟨x, Submonoid.mem_powers x⟩ : Submonoid.powers x)
  let g : L →ₐ[k] L := IsLocalization.Away.liftAlgHom x (f := f) hf_x
  let h : L →ₐ[k] L := IsLocalization.Away.liftAlgHom x (f := q) hq_x
  have h_alg (a : A) : h (algebraMap A L a) = q a := by
    change IsLocalization.Away.lift x hq_x (algebraMap A L a) = q a
    exact IsLocalization.Away.lift_eq x hq_x a
  have h_ratio : h r = algebraMap A L y := by
    change IsLocalization.Away.lift x hq_x
        (IsLocalization.mk' L y
          (⟨x, Submonoid.mem_powers x⟩ : Submonoid.powers x)) = _
    change IsLocalization.lift (S := L) _
      (IsLocalization.mk' L y
        (⟨x, Submonoid.mem_powers x⟩ : Submonoid.powers x)) = _
    rw [IsLocalization.lift_mk'_spec]
    change q (MvPolynomial.X 0) = q (MvPolynomial.X 1) *
      algebraMap A L (MvPolynomial.X 0)
    change (IsScalarTower.toAlgHom k A L)
        (MvPolynomial.aeval (fun i => if i = 0 then y * x else x)
          (MvPolynomial.X 0)) =
      (IsScalarTower.toAlgHom k A L)
        (MvPolynomial.aeval (fun i => if i = 0 then y * x else x)
          (MvPolynomial.X 1)) * algebraMap A L (MvPolynomial.X 0)
    rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    rw [if_pos (show (0 : Fin 2) = 0 by rfl),
      if_neg (show (1 : Fin 2) ≠ 0 by decide)]
    change (IsScalarTower.toAlgHom k A L) (y * x) =
      (IsScalarTower.toAlgHom k A L) x * algebraMap A L y
    rw [IsScalarTower.toAlgHom_apply k A L (y * x),
      IsScalarTower.toAlgHom_apply k A L x]
    rw [map_mul]
    simp [mul_comm]
  have hg_comp : g.toRingHom.comp (algebraMap A L) = f.toRingHom := by
    change (IsLocalization.Away.lift x hf_x).comp (algebraMap A L) = f.toRingHom
    exact IsLocalization.Away.lift_comp x hf_x
  have hcomp : h.toRingHom.comp g.toRingHom = RingHom.id L := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers x)
    rw [RingHom.comp_assoc, hg_comp]
    simp only [RingHom.id_comp]
    apply MvPolynomial.ringHom_ext
    · intro c
      change h (f (MvPolynomial.C c)) = algebraMap A L (MvPolynomial.C c)
      rw [MvPolynomial.algHom_C]
      rw [h.commutes c]
      rw [IsScalarTower.algebraMap_eq k A L]
      rfl
    · intro i
      fin_cases i
      · change h (f (MvPolynomial.X 0)) = algebraMap A L (MvPolynomial.X 0)
        rw [show f (MvPolynomial.X 0) = r by
          rw [MvPolynomial.aeval_X]
          simp [z, r]]
        rw [h_ratio]
        simp [y, chapter07PlaneX]
      · change h (f (MvPolynomial.X 1)) = algebraMap A L (MvPolynomial.X 1)
        rw [show f (MvPolynomial.X 1) = algebraMap A L x by
          rw [MvPolynomial.aeval_X]
          simp [z, x, chapter07PlaneY]]
        rw [h_alg]
        change (IsScalarTower.toAlgHom k A L)
            (MvPolynomial.aeval (fun i => if i = 0 then y * x else x)
              (MvPolynomial.X 1)) = algebraMap A L (MvPolynomial.X 1)
        rw [MvPolynomial.aeval_X]
        rw [if_neg (show (1 : Fin 2) ≠ 0 by decide)]
        change (IsScalarTower.toAlgHom k A L) x = algebraMap A L x
        exact IsScalarTower.toAlgHom_apply k A L x
  have hg_injective : Function.Injective g := by
    intro u v huv
    have hu : h (g u) = u := by
      simpa [RingHom.comp_apply] using congrArg (fun F : L →+* L => F u) hcomp
    have hv : h (g v) = v := by
      simpa [RingHom.comp_apply] using congrArg (fun F : L →+* L => F v) hcomp
    exact hu.symm.trans ((congrArg (fun t : L => h t) huv).trans hv)
  have halg_injective : Function.Injective (algebraMap A L) := by
    have hloc : IsLocalization (Submonoid.powers x) L := by
      change IsLocalization (Submonoid.powers (chapter07PlaneY k))
        (Localization.Away (chapter07PlaneY k))
      infer_instance
    exact @IsLocalization.injective A _ (Submonoid.powers x) L _ _ hloc
      (powers_le_nonZeroDivisors_of_noZeroDivisors (by
        change MvPolynomial.X (R := k) 1 ≠ 0
        exact MvPolynomial.X_ne_zero 1))
  have hf_injective : Function.Injective f := by
    intro p q hpq
    apply halg_injective
    apply hg_injective
    calc
      g (algebraMap A L p) = f p := by
        simpa [RingHom.comp_apply] using congrArg (fun F : A →+* L => F p) hg_comp
      _ = f q := hpq
      _ = g (algebraMap A L q) := by
        symm
        simpa [RingHom.comp_apply] using congrArg (fun F : A →+* L => F q) hg_comp
  have hfS_injective : Function.Injective fS :=
    eST.injective.comp ((AlgHom.injective_codRestrict f T hfS).2 hf_injective)
  have hfq : f.comp qA = IsScalarTower.toAlgHom k A L := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · rw [AlgHom.comp_apply]
      change f
        (MvPolynomial.aeval (fun i => if i = 0 then y * x else x)
          (MvPolynomial.X 0)) = (IsScalarTower.toAlgHom k A L) (MvPolynomial.X 0)
      rw [MvPolynomial.aeval_X]
      rw [if_pos (show (0 : Fin 2) = 0 by rfl)]
      rw [map_mul, hfy, hfx]
      change r * algebraMap A L x = (IsScalarTower.toAlgHom k A L) y
      rw [IsScalarTower.toAlgHom_apply k A L y]
      simpa [r, mul_comm] using (chapter07_second_ratio_relation A y x)
    · rw [AlgHom.comp_apply]
      change f
        (MvPolynomial.aeval (fun i => if i = 0 then y * x else x)
          (MvPolynomial.X 1)) = (IsScalarTower.toAlgHom k A L) (MvPolynomial.X 1)
      rw [MvPolynomial.aeval_X]
      rw [if_neg (show (1 : Fin 2) ≠ 0 by decide)]
      change f x = (IsScalarTower.toAlgHom k A L) x
      rw [hfx]
      exact IsScalarTower.toAlgHom_apply k A L x
  have hrange : ∀ v : L, v ∈ Algebra.adjoin A ({r} : Set L) →
      ∃ p : A, f p = v := by
    intro v hv
    refine Algebra.adjoin_induction (R := A) (s := ({r} : Set L))
      (p := fun v _ => ∃ p : A, f p = v) ?_ ?_ ?_ ?_ hv
    · intro v hv
      rcases hv with ⟨rfl, rfl⟩
      refine ⟨MvPolynomial.X 0, ?_⟩
      change MvPolynomial.aeval z (MvPolynomial.X 0) = r
      rw [MvPolynomial.aeval_X]
      simp [z]
    · intro c
      exact ⟨qA c, congrArg (fun F : A →ₐ[k] L => F c) hfq⟩
    · intro v w hv hw ihv ihw
      rcases ihv with ⟨p, hp⟩
      rcases ihw with ⟨q, hq⟩
      exact ⟨p + q, by simp [f, hp, hq]⟩
    · intro v w hv hw ihv ihw
      rcases ihv with ⟨p, hp⟩
      rcases ihw with ⟨q, hq⟩
      exact ⟨p * q, by simp [f, hp, hq]⟩
  have hfS_surjective : Function.Surjective fS := by
    intro v
    rcases hrange v.1 v.2 with ⟨p, hp⟩
    refine ⟨p, ?_⟩
    apply Subtype.ext
    exact hp
  exact ⟨(AlgEquiv.ofBijective fS ⟨hfS_injective, hfS_surjective⟩).symm⟩

theorem chapter07_plane_first_ratio_chart_is_polynomial_affine
    (k : Type u) [Field k] :
    Nonempty
      (chapter07FirstRatioChart (chapter07PlaneRing k) (chapter07PlaneX k) (chapter07PlaneY k) ≅
        Spec (.of (chapter07PlaneFirstChartModel k))) := by
  rcases chapter07_plane_first_chart_is_affine_two_variable_ring k with ⟨e⟩
  let E : CommRingCat.of
      (chapter07RatioSubalgebra (chapter07PlaneRing k)
        (chapter07PlaneX k) (chapter07PlaneY k)) ≅
      CommRingCat.of (chapter07PlaneFirstChartModel k) :=
    e.toRingEquiv.toCommRingCatIso
  let eSpec : Spec (.of
      (chapter07RatioSubalgebra (chapter07PlaneRing k)
        (chapter07PlaneX k) (chapter07PlaneY k))) ≅
      Spec (.of (chapter07PlaneFirstChartModel k)) := {
    hom := Spec.map E.inv
    inv := Spec.map E.hom
    hom_inv_id := by rw [← Spec.map_comp]; simp
    inv_hom_id := by rw [← Spec.map_comp]; simp }
  exact ⟨by simpa [chapter07FirstRatioChart] using eSpec⟩

theorem chapter07_plane_second_ratio_chart_is_polynomial_affine
    (k : Type u) [Field k] :
    Nonempty
      (chapter07SecondRatioChart (chapter07PlaneRing k) (chapter07PlaneX k) (chapter07PlaneY k) ≅
        Spec (.of (chapter07PlaneSecondChartModel k))) := by
  rcases chapter07_plane_second_chart_is_affine_two_variable_ring k with ⟨e⟩
  let E : CommRingCat.of
      (chapter07RatioSubalgebra (chapter07PlaneRing k)
        (chapter07PlaneY k) (chapter07PlaneX k)) ≅
      CommRingCat.of (chapter07PlaneSecondChartModel k) :=
    e.toRingEquiv.toCommRingCatIso
  let eSpec : Spec (.of
      (chapter07RatioSubalgebra (chapter07PlaneRing k)
        (chapter07PlaneY k) (chapter07PlaneX k))) ≅
      Spec (.of (chapter07PlaneSecondChartModel k)) := {
    hom := Spec.map E.inv
    inv := Spec.map E.hom
    hom_inv_id := by rw [← Spec.map_comp]; simp
    inv_hom_id := by rw [← Spec.map_comp]; simp }
  exact ⟨by simpa [chapter07SecondRatioChart] using eSpec⟩

noncomputable def chapter07PlaneOriginPoint
    (k : Type u) [Field k] : Spec (.of (chapter07PlaneRing k)) := by
  let f : chapter07PlaneRing k →+* k := MvPolynomial.constantCoeff
  have hset :
      MvPolynomial.X (R := k) '' ({(0 : Fin 2), 1} : Set (Fin 2)) =
        {chapter07PlaneX k, chapter07PlaneY k} := by
    ext z
    constructor
    · rintro ⟨i, hi, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      fin_cases i <;> simp [chapter07PlaneX, chapter07PlaneY]
    · intro hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact ⟨0, by simp, rfl⟩
      · exact ⟨1, by simp, rfl⟩
  have hker : RingHom.ker f = chapter07PlaneOriginIdeal k := by
    apply le_antisymm
    · intro p hp
      change p ∈ Ideal.span {chapter07PlaneX k, chapter07PlaneY k}
      rw [← hset, MvPolynomial.mem_ideal_span_X_image]
      intro m hm
      have hm0 : m ≠ 0 := by
        intro hmzero
        have hcoeff : MvPolynomial.coeff (0 : Fin 2 →₀ ℕ) p = 0 := by
          simpa [f, MvPolynomial.constantCoeff_eq] using hp
        exact (MvPolynomial.mem_support_iff.mp hm) (by simpa [hmzero] using hcoeff)
      obtain ⟨i, hi⟩ := m.support_nonempty_iff.mpr hm0
      refine ⟨i, ?_, Finsupp.mem_support_iff.mp hi⟩
      fin_cases i <;> simp
    · change Ideal.span {chapter07PlaneX k, chapter07PlaneY k} ≤ RingHom.ker f
      rw [Ideal.span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl <;> simp [f, chapter07PlaneX, chapter07PlaneY]
  exact ⟨chapter07PlaneOriginIdeal k, hker ▸ RingHom.ker_isPrime f⟩

noncomputable def chapter07PlaneBlowup
    (k : Type u) [Field k] :
    Chapter07Blowup
      (chapter07AffineCoherentIdeal (chapter07PlaneRing k)
        (chapter07PlaneOriginIdeal k) (by
          change (Ideal.span {chapter07PlaneX k, chapter07PlaneY k}).FG
          exact Submodule.fg_span (by simp))) :=
  chapter07Blowup _

def chapter07PlaneExceptionalFiber (k : Type u) [Field k] : Scheme :=
  (chapter07PlaneBlowup k).projection.fiber (chapter07PlaneOriginPoint k)

theorem chapter07_plane_origin_exceptional_fiber_is_projective_line
    (k : Type u) [Field k] :
    Nonempty
      (chapter07PlaneExceptionalFiber k ≅ chapter04ProjectiveLine k) := by
  sorry

/-! ### Regular surfaces and residue-field forms of the exceptional curve -/

noncomputable def chapter07PointIdeal {X : Scheme.{u}} (x : X) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    (⟨closure ({x} : Set X), isClosed_closure⟩ : Closeds X)

theorem chapter07_blowup_of_regular_surface_at_regular_point_is_regular
    {X : Scheme.{u}} (hX : Chapter07RegularSurface X) (x : X)
    (hx : Chapter07ClosedRegularPoint x)
    (I : Chapter07CoherentIdeal X)
    (hI : I.ideal = chapter07PointIdeal x) :
    Chapter07RegularSurface (chapter07Blowup I).carrier := by
  sorry

def chapter07FirstChartParameterA
    (A : Type u) [CommRing A] (a b : A) :
    chapter07RatioSubalgebra A a b :=
  algebraMap A _ a

def chapter07FirstChartParameterB
    (A : Type u) [CommRing A] (a b : A) :
    chapter07RatioSubalgebra A a b :=
  algebraMap A _ b

def chapter07FirstChartParameterT
    (A : Type u) [CommRing A] (a b : A) :
    chapter07RatioSubalgebra A a b :=
  ⟨chapter07FirstRatio A a b,
    Algebra.subset_adjoin (Set.mem_singleton (chapter07FirstRatio A a b))⟩

theorem chapter07_first_chart_parameter_relation
    (A : Type u) [CommRing A] (a b : A) :
    chapter07FirstChartParameterA A a b * chapter07FirstChartParameterT A a b =
      chapter07FirstChartParameterB A a b := by
  apply Subtype.ext
  exact chapter07_first_ratio_relation A a b

def chapter07SecondChartParameterA
    (A : Type u) [CommRing A] (a b : A) :
    chapter07RatioSubalgebra A b a :=
  algebraMap A _ a

def chapter07SecondChartParameterB
    (A : Type u) [CommRing A] (a b : A) :
    chapter07RatioSubalgebra A b a :=
  algebraMap A _ b

def chapter07SecondChartParameterS
    (A : Type u) [CommRing A] (a b : A) :
    chapter07RatioSubalgebra A b a :=
  ⟨chapter07SecondRatio A a b,
    Algebra.subset_adjoin (Set.mem_singleton (chapter07SecondRatio A a b))⟩

theorem chapter07_second_chart_parameter_relation
    (A : Type u) [CommRing A] (a b : A) :
    chapter07SecondChartParameterB A a b * chapter07SecondChartParameterS A a b =
      chapter07SecondChartParameterA A a b := by
  apply Subtype.ext
  exact chapter07_second_ratio_relation A a b

def chapter07ExceptionalCurveAtPoint
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X} (B : Chapter07Blowup I) (x : X) : Scheme :=
  B.projection.fiber x

theorem chapter07_exceptional_curve_is_projective_line_over_residue_field
    {X : Scheme.{u}} (hX : Chapter07RegularSurface X) (x : X)
    (hx : Chapter07ClosedRegularPoint x)
    (hxDimension : Order.coheight x = 2)
    (I : Chapter07CoherentIdeal X)
    (hI : I.ideal = chapter07PointIdeal x) :
    Nonempty
      (chapter07ExceptionalCurveAtPoint (chapter07Blowup I) x ≅
        chapter04ProjectiveLine (X.residueField x)) := by
  sorry

def chapter07ExceptionalDirection
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X} (B : Chapter07Blowup I) (x : X) :=
  chapter07ExceptionalCurveAtPoint B x

theorem chapter07_exceptional_curve_records_tangent_directions
    {X : Scheme.{u}} (hX : Chapter07RegularSurface X) (x : X)
    (hx : Chapter07ClosedRegularPoint x)
    (hxDimension : Order.coheight x = 2)
    (I : Chapter07CoherentIdeal X)
    (hI : I.ideal = chapter07PointIdeal x) :
    Nonempty
      (chapter07ExceptionalDirection (chapter07Blowup I) x ≅
        chapter04ProjectiveLine (X.residueField x)) := by
  exact chapter07_exceptional_curve_is_projective_line_over_residue_field
    hX x hx hxDimension I hI

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07
