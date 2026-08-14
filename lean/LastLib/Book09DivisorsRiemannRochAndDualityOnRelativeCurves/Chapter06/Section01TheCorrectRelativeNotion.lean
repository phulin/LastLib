import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter06.Dependencies
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Flat.TorsionFree

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter06

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11
open RelativeScheme
open scoped BigOperators Polynomial

universe u

/-! ## 6.1. The correct relative notion -/

theorem chapter06_relative_effective_divisor_is_cartier_and_finite_flat
    {S : Scheme.{u}} {C T : RelativeScheme S} {d : ℕ}
    (D : Chapter06RelativeEffectiveDivisor C T d) :
    D.divisor.ideal.IsEffectiveCartier ∧
      Chapter06FiniteFlatRank (chapter06RelativeDivisorProjection D) d := by
  exact ⟨D.divisor.isEffectiveCartier, D.finite_flat_rank⟩

theorem chapter06_relative_effective_divisor_inclusion_is_closed_immersion
    {S : Scheme.{u}} {C T : RelativeScheme S} {d : ℕ}
    (D : Chapter06RelativeEffectiveDivisor C T d) :
    IsClosedImmersion D.divisor.inclusion := by
  infer_instance

theorem chapter06_finite_flat_closed_family_inclusion_is_closed_immersion
    {S : Scheme.{u}} {C T : RelativeScheme S} {d : ℕ}
    (Z : Chapter06FiniteFlatClosedFamily C T d) :
    IsClosedImmersion Z.ideal.subschemeι := by
  infer_instance

private theorem chapter06_effective_cartier_divisor_ext
    {X : Scheme.{u}} (D E : EffectiveCartierDivisor X)
    (h : D.ideal = E.ideal) : D = E := by
  cases D
  cases E
  cases h
  rfl

theorem chapter06_relative_effective_divisor_ext
    {S : Scheme.{u}} {C T : RelativeScheme S} {d : ℕ}
    (D E : Chapter06RelativeEffectiveDivisor C T d)
    (h : D.divisor.ideal = E.divisor.ideal) : D = E := by
  rcases D with ⟨D, hD⟩
  rcases E with ⟨E, hE⟩
  have hDE : D = E := chapter06_effective_cartier_divisor_ext D E h
  subst E
  congr

noncomputable def chapter06RelativeEffectiveDivisorBaseChange
    {S : Scheme.{u}} (C T U : RelativeScheme S) (u : U ⟶ T)
    (d : ℕ)
    (D : Chapter06RelativeEffectiveDivisor C T d) :
    Chapter06RelativeEffectiveDivisor C U d := by
  refine
    { divisor :=
        { ideal :=
            D.divisor.ideal.comap
              (chapter06RelativeDivisorBaseChangeAmbientMap C T U u)
          isEffectiveCartier := by sorry }
      finite_flat_rank := by
        exact
          (chapter06FiniteFlatClosedFamilyBaseChange C T U u d
            { ideal := D.divisor.ideal
              finite_flat_rank := D.finite_flat_rank }).finite_flat_rank }

def Chapter06RelativeDivisorBaseChangeRelation
    {S : Scheme.{u}} {C T U : RelativeScheme S} {d : ℕ}
    (u : U ⟶ T) (D : Chapter06RelativeEffectiveDivisor C T d)
    (E : Chapter06RelativeEffectiveDivisor C U d) : Prop :=
  Chapter11DivisorPullbackRelation
    (chapter06RelativeDivisorBaseChangeAmbientMap C T U u)
    D.divisor E.divisor

theorem chapter06_relative_effective_divisor_base_change_is_cartier
    {S : Scheme.{u}} (C T U : RelativeScheme S) (u : U ⟶ T)
    (d : ℕ)
    (D : Chapter06RelativeEffectiveDivisor C T d) :
    (chapter06RelativeEffectiveDivisorBaseChange C T U u d D).divisor.ideal.IsEffectiveCartier := by
  exact (chapter06RelativeEffectiveDivisorBaseChange C T U u d D).divisor.isEffectiveCartier

theorem chapter06_relative_effective_divisor_base_change_is_finite_flat
    {S : Scheme.{u}} (C T U : RelativeScheme S) (u : U ⟶ T)
    (d : ℕ)
    (D : Chapter06RelativeEffectiveDivisor C T d) :
    Chapter06FiniteFlatRank
      (chapter06RelativeDivisorProjection
        (chapter06RelativeEffectiveDivisorBaseChange C T U u d D)) d := by
  exact (chapter06RelativeEffectiveDivisorBaseChange C T U u d D).finite_flat_rank

theorem chapter06_relative_effective_divisor_base_change_has_same_rank
    {S : Scheme.{u}} (C T U : RelativeScheme S) (u : U ⟶ T)
    (d : ℕ)
    (D : Chapter06RelativeEffectiveDivisor C T d) (t : U.carrier) :
    Scheme.Hom.finrank
        (chapter06RelativeDivisorProjection
          (chapter06RelativeEffectiveDivisorBaseChange C T U u d D)) t = d := by
  exact chapter06_relativeEffectiveDivisor_rank
    (chapter06RelativeEffectiveDivisorBaseChange C T U u d D) t

theorem chapter06_relative_effective_divisor_base_change_is_pullback
    {S : Scheme.{u}} (C T U : RelativeScheme S) (u : U ⟶ T)
    (d : ℕ)
    (D : Chapter06RelativeEffectiveDivisor C T d) :
      Chapter06RelativeDivisorBaseChangeRelation u D
      (chapter06RelativeEffectiveDivisorBaseChange C T U u d D) := by
  let f := chapter06RelativeDivisorBaseChangeAmbientMap C T U u
  let I := D.divisor.ideal
  let swapIso : pullback f I.subschemeι ≅ pullback I.subschemeι f :=
    { hom := pullback.lift (pullback.snd f I.subschemeι)
          (pullback.fst f I.subschemeι) pullback.condition.symm
      inv := pullback.lift (pullback.snd I.subschemeι f)
          (pullback.fst I.subschemeι f) pullback.condition.symm
      hom_inv_id := by
        apply (IsPullback.of_hasPullback f I.subschemeι).hom_ext <;>
          simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
            Category.id_comp]
      inv_hom_id := by
        apply (IsPullback.of_hasPullback I.subschemeι f).hom_ext <;>
          simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
            Category.id_comp] }
  change ∃ e : (I.comap f).subscheme ≅ pullback I.subschemeι f,
    e.hom ≫ pullback.snd I.subschemeι f = (I.comap f).subschemeι
  refine ⟨I.comapIso f ≪≫ swapIso, ?_⟩
  change (I.comapIso f).hom ≫ swapIso.hom ≫ pullback.snd I.subschemeι f =
    (I.comap f).subschemeι
  rw [show swapIso.hom ≫ pullback.snd I.subschemeι f =
      pullback.fst f I.subschemeι by
        exact pullback.lift_snd _ _ _]
  exact I.comapIso_hom_fst f

theorem chapter06_relative_effective_divisor_base_change_id
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    (D : Chapter06RelativeEffectiveDivisor C T d) :
    chapter06RelativeEffectiveDivisorBaseChange C T T (𝟙 T) d D = D := by
  apply chapter06_relative_effective_divisor_ext
  have hmap : chapter06RelativeDivisorBaseChangeAmbientMap C T T (𝟙 T) =
      𝟙 (Chapter06RelativeDivisorAmbient C T) := by
    exact chapter06_relative_divisor_base_change_ambient_map_id C T
  change D.divisor.ideal.comap
      (chapter06RelativeDivisorBaseChangeAmbientMap C T T (𝟙 T)) =
    D.divisor.ideal
  rw [hmap, Scheme.IdealSheafData.comap_id]

theorem chapter06_relative_effective_divisor_base_change_comp
    {S : Scheme.{u}} (C T U V : RelativeScheme S)
    (u : U ⟶ T) (v : V ⟶ U) (d : ℕ)
    (D : Chapter06RelativeEffectiveDivisor C T d) :
    chapter06RelativeEffectiveDivisorBaseChange C U V v d
        (chapter06RelativeEffectiveDivisorBaseChange C T U u d D) =
      chapter06RelativeEffectiveDivisorBaseChange C T V (v ≫ u) d D := by
  apply chapter06_relative_effective_divisor_ext
  change
    (D.divisor.ideal.comap
      (chapter06RelativeDivisorBaseChangeAmbientMap C T U u)).comap
        (chapter06RelativeDivisorBaseChangeAmbientMap C U V v) =
      D.divisor.ideal.comap
        (chapter06RelativeDivisorBaseChangeAmbientMap C T V (v ≫ u))
  rw [← Scheme.IdealSheafData.comap_comp]
  congr 1
  exact chapter06_relative_divisor_base_change_ambient_map_comp C T U V u v

theorem chapter06FiniteFlatClosedFamilyBaseChange_ideal
    {S : Scheme.{u}} (C T U : RelativeScheme S) (u : U ⟶ T)
    (d : ℕ) (Z : Chapter06FiniteFlatClosedFamily C T d) :
    (chapter06FiniteFlatClosedFamilyBaseChange C T U u d Z).ideal =
      Z.ideal.comap (chapter06RelativeDivisorBaseChangeAmbientMap C T U u) :=
  rfl

theorem chapter06_finiteFlatClosedFamily_base_change_has_same_rank
    {S : Scheme.{u}} (C T U : RelativeScheme S) (u : U ⟶ T)
    (d : ℕ) (Z : Chapter06FiniteFlatClosedFamily C T d) (t : U.carrier) :
    Scheme.Hom.finrank
        (chapter06FiniteFlatClosedFamilyProjection
          (chapter06FiniteFlatClosedFamilyBaseChange C T U u d Z)) t = d := by
  exact (chapter06FiniteFlatClosedFamilyBaseChange C T U u d Z).finite_flat_rank.2.2.2 t

theorem chapter06_finiteFlatClosedFamily_base_change_is_effectiveCartier
    {S : Scheme.{u}} (C T U : RelativeScheme S) (u : U ⟶ T)
    (d : ℕ) (Z : Chapter06FiniteFlatClosedFamily C T d)
    (hZ : chapter06IsEffectiveCartierFamily Z) :
    chapter06IsEffectiveCartierFamily
      (chapter06FiniteFlatClosedFamilyBaseChange C T U u d Z) := by
  sorry

theorem chapter06_associated_line_bundle_canonical_section_vanishes_on_divisor
    {S : Scheme.{u}} {C T : RelativeScheme S} {d : ℕ}
    [Chapter10IdealDualAPI (Chapter06RelativeDivisorAmbient C T)]
    [Chapter10SectionVanishingIdealAPI (Chapter06RelativeDivisorAmbient C T)]
    (D : Chapter06RelativeEffectiveDivisor C T d) :
    chapter10SectionVanishingIdeal (chapter06AssociatedLineBundleCanonicalSection D) =
      D.divisor.ideal := by
  exact chapter10OofD_section_vanishingIdeal
    (chapter06AsChapter10EffectiveCartierDivisor D)

theorem chapter06_associated_line_bundle_has_fiberwise_degree
    {S : Scheme.{u}} {C T : RelativeScheme S} {d : ℕ}
    [Chapter06LineBundleFiberwiseDegreeAPI C T]
    [Chapter10IdealDualAPI (Chapter06RelativeDivisorAmbient C T)]
    (D : Chapter06RelativeEffectiveDivisor C T d) (t : T.carrier) :
    chapter06LineBundleFiberwiseDegree C T
      (chapter06AssociatedLineBundle D) t = (d : ℤ) := by
  exact chapter06_line_bundle_degree_of_associated_divisor D t

/-!
The following is the affine model of the warning `tx = 0` over `Spec k[t]`.
The fiber profile records the one-point fibers away from `t = 0` and the full
affine-line fiber at `t = 0`; the non-flatness theorem is the obstruction to
using this family as a relative effective divisor.
-/

abbrev chapter06TxZeroBaseRing (k : Type u) [CommRing k] := Polynomial k

abbrev chapter06TxZeroAmbientRing (k : Type u) [CommRing k] :=
  Polynomial (Polynomial k)

def chapter06TxZeroStructureMap (k : Type u) [CommRing k] :
    chapter06TxZeroBaseRing k →+* chapter06TxZeroAmbientRing k :=
  Polynomial.C

def chapter06TxZeroIdeal (k : Type u) [CommRing k] :
    Ideal (chapter06TxZeroAmbientRing k) :=
  Ideal.span ({
    Polynomial.C (Polynomial.X : Polynomial k) *
      (Polynomial.X : Polynomial (Polynomial k))
  } : Set (Polynomial (Polynomial k)))

abbrev chapter06TxZeroTotalRing (k : Type u) [CommRing k] :=
  chapter06TxZeroAmbientRing k ⧸ chapter06TxZeroIdeal k

def chapter06TxZeroQuotientMap (k : Type u) [CommRing k] :
    CommRingCat.of (chapter06TxZeroBaseRing k) ⟶
      CommRingCat.of (chapter06TxZeroTotalRing k) :=
  CommRingCat.ofHom
    ((Ideal.Quotient.mk (chapter06TxZeroIdeal k)).comp
      (chapter06TxZeroStructureMap k))

def chapter06TxZeroBaseScheme (k : Type u) [CommRing k] : Scheme :=
  Spec (.of (chapter06TxZeroBaseRing k))

def chapter06TxZeroTotalScheme (k : Type u) [CommRing k] : Scheme :=
  Spec (.of (chapter06TxZeroTotalRing k))

def chapter06TxZeroFamilyMap (k : Type u) [CommRing k] :
    chapter06TxZeroTotalScheme k ⟶ chapter06TxZeroBaseScheme k :=
  Scheme.Spec.map (chapter06TxZeroQuotientMap k).op

abbrev chapter06TxZeroFiberRing (k : Type u) [Field k] (a : k) :=
  Polynomial k ⧸
    Ideal.span ({Polynomial.C a * (Polynomial.X : Polynomial k)} : Set (Polynomial k))

def chapter06TxZeroFiberIsOnePoint (k : Type u) [Field k] (a : k) : Prop :=
  Nonempty (chapter06TxZeroFiberRing k a ≃ₐ[k] k)

def chapter06TxZeroFiberIsAffineLine (k : Type u) [Field k] : Prop :=
  Nonempty (chapter06TxZeroFiberRing k 0 ≃ₐ[k] Polynomial k)

structure Chapter06TxZeroFiberProfile (k : Type u) [Field k] where
  generic_is_one_point : ∀ a : k, a ≠ 0 → chapter06TxZeroFiberIsOnePoint k a
  special_is_affine_line : chapter06TxZeroFiberIsAffineLine k

theorem chapter06_tx_zero_fiber_profile (k : Type u) [Field k] :
    Nonempty (Chapter06TxZeroFiberProfile k) := by
  classical
  refine ⟨{
    generic_is_one_point := ?_
    special_is_affine_line := ?_ }⟩
  · intro a ha
    let I : Ideal (Polynomial k) :=
      Ideal.span ({Polynomial.C a * (Polynomial.X : Polynomial k)} : Set (Polynomial k))
    let J : Ideal (Polynomial k) :=
      Ideal.span ({(Polynomial.X : Polynomial k)} : Set (Polynomial k))
    have hunit : IsUnit (Polynomial.C a : Polynomial k) :=
      Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr ha)
    have hIJ : I = J := by
      dsimp [I, J]
      exact Ideal.span_singleton_mul_left_unit hunit Polynomial.X
    have hJ : J = Ideal.span ({Polynomial.X - Polynomial.C (0 : k)} : Set (Polynomial k)) := by
      simp [J]
    refine ⟨((Ideal.quotientEquivAlgOfEq k hIJ).trans
      ((Ideal.quotientEquivAlgOfEq k hJ).trans
        (Polynomial.quotientSpanXSubCAlgEquiv (0 : k))))⟩
  · let I : Ideal (Polynomial k) :=
      Ideal.span ({Polynomial.C (0 : k) * (Polynomial.X : Polynomial k)} : Set (Polynomial k))
    have hI : I = ⊥ := by
      simp [I]
    refine ⟨(Ideal.quotientEquivAlgOfEq k hI).trans
      (AlgEquiv.quotientBot k (Polynomial k))⟩

theorem chapter06_tx_zero_family_not_flat (k : Type u) [Field k] :
    ¬ Module.Flat (chapter06TxZeroBaseRing k) (chapter06TxZeroTotalRing k) := by
  intro hflat
  let q : chapter06TxZeroAmbientRing k →+*
      chapter06TxZeroTotalRing k := Ideal.Quotient.mk _
  let φ : chapter06TxZeroAmbientRing k →+* Polynomial k :=
    Polynomial.mapRingHom (Polynomial.evalRingHom (0 : k))
  have hφ : chapter06TxZeroIdeal k ≤ RingHom.ker φ := by
    refine Ideal.span_le.2 ?_
    intro p hp
    rw [Set.mem_singleton_iff] at hp
    subst p
    simp [φ]
  have hqX : q (Polynomial.X : chapter06TxZeroAmbientRing k) ≠ 0 := by
    intro hX
    have hmem : (Polynomial.X : chapter06TxZeroAmbientRing k) ∈
        chapter06TxZeroIdeal k := Ideal.Quotient.eq_zero_iff_mem.mp hX
    have hzero := hφ hmem
    simp [φ] at hzero
  have ht : (Polynomial.X : chapter06TxZeroBaseRing k) ∈
      nonZeroDivisors (chapter06TxZeroBaseRing k) := by
    simp [mem_nonZeroDivisors_iff_ne_zero]
  have hregular : IsSMulRegular (chapter06TxZeroTotalRing k)
      (Polynomial.X : chapter06TxZeroBaseRing k) :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors ht
  have hzero : (Polynomial.X : chapter06TxZeroBaseRing k) •
      q (Polynomial.X : chapter06TxZeroAmbientRing k) = 0 := by
    change (Polynomial.X : chapter06TxZeroBaseRing k) •
      (Submodule.Quotient.mk (p := chapter06TxZeroIdeal k)
        (Polynomial.X : chapter06TxZeroAmbientRing k)) = 0
    rw [← Submodule.Quotient.mk_smul]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.subset_span
    simp [Algebra.smul_def]
  apply hqX
  apply hregular
  change (Polynomial.X : chapter06TxZeroBaseRing k) •
    q (Polynomial.X : chapter06TxZeroAmbientRing k) =
      (Polynomial.X : chapter06TxZeroBaseRing k) • 0
  simpa only [smul_zero] using hzero

theorem chapter06_tx_zero_family_map_not_flat (k : Type u) [Field k] :
    ¬ Flat (chapter06TxZeroFamilyMap k) := by
  intro h
  apply chapter06_tx_zero_family_not_flat k
  have hs : Flat (AlgebraicGeometry.Spec.map (chapter06TxZeroQuotientMap k)) := by
    simpa [chapter06TxZeroFamilyMap, chapter06TxZeroTotalScheme,
      chapter06TxZeroBaseScheme, Scheme.Spec] using h
  have h' := (Flat.SpecMap_iff (f := chapter06TxZeroQuotientMap k)).mp hs
  dsimp only [RingHom.Flat] at h'
  convert h' using 1
  · rfl
  · rfl
  · apply Module.ext
    rename_i inst e3 e4
    cases e3
    cases e4
    funext r x
    refine Submodule.Quotient.induction_on (p := chapter06TxZeroIdeal k) x ?_
    intro y
    have hleft := Submodule.Quotient.mk_smul
      (p := chapter06TxZeroIdeal k) r y
    calc
      _ = (Submodule.Quotient.mk (r • y) : chapter06TxZeroTotalRing k) := by
        symm
        exact hleft
      _ = (Submodule.Quotient.mk (Polynomial.C r * y) :
          chapter06TxZeroTotalRing k) := by
        rw [Algebra.smul_def, Polynomial.C_eq_algebraMap]
      _ = (chapter06TxZeroQuotientMap k).hom.toAlgebra.algebraMap r *
          (Submodule.Quotient.mk y) := by
        change (Ideal.Quotient.mk (chapter06TxZeroIdeal k)) (Polynomial.C r) *
            (Ideal.Quotient.mk (chapter06TxZeroIdeal k)) y =
          (Ideal.Quotient.mk (chapter06TxZeroIdeal k)) (Polynomial.C r) *
            (Ideal.Quotient.mk (chapter06TxZeroIdeal k)) y
        rfl
      _ = _ := by
        exact (chapter06TxZeroQuotientMap k).hom.toAlgebra.smul_def' r
          (Submodule.Quotient.mk y) |>.symm

theorem chapter06_tx_zero_family_not_finite_flat_of_constant_rank
    (k : Type u) [Field k] :
    ¬ ∃ d : ℕ, Chapter06FiniteFlatRank (chapter06TxZeroFamilyMap k) d := by
  rintro ⟨d, hd⟩
  exact chapter06_tx_zero_family_map_not_flat k hd.2.1

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter06
