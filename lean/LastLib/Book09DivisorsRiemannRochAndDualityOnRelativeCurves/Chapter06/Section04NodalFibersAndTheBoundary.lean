import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter06.Section03UniversalDivisorsAndAddition

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter06

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01
open RelativeScheme
open scoped AlgebraicGeometry

universe u

/-! ## 6.4. Nodal fibers and the boundary -/

abbrev Chapter06CartierDivisorPoint {S : Scheme.{u}}
    (C T : RelativeScheme S) (d : ℕ) :=
  {Z : Chapter06FiniteFlatClosedFamily C T d // chapter06IsEffectiveCartierFamily Z}

theorem chapter06_cartier_divisor_locus_is_open
    {S : Scheme.{u}} (C : RelativeScheme S) (d : ℕ)
    (H : Chapter06LengthDHilbertSpaceData C d)
    (hC : Chapter06NodalRelativeCurve C) :
    Nonempty (Chapter06CartierDivisorOpenLocusData C d H) := by
  sorry

theorem chapter06_cartier_divisor_locus_is_stable_under_base_change
    {S : Scheme.{u}} (C : RelativeScheme S) (d : ℕ)
    (H : Chapter06LengthDHilbertSpaceData C d)
    (L : Chapter06CartierDivisorOpenLocusData C d H)
    (T U : RelativeScheme S) (u : U ⟶ T)
    (f : T ⟶ L.locus) :
    chapter06IsEffectiveCartierFamily
      (chapter06FiniteFlatClosedFamilyBaseChange C T U u d
        ((L.represents T f).1)) := by
  exact chapter06_finiteFlatClosedFamily_base_change_is_effectiveCartier C T U u d
    ((L.represents T f).1) ((L.represents T f).2)

theorem chapter06_cartier_divisor_locus_representation_is_natural
    {S : Scheme.{u}} (C : RelativeScheme S) (d : ℕ)
    (H : Chapter06LengthDHilbertSpaceData C d)
    (L : Chapter06CartierDivisorOpenLocusData C d H)
    (T U : RelativeScheme S) (u : U ⟶ T)
    (f : T ⟶ L.locus) :
    chapter06FiniteFlatClosedFamilyBaseChange C T U u d
        ((L.represents T f).1) =
      (L.represents U (u ≫ f)).1 := by
  exact L.represents_natural u f

/-!
The standard ramified smoothing is kept at the coordinate-ring level.  This
is enough to expose the two-generator section ideal and the missing Cartier
limit without introducing a second local-ring implementation.
-/

abbrev chapter06NodalSmoothingPolynomialRing (R : Type u) [CommSemiring R] :=
  MvPolynomial (Fin 2) R

def chapter06NodalSmoothingEquationIdeal
    (R : Type u) [CommRing R] (π : R) :
    Ideal (chapter06NodalSmoothingPolynomialRing R) :=
  Ideal.span ({
    MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) -
      MvPolynomial.C (π ^ 2)
  } : Set (chapter06NodalSmoothingPolynomialRing R))

private theorem chapter06_mvPolynomial_eval₂_kernel_fin_two
    (R : Type u) [CommRing R] (a : Fin 2 → R) :
    RingHom.ker (MvPolynomial.eval₂Hom (RingHom.id R) a) =
      Ideal.span ({
        MvPolynomial.X (0 : Fin 2) - MvPolynomial.C (a 0),
        MvPolynomial.X (1 : Fin 2) - MvPolynomial.C (a 1)
      } : Set (chapter06NodalSmoothingPolynomialRing R)) := by
  let ev := MvPolynomial.eval₂Hom (RingHom.id R) a
  let J : Ideal (chapter06NodalSmoothingPolynomialRing R) := Ideal.span ({
    MvPolynomial.X (0 : Fin 2) - MvPolynomial.C (a 0),
    MvPolynomial.X (1 : Fin 2) - MvPolynomial.C (a 1)
  } : Set (chapter06NodalSmoothingPolynomialRing R))
  apply le_antisymm
  · intro p hp
    change ev p = 0 at hp
    have hdecomp : ∀ p : chapter06NodalSmoothingPolynomialRing R,
        p - MvPolynomial.C (ev p) ∈ J := by
      intro p
      induction p using MvPolynomial.induction_on with
      | C r => simp [ev]
      | add p q hp hq =>
          convert J.add_mem hp hq using 1; simp [ev]; ring
      | mul_X p i hp =>
          have hgen : MvPolynomial.X i - MvPolynomial.C (a i) ∈ J := by
            apply Ideal.subset_span
            fin_cases i
            all_goals simp
          have hmul := J.mul_mem_right (MvPolynomial.X i) hp
          have hgenmul := J.mul_mem_left (MvPolynomial.C (ev p)) hgen
          convert J.add_mem hmul hgenmul using 1; simp [ev]; ring
    simpa [hp] using hdecomp p
  · change J ≤ RingHom.ker ev
    refine Ideal.span_le.2 ?_
    intro p hp
    rcases hp with rfl | rfl
    · simp [ev]
    · simp [ev]

abbrev chapter06NodalSmoothingTotalRing
    (R : Type u) [CommRing R] (π : R) :=
  chapter06NodalSmoothingPolynomialRing R ⧸
    chapter06NodalSmoothingEquationIdeal R π

def chapter06NodalSmoothingBaseStructureMap
    (R : Type u) [CommRing R] (π : R) :
    R →+* chapter06NodalSmoothingTotalRing R π :=
  (Ideal.Quotient.mk (chapter06NodalSmoothingEquationIdeal R π)).comp
    (MvPolynomial.C)

def chapter06NodalSmoothingQuotientMap
    (R : Type u) [CommRing R] (π : R) :
    CommRingCat.of R ⟶ CommRingCat.of (chapter06NodalSmoothingTotalRing R π) :=
  CommRingCat.ofHom (chapter06NodalSmoothingBaseStructureMap R π)

def chapter06NodalSmoothingBaseScheme
    (R : Type u) [CommRing R] : Scheme :=
  Spec (.of R)

def chapter06NodalSmoothingTotalScheme
    (R : Type u) [CommRing R] (π : R) : Scheme :=
  Spec (.of (chapter06NodalSmoothingTotalRing R π))

def chapter06NodalSmoothingFamilyMap
    (R : Type u) [CommRing R] (π : R) :
    chapter06NodalSmoothingTotalScheme R π ⟶ chapter06NodalSmoothingBaseScheme R :=
  Scheme.Spec.map (chapter06NodalSmoothingQuotientMap R π).op

def chapter06NodalSmoothingSectionMap
    (R : Type u) [CommRing R] (π : R) :
    chapter06NodalSmoothingTotalRing R π →+* R :=
  Ideal.Quotient.lift
    (chapter06NodalSmoothingEquationIdeal R π)
    (MvPolynomial.eval₂Hom (RingHom.id R) (fun _ : Fin 2 => π)) (by
      change Ideal.span ({
        MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) -
          MvPolynomial.C (π ^ 2)
      } : Set (chapter06NodalSmoothingPolynomialRing R)) ≤
        RingHom.ker (MvPolynomial.eval₂Hom (RingHom.id R) (fun _ : Fin 2 => π))
      refine Ideal.span_le.2 ?_
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      simp [pow_two])

def chapter06NodalSmoothingSection
    (R : Type u) [CommRing R] (π : R) :
    chapter06NodalSmoothingBaseScheme R ⟶
      chapter06NodalSmoothingTotalScheme R π :=
  Scheme.Spec.map (CommRingCat.ofHom (chapter06NodalSmoothingSectionMap R π)).op

theorem chapter06_nodal_smoothing_section_is_over_base
    (R : Type u) [CommRing R] (π : R) :
    chapter06NodalSmoothingSection R π ≫
        chapter06NodalSmoothingFamilyMap R π =
      𝟙 (chapter06NodalSmoothingBaseScheme R) := by
  dsimp [chapter06NodalSmoothingSection, chapter06NodalSmoothingFamilyMap,
    chapter06NodalSmoothingQuotientMap, chapter06NodalSmoothingSectionMap,
    chapter06NodalSmoothingBaseStructureMap, chapter06NodalSmoothingBaseScheme,
    chapter06NodalSmoothingTotalScheme]
  simp only [← CommRingCat.ofHom_comp]
  rw [← Spec.map_comp]
  rw [← CommRingCat.ofHom_comp, ← Spec.map_id]
  congr 1
  ext x
  simp

def chapter06NodalSmoothingSectionIdeal
    (R : Type u) [CommRing R] (π : R) :
    Ideal (chapter06NodalSmoothingTotalRing R π) :=
  Ideal.map (Ideal.Quotient.mk (chapter06NodalSmoothingEquationIdeal R π))
    (Ideal.span ({
      MvPolynomial.X (0 : Fin 2) - MvPolynomial.C π,
      MvPolynomial.X (1 : Fin 2) - MvPolynomial.C π
    } : Set (chapter06NodalSmoothingPolynomialRing R)))

def chapter06NodalSmoothingSectionPointKernel
    (R : Type u) [CommRing R] (π : R) :
    Ideal (chapter06NodalSmoothingTotalRing R π) :=
  RingHom.ker (chapter06NodalSmoothingSectionMap R π)

theorem chapter06_nodal_smoothing_section_ideal_eq_point_kernel
    (R : Type u) [CommRing R] (π : R) :
    chapter06NodalSmoothingSectionIdeal R π =
      chapter06NodalSmoothingSectionPointKernel R π := by
  rw [chapter06NodalSmoothingSectionIdeal, chapter06NodalSmoothingSectionPointKernel]
  symm
  have hker :
      RingHom.ker (chapter06NodalSmoothingSectionMap R π) =
        (RingHom.ker (MvPolynomial.eval₂Hom (RingHom.id R) (fun _ : Fin 2 => π))).map
          (Ideal.Quotient.mk (chapter06NodalSmoothingEquationIdeal R π)) := by
    unfold chapter06NodalSmoothingSectionMap
    apply Ideal.ker_quotient_lift
  rw [hker, chapter06_mvPolynomial_eval₂_kernel_fin_two]

/-!
The local ring used for the section obstruction must be the stalk over the
closed point of the base.  Localizing at the complement of the section kernel
would invert `π`, and therefore localize at the generic point of the section;
the section ideal is principal there.  The preimage of the units of the local
base is the complement of the maximal ideal over the closed point whenever the
section passes through the node; for a DVR with uniformizer `π` this ideal is
`(π, x, y)`.  It is a multiplicative set without any extra primality proof.
-/
def chapter06NodalSmoothingSectionPointComplement
    (R : Type u) [CommRing R] [IsLocalRing R] (π : R) :
    Submonoid (chapter06NodalSmoothingTotalRing R π) where
  carrier := {a | IsUnit (chapter06NodalSmoothingSectionMap R π a)}
  one_mem' := by
    change IsUnit (chapter06NodalSmoothingSectionMap R π 1)
    simp
  mul_mem' := by
    intro a b ha hb
    change IsUnit (chapter06NodalSmoothingSectionMap R π (a * b))
    change IsUnit (chapter06NodalSmoothingSectionMap R π a) at ha
    change IsUnit (chapter06NodalSmoothingSectionMap R π b) at hb
    rw [map_mul]
    exact ha.mul hb

abbrev Chapter06NodalSmoothingSectionPointLocalRing
    (R : Type u) [CommRing R] [IsLocalRing R] [IsDomain R] (π : R) :=
  Localization (chapter06NodalSmoothingSectionPointComplement R π)

def chapter06NodalSmoothingSectionPointLocalIdeal
    (R : Type u) [CommRing R] [IsLocalRing R] [IsDomain R] (π : R) :
    Ideal (Chapter06NodalSmoothingSectionPointLocalRing R π) :=
  Ideal.map (algebraMap (chapter06NodalSmoothingTotalRing R π)
      (Chapter06NodalSmoothingSectionPointLocalRing R π))
    (chapter06NodalSmoothingSectionIdeal R π)

def Chapter06NodalSmoothingSectionCartierObstruction
    (R : Type u) [CommRing R] [IsLocalRing R] [IsDomain R] (π : R) : Prop :=
  ¬ ∃ a : Chapter06NodalSmoothingSectionPointLocalRing R π,
    chapter06NodalSmoothingSectionPointLocalIdeal R π =
      Ideal.span ({a} : Set (Chapter06NodalSmoothingSectionPointLocalRing R π))

def chapter06NodalSmoothingNodeIdeal
    (R : Type u) [CommRing R] (π : R) :
    Ideal (chapter06NodalSmoothingTotalRing R π) :=
  Ideal.map (Ideal.Quotient.mk (chapter06NodalSmoothingEquationIdeal R π))
    (Ideal.span ({
      MvPolynomial.X (0 : Fin 2),
      MvPolynomial.X (1 : Fin 2)
    } : Set (chapter06NodalSmoothingPolynomialRing R)))

abbrev chapter06NodalSmoothingGenericFiberRing
    (R : Type u) [CommRing R] [IsDomain R] (π : R) :=
  MvPolynomial (Fin 2) (FractionRing R) ⧸
    Ideal.span ({
      MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) -
        MvPolynomial.C ((algebraMap R (FractionRing R) π) ^ 2)
    } : Set (MvPolynomial (Fin 2) (FractionRing R)))

def chapter06NodalSmoothingGenericFiberStructureMap
    (R : Type u) [CommRing R] [IsDomain R] (π : R) :
    FractionRing R →+* chapter06NodalSmoothingGenericFiberRing R π :=
  (Ideal.Quotient.mk _).comp (MvPolynomial.C)

def chapter06NodalSmoothingGenericFiberMap
    (R : Type u) [CommRing R] [IsDomain R] (π : R) :
    Spec (.of (chapter06NodalSmoothingGenericFiberRing R π)) ⟶
      Spec (.of (FractionRing R)) :=
  Scheme.Spec.map
    (CommRingCat.ofHom (chapter06NodalSmoothingGenericFiberStructureMap R π)).op

def chapter06NodalSmoothingGenericFiberSectionIdeal
    (R : Type u) [CommRing R] [IsDomain R] (π : R) :
    Ideal (chapter06NodalSmoothingGenericFiberRing R π) :=
  Ideal.map (Ideal.Quotient.mk _)
    (Ideal.span ({
      MvPolynomial.X (0 : Fin 2) -
        MvPolynomial.C (algebraMap R (FractionRing R) π),
      MvPolynomial.X (1 : Fin 2) -
        MvPolynomial.C (algebraMap R (FractionRing R) π)
    } : Set (MvPolynomial (Fin 2) (FractionRing R))) )

abbrev chapter06NodalSmoothingSpecialFiberField
    (R : Type u) [CommRing R] [IsLocalRing R] :=
  IsLocalRing.ResidueField R

abbrev chapter06NodalSmoothingSpecialFiberRing
    (R : Type u) [CommRing R] [IsLocalRing R] :=
  MvPolynomial (Fin 2) (chapter06NodalSmoothingSpecialFiberField R) ⧸
    Ideal.span ({
      MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)
    } : Set (MvPolynomial (Fin 2) (chapter06NodalSmoothingSpecialFiberField R)))

def chapter06NodalSmoothingSpecialFiberScheme
    (R : Type u) [CommRing R] [IsLocalRing R] : Scheme :=
  Spec (.of (chapter06NodalSmoothingSpecialFiberRing R))

structure Chapter06NodalSmoothingBoundaryProfile
    (R : Type u) [CommRing R] [IsLocalRing R] [IsDomain R] (π : R) where
  generic_fiber_smooth :
    SmoothOfRelativeDimension 1 (chapter06NodalSmoothingGenericFiberMap R π)
  generic_section_is_principal :
    ∃ a : chapter06NodalSmoothingGenericFiberRing R π,
      chapter06NodalSmoothingGenericFiberSectionIdeal R π =
        Ideal.span ({a} : Set (chapter06NodalSmoothingGenericFiberRing R π))
  special_fiber_nodal :
    chapter01NodalScheme (chapter06NodalSmoothingSpecialFiberScheme R)
  section_through_node :
    Ideal.map (chapter06NodalSmoothingSectionMap R π)
        (chapter06NodalSmoothingNodeIdeal R π) ≤
      IsLocalRing.maximalIdeal R
  section_height_one :
    (chapter06NodalSmoothingSectionIdeal R π).height = 1
  relation_has_no_linear_term :
    MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) -
        MvPolynomial.C (π ^ 2) ∈
      (Ideal.span ({
        MvPolynomial.X (0 : Fin 2),
        MvPolynomial.X (1 : Fin 2),
        MvPolynomial.C π
      } : Set (chapter06NodalSmoothingPolynomialRing R)) :
        Ideal (chapter06NodalSmoothingPolynomialRing R)) ^ 2

theorem chapter06_nodal_smoothing_boundary_profile_exists
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsDiscreteValuationRing R] (π : R)
    (hπ : Ideal.span ({π} : Set R) = IsLocalRing.maximalIdeal R) :
    Nonempty (Chapter06NodalSmoothingBoundaryProfile R π) := by
  sorry

theorem chapter06_nodal_smoothing_section_is_not_globally_principal
    (R : Type u) [CommRing R] [IsLocalRing R] [IsDomain R] (π : R)
    (P : Chapter06NodalSmoothingBoundaryProfile R π) :
    ¬ ∃ a : chapter06NodalSmoothingTotalRing R π,
      chapter06NodalSmoothingSectionIdeal R π = Ideal.span ({a} : Set _) :=
by
  rintro ⟨a, ha⟩
  let k := chapter06NodalSmoothingSpecialFiberField R
  let B := chapter06NodalSmoothingSpecialFiberRing R
  let qR := Ideal.Quotient.mk (chapter06NodalSmoothingEquationIdeal R π)
  let qk := Ideal.Quotient.mk
    (Ideal.span ({
      MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)
    } : Set (MvPolynomial (Fin 2) k)))
  have hπ_node :
      π ∈ Ideal.map (chapter06NodalSmoothingSectionMap R π)
        (chapter06NodalSmoothingNodeIdeal R π) := by
    have hx :
        qR (MvPolynomial.X (0 : Fin 2)) ∈
          chapter06NodalSmoothingNodeIdeal R π := by
      apply Ideal.mem_map_of_mem
      exact Ideal.subset_span (by simp)
    have hx' := Ideal.mem_map_of_mem
      (chapter06NodalSmoothingSectionMap R π) hx
    simpa [qR, chapter06NodalSmoothingSectionMap,
      Ideal.Quotient.lift_mk] using hx'
  have hπmax : π ∈ IsLocalRing.maximalIdeal R :=
    P.section_through_node hπ_node
  have hπ0 : algebraMap R k π = 0 := by
    change algebraMap R (IsLocalRing.ResidueField R) π = 0
    rw [IsLocalRing.ResidueField.algebraMap_eq,
      IsLocalRing.residue_eq_zero_iff]
    exact hπmax
  let p : MvPolynomial (Fin 2) R →+* MvPolynomial (Fin 2) k :=
    MvPolynomial.eval₂Hom (MvPolynomial.C.comp (algebraMap R k))
      (fun i => MvPolynomial.X i)
  let F : chapter06NodalSmoothingTotalRing R π →+* B :=
    Ideal.Quotient.lift
      (chapter06NodalSmoothingEquationIdeal R π)
      (qk.comp p) (by
          have hEq :
              chapter06NodalSmoothingEquationIdeal R π ≤
                RingHom.ker (qk.comp p) := by
            refine Ideal.span_le.2 ?_
            intro z hz
            rcases Set.mem_singleton_iff.mp hz with rfl
            change (qk.comp p)
              (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) -
                MvPolynomial.C (π ^ 2)) = 0
            simp only [p, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C,
              RingHom.coe_comp, Function.comp_apply, map_sub, map_mul,
              map_pow, hπ0, map_zero]
            have hzero : (0 : B) ^ (2 : ℕ) = 0 := by simp
            rw [hzero, sub_zero]
            rw [← map_mul]
            rw [Ideal.Quotient.eq_zero_iff_mem]
            exact Ideal.subset_span (by simp)
          exact fun z hz => hEq hz)
  have hI_le_node :
      Ideal.map F (chapter06NodalSmoothingSectionIdeal R π) ≤
        chapter10NodeIdeal k := by
    rw [chapter06NodalSmoothingSectionIdeal, Ideal.map_map]
    apply Ideal.map_le_iff_le_comap.2
    refine Ideal.span_le.2 ?_
    intro z hz
    rcases hz with rfl | rfl
    · have hx :
          qk (MvPolynomial.X (0 : Fin 2)) ∈ chapter10NodeIdeal k := by
        apply Ideal.mem_map_of_mem
        exact Ideal.subset_span (by simp)
      simpa [F, p, qR, hπ0] using hx
    · have hy :
          qk (MvPolynomial.X (1 : Fin 2)) ∈ chapter10NodeIdeal k := by
        apply Ideal.mem_map_of_mem
        exact Ideal.subset_span (by simp)
      simpa [F, p, qR, hπ0] using hy
  have hnode_le_image :
      chapter10NodeIdeal k ≤ Ideal.span ({F a} : Set B) := by
    rw [chapter10NodeIdeal]
    apply Ideal.map_le_iff_le_comap.2
    refine Ideal.span_le.2 ?_
    intro z hz
    rcases hz with rfl | rfl
    · have hx :
          qR (MvPolynomial.X (0 : Fin 2) -
            MvPolynomial.C π) ∈
            chapter06NodalSmoothingSectionIdeal R π := by
          apply Ideal.mem_map_of_mem
          exact Ideal.subset_span (by simp)
      have hx' := Ideal.mem_map_of_mem F hx
      rw [ha] at hx'
      simpa [F, p, qR, hπ0, Ideal.Quotient.eq_zero_iff_mem,
        Ideal.map_span] using hx'
    · have hy :
          qR (MvPolynomial.X (1 : Fin 2) -
            MvPolynomial.C π) ∈
            chapter06NodalSmoothingSectionIdeal R π := by
          apply Ideal.mem_map_of_mem
          exact Ideal.subset_span (by simp)
      have hy' := Ideal.mem_map_of_mem F hy
      rw [ha] at hy'
      simpa [F, p, qR, hπ0, Ideal.Quotient.eq_zero_iff_mem,
        Ideal.map_span] using hy'
  have himage_le_node :
      Ideal.span ({F a} : Set B) ≤ chapter10NodeIdeal k := by
    have h := hI_le_node
    rw [ha] at h
    simpa [Ideal.map_span] using h
  exact chapter10_node_ideal_is_not_principal k ⟨F a,
    le_antisymm hnode_le_image himage_le_node⟩

theorem chapter06_nodal_smoothing_section_is_not_cartier
    (R : Type u) [CommRing R] [IsLocalRing R] [IsDomain R] (π : R)
    (P : Chapter06NodalSmoothingBoundaryProfile R π) :
    Chapter06NodalSmoothingSectionCartierObstruction R π :=
by
  sorry

theorem chapter06_nodal_smoothing_section_is_not_locally_cartier
    (R : Type u) [CommRing R] [IsLocalRing R] [IsDomain R] (π : R)
    (P : Chapter06NodalSmoothingBoundaryProfile R π) :
    Chapter06NodalSmoothingSectionCartierObstruction R π :=
  chapter06_nodal_smoothing_section_is_not_cartier R π P

def chapter06CartierLocusOmitsNodalLimit
    (R : Type u) [CommRing R] [IsLocalRing R] [IsDomain R] (π : R) : Prop :=
  (∃ a : chapter06NodalSmoothingGenericFiberRing R π,
      chapter06NodalSmoothingGenericFiberSectionIdeal R π =
        Ideal.span ({a} : Set (chapter06NodalSmoothingGenericFiberRing R π))) ∧
    Chapter06NodalSmoothingSectionCartierObstruction R π

theorem chapter06_cartier_locus_omits_nodal_limit
    (R : Type u) [CommRing R] [IsLocalRing R] [IsDomain R] (π : R)
    (P : Chapter06NodalSmoothingBoundaryProfile R π) :
    chapter06CartierLocusOmitsNodalLimit R π :=
  ⟨P.generic_section_is_principal,
    chapter06_nodal_smoothing_section_is_not_cartier R π P⟩

def chapter06NodalSmoothingRelativeCurve
    (R : Type u) [CommRing R] (π : R) :
    RelativeScheme (chapter06NodalSmoothingBaseScheme R) where
  carrier := chapter06NodalSmoothingTotalScheme R π
  structuralMap := chapter06NodalSmoothingFamilyMap R π

def chapter06NodalSmoothingGenericTest
    (R : Type u) [CommRing R] [IsDomain R] :
    RelativeScheme (chapter06NodalSmoothingBaseScheme R) where
  carrier := Spec (.of (FractionRing R))
  structuralMap :=
    Scheme.Spec.map
      (CommRingCat.ofHom (algebraMap R (FractionRing R))).op

abbrev chapter06NodalSmoothingSpecialTest
    (R : Type u) [CommRing R] :
    RelativeScheme (chapter06NodalSmoothingBaseScheme R) :=
  RelativeScheme.base (chapter06NodalSmoothingBaseScheme R)

def chapter06NodalSmoothingGenericToSpecialTest
    (R : Type u) [CommRing R] [IsDomain R] :
    chapter06NodalSmoothingGenericTest R ⟶
      chapter06NodalSmoothingSpecialTest R where
  hom := (chapter06NodalSmoothingGenericTest R).structuralMap
  comm := by
    simp [chapter06NodalSmoothingSpecialTest, RelativeScheme.base]

noncomputable def chapter06NodalSmoothingGenericSectionIdealSheaf
    (R : Type u) [CommRing R] [IsDomain R] (π : R)
    (e : Chapter06RelativeDivisorAmbient
      (chapter06NodalSmoothingRelativeCurve R π)
        (chapter06NodalSmoothingGenericTest R) ≅
      Spec (.of (chapter06NodalSmoothingGenericFiberRing R π))) :
    (Chapter06RelativeDivisorAmbient
      (chapter06NodalSmoothingRelativeCurve R π)
        (chapter06NodalSmoothingGenericTest R)).IdealSheafData :=
  (Scheme.IdealSheafData.ofIdealTop
      ((chapter06NodalSmoothingGenericFiberSectionIdeal R π).map
        (Scheme.ΓSpecIso
          (.of (chapter06NodalSmoothingGenericFiberRing R π))).inv.hom)).comap e.hom

noncomputable def chapter06NodalSmoothingSectionIdealSheaf
    (R : Type u) [CommRing R] [IsDomain R] (π : R)
    (e : Chapter06RelativeDivisorAmbient
      (chapter06NodalSmoothingRelativeCurve R π)
        (chapter06NodalSmoothingSpecialTest R) ≅
      chapter06NodalSmoothingTotalScheme R π) :
    (Chapter06RelativeDivisorAmbient
      (chapter06NodalSmoothingRelativeCurve R π)
        (chapter06NodalSmoothingSpecialTest R)).IdealSheafData :=
  (Scheme.IdealSheafData.ofIdealTop
      ((chapter06NodalSmoothingSectionIdeal R π).map
        (Scheme.ΓSpecIso
          (.of (chapter06NodalSmoothingTotalRing R π))).inv.hom)).comap e.hom

def chapter06NodalSmoothingGenericFiberSectionMap
    (R : Type u) [CommRing R] [IsDomain R] (π : R) :
    chapter06NodalSmoothingGenericFiberRing R π →+* FractionRing R :=
  Ideal.Quotient.lift
    (Ideal.span ({
      MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) -
        MvPolynomial.C ((algebraMap R (FractionRing R) π) ^ 2)
    } : Set (MvPolynomial (Fin 2) (FractionRing R))))
    (MvPolynomial.eval₂Hom (RingHom.id _) (fun _ : Fin 2 =>
      algebraMap R (FractionRing R) π)) (by
      change Ideal.span ({
        MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) -
          MvPolynomial.C ((algebraMap R (FractionRing R) π) ^ 2)
      } : Set (MvPolynomial (Fin 2) (FractionRing R))) ≤
        RingHom.ker (MvPolynomial.eval₂Hom (RingHom.id _) (fun _ : Fin 2 =>
          algebraMap R (FractionRing R) π))
      refine Ideal.span_le.2 ?_
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      simp [pow_two])

def chapter06NodalSmoothingGenericFiberSection
    (R : Type u) [CommRing R] [IsDomain R] (π : R) :
    Spec (.of (FractionRing R)) ⟶
      Spec (.of (chapter06NodalSmoothingGenericFiberRing R π)) :=
  Scheme.Spec.map
    (CommRingCat.ofHom (chapter06NodalSmoothingGenericFiberSectionMap R π)).op

theorem chapter06_nodal_smoothing_generic_fiber_section_ideal_eq_kernel
    (R : Type u) [CommRing R] [IsDomain R] (π : R) :
    chapter06NodalSmoothingGenericFiberSectionIdeal R π =
      RingHom.ker (chapter06NodalSmoothingGenericFiberSectionMap R π) := by
  rw [chapter06NodalSmoothingGenericFiberSectionIdeal]
  symm
  have hker :
      RingHom.ker (chapter06NodalSmoothingGenericFiberSectionMap R π) =
        (RingHom.ker
          (MvPolynomial.eval₂Hom (RingHom.id (FractionRing R)) (fun _ : Fin 2 =>
            algebraMap R (FractionRing R) π))).map
          (Ideal.Quotient.mk _) := by
    unfold chapter06NodalSmoothingGenericFiberSectionMap
    apply Ideal.ker_quotient_lift
  rw [hker, chapter06_mvPolynomial_eval₂_kernel_fin_two]

def chapter06NodalSmoothingGenericSectionIsCartierPoint
    (R : Type u) [CommRing R] [IsLocalRing R] [IsDomain R] (π : R)
    {H : Chapter06LengthDHilbertSpaceData
      (chapter06NodalSmoothingRelativeCurve R π) 1}
    (L : Chapter06CartierDivisorOpenLocusData
      (chapter06NodalSmoothingRelativeCurve R π) 1 H)
    (e : Chapter06RelativeDivisorAmbient
      (chapter06NodalSmoothingRelativeCurve R π)
        (chapter06NodalSmoothingGenericTest R) ≅
      Spec (.of (chapter06NodalSmoothingGenericFiberRing R π)))
    (_e_over : e.hom ≫ chapter06NodalSmoothingGenericFiberMap R π =
      pullback.snd
        (chapter06NodalSmoothingRelativeCurve R π).structuralMap
        (chapter06NodalSmoothingGenericTest R).structuralMap)
    (s : Spec (.of (FractionRing R)) ⟶
      Spec (.of (chapter06NodalSmoothingGenericFiberRing R π)))
    (g : chapter06NodalSmoothingGenericTest R ⟶ L.locus) : Prop :=
  s = chapter06NodalSmoothingGenericFiberSection R π ∧
    e.hom ≫ chapter06NodalSmoothingGenericFiberMap R π =
      pullback.snd
        (chapter06NodalSmoothingRelativeCurve R π).structuralMap
        (chapter06NodalSmoothingGenericTest R).structuralMap ∧
    (∃ a : chapter06NodalSmoothingGenericFiberRing R π,
      chapter06NodalSmoothingGenericFiberSectionIdeal R π =
        Ideal.span ({a} : Set (chapter06NodalSmoothingGenericFiberRing R π))) ∧
      (H.represents (chapter06NodalSmoothingGenericTest R)
          (g ≫ L.inclusion)).ideal =
        chapter06NodalSmoothingGenericSectionIdealSheaf R π e

def chapter06NodalSmoothingSpecializationIsOmittedLimit
    (R : Type u) [CommRing R] [IsLocalRing R] [IsDomain R] (π : R)
    {H : Chapter06LengthDHilbertSpaceData
      (chapter06NodalSmoothingRelativeCurve R π) 1}
    (L : Chapter06CartierDivisorOpenLocusData
      (chapter06NodalSmoothingRelativeCurve R π) 1 H)
    (e : Chapter06RelativeDivisorAmbient
      (chapter06NodalSmoothingRelativeCurve R π)
        (chapter06NodalSmoothingSpecialTest R) ≅
      chapter06NodalSmoothingTotalScheme R π)
    (_e_over : e.hom ≫ chapter06NodalSmoothingFamilyMap R π =
      pullback.snd
        (chapter06NodalSmoothingRelativeCurve R π).structuralMap
        (chapter06NodalSmoothingSpecialTest R).structuralMap)
    (s : (chapter06NodalSmoothingSpecialTest R).carrier ⟶
      (chapter06NodalSmoothingRelativeCurve R π).carrier)
    (p : chapter06NodalSmoothingSpecialTest R ⟶ H.carrier) : Prop :=
  s = chapter06NodalSmoothingSection R π ∧
    e.hom ≫ chapter06NodalSmoothingFamilyMap R π =
      pullback.snd
        (chapter06NodalSmoothingRelativeCurve R π).structuralMap
        (chapter06NodalSmoothingSpecialTest R).structuralMap ∧
    Chapter06NodalSmoothingSectionCartierObstruction R π ∧
      (H.represents (chapter06NodalSmoothingSpecialTest R) p).ideal =
        chapter06NodalSmoothingSectionIdealSheaf R π e ∧
      ¬ ∃ g : chapter06NodalSmoothingSpecialTest R ⟶ L.locus,
        g ≫ L.inclusion = p

structure Chapter06NodalSmoothingHilbertBoundaryProfile
    (R : Type u) [CommRing R] [IsLocalRing R] [IsDomain R] (π : R)
    (H : Chapter06LengthDHilbertSpaceData
      (chapter06NodalSmoothingRelativeCurve R π) 1)
    (L : Chapter06CartierDivisorOpenLocusData
      (chapter06NodalSmoothingRelativeCurve R π) 1 H) where
  boundary : Chapter06NodalSmoothingBoundaryProfile R π
  generic_ambient_iso :
    Chapter06RelativeDivisorAmbient
      (chapter06NodalSmoothingRelativeCurve R π)
        (chapter06NodalSmoothingGenericTest R) ≅
      Spec (.of (chapter06NodalSmoothingGenericFiberRing R π))
  generic_ambient_iso_over :
    generic_ambient_iso.hom ≫ chapter06NodalSmoothingGenericFiberMap R π =
      pullback.snd
        (chapter06NodalSmoothingRelativeCurve R π).structuralMap
        (chapter06NodalSmoothingGenericTest R).structuralMap
  generic_section :
    Spec (.of (FractionRing R)) ⟶
      Spec (.of (chapter06NodalSmoothingGenericFiberRing R π))
  generic_point : chapter06NodalSmoothingGenericTest R ⟶ L.locus
  generic_point_is_cartier :
    chapter06NodalSmoothingGenericSectionIsCartierPoint R π L
      generic_ambient_iso generic_ambient_iso_over generic_section generic_point
  special_ambient_iso :
    Chapter06RelativeDivisorAmbient
      (chapter06NodalSmoothingRelativeCurve R π)
        (chapter06NodalSmoothingSpecialTest R) ≅
      chapter06NodalSmoothingTotalScheme R π
  special_ambient_iso_over :
    special_ambient_iso.hom ≫ chapter06NodalSmoothingFamilyMap R π =
      pullback.snd
        (chapter06NodalSmoothingRelativeCurve R π).structuralMap
        (chapter06NodalSmoothingSpecialTest R).structuralMap
  specialization_section :
    (chapter06NodalSmoothingSpecialTest R).carrier ⟶
      (chapter06NodalSmoothingRelativeCurve R π).carrier
  specialization_point : chapter06NodalSmoothingSpecialTest R ⟶ H.carrier
  specialization_is_omitted_limit :
    chapter06NodalSmoothingSpecializationIsOmittedLimit R π L
      special_ambient_iso special_ambient_iso_over specialization_section
        specialization_point
  generic_specialization_compatibility :
    chapter06NodalSmoothingGenericToSpecialTest R ≫ specialization_point =
      generic_point ≫ L.inclusion

theorem chapter06_nodal_smoothing_hilbert_boundary_profile_exists
    (R : Type u) [CommRing R] [IsLocalRing R] [IsDomain R] (π : R)
    {H : Chapter06LengthDHilbertSpaceData
      (chapter06NodalSmoothingRelativeCurve R π) 1}
    (L : Chapter06CartierDivisorOpenLocusData
      (chapter06NodalSmoothingRelativeCurve R π) 1 H)
    (P : Chapter06NodalSmoothingBoundaryProfile R π) :
    Nonempty (Chapter06NodalSmoothingHilbertBoundaryProfile R π H L) := by
  sorry

/- LOCAL_DEPENDENCY_GUESS (6.4): Book 8 exposes the finite-length Hilbert locus
   through projective-completion and test-scheme structures, while this chapter's
   relative-scheme interface has not yet been bridged to those canonical objects.
The bridge above records the coordinate profile against the representing
equivalences and the omitted specialization point. -/

/-!
The smooth locus is Mathlib's canonical open smooth locus.  Pulling it back
to `C ×_S T` gives the support condition used by marked-point and Abel-map
constructions on a nodal family.
-/

abbrev chapter06SmoothLocus {S : Scheme.{u}} (C : RelativeScheme S)
    [LocallyOfFinitePresentation C.structuralMap] : C.carrier.Opens :=
  C.structuralMap.smoothLocus

abbrev chapter06SmoothLocusInclusion {S : Scheme.{u}} (C : RelativeScheme S)
    [LocallyOfFinitePresentation C.structuralMap] :
    (chapter06SmoothLocus C).toScheme ⟶ C.carrier :=
  Scheme.Opens.ι _

def chapter06RelativeDivisorSupportedOnSmoothLocus
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [LocallyOfFinitePresentation C.structuralMap]
    (D : Chapter06RelativeEffectiveDivisor C T d) : Prop :=
  ∀ x, x ∈ D.divisor.ideal.support →
    x ∈ pullback.fst C.structuralMap T.structuralMap ⁻¹ᵁ chapter06SmoothLocus C

def chapter06MarkedSectionInSmoothLocus
    {S : Scheme.{u}} (C T : RelativeScheme S)
    [LocallyOfFinitePresentation C.structuralMap]
    (p : T ⟶ C) : Prop :=
  ∃ q : T.carrier ⟶ (chapter06SmoothLocus C).toScheme,
    q ≫ chapter06SmoothLocusInclusion C = p.hom

def chapter06FiniteFlatClosedFamilySupportedOnSmoothLocus
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [LocallyOfFinitePresentation C.structuralMap]
    (Z : Chapter06FiniteFlatClosedFamily C T d) : Prop :=
  ∀ x, x ∈ Z.ideal.support →
    x ∈ pullback.fst C.structuralMap T.structuralMap ⁻¹ᵁ chapter06SmoothLocus C

theorem chapter06_nodal_smooth_locus_finite_flat_family_is_cartier
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [LocallyOfFinitePresentation C.structuralMap]
    (hC : Chapter06NodalRelativeCurve C)
    (Z : Chapter06FiniteFlatClosedFamily C T d)
    (hsupport : chapter06FiniteFlatClosedFamilySupportedOnSmoothLocus C T d Z) :
    chapter06IsEffectiveCartierFamily Z := by
  sorry

theorem chapter06_symmetric_power_smooth_locus_points_are_cartier
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [Chapter06SmoothProjectiveRelativeCurve C]
    [LocallyOfFinitePresentation C.structuralMap]
    (f : T ⟶ Chapter06SymmetricPower C d) :
    (chapter06UniversalDivisorEquiv C T d f).divisor.ideal.IsEffectiveCartier := by
  exact (chapter06UniversalDivisorEquiv C T d f).divisor.isEffectiveCartier

theorem chapter06_symmetric_power_universal_divisor_is_supported_on_smooth_locus
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [Chapter06SmoothProjectiveRelativeCurve C]
    [LocallyOfFinitePresentation C.structuralMap]
    (f : T ⟶ Chapter06SymmetricPower C d) :
      chapter06RelativeDivisorSupportedOnSmoothLocus C T d
      (chapter06UniversalDivisorEquiv C T d f) := by
  intro x hx
  change (pullback.fst C.structuralMap T.structuralMap).base x ∈
    C.structuralMap.smoothLocus
  rw [@Scheme.Hom.smoothLocus_eq_top _ _ C.structuralMap
    (@SmoothOfRelativeDimension.smooth 1 _ _ _
      (Chapter11SmoothQuasiProjectiveCurve.smooth (C := C)))]
  trivial

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter06
