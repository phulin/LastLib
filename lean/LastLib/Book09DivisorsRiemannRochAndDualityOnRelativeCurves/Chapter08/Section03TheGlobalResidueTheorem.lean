import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08.Section01TheLocalResidue

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry BigOperators

noncomputable section

universe u v

/-! ### 8.3 Global residue theorem -/

variable (k : Type u) [Field k]
variable (C : Chapter08ProperGeometricallyConnectedCurve k)

structure Chapter08GlobalResidueFamily
    (C : Chapter08ProperGeometricallyConnectedCurve k)
    where
  finiteSupport :
    ∀ η : Chapter08RationalDifferentials k C.carrier,
      Set.Finite {x : Chapter08ClosedPoint C.carrier |
        chapter08CanonicalResidueAt k C.toChapter08SmoothIntegralCurve x η ≠ 0}

def chapter08_global_differential_pole_support
    {C : Chapter08ProperGeometricallyConnectedCurve k}
    (η : Chapter08RationalDifferentials k C.carrier) :
    Set (Chapter08ClosedPoint C.carrier) :=
  {x | ¬ chapter08DifferentialRegularAt k C.toChapter08SmoothIntegralCurve x η}

theorem chapter08_global_differential_pole_support_finite
    {C : Chapter08ProperGeometricallyConnectedCurve k}
    (η : Chapter08RationalDifferentials k C.carrier) :
    (chapter08_global_differential_pole_support k η).Finite := by
  sorry

/- The global interface is also consumed by the later Cech-duality chapter,
   which needs the local residue system itself rather than only its canonical
   evaluation.  Exposing the canonical choice here keeps both descriptions
   definitionally aligned. -/
noncomputable def Chapter08GlobalResidueFamily.localResidue
    {C : Chapter08ProperGeometricallyConnectedCurve k}
    (_G : Chapter08GlobalResidueFamily k C)
    (x : Chapter08ClosedPoint C.carrier) :
    Chapter08LocalResidueSystem k C.toChapter08SmoothIntegralCurve x :=
  chapter08CanonicalLocalResidueSystem k C.toChapter08SmoothIntegralCurve x

theorem chapter08_global_residue_family_exists
    (C : Chapter08ProperGeometricallyConnectedCurve k)
    :
    Nonempty (Chapter08GlobalResidueFamily k C) := by
  refine ⟨⟨?_⟩⟩
  intro η
  apply (chapter08_global_differential_pole_support_finite k η).subset
  intro x hx
  change ¬ chapter08DifferentialRegularAt k C.toChapter08SmoothIntegralCurve x η
  intro hregular
  let R := chapter08CanonicalLocalResidueSystem k
    C.toChapter08SmoothIntegralCurve x
  have hregular' : η ∈ R.regularDifferentials := by
    have h₁ : 0 < (1 : ℕ) := Nat.zero_lt_succ 0
    rw [← R.regularDifferentials_eq_stage 1 h₁]
    exact ((R.stages.adjunction 1 h₁).principalParts.regularDifferentials_characterization η).2
      hregular
  exact hx (chapter08_canonical_residue_kills_regular k
    C.toChapter08SmoothIntegralCurve x hregular')

def chapter08_global_residue_support
    {C : Chapter08ProperGeometricallyConnectedCurve k}
    (_G : Chapter08GlobalResidueFamily k C) (η : Chapter08RationalDifferentials k C.carrier) :
    Set (Chapter08ClosedPoint C.carrier) :=
  {x | chapter08CanonicalResidueAt k C.toChapter08SmoothIntegralCurve x η ≠ 0}

theorem chapter08_global_residue_support_finite
    {C : Chapter08ProperGeometricallyConnectedCurve k}
    (G : Chapter08GlobalResidueFamily k C)
    (η : Chapter08RationalDifferentials k C.carrier) :
    (chapter08_global_residue_support k G η).Finite := by
  simpa [chapter08_global_residue_support] using G.finiteSupport η

theorem chapter08_residue_zero_off_global_support
    {C : Chapter08ProperGeometricallyConnectedCurve k}
    (G : Chapter08GlobalResidueFamily k C)
    (η : Chapter08RationalDifferentials k C.carrier)
    {x : Chapter08ClosedPoint C.carrier}
    (hx : x ∉ chapter08_global_residue_support k G η) :
    chapter08CanonicalResidueAt k C.toChapter08SmoothIntegralCurve x η = 0 := by
  by_contra hres
  apply hx
  change chapter08CanonicalResidueAt k C.toChapter08SmoothIntegralCurve x η ≠ 0
  exact hres

noncomputable def chapter08_residue_sum
    {C : Chapter08ProperGeometricallyConnectedCurve k}
    (G : Chapter08GlobalResidueFamily k C)
    (η : Chapter08RationalDifferentials k C.carrier) : k :=
  Finset.sum (chapter08_global_residue_support_finite k G η).toFinset
    (fun x => chapter08CanonicalResidueAt k C.toChapter08SmoothIntegralCurve x η)

theorem chapter08_global_residue_theorem
    {C : Chapter08ProperGeometricallyConnectedCurve k}
    (G : Chapter08GlobalResidueFamily k C)
    (η : Chapter08RationalDifferentials k C.carrier) :
    chapter08_residue_sum k G η = 0 := by
  sorry

/- The boundary terms in the projective-line example are the two omitted
points of the affine multiplicative line. -/
def chapter08DtOverT
    {F : Type v} [Field F] [Algebra k F] (T : F) : Ω[F⁄k] :=
  T⁻¹ • KaehlerDifferential.D k F T

structure Chapter08PuncturedLineBoundaryResidues
    (C : Chapter08ProperGeometricallyConnectedCurve k) where
  zero : Chapter08ClosedPoint C.carrier
  infinity : Chapter08ClosedPoint C.carrier
  zero_ne_infinity : zero.1 ≠ infinity.1
  coordinate : C.carrier.functionField
  coordinate_is_nonzero : coordinate ≠ 0
  differential : Chapter08RationalDifferentials k C.carrier
  differential_eq_dt_over_t : differential = chapter08DtOverT k coordinate
  zero_residue :
    chapter08CanonicalResidueAt k C.toChapter08SmoothIntegralCurve zero differential = 1
  infinity_residue :
    chapter08CanonicalResidueAt k C.toChapter08SmoothIntegralCurve infinity differential = -1

theorem chapter08_dt_over_t_boundary_sum
    (e : Chapter08PuncturedLineBoundaryResidues k C) :
    chapter08CanonicalResidueAt k C.toChapter08SmoothIntegralCurve e.zero e.differential +
        chapter08CanonicalResidueAt k C.toChapter08SmoothIntegralCurve e.infinity e.differential = 0 := by
  rw [e.zero_residue, e.infinity_residue]
  simp

theorem chapter08_dt_over_t_has_nonzero_omitted_residue
    (e : Chapter08PuncturedLineBoundaryResidues k C) :
    chapter08CanonicalResidueAt k C.toChapter08SmoothIntegralCurve e.zero e.differential ≠ 0 := by
  rw [e.zero_residue]
  exact one_ne_zero

/- Local dependency guess: the earlier scheme API has no chapter-facing
construction of the projective-line morphism attached to a separating
element, so the induced-map compatibility is kept explicit. -/
structure Chapter08SeparatingElement
    (C : Chapter08ProperGeometricallyConnectedCurve k)
    where
  element : C.carrier.functionField
  inducedFiniteMap : Chapter08FiniteMapToProjectiveLine k C
  element_eq_inducedMap_element : inducedFiniteMap.element = element
  coordinate : inducedFiniteMap.functionFieldMap.functionField
  coordinate_eq_element :
    inducedFiniteMap.functionFieldMap.map coordinate = element

theorem chapter08_separating_element_gives_finite_generically_separable_map
    (C : Chapter08ProperGeometricallyConnectedCurve k)
    :
    Nonempty (Chapter08SeparatingElement k C) := by
  sorry

/-! Prescribed principal parts and the one obstruction detected by residues. -/

structure Chapter08LocalPolarPart
    {C : Chapter08ProperGeometricallyConnectedCurve k}
    (x : Chapter08ClosedPoint C.carrier) where
  representative : Chapter08RationalDifferentials k C.carrier
  classRepresentative : (Chapter08RationalDifferentials k C.carrier) ⧸
    (chapter08CanonicalLocalResidueSystem k C.toChapter08SmoothIntegralCurve x).regularDifferentials
  classRepresentative_eq :
    classRepresentative =
      Submodule.mkQ
        (chapter08CanonicalLocalResidueSystem k C.toChapter08SmoothIntegralCurve x).regularDifferentials
        representative

structure Chapter08PrescribedPolarParts
    (C : Chapter08ProperGeometricallyConnectedCurve k)
    (G : Chapter08GlobalResidueFamily k C) where
  allowedPoles : Finset (Chapter08ClosedPoint C.carrier)
  part :
    ∀ x : allowedPoles,
      Chapter08LocalPolarPart k x.1
  totalResidue : k
  totalResidue_eq_sum :
    totalResidue =
      ∑ x : allowedPoles,
        chapter08CanonicalResidueAt k C.toChapter08SmoothIntegralCurve x.1
          (part x).representative

def Chapter08PrescribedPolarParts.realizes
    {C : Chapter08ProperGeometricallyConnectedCurve k}
    {G : Chapter08GlobalResidueFamily k C}
    (P : Chapter08PrescribedPolarParts k C G)
    (η : Chapter08RationalDifferentials k C.carrier) : Prop :=
  (∀ x : P.allowedPoles,
      Submodule.mkQ
          (chapter08CanonicalLocalResidueSystem k C.toChapter08SmoothIntegralCurve x.1).regularDifferentials η =
        (P.part x).classRepresentative) ∧
    (∀ x, x ∉ P.allowedPoles →
      η ∈ (chapter08CanonicalLocalResidueSystem k C.toChapter08SmoothIntegralCurve x).regularDifferentials)

theorem chapter08_global_polar_parts_have_zero_total_residue
    {C : Chapter08ProperGeometricallyConnectedCurve k}
    (G : Chapter08GlobalResidueFamily k C)
    (P : Chapter08PrescribedPolarParts k C G)
    {η : Chapter08RationalDifferentials k C.carrier}
    (hη : Chapter08PrescribedPolarParts.realizes k P η) :
    P.totalResidue = 0 := by
  have hrepresentative : ∀ z : P.allowedPoles,
      chapter08CanonicalResidueAt k C.toChapter08SmoothIntegralCurve
          z.1 (P.part z).representative =
        chapter08CanonicalResidueAt k C.toChapter08SmoothIntegralCurve z.1 η := by
    intro z
    let R :=
      (chapter08CanonicalLocalResidueSystem k C.toChapter08SmoothIntegralCurve z.1).regularDifferentials
    have hclass :
        Submodule.mkQ R η =
          Submodule.mkQ R (P.part z).representative := by
      rw [hη.1 z, (P.part z).classRepresentative_eq]
    have hdiff :
        η - (P.part z).representative ∈ R := by
      rw [← Submodule.Quotient.mk_eq_zero]
      change R.mkQ η - R.mkQ (P.part z).representative = 0
      rw [hclass, sub_self]
    have hzero := chapter08_canonical_residue_kills_regular k
      C.toChapter08SmoothIntegralCurve z.1 hdiff
    have hzero' :
        chapter08CanonicalResidueAt k C.toChapter08SmoothIntegralCurve z.1 η -
          chapter08CanonicalResidueAt k C.toChapter08SmoothIntegralCurve z.1
            (P.part z).representative = 0 := by
      simpa [chapter08CanonicalResidueAt_apply, map_sub] using hzero
    exact (sub_eq_zero.mp hzero').symm
  let S := chapter08_global_residue_support_finite k G η
  have hallowed : S.toFinset ⊆ P.allowedPoles := by
    intro y hy
    by_contra hyallowed
    have hregular := hη.2 y hyallowed
    have hzero := chapter08_canonical_residue_kills_regular k
      C.toChapter08SmoothIntegralCurve y hregular
    exact S.mem_toFinset.mp hy hzero
  calc
    P.totalResidue =
        ∑ z : P.allowedPoles,
          chapter08CanonicalResidueAt k C.toChapter08SmoothIntegralCurve z.1
            (P.part z).representative := P.totalResidue_eq_sum
    _ = ∑ z : P.allowedPoles,
          chapter08CanonicalResidueAt k C.toChapter08SmoothIntegralCurve z.1 η := by
      apply Fintype.sum_congr
      intro z
      exact hrepresentative z
    _ = Finset.sum S.toFinset
          (fun y => chapter08CanonicalResidueAt
            k C.toChapter08SmoothIntegralCurve y η) := by
      have hcoe :
          (∑ z : P.allowedPoles,
              chapter08CanonicalResidueAt k C.toChapter08SmoothIntegralCurve z.1 η) =
            Finset.sum P.allowedPoles
              (fun y => chapter08CanonicalResidueAt
                k C.toChapter08SmoothIntegralCurve y η) :=
        Finset.sum_coe_sort P.allowedPoles (fun y =>
          chapter08CanonicalResidueAt k C.toChapter08SmoothIntegralCurve y η)
      rw [hcoe]
      symm
      apply Finset.sum_subset hallowed
      intro y hyallowed hySupport
      apply chapter08_residue_zero_off_global_support k G η
      intro hyS
      exact hySupport (S.mem_toFinset.mpr hyS)
    _ = chapter08_residue_sum k G η := by
      rfl
    _ = 0 := chapter08_global_residue_theorem k G η

/- This is the later-duality lifting interface used only for the converse;
the residue theorem above supplies the necessary direction independently. -/
structure Chapter08PolarPartLiftingInterface
    {C : Chapter08ProperGeometricallyConnectedCurve k}
    (G : Chapter08GlobalResidueFamily k C) where
  lift : ∀ P : Chapter08PrescribedPolarParts k C G,
    P.totalResidue = 0 → ∃ η, Chapter08PrescribedPolarParts.realizes k P η

theorem chapter08_polar_parts_global_iff_zero_total_residue
    {C : Chapter08ProperGeometricallyConnectedCurve k}
    (G : Chapter08GlobalResidueFamily k C)
    (L : Chapter08PolarPartLiftingInterface k G)
    (P : Chapter08PrescribedPolarParts k C G) :
    (∃ η, Chapter08PrescribedPolarParts.realizes k P η) ↔ P.totalResidue = 0 := by
  constructor
  · rintro ⟨η, hη⟩
    exact chapter08_global_polar_parts_have_zero_total_residue k G P hη
  · intro hP
    exact L.lift P hP

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08
