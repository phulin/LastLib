import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08.Section01TheLocalResidue

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry BigOperators

noncomputable section

universe u v

/-! ### 8.3 Global residue theorem -/

variable (k : Type u) [Field k]

structure Chapter08GlobalResidueFamily
    (C : Chapter08ProperGeometricallyConnectedCurve k)
    [Algebra k C.carrier.functionField] where
  finiteSupport :
    ∀ η : Chapter08RationalDifferentials k C.carrier,
      Set.Finite {x : Chapter08ClosedPoint C.carrier |
        chapter08CanonicalResidueAt k C.toChapter08SmoothIntegralCurve x η ≠ 0}

/- The global interface is also consumed by the later Cech-duality chapter,
   which needs the local residue system itself rather than only its canonical
   evaluation.  Exposing the canonical choice here keeps both descriptions
   definitionally aligned. -/
noncomputable def Chapter08GlobalResidueFamily.localResidue
    {C : Chapter08ProperGeometricallyConnectedCurve k}
    [Algebra k C.carrier.functionField]
    (_G : Chapter08GlobalResidueFamily k C)
    (x : Chapter08ClosedPoint C.carrier) :
    Chapter08LocalResidueSystem k C.toChapter08SmoothIntegralCurve x :=
  chapter08CanonicalLocalResidueSystem k C.toChapter08SmoothIntegralCurve x

theorem chapter08_global_residue_family_exists
    (C : Chapter08ProperGeometricallyConnectedCurve k)
    [Algebra k C.carrier.functionField] :
    Nonempty (Chapter08GlobalResidueFamily k C) := by
  sorry

def chapter08_global_residue_support
    {C : Chapter08ProperGeometricallyConnectedCurve k}
    [Algebra k C.carrier.functionField]
    (_G : Chapter08GlobalResidueFamily k C) (η : Chapter08RationalDifferentials k C.carrier) :
    Set (Chapter08ClosedPoint C.carrier) :=
  {x | chapter08CanonicalResidueAt k C.toChapter08SmoothIntegralCurve x η ≠ 0}

theorem chapter08_global_residue_support_finite
    {C : Chapter08ProperGeometricallyConnectedCurve k}
    [Algebra k C.carrier.functionField]
    (G : Chapter08GlobalResidueFamily k C)
    (η : Chapter08RationalDifferentials k C.carrier) :
    (chapter08_global_residue_support k G η).Finite := by
  sorry

theorem chapter08_residue_zero_off_global_support
    {C : Chapter08ProperGeometricallyConnectedCurve k}
    [Algebra k C.carrier.functionField]
    (G : Chapter08GlobalResidueFamily k C)
    (η : Chapter08RationalDifferentials k C.carrier)
    {x : Chapter08ClosedPoint C.carrier}
    (hx : x ∉ chapter08_global_residue_support k G η) :
    chapter08CanonicalResidueAt k C.toChapter08SmoothIntegralCurve x η = 0 := by
  sorry

noncomputable def chapter08_residue_sum
    {C : Chapter08ProperGeometricallyConnectedCurve k}
    [Algebra k C.carrier.functionField]
    (G : Chapter08GlobalResidueFamily k C)
    (η : Chapter08RationalDifferentials k C.carrier) : k :=
  Finset.sum (chapter08_global_residue_support_finite k G η).toFinset
    (fun x => chapter08CanonicalResidueAt k C.toChapter08SmoothIntegralCurve x η)

theorem chapter08_global_residue_theorem
    {C : Chapter08ProperGeometricallyConnectedCurve k}
    [Algebra k C.carrier.functionField]
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
    (F : Type v) [Field F] [Algebra k F] where
  coordinate : F
  coordinate_is_nonzero : coordinate ≠ 0
  differential : Ω[F⁄k]
  differential_eq_dt_over_t : differential = chapter08DtOverT k coordinate
  residueAtZero : Ω[F⁄k] →ₗ[k] k
  residueAtInfinity : Ω[F⁄k] →ₗ[k] k
  zero_residue : residueAtZero differential = 1
  infinity_residue : residueAtInfinity differential = -1

theorem chapter08_dt_over_t_boundary_sum
    {F : Type v} [Field F] [Algebra k F]
    (e : Chapter08PuncturedLineBoundaryResidues k F) :
    e.residueAtZero e.differential + e.residueAtInfinity e.differential = 0 := by
  rw [e.zero_residue, e.infinity_residue]
  simp

theorem chapter08_dt_over_t_has_nonzero_omitted_residue
    {F : Type v} [Field F] [Algebra k F]
    (e : Chapter08PuncturedLineBoundaryResidues k F) :
    e.residueAtZero e.differential ≠ 0 := by
  rw [e.zero_residue]
  exact one_ne_zero

/- Local dependency guess: the earlier scheme API has no chapter-facing
construction of the projective-line morphism attached to a separating
element, so the induced-map compatibility is kept explicit. -/
structure Chapter08SeparatingElement
    (C : Chapter08ProperGeometricallyConnectedCurve k)
    [Algebra k C.carrier.functionField] where
  element : C.carrier.functionField
  inducedFiniteMap : Chapter08FiniteMapToProjectiveLine k C
  element_eq_inducedMap_element : inducedFiniteMap.element = element
  coordinate : inducedFiniteMap.functionFieldMap.functionField
  coordinate_eq_element :
    inducedFiniteMap.functionFieldMap.map coordinate = element

theorem chapter08_separating_element_gives_finite_generically_separable_map
    (C : Chapter08ProperGeometricallyConnectedCurve k)
    [Algebra k C.carrier.functionField] :
    Nonempty (Chapter08SeparatingElement k C) := by
  sorry

/-! Prescribed principal parts and the one obstruction detected by residues. -/

structure Chapter08LocalPolarPart
    {C : Chapter08ProperGeometricallyConnectedCurve k}
    [Algebra k C.carrier.functionField]
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
    [Algebra k C.carrier.functionField]
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
    [Algebra k C.carrier.functionField]
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
    [Algebra k C.carrier.functionField]
    (G : Chapter08GlobalResidueFamily k C)
    (P : Chapter08PrescribedPolarParts k C G)
    {η : Chapter08RationalDifferentials k C.carrier}
    (hη : Chapter08PrescribedPolarParts.realizes k P η) :
    P.totalResidue = 0 := by
  sorry

/- This is the later-duality lifting interface used only for the converse;
the residue theorem above supplies the necessary direction independently. -/
structure Chapter08PolarPartLiftingInterface
    {C : Chapter08ProperGeometricallyConnectedCurve k}
    [Algebra k C.carrier.functionField]
    (G : Chapter08GlobalResidueFamily k C) where
  lift : ∀ P : Chapter08PrescribedPolarParts k C G,
    P.totalResidue = 0 → ∃ η, Chapter08PrescribedPolarParts.realizes k P η

theorem chapter08_polar_parts_global_iff_zero_total_residue
    {C : Chapter08ProperGeometricallyConnectedCurve k}
    [Algebra k C.carrier.functionField]
    (G : Chapter08GlobalResidueFamily k C)
    (L : Chapter08PolarPartLiftingInterface k G)
    (P : Chapter08PrescribedPolarParts k C G) :
    (∃ η, Chapter08PrescribedPolarParts.realizes k P η) ↔ P.totalResidue = 0 := by
  sorry

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08
