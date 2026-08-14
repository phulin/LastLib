import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08.Section02IndependenceOfParameter

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u v

/-! ### 8.3 Global residue theorem -/

variable (k : Type u) [Field k]

structure Chapter08GlobalResidueFamily
    (C : Chapter08ProperGeometricallyConnectedCurve k)
    [Algebra k C.carrier.functionField] where
  localResidue :
    ∀ x : Chapter08ClosedPoint C.carrier,
      Chapter08LocalResidueSystem k C.toChapter08SmoothIntegralCurve x
  finiteSupport :
    ∀ η : Chapter08RationalDifferentials k C.carrier,
      Set.Finite {x : Chapter08ClosedPoint C.carrier |
        chapter08ResidueAt k C.toChapter08SmoothIntegralCurve x
          (localResidue x) η ≠ 0}

def chapter08_global_residue_support
    {C : Chapter08ProperGeometricallyConnectedCurve k}
    [Algebra k C.carrier.functionField]
    (G : Chapter08GlobalResidueFamily k C) (η : Chapter08RationalDifferentials k C.carrier) :
    Set (Chapter08ClosedPoint C.carrier) :=
  {x | chapter08ResidueAt k C.toChapter08SmoothIntegralCurve x
    (G.localResidue x) η ≠ 0}

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
    chapter08ResidueAt k C.toChapter08SmoothIntegralCurve x
      (G.localResidue x) η = 0 := by
  sorry

noncomputable def chapter08_residue_sum
    {C : Chapter08ProperGeometricallyConnectedCurve k}
    [Algebra k C.carrier.functionField]
    (G : Chapter08GlobalResidueFamily k C)
    (η : Chapter08RationalDifferentials k C.carrier) : k :=
  ∑ x in (chapter08_global_residue_support k G η).toFinset,
    chapter08ResidueAt k C.toChapter08SmoothIntegralCurve x
      (G.localResidue x) η

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
  differential : Ω[F⁄k]
  differential_eq_dt_over_t : differential = chapter08DtOverT k coordinate
  residueAtZero : k
  residueAtInfinity : k
  zero_residue : residueAtZero = 1
  infinity_residue : residueAtInfinity = -1

theorem chapter08_dt_over_t_boundary_sum
    {F : Type v} [Field F] [Algebra k F]
    (e : Chapter08PuncturedLineBoundaryResidues k F) :
    e.residueAtZero + e.residueAtInfinity = 0 := by
  sorry

theorem chapter08_dt_over_t_has_nonzero_omitted_residue
    {F : Type v} [Field F] [Algebra k F]
    (e : Chapter08PuncturedLineBoundaryResidues k F) :
    e.residueAtZero ≠ 0 := by
  sorry

/- Local dependency guess: the earlier scheme API has no chapter-facing
construction of the projective-line morphism attached to a separating
element, so the induced-map compatibility is kept explicit. -/
structure Chapter08SeparatingElement
    (C : Chapter08ProperGeometricallyConnectedCurve k)
    [Algebra k C.carrier.functionField] where
  element : C.carrier.functionField
  inducedFiniteMap : Chapter08FiniteMapOfProperCurves k
  element_realizes_inducedMap : Prop

theorem chapter08_separating_element_gives_finite_generically_separable_map
    (C : Chapter08ProperGeometricallyConnectedCurve k)
    [Algebra k C.carrier.functionField] :
    Nonempty (Chapter08SeparatingElement k C) := by
  sorry

/-! Prescribed principal parts and the one obstruction detected by residues. -/

structure Chapter08LocalPolarPart
    {C : Chapter08ProperGeometricallyConnectedCurve k}
    [Algebra k C.carrier.functionField]
    (R : Chapter08LocalResidueSystem k C.toChapter08SmoothIntegralCurve x) where
  representative : Chapter08RationalDifferentials k C.carrier
  classRepresentative : Submodule.Quotient R.regularDifferentials
  classRepresentative_eq :
    classRepresentative = Submodule.Quotient.mkQ R.regularDifferentials representative

structure Chapter08PrescribedPolarParts
    (C : Chapter08ProperGeometricallyConnectedCurve k)
    [Algebra k C.carrier.functionField]
    (G : Chapter08GlobalResidueFamily k C) where
  allowedPoles : Finset (Chapter08ClosedPoint C.carrier)
  part :
    ∀ x : allowedPoles,
      Chapter08LocalPolarPart k (G.localResidue x.1)
  totalResidue : k
  totalResidue_eq_sum :
    totalResidue =
      ∑ x : allowedPoles,
        chapter08ResidueAt k C.toChapter08SmoothIntegralCurve x.1
          (G.localResidue x.1) (part x).representative

def Chapter08PrescribedPolarParts.realizes
    {C : Chapter08ProperGeometricallyConnectedCurve k}
    [Algebra k C.carrier.functionField]
    {G : Chapter08GlobalResidueFamily k C}
    (P : Chapter08PrescribedPolarParts k C G)
    (η : Chapter08RationalDifferentials k C.carrier) : Prop :=
  (∀ x : P.allowedPoles,
      Submodule.Quotient.mkQ (G.localResidue x.1).regularDifferentials η =
        (P.part x).classRepresentative) ∧
    (∀ x, x ∉ P.allowedPoles → η ∈ (G.localResidue x).regularDifferentials)

theorem chapter08_global_polar_parts_have_zero_total_residue
    {C : Chapter08ProperGeometricallyConnectedCurve k}
    [Algebra k C.carrier.functionField]
    (G : Chapter08GlobalResidueFamily k C)
    (P : Chapter08PrescribedPolarParts k C G)
    {η : Chapter08RationalDifferentials k C.carrier}
    (hη : P.realizes η) :
    P.totalResidue = 0 := by
  sorry

/- This is the later-duality lifting interface used only for the converse;
the residue theorem above supplies the necessary direction independently. -/
structure Chapter08PolarPartLiftingInterface
    {C : Chapter08ProperGeometricallyConnectedCurve k}
    [Algebra k C.carrier.functionField]
    (G : Chapter08GlobalResidueFamily k C) where
  lift : ∀ P : Chapter08PrescribedPolarParts k C G,
    P.totalResidue = 0 → ∃ η, P.realizes η

theorem chapter08_polar_parts_global_iff_zero_total_residue
    {C : Chapter08ProperGeometricallyConnectedCurve k}
    [Algebra k C.carrier.functionField]
    (G : Chapter08GlobalResidueFamily k C)
    (L : Chapter08PolarPartLiftingInterface k G)
    (P : Chapter08PrescribedPolarParts k C G) :
    (∃ η, P.realizes η) ↔ P.totalResidue = 0 := by
  sorry

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08
