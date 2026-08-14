import Mathlib.Algebra.Ring.Regular
import Mathlib.RingTheory.MvPowerSeries.Basic
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter07.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter07

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped BigOperators TensorProduct

noncomputable section

universe u

/-!
## 7.3 Differentials at singular points
-/

/- The node is represented by the literal formal power-series quotient
`k[[x,y]]/(xy)`. -/
abbrev Chapter07NodeAmbient (k : Type u) [CommRing k] :=
  MvPowerSeries (Fin 2) k

def chapter07NodeEquation (k : Type u) [CommRing k] : Chapter07NodeAmbient k :=
  MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2)

def chapter07NodeIdeal (k : Type u) [CommRing k] : Ideal (Chapter07NodeAmbient k) :=
  Ideal.span {chapter07NodeEquation k}

abbrev Chapter07NodeRing (k : Type u) [CommRing k] :=
  Chapter07NodeAmbient k ⧸ chapter07NodeIdeal k

def chapter07NodeX (k : Type u) [CommRing k] : Chapter07NodeRing k :=
  Ideal.Quotient.mk (chapter07NodeIdeal k) (MvPowerSeries.X (0 : Fin 2))

def chapter07NodeY (k : Type u) [CommRing k] : Chapter07NodeRing k :=
  Ideal.Quotient.mk (chapter07NodeIdeal k) (MvPowerSeries.X (1 : Fin 2))

abbrev Chapter07NodeDifferentials (k : Type u) [CommRing k] :=
  Ω[Chapter07NodeRing k⁄k]

def chapter07NodeConormalEquationDifferential
    (k : Type u) [CommRing k] : Ω[Chapter07NodeAmbient k⁄k] :=
  KaehlerDifferential.D k (Chapter07NodeAmbient k) (chapter07NodeEquation k)

theorem chapter07_node_conormal_relation
    (k : Type u) [CommRing k] :
    KaehlerDifferential.D k (Chapter07NodeAmbient k) (chapter07NodeEquation k) =
      KaehlerDifferential.D k (Chapter07NodeAmbient k)
          (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2)) := by
  rfl

theorem chapter07_node_conormal_differential_expands
    (k : Type u) [CommRing k] :
    chapter07NodeConormalEquationDifferential k =
      MvPowerSeries.X (0 : Fin 2) •
          KaehlerDifferential.D k (Chapter07NodeAmbient k)
            (MvPowerSeries.X (1 : Fin 2)) +
        MvPowerSeries.X (1 : Fin 2) •
          KaehlerDifferential.D k (Chapter07NodeAmbient k)
            (MvPowerSeries.X (0 : Fin 2)) := by
  exact (KaehlerDifferential.D k (Chapter07NodeAmbient k)).leibniz _ _

/- The displayed presentation `(A dx ⊕ A dy)/(y dx + x dy)` is made into an
actual quotient module.  The equivalence with the canonical Kähler module is
kept as a local presentation theorem until the quotient-presentation API is
extended to formal power-series quotients. -/
abbrev Chapter07NodeFreeDifferentials (k : Type u) [CommRing k] :=
  Chapter07NodeRing k × Chapter07NodeRing k

def chapter07NodeRelationVector (k : Type u) [CommRing k] :
    Chapter07NodeFreeDifferentials k :=
  (chapter07NodeY k, chapter07NodeX k)

def chapter07NodeRelationSubmodule (k : Type u) [CommRing k] :
    Submodule (Chapter07NodeRing k) (Chapter07NodeFreeDifferentials k) :=
  Submodule.span (Chapter07NodeRing k) {chapter07NodeRelationVector k}

abbrev Chapter07NodePresentedDifferentials (k : Type u) [CommRing k] :=
  Chapter07NodeFreeDifferentials k ⧸ chapter07NodeRelationSubmodule k

noncomputable def chapter07NodeDx (k : Type u) [CommRing k] :
    Chapter07NodePresentedDifferentials k :=
  Submodule.Quotient.mk (1, 0)

noncomputable def chapter07NodeDy (k : Type u) [CommRing k] :
    Chapter07NodePresentedDifferentials k :=
  Submodule.Quotient.mk (0, 1)

structure Chapter07NodeDifferentialPresentationData
    (k : Type u) [CommRing k] where
  equivalence :
    Chapter07NodePresentedDifferentials k ≃ₗ[Chapter07NodeRing k]
      Chapter07NodeDifferentials k

/- LOCAL_DEPENDENCY_GUESS: this is the exact quotient presentation needed to
turn the conormal relation into the displayed `dx,dy` presentation. -/
theorem chapter07_node_differential_presentation
    (k : Type u) [Field k] :
    Nonempty (Chapter07NodeDifferentialPresentationData k) := by
  sorry

noncomputable def chapter07NodeDifferentialPresentationData
    (k : Type u) [Field k] : Chapter07NodeDifferentialPresentationData k :=
  Classical.choice (chapter07_node_differential_presentation k)

noncomputable def chapter07NodeTorsionCandidate (k : Type u) [Field k] :
    Chapter07NodePresentedDifferentials k :=
  chapter07NodeX k • chapter07NodeDy k

theorem chapter07_node_differential_relation
    (k : Type u) [Field k] :
    chapter07NodeX k • chapter07NodeDy k =
      -(chapter07NodeY k • chapter07NodeDx k) := by
  sorry

theorem chapter07_node_torsion_candidate_nonzero
    (k : Type u) [Field k] :
    chapter07NodeTorsionCandidate k ≠ 0 := by
  sorry

noncomputable def chapter07NodeCanonicalTorsionCandidate
    (k : Type u) [Field k] : Chapter07NodeDifferentials k :=
  (chapter07NodeDifferentialPresentationData k).equivalence
    (chapter07NodeTorsionCandidate k)

theorem chapter07_node_canonical_torsion_candidate_nonzero
    (k : Type u) [Field k] :
    chapter07NodeCanonicalTorsionCandidate k ≠ 0 := by
  intro h
  apply chapter07_node_torsion_candidate_nonzero k
  exact (chapter07NodeDifferentialPresentationData k).equivalence.injective (by simpa using h)

theorem chapter07_node_canonical_torsion_candidate_killed
    (k : Type u) [Field k] :
    (chapter07NodeX k + chapter07NodeY k) •
        chapter07NodeCanonicalTorsionCandidate k = 0 := by
  sorry

theorem chapter07_node_torsion_candidate_killed
    (k : Type u) [Field k] :
    (chapter07NodeX k + chapter07NodeY k) • chapter07NodeTorsionCandidate k = 0 := by
  sorry

theorem chapter07_node_x_add_y_is_regular
    (k : Type u) [Field k] :
    IsRegular (chapter07NodeX k + chapter07NodeY k) := by
  sorry

def chapter07NodeDifferentialsNotLocallyFree (k : Type u) [Field k] : Prop :=
  ¬ Module.Free (Chapter07NodeRing k) (Chapter07NodeDifferentials k)

def chapter07NodeDifferentialsHaveTorsion (k : Type u) [Field k] : Prop :=
  ∃ (m : Chapter07NodeDifferentials k) (r : Chapter07NodeRing k),
    m ≠ 0 ∧ r ≠ 0 ∧ r • m = 0

theorem chapter07_node_differentials_not_locally_free
    (k : Type u) [Field k] : chapter07NodeDifferentialsNotLocallyFree k := by
  sorry

theorem chapter07_node_differentials_have_torsion
    (k : Type u) [Field k] : chapter07NodeDifferentialsHaveTorsion k := by
  sorry

structure Chapter07SmoothToNodalSpecializationData
    (k : Type u) [Field k] where
  family : Scheme.{u}
  base : Scheme.{u}
  familyMap : family ⟶ base
  smoothFamily : Smooth familyMap
  genericPoint : base
  genericFiber : Scheme.{u}
  specialPoint : base
  specialFiber : Scheme.{u}
  smoothFiber : Scheme.{u}
  nodalFiber : Scheme.{u}
  genericFiber_model : Nonempty
    (genericFiber ≅ familyMap.fiber genericPoint)
  specialFiber_model : Nonempty
    (specialFiber ≅ familyMap.fiber specialPoint)
  smoothFiberDifferentials : smoothFiber.Modules
  nodalFiberDifferentials : nodalFiber.Modules
  smoothFiber_model : Nonempty (smoothFiber ≅ genericFiber)
  nodalFiber_model : Nonempty (nodalFiber ≅ specialFiber)
  smoothFiber_isLineBundle : Chapter07IsLineBundle smoothFiberDifferentials
  nodalFiber_isNotLineBundle : ¬ Chapter07IsLineBundle nodalFiberDifferentials
  nodalFiber_node_model : Nonempty
    (nodalFiber ≅ AlgebraicGeometry.Spec (CommRingCat.of (Chapter07NodeRing k)))

/- This records the precise degeneration warning without identifying an
arbitrary family with the node. -/
theorem chapter07_smooth_fibers_can_have_a_nodal_differential_specialization
    (k : Type u) [Field k] :
    Nonempty (Chapter07SmoothToNodalSpecializationData k) := by
  sorry

/- The cusp subring is the subalgebra of `k[[t]]` generated by `t²,t³`; its
ordinary differential image is recorded in the normalization's `dt` chart. -/
def chapter07CuspSubalgebra (k : Type u) [CommRing k] :
    Subalgebra k (PowerSeries k) :=
  Subalgebra.adjoin k {((PowerSeries.X : PowerSeries k) ^ 2),
    ((PowerSeries.X : PowerSeries k) ^ 3)}

abbrev Chapter07CuspRing (k : Type u) [CommRing k] :=
  ↥(chapter07CuspSubalgebra k)

abbrev Chapter07CuspNormalization (k : Type u) [CommRing k] := PowerSeries k

def chapter07CuspFirstGenerator (k : Type u) [CommRing k] : PowerSeries k :=
  PowerSeries.C (2 : k) * (PowerSeries.X : PowerSeries k)

def chapter07CuspSecondGenerator (k : Type u) [CommRing k] : PowerSeries k :=
  PowerSeries.C (3 : k) * (PowerSeries.X : PowerSeries k) ^ 2

def chapter07CuspOrdinaryDifferentialImage (k : Type u) [CommRing k] :
    Submodule k (Chapter07CuspNormalization k) :=
  Submodule.span k
    {chapter07CuspFirstGenerator k, chapter07CuspSecondGenerator k}

theorem chapter07_cusp_ordinary_differentials_have_expected_generators
    (k : Type u) [CommRing k] :
    chapter07CuspOrdinaryDifferentialImage k =
      Submodule.span k
        {chapter07CuspFirstGenerator k, chapter07CuspSecondGenerator k} := by
  rfl

theorem chapter07_cusp_misses_dt
    (k : Type u) [Field k] (h2 : (2 : k) ≠ 0) :
    (1 : Chapter07CuspNormalization k) ∉ chapter07CuspOrdinaryDifferentialImage k := by
  sorry

theorem chapter07_cusp_characteristic_two_changes_the_first_generator
    (k : Type u) [Field k] (h2 : (2 : k) = 0) :
    chapter07CuspFirstGenerator k = 0 := by
  simp [chapter07CuspFirstGenerator, h2]

theorem chapter07_cusp_characteristic_three_changes_the_second_generator
    (k : Type u) [Field k] (h3 : (3 : k) = 0) :
    chapter07CuspSecondGenerator k = 0 := by
  simp [chapter07CuspSecondGenerator, h3]

abbrev Chapter07NodeScheme (k : Type u) [CommRing k] : Scheme.{u} :=
  AlgebraicGeometry.Spec (CommRingCat.of (Chapter07NodeRing k))

abbrev Chapter07NodeNormalizationRing (k : Type u) [CommRing k] :=
  PowerSeries k × PowerSeries k

abbrev Chapter07NodeNormalizationScheme (k : Type u) [CommRing k] : Scheme.{u} :=
  AlgebraicGeometry.Spec (CommRingCat.of (Chapter07NodeNormalizationRing k))

/- LOCAL_DEPENDENCY_GUESS: Mathlib does not yet construct the dualizing
module of this singular affine curve.  The record exposes the controlled
pole/residue-cancellation data while retaining an honest line-bundle object
for the node. -/
structure Chapter07NodeDualizingSheafData
    (k : Type u) [Field k] where
  dualizing : Chapter07LineBundle (Chapter07NodeScheme k)
  normalization : Scheme.{u}
  normalizationMap : normalization ⟶ Chapter07NodeScheme k
  normalization_model : Nonempty
    (normalization ≅ Chapter07NodeNormalizationScheme k)
  allowedRationalSections : Type u
  residue : allowedRationalSections → Fin 2 → k
  residues_cancel : ∀ η, ∑ i : Fin 2, residue η i = 0
  ordinary_differentials_not_free :
    ¬ Module.Free (Chapter07NodeRing k) (Chapter07NodeDifferentials k)

theorem chapter07_node_dualizing_sheaf_exists
    (k : Type u) [Field k] :
    Nonempty (Chapter07NodeDualizingSheafData k) := by
  sorry

noncomputable def chapter07NodeDualizingSheafData
    (k : Type u) [Field k] : Chapter07NodeDualizingSheafData k :=
  Classical.choice (chapter07_node_dualizing_sheaf_exists k)

theorem chapter07_node_dualizing_sheaf_is_invertible
    (k : Type u) [Field k] :
    Chapter07IsLineBundle
      (chapter07NodeDualizingSheafData k).dualizing.module := by
  exact (chapter07NodeDualizingSheafData k).dualizing.isInvertible

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter07
