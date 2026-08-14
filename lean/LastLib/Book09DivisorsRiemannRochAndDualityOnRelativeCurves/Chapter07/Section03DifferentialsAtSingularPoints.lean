import Mathlib.Algebra.Ring.Regular
import Mathlib.RingTheory.MvPowerSeries.Basic
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter07.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter07

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09
open scoped BigOperators TensorProduct

noncomputable section

universe u

/-!
## 7.3 Differentials at singular points
-/

/- The node is represented by the completed-coordinate quotient
`k[[x,y]]/(xy)`.  The displayed presentation below is an explicit completed
model; the algebraic Kähler module is kept as a separate definition. -/
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

theorem chapter07_node_equation
    (k : Type u) [CommRing k] :
    chapter07NodeX k * chapter07NodeY k = 0 := by
  sorry

/- The actual algebraic Kähler module is retained separately.  The displayed
   `A dx ⊕ A dy` presentation below is the completed coordinate model used by
   the node calculation; no unsupported comparison with algebraic Ω is made. -/
abbrev Chapter07NodeKahlerDifferentials (k : Type u) [CommRing k] :=
  Ω[Chapter07NodeRing k⁄k]

def chapter07NodeConormalEquationDifferential
    (k : Type u) [CommRing k] : Ω[Chapter07NodeAmbient k⁄k] :=
  KaehlerDifferential.D k (Chapter07NodeAmbient k) (chapter07NodeEquation k)

theorem chapter07_node_conormal_differential_expands
    (k : Type u) [CommRing k] :
    chapter07NodeConormalEquationDifferential k =
      (MvPowerSeries.X (0 : Fin 2) : Chapter07NodeAmbient k) •
          KaehlerDifferential.D k (Chapter07NodeAmbient k)
            (MvPowerSeries.X (1 : Fin 2)) +
        (MvPowerSeries.X (1 : Fin 2) : Chapter07NodeAmbient k) •
          KaehlerDifferential.D k (Chapter07NodeAmbient k)
            (MvPowerSeries.X (0 : Fin 2)) := by
  sorry

/- The displayed presentation `(A dx ⊕ A dy)/(y dx + x dy)` is made into an
actual quotient module. For a formal power-series ring this is the completed
conormal model; ordinary algebraic Kähler differentials need not be generated
by `dx` and `dy`, so no equivalence with `Ω[A⁄k]` is asserted here. -/
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

abbrev Chapter07NodeCompletedDifferentialsApproximation
    (k : Type u) [CommRing k] :=
  Chapter07NodePresentedDifferentials k

abbrev Chapter07NodeCompletedDifferentials (k : Type u) [CommRing k] :=
  Chapter07NodeCompletedDifferentialsApproximation k

abbrev Chapter07NodeDifferentials (k : Type u) [CommRing k] :=
  Chapter07NodeKahlerDifferentials k

noncomputable def chapter07NodeDx (k : Type u) [CommRing k] :
    Chapter07NodePresentedDifferentials k :=
  Submodule.Quotient.mk (1, 0)

noncomputable def chapter07NodeDy (k : Type u) [CommRing k] :
    Chapter07NodePresentedDifferentials k :=
  Submodule.Quotient.mk (0, 1)

theorem chapter07_node_conormal_relation
    (k : Type u) [CommRing k] :
    chapter07NodeY k • chapter07NodeDx k +
        chapter07NodeX k • chapter07NodeDy k = 0 := by
  sorry

noncomputable def chapter07NodeTorsionCandidate (k : Type u) [Field k] :
    Chapter07NodeCompletedDifferentials k :=
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

theorem chapter07_node_torsion_candidate_killed
    (k : Type u) [Field k] :
    (chapter07NodeX k + chapter07NodeY k) • chapter07NodeTorsionCandidate k = 0 := by
  sorry

theorem chapter07_node_x_add_y_is_regular
    (k : Type u) [Field k] :
    IsRegular (chapter07NodeX k + chapter07NodeY k) := by
  sorry

def chapter07NodeDifferentialsNotFree (k : Type u) [Field k] : Prop :=
  ¬ Module.Free (Chapter07NodeRing k) (Chapter07NodeDifferentials k)

def chapter07NodeDifferentialsHaveTorsion (k : Type u) [Field k] : Prop :=
  ∃ (m : Chapter07NodeDifferentials k) (r : Chapter07NodeRing k),
    m ≠ 0 ∧ r ≠ 0 ∧ r • m = 0

def chapter07NodeDisplayedDifferentialsNotFree (k : Type u) [Field k] : Prop :=
  ¬ Module.Free (Chapter07NodeRing k) (Chapter07NodeCompletedDifferentials k)

theorem chapter07_node_differentials_not_free
    (k : Type u) [Field k] : chapter07NodeDifferentialsNotFree k := by
  sorry

theorem chapter07_node_differentials_have_torsion
    (k : Type u) [Field k] : chapter07NodeDifferentialsHaveTorsion k := by
  sorry

structure Chapter07SmoothToNodalSpecializationData
    (k : Type u) [Field k] where
  family : Scheme.{u}
  base : Scheme.{u}
  familyMap : family ⟶ base
  flatFamily : Flat familyMap
  relativeDifferentials : Chapter07RelativeDifferentialSheafData familyMap
  genericPoint : base
  specialPoint : base
  genericPoint_ne_specialPoint : genericPoint ≠ specialPoint
  smoothFiber : Scheme.{u}
  nodalFiber : Scheme.{u}
  genericFiber_model : Nonempty
    (smoothFiber ≅ familyMap.fiber genericPoint)
  specialFiber_model : Nonempty
    (nodalFiber ≅ familyMap.fiber specialPoint)
  smoothFiber_differentials_isLineBundle :
    Chapter07IsLineBundle
      ((Scheme.Modules.pullback (familyMap.fiberι genericPoint)).obj
        relativeDifferentials.relativeDifferentials)
  nodalFiber_differentials_isNotLineBundle :
    ¬ Chapter07IsLineBundle
      ((Scheme.Modules.pullback (familyMap.fiberι specialPoint)).obj
        relativeDifferentials.relativeDifferentials)
  nodalFiber_node_model : Nonempty
    (nodalFiber ≅
      AlgebraicGeometry.Spec (CommRingCat.of (Chapter07NodeRing k)))

/- This records the precise degeneration warning without identifying an
arbitrary family with the node. -/
theorem chapter07_smooth_fibers_can_have_a_nodal_differential_specialization
    (k : Type u) [Field k] :
    Nonempty (Chapter07SmoothToNodalSpecializationData k) := by
  sorry

/- The cusp subring is the subalgebra of `k[[t]]` generated by `t²,t³`.  Its
ordinary differential image is the range of the canonical Kähler map into the
normalization, rather than an independently chosen submodule. -/
def chapter07CuspSubalgebra (k : Type u) [CommRing k] :
    Subalgebra k (PowerSeries k) :=
  Algebra.adjoin k {((PowerSeries.X : PowerSeries k) ^ 2),
    ((PowerSeries.X : PowerSeries k) ^ 3)}

abbrev Chapter07CuspRing (k : Type u) [CommRing k] :=
  ↥(chapter07CuspSubalgebra k)

abbrev Chapter07CuspNormalization (k : Type u) [CommRing k] := PowerSeries k

abbrev Chapter07CuspOrdinaryDifferentials (k : Type u) [CommRing k] :=
  Ω[Chapter07CuspRing k⁄k]

abbrev Chapter07CuspNormalizationDifferentials (k : Type u) [CommRing k] :=
  Ω[Chapter07CuspNormalization k⁄k]

noncomputable def chapter07CuspDifferentialMap (k : Type u) [CommRing k] :
    Chapter07CuspOrdinaryDifferentials k →ₗ[Chapter07CuspRing k]
      Chapter07CuspNormalizationDifferentials k :=
  KaehlerDifferential.map k k (Chapter07CuspRing k)
    (Chapter07CuspNormalization k)

def chapter07CuspFirstGenerator (k : Type u) [CommRing k] :
    Chapter07CuspNormalizationDifferentials k :=
  (PowerSeries.C (2 : k) * (PowerSeries.X : PowerSeries k)) •
    KaehlerDifferential.D k (PowerSeries k) (PowerSeries.X : PowerSeries k)

def chapter07CuspSecondGenerator (k : Type u) [CommRing k] :
    Chapter07CuspNormalizationDifferentials k :=
  (PowerSeries.C (3 : k) * (PowerSeries.X : PowerSeries k) ^ 2) •
    KaehlerDifferential.D k (PowerSeries k) (PowerSeries.X : PowerSeries k)

def chapter07CuspOrdinaryDifferentialImage (k : Type u) [CommRing k] :
    Submodule (Chapter07CuspRing k) (Chapter07CuspNormalizationDifferentials k) :=
  LinearMap.range (chapter07CuspDifferentialMap k)

theorem chapter07_cusp_ordinary_differentials_have_expected_generators
    (k : Type u) [CommRing k] :
    chapter07CuspOrdinaryDifferentialImage k =
      Submodule.span (Chapter07CuspRing k)
        {chapter07CuspFirstGenerator k, chapter07CuspSecondGenerator k} := by
  sorry

theorem chapter07_cusp_misses_dt
    (k : Type u) [Field k] (h2 : (2 : k) ≠ 0) :
    KaehlerDifferential.D k (PowerSeries k) (PowerSeries.X : PowerSeries k) ∉
      chapter07CuspOrdinaryDifferentialImage k := by
  sorry

theorem chapter07_cusp_characteristic_two_changes_the_first_generator
    (k : Type u) [Field k] (h2 : (2 : k) = 0) :
    chapter07CuspFirstGenerator k = 0 := by
  sorry

theorem chapter07_cusp_characteristic_three_changes_the_second_generator
    (k : Type u) [Field k] (h3 : (3 : k) = 0) :
    chapter07CuspSecondGenerator k = 0 := by
  sorry

abbrev Chapter07NodeScheme (k : Type u) [CommRing k] : Scheme.{u} :=
  AlgebraicGeometry.Spec (CommRingCat.of (Chapter07NodeRing k))

abbrev Chapter07NodeNormalizationRing (k : Type u) [CommRing k] :=
  PowerSeries k × PowerSeries k

abbrev Chapter07NodeNormalizationScheme (k : Type u) [CommRing k] : Scheme.{u} :=
  AlgebraicGeometry.Spec (CommRingCat.of (Chapter07NodeNormalizationRing k))

/- A completed Rosenlicht section is represented by its two branch
   coefficients; the subtype records the opposite-residue condition.  Its
   displayed differential is obtained through the actual Kähler differentials
   of the normalization branches. -/
abbrev Chapter07NodeBranchDifferentials (k : Type u) [Field k] :=
  Ω[PowerSeries k⁄k]

abbrev Chapter07NodeRosenlichtDifferentials (k : Type u) [Field k] :=
  Chapter07NodeBranchDifferentials k × Chapter07NodeBranchDifferentials k

structure Chapter07NodeCompletedRosenlichtSection (k : Type u) [Field k] where
  left : PowerSeries k
  right : PowerSeries k
  residues_cancel :
    PowerSeries.constantCoeff left + PowerSeries.constantCoeff right = 0

abbrev Chapter07NodeAllowedRationalSection (k : Type u) [Field k] :=
  Chapter07NodeCompletedRosenlichtSection k

noncomputable def chapter07NodeRosenlichtDifferential
    (k : Type u) [Field k]
    (η : Chapter07NodeCompletedRosenlichtSection k) :
    Chapter07NodeRosenlichtDifferentials k :=
  (η.left • KaehlerDifferential.D k (PowerSeries k)
      (PowerSeries.X : PowerSeries k),
    η.right • KaehlerDifferential.D k (PowerSeries k)
      (PowerSeries.X : PowerSeries k))

def chapter07NodeAllowedRationalResidue
    (k : Type u) [Field k]
    (η : Chapter07NodeAllowedRationalSection k) : Fin 2 → k :=
  fun i => if i = 0 then PowerSeries.constantCoeff η.left
    else PowerSeries.constantCoeff η.right

/- The completed node is Gorenstein; its dualizing module is represented here
   by the actual structure-sheaf module, while the normalization morphism and
   residue condition remain explicit geometric data. -/
noncomputable def chapter07NodeDualizingSheaf
    (k : Type u) [Field k] : Chapter07LineBundle (Chapter07NodeScheme k) :=
  chapter09StructureSheafLineBundle (Chapter07NodeScheme k)

structure Chapter07NodeDualizingSheafData
    (k : Type u) [Field k] where
  normalizationMap : Chapter07NodeNormalizationScheme k ⟶ Chapter07NodeScheme k
  residues_cancel : ∀ η : Chapter07NodeAllowedRationalSection k,
    ∑ i : Fin 2, chapter07NodeAllowedRationalResidue k η i = 0
  displayed_differentials_not_free :
    chapter07NodeDisplayedDifferentialsNotFree k

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
      (chapter07NodeDualizingSheaf k).module := by
  sorry

theorem chapter07_node_dualizing_sheaf_is_free_rank_one
    (k : Type u) [Field k] :
    chapter09LineBundleIsomorphic (chapter07NodeDualizingSheaf k)
      (chapter09StructureSheafLineBundle (Chapter07NodeScheme k)) := by
  sorry

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter07
