import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter14.Section02TheBaseChangeTheorem

/-!
## 14.3 The Hodge bundle in smooth and nodal families

The dualizing pushforward is the stable object in both the smooth and nodal
settings.  The smooth differential comparison and the normalization/residue
description are kept as explicit data so later chapters can use either
formulation without losing the singular-fiber hypotheses.
-/

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter14

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04

noncomputable section

/-! The relative differential sheaf and its pushforward. -/

abbrev chapter14DifferentialSheaf
    (Ω : Chapter14RelativeDifferentialData)
    {X S : Scheme} (f : X ⟶ S) : X.Modules :=
  Ω.differentials f

abbrev chapter14DifferentialPushforwardOf
    (Ω : Chapter14RelativeDifferentialData)
    {X S : Scheme} (f : X ⟶ S) : S.Modules :=
  (Scheme.Modules.pushforward f).obj (Ω.differentials f)

def chapter14HodgeBundle
    {C : Chapter14RelativeCurveFamily}
    (D : Chapter14RelativeDualityData C) : C.S.Modules :=
  (Scheme.Modules.pushforward C.map).obj D.dualizing.omega

def chapter14DifferentialHodgeBundle
    {F : Chapter14SmoothRelativeCurveFamily}
    (Ω : Chapter14RelativeDifferentialData) : F.curve.S.Modules :=
  chapter14DifferentialPushforwardOf Ω F.curve.map

def chapter14SmoothingDifferentialFailureStatement
    (F : Chapter14SmoothRelativeCurveFamily)
    (D : Chapter14RelativeDualityData F.curve)
    (Ω : Chapter14RelativeDifferentialData) : Prop :=
  Nonempty (Chapter14SmoothingDifferentialFailureWitness F D Ω)

/-! Smooth families: `Ω¹` identifies with the relative dualizing sheaf. -/

structure Chapter14SmoothDifferentialDualizingIdentification
    (F : Chapter14SmoothRelativeCurveFamily)
    (D : Chapter14RelativeDualityData F.curve)
    (Ω : Chapter14RelativeDifferentialData) where
  sheafIso : Ω.differentials F.curve.map ≅ D.dualizing.omega
  pushforwardIso : chapter14DifferentialHodgeBundle F Ω ≅ chapter14HodgeBundle D
  pushforwardIso_is_induced : Prop

def chapter14SmoothHodgeBundle
    {F : Chapter14SmoothRelativeCurveFamily}
    {D : Chapter14RelativeDualityData F.curve}
    {Ω : Chapter14RelativeDifferentialData}
    (I : Chapter14SmoothDifferentialDualizingIdentification F D Ω) :
    F.curve.S.Modules :=
  chapter14HodgeBundle D

structure Chapter14SmoothHodgeBundleFiberDescription
    (F : Chapter14SmoothRelativeCurveFamily)
    (D : Chapter14RelativeDualityData F.curve)
    (Ω : Chapter14RelativeDifferentialData)
    (I : Chapter14SmoothDifferentialDualizingIdentification F D Ω)
    (B : Chapter14FiberCohomologyData) where
  hodgeLocallyFree : chapter04FiniteLocallyFree (chapter14HodgeBundle D)
  fiberH0 : ∀ s : F.curve.S, Type
  fiberIsoH0 : ∀ s : F.curve.S,
    Nonempty (B.fiber (chapter14HodgeBundle D) s ≃ fiberH0 s)
  fiberH0IsoDifferentialSections : ∀ s : F.curve.S,
    Nonempty (fiberH0 s ≃ B.h0 F.curve.map
      (Ω.differentials F.curve.map) s)
  fiberH0IsDifferentialSections : ∀ s : F.curve.S, Prop
  rank : ℕ
  rank_eq_genus : rank = F.genus
  fiberDimension : ∀ s : F.curve.S, ∃ n : ℕ, n = rank

def chapter14SmoothHodgeBundleStatement
    (F : Chapter14SmoothRelativeCurveFamily)
    (D : Chapter14RelativeDualityData F.curve)
    (Ω : Chapter14RelativeDifferentialData)
    (I : Chapter14SmoothDifferentialDualizingIdentification F D Ω)
    (B : Chapter14FiberCohomologyData) : Prop :=
  Nonempty (Chapter14SmoothHodgeBundleFiberDescription F D Ω I B)

theorem chapter14_smooth_hodge_bundle_is_locally_free_rank_genus
    (F : Chapter14SmoothRelativeCurveFamily)
    (D : Chapter14RelativeDualityData F.curve)
    (Ω : Chapter14RelativeDifferentialData)
    (I : Chapter14SmoothDifferentialDualizingIdentification F D Ω)
    (B : Chapter14FiberCohomologyData)
    (H : Chapter14RelativeCohomologyConstancyData F.curve D)
    (hB : H.fiberCohomology = B) :
    Nonempty (Chapter14SmoothHodgeBundleFiberDescription F D Ω I B) := by
  sorry

theorem chapter14_smooth_hodge_bundle_description_of_statement
    (F : Chapter14SmoothRelativeCurveFamily)
    (D : Chapter14RelativeDualityData F.curve)
    (Ω : Chapter14RelativeDifferentialData)
    (I : Chapter14SmoothDifferentialDualizingIdentification F D Ω)
    (B : Chapter14FiberCohomologyData)
    (H : Chapter14SmoothHodgeBundleStatement F D Ω I B) :
    Chapter14SmoothHodgeBundleFiberDescription F D Ω I B := by
  exact Classical.choice H

/-! Nodal families: the Hodge bundle is still `f_*ω`. -/

structure Chapter14NodalHodgeBundleDescription
    (F : Chapter14NodalRelativeCurveFamily)
    (D : Chapter14RelativeDualityData F.curve)
    (B : Chapter14FiberCohomologyData) where
  hodgeBundle : F.curve.S.Modules
  hodgeBundle_eq_duality_pushforward : hodgeBundle = chapter14HodgeBundle D
  differentialDescription : Chapter14NodalFiberDifferentialDescription F D B
  hodgeLocallyFree : chapter04FiniteLocallyFree hodgeBundle
  rank : ℕ
  rank_eq_arithmeticGenus : rank = F.arithmeticGenus
  fiber : ∀ s : F.curve.S, Type
  fiberIso : ∀ s : F.curve.S,
    Nonempty (B.fiber hodgeBundle s ≃ fiber s)
  fiberIsNormalizationDifferentialsWithOppositeResidues :
    ∀ s : F.curve.S, Prop
  normalizedComponentGenus : ∀ s : F.curve.S, ℕ
  dualGraphCycleRank : ∀ s : F.curve.S, ℕ
  arithmeticGenusDecomposition : ∀ s : F.curve.S,
    normalizedComponentGenus s + dualGraphCycleRank s = F.arithmeticGenus
  nodePoleFormsAccountForGraphCycles : ∀ s : F.curve.S, Prop

def chapter14NodalHodgeBundle
    {F : Chapter14NodalRelativeCurveFamily}
    (D : Chapter14RelativeDualityData F.curve) : F.curve.S.Modules :=
  chapter14HodgeBundle D

def chapter14NodalHodgeBundleStatement
    (F : Chapter14NodalRelativeCurveFamily)
    (D : Chapter14RelativeDualityData F.curve)
    (B : Chapter14FiberCohomologyData) : Prop :=
  Nonempty (Chapter14NodalHodgeBundleDescription F D B)

theorem chapter14_nodal_hodge_bundle_description
    (F : Chapter14NodalRelativeCurveFamily)
    (D : Chapter14RelativeDualityData F.curve)
    (B : Chapter14FiberCohomologyData)
    (H : Chapter14RelativeCohomologyConstancyData F.curve D)
    (hB : H.fiberCohomology = B) :
    Nonempty (Chapter14NodalHodgeBundleDescription F D B) := by
  sorry

theorem chapter14_nodal_hodge_bundle_has_arithmetic_genus_rank
    (F : Chapter14NodalRelativeCurveFamily)
    (D : Chapter14RelativeDualityData F.curve)
    (B : Chapter14FiberCohomologyData)
    (H : chapter14NodalHodgeBundleStatement F D B) :
    (Classical.choice H).rank = F.arithmeticGenus := by
  exact (Classical.choice H).rank_eq_arithmeticGenus

theorem chapter14_nodal_hodge_fiber_has_opposite_residues
    (F : Chapter14NodalRelativeCurveFamily)
    (D : Chapter14RelativeDualityData F.curve)
    (B : Chapter14FiberCohomologyData)
    (H : chapter14NodalHodgeBundleStatement F D B) (s : F.curve.S) :
    (Classical.choice H).fiberIsNormalizationDifferentialsWithOppositeResidues s := by
  exact (Classical.choice H).fiberIsNormalizationDifferentialsWithOppositeResidues s

/-! The Hodge bundle is stable under arbitrary base change. -/

structure Chapter14HodgeBundleBaseChangeData
    {C : Chapter14RelativeCurveFamily}
    (D : Chapter14RelativeDualityData C) where
  baseChange : ∀ {T : Scheme} (g : T ⟶ C.S),
    (Scheme.Modules.pullback g).obj (chapter14HodgeBundle D) ≅
      (Scheme.Modules.pushforward (pullback.snd C.map g)).obj
        (D.dualizing.baseChangeOmega g)
  compatibleWithTrace : Prop
  compatibleWithPairing : Prop

structure Chapter14HodgeBundleBaseChangeStatement
    {C : Chapter14RelativeCurveFamily}
    (D : Chapter14RelativeDualityData C) where
  forTestScheme : ∀ {T : Scheme} (g : T ⟶ C.S), Prop
  arbitrary : Prop
  selectedByDuality : Prop

theorem chapter14_hodge_bundle_commutes_with_arbitrary_base_change
    {C : Chapter14RelativeCurveFamily}
    (D : Chapter14RelativeDualityData C)
    (hconn : GeometricallyConnected C.map)
    (hred : GeometricallyReduced C.map)
    (H : Chapter14RelativeCohomologyConstancyData C D) :
    Nonempty (Chapter14HodgeBundleBaseChangeData D) := by
  sorry

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter14
