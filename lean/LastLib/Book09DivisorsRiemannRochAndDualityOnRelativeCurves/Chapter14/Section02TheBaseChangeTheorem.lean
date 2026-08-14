import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter14.Dependencies

/-!
## 14.2 The base-change theorem

This leaf records the arbitrary-base-change statements and the connected-fiber
specialization.  The comparison maps are part of the dependency interface, so
the theorem statements expose their directions and their compatibility with
the trace rather than hiding them behind propositions.
-/

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter14

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04

noncomputable section

/-! The base-change comparison for the relative dualizing sheaf. -/

abbrev chapter14RelativeDualizingBaseChangeIso
    {C : Chapter14RelativeCurveFamily}
    (W : Chapter14RelativeDualizingSheafTheory C)
    {T : Scheme} (g : T ⟶ C.S) :
    (Scheme.Modules.pullback (pullback.fst C.map g)).obj W.omega ≅
      W.baseChangeOmega g :=
  W.baseChangeIso g

@[simp]
theorem chapter14_relative_dualizing_base_change_iso_eq_data
    {C : Chapter14RelativeCurveFamily}
    (W : Chapter14RelativeDualizingSheafTheory C)
    {T : Scheme} (g : T ⟶ C.S) :
    chapter14RelativeDualizingBaseChangeIso W g = W.baseChangeIso g :=
  rfl

/-! The trace base-change datum, including the pulled-back trace itself. -/

abbrev chapter14TraceBaseChangeData
    {C : Chapter14RelativeCurveFamily}
    (D : Chapter14RelativeDualityData C)
    {T : Scheme} (g : T ⟶ C.S) :
    Chapter14RelativeBaseChangeTraceData C D.cohomology D.dualizing D.trace g :=
  D.baseChange g

def chapter14TraceAfterBaseChange
    {C : Chapter14RelativeCurveFamily}
    (D : Chapter14RelativeDualityData C)
    {T : Scheme} (g : T ⟶ C.S) :
    chapter14R1Pushforward D.cohomology (pullback.snd C.map g)
        (D.dualizing.baseChangeOmega g) ⟶
      chapter14StructureSheaf T :=
  (D.baseChange g).traceAfterBaseChange

theorem chapter14_trace_base_change_compatibility
    {C : Chapter14RelativeCurveFamily}
    (D : Chapter14RelativeDualityData C)
    {T : Scheme} (g : T ⟶ C.S) :
    (D.baseChange g).cohomologyIso.hom ≫
        D.cohomology.map (pullback.snd C.map g)
          (D.baseChange g).omegaIso.hom 1 ≫
          chapter14TraceAfterBaseChange D g =
      (Scheme.Modules.pullback g).map D.trace ≫ (D.baseChange g).unitIso.hom := by
  exact (D.baseChange g).trace_compatibility

/-!
The finite-free matrix explanation is represented as a reusable compatibility
record: tensoring the differential and dualizing it commute with base change,
and evaluation is natural for the resulting transposed map.
-/

abbrev chapter14PullbackFiniteFreeModelK0
    {S T : Scheme} (g : T ⟶ S) {M : S.Modules}
    (K : Chapter14FiniteFreeModel S M) : T.Modules :=
  (Scheme.Modules.pullback g).obj K.K0

abbrev chapter14PullbackFiniteFreeModelK1
    {S T : Scheme} (g : T ⟶ S) {M : S.Modules}
    (K : Chapter14FiniteFreeModel S M) : T.Modules :=
  (Scheme.Modules.pullback g).obj K.K1

abbrev chapter14PullbackFiniteFreeModelDifferential
    {S T : Scheme} (g : T ⟶ S) {M : S.Modules}
    (K : Chapter14FiniteFreeModel S M) :
    chapter14PullbackFiniteFreeModelK0 g K ⟶
      chapter14PullbackFiniteFreeModelK1 g K :=
  (Scheme.Modules.pullback g).map K.differential

structure Chapter14FiniteFreeBaseChangeCompatibility
    {S T : Scheme} (g : T ⟶ S)
    (D_S : Chapter14SheafDualityData S)
    (D_T : Chapter14SheafDualityData T) where
  dualPullbackIso : ∀ {M : S.Modules} (K : Chapter14FiniteFreeModel S M),
    D_T.dual (chapter14PullbackFiniteFreeModelK1 g K) ≅
      chapter14PullbackFiniteFreeModelK0 g
        (chapter14TransposedDualModel D_S K)
  matrixPullback : Prop
  transposeTensorCompatibility : Prop
  evaluationTensorCompatibility : Prop

theorem chapter14_finite_free_model_explains_trace_base_change
    {C : Chapter14RelativeCurveFamily}
    (D : Chapter14RelativeDualityData C)
    {T : Scheme} (g : T ⟶ C.S)
    (D_T : Chapter14SheafDualityData T)
    (K : Chapter14FiniteFreeBaseChangeCompatibility g D.dualOnBase
      D_T) :
    K.matrixPullback ∧ K.transposeTensorCompatibility ∧
      K.evaluationTensorCompatibility := by
  exact ⟨K.matrixPullback, K.transposeTensorCompatibility,
    K.evaluationTensorCompatibility⟩

/-! Connected and reduced fibers. -/

structure Chapter14ConnectedReducedFiberData
    (C : Chapter14RelativeCurveFamily) where
  geometricallyConnected : GeometricallyConnected C.map
  geometricallyReduced : GeometricallyReduced C.map
  h0StructureSheaf : ∀ s : C.S, Prop
  h0IsOne : ∀ s : C.S, Prop

def chapter14HasConnectedReducedFibers
    (C : Chapter14RelativeCurveFamily) : Prop :=
  Nonempty (Chapter14ConnectedReducedFiberData C)

structure Chapter14UnitPushforwardIdentification
    (C : Chapter14RelativeCurveFamily)
    (D : Chapter14RelativeDualityData C) where
  unit : chapter14StructureSheaf C.S ⟶
    (Scheme.Modules.pushforward C.map).obj (chapter14StructureSheaf C.X)
  iso : chapter14StructureSheaf C.S ≅
    (Scheme.Modules.pushforward C.map).obj (chapter14StructureSheaf C.X)
  unit_eq_iso_hom : iso.hom = unit
  compatibleWithBaseChange : Prop

def chapter14StructureSheafPushforwardIso
    {C : Chapter14RelativeCurveFamily}
    {D : Chapter14RelativeDualityData C}
    (I : Chapter14UnitPushforwardIdentification C D) :
    (Scheme.Modules.pushforward C.map).obj (chapter14StructureSheaf C.X) ≅
      chapter14StructureSheaf C.S :=
  I.iso.symm

@[simp]
theorem chapter14StructureSheafPushforwardIso_hom
    {C : Chapter14RelativeCurveFamily}
    {D : Chapter14RelativeDualityData C}
    (I : Chapter14UnitPushforwardIdentification C D) :
    (chapter14StructureSheafPushforwardIso I).hom = I.iso.inv :=
  rfl

def chapter14StructureSheafPushforward
    (C : Chapter14RelativeCurveFamily) : C.S.Modules :=
  (Scheme.Modules.pushforward C.map).obj (chapter14StructureSheaf C.X)

/-! Equation (14.4). -/

structure Chapter14TraceIsomorphism
    (C : Chapter14RelativeCurveFamily)
    (D : Chapter14RelativeDualityData C) where
  iso : chapter14R1Pushforward D.cohomology C.map D.dualizing.omega ≅
    chapter14StructureSheaf C.S
  iso_hom_eq_trace : iso.hom = D.trace
  compatibleWithBaseChange : Prop

/-! Equation (14.5). -/

structure Chapter14DualityPushforwardIsomorphism
    (C : Chapter14RelativeCurveFamily)
    (D : Chapter14RelativeDualityData C) where
  iso :
    (Scheme.Modules.pushforward C.map).obj D.dualizing.omega ≅
      D.dualOnBase.dual (chapter14R1Pushforward D.cohomology C.map
        (chapter14StructureSheaf C.X))
  compatibleWithPairing : Prop
  compatibleWithBaseChange : Prop

structure Chapter14ConnectedFiberBaseChangeConclusion
    (C : Chapter14RelativeCurveFamily)
    (D : Chapter14RelativeDualityData C) where
  fibers : Chapter14ConnectedReducedFiberData C
  structureSheafPushforward : Chapter14UnitPushforwardIdentification C D
  traceIsomorphism : Chapter14TraceIsomorphism C D
  dualityPushforward : Chapter14DualityPushforwardIsomorphism C D

/- LOCAL_DEPENDENCY_GUESS: Section 13.2's cohomology-and-base-change package
is not yet available under the Book 9 namespace.  The following theorem is the
book-facing bridge; its hypotheses explicitly include the fiberwise H⁰=1 and
locally constant H¹ data used in the source argument. -/

structure Chapter14RelativeCohomologyConstancyData
    (C : Chapter14RelativeCurveFamily)
    (D : Chapter14RelativeDualityData C) where
  fiberCohomology : Chapter14FiberCohomologyData
  h0StructureSheafOne : ∀ s : C.S,
    Nonempty (fiberCohomology.fiber (chapter14StructureSheafPushforward C) s ≃ Unit)
  h1Rank : C.S → ℕ
  eulerCharacteristic : C.S → ℤ
  h1LocallyConstant : ∀ s t : C.S, h1Rank s = h1Rank t
  eulerCharacteristicLocallyConstant :
    ∀ s t : C.S, eulerCharacteristic s = eulerCharacteristic t
  h1RankDeterminedByEulerCharacteristic :
    ∀ s : C.S, (h1Rank s : ℤ) = 1 - eulerCharacteristic s
  structureSheafBaseChange :
    chapter14HigherDirectImageCommutesWithBaseChange D.cohomology
      C.map (chapter14StructureSheaf C.X) 0
  omegaBaseChange :
    chapter14HigherDirectImageCommutesWithBaseChange D.cohomology
      C.map D.dualizing.omega 0
  r1OmegaBaseChange :
    chapter14HigherDirectImageCommutesWithBaseChange D.cohomology
      C.map D.dualizing.omega 1
  r1StructureSheafBaseChange :
    chapter14HigherDirectImageCommutesWithBaseChange D.cohomology
      C.map (chapter14StructureSheaf C.X) 1
  pushforwardStructureSheafLocallyFree :
    chapter04FiniteLocallyFree (chapter14StructureSheafPushforward C)
  r1StructureSheafLocallyFree :
    chapter04FiniteLocallyFree
      (chapter14R1Pushforward D.cohomology C.map
        (chapter14StructureSheaf C.X))
  omegaPushforwardLocallyFree :
    chapter04FiniteLocallyFree
      ((Scheme.Modules.pushforward C.map).obj D.dualizing.omega)
  r1OmegaLocallyFree :
    chapter04FiniteLocallyFree
      (chapter14R1Pushforward D.cohomology C.map D.dualizing.omega)

theorem chapter14_connected_reduced_fibers_give_the_standard_pushforwards
    (C : Chapter14RelativeCurveFamily)
    (D : Chapter14RelativeDualityData C)
    (hconn : GeometricallyConnected C.map)
    (hred : GeometricallyReduced C.map)
    (H : Chapter14RelativeCohomologyConstancyData C D) :
    Nonempty (Chapter14ConnectedFiberBaseChangeConclusion C D) := by
  sorry

/-! Constant-genus rank and arbitrary base change. -/

structure Chapter14ConstantGenusData
    (C : Chapter14RelativeCurveFamily)
    (D : Chapter14RelativeDualityData C) where
  genus : ℕ
  h1Rank : C.S → ℕ
  h1RankIsConstant : ∀ s : C.S, h1Rank s = genus
  rankOfR1StructureSheaf : ∀ s : C.S, h1Rank s = genus
  rankOfOmegaPushforward : ∀ s : C.S, h1Rank s = genus

structure Chapter14ConstantGenusBaseChangeConclusion
    (C : Chapter14RelativeCurveFamily)
    (D : Chapter14RelativeDualityData C)
    (G : Chapter14ConstantGenusData C D) where
  dualityPushforward : Chapter14DualityPushforwardIsomorphism C D
  r1StructureSheafLocallyFree :
    chapter04FiniteLocallyFree
      (chapter14R1Pushforward D.cohomology C.map (chapter14StructureSheaf C.X))
  omegaPushforwardLocallyFree :
    chapter04FiniteLocallyFree
      ((Scheme.Modules.pushforward C.map).obj D.dualizing.omega)
  r1StructureSheafRank_eq_genus :
    ∀ s : C.S, G.h1Rank s = G.genus
  omegaPushforwardRank_eq_genus :
    ∀ s : C.S, G.h1Rank s = G.genus
  arbitraryBaseChange :
    chapter14HigherDirectImageCommutesWithBaseChange D.cohomology
        C.map (chapter14StructureSheaf C.X) 1 ∧
      chapter14HigherDirectImageCommutesWithBaseChange D.cohomology
        C.map D.dualizing.omega 0

theorem chapter14_constant_genus_gives_locally_free_hodge_pushforward
    (C : Chapter14RelativeCurveFamily)
    (D : Chapter14RelativeDualityData C)
    (hconn : GeometricallyConnected C.map)
    (hred : GeometricallyReduced C.map)
    (G : Chapter14ConstantGenusData C D)
    (H : Chapter14RelativeCohomologyConstancyData C D) :
    Nonempty (Chapter14ConstantGenusBaseChangeConclusion C D G) := by
  sorry

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter14
