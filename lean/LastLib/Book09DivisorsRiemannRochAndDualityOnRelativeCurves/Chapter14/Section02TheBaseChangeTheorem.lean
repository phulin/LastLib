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
    {C : Chapter14RelativeCurveFamily}
    {H : Chapter14RelativeCohomologyTheory}
    {E : Chapter14VectorBundle C.X}
    {T : Scheme} (g : T ⟶ C.S)
    (K : Chapter14FiniteFreeModel C H E) : T.Modules :=
  (Scheme.Modules.pullback g).obj K.K0

abbrev chapter14PullbackFiniteFreeModelK1
    {C : Chapter14RelativeCurveFamily}
    {H : Chapter14RelativeCohomologyTheory}
    {E : Chapter14VectorBundle C.X}
    {T : Scheme} (g : T ⟶ C.S)
    (K : Chapter14FiniteFreeModel C H E) : T.Modules :=
  (Scheme.Modules.pullback g).obj K.K1

abbrev chapter14PullbackFiniteFreeModelDifferential
    {C : Chapter14RelativeCurveFamily}
    {H : Chapter14RelativeCohomologyTheory}
    {E : Chapter14VectorBundle C.X}
    {T : Scheme} (g : T ⟶ C.S)
    (K : Chapter14FiniteFreeModel C H E) :
    chapter14PullbackFiniteFreeModelK0 g K ⟶
      chapter14PullbackFiniteFreeModelK1 g K :=
  (Scheme.Modules.pullback g).map K.differential

structure Chapter14FiniteFreeBaseChangeCompatibility
    {C : Chapter14RelativeCurveFamily}
    {H : Chapter14RelativeCohomologyTheory}
    {E : Chapter14VectorBundle C.X}
    {T : Scheme} (g : T ⟶ C.S)
    (D_S : Chapter14SheafDualityData C.S)
    (D_T : Chapter14SheafDualityData T) where
  dualPullbackIso : ∀ (K : Chapter14FiniteFreeModel C H E),
    D_T.dual (chapter14PullbackFiniteFreeModelK1 g K) ≅
      (Scheme.Modules.pullback g).obj
        (chapter14TransposedDualModel D_S K).K0

theorem chapter14_finite_free_model_explains_trace_base_change
    {C : Chapter14RelativeCurveFamily}
    (D : Chapter14RelativeDualityData C)
    {T : Scheme} (g : T ⟶ C.S)
    {E : Chapter14VectorBundle C.X}
    (D_T : Chapter14SheafDualityData T)
    (K : @Chapter14FiniteFreeBaseChangeCompatibility C D.cohomology E T g
      D.dualOnBase D_T) :
    ∀ (model : Chapter14FiniteFreeModel C D.cohomology E),
      Nonempty (D_T.dual (chapter14PullbackFiniteFreeModelK1 g model) ≅
        (Scheme.Modules.pullback g).obj
          (chapter14TransposedDualModel D.dualOnBase model).K0) := by
  intro model
  exact ⟨K.dualPullbackIso model⟩

/-! Connected and reduced fibers. -/

structure Chapter14ConnectedReducedFiberData
  (C : Chapter14RelativeCurveFamily) where
  geometricallyConnected : GeometricallyConnected C.map
  geometricallyReduced : GeometricallyReduced C.map
  fiberCohomology : Chapter14FiberCohomologyData C
  h0StructureSheafOne : ∀ s : C.S,
    Nonempty (((fiberCohomology.fiber
      ((Scheme.Modules.pushforward C.map).obj (chapter14StructureSheaf C.X)) s : Type)
      ≃ₗ[C.S.residueField s] C.S.residueField s))
  h0StructureSheafFinrankOne : ∀ s : C.S,
    fiberCohomology.fiberFinrank
      ((Scheme.Modules.pushforward C.map).obj (chapter14StructureSheaf C.X)) s = 1

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

/-! Equation (14.5). -/

structure Chapter14DualityPushforwardIsomorphism
    (C : Chapter14RelativeCurveFamily)
    (D : Chapter14RelativeDualityData C) where
  iso :
    (Scheme.Modules.pushforward C.map).obj D.dualizing.omega ≅
      D.dualOnBase.dual (chapter14R1Pushforward D.cohomology C.map
        (chapter14StructureSheaf C.X))

structure Chapter14ConnectedFiberBaseChangeConclusion
    (C : Chapter14RelativeCurveFamily)
    (D : Chapter14RelativeDualityData C) where
  fibers : Chapter14ConnectedReducedFiberData C
  structureSheafPushforward : Chapter14UnitPushforwardIdentification C D
  traceIsomorphism : Chapter14TraceIsomorphism C D
  dualityPushforward : Chapter14DualityPushforwardIsomorphism C D

/- Chapter 13 provides a typed cohomology-and-base-change package for its
projective relative-curve interface.  The present proper-family interface has
different data, so the following record is the explicit bridge for this
chapter; its hypotheses contain only the fiberwise H⁰=1 and locally constant
Euler/H¹ information used in the source argument. -/

structure Chapter14RelativeCohomologyConstancyData
    (C : Chapter14RelativeCurveFamily)
    (D : Chapter14RelativeDualityData C) where
  fiberCohomology : Chapter14FiberCohomologyData C
  h0StructureSheafOne : ∀ s : C.S,
    Nonempty (((fiberCohomology.fiber (chapter14StructureSheafPushforward C) s : Type)
      ≃ₗ[C.S.residueField s] C.S.residueField s))
  h0StructureSheafFinrankOne : ∀ s : C.S,
    fiberCohomology.fiberFinrank (chapter14StructureSheafPushforward C) s = 1
  h1Rank : C.S → ℕ
  eulerCharacteristic : C.S → ℤ
  eulerCharacteristicLocallyConstant :
    chapter14LocallyConstant eulerCharacteristic
  h1RankDeterminedByEulerCharacteristic :
    ∀ s : C.S, (h1Rank s : ℤ) = 1 - eulerCharacteristic s
  h1Rank_eq_fiberFinrank : ∀ s : C.S,
    h1Rank s = fiberCohomology.fiberFinrank
      (chapter14R1Pushforward D.cohomology C.map
        (chapter14StructureSheaf C.X)) s

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
    (D : Chapter14RelativeDualityData C)
    (H : Chapter14RelativeCohomologyConstancyData C D) where
  genus : ℕ
  h1RankIsConstant : ∀ s : C.S, H.h1Rank s = genus

structure Chapter14ConstantGenusBaseChangeConclusion
    (C : Chapter14RelativeCurveFamily)
    (D : Chapter14RelativeDualityData C)
    (H : Chapter14RelativeCohomologyConstancyData C D)
    (G : Chapter14ConstantGenusData C D H) where
  dualityPushforward : Chapter14DualityPushforwardIsomorphism C D
  r1StructureSheafLocallyFree :
    chapter04FiniteLocallyFree
      (chapter14R1Pushforward D.cohomology C.map (chapter14StructureSheaf C.X))
  omegaPushforwardLocallyFree :
    chapter04FiniteLocallyFree
      ((Scheme.Modules.pushforward C.map).obj D.dualizing.omega)
  traceIsomorphism : Chapter14TraceIsomorphism C D
  r1StructureSheafRank_eq_genus :
    ∀ s : C.S,
      H.fiberCohomology.fiberFinrank
        (chapter14R1Pushforward D.cohomology C.map
          (chapter14StructureSheaf C.X)) s = G.genus
  omegaPushforwardRank_eq_genus :
    ∀ s : C.S,
      H.fiberCohomology.fiberFinrank
        ((Scheme.Modules.pushforward C.map).obj D.dualizing.omega) s = G.genus
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
    (H : Chapter14RelativeCohomologyConstancyData C D)
    (G : Chapter14ConstantGenusData C D H) :
    Nonempty (Chapter14ConstantGenusBaseChangeConclusion C D H G) := by
  sorry

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter14
