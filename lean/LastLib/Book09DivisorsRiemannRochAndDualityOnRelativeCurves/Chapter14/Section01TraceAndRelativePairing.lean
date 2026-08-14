import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter14.Dependencies

/-!
## 14.1 Trace and the relative pairing

The trace is the primitive relative-duality map.  Multiplication is recorded
separately, so the displayed pairing is a genuine composite and not an
independent map chosen with the desired codomain.
-/

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter14

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09

noncomputable section

/-! The trace `R¹f_*ωₓ/ₛ ⟶ 𝒪ₛ`. -/

abbrev chapter14Trace
    {C : Chapter14RelativeCurveFamily}
    (D : Chapter14RelativeDualityData C) :
    chapter14R1Pushforward D.cohomology C.map D.dualizing.omega ⟶
      chapter14StructureSheaf C.S :=
  D.trace

@[simp]
theorem chapter14_trace_eq_data_trace
    {C : Chapter14RelativeCurveFamily}
    (D : Chapter14RelativeDualityData C) :
    chapter14Trace D = D.trace :=
  rfl

/-! Equation (14.1). -/

theorem chapter14_relative_pairing_eq_multiplication_then_trace
    {C : Chapter14RelativeCurveFamily}
    (D : Chapter14RelativeDualityData C) (E : Chapter14VectorBundle C.X) :
    chapter14RelativePairing D E = D.multiplication E ≫ D.trace :=
  rfl

/-! Equation (14.2), relative Serre duality for a vector bundle. -/

theorem chapter14_relative_serre_duality
    {C : Chapter14RelativeCurveFamily}
    (D : Chapter14RelativeDualityData C) (E : Chapter14VectorBundle C.X) :
    Nonempty (
      (Scheme.Modules.pushforward C.map).obj
          (chapter04Tensor (D.dualOnTotalSpace.dual E.sheaf)
            D.dualizing.omega) ≅
        D.dualOnBase.dual (chapter14R1Pushforward D.cohomology C.map E.sheaf)) := by
  sorry

/-! The matrix-level dual reverses the two degrees and transposes the map. -/

theorem chapter14_transposed_dual_model_computes
    {C : Chapter14RelativeCurveFamily}
    (D : Chapter14RelativeDualityData C)
    {H : Chapter14RelativeCohomologyTheory}
    {E : Chapter14VectorBundle C.X}
    (K : Chapter14FiniteFreeModel C H E) :
    Nonempty (Chapter14TransposedDualFiniteFreeModel D.dualOnBase K) := by
  sorry

/-! A convenient explicit statement of the degree reversal. -/

@[simp]
theorem chapter14_transposed_dual_model_K0
    {C : Chapter14RelativeCurveFamily}
    {H : Chapter14RelativeCohomologyTheory}
    {E : Chapter14VectorBundle C.X}
    (D : Chapter14SheafDualityData C.S)
    (K : Chapter14FiniteFreeModel C H E) :
    (chapter14TransposedDualModel D K).K0 = D.dual K.K1 :=
  rfl

@[simp]
theorem chapter14_transposed_dual_model_K1
    {C : Chapter14RelativeCurveFamily}
    {H : Chapter14RelativeCohomologyTheory}
    {E : Chapter14VectorBundle C.X}
    (D : Chapter14SheafDualityData C.S)
    (K : Chapter14FiniteFreeModel C H E) :
    (chapter14TransposedDualModel D K).K1 = D.dual K.K0 :=
  rfl

@[simp]
theorem chapter14_transposed_dual_model_differential
    {C : Chapter14RelativeCurveFamily}
    {H : Chapter14RelativeCohomologyTheory}
    {E : Chapter14VectorBundle C.X}
    (D : Chapter14SheafDualityData C.S)
    (K : Chapter14FiniteFreeModel C H E) :
    (chapter14TransposedDualModel D K).differential = D.dualMap K.differential :=
  rfl

/-! Perfectness when the two relevant pushforwards are locally free. -/

theorem chapter14_relative_pairing_is_perfect_of_pushforward_locally_free
    {C : Chapter14RelativeCurveFamily}
    (D : Chapter14RelativeDualityData C) (E : Chapter14VectorBundle C.X)
    (h₁ : chapter04FiniteLocallyFree
      (chapter14R1Pushforward D.cohomology C.map E.sheaf))
    (h₀dual : chapter04FiniteLocallyFree
      ((Scheme.Modules.pushforward C.map).obj
        (chapter04Tensor (D.dualOnTotalSpace.dual E.sheaf)
          D.dualizing.omega))) :
    Nonempty (Chapter14PerfectPairingData
      (chapter14R1Pushforward D.cohomology C.map E.sheaf)
      ((Scheme.Modules.pushforward C.map).obj
        (chapter04Tensor (D.dualOnTotalSpace.dual E.sheaf)
          D.dualizing.omega))
      D.dualOnBase (chapter14RelativePairing D E)) := by
  sorry

/-! Equation (14.3). -/

theorem chapter14_relative_serre_duality_degree_zero
    {C : Chapter14RelativeCurveFamily}
    (D : Chapter14RelativeDualityData C) (E : Chapter14VectorBundle C.X)
    (h₀ : chapter04FiniteLocallyFree
      ((Scheme.Modules.pushforward C.map).obj E.sheaf))
    (h₁dual : chapter04FiniteLocallyFree
      (chapter14R1Pushforward D.cohomology C.map
        (chapter04Tensor (D.dualOnTotalSpace.dual E.sheaf)
          D.dualizing.omega))) :
    Nonempty (
      D.dualOnBase.dual ((Scheme.Modules.pushforward C.map).obj E.sheaf) ≅
      chapter14R1Pushforward D.cohomology C.map
          (chapter04Tensor (D.dualOnTotalSpace.dual E.sheaf)
            D.dualizing.omega)) := by
  sorry

/-! Fiberwise compatibility with the absolute pairings from Chapter 12. -/

/- The earlier Chapter 12 residue-pairing declarations use a different
absolute-curve/fiber-cohomology interface.  The fields below keep the
comparison target and perfectness assertion explicit until that interface is
adapted to this relative family. -/

structure Chapter14FiberwisePairingAt
    (C : Chapter14RelativeCurveFamily)
    (D : Chapter14RelativeDualityData C)
    (E : Chapter14VectorBundle C.X)
    (B : Chapter14FiberCohomologyData C) (s : C.S) where
  left : ModuleCat (C.S.residueField s)
  right : ModuleCat (C.S.residueField s)
  pairing : ModuleCat.carrier left → ModuleCat.carrier right →
    C.S.residueField s
  leftIsFiberH1 : Nonempty (
    ModuleCat.carrier left ≃ₗ[C.S.residueField s]
      ModuleCat.carrier (B.h1 E.sheaf s).module)
  rightIsFiberH0OfDualDifferentials :
    Nonempty (
      ModuleCat.carrier right ≃ₗ[C.S.residueField s]
        ModuleCat.carrier (B.h0 (chapter04Tensor (D.dualOnTotalSpace.dual E.sheaf)
          D.dualizing.omega) s).module)
  perfectPairing : Chapter09PerfectPairing (C.S.residueField s)
    (ModuleCat.carrier left) (ModuleCat.carrier right)
  perfectPairing_eq_pairing : perfectPairing.pairing = pairing

def chapter14FiberwisePairingCompatibility
    {C : Chapter14RelativeCurveFamily}
    (D : Chapter14RelativeDualityData C) (E : Chapter14VectorBundle C.X)
    (B : Chapter14FiberCohomologyData C) : Prop :=
  ∀ s : C.S, Nonempty (Chapter14FiberwisePairingAt C D E B s)

theorem chapter14_relative_pairing_is_fiberwise_chapter12_pairing
    {C : Chapter14RelativeCurveFamily}
    (D : Chapter14RelativeDualityData C) (E : Chapter14VectorBundle C.X)
    (B : Chapter14FiberCohomologyData C) :
    chapter14FiberwisePairingCompatibility D E B := by
  sorry

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter14
