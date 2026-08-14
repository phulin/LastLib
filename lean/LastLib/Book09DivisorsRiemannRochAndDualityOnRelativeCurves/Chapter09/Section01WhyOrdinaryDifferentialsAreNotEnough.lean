import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09.Core

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09

noncomputable section

open CategoryTheory
open AlgebraicGeometry

universe u

/-! ### 9.1 Why ordinary differentials are not enough -/

/-- The trace functional required of a dualizing sheaf on a proper curve. -/
structure Chapter09TraceFunctional
    (k : Type u) [Field k] {X : Scheme.{u}} (ω : X.Modules) where
  trace : chapter09H ω 1 → k

/-- The two roles of regular differentials on a smooth curve. -/
structure Chapter09SmoothDifferentialRoles
    (k : Type u) [Field k]
  (C : Chapter09ProperCurveOverField k) where
  differentials : C.scheme.Modules
  isRelativeDifferentials : Prop
  firstOrderForms : Prop
  dualToH1StructureSheaf : Prop

theorem chapter09_smooth_differentials_have_both_roles
    (k : Type u) [Field k]
    (C : Chapter09ProperCurveOverField k)
    [Smooth C.structureMap] :
    Nonempty (Chapter09SmoothDifferentialRoles k C) := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the pinned scheme API has no node predicate or
Kähler-differential module sheaf, so the node condition is kept as a named
hypothesis while the non-invertibility assertion remains a theorem. -/
/-- The local warning that Kähler differentials at a node need not be invertible. -/
structure Chapter09NodeDifferentialFailure (X : Scheme.{u}) where
  node : X
  isNode : Prop
  kahlerDifferentials : X.Modules
  doesNotRepresentDuality : Prop

theorem chapter09_node_differentials_not_invertible
    {X : Scheme.{u}} (W : Chapter09NodeDifferentialFailure X) :
    ¬ chapter09IsInvertible W.kahlerDifferentials := by
  sorry

theorem chapter09_node_differentials_do_not_represent_duality
    {X : Scheme.{u}} (W : Chapter09NodeDifferentialFailure X) :
    W.doesNotRepresentDuality := by
  sorry

/-- The multiplication/trace pairing for a coherent sheaf, in the range `i = 0, 1`. -/
def chapter09_multiplication_followed_by_trace_is_perfect
    (k : Type u) [Field k]
    (C : Chapter09CohenMacaulayCurveOverField k)
    [Chapter09ExtTheory C.scheme]
    [Chapter09AbsoluteDerivedHomTheory k C.scheme]
    (D : Chapter09AbsoluteDualizingData k C)
    (F : C.scheme.Modules) (i : ℕ)
    (hF : chapter09Coherent F) (hi : i ≤ 1) :
    Chapter09PerfectPairing k (chapter09H F i)
      (chapter09Ext F D.sheaf (1 - i)) := by
  exact D.perfectPairing F i hF hi

/-- The perfect pairing can be retained in its field-linear form. -/
theorem chapter09_multiplication_followed_by_trace_is_linearly_perfect
    (k : Type u) [Field k]
    (C : Chapter09CohenMacaulayCurveOverField k)
    [Chapter09ExtTheory C.scheme]
    [Chapter09AbsoluteDerivedHomTheory k C.scheme]
    (D : Chapter09AbsoluteDualizingData k C)
    (F : C.scheme.Modules) (i : ℕ)
    (hF : chapter09Coherent F) (hi : i ≤ 1) :
    ∃ hFmodule : Module k (chapter09H F i),
      ∃ hExt : Module k (chapter09Ext F D.sheaf (1 - i)),
        @Nonempty
          (letI : Module k (chapter09H F i) := hFmodule
           letI : Module k (chapter09Ext F D.sheaf (1 - i)) := hExt
           Chapter09LinearPerfectPairing k (chapter09H F i)
             (chapter09Ext F D.sheaf (1 - i))) := by
  exact D.linearPerfectPairing F i hF hi

/-- A book-facing statement of the trace pairing before identifying the second factor. -/
structure Chapter09TracePairingStatement
    (k : Type u) [Field k]
    {X : Scheme.{u}} [Chapter09ExtTheory X]
    (ω F : X.Modules) (i : ℕ) where
  trace : chapter09H ω 1 → k
  multiplicationPairing : chapter09H F i → chapter09Ext F ω (1 - i) → k
  pairing_is_multiplication_then_trace : Prop
  perfect :
    Chapter09PerfectPairing k (chapter09H F i) (chapter09Ext F ω (1 - i))

/-- For a vector bundle, the Ext factor is represented by cohomology of `E^∨ ⊗ ω`. -/
def chapter09_vector_bundle_second_factor_is_cohomology
    (k : Type u) [Field k]
    (C : Chapter09CohenMacaulayCurveOverField k)
    [Chapter09ExtTheory C.scheme]
    [Chapter09AbsoluteDerivedHomTheory k C.scheme]
    (D : Chapter09AbsoluteDualizingData k C)
    (E : C.scheme.Modules)
    (V : Chapter09VectorBundleDualTensor E D.sheaf)
    (hE : chapter09VectorBundle E) (i : ℕ) (hi : i ≤ 1) :
    Chapter09PerfectPairing k (chapter09H E i)
      (chapter09H V.tensor (1 - i)) := by
  exact D.vectorBundlePairing E V hE i hi

/-- The representing dualizing sheaf is unique up to a trace-compatible isomorphism. -/
theorem chapter09_dualizing_sheaf_unique_up_to_trace
    (k : Type u) [Field k]
    (C : Chapter09CohenMacaulayCurveOverField k)
    [Chapter09ExtTheory C.scheme]
    [Chapter09AbsoluteDerivedHomTheory k C.scheme]
    (D E : Chapter09AbsoluteDualizingData k C) :
    Nonempty
      (Chapter09TraceCompatibleIso k D.sheaf E.sheaf D.trace E.trace) := by
  sorry

/-- Compatibility with the trace makes the comparison isomorphism unique. -/
theorem chapter09_trace_compatible_comparison_unique
    (k : Type u) [Field k]
    (C : Chapter09CohenMacaulayCurveOverField k)
    [Chapter09ExtTheory C.scheme]
    [Chapter09AbsoluteDerivedHomTheory k C.scheme]
    (D E : Chapter09AbsoluteDualizingData k C)
    (e e' : Chapter09TraceCompatibleIso k D.sheaf E.sheaf D.trace E.trace) :
    e.iso = e'.iso := by
  sorry

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09
