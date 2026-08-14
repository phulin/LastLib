import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09.Core

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09

noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry

universe u

/-! ### 9.2 Dualizing sheaves on proper curves -/

/-- Proper Cohen--Macaulay curves over a field admit the Chapter 9 duality package. -/
theorem chapter09_proper_cm_curve_has_dualizing_sheaf
    (k : Type u) [Field k]
    (C : Chapter09CohenMacaulayCurveOverField k)
    [Chapter09ExtTheory C.scheme]
    [Chapter09AbsoluteDerivedHomTheory k C.scheme] :
    Nonempty (Chapter09AbsoluteDualizingData k C) := by
  sorry

/-- A proper Cohen--Macaulay curve over a field has a projective-space presentation. -/
theorem chapter09_proper_cm_curve_has_projective_embedding
    (k : Type u) [Field k]
    (C : Chapter09CohenMacaulayCurveOverField k) :
    Nonempty (Chapter09ProjectiveEmbedding k C) := by
  sorry

/-- The chosen dualizing sheaf can be obtained from a projective embedding by sheaf Ext. -/
theorem chapter09_dualizing_sheaf_from_projective_embedding
    (k : Type u) [Field k]
    (C : Chapter09CohenMacaulayCurveOverField k)
    (I : Chapter09ProjectiveEmbedding k C)
    [Chapter09ExtTheory I.ambient] :
    Nonempty (Chapter09AbsoluteExtConstruction k C I) := by
  sorry

/-- The codimension of a projective curve in `P^N` is `N - 1`. -/
theorem chapter09_projective_curve_pure_codimension
    (k : Type u) [Field k]
    (C : Chapter09CohenMacaulayCurveOverField k)
    (I : Chapter09ProjectiveEmbedding k C) :
    ∃ h : Chapter09FiniteLocallyFreeResolutionProfile
      (chapter09Pushforward I.embedding (chapter09StructureSheaf C.scheme)),
      h.pureCodimension ∧ h.codimension = I.N - 1 := by
  sorry

/-- The coefficient functional on Laurent monomials used by the Cech pairing. -/
def chapter09CoefficientOfInverseProduct
    {k : Type u} [Field k] {N : ℕ}
    (a b : Fin (N + 1) → ℤ) : Prop :=
  ∀ j, a j + b j = chapter09InverseProductExponent N j

/-- Laurent monomials pair the indicated Cech degrees by the inverse-product coefficient. -/
theorem chapter09_projective_space_laurent_monomial_pairing
    (k : Type u) [Field k] (N : ℕ) (m : ℤ) (q : ℕ) (hq : q ≤ N) :
    Nonempty (Chapter09ProjectiveCechPairing k N m q) := by
  sorry

/-- The coefficient convention in the Cech package is exactly
`(x₀ ⋯ x_N)⁻¹`, not an unspecified residue functional. -/
theorem chapter09_projective_space_pairing_uses_inverse_product
    (k : Type u) [Field k] (N : ℕ) (m : ℤ) (q : ℕ) (hq : q ≤ N)
    (P : Chapter09ProjectiveCechPairing k N m q) :
    P.coefficient_of_inverse_product := by
  sorry

/-- The projective resolution and change-of-rings pairing package for all coherent sheaves. -/
structure Chapter09ProjectiveCoherentPairingExtension
    (k : Type u) [Field k]
    (C : Chapter09CohenMacaulayCurveOverField k)
    (I : Chapter09ProjectiveEmbedding k C)
    [Chapter09ExtTheory C.scheme]
    [Chapter09ExtTheory I.ambient]
    [Chapter09AbsoluteDerivedHomTheory k C.scheme] where
  construction : Chapter09AbsoluteExtConstruction k C I
  pairing :
    ∀ (F : C.scheme.Modules) (i : ℕ),
      chapter09Coherent F → i ≤ 1 →
        Chapter09PerfectPairing k (chapter09H F i)
          (chapter09Ext F construction.dualizingSheaf (1 - i))

/-- Finite locally free resolutions extend the projective-space pairing to coherent sheaves. -/
theorem chapter09_projective_pairing_extends_to_coherent_sheaves
    (k : Type u) [Field k]
    (C : Chapter09CohenMacaulayCurveOverField k)
    (I : Chapter09ProjectiveEmbedding k C)
    [Chapter09ExtTheory C.scheme]
    [Chapter09ExtTheory I.ambient]
    [Chapter09AbsoluteDerivedHomTheory k C.scheme] :
    Nonempty (Chapter09ProjectiveCoherentPairingExtension k C I) := by
  sorry

/-- The change-of-rings identification is concentrated in codimension `N - 1`. -/
theorem chapter09_change_of_rings_identifies_curve_ext
    (k : Type u) [Field k]
    (C : Chapter09CohenMacaulayCurveOverField k)
    (I : Chapter09ProjectiveEmbedding k C)
    [Chapter09ExtTheory I.ambient]
    (hresolution :
      Chapter09FiniteLocallyFreeResolutionProfile
        (chapter09Pushforward I.embedding (chapter09StructureSheaf C.scheme))) :
    hresolution.pureCodimension ∧ hresolution.codimension = I.N - 1 := by
  sorry

theorem chapter09_projective_ext_construction_has_change_of_rings_identification
    (k : Type u) [Field k]
    (C : Chapter09CohenMacaulayCurveOverField k)
    (I : Chapter09ProjectiveEmbedding k C)
    [Chapter09ExtTheory I.ambient]
    (D : Chapter09AbsoluteExtConstruction k C I) :
    D.changeOfRingsIdentification := by
  sorry

/-- The natural shifted derived duality comparison, formula (9.2). -/
def chapter09_absolute_derived_duality
    (k : Type u) [Field k]
    (C : Chapter09CohenMacaulayCurveOverField k)
    [Chapter09ExtTheory C.scheme]
    [Chapter09AbsoluteDerivedHomTheory k C.scheme]
    (D : Chapter09AbsoluteDualizingData k C)
    (F : C.scheme.Modules) (hF : chapter09Coherent F) :
    Chapter09AbsoluteDerivedDualityComparison k F D.sheaf := by
  exact D.derivedDuality F hF

/-- The unit class in (9.2) gives the global trace functional. -/
theorem chapter09_trace_is_the_image_of_one
    (k : Type u) [Field k]
    (C : Chapter09CohenMacaulayCurveOverField k)
    [Chapter09ExtTheory C.scheme]
    [Chapter09AbsoluteDerivedHomTheory k C.scheme]
    (D : Chapter09AbsoluteDualizingData k C) :
    D.trace_is_image_of_one := by
  sorry

/-- Degree zero of the derived comparison gives the zero-dimensional formula (9.1). -/
theorem chapter09_zero_dimensional_ext_dual
    (k : Type u) [Field k]
    (C : Chapter09CohenMacaulayCurveOverField k)
    [Chapter09ExtTheory C.scheme]
    [Chapter09AbsoluteDerivedHomTheory k C.scheme]
    (D : Chapter09AbsoluteDualizingData k C)
    (T : C.scheme.Modules) (hT : chapter09ZeroDimensional T) :
    Nonempty (chapter09Ext T D.sheaf 1 ≃ chapter09Dual k (chapter09H T 0)) := by
  exact D.zeroDimensionalExt T hT

/-- The same zero-dimensional identification with the field-linear dual. -/
theorem chapter09_zero_dimensional_ext_linear_dual
    (k : Type u) [Field k]
    (C : Chapter09CohenMacaulayCurveOverField k)
    [Chapter09ExtTheory C.scheme]
    [Chapter09AbsoluteDerivedHomTheory k C.scheme]
    (D : Chapter09AbsoluteDualizingData k C)
    (T : C.scheme.Modules) (hT : chapter09ZeroDimensional T) :
    ∃ hTmodule : Module k (chapter09H T 0),
      ∃ hExt : Module k (chapter09Ext T D.sheaf 1),
        @Nonempty
          (letI : Module k (chapter09H T 0) := hTmodule
           letI : Module k (chapter09Ext T D.sheaf 1) := hExt
           chapter09Ext T D.sheaf 1 ≃ₗ[k] chapter09LinearDual k (chapter09H T 0)) := by
  exact D.zeroDimensionalLinearExt T hT

/-- Cohomology of the derived comparison recovers the full perfect pairing. -/
def chapter09_absolute_duality_full_perfect_pairing
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

/-- Independence of the chosen projective embedding, with comparison on the curve. -/
structure Chapter09EmbeddingIndependenceComparison
    (k : Type u) [Field k]
    (C : Chapter09CohenMacaulayCurveOverField k)
    (I J : Chapter09ProjectiveEmbedding k C)
    [Chapter09ExtTheory I.ambient] [Chapter09ExtTheory J.ambient] where
  inducedDualizingIso :
    ∀ (DI : Chapter09AbsoluteExtConstruction k C I)
      (DJ : Chapter09AbsoluteExtConstruction k C J),
      Nonempty (DI.dualizingSheaf ≅ DJ.dualizingSheaf)
  representsTheSameFunctor : Prop
  traceCompatible : Prop
  comparisonUnique : Prop
  cocycle : Prop

/-- Two projective constructions represent the same duality functor. -/
theorem chapter09_dualizing_construction_independent_of_embedding
    (k : Type u) [Field k]
    (C : Chapter09CohenMacaulayCurveOverField k)
    (I J : Chapter09ProjectiveEmbedding k C)
    [Chapter09ExtTheory I.ambient] [Chapter09ExtTheory J.ambient] :
    Nonempty (Chapter09EmbeddingIndependenceComparison k C I J) := by
  sorry

/-- A Cohen--Macaulay curve has no embedded zero-dimensional components. -/
structure Chapter09EmbeddedZeroDimensionalComponent (X : Scheme.{u}) where
  component : Prop
  embedded : Prop
  zeroDimensional : Prop

def chapter09HasEmbeddedZeroDimensionalComponent (X : Scheme.{u}) : Prop :=
  ∃ h : Chapter09EmbeddedZeroDimensionalComponent X, h.component ∧ h.embedded ∧
    h.zeroDimensional

theorem chapter09_cm_excludes_embedded_zero_dimensional_components
    (k : Type u) [Field k]
    (C : Chapter09CohenMacaulayCurveOverField k) :
    ¬ chapter09HasEmbeddedZeroDimensionalComponent C.scheme := by
  sorry

/-- Without Cohen--Macaulayness, duality is represented in more than one sheaf degree. -/
structure Chapter09NonCohenMacaulayDualityWarning (X : Scheme.{u}) where
  notCohenMacaulay : ¬ chapter09CohenMacaulay X
  multipleSheafDegrees : Prop
  noSingleDualizingSheafEncodesAllDuality : Prop

theorem chapter09_non_cm_duality_needs_multiple_sheaf_degrees
    {X : Scheme.{u}} (W : Chapter09NonCohenMacaulayDualityWarning X) :
    W.multipleSheafDegrees := by
  sorry

/-- A pure reduced curve is Cohen--Macaulay in the one-dimensional case. -/
structure Chapter09PureReducedCurve (X : Scheme.{u}) where
  reduced : IsReduced X
  locallyNoetherian : IsLocallyNoetherian X
  pureDimensionOne : Prop
  localRingsDimensionOne : Prop
  nonZeroDivisorAvoidingMinimalPrimes : Prop

theorem chapter09_pure_reduced_curve_is_cohen_macaulay
    {X : Scheme.{u}} (C : Chapter09PureReducedCurve X) :
    chapter09CohenMacaulay X := by
  sorry

/-! ### Gorenstein consequences and the non-Gorenstein warning -/

/-- For a proper Cohen--Macaulay curve, Gorensteinness is exactly invertibility of `ω`. -/
theorem chapter09_absolute_gorenstein_iff_invertible
    (k : Type u) [Field k]
    (C : Chapter09CohenMacaulayCurveOverField k)
    [Chapter09ExtTheory C.scheme]
    [Chapter09AbsoluteDerivedHomTheory k C.scheme]
    (D : Chapter09AbsoluteDualizingData k C) :
    chapter09AbsoluteGorenstein k C D ↔ chapter09IsInvertible D.sheaf :=
  Iff.rfl

/-- Smooth proper curves are Gorenstein. -/
theorem chapter09_smooth_curve_is_gorenstein
    (k : Type u) [Field k]
    (C : Chapter09CohenMacaulayCurveOverField k)
    [Smooth C.structureMap]
    [Chapter09ExtTheory C.scheme]
    [Chapter09AbsoluteDerivedHomTheory k C.scheme]
    (D : Chapter09AbsoluteDualizingData k C) :
    chapter09AbsoluteGorenstein k C D := by
  sorry

/-- Absolute local complete intersections of pure dimension one are Gorenstein. -/
theorem chapter09_lci_curve_is_gorenstein
    (k : Type u) [Field k]
    (C : Chapter09CohenMacaulayCurveOverField k)
    (L : Chapter09RelativeLocalCompleteIntersection C.structureMap)
    [Chapter09ExtTheory C.scheme]
    [Chapter09AbsoluteDerivedHomTheory k C.scheme]
    (D : Chapter09AbsoluteDualizingData k C) :
    chapter09AbsoluteGorenstein k C D := by
  sorry

/-- A nodal proper curve is Gorenstein. -/
structure Chapter09NodalCurve
    (k : Type u) [Field k]
    (C : Chapter09CohenMacaulayCurveOverField k) where
  localNodeModel : Prop

theorem chapter09_nodal_curve_is_gorenstein
    (k : Type u) [Field k]
    (C : Chapter09CohenMacaulayCurveOverField k)
    (N : Chapter09NodalCurve k C)
    [Chapter09ExtTheory C.scheme]
    [Chapter09AbsoluteDerivedHomTheory k C.scheme]
    (D : Chapter09AbsoluteDualizingData k C) :
    chapter09AbsoluteGorenstein k C D := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the pinned revision has no canonical local
non-Gorenstein curve example or torsion-free-rank-one sheaf predicate. -/
/-- A reduced curve may have a torsion-free rank-one dualizing sheaf that is not invertible. -/
structure Chapter09ReducedNonGorensteinCurve
    (k : Type u) [Field k]
    (C : Chapter09CohenMacaulayCurveOverField k)
    [Chapter09ExtTheory C.scheme]
    [Chapter09AbsoluteDerivedHomTheory k C.scheme] where
  reduced : IsReduced C.scheme
  dualizing : Chapter09AbsoluteDualizingData k C
  torsionFreeRankOne : Prop
  notInvertible : ¬ chapter09IsInvertible dualizing.sheaf
  canonicalCartierFormulasRequireModification : Prop

theorem chapter09_reduced_curve_need_not_be_gorenstein
    (k : Type u) [Field k]
    (C : Chapter09CohenMacaulayCurveOverField k)
    [Chapter09ExtTheory C.scheme]
    [Chapter09AbsoluteDerivedHomTheory k C.scheme]
    (W : Chapter09ReducedNonGorensteinCurve k C) :
    ¬ chapter09AbsoluteGorenstein k C W.dualizing := by
  exact W.notInvertible

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09
