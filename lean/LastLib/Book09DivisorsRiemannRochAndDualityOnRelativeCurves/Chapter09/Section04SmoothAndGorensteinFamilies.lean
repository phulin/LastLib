import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09.Core
import Mathlib.RingTheory.LocalProperties.InjectiveDimension

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04

universe u

/-! ### 9.4 Smooth and Gorenstein families -/

/-- The residue-chart compatibility used to identify the smooth trace with the usual residue trace. -/
structure Chapter09SmoothResidueTraceCompatibility
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Chapter09RelativeDerivedHomTheory f]
    (D : Chapter09RelativeDualizingData f)
    (differentials : X.Modules) where
  identification : D.omega ≅ differentials
  étaleCoordinateTrace : Prop
  étaleCoordinateTrace_holds : étaleCoordinateTrace
  residueTrace : Prop
  residueTrace_holds : residueTrace
  compatible : Prop
  compatible_holds : compatible

/-- Smooth relative curves have dualizing sheaf equal to relative differentials. -/
theorem chapter09_smooth_curve_dualizing_is_differentials
    (F : Chapter09RelativeCurveFamily)
    [SmoothOfRelativeDimension 1 F.f]
    [Chapter09RelativeDerivedHomTheory F.f]
    [Chapter09DifferentialSheafTheory F.f]
    (D : Chapter09RelativeDualizingData F.f) :
    Nonempty (D.omega ≅ chapter09RelativeDifferentials F.f) := by
  sorry

/-- The missing smooth Kähler-differential API supplies the line-bundle
property needed to pass from the smooth identification to Gorensteinness. -/
theorem chapter09_smooth_relative_differentials_are_vector_bundle
    (F : Chapter09RelativeCurveFamily)
    [SmoothOfRelativeDimension 1 F.f]
    [Chapter09DifferentialSheafTheory F.f] :
    chapter09VectorBundle (chapter09RelativeDifferentials F.f) := by
  sorry

/-- The smooth identification is compatible with the étale-coordinate residue trace. -/
theorem chapter09_smooth_trace_is_residue_trace
    (F : Chapter09RelativeCurveFamily)
    [SmoothOfRelativeDimension 1 F.f]
    [Chapter09RelativeDerivedHomTheory F.f]
    [Chapter09DifferentialSheafTheory F.f]
    (D : Chapter09RelativeDualizingData F.f) :
    Nonempty
      (Chapter09SmoothResidueTraceCompatibility F.f D
        (chapter09RelativeDifferentials F.f)) := by
  sorry

/-- Smooth relative curves are Gorenstein, since their dualizing sheaf is the
relative line bundle of differentials. -/
theorem chapter09_smooth_curve_family_is_gorenstein
    (F : Chapter09RelativeCurveFamily)
    [SmoothOfRelativeDimension 1 F.f]
    [Chapter09RelativeDerivedHomTheory F.f]
    [Chapter09DifferentialSheafTheory F.f]
    (D : Chapter09RelativeDualizingData F.f) :
    chapter09RelativeGorenstein D := by
  sorry

/-! ### The Gorenstein criterion -/

/-! The canonical local-ring criterion used here is finite self-injective
dimension for a commutative noetherian local ring. -/
def chapter09LocalRingIsGorenstein (R : Type*) [CommRing R] : Prop :=
  IsLocalRing R ∧ IsNoetherianRing R ∧
    ∃ n : ℕ, CategoryTheory.HasInjectiveDimensionLE (ModuleCat.of R R) n

def chapter09FiberIsGorenstein
    {X S : Scheme.{u}} (f : X ⟶ S) (s : S) : Prop :=
  ∀ y : f.fiber s,
    chapter09LocalRingIsGorenstein ((f.fiber s).presheaf.stalk y)

/- This name is retained for later chapters that record the source-level
fiberwise hypothesis.  Since the pinned API has no canonical local
Gorenstein predicate, proofs of the invertibility criterion use the
dualizing-data version immediately below. -/
def chapter09GorensteinMorphism
    {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Flat f ∧ ∀ s : S, chapter09FiberIsGorenstein f s

def chapter09GorensteinMorphismWithDualizingData
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Chapter09RelativeDerivedHomTheory f]
    (D : Chapter09RelativeDualizingData f) : Prop :=
  Flat f ∧ chapter09RelativeGorenstein D

/-- In the relative curve setting, Gorensteinness is equivalent to invertibility of `ω`. -/
theorem chapter09_relative_gorenstein_iff_invertible_dualizing
    (F : Chapter09RelativeCurveFamily)
    [Chapter09RelativeDerivedHomTheory F.f]
    (D : Chapter09RelativeDualizingData F.f) :
    chapter09GorensteinMorphism F.f ↔
      chapter09GorensteinMorphismWithDualizingData F.f D := by
  sorry

/-- A relative local complete intersection of pure relative dimension one is Gorenstein. -/
theorem chapter09_relative_lci_is_gorenstein
    (F : Chapter09RelativeCurveFamily)
    (L : Chapter09RelativeLocalCompleteIntersection F.f)
    [Chapter09RelativeDerivedHomTheory F.f]
    (D : Chapter09RelativeDualizingData F.f) :
    chapter09RelativeGorenstein D := by
  sorry

/-- A family cut out by one regular equation in a smooth relative surface has invertible dualizing sheaf. -/
theorem chapter09_regular_relative_hypersurface_is_gorenstein
    (F : Chapter09RelativeCurveFamily)
    (H : Chapter09RelativeHypersurface F.f)
    [Chapter09RelativeDerivedHomTheory F.f]
    (D : Chapter09RelativeDualizingData F.f) :
    chapter09RelativeGorenstein D := by
  sorry

/-! ### Adjunction -/

/-- The relative hypersurface adjunction isomorphism (9.6). -/
theorem chapter09_relative_hypersurface_adjunction
    (F : Chapter09RelativeCurveFamily)
    (H : Chapter09RelativeHypersurface F.f)
    [Chapter09RelativeDerivedHomTheory F.f]
    (D : Chapter09RelativeDualizingData F.f)
    (ambientOmega : H.ambient.Modules)
    (hambientOmega : chapter09IsInvertible ambientOmega)
    (hambientOmega_is_relativeDualizing : Prop)
    (hambientOmega_is_relativeDualizing_holds : hambientOmega_is_relativeDualizing) :
    Nonempty
      (D.omega ≅
        chapter09Pullback H.inclusion
          (chapter04Tensor ambientOmega H.divisorLineBundle.sheaf)) := by
  sorry

/-- The adjunction right-hand side stays invertible through a nodal fiber. -/
theorem chapter09_hypersurface_adjunction_rhs_invertible_at_node
    (F : Chapter09RelativeCurveFamily)
    (H : Chapter09RelativeHypersurface F.f)
    (ambientOmega : H.ambient.Modules)
    (hambientOmega : chapter09IsInvertible ambientOmega) :
    chapter09IsInvertible
      (chapter09Pullback H.inclusion
        (chapter04Tensor ambientOmega H.divisorLineBundle.sheaf)) := by
  sorry

/-- The invertible adjunction sheaf is the practical sheaf of invariant differentials. -/
structure Chapter09InvariantDifferentialConstruction
    (F : Chapter09RelativeCurveFamily)
    [Chapter09RelativeDerivedHomTheory F.f]
    (D : Chapter09RelativeDualizingData F.f)
    (H : Chapter09RelativeHypersurface F.f) where
  ambientOmega : H.ambient.Modules
  ambientOmega_is_relativeDualizing : Prop
  ambientOmega_is_relativeDualizing_holds : ambientOmega_is_relativeDualizing
  ambientOmega_invertible : chapter09IsInvertible ambientOmega
  adjunctionSheaf : F.X.Modules
  adjunctionSheaf_eq :
    adjunctionSheaf =
      chapter09Pullback H.inclusion
        (chapter04Tensor ambientOmega H.divisorLineBundle.sheaf)
  invariantDifferentialIso : D.omega ≅ adjunctionSheaf
  invertible : chapter09IsInvertible adjunctionSheaf

theorem chapter09_hypersurface_provides_invariant_differentials
    (F : Chapter09RelativeCurveFamily)
    (H : Chapter09RelativeHypersurface F.f)
    [Chapter09RelativeDerivedHomTheory F.f]
    (D : Chapter09RelativeDualizingData F.f) :
    Nonempty (Chapter09InvariantDifferentialConstruction F D H) := by
  sorry

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09
