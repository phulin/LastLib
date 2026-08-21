import LastLib.Book05LocalClassFieldTheory.Chapter03.Core
import Mathlib.RepresentationTheory.Homological.FiniteCyclic

namespace LastLib.Book05LocalClassFieldTheory.Chapter03

noncomputable section

open CategoryTheory
open scoped BigOperators

/-! ## 3.1. Why cyclic extensions come first -/

/-- The canonical two-periodic group-ring resolution attached to a cyclic generator. -/
noncomputable def chapter03PeriodicResolution
    (G : Type) [CommGroup G] [Fintype G] (σ : G)
    (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) :=
  Rep.FiniteCyclicGroup.resolution (k := ℤ) (G := G) σ hσ

/-- The corresponding alternating complex after applying a representation. -/
noncomputable abbrev chapter03PeriodicModuleComplex
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) (σ : G) :=
  Rep.FiniteCyclicGroup.moduleCatChainComplex (k := ℤ) (G := G) A σ

/-- The additive norm map in the periodic complex. -/
abbrev chapter03PeriodicNormMap
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) :=
  letI : Module ℤ A.V := A.hV2
  A.norm.hom.toLinearMap

/-- The additive difference map in the periodic complex. -/
abbrev chapter03PeriodicDifferenceMap
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) (σ : G) :=
  letI : Module ℤ A.V := A.hV2
  (A.applyAsHom σ - 𝟙 A).hom.toLinearMap

theorem chapter03_periodic_norm_after_difference_eq_zero
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) (σ : G) :
    letI : Module ℤ A.V := A.hV2
    (chapter03PeriodicNormMap A).comp (chapter03PeriodicDifferenceMap A σ) = 0 := by
  have h := congrArg (fun f => f.hom)
    ((Rep.FiniteCyclicGroup.subCompNormHom (k := ℤ) (G := G) A σ).zero)
  simpa [chapter03PeriodicNormMap, chapter03PeriodicDifferenceMap] using h

theorem chapter03_periodic_difference_after_norm_eq_zero
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) (σ : G) :
    letI : Module ℤ A.V := A.hV2
    (chapter03PeriodicDifferenceMap A σ).comp (chapter03PeriodicNormMap A) = 0 := by
  have h := congrArg (fun f => f.hom)
    ((Rep.FiniteCyclicGroup.normHomCompSub (k := ℤ) (G := G) A σ).zero)
  simpa [chapter03PeriodicNormMap, chapter03PeriodicDifferenceMap] using h

theorem chapter03_periodic_complex_has_alternating_differentials
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) (σ : G) :
    letI : Module ℤ A.V := A.hV2
    (chapter03PeriodicNormMap A).comp (chapter03PeriodicDifferenceMap A σ) = 0 ∧
      (chapter03PeriodicDifferenceMap A σ).comp (chapter03PeriodicNormMap A) = 0 := by
  exact ⟨chapter03_periodic_norm_after_difference_eq_zero A σ,
    chapter03_periodic_difference_after_norm_eq_zero A σ⟩

noncomputable def chapter03_periodic_resolution_is_projective_resolution
    {G : Type} [CommGroup G] [Fintype G] (σ : G)
    (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) :
    ProjectiveResolution (Rep.trivial ℤ G ℤ) :=
  chapter03PeriodicResolution G σ hσ

theorem chapter03_difference_unit_is_multiplicative_action
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (σ : Gal(L/K)) (y : Lˣ) :
    (chapter03DifferenceUnit K L σ y : L) = σ (y : L) / (y : L) := by
  exact chapter03_difference_unit_apply K L σ y

theorem chapter03_norm_unit_is_field_norm
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : Lˣ) :
    (chapter03NormUnit K L x : K) = Algebra.norm K (x : L) := by
  exact chapter03_norm_unit_apply K L x

end

end LastLib.Book05LocalClassFieldTheory.Chapter03
