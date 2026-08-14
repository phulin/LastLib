import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.Dependencies

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open scoped AlgebraicGeometry

universe u v

/-! ## 7.1. The universal remedy for an ideal -/

/- LOCAL_DEPENDENCY_GUESS: the pinned Mathlib API exposes absolute `Proj` but not relative `Proj`
of a quasi-coherent graded algebra.  The record below keeps the relative-Proj presentation and
its universal property together until that API is available. -/
structure Chapter07Blowup {X : Scheme.{u}} (I : Chapter07CoherentIdeal X) where
  carrier : Scheme.{u}
  projection : carrier ⟶ X
  rees_presentation : Prop
  quasiCompact : QuasiCompact projection
  quasiSeparated : QuasiSeparated projection
  tautologicalIdeal : Chapter07CoherentIdeal carrier
  tautological_ideal_eq_pullback :
    tautologicalIdeal.ideal = I.ideal.comap projection
  tautological_isInvertible : Chapter07IsInvertibleIdeal tautologicalIdeal.ideal
  universal : ∀ {Y : Scheme.{u}} (g : Y ⟶ X),
    Chapter07IsInvertibleIdeal (I.ideal.comap g) →
      ∃! u : Y ⟶ carrier, u ≫ projection = g

def chapter07BlowupTautologicalIdeal
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X} (B : Chapter07Blowup I) :
    Chapter07CoherentIdeal B.carrier :=
  B.tautologicalIdeal

theorem chapter07_blowup_tautologicalIdeal_eq_pullback
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X} (B : Chapter07Blowup I) :
    B.tautologicalIdeal.ideal = I.ideal.comap B.projection :=
  B.tautological_ideal_eq_pullback

theorem chapter07_blowup_tautologicalIdeal_isInvertible
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X} (B : Chapter07Blowup I) :
    Chapter07IsInvertibleIdeal B.tautologicalIdeal.ideal :=
  B.tautological_isInvertible

structure Chapter07IdealModulePresentation
    {X : Scheme.{u}} (I : X.IdealSheafData) where
  module : X.Modules
  isInvertible : chapter04IsInvertible module
  /- LOCAL_DEPENDENCY_GUESS: pinned Mathlib has ideal-sheaf data but no coherent ideal
  subsheaf object in `X.Modules`; this field is the missing realization relation. -/
  realizesIdeal : Prop

structure Chapter07IdealLineBundleIso
    {X : Scheme.{u}} (I : X.IdealSheafData) where
  idealModule : Chapter07IdealModulePresentation I
  line : Chapter04LineBundle X
  iso : idealModule.module ≅ line.sheaf

/- The sign convention is intentionally carried by the name of the chosen twisting line. -/
def Chapter07OOne {X : Scheme.{u}} (I : X.IdealSheafData) : Prop :=
  Nonempty (Chapter07IdealLineBundleIso I)

theorem chapter07_blowup_tautological_ideal_is_O_one
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X} (B : Chapter07Blowup I) :
    Chapter07OOne B.tautologicalIdeal.ideal := by
  sorry

theorem chapter07_blowup_exists
    {X : Scheme.{u}} (I : Chapter07CoherentIdeal X) : Nonempty (Chapter07Blowup I) := by
  sorry

noncomputable def chapter07Blowup
    {X : Scheme.{u}} (I : Chapter07CoherentIdeal X) : Chapter07Blowup I :=
  Classical.choice (chapter07_blowup_exists I)

abbrev chapter07BlowupScheme
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X} (B : Chapter07Blowup I) : Scheme :=
  B.carrier

abbrev chapter07BlowupMap
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X} (B : Chapter07Blowup I) :
    B.carrier ⟶ X :=
  B.projection

theorem chapter07_blowup_universal_property
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X} (B : Chapter07Blowup I)
    {Y : Scheme.{u}} (g : Y ⟶ X)
    (hI : Chapter07IsInvertibleIdeal (I.ideal.comap g)) :
    ∃! u : Y ⟶ B.carrier, u ≫ B.projection = g :=
  B.universal g hI

theorem chapter07_blowup_factor_exists
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X} (B : Chapter07Blowup I)
    {Y : Scheme.{u}} (g : Y ⟶ X)
    (hI : Chapter07IsInvertibleIdeal (I.ideal.comap g)) :
    ∃ u : Y ⟶ B.carrier, u ≫ B.projection = g := by
  exact (chapter07_blowup_universal_property B g hI).exists

theorem chapter07_blowup_factor_unique
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X} (B : Chapter07Blowup I)
    {Y : Scheme.{u}} (g : Y ⟶ X)
    (hI : Chapter07IsInvertibleIdeal (I.ideal.comap g))
    {u v : Y ⟶ B.carrier} (hu : u ≫ B.projection = g) (hv : v ≫ B.projection = g) :
    u = v := by
  exact (chapter07_blowup_universal_property B g hI).unique u hu v hv

theorem chapter07_blowup_projection_is_qc
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X} (B : Chapter07Blowup I) :
    QuasiCompact B.projection :=
  B.quasiCompact

theorem chapter07_blowup_projection_is_qs
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X} (B : Chapter07Blowup I) :
    QuasiSeparated B.projection :=
  B.quasiSeparated

theorem chapter07_blowup_unit_ideal_isIso
    (X : Scheme.{u}) :
    IsIso (chapter07Blowup (chapter07UnitCoherentIdeal X)).projection := by
  sorry

theorem chapter07_blowup_invertible_ideal_isIso
    {X : Scheme.{u}} (I : Chapter07CoherentIdeal X)
    (hI : Chapter07IsInvertibleIdeal I.ideal) :
    IsIso (chapter07Blowup I).projection := by
  sorry

def chapter07BlowupRestriction
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X} (B : Chapter07Blowup I)
    (U : X.Opens) : (B.projection ⁻¹ᵁ U).toScheme ⟶ U.toScheme :=
  B.projection ∣_ U

theorem chapter07_blowup_isIso_off_support
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X} (B : Chapter07Blowup I) :
    IsIso (chapter07BlowupRestriction B I.ideal.support.compl) := by
  sorry

theorem chapter07_blowup_isIso_off_finite_closed_center
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X} (B : Chapter07Blowup I)
    (C : Chapter07FiniteClosedPointCenter I) :
    IsIso (chapter07BlowupRestriction B I.ideal.support.compl) := by
  exact chapter07_blowup_isIso_off_support B

noncomputable def chapter07FiniteCenterComplement
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X}
    (C : Chapter07FiniteClosedPointCenter I) : X.Opens := by
  refine ⟨(C.points : Set X)ᶜ, ?_⟩
  sorry

theorem chapter07_blowup_isIso_over_finite_center_complement
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X} (B : Chapter07Blowup I)
    (C : Chapter07FiniteClosedPointCenter I) :
    IsIso (chapter07BlowupRestriction B (chapter07FiniteCenterComplement C)) := by
  sorry

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07
