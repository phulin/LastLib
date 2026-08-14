import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.Dependencies

/-!
## 10.3 A table of descending properties

The table is exposed as individual declarations so downstream chapters can use the weakest
hypotheses for a particular morphism property.
-/

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

theorem chapter10_affine_fpqc_local_on_base :
    chapter10FpqcLocalOnBase (@IsAffineHom) := by
  sorry

theorem chapter10_quasiCompact_fpqc_local_on_base :
    chapter10FpqcLocalOnBase (@QuasiCompact) := by
  sorry

theorem chapter10_quasiSeparated_fpqc_local_on_base :
    chapter10FpqcLocalOnBase (@QuasiSeparated) := by
  sorry

theorem chapter10_separated_fpqc_local_on_base :
    chapter10FpqcLocalOnBase (@IsSeparated) := by
  sorry

theorem chapter10_locallyOfFiniteType_fpqc_local_on_base :
    chapter10FpqcLocalOnBase (@LocallyOfFiniteType) := by
  sorry

theorem chapter10_finiteType_fpqc_local_on_base :
    chapter10FpqcLocalOnBase (@chapter10FiniteType) := by
  sorry

theorem chapter10_locallyOfFinitePresentation_fpqc_local_on_base :
    chapter10FpqcLocalOnBase (@LocallyOfFinitePresentation) := by
  sorry

theorem chapter10_finitePresentation_fpqc_local_on_base :
    chapter10FpqcLocalOnBase (@chapter10FinitePresentation) := by
  sorry

theorem chapter10_flat_fpqc_local_on_base :
    chapter10FpqcLocalOnBase (@Flat) := by
  sorry

theorem chapter10_finiteLocallyFreeOfRank_fpqc_local_on_base (r : ℕ) :
    chapter10FpqcLocalOnBase (fun {X S} f => chapter10FiniteLocallyFreeOfRank f r) := by
  sorry

theorem chapter10_finite_fpqc_local_on_base :
    chapter10FpqcLocalOnBase (@IsFinite) := by
  sorry

theorem chapter10_monomorphism_fpqc_local_on_base :
    chapter10FpqcLocalOnBase (@monomorphisms Scheme.{u}) := by
  sorry

theorem chapter10_openImmersion_fpqc_local_on_base :
    chapter10FpqcLocalOnBase (@IsOpenImmersion) := by
  sorry

theorem chapter10_closedImmersion_fpqc_local_on_base :
    chapter10FpqcLocalOnBase (@IsClosedImmersion) := by
  sorry

theorem chapter10_locallyClosedImmersion_fpqc_local_on_base :
    chapter10FpqcLocalOnBase (@IsImmersion) := by
  sorry

theorem chapter10_proper_fpqc_local_on_base :
    chapter10FpqcLocalOnBase (@IsProper) := by
  sorry

theorem chapter10_smooth_fpqc_local_on_base :
    chapter10FpqcLocalOnBase (@Smooth) := by
  sorry

theorem chapter10_etale_fpqc_local_on_base :
    chapter10FpqcLocalOnBase (@Etale) := by
  sorry

theorem chapter10_unramified_fpqc_local_on_base :
    chapter10FpqcLocalOnBase (@chapter10Unramified) := by
  sorry

/-- The general bridge from a canonical Mathlib descent instance to the source-facing iff. -/
theorem chapter10_fpqc_local_of_descendsAlong
    (P : MorphismProperty Scheme.{u})
    (hP : chapter10StableUnderBaseChange P)
    (hdesc : P.DescendsAlong chapter10FpqcMorphismProperty) :
    chapter10FpqcLocalOnBase P := by
  sorry

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10
