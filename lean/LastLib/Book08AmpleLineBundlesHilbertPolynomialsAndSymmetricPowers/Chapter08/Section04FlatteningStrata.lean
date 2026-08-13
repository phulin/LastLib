import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08.Dependencies

namespace LastLib
namespace Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers
namespace Chapter08

open AlgebraicGeometry CategoryTheory

noncomputable section

/-! ## 8.4 Flattening strata -/

/- The universal property of a flattening stratum, including nilpotent test
   schemes. -/
structure Chapter08FlatteningStratumData
    {F : Chapter08PolarizedFamily} (E : Chapter08FamilySheaf F)
    (D : Chapter08FiberwiseHilbertData E)
    (B : Chapter08BaseChangeHilbertData E D)
    (P : Chapter08NumericalPolynomial) where
  stratum : Chapter08FlatteningStratum F.family.S
  factors_iff :
    ∀ {T : Scheme} (t : T ⟶ F.family.S),
      Chapter08BaseChangeHasFlatPolynomial E B t P ↔
        ∃ g : T ⟶ stratum.stratum, g ≫ stratum.inclusion = t

/- The inclusion of a stratum has its book-facing immersion instance. -/
instance {F : Chapter08PolarizedFamily} {E : Chapter08FamilySheaf F}
    {H : Chapter08FiberwiseHilbertData E}
    {B : Chapter08BaseChangeHilbertData E H} {P : Chapter08NumericalPolynomial}
    (D : Chapter08FlatteningStratumData E H B P) :
    IsImmersion D.stratum.inclusion := D.stratum.immersion

theorem chapter08_flattening_stratum_is_locally_closed
    {S : Scheme} (D : Chapter08FlatteningStratum S) :
    IsLocallyClosed (Set.range D.inclusion) := by
  exact @Scheme.Hom.isLocallyClosed_range _ _ D.inclusion D.immersion

/- LOCAL_DEPENDENCY_GUESS: the canonical flattening-stratification theorem and
   its Fitting-ideal construction are absent from the pinned Mathlib API. -/
theorem chapter08_flattening_stratum
    {F : Chapter08PolarizedFamily} (E : Chapter08FamilySheaf F)
    (D : Chapter08FiberwiseHilbertData E)
    (B : Chapter08BaseChangeHilbertData E D)
    (hnoetherian : IsNoetherian F.family.S)
    (hveryample : Chapter08RelativelyVeryAmple F.family.f F.lineBundle
      F.lineBundle_invertible.is_invertible)
    (P : Chapter08NumericalPolynomial) :
    Nonempty (Chapter08FlatteningStratumData E D B P) := by
  sorry

/- The numerical flatness criterion uses the flattening theorem above.  It is
   placed in this file so the formal dependency order matches that proof route;
   the locally noetherian statement is obtained by applying the construction
   on affine noetherian neighborhoods. -/
theorem chapter08_numerical_flatness_iff
    {F : Chapter08PolarizedFamily} (E : Chapter08FamilySheaf F)
    (D : Chapter08FiberwiseHilbertData E)
    (hred : IsReduced F.family.S) :
    Chapter08FlatOver F.family.f E.sheaf ↔
      Chapter08LocallyConstant (fun s => D.fiberPolynomial s) := by
  sorry

/- Every point of the base lies on a stratum for some numerical polynomial. -/
theorem chapter08_flattening_strata_cover
    {F : Chapter08PolarizedFamily} (E : Chapter08FamilySheaf F)
    (D : Chapter08FiberwiseHilbertData E)
    (B : Chapter08BaseChangeHilbertData E D)
    (hnoetherian : IsNoetherian F.family.S)
    (hveryample : Chapter08RelativelyVeryAmple F.family.f F.lineBundle
      F.lineBundle_invertible.is_invertible) :
    ∀ s : F.family.S,
      ∃ P : Chapter08NumericalPolynomial,
        ∃ H : Chapter08FlatteningStratumData E D B P,
          ∃ x : H.stratum.stratum, H.stratum.inclusion x = s := by
  sorry

/- Only finitely many strata meet a quasi-compact open subset of the base. -/
theorem chapter08_flattening_strata_finite_on_quasi_compact_open
    {F : Chapter08PolarizedFamily} (E : Chapter08FamilySheaf F)
    (D : Chapter08FiberwiseHilbertData E)
    (B : Chapter08BaseChangeHilbertData E D)
    (hnoetherian : IsNoetherian F.family.S)
    (hveryample : Chapter08RelativelyVeryAmple F.family.f F.lineBundle
      F.lineBundle_invertible.is_invertible)
    (U : Set F.family.S) (hUopen : IsOpen U) (hUcompact : IsCompact U) :
    Set.Finite {P : Chapter08NumericalPolynomial |
      ∃ H : Chapter08FlatteningStratumData E D B P,
        Chapter08StratumMeets H.stratum U} := by
  sorry

/- A named predicate makes explicit that the theorem only provides a locally
   closed immersion, not an open stratum. -/
def Chapter08StratumIsOpen {S : Scheme} (D : Chapter08FlatteningStratum S) : Prop :=
  IsOpen (Set.range D.inclusion)

/- Flatness of a finitely presented family is locally persistent on the base. -/
structure Chapter08FlatnessOpenProfile
    {F : Chapter08PolarizedFamily} (E : Chapter08FamilySheaf F)
    (s : F.family.S) where
  neighborhood : Set F.family.S
  neighborhood_open : IsOpen neighborhood
  point_mem_neighborhood : s ∈ neighborhood
  flat_on_neighborhood :
    ∀ t ∈ neighborhood, chapter08FlatAt F.family.f E.sheaf t

/- LOCAL_DEPENDENCY_GUESS: this abstracts openness of the flat locus for the
   finitely presented family in the source warning. -/
theorem chapter08_flatness_persists_on_open_neighborhood
    {F : Chapter08PolarizedFamily} (E : Chapter08FamilySheaf F)
    (s : F.family.S) (hflat : chapter08FlatAt F.family.f E.sheaf s) :
    Nonempty (Chapter08FlatnessOpenProfile E s) := by
  sorry

end
end Chapter08
end Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers
end LastLib
