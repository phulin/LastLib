import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter13.Dependencies

/-!
# 13.1 The torsor identity

The displayed isomorphism is kept as a scheme morphism, while the pointwise formulation is stated
in the internal language of `Over S`.  This makes the uniqueness clause available without choosing
geometric points.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry MonObj

universe u

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter13

noncomputable section

theorem chapter13_torsorIdentity_iff_unique
    {S : Scheme.{u}} {G : Chapter13GroupScheme S} {P : Chapter13SchemeOver S}
    (A : Chapter13RightAction G P) :
    Chapter13TorsorIdentity A ↔
      ∀ (T : Over S) (p q : T ⟶ P),
        ∃! g : T ⟶ G.X,
          CartesianMonoidalCategory.lift p g ≫ A.act = q := by
  sorry

theorem chapter13_torsorIdentity_is_stable_under_baseChange
    {S T : Scheme.{u}} {G : Chapter13GroupScheme S} {P : Chapter13SchemeOver S}
    (A : Chapter13RightAction G P) (t : T ⟶ S)
    (h : Chapter13TorsorIdentity A) :
    Chapter13TorsorIdentity (chapter13BaseChangedRightAction A t) := by
  sorry

theorem chapter13_torsorIdentity_of_fpqc_baseChange
    {S T : Scheme.{u}} {G : Chapter13GroupScheme S} {P : Chapter13SchemeOver S}
    (A : Chapter13RightAction G P) (t : T ⟶ S)
    (ht : Chapter13FpqcCover t)
    (h : Chapter13TorsorIdentity (chapter13BaseChangedRightAction A t)) :
    Chapter13TorsorIdentity A := by
  sorry

/- The empty object is the precise boundary example: its comparison map is an isomorphism for
every action datum, but its structural morphism is not a cover over a nonempty base. -/
theorem chapter13_empty_action_satisfies_identity
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (A : Chapter13RightAction G (Over.mk (Scheme.emptyTo S))) :
    Chapter13TorsorIdentity A := by
  sorry

theorem chapter13_empty_scheme_not_fpqc_cover
    {S : Scheme.{u}} [Nonempty S] :
    ¬ Chapter13FpqcCover (Scheme.emptyTo S) := by
  sorry

theorem chapter13_torsor_cover_is_an_independent_clause
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (Q : Chapter13FpqcTorsor G) :
    Chapter13FpqcCover Q.carrier.hom :=
  Q.cover

noncomputable def chapter13RegularFpqcTorsor
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (hG : Chapter13FpqcCover G.X.hom) : Chapter13FpqcTorsor G := by
  exact
    { carrier := G.X
      action := chapter13RegularRightAction G
      identity := by sorry
      cover := hG }

noncomputable def chapter13RegularFppfTorsor
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (hG : Chapter13FppfCover G.X.hom) : Chapter13FppfTorsor G := by
  exact
    { carrier := G.X
      action := chapter13RegularRightAction G
      identity := by sorry
      cover := hG }

theorem chapter13_torsor_trivializes_over_its_total_space
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (Q : Chapter13FpqcTorsor G) :
    Nonempty (Chapter13TorsorLocalTrivialization Q.action Q.carrier.hom) := by
  sorry

/-! ### Finite locally free group schemes -/

theorem chapter13_fpqc_torsor_finite_locally_free
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (Q : Chapter13FpqcTorsor G)
    (hG : Chapter13FiniteLocallyFreeOfPositiveRank G.X.hom) :
    Chapter13FiniteLocallyFree Q.carrier.hom ∧
      Chapter13SameFiniteLocallyFreeRank Q.carrier.hom G.X.hom := by
  sorry

theorem chapter13_fppf_torsor_finite_locally_free
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (Q : Chapter13FppfTorsor G)
    (hG : Chapter13FiniteLocallyFreeOfPositiveRank G.X.hom) :
    Chapter13FiniteLocallyFree Q.carrier.hom ∧
      Chapter13SameFiniteLocallyFreeRank Q.carrier.hom G.X.hom := by
  sorry

theorem chapter13_fpqc_iff_fppf_for_finite_locally_free_group
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (hG : Chapter13FiniteLocallyFreeOfPositiveRank G.X.hom) :
    Nonempty (Chapter13FpqcTorsor G) ↔ Nonempty (Chapter13FppfTorsor G) := by
  sorry

theorem chapter13_fpqc_torsor_is_fppf_for_finite_locally_free_group
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (Q : Chapter13FpqcTorsor G)
    (hG : Chapter13FiniteLocallyFreeOfPositiveRank G.X.hom) :
    Nonempty (Chapter13FppfTorsor G) := by
  sorry

theorem chapter13_fppf_torsor_is_fpqc_for_finite_locally_free_group
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (Q : Chapter13FppfTorsor G)
    (hG : Chapter13FiniteLocallyFreeOfPositiveRank G.X.hom) :
    Nonempty (Chapter13FpqcTorsor G) := by
  sorry

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter13
