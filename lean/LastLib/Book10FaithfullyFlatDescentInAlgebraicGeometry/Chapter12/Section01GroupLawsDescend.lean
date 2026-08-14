import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter12.Dependencies

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter12

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoObj

universe u

/-!
### 12.1 Group laws descend

The descent datum records the underlying scheme gluing and its cocycle.  The theorem below adds the
group-object structure by descending the three structure maps and checking their equations after
the fpqc cover.
-/

theorem chapter12_group_laws_descend
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    (D : Chapter12GroupSchemeDescentDatum p) :
    ∃ G : Chapter12GroupScheme S,
      Nonempty (Chapter12GroupScheme.baseChange p G ≅ D.upstairs) := by
  sorry

/-- Equality of homomorphisms can be detected after a faithfully flat base change. -/
theorem chapter12_group_hom_ext_of_faithfullyFlat
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FaithfullyFlat p)
    {G H : Chapter12GroupScheme S} (f g : G ⟶ H)
    (h : Chapter12GroupScheme.baseChangeHom p f =
      Chapter12GroupScheme.baseChangeHom p g) :
    f = g := by
  sorry

/-!
The commutativity equation is the equality of multiplication with its pullback along the
symmetry.  It is kept as an instance-shaped proposition so later affine and finite commutative
group-object APIs can consume it directly.
-/

theorem chapter12_commutativity_descends
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FaithfullyFlat p)
    (G : Chapter12GroupScheme S) (G_T : Chapter12GroupScheme T)
    (e : Chapter12GroupScheme.baseChange p G ≅ G_T)
    (hcomm : IsCommMonObj G_T.X) :
    IsCommMonObj G.X := by
  sorry

theorem chapter12_finite_descends
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FaithfullyFlat p)
    (G : Chapter12GroupScheme S) (G_T : Chapter12GroupScheme T)
    (e : Chapter12GroupScheme.baseChange p G ≅ G_T)
    (hfinite : Chapter12Finite G_T.X.hom) :
    Chapter12Finite G.X.hom := by
  sorry

theorem chapter12_flat_descends
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FaithfullyFlat p)
    (G : Chapter12GroupScheme S) (G_T : Chapter12GroupScheme T)
    (e : Chapter12GroupScheme.baseChange p G ≅ G_T)
    (hflat : Chapter12Flat G_T.X.hom) :
    Chapter12Flat G.X.hom := by
  sorry

theorem chapter12_locallyOfFinitePresentation_descends
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FaithfullyFlat p)
    (G : Chapter12GroupScheme S) (G_T : Chapter12GroupScheme T)
    (e : Chapter12GroupScheme.baseChange p G ≅ G_T)
    (hlfp : Chapter12LocallyOfFinitePresentation G_T.X.hom) :
    Chapter12LocallyOfFinitePresentation G.X.hom := by
  sorry

theorem chapter12_finiteLocallyFree_descends
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FaithfullyFlat p)
    (G : Chapter12GroupScheme S) (G_T : Chapter12GroupScheme T)
    (e : Chapter12GroupScheme.baseChange p G ≅ G_T)
    (hfinite : Chapter12FiniteLocallyFree G_T.X.hom) :
    Chapter12FiniteLocallyFree G.X.hom := by
  sorry

theorem chapter12_finiteLocallyFree_rank_descends
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FaithfullyFlat p)
    (G : Chapter12GroupScheme S) (G_T : Chapter12GroupScheme T)
    (e : Chapter12GroupScheme.baseChange p G ≅ G_T) (n : ℕ)
    (hrank : Chapter12FiniteLocallyFreeOfRank G_T.X.hom n) :
    Chapter12FiniteLocallyFreeOfRank G.X.hom n := by
  sorry

/-! The finite-flat and finite-locally-free group-object categories inherit effectivity. -/

theorem chapter12_finiteFlat_group_objects_effective_fpqc_descent
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    (D : Chapter12GroupSchemeDescentDatum p)
    (hfiniteFlat : Chapter12FiniteFlat D.upstairs.X.hom) :
    ∃ G : Chapter12FiniteFlatGroupScheme S,
      Nonempty (Chapter12GroupScheme.baseChange p G.group ≅ D.upstairs) := by
  sorry

theorem chapter12_finiteLocallyFree_group_objects_effective_fpqc_descent
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    (D : Chapter12GroupSchemeDescentDatum p)
    (hfiniteLocallyFree : Chapter12FiniteLocallyFree D.upstairs.X.hom) :
    ∃ G : Chapter12FiniteLocallyFreeGroupScheme S,
      Nonempty (Chapter12GroupScheme.baseChange p G.group ≅ D.upstairs) := by
  sorry

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter12
