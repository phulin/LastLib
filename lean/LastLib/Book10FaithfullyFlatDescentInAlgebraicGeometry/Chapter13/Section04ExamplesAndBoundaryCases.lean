import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter13.Section03ContractedProductsAndTwisting

/-!
# 13.4 Examples and boundary cases

The concrete relative group-scheme constructions for `Gₘ`, `GL_r`, and `μₙ` are not yet exposed by
the pinned earlier LastLib chapters.  The correspondence records below isolate exactly the APIs
that the examples require, while the pointwise power-equation and stabilizer interfaces are stated
directly and independently of a missing relative group-scheme implementation.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry MonObj

universe u

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter13

noncomputable section

/- LOCAL_DEPENDENCY_GUESS: a canonical relative `Gₘ` object and its standard one-dimensional
representation are not available in the pinned earlier API.  This is the exact equivalence
interface needed by the line-bundle example; it is deliberately not used as a hypothesis for a
different theorem. -/
structure Chapter13GmTorsorLineBundleCorrespondence (S : Scheme.{u}) where
  group : Chapter13GroupScheme S
  fromTorsor : Chapter13FpqcTorsor group →
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Chapter04LineBundle S
  fromLineBundle :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Chapter04LineBundle S →
      Chapter13FpqcTorsor group
  torsor_inverse : ∀ P, fromLineBundle (fromTorsor P) = P
  lineBundle_inverse : ∀ L, fromTorsor (fromLineBundle L) = L

/- LOCAL_DEPENDENCY_GUESS: the pinned API also lacks the relative `GL_r` frame-group scheme.
The local-basis field makes the rank parameter mathematically meaningful rather than an unused
index. -/
structure Chapter13RankedFiniteLocallyFreeSheaf (S : Scheme.{u}) (r : ℕ) where
  sheaf : S.Modules
  finiteLocallyFree : Chapter13FiniteLocallyFreeSheaf S
  sheaf_eq : finiteLocallyFree.sheaf = sheaf
  local_basis :
    ∃ q : sheaf.LocalGeneratorsData,
      q.IsLocallyFreeData ∧
        ∀ i, Nonempty ((q.generators i).I ≃ Fin r)

structure Chapter13GLFrameBundleCorrespondence (S : Scheme.{u}) (r : ℕ) where
  group : Chapter13GroupScheme S
  fromFrameTorsor : Chapter13FpqcTorsor group →
    Chapter13RankedFiniteLocallyFreeSheaf S r
  toFrameTorsor : Chapter13RankedFiniteLocallyFreeSheaf S r →
    Chapter13FpqcTorsor group
  frame_inverse : ∀ P, toFrameTorsor (fromFrameTorsor P) = P
  bundle_inverse : ∀ V, fromFrameTorsor (toFrameTorsor V) = V

/-! ### The finite-flat `μₙ` equation -/

def Chapter13PowerEquation {R : Type u} [CommRing R]
    (n : ℕ) (a : Rˣ) : Type u :=
  {z : Rˣ // (z : R) ^ n = (a : R)}

abbrev Chapter13MuNPoint (R : Type u) [CommRing R] (n : ℕ) :=
  rootsOfUnity n R

instance chapter13PowerEquationMulAction {R : Type u} [CommRing R]
    (n : ℕ) (a : Rˣ) : MulAction (Chapter13MuNPoint R n)
      (Chapter13PowerEquation n a) where
  smul z w :=
    ⟨z.1 * w.1, by sorry⟩
  one_smul := by sorry
  mul_smul := by sorry

instance chapter13PowerEquationSDiv {R : Type u} [CommRing R]
    (n : ℕ) (a : Rˣ) : SDiv (Chapter13MuNPoint R n)
      (Chapter13PowerEquation n a) where
  sdiv z w :=
    ⟨z.1 / w.1, by sorry⟩

theorem chapter13_powerEquation_is_torsor_of_nonempty
    {R : Type u} [CommRing R] (n : ℕ) (a : Rˣ)
    (h : Nonempty (Chapter13PowerEquation n a)) :
    Torsor (Chapter13MuNPoint R n) (Chapter13PowerEquation n a) := by
  letI : Nonempty (Chapter13PowerEquation n a) := h
  sorry

/-- The usual étale criterion for the power equation is the invertibility of `n`. -/
def Chapter13PowerEquationEtaleCriterion {R : Type u} [CommRing R] (n : ℕ) : Prop :=
  IsUnit (n : R)

theorem chapter13_powerEquation_not_in_the_etale_range
    {R : Type u} [CommRing R] {n : ℕ}
    (hn : ¬ IsUnit (n : R)) :
    ¬ Chapter13PowerEquationEtaleCriterion n := by
  exact hn

/-! ### Pointwise and scheme-theoretic boundaries -/

theorem chapter13_pointwise_transitivity_does_not_detect_stabilizers
    {G P : Type u} [Group G] [MulAction G P]
    (htrans : ∀ x y : P, ∃ g : G, g • x = y)
    (hstabilizer : ∃ (p : P) (g : G), g ≠ 1 ∧ g • p = p) :
    ¬ (∀ x y : P, ∃! g : G, g • x = y) := by
  sorry

theorem chapter13_scheme_identity_is_stronger_than_pointwise_transitivity
    {S : Scheme.{u}} {G : Chapter13GroupScheme S} {P : Chapter13SchemeOver S}
    (A : Chapter13RightAction G P)
    (hA : Chapter13TorsorIdentity A) :
    ∀ (T : Over S) (p q : T ⟶ P), ∃ g : T ⟶ G.X,
      CartesianMonoidalCategory.lift p g ≫ A.act = q := by
  intro T p q
  exact ((chapter13_torsorIdentity_iff_unique A).mp hA T p q).exists

/- The contracted-product construction above is explicitly an effective scheme descent datum;
this is the scheme-theoretic structure that a quotient of underlying topological spaces alone
does not provide. -/
theorem chapter13_contractedProduct_is_scheme_theoretic
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (P : Chapter13FpqcTorsor G) (X : Chapter13SchemeOver S)
    (Xaction : Chapter13LeftAction G X) :
    Nonempty (Chapter13SchemeOver S) := by
  exact ⟨(chapter13ContractedProduct P X Xaction).carrier⟩

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter13
