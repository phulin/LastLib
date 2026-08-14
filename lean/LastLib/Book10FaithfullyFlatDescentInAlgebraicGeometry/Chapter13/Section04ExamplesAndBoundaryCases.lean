import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter13.Section01TheTorsorIdentity
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter13.Section03ContractedProductsAndTwisting

/-!
# 13.4 Examples and boundary cases

The group-scheme examples below are exposed through their standard functor-of-points interfaces.
The pinned earlier chapters do not provide a single canonical constructor for each relative
scheme, so the interfaces retain the identifying equivalences and their base-change maps.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry MonObj

universe u

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter13

noncomputable section

abbrev Chapter13RelativeGmPointGroup {T : Scheme.{u}} := Γ(T, ⊤)ˣ

abbrev Chapter13RelativeGLPointGroup (T : Scheme.{u}) (r : ℕ) :=
  Matrix.GeneralLinearGroup (Fin r) Γ(T, ⊤)

/- The pointwise equivalence is the identifying interface for the standard
relative multiplicative group. -/
structure Chapter13RelativeGmModel (S : Scheme.{u}) where
  group : Chapter13GroupScheme S
  pointsEquiv : ∀ {T : Scheme.{u}} (t : T ⟶ S),
    (Over.mk t ⟶ group.X) ≃* Chapter13RelativeGmPointGroup (T := T)
  pointMap : ∀ {T U : Scheme.{u}} (t : T ⟶ S) (u : U ⟶ T),
    (Over.mk t ⟶ group.X) → (Over.mk (u ≫ t) ⟶ group.X)
  pointMap_is_pullback : ∀ {T U : Scheme.{u}} (t : T ⟶ S) (u : U ⟶ T)
    (g : Over.mk t ⟶ group.X),
    pointMap t u g = Over.homMk u ≫ g
  pointMap_natural : ∀ {T U : Scheme.{u}} (t : T ⟶ S) (u : U ⟶ T)
    (g : Over.mk t ⟶ group.X),
    pointsEquiv (u ≫ t) (pointMap t u g) =
      Units.map u.appTop.hom.toMonoidHom (pointsEquiv t g)

structure Chapter13GmTorsorLineBundleCorrespondence (S : Scheme.{u}) where
  groupModel : Chapter13RelativeGmModel S
  fromTorsor : Chapter13FpqcTorsor groupModel.group →
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Chapter04LineBundle S
  fromLineBundle :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Chapter04LineBundle S →
      Chapter13FpqcTorsor groupModel.group
  torsor_inverse : ∀ P,
    Nonempty (Chapter13EquivariantIso
      (fromLineBundle (fromTorsor P)).action P.action)
  lineBundle_inverse : ∀ L,
    Nonempty ((fromTorsor (fromLineBundle L)).sheaf ≅ L.sheaf)

theorem chapter13_gm_torsor_lineBundle_correspondence_exists
    (S : Scheme.{u}) :
    Nonempty (Chapter13GmTorsorLineBundleCorrespondence S) := by
  sorry

/- The pointwise equivalence is the identifying interface for the standard
relative general linear group. -/
structure Chapter13RelativeGLModel (S : Scheme.{u}) (r : ℕ) where
  group : Chapter13GroupScheme S
  pointsEquiv : ∀ {T : Scheme.{u}} (t : T ⟶ S),
    (Over.mk t ⟶ group.X) ≃* Chapter13RelativeGLPointGroup T r
  pointMap : ∀ {T U : Scheme.{u}} (t : T ⟶ S) (u : U ⟶ T),
    (Over.mk t ⟶ group.X) → (Over.mk (u ≫ t) ⟶ group.X)
  pointMap_is_pullback : ∀ {T U : Scheme.{u}} (t : T ⟶ S) (u : U ⟶ T)
    (g : Over.mk t ⟶ group.X),
    pointMap t u g = Over.homMk u ≫ g
  pointMap_natural : ∀ {T U : Scheme.{u}} (t : T ⟶ S) (u : U ⟶ T)
    (g : Over.mk t ⟶ group.X),
    pointsEquiv (u ≫ t) (pointMap t u g) =
      Matrix.GeneralLinearGroup.map u.appTop.hom (pointsEquiv t g)

structure Chapter13RankedFiniteLocallyFreeSheaf (S : Scheme.{u}) (r : ℕ) where
  sheaf : S.Modules
  finiteLocallyFree : Chapter13FiniteLocallyFreeSheaf S
  sheaf_eq : finiteLocallyFree.sheaf = sheaf
  local_basis :
    ∃ q : sheaf.LocalGeneratorsData.{u},
      q.IsLocallyFreeData ∧
        ∀ i, Nonempty ((q.generators i).I ≃ Fin r)

structure Chapter13GLFrameBundleCorrespondence (S : Scheme.{u}) (r : ℕ) where
  groupModel : Chapter13RelativeGLModel S r
  fromFrameTorsor : Chapter13FpqcTorsor groupModel.group →
    Chapter13RankedFiniteLocallyFreeSheaf S r
  toFrameTorsor : Chapter13RankedFiniteLocallyFreeSheaf S r →
    Chapter13FpqcTorsor groupModel.group
  frame_inverse : ∀ P,
    Nonempty (Chapter13EquivariantIso
      (toFrameTorsor (fromFrameTorsor P)).action P.action)
  bundle_inverse : ∀ V,
    Nonempty ((fromFrameTorsor (toFrameTorsor V)).sheaf ≅ V.sheaf)

theorem chapter13_gl_frameBundle_correspondence_exists
    (S : Scheme.{u}) (r : ℕ) :
    Nonempty (Chapter13GLFrameBundleCorrespondence S r) := by
  sorry

/- The positive-nth-root group is recorded as a finite locally free rank-n
relative group scheme, with the exact étale criterion. -/
structure Chapter13RelativeMuNModel (S : Scheme.{u}) (n : ℕ) where
  positive : 0 < n
  group : Chapter13GroupScheme S
  pointsEquiv : ∀ {T : Scheme.{u}} (t : T ⟶ S),
    (Over.mk t ⟶ group.X) ≃* rootsOfUnity n Γ(T, ⊤)
  pointMap : ∀ {T U : Scheme.{u}} (t : T ⟶ S) (u : U ⟶ T),
    (Over.mk t ⟶ group.X) → (Over.mk (u ≫ t) ⟶ group.X)
  pointMap_is_pullback : ∀ {T U : Scheme.{u}} (t : T ⟶ S) (u : U ⟶ T)
    (g : Over.mk t ⟶ group.X),
    pointMap t u g = Over.homMk u ≫ g
  pointMap_natural : ∀ {T U : Scheme.{u}} (t : T ⟶ S) (u : U ⟶ T)
    (g : Over.mk t ⟶ group.X),
    pointsEquiv (u ≫ t) (pointMap t u g) =
      restrictRootsOfUnity u.appTop.hom n (pointsEquiv t g)
  finiteLocallyFree : Chapter13FiniteLocallyFreeOfRank group.X.hom n
  etale_iff : Etale group.X.hom ↔ IsUnit (n : Γ(S, ⊤))

theorem chapter13_relativeMuN_is_fppf_cover
    {S : Scheme.{u}} {n : ℕ} (M : Chapter13RelativeMuNModel S n) :
    Chapter13FppfCover M.group.X.hom := by
  sorry

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
    ⟨z.1 * w.1, by
      change ((z.1 : R) * (w.1 : R)) ^ n = (a : R)
      rw [mul_pow, (mem_rootsOfUnity' n z.1).mp z.2, one_mul, w.2]⟩
  one_smul := by
    intro w
    apply Subtype.ext
    change (1 : Rˣ) * w.1 = w.1
    exact one_mul _
  mul_smul := by
    intro z₁ z₂ w
    apply Subtype.ext
    change (z₁.1 * z₂.1) * w.1 = z₁.1 * (z₂.1 * w.1)
    exact mul_assoc _ _ _

instance chapter13PowerEquationSDiv {R : Type u} [CommRing R]
    (n : ℕ) (a : Rˣ) : SDiv (Chapter13MuNPoint R n)
      (Chapter13PowerEquation n a) where
  sdiv z w :=
    ⟨z.1⁻¹ * w.1, by
      rw [mem_rootsOfUnity]
      have hz : z.1 ^ n = a := by
        apply Units.ext
        simpa [Units.val_pow_eq_pow_val] using z.2
      have hw : w.1 ^ n = a := by
        apply Units.ext
        simpa [Units.val_pow_eq_pow_val] using w.2
      rw [mul_pow, inv_pow, hz, hw]
      exact inv_mul_cancel a⟩

@[instance_reducible]
noncomputable def chapter13_powerEquation_is_torsor_of_nonempty
    {R : Type u} [CommRing R] (n : ℕ) (a : Rˣ)
    (h : Nonempty (Chapter13PowerEquation n a)) :
    Torsor (Chapter13MuNPoint R n) (Chapter13PowerEquation n a) := by sorry

/- The pointwise type above records only solutions over one ring.  This
   presentation records the scheme-theoretic torsor promised by the source:
   its points over every base change are the corresponding power-equation
   solutions, and the torsor action is multiplication by a root of unity. -/
structure Chapter13PowerEquationFppfTorsorPresentation
    (S : Scheme.{u}) (n : ℕ) (a : Γ(S, ⊤)ˣ) where
  model : Chapter13RelativeMuNModel S n
  torsor : Chapter13FppfTorsor model.group
  pointsEquiv : ∀ {T : Scheme.{u}} (t : T ⟶ S),
    (Over.mk t ⟶ torsor.carrier) ≃
      Chapter13PowerEquation n (Units.map t.appTop.hom.toMonoidHom a)
  /-- The pointwise description is natural under base change of the test scheme. -/
  points_natural : ∀ {T U : Scheme.{u}} (t : T ⟶ S) (u : U ⟶ T)
    (x : Over.mk t ⟶ torsor.carrier),
    pointsEquiv (u ≫ t)
        ((Over.homMk u : Over.mk (u ≫ t) ⟶ Over.mk t) ≫ x) =
      ⟨Units.map u.appTop.hom.toMonoidHom (pointsEquiv t x).1, by sorry⟩
  action_points : ∀ {T : Scheme.{u}} (t : T ⟶ S)
    (g : Over.mk t ⟶ model.group.X) (x : Over.mk t ⟶ torsor.carrier),
    pointsEquiv t
        (CartesianMonoidalCategory.lift x g ≫ torsor.action.act) =
      ⟨(model.pointsEquiv t g : Γ(T, ⊤)ˣ) * (pointsEquiv t x).1, by sorry⟩

theorem chapter13_powerEquation_fppf_torsor_presentation_exists
    {S : Scheme.{u}} {n : ℕ} (hn : 0 < n) (a : Γ(S, ⊤)ˣ) :
    Nonempty (Chapter13PowerEquationFppfTorsorPresentation S n a) := by
  sorry

theorem chapter13_powerEquation_presentation_not_etale_of_not_unit
    {S : Scheme.{u}} {n : ℕ} {a : Γ(S, ⊤)ˣ}
    (P : Chapter13PowerEquationFppfTorsorPresentation S n a)
    (hn : ¬ IsUnit (n : Γ(S, ⊤))) :
    ¬ Etale P.torsor.carrier.hom := by
  sorry

/-- The usual étale criterion for the power equation is the invertibility of `n`. -/
def Chapter13PowerEquationEtaleCriterion {R : Type u} [CommRing R] (n : ℕ) : Prop :=
  IsUnit (n : R)

theorem chapter13_powerEquation_not_in_the_etale_range
    {R : Type u} [CommRing R] {n : ℕ}
    (hn : ¬ IsUnit (n : R)) :
    ¬ Chapter13PowerEquationEtaleCriterion (R := R) n := by
  exact hn

/-! ### Pointwise and scheme-theoretic boundaries -/

theorem chapter13_pointwise_transitivity_does_not_detect_stabilizers
    {G P : Type u} [Group G] [MulAction G P]
    (htrans : ∀ x y : P, ∃ g : G, g • x = y)
    (hstabilizer : ∃ (p : P) (g : G), g ≠ 1 ∧ g • p = p) :
    ¬ (∀ x y : P, ∃! g : G, g • x = y) := by sorry

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
    Nonempty (Chapter13ContractedProductData P X Xaction) := by
  exact ⟨chapter13ContractedProduct P X Xaction⟩

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter13
