import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.RegularLocalRing.Defs
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.Dependencies

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter04

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u v

/-!
Shared interfaces for Chapter 4.

Mathlib supplies ideal sheaves, their comap along a morphism, closed subschemes,
residue fields, and the cotangent module `I.Cotangent`.  The preceding books
also supply the effective-Cartier, invertible-sheaf, and relative-projective-
bundle adapters used below.  The only construction not present in the pinned
tree is the relative blowup itself, so the small record below is the natural
universal-property interface consumed by this chapter.
-/

abbrev Chapter04EffectiveCartierDivisor (X : Scheme.{u}) :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.EffectiveCartierDivisor X

abbrev Chapter04LineBundle (X : Scheme.{u}) :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Chapter04LineBundle X

abbrev Chapter04ProjectiveBundle (S : Scheme.{u}) :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Chapter04ProjectiveBundle S

def chapter04LineBundleIsomorphic {X : Scheme.{u}}
    (L M : Chapter04LineBundle X) : Prop :=
  Nonempty (L.sheaf ≅ M.sheaf)

theorem chapter04LineBundleIsomorphic_refl {X : Scheme.{u}}
    (L : Chapter04LineBundle X) : chapter04LineBundleIsomorphic L L := by
  exact ⟨Iso.refl _⟩

theorem chapter04LineBundleIsomorphic_symm {X : Scheme.{u}}
    {L M : Chapter04LineBundle X}
    (h : chapter04LineBundleIsomorphic L M) :
    chapter04LineBundleIsomorphic M L := by
  rcases h with ⟨e⟩
  exact ⟨e.symm⟩

/- The affine finite-generation criterion is the coherent-ideal hypothesis
   used by the relative Proj construction. -/
def Chapter04CoherentIdeal {X : Scheme.{u}} (I : X.IdealSheafData) : Prop :=
  ∀ U : X.affineOpens, (I.ideal U).FG

/- A locally principal ideal is the invertibility predicate needed in the
   universal property of the blowup.  It is deliberately stated without a
   non-zero-divisor condition: invertible ideals on a nonintegral test scheme
   need not define effective Cartier divisors. -/
def Chapter04LocallyPrincipalIdeal {X : Scheme.{u}}
    (I : X.IdealSheafData) : Prop :=
  ∀ (U : X.affineOpens) (x : U.1),
    ∃ (V : X.affineOpens) (f : Γ(X, V.1)),
      x.1 ∈ V.1 ∧ V ≤ U ∧ I.ideal V = Ideal.span ({f} : Set Γ(X, V.1))

/- LOCAL_DEPENDENCY_GUESS (Chapter 3): the relative Proj blowup is represented
   by its canonical universal property for maps along which the center ideal
   becomes locally principal.  This interface does not assume any conclusion
   about exceptional divisors or transforms. -/
structure Chapter04Blowup (X : Scheme.{u}) (I : X.IdealSheafData) where
  carrier : Scheme.{u}
  morphism : carrier ⟶ X
  pullback_ideal_locallyPrincipal :
    Chapter04LocallyPrincipalIdeal (I.comap morphism)
  universal :
    ∀ {T : Scheme.{u}} (f : T ⟶ X),
      Chapter04LocallyPrincipalIdeal (I.comap f) →
        ∃! g : T ⟶ carrier, g ≫ morphism = f

abbrev Chapter04Blowup.center {X : Scheme.{u}} {I : X.IdealSheafData}
    (B : Chapter04Blowup X I) : Scheme.{u} :=
  I.subscheme

abbrev Chapter04Blowup.centerι {X : Scheme.{u}} {I : X.IdealSheafData}
    (B : Chapter04Blowup X I) : B.center ⟶ X :=
  I.subschemeι

abbrev Chapter04Blowup.exceptionalIdeal {X : Scheme.{u}} {I : X.IdealSheafData}
    (B : Chapter04Blowup X I) : B.carrier.IdealSheafData :=
  I.comap B.morphism

@[simp]
theorem chapter04Blowup_exceptionalIdeal_def
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (B : Chapter04Blowup X I) :
    B.exceptionalIdeal = I.comap B.morphism :=
  rfl

/- The regular-immersion formulation follows the canonical stalkwise regular
   sequence interface already used in the preceding projective-geometry API. -/
structure Chapter04RegularClosedImmersion
    {Z X : Scheme.{u}} (i : Z ⟶ X) (r : ℕ) : Prop where
  closed : IsClosedImmersion i
  regularSequence :
    ∀ z : Z, ∃ rs : List (X.presheaf.stalk (i z)),
      rs.length = r ∧
        RingTheory.Sequence.IsRegular (X.presheaf.stalk (i z)) rs ∧
          RingHom.ker (i.stalkMap z).hom = Ideal.ofList rs

def Chapter04RegularClosedCenter {X : Scheme.{u}}
    (I : X.IdealSheafData) : Prop :=
  ∃ r : ℕ, Chapter04RegularClosedImmersion I.subschemeι r

def Chapter04IntegralRegularClosedCenter {X : Scheme.{u}}
    (I : X.IdealSheafData) : Prop :=
  IsIntegral I.subscheme ∧ Chapter04RegularClosedCenter I

/- The equality of line bundles is expressed by an isomorphism of module
   sheaves, the canonical equality notion in the preceding line-bundle API. -/
def chapter04ProjectiveBundleTautological {S : Scheme.{u}}
    (P : Chapter04ProjectiveBundle S) : Chapter04LineBundle P.space :=
  { sheaf := P.tautological
    isInvertible := P.tautological_isInvertible }

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter04
