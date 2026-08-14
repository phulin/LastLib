import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Birational.Birational
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.RegularLocalRing.Defs
import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter03.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.Dependencies
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter02.Section02EffectiveCartierDivisors

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
   bundle adapters used below.  Chapter 3 supplies the canonical relative
   Rees/Proj presentation; the small record below adapts that presentation to
   the effective-Cartier and transform interfaces consumed by this chapter.
-/

abbrev Chapter04EffectiveCartierDivisor (X : Scheme.{u}) :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.EffectiveCartierDivisor X

abbrev Chapter04LineBundle (X : Scheme.{u}) :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Chapter04LineBundle X

abbrev Chapter04ProjectiveBundle (S : Scheme.{u}) :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Chapter04ProjectiveBundle S

/- The earlier divisor API realizes an ideal sheaf as the kernel of the
   structure-sheaf map to the closed subscheme.  Reusing it makes the
   exceptional-ideal restriction below a genuine module pullback rather than
   an unrelated line bundle with matching local section groups. -/
abbrev Chapter04IdealModule {X : Scheme.{u}} (I : X.IdealSheafData) : X.Modules :=
  LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter02.chapter02IdealOminusD I

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

theorem chapter04LineBundleIsomorphic_trans {X : Scheme.{u}}
    {L M N : Chapter04LineBundle X}
    (hLM : chapter04LineBundleIsomorphic L M)
    (hMN : chapter04LineBundleIsomorphic M N) :
    chapter04LineBundleIsomorphic L N := by
  rcases hLM with ⟨eLM⟩
  rcases hMN with ⟨eMN⟩
  exact ⟨eLM.trans eMN⟩

/- The affine finite-generation criterion is the coherent-ideal hypothesis
   used by the relative Proj construction. -/
def Chapter04CoherentIdeal {X : Scheme.{u}} (I : X.IdealSheafData) : Prop :=
  ∀ U : X.affineOpens, (I.ideal U).FG

/- The preceding chapter owns the canonical coherent-ideal record used by the
   relative Rees/Proj construction.  This adapter keeps the Chapter 4 ideal
   sheaf presentation while making its finite-generation witness available to
   that earlier interface. -/
def chapter04CoherentIdealData {X : Scheme.{u}} {I : X.IdealSheafData}
    (hI : Chapter04CoherentIdeal I) :
    LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter03.Chapter03CoherentIdeal X :=
  { ideal := I
    finitelyGenerated := hI }

/- A locally principal ideal is the effective-Cartier invertibility predicate
needed in the universal property of the blowup.  The non-zero-divisor clause
keeps the pullback in the Cartier-divisor setting used by this chapter. -/
def Chapter04LocallyPrincipalIdeal {X : Scheme.{u}}
    (I : X.IdealSheafData) : Prop :=
  ∀ (U : X.affineOpens) (x : U.1),
    ∃ (V : X.affineOpens) (f : Γ(X, V.1)),
      x.1 ∈ V.1 ∧ V ≤ U ∧
        I.ideal V = Ideal.span ({f} : Set Γ(X, V.1)) ∧
          f ∈ nonZeroDivisors Γ(X, V.1)

/- LOCAL_DEPENDENCY_GUESS (Chapter 3): the relative Proj blowup is represented
   by its canonical universal property for maps along which the center ideal
   becomes locally principal.  This interface does not assume any conclusion
   about exceptional divisors or transforms. -/
structure Chapter04Blowup (X : Scheme.{u}) (I : X.IdealSheafData) where
  coherent : Chapter04CoherentIdeal I
  /- The carrier and morphism below are required to be the relative-Rees/Proj
     blowup supplied by Chapter 3, rather than an unrelated object satisfying
     only a look-alike universal property. -/
  presentation :
    LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter03.Chapter03Blowup
      (chapter04CoherentIdealData coherent)
  carrier : Scheme.{u}
  carrier_iso : carrier ≅ presentation.carrier
  morphism : carrier ⟶ X
  morphism_eq_presentation : carrier_iso.hom ≫ presentation.projection = morphism
  pullback_ideal_locallyPrincipal :
    Chapter04LocallyPrincipalIdeal (I.comap morphism)
  universal :
    ∀ {T : Scheme.{u}} (f : T ⟶ X),
      Chapter04LocallyPrincipalIdeal (I.comap f) →
        ∃! g : T ⟶ carrier, g ≫ morphism = f

/- The preceding chapter constructs the relative Rees/Proj object on a
   noetherian scheme.  This adapter exposes that construction with the
   Chapter 4 universal-property record. -/
theorem chapter04_blowup_exists
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (hI : Chapter04CoherentIdeal I) :
    Nonempty (Chapter04Blowup X I) := by
  sorry

noncomputable def chapter04Blowup
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (hI : Chapter04CoherentIdeal I) : Chapter04Blowup X I :=
  Classical.choice (chapter04_blowup_exists I hI)

/- The relative-Rees presentation also supplies geometric properties that are
   needed by the transform and intersection constructions.  They are kept in
   a companion record so existing universal-property constructors remain
   source-compatible while later proof routes can require the full package. -/
structure Chapter04AwayFromCenterIso
    {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : Y ⟶ X) where
  source_open : Y.Opens
  target_open : X.Opens
  source_open_eq_complement :
    (source_open : Set Y) = {y | f y ∉ (I.support : Set X)}
  target_open_eq_complement :
    (target_open : Set X) = {x | x ∉ (I.support : Set X)}
  iso : source_open.toScheme ≅ target_open.toScheme
  commutes : iso.hom ≫ target_open.ι = source_open.ι ≫ f

structure Chapter04BlowupGeometryData
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (B : Chapter04Blowup X I) where
  projective :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04Projective
      B.morphism
  /- Birationality requires an integral target and a dense center complement;
     these are hypotheses of the geometric assertion, not properties of an
     arbitrary blowup record. -/
  birational :
    IsIntegral X → Dense ((I.support : Set X)ᶜ) → Scheme.Birational B.carrier X
  off_center : Chapter04AwayFromCenterIso I B.morphism
  tautologicalIdeal : B.carrier.IdealSheafData
  tautologicalIdeal_eq_exceptional : tautologicalIdeal = I.comap B.morphism

abbrev Chapter04Blowup.center {X : Scheme.{u}} {I : X.IdealSheafData}
    (_B : Chapter04Blowup X I) : Scheme.{u} :=
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
   sequence interface used by the preceding blowup chapters.  Chapter 3's
   later geometric section is not imported here because this chapter only
   needs the local center predicate and must remain independent of that
   section's unresolved auxiliary interfaces. -/
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
