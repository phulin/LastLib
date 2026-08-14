import Mathlib.AlgebraicGeometry.Birational.Birational
import Mathlib.AlgebraicGeometry.Geometrically.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Topology.KrullDimension

import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Dependencies
import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter03.Dependencies

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter05

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09
open scoped AlgebraicGeometry

universe u v

/-!
## Shared interfaces for Chapter 5

The pinned Mathlib API supplies schemes, residue fields, affine opens, regular local rings,
closed immersions, and birationality.  It does not package the scheme-theoretic blowup of a
coherent ideal, normal bundles of effective Cartier divisors, or the degree and section spaces
used in the arithmetic-surface statements.  The records below keep those interfaces explicit and
tie them to the canonical objects that are already available.
-/

/-! ### Regular surfaces and arithmetic surfaces -/

def Chapter05SurfaceDimensionTwo (X : Scheme.{u}) : Prop :=
  (∀ U : X.affineOpens, ringKrullDim Γ(X, U) ≤ 2) ∧
    ∃ U : X.affineOpens, ringKrullDim Γ(X, U) = 2

def Chapter05PureDimensionOne (X : Scheme.{u}) : Prop :=
  ∀ Z : irreducibleComponents X,
    topologicalKrullDim Z.1 = (1 : WithBot ℕ∞)

def Chapter05RelativeDimensionOne {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  geometrically Chapter05PureDimensionOne f

/- LOCAL_DEPENDENCY_GUESS: Mathlib has the local regular-ring and Noetherian predicates, but no
single scheme-level predicate for a regular noetherian surface of absolute dimension two. -/
class Chapter05RegularNoetherianSurface (X : Scheme.{u}) : Prop
    extends IsNoetherian X where
  integral : IsIntegral X
  regular_local_ring : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)
  dimension_two : Chapter05SurfaceDimensionTwo X

/- LOCAL_DEPENDENCY_GUESS: the relative-dimension-one part of the arithmetic-surface package is
not a primitive in the pinned morphism API; properness and flatness remain canonical fields. -/
class Chapter05ArithmeticSurface (X S : Scheme.{u}) (f : X ⟶ S)
    [Chapter05RegularNoetherianSurface X] : Prop where
  base_dedekind :
    LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03.Chapter03DedekindBase S
  base_connected : _root_.IsConnected (Set.univ : Set S)
  proper : IsProper f
  flat : Flat f
  relative_dimension_one : Chapter05RelativeDimensionOne f

theorem chapter05ArithmeticSurface.baseDedekind
    {X S : Scheme.{u}} [Chapter05RegularNoetherianSurface X]
    {f : X ⟶ S} [T : Chapter05ArithmeticSurface X S f] :
    LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03.Chapter03DedekindBase S :=
  T.base_dedekind

def Chapter05RegularSystemOfParameters {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (u v : A) : Prop :=
  Ideal.span ({u, v} : Set A) = IsLocalRing.maximalIdeal A ∧
    RingTheory.Sequence.IsRegular A [u, v]

structure Chapter05RegularPoint (X : Scheme.{u})
    [Chapter05RegularNoetherianSurface X] where
  point : X
  closed : IsClosed ({point} : Set X)
  parameters : X.presheaf.stalk point × X.presheaf.stalk point
  parameters_is_regular_system :
    Chapter05RegularSystemOfParameters parameters.1 parameters.2

abbrev Chapter05LocalRing {X : Scheme.{u}}
    [Chapter05RegularNoetherianSurface X]
    (P : Chapter05RegularPoint X) := X.presheaf.stalk P.point

abbrev Chapter05ParameterU {X : Scheme.{u}}
    [Chapter05RegularNoetherianSurface X]
    (P : Chapter05RegularPoint X) : Chapter05LocalRing P :=
  P.parameters.1

abbrev Chapter05ParameterV {X : Scheme.{u}}
    [Chapter05RegularNoetherianSurface X]
    (P : Chapter05RegularPoint X) : Chapter05LocalRing P :=
  P.parameters.2

structure Chapter05PointOverBase {X S : Scheme.{u}}
    [Chapter05RegularNoetherianSurface X] (f : X ⟶ S) where
  point : Chapter05RegularPoint X
  base_point : S
  base_point_closed : IsClosed ({base_point} : Set S)
  lies_over : f point.point = base_point

def chapter05ResidueDegree {X S : Scheme.{u}}
    [Chapter05RegularNoetherianSurface X] {f : X ⟶ S}
    (p : Chapter05PointOverBase f) : ℕ :=
  f.residueDegree p.point.point

theorem chapter05_residueDegree_eq_canonical_finrank
    {X S : Scheme.{u}} [Chapter05RegularNoetherianSurface X]
    {f : X ⟶ S} (p : Chapter05PointOverBase f) :
    chapter05ResidueDegree p = f.residueDegree p.point.point :=
  rfl

/-! ### Book-facing line bundles and their elementary API -/

abbrev Chapter05LineBundle (X : Scheme.{u}) := Chapter09LineBundle X

abbrev Chapter05LineBundleIso {X : Scheme.{u}}
    (L M : Chapter05LineBundle X) := Chapter09LineBundleIso L M

def chapter05LineBundleIsomorphic {X : Scheme.{u}}
    (L M : Chapter05LineBundle X) : Prop :=
  chapter09LineBundleIsomorphic L M

theorem chapter05_lineBundleIsomorphic_iff {X : Scheme.{u}}
    (L M : Chapter05LineBundle X) :
    chapter05LineBundleIsomorphic L M ↔
      Nonempty (Chapter05LineBundleIso L M) :=
  Iff.rfl

def chapter05LineBundleIsoRefl {X : Scheme.{u}}
    (L : Chapter05LineBundle X) : Chapter05LineBundleIso L L :=
  ⟨Iso.refl L.module⟩

def chapter05LineBundleIsoSymm {X : Scheme.{u}}
    {L M : Chapter05LineBundle X} (e : Chapter05LineBundleIso L M) :
    Chapter05LineBundleIso M L :=
  ⟨e.hom.symm⟩

def chapter05LineBundleIsoTrans {X : Scheme.{u}}
    {L M N : Chapter05LineBundle X}
    (e₁ : Chapter05LineBundleIso L M)
    (e₂ : Chapter05LineBundleIso M N) :
    Chapter05LineBundleIso L N :=
  ⟨e₁.hom.trans e₂.hom⟩

theorem chapter05_lineBundleIsomorphic_refl {X : Scheme.{u}}
    (L : Chapter05LineBundle X) :
    chapter05LineBundleIsomorphic L L :=
  ⟨chapter05LineBundleIsoRefl L⟩

theorem chapter05_lineBundleIsomorphic_symm {X : Scheme.{u}}
    {L M : Chapter05LineBundle X}
    (h : chapter05LineBundleIsomorphic L M) :
    chapter05LineBundleIsomorphic M L := by
  rcases h with ⟨e⟩
  exact ⟨chapter05LineBundleIsoSymm e⟩

theorem chapter05_lineBundleIsomorphic_trans {X : Scheme.{u}}
    {L M N : Chapter05LineBundle X}
    (hLM : chapter05LineBundleIsomorphic L M)
    (hMN : chapter05LineBundleIsomorphic M N) :
    chapter05LineBundleIsomorphic L N := by
  rcases hLM with ⟨e₁⟩
  rcases hMN with ⟨e₂⟩
  exact ⟨chapter05LineBundleIsoTrans e₁ e₂⟩

def chapter05StructureSheafLineBundle (X : Scheme.{u}) :
    Chapter05LineBundle X :=
  chapter09StructureSheafLineBundle X

def chapter05PullbackLineBundle {X Y : Scheme.{u}}
    (f : X ⟶ Y) (L : Chapter05LineBundle Y) :
    Chapter05LineBundle X :=
  chapter09PullbackLineBundle f L

/-! ### Degree and global sections -/

/- LOCAL_DEPENDENCY_GUESS: Book 9 supplies the intended degree theory conceptually, but the
arithmetic degree over a chosen residue field is not exposed as a reusable local interface. -/
class Chapter05CurveDegreeTheory (C : Scheme.{u}) (k : Type u) [Field k]
    (f : C ⟶ AlgebraicGeometry.Spec (.of k)) where
  proper : IsProper f
  degree : Chapter05LineBundle C → ℤ
  degree_structureSheaf :
    degree (chapter05StructureSheafLineBundle C) = 0
  degree_iso : ∀ {L M},
    chapter05LineBundleIsomorphic L M → degree L = degree M

def chapter05Degree {C : Scheme.{u}} {k : Type u} [Field k]
    {f : C ⟶ AlgebraicGeometry.Spec (.of k)}
    [Chapter05CurveDegreeTheory C k f]
    (L : Chapter05LineBundle C) : ℤ :=
  Chapter05CurveDegreeTheory.degree (f := f) L

theorem chapter05_degree_eq_of_isomorphic
    {C : Scheme.{u}} {k : Type u} [Field k]
    {f : C ⟶ AlgebraicGeometry.Spec (.of k)}
    [Chapter05CurveDegreeTheory C k f]
    {L M : Chapter05LineBundle C}
    (hLM : chapter05LineBundleIsomorphic L M) :
    chapter05Degree (f := f) L = chapter05Degree (f := f) M :=
  Chapter05CurveDegreeTheory.degree_iso (f := f) hLM

/- LOCAL_DEPENDENCY_GUESS: the finite-dimensional H⁰ package is not bundled with the current
sheaf API.  The H⁰ object below is the book-facing module of global sections; its canonical sheaf
implementation, finite rank, and invariance under line-bundle isomorphism are supplied separately. -/
class Chapter05GlobalSectionsTheory (C : Scheme.{u}) (k : Type u) [Field k]
    (f : C ⟶ AlgebraicGeometry.Spec (.of k)) where
  H0 : Chapter05LineBundle C → Type u
  addCommGroup : ∀ L, AddCommGroup (H0 L)
  module : ∀ L,
    letI : AddCommGroup (H0 L) := addCommGroup L
    Module k (H0 L)
  finite : ∀ L,
    letI : AddCommGroup (H0 L) := addCommGroup L
    letI : Module k (H0 L) := module L
    Module.Finite k (H0 L)
  finrank_isomorphic : ∀ {L M},
    chapter05LineBundleIsomorphic L M →
      (letI : AddCommGroup (H0 L) := addCommGroup L
       letI : Module k (H0 L) := module L
       Module.finrank k (H0 L)) =
      (letI : AddCommGroup (H0 M) := addCommGroup M
       letI : Module k (H0 M) := module M
       Module.finrank k (H0 M))

instance chapter05GlobalSectionsTheory.addCommGroup
    {C : Scheme.{u}} {k : Type u} [Field k]
    {f : C ⟶ AlgebraicGeometry.Spec (.of k)}
    [T : Chapter05GlobalSectionsTheory C k f]
    (L : Chapter05LineBundle C) : AddCommGroup (T.H0 L) :=
  T.addCommGroup L

instance chapter05GlobalSectionsTheory.module
    {C : Scheme.{u}} {k : Type u} [Field k]
    {f : C ⟶ AlgebraicGeometry.Spec (.of k)}
    [T : Chapter05GlobalSectionsTheory C k f]
    (L : Chapter05LineBundle C) : Module k (T.H0 L) :=
  letI : AddCommGroup (T.H0 L) := T.addCommGroup L
  T.module L

abbrev Chapter05H0 {C : Scheme.{u}} {k : Type u} [Field k]
    {f : C ⟶ AlgebraicGeometry.Spec (.of k)}
    [Chapter05GlobalSectionsTheory C k f]
    (L : Chapter05LineBundle C) : Type u :=
  Chapter05GlobalSectionsTheory.H0 (f := f) L

def chapter05H0Finrank {C : Scheme.{u}} {k : Type u} [Field k]
    {f : C ⟶ AlgebraicGeometry.Spec (.of k)}
    [T : Chapter05GlobalSectionsTheory C k f]
    (L : Chapter05LineBundle C) : ℕ :=
  letI : AddCommGroup (T.H0 L) := T.addCommGroup L
  letI : Module k (T.H0 L) := T.module L
  Module.finrank k (T.H0 L)

/- LOCAL_DEPENDENCY_GUESS: the pinned cohomology API does not yet expose the standard
negative-degree vanishing theorem for proper integral curves, so the section-space interface keeps
that theorem as a separate reusable hypothesis rather than baking a particular line bundle into the
exceptional-curve data. -/
class Chapter05NegativeDegreeGlobalSectionsTheory (C : Scheme.{u}) (k : Type u) [Field k]
    (f : C ⟶ AlgebraicGeometry.Spec (.of k))
    [Chapter05CurveDegreeTheory C k f]
    [Chapter05GlobalSectionsTheory C k f] : Prop where
  negative_degree_vanishing : ∀ {L : Chapter05LineBundle C},
    chapter05Degree (f := f) L < 0 →
      chapter05H0Finrank (f := f) L = 0

theorem chapter05_h0_finrank_eq_of_isomorphic
    {C : Scheme.{u}} {k : Type u} [Field k]
    {f : C ⟶ AlgebraicGeometry.Spec (.of k)}
    [T : Chapter05GlobalSectionsTheory C k f]
    {L M : Chapter05LineBundle C}
    (hLM : chapter05LineBundleIsomorphic L M) :
    chapter05H0Finrank (f := f) L = chapter05H0Finrank (f := f) M := by
  simpa [chapter05H0Finrank] using T.finrank_isomorphic hLM

/-! ### The residue-field projective line and numerical bookkeeping -/

abbrev chapter05ProjectiveLine (k : Type u) [Field k] : Scheme.{u} :=
  chapter02ProjectiveSpace (AlgebraicGeometry.Spec (CommRingCat.of k)) 1

structure Chapter05CurveNumericalData (k : Type u) [Field k] where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ AlgebraicGeometry.Spec (.of k)
  proper : IsProper structureMap
  genus : ℕ
  selfIntersection : ℤ

def chapter05NegativeSelfIntersection {k : Type u} [Field k]
    (C : Chapter05CurveNumericalData k) : Prop :=
  C.selfIntersection < 0

def chapter05PointBlowupNumericalSignature {k : Type u} [Field k]
    (C : Chapter05CurveNumericalData k) : Prop :=
  C.genus = 0 ∧ C.selfIntersection = -1

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter05
