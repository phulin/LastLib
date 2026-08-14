import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.CommHopfAlgCat
import Mathlib.AlgebraicGeometry.EffectiveEpi
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Bialgebra.Hom
import Mathlib.RingTheory.Bialgebra.TensorProduct
import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
import Mathlib.RingTheory.Finiteness.Descent
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11.Section01TheoremAndHypotheses

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter12

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped MonObj

universe u v

/-!
Shared interfaces for Chapter 12.  Group schemes are represented by the canonical group-object
category in the slice; the remaining predicates retain the morphism properties used by the
source text instead of replacing them with finiteness shorthands.
-/

/-- An `S`-group scheme, represented as a group object in `Over S`. -/
abbrev Chapter12GroupScheme (S : Scheme.{u}) := Grp (Over S)

/-- A commutative `S`-group scheme, represented as a commutative group object in `Over S`. -/
abbrev Chapter12CommutativeGroupScheme (S : Scheme.{u}) := CommGrp (Over S)

/-- Construct an `S`-group scheme from a scheme map carrying a group-object instance. -/
def chapter12GroupSchemeOf (S G : Scheme.{u}) (f : G ⟶ S)
    [GrpObj (Over.mk f)] : Chapter12GroupScheme S :=
  { X := Over.mk f }

/-- Construct a commutative `S`-group scheme from a commutative group-object instance. -/
def chapter12CommutativeGroupSchemeOf (S G : Scheme.{u}) (f : G ⟶ S)
    [GrpObj (Over.mk f)] [IsCommMonObj (Over.mk f)] :
    Chapter12CommutativeGroupScheme S :=
  { X := Over.mk f }

namespace Chapter12GroupScheme

/-- The underlying scheme of a group scheme. -/
abbrev carrier (G : Chapter12GroupScheme S) : Scheme.{u} := G.X.left

/-- The structural morphism of a group scheme. -/
abbrev structuralMap (G : Chapter12GroupScheme S) : G.carrier ⟶ S := G.X.hom

/-- The multiplication morphism in the slice. -/
abbrev multiplication (G : Chapter12GroupScheme S) : G.X ⊗ G.X ⟶ G.X := μ[G.X]

/-! The corresponding scheme maps are exposed explicitly for the book's geometric notation. -/

/-- The multiplication scheme map `G ×ₛ G ⟶ G`. -/
abbrev multiplicationScheme (G : Chapter12GroupScheme S) :
    (G.X ⊗ G.X).left ⟶ G.carrier := G.multiplication.left

/-- The identity section in the slice. -/
abbrev identity (G : Chapter12GroupScheme S) : 𝟙_ (Over S) ⟶ G.X := η[G.X]

/-- The identity section `S ⟶ G`. -/
abbrev identityScheme (G : Chapter12GroupScheme S) : S ⟶ G.carrier := G.identity.left

/-- The inverse morphism in the slice. -/
abbrev inverse (G : Chapter12GroupScheme S) : G.X ⟶ G.X := GrpObj.inv (X := G.X)

/-- The inverse scheme map `G ⟶ G`. -/
abbrev inverseScheme (G : Chapter12GroupScheme S) : G.carrier ⟶ G.carrier := G.inverse.left

/-- The underlying scheme map of a homomorphism of group schemes. -/
abbrev homScheme {G H : Chapter12GroupScheme S} (f : G ⟶ H) : G.carrier ⟶ H.carrier :=
  f.hom.hom.left

@[simp]
theorem homScheme_id (G : Chapter12GroupScheme S) : homScheme (𝟙 G) = 𝟙 G.carrier := rfl

@[simp]
theorem homScheme_comp {G H K : Chapter12GroupScheme S} (f : G ⟶ H) (g : H ⟶ K) :
    homScheme (f ≫ g) = homScheme f ≫ homScheme g := rfl

@[ext]
theorem hom_ext {G H : Chapter12GroupScheme S} {f g : G ⟶ H}
    (h : homScheme f = homScheme g) : f = g := by
  apply Grp.hom_ext f g
  exact Over.OverMorphism.ext h

/-- Pull a group scheme back along a map of base schemes. -/
def baseChange {S T : Scheme.{u}} (p : T ⟶ S) (G : Chapter12GroupScheme S) :
    Chapter12GroupScheme T :=
  (Over.pullback p).mapGrp.obj G

/-- Pull a homomorphism of group schemes back along a map of base schemes. -/
def baseChangeHom {S T : Scheme.{u}} (p : T ⟶ S)
    {G H : Chapter12GroupScheme S} (f : G ⟶ H) :
    baseChange p G ⟶ baseChange p H :=
  (Over.pullback p).mapGrp.map f

/-- Pull an isomorphism of group schemes back along a map of base schemes. -/
def baseChangeIso {S T : Scheme.{u}} (p : T ⟶ S)
    {G H : Chapter12GroupScheme S} (e : G ≅ H) :
    baseChange p G ≅ baseChange p H :=
  (Over.pullback p).mapGrp.mapIso e

end Chapter12GroupScheme

namespace Chapter12CommutativeGroupScheme

/-- The underlying scheme of a commutative group scheme. -/
abbrev carrier (G : Chapter12CommutativeGroupScheme S) : Scheme.{u} := G.X.left

/-- The structural morphism of a commutative group scheme. -/
abbrev structuralMap (G : Chapter12CommutativeGroupScheme S) : G.carrier ⟶ S := G.X.hom

/-- The multiplication morphism in the slice. -/
abbrev multiplication (G : Chapter12CommutativeGroupScheme S) : G.X ⊗ G.X ⟶ G.X := μ[G.X]

/-- The multiplication scheme map `G ×ₛ G ⟶ G`. -/
abbrev multiplicationScheme (G : Chapter12CommutativeGroupScheme S) :
    (G.X ⊗ G.X).left ⟶ G.carrier := G.multiplication.left

/-- The identity section in the slice. -/
abbrev identity (G : Chapter12CommutativeGroupScheme S) : 𝟙_ (Over S) ⟶ G.X := η[G.X]

/-- The identity section `S ⟶ G`. -/
abbrev identityScheme (G : Chapter12CommutativeGroupScheme S) : S ⟶ G.carrier := G.identity.left

/-- The inverse morphism in the slice. -/
abbrev inverse (G : Chapter12CommutativeGroupScheme S) : G.X ⟶ G.X :=
  GrpObj.inv (X := G.X)

/-- The inverse scheme map `G ⟶ G`. -/
abbrev inverseScheme (G : Chapter12CommutativeGroupScheme S) : G.carrier ⟶ G.carrier := G.inverse.left

/-- The underlying scheme map of a homomorphism of commutative group schemes. -/
abbrev homScheme {G H : Chapter12CommutativeGroupScheme S} (f : G ⟶ H) :
    G.carrier ⟶ H.carrier := f.hom.hom.hom.left

@[simp]
theorem homScheme_id (G : Chapter12CommutativeGroupScheme S) : homScheme (𝟙 G) = 𝟙 G.carrier := rfl

@[simp]
theorem homScheme_comp {G H K : Chapter12CommutativeGroupScheme S} (f : G ⟶ H) (g : H ⟶ K) :
    homScheme (f ≫ g) = homScheme f ≫ homScheme g := rfl

@[ext]
theorem hom_ext {G H : Chapter12CommutativeGroupScheme S} {f g : G ⟶ H}
    (h : homScheme f = homScheme g) : f = g := by
  apply CommGrp.hom_ext f g
  exact Over.OverMorphism.ext h

/-- Pull a commutative group scheme back along a map of base schemes. -/
def baseChange {S T : Scheme.{u}} (p : T ⟶ S)
    (G : Chapter12CommutativeGroupScheme S) :
    Chapter12CommutativeGroupScheme T :=
  (Over.pullback p).mapCommGrp.obj G

/-- Pull a homomorphism of commutative group schemes back along a base change. -/
def baseChangeHom {S T : Scheme.{u}} (p : T ⟶ S)
    {G H : Chapter12CommutativeGroupScheme S} (f : G ⟶ H) :
    baseChange p G ⟶ baseChange p H :=
  (Over.pullback p).mapCommGrp.map f

/-- Pull an isomorphism of commutative group schemes back along a base change. -/
def baseChangeIso {S T : Scheme.{u}} (p : T ⟶ S)
    {G H : Chapter12CommutativeGroupScheme S} (e : G ≅ H) :
    baseChange p G ≅ baseChange p H :=
  (Over.pullback p).mapCommGrp.mapIso e

end Chapter12CommutativeGroupScheme

/-! ### Morphism properties used for finite-flat group objects -/

/-- The finite morphism property. -/
abbrev Chapter12Finite {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop := IsFinite f

/-- The flat morphism property. -/
abbrev Chapter12Flat {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop := Flat f

/-- The locally finite-presentation morphism property. -/
abbrev Chapter12LocallyOfFinitePresentation {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  LocallyOfFinitePresentation f

/-- Finite presentation, keeping the quasi-compact part explicit. -/
def Chapter12FinitePresentation {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  LocallyOfFinitePresentation f ∧ QuasiCompact f

/-- Finite and flat, with the two source properties kept separate. -/
def Chapter12FiniteFlat {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  IsFinite f ∧ Flat f

/-- Finite, flat, and locally of finite presentation. -/
def Chapter12FiniteLocallyFree {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f

/-- Finite locally free of a specified constant rank. -/
def Chapter12FiniteLocallyFreeOfRank {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) : Prop :=
  Chapter12FiniteLocallyFree f ∧ ∀ y : Y, Scheme.Hom.finrank f y = n

/-- Faithfully flat morphisms, expressed by flatness and surjectivity. -/
def Chapter12FaithfullyFlat {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  Flat f ∧ Surjective f

/-- Faithfully flat and locally of finite presentation, without a quasi-compact hypothesis. -/
def Chapter12FaithfullyFlatLocallyOfFinitePresentation
    {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  Flat f ∧ Surjective f ∧ LocallyOfFinitePresentation f

/-- An fpqc cover in the convention used by this chapter. -/
def Chapter12FpqcCover {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  QuasiCompact f ∧ Flat f ∧ Surjective f

/-- A single fppf cover: flat, locally finitely presented, and surjective.  Quasi-compactness is
separate because a surjective fppf morphism need not be quasi-compact. -/
def Chapter12Fppf {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  Flat f ∧ LocallyOfFinitePresentation f ∧ Surjective f

theorem chapter12_fpqcCover_iff_faithfullyFlat_and_quasiCompact
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Chapter12FpqcCover f ↔ Chapter12FaithfullyFlat f ∧ QuasiCompact f := by
  constructor
  · rintro ⟨hq, hf, hs⟩
    exact ⟨⟨hf, hs⟩, hq⟩
  · rintro ⟨⟨hf, hs⟩, hq⟩
    exact ⟨hq, hf, hs⟩

theorem chapter12_fppf_iff_faithfullyFlatLocallyOfFinitePresentation
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Chapter12Fppf f ↔
      Chapter12FaithfullyFlatLocallyOfFinitePresentation f := by
  constructor
  · rintro ⟨hf, hlfp, hs⟩
    exact ⟨hf, hs, hlfp⟩
  · rintro ⟨hf, hs, hlfp⟩
    exact ⟨hf, hlfp, hs⟩

theorem chapter12_fppf_quasiCompact_to_fpqcCover
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Chapter12Fppf f → QuasiCompact f → Chapter12FpqcCover f := by
  intro hfppf hq
  exact ⟨hq, hfppf.1, hfppf.2.2⟩

/-! The canonical Chapter 11 API uses the order `flat ∧ surjective ∧ quasi-compact` for a
singleton fpqc morphism, whereas the book-facing predicate above follows the order in Chapter 2.
This bridge keeps the two interfaces interchangeable in descent proofs. -/

theorem chapter12_fpqcCover_isFpqcMorphism
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p) :
    LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11.Scheme.IsFpqcMorphism p := by
  exact ⟨hp.2.1, hp.2.2, hp.1⟩

/-- A finite-flat group scheme package used when the property is part of the object. -/
structure Chapter12FiniteFlatGroupScheme (S : Scheme.{u}) where
  group : Chapter12GroupScheme S
  finiteFlat : Chapter12FiniteFlat group.X.hom

/-- A commutative finite locally free group scheme package. -/
structure Chapter12FiniteLocallyFreeCommutativeGroupScheme (S : Scheme.{u}) where
  group : Chapter12CommutativeGroupScheme S
  finiteLocallyFree : Chapter12FiniteLocallyFree group.X.hom

/-- A finite locally free (not necessarily commutative) group scheme package. -/
structure Chapter12FiniteLocallyFreeGroupScheme (S : Scheme.{u}) where
  group : Chapter12GroupScheme S
  finiteLocallyFree : Chapter12FiniteLocallyFree group.X.hom

/-!
The following records refine the canonical scheme-valued descent interface from Chapter 11 with
group-object structure.  The explicit pullback-compatibility fields keep the group comparison maps
in the same pseudofunctorial form as the underlying scheme descent datum.
-/

/-! The associativity comparison for iterated pullback of a group scheme. -/

def chapter12GroupSchemeBaseChangeCompIso
    {S T U : Scheme.{u}} (p : T ⟶ S) (q : U ⟶ T)
    (G : Chapter12GroupScheme S) :
    Chapter12GroupScheme.baseChange q (Chapter12GroupScheme.baseChange p G) ≅
      Chapter12GroupScheme.baseChange (q ≫ p) G := by
  exact
    ((Functor.mapGrpCompIso (F := Over.pullback p) (G := Over.pullback q)).app G).symm ≪≫
      ((Functor.mapGrpNatIso (Over.pullbackComp q p)).app G).symm

def chapter12CommutativeGroupSchemeBaseChangeCompIso
    {S T U : Scheme.{u}} (p : T ⟶ S) (q : U ⟶ T)
    (G : Chapter12CommutativeGroupScheme S) :
    Chapter12CommutativeGroupScheme.baseChange q
        (Chapter12CommutativeGroupScheme.baseChange p G) ≅
      Chapter12CommutativeGroupScheme.baseChange (q ≫ p) G := by
  exact
    ((Functor.mapCommGrpCompIso (F := Over.pullback p) (G := Over.pullback q)).app G).symm ≪≫
      ((Functor.mapCommGrpNatIso (Over.pullbackComp q p)).app G).symm

/-! ### Coherent descent data -/

/--
Coherent descent data for a group object over an fpqc cover.  The comparison maps are given for
all pairs of test maps with the same composite to the base; `compare_comp` is the cocycle law.
This is the group-object form of the descent datum used by the fpqc stack statement.
-/
structure Chapter12GroupSchemeDescentDatum {S T : Scheme.{u}} (p : T ⟶ S) where
  upstairs : Chapter12GroupScheme T
  compare {U : Scheme.{u}} (q₁ q₂ : U ⟶ T) (h : q₁ ≫ p = q₂ ≫ p) :
    Chapter12GroupScheme.baseChange q₁ upstairs ≅
      Chapter12GroupScheme.baseChange q₂ upstairs
  compare_self {U : Scheme.{u}} (q : U ⟶ T) (h : q ≫ p = q ≫ p) :
    compare q q h = Iso.refl _
  compare_comp {U : Scheme.{u}} (q₁ q₂ q₃ : U ⟶ T)
      (h₁₂ : q₁ ≫ p = q₂ ≫ p) (h₂₃ : q₂ ≫ p = q₃ ≫ p)
      (h₁₃ : q₁ ≫ p = q₃ ≫ p) :
    (compare q₁ q₂ h₁₂).hom ≫ (compare q₂ q₃ h₂₃).hom =
      (compare q₁ q₃ h₁₃).hom
  compare_pull {U V : Scheme.{u}} (r : V ⟶ U) (q₁ q₂ : U ⟶ T)
      (h : q₁ ≫ p = q₂ ≫ p)
      (h' : (r ≫ q₁) ≫ p = (r ≫ q₂) ≫ p) :
    (Chapter12GroupScheme.baseChangeIso r (compare q₁ q₂ h)).hom =
      (chapter12GroupSchemeBaseChangeCompIso q₁ r upstairs).hom ≫
        (compare (r ≫ q₁) (r ≫ q₂) h').hom ≫
          (chapter12GroupSchemeBaseChangeCompIso q₂ r upstairs).inv

/-- A morphism of the preceding descent data. -/
def chapter12DescentHomCompatible {S T : Scheme.{u}} {p : T ⟶ S}
    (D₁ D₂ : Chapter12GroupSchemeDescentDatum p)
    (f : D₁.upstairs ⟶ D₂.upstairs) : Prop :=
  ∀ {U : Scheme.{u}} (q₁ q₂ : U ⟶ T) (h : q₁ ≫ p = q₂ ≫ p),
    Chapter12GroupScheme.baseChangeHom q₁ f ≫ (D₂.compare q₁ q₂ h).hom =
      (D₁.compare q₁ q₂ h).hom ≫ Chapter12GroupScheme.baseChangeHom q₂ f

/-- The commutative-group-object version of coherent fpqc descent data. -/
structure Chapter12CommutativeGroupSchemeDescentDatum {S T : Scheme.{u}} (p : T ⟶ S) where
  upstairs : Chapter12CommutativeGroupScheme T
  compare {U : Scheme.{u}} (q₁ q₂ : U ⟶ T) (h : q₁ ≫ p = q₂ ≫ p) :
    Chapter12CommutativeGroupScheme.baseChange q₁ upstairs ≅
      Chapter12CommutativeGroupScheme.baseChange q₂ upstairs
  compare_self {U : Scheme.{u}} (q : U ⟶ T) (h : q ≫ p = q ≫ p) :
    compare q q h = Iso.refl _
  compare_comp {U : Scheme.{u}} (q₁ q₂ q₃ : U ⟶ T)
      (h₁₂ : q₁ ≫ p = q₂ ≫ p) (h₂₃ : q₂ ≫ p = q₃ ≫ p)
      (h₁₃ : q₁ ≫ p = q₃ ≫ p) :
    (compare q₁ q₂ h₁₂).hom ≫ (compare q₂ q₃ h₂₃).hom =
      (compare q₁ q₃ h₁₃).hom
  compare_pull {U V : Scheme.{u}} (r : V ⟶ U) (q₁ q₂ : U ⟶ T)
      (h : q₁ ≫ p = q₂ ≫ p)
      (h' : (r ≫ q₁) ≫ p = (r ≫ q₂) ≫ p) :
    (Chapter12CommutativeGroupScheme.baseChangeIso r (compare q₁ q₂ h)).hom =
      (chapter12CommutativeGroupSchemeBaseChangeCompIso q₁ r upstairs).hom ≫
        (compare (r ≫ q₁) (r ≫ q₂) h').hom ≫
          (chapter12CommutativeGroupSchemeBaseChangeCompIso q₂ r upstairs).inv

/-- Compatibility of a commutative group homomorphism with commutative descent data. -/
def chapter12CommutativeDescentHomCompatible {S T : Scheme.{u}} {p : T ⟶ S}
    (D₁ D₂ : Chapter12CommutativeGroupSchemeDescentDatum p)
    (f : D₁.upstairs ⟶ D₂.upstairs) : Prop :=
  ∀ {U : Scheme.{u}} (q₁ q₂ : U ⟶ T) (h : q₁ ≫ p = q₂ ≫ p),
    Chapter12CommutativeGroupScheme.baseChangeHom q₁ f ≫ (D₂.compare q₁ q₂ h).hom =
      (D₁.compare q₁ q₂ h).hom ≫
        Chapter12CommutativeGroupScheme.baseChangeHom q₂ f

/-!
The canonical comparison between two iterated pullbacks of an object already defined over the
base.  The equality `h` identifies the two composites to the base; the resulting isomorphism is
the one used when comparing an effective descent object with a prescribed datum.
-/

def chapter12GroupSchemeBaseChangeComparison
    {S T U : Scheme.{u}} (p : T ⟶ S) (G : Chapter12GroupScheme S)
    (q₁ q₂ : U ⟶ T) (h : q₁ ≫ p = q₂ ≫ p) :
    Chapter12GroupScheme.baseChange q₁ (Chapter12GroupScheme.baseChange p G) ≅
      Chapter12GroupScheme.baseChange q₂ (Chapter12GroupScheme.baseChange p G) := by
  exact chapter12GroupSchemeBaseChangeCompIso p q₁ G ≪≫
    eqToIso (by rw [h]) ≪≫ (chapter12GroupSchemeBaseChangeCompIso p q₂ G).symm

def chapter12CommutativeGroupSchemeBaseChangeComparison
    {S T U : Scheme.{u}} (p : T ⟶ S)
    (G : Chapter12CommutativeGroupScheme S)
    (q₁ q₂ : U ⟶ T) (h : q₁ ≫ p = q₂ ≫ p) :
    Chapter12CommutativeGroupScheme.baseChange q₁
        (Chapter12CommutativeGroupScheme.baseChange p G) ≅
      Chapter12CommutativeGroupScheme.baseChange q₂
        (Chapter12CommutativeGroupScheme.baseChange p G) := by
  exact chapter12CommutativeGroupSchemeBaseChangeCompIso p q₁ G ≪≫
    eqToIso (by rw [h]) ≪≫
      (chapter12CommutativeGroupSchemeBaseChangeCompIso p q₂ G).symm

/-!
An upstairs isomorphism is a genuine comparison with a descent datum only when it intertwines the
datum's overlap isomorphisms with the canonical pullback comparisons.  Keeping this condition
explicit prevents an arbitrary isomorphism of the upstairs objects from being mistaken for an
effective descent comparison.
-/

def chapter12GroupSchemeDescentComparisonCompatible
    {S T : Scheme.{u}} {p : T ⟶ S}
    (D : Chapter12GroupSchemeDescentDatum p)
    (G : Chapter12GroupScheme S)
    (e : Chapter12GroupScheme.baseChange p G ≅ D.upstairs) : Prop :=
  ∀ {U : Scheme.{u}} (q₁ q₂ : U ⟶ T) (h : q₁ ≫ p = q₂ ≫ p),
    (Chapter12GroupScheme.baseChangeIso q₁ e).hom ≫ (D.compare q₁ q₂ h).hom =
      (chapter12GroupSchemeBaseChangeComparison p G q₁ q₂ h).hom ≫
        (Chapter12GroupScheme.baseChangeIso q₂ e).hom

def chapter12CommutativeGroupSchemeDescentComparisonCompatible
    {S T : Scheme.{u}} {p : T ⟶ S}
    (D : Chapter12CommutativeGroupSchemeDescentDatum p)
    (G : Chapter12CommutativeGroupScheme S)
    (e : Chapter12CommutativeGroupScheme.baseChange p G ≅ D.upstairs) : Prop :=
  ∀ {U : Scheme.{u}} (q₁ q₂ : U ⟶ T) (h : q₁ ≫ p = q₂ ≫ p),
    (Chapter12CommutativeGroupScheme.baseChangeIso q₁ e).hom ≫
        (D.compare q₁ q₂ h).hom =
      (chapter12CommutativeGroupSchemeBaseChangeComparison p G q₁ q₂ h).hom ≫
        (Chapter12CommutativeGroupScheme.baseChangeIso q₂ e).hom

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter12
