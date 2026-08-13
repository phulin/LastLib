import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Sym.Basic
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.Section01ProjectiveBundles
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.Dependencies

/-!
# Chapter 13: universal constructions for later geometry

This file contains the small amount of shared infrastructure used by the four
source sections.  Mathlib supplies the scheme-theoretic pullback, fiber,
immersion, and geometric-fiber APIs used below.  Relative Hilbert schemes,
relative projective spaces, and algebraic symmetric powers are not part of the
pinned Mathlib snapshot, so their book-facing interfaces are recorded as
explicit representability data rather than hidden behind an unavailable
construction.
-/

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter13

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04

noncomputable section

/-! ## Relative schemes and pullbacks -/

/-- A scheme equipped with a specified morphism to the base scheme. -/
structure Chapter13RelativeScheme (S : Scheme) where
  scheme : Scheme
  toBase : scheme ⟶ S

/-- A morphism of the relative schemes over a fixed base. -/
structure Chapter13RelativeMap {S : Scheme}
    (T U : Chapter13RelativeScheme S) where
  map : T.scheme ⟶ U.scheme
  over : map ≫ U.toBase = T.toBase

/-- The identity relative morphism. -/
def chapter13RelativeMapId {S : Scheme} (T : Chapter13RelativeScheme S) :
    Chapter13RelativeMap T T where
  map := 𝟙 T.scheme
  over := by simp

/-- Composition of relative morphisms. -/
def chapter13RelativeMapComp {S : Scheme}
    {T U V : Chapter13RelativeScheme S}
    (f : Chapter13RelativeMap T U) (g : Chapter13RelativeMap U V) :
    Chapter13RelativeMap T V where
  map := f.map ≫ g.map
  over := by rw [Category.assoc, g.over, f.over]

/-! A scheme isomorphism over the fixed base. -/

structure Chapter13RelativeIso {S : Scheme}
    (T U : Chapter13RelativeScheme S) where
  hom : Chapter13RelativeMap T U
  inv : Chapter13RelativeMap U T
  hom_inv_id : hom.map ≫ inv.map = 𝟙 T.scheme
  inv_hom_id : inv.map ≫ hom.map = 𝟙 U.scheme

@[simp]
theorem chapter13RelativeMapId_map {S : Scheme} (T : Chapter13RelativeScheme S) :
    (chapter13RelativeMapId T).map = 𝟙 T.scheme := rfl

@[simp]
theorem chapter13RelativeMapComp_map {S : Scheme}
    {T U V : Chapter13RelativeScheme S}
    (f : Chapter13RelativeMap T U) (g : Chapter13RelativeMap U V) :
    (chapter13RelativeMapComp f g).map = f.map ≫ g.map := rfl

/-- A base change of a scheme morphism along a second map to the base. -/
def chapter13BaseChange {X S T : Scheme} (f : X ⟶ S) (g : T ⟶ S) : Scheme :=
  pullback f g

abbrev chapter13BaseChangeToSource {X S T : Scheme} (f : X ⟶ S) (g : T ⟶ S) :
    chapter13BaseChange f g ⟶ X :=
  pullback.fst f g

abbrev chapter13BaseChangeToTest {X S T : Scheme} (f : X ⟶ S) (g : T ⟶ S) :
    chapter13BaseChange f g ⟶ T :=
  pullback.snd f g

@[simp, reassoc]
theorem chapter13BaseChange_condition {X S T : Scheme} (f : X ⟶ S) (g : T ⟶ S) :
    chapter13BaseChangeToSource f g ≫ f = chapter13BaseChangeToTest f g ≫ g :=
  pullback.condition

/-- The relative product over the base, with its two projections. -/
abbrev chapter13RelativeProduct {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) : Scheme :=
  pullback f g

abbrev chapter13RelativeProduct_fst {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) :
    chapter13RelativeProduct f g ⟶ X :=
  pullback.fst f g

abbrev chapter13RelativeProduct_snd {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) :
    chapter13RelativeProduct f g ⟶ Y :=
  pullback.snd f g

abbrev chapter13RelativeProductToBase {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) :
    chapter13RelativeProduct f g ⟶ S :=
  chapter13RelativeProduct_fst f g ≫ f

@[simp, reassoc]
theorem chapter13RelativeProductToBase_eq_snd {X Y S : Scheme}
    (f : X ⟶ S) (g : Y ⟶ S) :
    chapter13RelativeProductToBase f g = chapter13RelativeProduct_snd f g ≫ g := by
  exact pullback.condition

/-- The graph map into a relative product. -/
def chapter13Graph {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S)
    (u : X ⟶ Y) (hu : u ≫ g = f) : X ⟶ chapter13RelativeProduct f g :=
  pullback.lift (𝟙 X) u (by simp [hu])

@[simp, reassoc]
theorem chapter13Graph_fst {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S)
    (u : X ⟶ Y) (hu : u ≫ g = f) :
    chapter13Graph f g u hu ≫ chapter13RelativeProduct_fst f g = 𝟙 X :=
  pullback.lift_fst _ _ _

@[simp, reassoc]
theorem chapter13Graph_snd {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S)
    (u : X ⟶ Y) (hu : u ≫ g = f) :
    chapter13Graph f g u hu ≫ chapter13RelativeProduct_snd f g = u :=
  pullback.lift_snd _ _ _

/-- The graph is closed when the target is separated over the base. -/
theorem chapter13Graph_isClosedImmersion {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S)
    [IsSeparated g] (u : X ⟶ Y) (hu : u ≫ g = f) :
    IsClosedImmersion (chapter13Graph f g u hu) := by
  sorry

/-- The open subscheme of a relative scheme, retaining its structure map to the base. -/
def chapter13OpenRelativeScheme {S : Scheme}
    (T : Chapter13RelativeScheme S) (U : T.scheme.Opens) : Chapter13RelativeScheme S where
  scheme := U.toScheme
  toBase := U.ι ≫ T.toBase

/-! ## Book-facing line bundles and projective embeddings -/

/-
The preceding chapters supply the canonical invertible-sheaf, ampleness, and
projective-space interfaces used here.
-/

/-- A rank-one locally free sheaf together with the book's ampleness datum. -/
abbrev chapter13RankOneSheaf {X : Scheme} (lineBundle : X.Modules) : Prop :=
  chapter04IsInvertible lineBundle

structure Chapter13Polarization {X S : Scheme} (f : X ⟶ S) where
  lineBundle : Chapter04LineBundle X
  ample : chapter04Ample f lineBundle

/-- The relative projective-space datum needed to define a projective morphism. -/
structure Chapter13RelativeProjectiveSpaceData (S : Scheme) (n : ℕ) where
  bundle : Chapter04ProjectiveBundle S
  /-- Identification with the canonical `ℙ^n_S`, over the base. -/
  isProjectiveSpace : Nonempty
    { e : bundle.space ≅ chapter02ProjectiveSpace S n //
      e.hom ≫ chapter02ProjectiveSpaceProjection S n = bundle.projection }

abbrev Chapter13RelativeProjectiveSpaceData.scheme
    {S : Scheme} {n : ℕ} (P : Chapter13RelativeProjectiveSpaceData S n) : Scheme :=
  P.bundle.space

abbrev Chapter13RelativeProjectiveSpaceData.toBase
    {S : Scheme} {n : ℕ} (P : Chapter13RelativeProjectiveSpaceData S n) :
    P.scheme ⟶ S :=
  P.bundle.projection

/-- A closed embedding into a relative projective space. -/
def Chapter13ProjectiveMorphism {X S : Scheme} (f : X ⟶ S) : Prop :=
  chapter04Projective f

/-! ## Hilbert-polynomial certificates and relative families -/

/-- A numerical Hilbert-function certificate for a map into a polarized ambient scheme.

Closedness is recorded by the surrounding family or graph data.  The Hilbert
function is integer-valued, while the polynomial uses the canonical
integer-valued-over-`ℚ` normalization from Chapter 8.
-/
abbrev Chapter13NumericalPolynomial := Chapter08NumericalPolynomial

structure Chapter13HilbertPolynomialCertificate
    {S : Scheme} (Z A : Scheme) (i : Z ⟶ A) (aS : A ⟶ S)
    (L : Chapter13Polarization aS) where
  hilbertFunction : ℕ → ℤ
  /-- A Hilbert function is a dimension, hence is nonnegative in every degree. -/
  hilbertFunction_nonnegative : ∀ n, 0 ≤ hilbertFunction n
  polynomial : Chapter13NumericalPolynomial
  agrees_eventually : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    hilbertFunction n = polynomial.value n

/-- A flat proper finitely presented closed family in a base change of an ambient scheme. -/
structure Chapter13FlatClosedFamily {S X : Scheme} (xS : X ⟶ S)
    (L : Chapter13Polarization xS) (P : Chapter13NumericalPolynomial)
    (T : Chapter13RelativeScheme S) where
  scheme : Scheme
  projection : scheme ⟶ T.scheme
  inclusion : scheme ⟶ chapter13BaseChange xS T.toBase
  inclusion_over : inclusion ≫ chapter13BaseChangeToTest xS T.toBase = projection
  closed : IsClosedImmersion inclusion
  flat : Flat projection
  finitePresentation : LocallyOfFinitePresentation projection
  proper : IsProper projection
  projective : Chapter13ProjectiveMorphism projection
  hilbert : Chapter13HilbertPolynomialCertificate
      scheme X (inclusion ≫ chapter13BaseChangeToSource xS T.toBase) xS L
  hilbert_polynomial : hilbert.polynomial = P

/-- A contravariant functor on the category of schemes over a fixed base. -/
structure Chapter13RelativePresheaf (S : Scheme) where
  obj : Chapter13RelativeScheme S → Type*
  map : {T U : Chapter13RelativeScheme S} →
    Chapter13RelativeMap T U → obj U → obj T
  map_id : ∀ (T : Chapter13RelativeScheme S) (x : obj T),
    map (chapter13RelativeMapId T) x = x
  map_comp : ∀ {T U V : Chapter13RelativeScheme S}
    (f : Chapter13RelativeMap T U) (g : Chapter13RelativeMap U V) (x : obj V),
    map f (map g x) = map (chapter13RelativeMapComp f g) x

/-- Representability of a relative presheaf, including the naturality equation. -/
structure Chapter13RepresentedRelativePresheaf {S : Scheme}
    (F : Chapter13RelativePresheaf S) where
  representative : Chapter13RelativeScheme S
  equiv : ∀ T : Chapter13RelativeScheme S,
    F.obj T ≃ Chapter13RelativeMap T representative
  naturality : ∀ {T U : Chapter13RelativeScheme S}
    (f : Chapter13RelativeMap T U) (x : F.obj U),
    equiv T (F.map f x) =
      chapter13RelativeMapComp f (equiv U x)

/-- Hilbert representability data for one fixed ambient polarization and polynomial. -/
structure Chapter13HilbertSchemeData {S X : Scheme} (xS : X ⟶ S)
    (L : Chapter13Polarization xS) (P : Chapter13NumericalPolynomial) where
  functor : Chapter13RelativePresheaf S
  familyPullback : {T U : Chapter13RelativeScheme S} →
    Chapter13RelativeMap T U →
      Chapter13FlatClosedFamily xS L P U →
        Chapter13FlatClosedFamily xS L P T
  familyPullback_id : ∀ {T : Chapter13RelativeScheme S}
    (x : Chapter13FlatClosedFamily xS L P T),
    familyPullback (chapter13RelativeMapId T) x = x
  familyPullback_comp : ∀ {T U V : Chapter13RelativeScheme S}
    (f : Chapter13RelativeMap T U) (g : Chapter13RelativeMap U V)
    (x : Chapter13FlatClosedFamily xS L P V),
    familyPullback f (familyPullback g x) =
      familyPullback (chapter13RelativeMapComp f g) x
  classifies : ∀ T : Chapter13RelativeScheme S,
    functor.obj T ≃ Chapter13FlatClosedFamily xS L P T
  classifies_naturality : ∀ {T U : Chapter13RelativeScheme S}
    (f : Chapter13RelativeMap T U) (x : functor.obj U),
    classifies T (functor.map f x) =
      familyPullback f (classifies U x)
  represented : Chapter13RepresentedRelativePresheaf functor
  projective : Chapter13ProjectiveMorphism represented.representative.toBase
  finitePresentation :
    LocallyOfFinitePresentation represented.representative.toBase

/-- The representing relative scheme underlying a Hilbert-scheme datum. -/
def chapter13HilbertScheme {S X : Scheme} {xS : X ⟶ S}
    {L : Chapter13Polarization xS} {P : Chapter13NumericalPolynomial}
    (H : Chapter13HilbertSchemeData xS L P) : Scheme :=
  H.represented.representative.scheme

/-- Its structure morphism to the base. -/
def chapter13HilbertSchemeToBase {S X : Scheme} {xS : X ⟶ S}
    {L : Chapter13Polarization xS} {P : Chapter13NumericalPolynomial}
    (H : Chapter13HilbertSchemeData xS L P) :
    chapter13HilbertScheme H ⟶ S :=
  H.represented.representative.toBase

/-- The universal flat closed family supplied by representability. -/
def chapter13UniversalHilbertFamily {S X : Scheme} {xS : X ⟶ S}
    {L : Chapter13Polarization xS} {P : Chapter13NumericalPolynomial}
    (H : Chapter13HilbertSchemeData xS L P) :
    Chapter13FlatClosedFamily xS L P H.represented.representative :=
  H.classifies _ ((H.represented.equiv _).symm (chapter13RelativeMapId _))

/-! ## Universal families and scheme-theoretic loci -/

/-- A universal family with the properties used by the closed-locus criteria. -/
structure Chapter13UniversalFamilyData (H X : Scheme) where
  base : Scheme
  parameterToBase : H ⟶ base
  ambientToBase : X ⟶ base
  family : Scheme
  projection : family ⟶ H
  map : family ⟶ X
  map_over : map ≫ ambientToBase = projection ≫ parameterToBase
  familyToProduct : family ⟶ chapter13RelativeProduct ambientToBase parameterToBase
  familyToProduct_fst :
    familyToProduct ≫ chapter13RelativeProduct_fst ambientToBase parameterToBase = map
  familyToProduct_snd :
    familyToProduct ≫ chapter13RelativeProduct_snd ambientToBase parameterToBase = projection
  closed : IsClosedImmersion familyToProduct
  flat : Flat projection
  finitePresentation : LocallyOfFinitePresentation projection
  proper : IsProper projection

/-- The family over a test scheme `T ⟶ H`. -/
def chapter13UniversalFamilyBaseChange {H X T : Scheme}
    (U : Chapter13UniversalFamilyData H X) (t : T ⟶ H) : Scheme :=
  pullback U.projection t

/-- The map from that base change to the ambient scheme. -/
def chapter13UniversalFamilyBaseChangedMap {H X T : Scheme}
    (U : Chapter13UniversalFamilyData H X) (t : T ⟶ H) :
    chapter13UniversalFamilyBaseChange U t ⟶ X :=
  pullback.fst U.projection t ≫ U.map

/-- Containment of the universal family in a fixed closed subscheme. -/
def chapter13ContainsFixedSubscheme {H X Z : Scheme}
    (U : Chapter13UniversalFamilyData H X) (j : Z ⟶ X)
    (T : Scheme) (t : T ⟶ H) : Prop :=
  ∃ q : chapter13UniversalFamilyBaseChange U t ⟶ Z,
    q ≫ j = chapter13UniversalFamilyBaseChangedMap U t

/-- Invariance under a fixed endomorphism, expressed on the universal family. -/
def chapter13InvariantUnder {H X : Scheme}
    (U : Chapter13UniversalFamilyData H X) (σ : X ⟶ X)
    (T : Scheme) (t : T ⟶ H) : Prop :=
  ∃ q : chapter13UniversalFamilyBaseChange U t ⟶
      chapter13UniversalFamilyBaseChange U t,
    q ≫ pullback.snd U.projection t = pullback.snd U.projection t ∧
    q ≫ chapter13UniversalFamilyBaseChangedMap U t =
      chapter13UniversalFamilyBaseChangedMap U t ≫ σ

/-- Incidence of a universal family with a fixed closed subscheme. -/
def chapter13Incidence {H X Z : Scheme}
    (U : Chapter13UniversalFamilyData H X) (j : Z ⟶ X)
    (T : Scheme) (t : T ⟶ H) : Prop :=
  IsSchemeTheoreticallyDominant
    (pullback.fst (chapter13UniversalFamilyBaseChangedMap U t) j ≫
      pullback.snd U.projection t)

/-- Avoidance of a fixed closed subscheme. -/
def chapter13Avoids {H X Z : Scheme}
    (U : Chapter13UniversalFamilyData H X) (j : Z ⟶ X)
    (T : Scheme) (t : T ⟶ H) : Prop :=
  IsEmpty ↑(pullback (C := Scheme)
    (chapter13UniversalFamilyBaseChangedMap U t) j)

/-- Smoothness of all geometric fibers of a family. -/
def chapter13SmoothFibers {Z T : Scheme} (p : Z ⟶ T) : Prop :=
  ∀ t : T, Smooth (p.fiberToSpecResidueField t)

/-- Geometric reducedness of all geometric fibers, in the canonical Mathlib form. -/
def chapter13GeometricallyReducedFibers {Z T : Scheme} (p : Z ⟶ T) : Prop :=
  ∀ t : T, GeometricallyReduced (p.fiberToSpecResidueField t)

/-- Equality of two maps after restricting them to a universal family. -/
def chapter13UniversalFamilyMapsEqual {H X Y : Scheme}
    (U : Chapter13UniversalFamilyData H X) (f g : X ⟶ Y)
    (T : Scheme) (t : T ⟶ H) : Prop :=
  pullback.fst U.projection t ≫ U.map ≫ f =
    pullback.fst U.projection t ≫ U.map ≫ g

/-- A closed condition on all scheme-valued test points of a parameter scheme. -/
structure Chapter13ClosedLocusData (H : Scheme)
    (Q : ∀ T : Scheme, (T ⟶ H) → Prop) where
  ideal : H.IdealSheafData
  represents : ∀ (T : Scheme) (t : T ⟶ H),
    Q T t ↔ ∃ q : T ⟶ ideal.subscheme,
      q ≫ ideal.subschemeι = t

/-- The closed subscheme represented by a closed-locus datum. -/
def chapter13ClosedLocus {H : Scheme}
    {Q : ∀ T : Scheme, (T ⟶ H) → Prop}
    (C : Chapter13ClosedLocusData H Q) : Scheme :=
  C.ideal.subscheme

def chapter13ClosedLocusι {H : Scheme}
    {Q : ∀ T : Scheme, (T ⟶ H) → Prop}
    (C : Chapter13ClosedLocusData H Q) : chapter13ClosedLocus C ⟶ H :=
  C.ideal.subschemeι

theorem chapter13ClosedLocus_isClosedImmersion {H : Scheme}
    {Q : ∀ T : Scheme, (T ⟶ H) → Prop}
    (C : Chapter13ClosedLocusData H Q) :
    IsClosedImmersion (chapter13ClosedLocusι C) := by
  change IsClosedImmersion C.ideal.subschemeι
  infer_instance

/-- An open condition on all scheme-valued test points of a parameter scheme. -/
structure Chapter13OpenLocusData (H : Scheme)
    (Q : ∀ T : Scheme, (T ⟶ H) → Prop) where
  locus : H.Opens
  represents : ∀ (T : Scheme) (t : T ⟶ H),
    Q T t ↔ ∃ q : T ⟶ locus.toScheme, q ≫ locus.ι = t

def chapter13OpenLocus {H : Scheme}
    {Q : ∀ T : Scheme, (T ⟶ H) → Prop}
    (O : Chapter13OpenLocusData H Q) : Scheme :=
  O.locus.toScheme

def chapter13OpenLocusι {H : Scheme}
    {Q : ∀ T : Scheme, (T ⟶ H) → Prop}
    (O : Chapter13OpenLocusData H Q) : chapter13OpenLocus O ⟶ H :=
  O.locus.ι

theorem chapter13OpenLocus_isOpenImmersion {H : Scheme}
    {Q : ∀ T : Scheme, (T ⟶ H) → Prop}
    (O : Chapter13OpenLocusData H Q) :
    IsOpenImmersion (chapter13OpenLocusι O) := by
  change IsOpenImmersion O.locus.ι
  infer_instance

/-- A locally closed condition: first impose a closed equation, then an open one. -/
structure Chapter13LocallyClosedLocusData (H : Scheme)
    (Q : ∀ T : Scheme, (T ⟶ H) → Prop) where
  ideal : H.IdealSheafData
  locus : ideal.subscheme.Opens
  represents : ∀ (T : Scheme) (t : T ⟶ H),
    Q T t ↔ ∃ q : T ⟶ locus.toScheme,
      q ≫ locus.ι ≫ ideal.subschemeι = t

def chapter13LocallyClosedLocus {H : Scheme}
    {Q : ∀ T : Scheme, (T ⟶ H) → Prop}
    (L : Chapter13LocallyClosedLocusData H Q) : Scheme :=
  L.locus.toScheme

def chapter13LocallyClosedLocusι {H : Scheme}
    {Q : ∀ T : Scheme, (T ⟶ H) → Prop}
    (L : Chapter13LocallyClosedLocusData H Q) :
    chapter13LocallyClosedLocus L ⟶ H :=
  L.locus.ι ≫ L.ideal.subschemeι

theorem chapter13LocallyClosedLocus_isLocallyClosed {H : Scheme}
    {Q : ∀ T : Scheme, (T ⟶ H) → Prop}
    (L : Chapter13LocallyClosedLocusData H Q) :
    IsOpenImmersion L.locus.ι ∧ IsClosedImmersion L.ideal.subschemeι := by
  constructor <;> infer_instance

theorem chapter13LocallyClosedLocus_isImmersion {H : Scheme}
    {Q : ∀ T : Scheme, (T ⟶ H) → Prop}
    (L : Chapter13LocallyClosedLocusData H Q) :
    IsImmersion (chapter13LocallyClosedLocusι L) := by
  change IsImmersion (L.locus.ι ≫ L.ideal.subschemeι)
  infer_instance

/-- Vanishing of a sheaf morphism, the coefficient-ideal formulation of an equation. -/
def chapter13SheafEquation {H : Scheme} {A B : H.Modules} (φ : A ⟶ B) : Prop :=
  φ = 0

theorem chapter13SheafEquation_iff {H : Scheme} {A B : H.Modules} (φ : A ⟶ B) :
    chapter13SheafEquation φ ↔ φ = 0 := Iff.rfl

/-! ## Symmetric powers and finite-length families -/

/-- Ordered `d`-tuples in a type. -/
abbrev chapter13OrderedTuple (X : Type*) (d : ℕ) := Fin d → X

/-- Two ordered tuples differ by a permutation of their entries. -/
def chapter13TuplePermutation {X : Type*} {d : ℕ}
    (x y : chapter13OrderedTuple X d) : Prop :=
  ∃ σ : Equiv.Perm (Fin d), y = x ∘ σ

def chapter13TuplePermutationSetoid (X : Type*) (d : ℕ) : Setoid (chapter13OrderedTuple X d) where
  r := chapter13TuplePermutation
  iseqv := by
    constructor
    · intro x
      exact ⟨Equiv.refl _, by rfl⟩
    · intro x y h
      sorry
    · intro x y z hxy hyz
      sorry

/-- The type-level symmetric power of a set of ordered tuples. -/
def chapter13SymmetricPower (X : Type*) (d : ℕ) : Type _ :=
  Quotient (chapter13TuplePermutationSetoid X d)

def chapter13SymmetricPowerMk {X : Type*} {d : ℕ}
    (x : chapter13OrderedTuple X d) : chapter13SymmetricPower X d :=
  Quotient.mk _ x

theorem chapter13SymmetricPower_mk_eq_mk_iff {X : Type*} {d : ℕ}
    (x y : chapter13OrderedTuple X d) :
    chapter13SymmetricPowerMk x = chapter13SymmetricPowerMk y ↔
      chapter13TuplePermutation x y := by
  sorry

theorem chapter13SymmetricPower_mk_perm {X : Type*} {d : ℕ}
    (x : chapter13OrderedTuple X d) (σ : Equiv.Perm (Fin d)) :
    chapter13SymmetricPowerMk (x ∘ σ) = chapter13SymmetricPowerMk x := by
  sorry

/-
LOCAL_DEPENDENCY_GUESS: the preceding chapters are expected to provide the
canonical finite-flat degree/length invariant.  The explicit `length` field
below is a neutral bridge until that invariant is available.
-/
/-- A finite-length subscheme of the base change of a relative scheme. -/
structure Chapter13FiniteLengthSubscheme {S : Scheme}
    (X T : Chapter13RelativeScheme S) (d : ℕ) where
  scheme : Scheme
  toTest : scheme ⟶ T.scheme
  inclusion : scheme ⟶ chapter13BaseChange X.toBase T.toBase
  inclusion_over : inclusion ≫ chapter13BaseChangeToTest X.toBase T.toBase = toTest
  closed : IsClosedImmersion inclusion
  [finite : IsFinite toTest]
  [flat : Flat toTest]
  finitePresentation : LocallyOfFinitePresentation toTest
  length_eq : ∀ t, toTest.finrank t = d

/- A closed immersion is effective Cartier when it is, up to isomorphism of its
   source, the subscheme cut out by an ideal sheaf which is locally generated by
   a non-zero-divisor.  This uses the canonical ideal-sheaf predicate supplied
   by the preceding symmetric-power chapter. -/
def chapter13IsEffectiveCartier {S : Scheme}
    {X T : Chapter13RelativeScheme S} {d : ℕ}
    (F : Chapter13FiniteLengthSubscheme X T d) : Prop :=
  ∃ I : (chapter13BaseChange X.toBase T.toBase).IdealSheafData,
    ∃ e : I.subscheme ≅ F.scheme,
      e.hom ≫ F.inclusion = I.subschemeι ∧ I.IsEffectiveCartier

/-- An effective divisor family with the canonical Cartier condition. -/
structure Chapter13EffectiveDivisorFamily {S : Scheme}
    (X T : Chapter13RelativeScheme S) (d : ℕ) where
  finiteLength : Chapter13FiniteLengthSubscheme X T d
  effectiveCartier : chapter13IsEffectiveCartier finiteLength

/-- Representability data for the relative symmetric power. -/
structure Chapter13RelativeSymmetricPowerData {S : Scheme}
    (X : Chapter13RelativeScheme S) (d : ℕ) where
  functor : Chapter13RelativePresheaf S
  familyPullback : {T U : Chapter13RelativeScheme S} →
    Chapter13RelativeMap T U →
      Chapter13EffectiveDivisorFamily X U d →
        Chapter13EffectiveDivisorFamily X T d
  familyPullback_id : ∀ {T : Chapter13RelativeScheme S}
    (x : Chapter13EffectiveDivisorFamily X T d),
    familyPullback (chapter13RelativeMapId T) x = x
  familyPullback_comp : ∀ {T U V : Chapter13RelativeScheme S}
    (f : Chapter13RelativeMap T U) (g : Chapter13RelativeMap U V)
    (x : Chapter13EffectiveDivisorFamily X V d),
    familyPullback f (familyPullback g x) =
      familyPullback (chapter13RelativeMapComp f g) x
  classifies : ∀ T : Chapter13RelativeScheme S,
    functor.obj T ≃ Chapter13EffectiveDivisorFamily X T d
  classifies_naturality : ∀ {T U : Chapter13RelativeScheme S}
    (f : Chapter13RelativeMap T U) (x : functor.obj U),
    classifies T (functor.map f x) =
      familyPullback f (classifies U x)
  represented : Chapter13RepresentedRelativePresheaf functor

def chapter13RelativeSymmetricPower {S : Scheme}
    {X : Chapter13RelativeScheme S} {d : ℕ}
    (D : Chapter13RelativeSymmetricPowerData X d) :
    Chapter13RelativeScheme S :=
  D.represented.representative

/-- The universal effective divisor obtained by evaluating the represented functor at its
representative and the identity map. -/
def chapter13UniversalRelativeSymmetricPowerDivisor {S : Scheme}
    {X : Chapter13RelativeScheme S} {d : ℕ}
    (D : Chapter13RelativeSymmetricPowerData X d) :
    Chapter13EffectiveDivisorFamily X (chapter13RelativeSymmetricPower D) d :=
  D.classifies _ ((D.represented.equiv _).symm (chapter13RelativeMapId _))

/-- A polarization-aware Hilbert problem; the polarization is part of the input. -/
structure Chapter13PolarizedHilbertProblem {X S : Scheme} (f : X ⟶ S) where
  polarization : Chapter13Polarization f
  polynomial : Chapter13NumericalPolynomial

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter13
