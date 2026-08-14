import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.RelativeGluing
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.GradedAlgebra.FiniteType
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.GradedAlgebra.TensorProduct
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Book 8, Chapter 1: Projective geometry over a base

This file records the book-facing interfaces for relative Proj.  The ordinary
graded-ring statements are thin wrappers around Mathlib.  Relative constructions
are expressed with quasi-coherent module objects, canonical ideal sheaves, and
the gluing data used by the scheme colimit interface.
-/

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter01

universe u
universe uA uM

open AlgebraicGeometry CategoryTheory Limits
open scoped AlgebraicGeometry BigOperators DirectSum TensorProduct

noncomputable section

/-! ### 1.1 Why relative projective geometry -/

/-- A line bundle, in the sense used in the chapter, is an invertible sheaf of modules.

The singleton local-generator formulation is the rank-one interface needed by the
book.  It is deliberately phrased in terms of Mathlib's `LocalGeneratorsData`.
-/
def Chapter01IsLineBundle {X : Scheme.{u}} (M : X.Modules) : Prop :=
  ∃ q : M.LocalGeneratorsData.{u},
    q.IsLocallyFreeData ∧ ∀ i, ∃ e : (q.generators i).I, ∀ j, j = e

structure Chapter01LineBundle (X : Scheme.{u}) where
  module : X.Modules
  isLineBundle : Chapter01IsLineBundle module

/-- Tensor products of module sheaves are formed by the canonical presheaf tensor
product followed by sheafification.  Keeping this operation here makes all later
line-bundle and twisting-sheaf interfaces use the same object. -/
noncomputable def chapter01SheafTensor {X : Scheme.{u}}
    (M N : X.Modules) : X.Modules := by
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (PresheafOfModules.Monoidal.tensorObj M.val N.val)

/-! The sheafification retains the symmetric monoidal comparison and the
canonical map from a pair of presheaf sections.  These two operations are
used below to state commutativity and to compare affine multiplication with
the sheaf multiplication. -/
noncomputable def chapter01SheafTensorSymmetry {X : Scheme.{u}}
    (M N : X.Modules) :
    chapter01SheafTensor M N ≅ chapter01SheafTensor N M := by
  sorry

noncomputable def chapter01SheafTensorSection {X : Scheme.{u}}
    {M N : X.Modules} (U : X.Opens)
    (x : ((Scheme.Modules.presheaf M).obj (Opposite.op U)).carrier)
    (y : ((Scheme.Modules.presheaf N).obj (Opposite.op U)).carrier) :
    ((Scheme.Modules.presheaf (chapter01SheafTensor M N)).obj
      (Opposite.op U)).carrier := by
  sorry

noncomputable def chapter01SheafTensorMap {X : Scheme.{u}}
    {M M' N N' : X.Modules} (f : M ⟶ M') (g : N ⟶ N') :
    chapter01SheafTensor M N ⟶ chapter01SheafTensor M' N' := by
  sorry

noncomputable def chapter01SheafTensorAssociator {X : Scheme.{u}}
    (M N P : X.Modules) :
    chapter01SheafTensor (chapter01SheafTensor M N) P ≅
      chapter01SheafTensor M (chapter01SheafTensor N P) := by
  sorry

noncomputable def chapter01SheafTensorLeftUnitor {X : Scheme.{u}} (M : X.Modules) :
    chapter01SheafTensor (SheafOfModules.unit X.ringCatSheaf) M ≅ M := by
  sorry

noncomputable def chapter01SheafTensorRightUnitor {X : Scheme.{u}} (M : X.Modules) :
    chapter01SheafTensor M (SheafOfModules.unit X.ringCatSheaf) ≅ M := by
  sorry

noncomputable def chapter01LineBundleTensorPower {X : Scheme.{u}}
    (L : Chapter01LineBundle X) (n : ℕ) : Chapter01LineBundle X := by
  induction n with
  | zero =>
      exact
        { module := SheafOfModules.unit X.ringCatSheaf
          isLineBundle := by sorry }
  | succ n ih =>
      exact
        { module := chapter01SheafTensor ih.module L.module
          isLineBundle := by sorry }

/-! Negative powers use a dual line bundle, not an unrelated arbitrary line
bundle.  The data record keeps the duality and power comparison explicit while
the underlying bundle remains available through the book-facing definition. -/
structure Chapter01LineBundleDualPowerData {X : Scheme.{u}}
    (L : Chapter01LineBundle X) (n : ℕ) where
  bundle : Chapter01LineBundle X
  dual : Chapter01LineBundle X
  duality : chapter01SheafTensor dual.module L.module ≅
    SheafOfModules.unit X.ringCatSheaf
  power : bundle.module ≅
    (chapter01LineBundleTensorPower dual n).module

noncomputable def chapter01LineBundleDualPowerData {X : Scheme.{u}}
    (L : Chapter01LineBundle X) (n : ℕ) :
    Chapter01LineBundleDualPowerData L n := by
  sorry

noncomputable def chapter01LineBundleDualPower {X : Scheme.{u}}
    (L : Chapter01LineBundle X) (n : ℕ) : Chapter01LineBundle X := by
  exact (chapter01LineBundleDualPowerData L n).bundle

noncomputable def chapter01PullbackLineBundle {X Y : Scheme.{u}}
    (f : Y ⟶ X) (L : Chapter01LineBundle X) : Chapter01LineBundle Y :=
  { module := (Scheme.Modules.pullback f).obj L.module
    isLineBundle := by sorry }

noncomputable def chapter01LineBundleIntegerPower {X : Scheme.{u}}
    (L : Chapter01LineBundle X) (n : ℤ) : Chapter01LineBundle X := by
  by_cases h : 0 ≤ n
  · exact chapter01LineBundleTensorPower L n.toNat
  · exact chapter01LineBundleDualPower L (-n).toNat

/-- The base change `X_T = X ×_S T` used throughout the chapter. -/
abbrev Chapter01BaseChange {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) : Scheme.{u} :=
  Limits.pullback f g

/-! ### 1.2 Graded algebras and homogeneous localization -/

/-- An internally graded commutative ring indexed by the nonnegative integers. -/
abbrev Chapter01NonnegativeGradedRing (A : Type*) [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) := GradedAlgebra 𝒜

theorem chapter01_mul_mem_graded {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    {m n : ℕ} {x y : A} (hx : x ∈ 𝒜 m) (hy : y ∈ 𝒜 n) :
    x * y ∈ 𝒜 (m + n) := by
  exact SetLike.mul_mem_graded hx hy

theorem chapter01_mul_mem_graded_of {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) (G : GradedAlgebra 𝒜)
    {m n : ℕ} {x y : A} (hx : x ∈ 𝒜 m) (hy : y ∈ 𝒜 n) :
    x * y ∈ 𝒜 (m + n) := by
  sorry

abbrev Chapter01HomogeneousPrime
    {A : Type*} [CommRing A] (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] :=
  ProjectiveSpectrum 𝒜

abbrev Chapter01OrdinaryProj
    {A : Type*} [CommRing A] (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] : Scheme :=
  AlgebraicGeometry.«Proj» 𝒜

def chapter01IrrelevantIdeal {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] : Ideal A :=
  (HomogeneousIdeal.irrelevant 𝒜).toIdeal

theorem chapter01_mem_irrelevant_iff {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] (a : A) :
    a ∈ chapter01IrrelevantIdeal 𝒜 ↔ GradedRing.proj 𝒜 0 a = 0 := by
  exact HomogeneousIdeal.mem_irrelevant_iff 𝒜 a

theorem chapter01_irrelevant_eq_positive_degree_span {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] :
    chapter01IrrelevantIdeal 𝒜 =
      Ideal.span (⋃ n : ℕ, ⋃ _ : 0 < n, (𝒜 n : Set A)) := by
  sorry

def chapter01FractionDegree (n d r : ℕ) : ℤ :=
  (n : ℤ) - (r * d : ℕ)

def chapter01StandardOpen {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] (f : A) :
    TopologicalSpace.Opens (ProjectiveSpectrum 𝒜) :=
  ProjectiveSpectrum.basicOpen 𝒜 f

def chapter01SchemeStandardOpen {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] (f : A) :
    (AlgebraicGeometry.«Proj» 𝒜).Opens :=
  AlgebraicGeometry.Proj.basicOpen 𝒜 f

abbrev chapter01StandardChartRing {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] (f : A) :=
  HomogeneousLocalization.Away 𝒜 f

theorem chapter01_mem_standardOpen {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    (f : A) (x : ProjectiveSpectrum 𝒜) :
  x ∈ chapter01StandardOpen 𝒜 f ↔ f ∉ x.asHomogeneousIdeal :=
  Iff.rfl

theorem chapter01_proj_point_is_relevant {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    (x : Chapter01HomogeneousPrime 𝒜) :
    ¬ HomogeneousIdeal.irrelevant 𝒜 ≤ x.asHomogeneousIdeal :=
  x.not_irrelevant_le

theorem chapter01_proj_point_is_prime {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    (x : Chapter01HomogeneousPrime 𝒜) :
    Ideal.IsPrime x.asHomogeneousIdeal.toIdeal :=
  x.isPrime

theorem chapter01_standard_open_inter {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] (f g : A) :
    chapter01StandardOpen 𝒜 (f * g) =
      chapter01StandardOpen 𝒜 f ⊓ chapter01StandardOpen 𝒜 g := by
  exact ProjectiveSpectrum.basicOpen_mul 𝒜 f g

theorem chapter01_scheme_standard_open_inter {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] (f g : A) :
    chapter01SchemeStandardOpen 𝒜 (f * g) =
      chapter01SchemeStandardOpen 𝒜 f ⊓ chapter01SchemeStandardOpen 𝒜 g := by
  exact AlgebraicGeometry.Proj.basicOpen_mul 𝒜 f g

theorem chapter01_standard_opens_cover {A ι : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] (f : ι → A)
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ Ideal.span (Set.range f)) :
    ⨆ i, chapter01SchemeStandardOpen 𝒜 (f i) = ⊤ := by
  exact AlgebraicGeometry.Proj.iSup_basicOpen_eq_top 𝒜 f hf

theorem chapter01_standard_opens_cover_of_adjoin {A ι : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] (f : ι → A)
    (hfn : ∀ i, ∃ n, 0 < n ∧ f i ∈ 𝒜 n)
    (hf : Algebra.adjoin (𝒜 0) (Set.range f) = ⊤) :
    ⨆ i, chapter01SchemeStandardOpen 𝒜 (f i) = ⊤ := by
  sorry

noncomputable def chapter01StandardChartIso {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    {d : ℕ} {f : A} (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    (chapter01SchemeStandardOpen 𝒜 f).toScheme ≅
      AlgebraicGeometry.Spec (.of (chapter01StandardChartRing 𝒜 f)) :=
  AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 f hf hd

noncomputable def chapter01_standard_chart_restriction_map {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    {m n : ℕ} {f g : A} (_hf : f ∈ 𝒜 m) (_hm : 0 < m)
    (hg : g ∈ 𝒜 n) (_hn : 0 < n) :
    chapter01StandardChartRing 𝒜 f →+*
      chapter01StandardChartRing 𝒜 (f * g) := by
  exact HomogeneousLocalization.awayMap 𝒜 hg rfl

theorem chapter01_proj_empty_of_irrelevant_eq_bot {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    (h : chapter01IrrelevantIdeal 𝒜 = ⊥) :
    IsEmpty (ProjectiveSpectrum 𝒜) := by
  sorry

/- The polynomial chart is the ratio chart in the source text. -/
abbrev Chapter01PolynomialChartCoordinateRing (k : Type*) [CommRing k]
    (r : ℕ) (i : Fin (r + 1)) :=
  MvPolynomial {j : Fin (r + 1) // j ≠ i} k

/- LOCAL_DEPENDENCY_GUESS: the pinned polynomial grading API does not expose
the weighted grading in the book's componentwise form. -/
structure Chapter01PolynomialGradingData
    (k : Type*) [CommRing k] (r : ℕ) (w : Fin (r + 1) → ℕ) where
  grading : ℕ → Submodule ℤ (MvPolynomial (Fin (r + 1)) k)
  graded : GradedAlgebra grading
  homogeneous_iff :
    ∀ n p, p ∈ grading n ↔
      p = 0 ∨ ∀ m ∈ p.support, (∑ i, w i * m i) = n
  variable_degree : ∀ i, MvPolynomial.X i ∈ grading (w i)
  positive_weight : ∀ i, 0 < w i

noncomputable def chapter01PolynomialProj
    {k : Type*} [CommRing k] {r : ℕ} {w : Fin (r + 1) → ℕ}
    (G : Chapter01PolynomialGradingData k r w) : Scheme := by
  letI := G.graded
  exact AlgebraicGeometry.«Proj» G.grading

/-! The degree-zero projection is the canonical structure morphism of an
ordinary Proj.  The extra ring hom records a chosen base algebra, which is
needed when the degree-zero part is only canonically isomorphic to that base
ring (as for a polynomial presentation). -/
noncomputable def chapter01ProjToBase
    {R A : Type u} [CommRing R] [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    (baseMap : R →+* A) :
    AlgebraicGeometry.«Proj» 𝒜 ⟶ AlgebraicGeometry.Spec (CommRingCat.of R) := by
  exact AlgebraicGeometry.Proj.toSpecZero 𝒜 ≫
    AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom
        ((GradedRing.projZeroRingHom' 𝒜).comp baseMap))

noncomputable def chapter01ProjToDegreeZero
    {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] :
    AlgebraicGeometry.«Proj» 𝒜 ⟶
      AlgebraicGeometry.Spec (CommRingCat.of (𝒜 0)) :=
  AlgebraicGeometry.Proj.toSpecZero 𝒜

noncomputable def chapter01PolynomialChartRing
    {k : Type*} [CommRing k] {r : ℕ} {w : Fin (r + 1) → ℕ}
    (G : Chapter01PolynomialGradingData k r w) (i : Fin (r + 1)) : CommRingCat := by
  letI := G.graded
  exact CommRingCat.of (HomogeneousLocalization.Away G.grading (MvPolynomial.X i))

theorem chapter01_polynomial_chart_coordinates
    {k : Type*} [CommRing k] {r : ℕ}
    (G : Chapter01PolynomialGradingData k r (fun _ => 1)) (i : Fin (r + 1)) :
    Nonempty (chapter01PolynomialChartRing G i ≅
      CommRingCat.of (Chapter01PolynomialChartCoordinateRing k r i)) := by
  sorry

theorem chapter01_weight_two_one_variable_proj
    {k : Type*} [Field k]
    (G : Chapter01PolynomialGradingData k 0 (fun _ => 2)) :
    Nonempty (chapter01PolynomialProj G ≅ AlgebraicGeometry.Spec (.of k)) := by
  sorry

theorem chapter01_weight_two_one_variable_proj_example
    {k : Type*} [Field k] :
    ∃ G : Chapter01PolynomialGradingData k 0 (fun _ => 2),
      Nonempty (chapter01PolynomialProj G ≅ AlgebraicGeometry.Spec (.of k)) := by
  sorry

/-! ### 1.3 The construction of relative Proj -/

/-! The affine section model is retained as the local chart presentation of a
quasi-coherent graded algebra.  The public algebra object below is sheaf-valued;
the model supplies the compatible affine charts used by the relative Proj API. -/
structure Chapter01RelativeAffineGradedModel (S : Scheme.{u}) where
  sections : ∀ _U : S.Opens, CommRingCat.{u}
  grading : ∀ U : S.Opens, ℕ → Submodule ℤ (sections U).carrier
  graded : ∀ U : S.Opens, GradedAlgebra (grading U)
  restriction : ∀ {U V : S.Opens}, (U ⟶ V) →
    (sections V).carrier →+* (sections U).carrier
  restriction_id : ∀ U, restriction (U := U) (V := U) (𝟙 U) = RingHom.id _
  restriction_comp :
    ∀ {U V W : S.Opens} (i : U ⟶ V) (j : V ⟶ W),
      (restriction (U := U) (V := V) i).comp (restriction (U := V) (V := W) j) =
        restriction (U := U) (V := W) (i ≫ j)
  restriction_preserves :
    ∀ {U V : S.Opens} (i : U ⟶ V) (n : ℕ) (x : (sections V).carrier),
      x ∈ grading V n → restriction (U := U) (V := V) i x ∈ grading U n
  degree_zero_map : ∀ U,
    (S.presheaf.obj (Opposite.op U)).carrier →+* (sections U).carrier
  degree_zero_map_mem : ∀ U (x : (S.presheaf.obj (Opposite.op U)).carrier),
    degree_zero_map U x ∈ grading U 0
  degree_zero_map_restriction :
    ∀ {U V : S.Opens} (i : U ⟶ V),
      (restriction (U := U) (V := V) i).comp (degree_zero_map V) =
        (degree_zero_map U).comp (S.presheaf.map i.op).hom

structure Chapter01RelativeGradedAlgebra (S : Scheme.{u}) where
  component : ℕ → S.Modules
  component_isQuasicoherent : ∀ n, (component n).IsQuasicoherent
  affineModel : Chapter01RelativeAffineGradedModel S
  component_sections : ∀ (n : ℕ) (U : S.Opens),
    AddCommGrpCat.of (affineModel.grading U n) ≅
      (Scheme.Modules.presheaf (component n)).obj (Opposite.op U)
  /-- The degreewise section identifications respect restriction maps. -/
  component_sections_restriction :
    ∀ {U V : S.Opens} (i : U ⟶ V) (n : ℕ) (x : affineModel.grading V n),
      (component_sections n U).hom
          ⟨affineModel.restriction i x,
            affineModel.restriction_preserves i n x x.property⟩ =
        (Scheme.Modules.presheaf (component n)).map i.op
          ((component_sections n V).hom x)
  /-- The affine component identifications respect the degree-zero
  structure-sheaf action.  Additive naturality alone would not identify
  the graded pieces as quasi-coherent modules. -/
  component_sections_degree_zero_smul :
    ∀ (n : ℕ) (U : S.Opens)
      (r : (S.presheaf.obj (Opposite.op U)).carrier)
      (x : affineModel.grading U n),
      ∃ y : affineModel.grading U n,
        y.1 = affineModel.degree_zero_map U r * x.1 ∧
          (component_sections n U).hom y =
            r • (component_sections n U).hom x
  /-- The degree-zero structure map transported to the degree-zero component. -/
  component_unit : ∀ U : S.Opens,
    (S.presheaf.obj (Opposite.op U)).carrier →
      ((Scheme.Modules.presheaf (component 0)).obj (Opposite.op U)).carrier
  component_unit_compatibility :
    ∀ (U : S.Opens) (x : (S.presheaf.obj (Opposite.op U)).carrier),
      component_unit U x =
        (component_sections 0 U).hom
          ⟨affineModel.degree_zero_map U x,
            affineModel.degree_zero_map_mem U x⟩
  /-- Multiplication on the degreewise sheaf sections. -/
  component_multiplication : ∀ (U : S.Opens) (m n : ℕ),
    ((Scheme.Modules.presheaf (component m)).obj (Opposite.op U)).carrier →
      ((Scheme.Modules.presheaf (component n)).obj (Opposite.op U)).carrier →
        ((Scheme.Modules.presheaf (component (m + n))).obj (Opposite.op U)).carrier
  component_multiplication_compatibility :
    ∀ (U : S.Opens) (m n : ℕ) (x : affineModel.grading U m)
      (y : affineModel.grading U n),
      (component_sections (m + n) U).hom
          ⟨x * y, chapter01_mul_mem_graded_of (affineModel.grading U)
            (affineModel.graded U) x.property y.property⟩ =
        component_multiplication U m n
          ((component_sections m U).hom x) ((component_sections n U).hom y)
  component_multiplication_restriction :
    ∀ {U V : S.Opens} (i : U ⟶ V) (m n : ℕ)
      (x : ((Scheme.Modules.presheaf (component m)).obj (Opposite.op V)).carrier)
      (y : ((Scheme.Modules.presheaf (component n)).obj (Opposite.op V)).carrier),
      component_multiplication U m n
          ((Scheme.Modules.presheaf (component m)).map i.op x)
          ((Scheme.Modules.presheaf (component n)).map i.op y) =
        (Scheme.Modules.presheaf (component (m + n))).map i.op
          (component_multiplication V m n x y)
  /-- The degree-zero unit as a morphism of sheaves of modules. -/
  sheaf_unit : SheafOfModules.unit S.ringCatSheaf ⟶ component 0
  /-- Multiplication as a morphism of sheaves of modules. -/
  sheaf_multiplication : ∀ m n,
    chapter01SheafTensor (component m) (component n) ⟶ component (m + n)
  /-- The sheaf multiplication evaluates to the affine graded multiplication
  on the canonical tensor sections. -/
  sheaf_multiplication_sections :
    ∀ (U : S.Opens) (m n : ℕ) (x : affineModel.grading U m)
      (y : affineModel.grading U n),
      (Scheme.Modules.Hom.app (sheaf_multiplication m n) U)
          (chapter01SheafTensorSection U
            ((component_sections m U).hom x)
            ((component_sections n U).hom y)) =
        component_multiplication U m n
          ((component_sections m U).hom x) ((component_sections n U).hom y)
  /-- Commutativity of the affine graded multiplication.  `HEq` records the
  canonical transport between the components of degrees `m + n` and `n + m`.
  -/
  component_multiplication_comm :
    ∀ (U : S.Opens) (m n : ℕ)
      (x : ((Scheme.Modules.presheaf (component m)).obj (Opposite.op U)).carrier)
      (y : ((Scheme.Modules.presheaf (component n)).obj (Opposite.op U)).carrier),
      HEq (component_multiplication U m n x y)
        (component_multiplication U n m y x)
  /-- The sheaf multiplication is commutative with respect to the canonical
  symmetry of the sheaf tensor product. -/
  sheaf_multiplication_comm : ∀ m n,
    (chapter01SheafTensorSymmetry (component m) (component n)).hom ≫
        sheaf_multiplication n m ≫
        eqToHom (by simp [Nat.add_comm] : component (n + m) = component (m + n)) =
      sheaf_multiplication m n
  sheaf_unit_sections :
    ∀ (U : S.Opens) (x : (S.presheaf.obj (Opposite.op U)).carrier),
      (Scheme.Modules.Hom.app sheaf_unit U) x = component_unit U x
  sheaf_unit_left : ∀ n,
    chapter01SheafTensorMap sheaf_unit (𝟙 (component n)) ≫
        sheaf_multiplication 0 n ≫
        eqToHom (by sorry : component (0 + n) = component n) =
      (chapter01SheafTensorLeftUnitor (component n)).hom
  sheaf_unit_right : ∀ n,
    chapter01SheafTensorMap (𝟙 (component n)) sheaf_unit ≫
        sheaf_multiplication n 0 ≫
        eqToHom (by sorry : component (n + 0) = component n) =
      (chapter01SheafTensorRightUnitor (component n)).hom
  sheaf_multiplication_assoc : ∀ m n k,
    chapter01SheafTensorMap (sheaf_multiplication m n) (𝟙 (component k)) ≫
        sheaf_multiplication (m + n) k ≫
        eqToHom (by sorry : component ((m + n) + k) = component (m + (n + k))) =
      (chapter01SheafTensorAssociator (component m) (component n) (component k)).hom ≫
        chapter01SheafTensorMap (𝟙 (component m)) (sheaf_multiplication n k) ≫
        sheaf_multiplication m (n + k)

abbrev Chapter01RelativeGradedAlgebra.sections {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) :=
  𝒜.affineModel.sections

abbrev Chapter01RelativeGradedAlgebra.grading {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) :=
  𝒜.affineModel.grading

abbrev Chapter01RelativeGradedAlgebra.graded {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) :=
  𝒜.affineModel.graded

abbrev Chapter01RelativeGradedAlgebra.restriction {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) {U V : S.Opens} (i : U ⟶ V) :=
  𝒜.affineModel.restriction i

abbrev Chapter01RelativeGradedAlgebra.restriction_id {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) :=
  𝒜.affineModel.restriction_id

abbrev Chapter01RelativeGradedAlgebra.restriction_comp {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) {U V W : S.Opens}
    (i : U ⟶ V) (j : V ⟶ W) :=
  𝒜.affineModel.restriction_comp i j

abbrev Chapter01RelativeGradedAlgebra.restriction_preserves {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) {U V : S.Opens}
    (i : U ⟶ V) (n : ℕ) (x : (𝒜.sections V).carrier) :=
  𝒜.affineModel.restriction_preserves i n x

abbrev Chapter01RelativeGradedAlgebra.degree_zero_map {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) :=
  𝒜.affineModel.degree_zero_map

abbrev Chapter01RelativeGradedAlgebra.degree_zero_map_mem {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) :=
  𝒜.affineModel.degree_zero_map_mem

abbrev Chapter01RelativeGradedAlgebra.degree_zero_map_restriction {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) {U V : S.Opens} (i : U ⟶ V) :=
  𝒜.affineModel.degree_zero_map_restriction i

/-! The degree-zero structure map is part of every relative graded algebra.
Equality with the structure sheaf is an additional hypothesis: quotients by
homogeneous ideals may acquire a nontrivial degree-zero kernel. -/
def Chapter01RelativeDegreeZeroIsStructureSheaf {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) : Prop :=
  ∀ U, Function.Bijective
    (fun x : (S.presheaf.obj (Opposite.op U)).carrier =>
      (⟨𝒜.degree_zero_map U x, 𝒜.degree_zero_map_mem U x⟩ : 𝒜.grading U 0))

abbrev Chapter01RelativeGradedAlgebra.degree_zero_is_structure_sheaf
    {S : Scheme.{u}} (𝒜 : Chapter01RelativeGradedAlgebra S) :=
  Chapter01RelativeDegreeZeroIsStructureSheaf 𝒜

instance chapter01RelativeGradedAlgebraGraded
    {S : Scheme.{u}} (𝒜 : Chapter01RelativeGradedAlgebra S) (U : S.Opens) :
    GradedAlgebra (𝒜.grading U) :=
  𝒜.graded U

abbrev chapter01RelativeSection {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) (U : S.Opens) :=
  𝒜.sections U

theorem chapter01_relative_multiplication_preserves_degree {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S)
    {U : S.Opens} {m n : ℕ} {x y : 𝒜.sections U}
    (hx : x ∈ 𝒜.grading U m) (hy : y ∈ 𝒜.grading U n) :
    x * y ∈ 𝒜.grading U (m + n) := by
  sorry

noncomputable def chapter01RelativeDegreeZeroLocalization {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) (U : S.Opens)
    {d : ℕ} (f : 𝒜.sections U) (_hf : f ∈ 𝒜.grading U d) (_hd : 0 < d) : CommRingCat.{u} := by
  exact CommRingCat.of (HomogeneousLocalization.Away (𝒜.grading U) f)

noncomputable def chapter01RelativeDegreeZeroRestrictionMap {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S)
    {U V : S.Opens} (i : U ⟶ V) {d : ℕ} (f : 𝒜.sections V)
    (hf : f ∈ 𝒜.grading V d) (hd : 0 < d) :
    (chapter01RelativeDegreeZeroLocalization 𝒜 V f hf hd).carrier →+*
      (chapter01RelativeDegreeZeroLocalization 𝒜 U (𝒜.restriction i f)
        (𝒜.restriction_preserves i d f hf) hd).carrier := by
  sorry

/-! Relative Proj is glued from its affine charts using Mathlib's canonical
`Scheme.Cover.RelativeGluingData`.  The chart fields in
`Chapter01RelativeProj` are the book-facing comparison API for that glued
scheme. -/
structure Chapter01RelativeGluingInterface (S : Scheme.{u}) where
  cover : S.OpenCover
  category : Category cover.I₀
  locallyDirected : letI := category; cover.LocallyDirected
  small : Small.{u} cover.I₀
  thin : Quiver.IsThin cover.I₀
  data :
    letI := category
    letI := locallyDirected
    Scheme.Cover.RelativeGluingData cover

namespace Chapter01RelativeGluingInterface

noncomputable def glued {S : Scheme.{u}}
    (G : Chapter01RelativeGluingInterface S) : Scheme.{u} := by
  letI := G.category
  letI := G.locallyDirected
  letI := G.small
  letI := G.thin
  exact G.data.glued

noncomputable def toBase {S : Scheme.{u}}
    (G : Chapter01RelativeGluingInterface S) : G.glued ⟶ S := by
  letI := G.category
  letI := G.locallyDirected
  letI := G.small
  letI := G.thin
  exact G.data.toBase

noncomputable def gluedCover {S : Scheme.{u}}
    (G : Chapter01RelativeGluingInterface S) : G.glued.OpenCover := by
  letI := G.category
  letI := G.locallyDirected
  letI := G.small
  letI := G.thin
  exact G.data.cover

end Chapter01RelativeGluingInterface

structure Chapter01RelativeProj {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) where
  gluing : Chapter01RelativeGluingInterface S
  standardOpen : ∀ (U : S.Opens) (_hU : IsAffineOpen U) (d : ℕ) (f : 𝒜.sections U),
    f ∈ 𝒜.grading U d → 0 < d → gluing.glued.Opens
  standardOpen_over :
    ∀ (U : S.Opens) (hU : IsAffineOpen U) (d : ℕ) (f : 𝒜.sections U)
      (hf : f ∈ 𝒜.grading U d) (hd : 0 < d),
      standardOpen U hU d f hf hd ≤ gluing.toBase ⁻¹ᵁ U
  standardOpen_cover :
    (⨆ (U : S.Opens) (hU : IsAffineOpen U) (d : ℕ) (f : 𝒜.sections U)
        (hf : f ∈ 𝒜.grading U d) (hd : 0 < d),
      standardOpen U hU d f hf hd) = ⊤
  standardOpen_mul :
    ∀ (U : S.Opens) (hU : IsAffineOpen U) (m n : ℕ) (f g : 𝒜.sections U)
      (hf : f ∈ 𝒜.grading U m) (hm : 0 < m)
      (hg : g ∈ 𝒜.grading U n) (hn : 0 < n)
      (hfg : f * g ∈ 𝒜.grading U (m + n)),
      standardOpen U hU (m + n) (f * g) hfg (Nat.add_pos_right m hn) =
        standardOpen U hU m f hf hm ⊓ standardOpen U hU n g hg hn
  standardOpen_chart :
    ∀ (U : S.Opens) (hU : IsAffineOpen U) (d : ℕ) (f : 𝒜.sections U)
      (hf : f ∈ 𝒜.grading U d) (hd : 0 < d),
      (standardOpen U hU d f hf hd).toScheme ≅
        AlgebraicGeometry.Spec
          (chapter01RelativeDegreeZeroLocalization 𝒜 U f hf hd)
  /-- The chart comparison is over the base, not merely an isomorphism of schemes. -/
  standardOpen_chart_projection :
    ∀ (U : S.Opens) (_hU : IsAffineOpen U) (d : ℕ) (f : 𝒜.sections U)
      (hf : f ∈ 𝒜.grading U d) (hd : 0 < d),
      AlgebraicGeometry.Spec
          (chapter01RelativeDegreeZeroLocalization 𝒜 U f hf hd) ⟶ S
  standardOpen_chart_over :
    ∀ (U : S.Opens) (hU : IsAffineOpen U) (d : ℕ) (f : 𝒜.sections U)
      (hf : f ∈ 𝒜.grading U d) (hd : 0 < d),
      (standardOpen_chart U hU d f hf hd).hom ≫
          standardOpen_chart_projection U hU d f hf hd =
        (standardOpen U hU d f hf hd).ι ≫ gluing.toBase
  /-- Restriction of a homogeneous chart along an inclusion of affine opens. -/
  standardOpen_restriction :
    ∀ {U V : S.Opens} (i : U ⟶ V) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
      {d : ℕ} (f : 𝒜.sections V) (hf : f ∈ 𝒜.grading V d) (hd : 0 < d),
      standardOpen U hU d (𝒜.restriction i f)
          (𝒜.restriction_preserves i d f hf) hd ≤
        standardOpen V hV d f hf hd ∧
      ∃ e :
          (standardOpen U hU d (𝒜.restriction i f)
            (𝒜.restriction_preserves i d f hf) hd).toScheme ⟶
          (standardOpen V hV d f hf hd).toScheme,
        e =
          (standardOpen_chart U hU d (𝒜.restriction i f)
              (𝒜.restriction_preserves i d f hf) hd).hom ≫
            AlgebraicGeometry.Spec.map
              (CommRingCat.ofHom
                (chapter01RelativeDegreeZeroRestrictionMap 𝒜 i f hf hd)) ≫
            (standardOpen_chart V hV d f hf hd).inv ∧
        e ≫ (standardOpen V hV d f hf hd).ι =
          (standardOpen U hU d (𝒜.restriction i f)
            (𝒜.restriction_preserves i d f hf) hd).ι
  /-- The standard affine charts are exactly the components of the gluing cover. -/
  standardOpen_gluing :
    ∀ (U : S.Opens) (hU : IsAffineOpen U) (d : ℕ) (f : 𝒜.sections U)
      (hf : f ∈ 𝒜.grading U d) (hd : 0 < d),
      ∃ i : gluing.gluedCover.I₀,
        standardOpen U hU d f hf hd = (gluing.gluedCover.f i).opensRange ∧
        ∃ e : gluing.gluedCover.X i ≅
            (standardOpen U hU d f hf hd).toScheme,
          e.hom ≫ (standardOpen U hU d f hf hd).ι = gluing.gluedCover.f i
  gluing_standardOpen :
    ∀ i : gluing.gluedCover.I₀,
      ∃ (U : S.Opens) (hU : IsAffineOpen U) (d : ℕ) (f : 𝒜.sections U)
        (hf : f ∈ 𝒜.grading U d) (hd : 0 < d),
        (gluing.gluedCover.f i).opensRange = standardOpen U hU d f hf hd ∧
          ∃ e : gluing.gluedCover.X i ≅
              (standardOpen U hU d f hf hd).toScheme,
            e.hom ≫ (standardOpen U hU d f hf hd).ι = gluing.gluedCover.f i

abbrev Chapter01RelativeProj.scheme {S : Scheme.{u}}
    {𝒜 : Chapter01RelativeGradedAlgebra S} (P : Chapter01RelativeProj 𝒜) :=
  P.gluing.glued

abbrev Chapter01RelativeProj.projection {S : Scheme.{u}}
    {𝒜 : Chapter01RelativeGradedAlgebra S} (P : Chapter01RelativeProj 𝒜) :=
  P.gluing.toBase

noncomputable def chapter01RelativeProj {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) : Chapter01RelativeProj 𝒜 :=
  by
    sorry

/-! The canonical relative gluing construction supplies the chart data above.
The existence theorem is retained as a compatibility wrapper, but no later
definition chooses a separate witness. -/
theorem chapter01_relative_proj_exists {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) :
    Nonempty (Chapter01RelativeProj 𝒜) := by
  sorry

theorem chapter01_relative_standard_open_inter {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) (P : Chapter01RelativeProj 𝒜)
    {U : S.Opens} (hU : IsAffineOpen U) {m n : ℕ} {f g : 𝒜.sections U}
    (hf : f ∈ 𝒜.grading U m) (hm : 0 < m)
    (hg : g ∈ 𝒜.grading U n) (hn : 0 < n)
    (hfg : f * g ∈ 𝒜.grading U (m + n)) :
    P.standardOpen U hU (m + n) (f * g) hfg (Nat.add_pos_right m hn) =
      P.standardOpen U hU m f hf hm ⊓ P.standardOpen U hU n g hg hn := by
  exact P.standardOpen_mul U hU m n f g hf hm hg hn hfg

def chapter01RelativeFinitePositiveGeneration {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) : Prop :=
  ∃ r : ℕ, ∃ x : Fin r → 𝒜.sections ⊤,
    (∀ i, ∃ n, 0 < n ∧ x i ∈ 𝒜.grading ⊤ n) ∧
      Algebra.adjoin (𝒜.grading ⊤ 0) (Set.range x) = ⊤ ∧
        ∀ (U : S.Opens) (i : U ⟶ ⊤),
            Algebra.adjoin (𝒜.grading U 0)
            (Set.range (fun j => 𝒜.restriction i (x j))) = ⊤

/-! The source statement is local on the base.  The global predicate above is
useful for a single global generating family; this version records the
sheaf-local finite-generation hypothesis separately. -/
def chapter01RelativeLocallyFinitePositiveGeneration {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) : Prop :=
  ∀ (U : S.Opens), IsAffineOpen U →
    ∃ r : ℕ, ∃ x : Fin r → 𝒜.sections U,
      (∀ i, ∃ n, 0 < n ∧ x i ∈ 𝒜.grading U n) ∧
        Algebra.adjoin (𝒜.grading U 0) (Set.range x) = ⊤

theorem chapter01_relative_proj_locally_of_finite_type {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S)
    (h₀ : Chapter01RelativeDegreeZeroIsStructureSheaf 𝒜)
    (h : chapter01RelativeFinitePositiveGeneration 𝒜) :
    LocallyOfFiniteType (chapter01RelativeProj 𝒜).projection := by
  sorry

theorem chapter01_relative_proj_locally_of_locally_finite_type {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S)
    (h₀ : Chapter01RelativeDegreeZeroIsStructureSheaf 𝒜)
    (h : chapter01RelativeLocallyFinitePositiveGeneration 𝒜) :
    LocallyOfFiniteType (chapter01RelativeProj 𝒜).projection := by
  sorry

def chapter01RelativeGeneratedInDegreeOneByFiniteType {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) : Prop :=
  ∃ r : ℕ, ∃ x : Fin (r + 1) → 𝒜.sections ⊤,
    (∀ i, x i ∈ 𝒜.grading ⊤ 1) ∧
      Algebra.adjoin (𝒜.grading ⊤ 0) (Set.range x) = ⊤ ∧
        ∀ (U : S.Opens) (i : U ⟶ ⊤),
          Algebra.adjoin (𝒜.grading U 0)
            (Set.range (fun j => 𝒜.restriction i (x j))) = ⊤

def chapter01RelativeLocallyGeneratedInDegreeOneByFiniteType {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) : Prop :=
  ∀ (U : S.Opens), IsAffineOpen U →
    ∃ r : ℕ, ∃ x : Fin (r + 1) → 𝒜.sections U,
      (∀ i, x i ∈ 𝒜.grading U 1) ∧
        Algebra.adjoin (𝒜.grading U 0) (Set.range x) = ⊤

/-! An invertible quotient is the object represented by the projective bundle
functor.  Keeping it as a structure makes the universal property below
independent of any choice of local generators. -/
structure Chapter01InvertibleQuotient {S T : Scheme.{u}}
    (E : S.Modules) (g : T ⟶ S) where
  lineBundle : Chapter01LineBundle T
  quotient : (Scheme.Modules.pullback g).obj E ⟶ lineBundle.module
  quotient_is_epi : Epi quotient

def chapter01InvertibleQuotientEquivalent {S T : Scheme.{u}}
    {E : S.Modules} {g : T ⟶ S}
    (p q : Chapter01InvertibleQuotient E g) : Prop :=
  ∃ e : p.lineBundle.module ≅ q.lineBundle.module,
    p.quotient ≫ e.hom = q.quotient

instance {S T : Scheme.{u}} {E : S.Modules} {g : T ⟶ S} :
    Setoid (Chapter01InvertibleQuotient E g) where
  r := chapter01InvertibleQuotientEquivalent
  iseqv := by sorry

abbrev Chapter01InvertibleQuotientClass {S T : Scheme.{u}}
    (E : S.Modules) (g : T ⟶ S) :=
  Quotient (inferInstance : Setoid (Chapter01InvertibleQuotient E g))

def chapter01InvertibleQuotientClassMk {S T : Scheme.{u}}
    {E : S.Modules} {g : T ⟶ S}
    (p : Chapter01InvertibleQuotient E g) :
    Chapter01InvertibleQuotientClass E g :=
  Quotient.mk _ p

structure Chapter01QuasiCoherentModule (S : Scheme.{u}) where
  carrier : S.Modules
  isQuasicoherent : carrier.IsQuasicoherent

def Chapter01FiniteLocallyFree {S : Scheme.{u}} (E : S.Modules) : Prop :=
  E.IsLocallyFree ∧ E.IsFiniteType

def Chapter01LocallyFreeRank {S : Scheme.{u}} (E : S.Modules) (r : ℕ) : Prop :=
  ∃ q : E.LocalGeneratorsData.{u},
    q.IsLocallyFreeData ∧ ∀ i, Nonempty ((q.generators i).I ≃ Fin r)

noncomputable def chapter01PullbackCompositionIso
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    (Scheme.Modules.pullback (f ≫ g)).obj M ≅
      (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) :=
  (Scheme.Modules.pullbackComp f g).symm.app M

noncomputable def chapter01PullbackInvertibleQuotientAlong
    {S T U : Scheme.{u}} (g : T ⟶ S) (h : U ⟶ T) {E : S.Modules}
    (Q : Chapter01InvertibleQuotient E g) :
    Chapter01InvertibleQuotient E (h ≫ g) :=
  { lineBundle := chapter01PullbackLineBundle h Q.lineBundle
    quotient := (chapter01PullbackCompositionIso h g E).hom ≫
      (Scheme.Modules.pullback h).map Q.quotient
    quotient_is_epi := by sorry }

/-! The arbitrary quasi-coherent projective bundle is kept separate from the
finite-rank package below.  Its universal property is stated on equivalence
classes of invertible quotients, and the compatibility field exposes the
pullback of the tautological quotient rather than an unrelated representative. -/
structure Chapter01ProjectiveBundleData
    (S : Scheme.{u}) (E : Chapter01QuasiCoherentModule S) where
  scheme : Scheme.{u}
  projection : scheme ⟶ S
  tautological : Chapter01LineBundle scheme
  universalQuotient :
    (Scheme.Modules.pullback projection).obj E.carrier ⟶ tautological.module
  universalQuotient_is_epi : Epi universalQuotient
  universalProperty : ∀ {T : Scheme.{u}} (g : T ⟶ S),
    {u : T ⟶ scheme // u ≫ projection = g} ≃
      Chapter01InvertibleQuotientClass E.carrier g
  universalProperty_natural :
    ∀ {T U : Scheme.{u}} (g : T ⟶ S) (h : U ⟶ T)
      (u : {u : T ⟶ scheme // u ≫ projection = g}),
      ∃ p : Chapter01InvertibleQuotient E.carrier g,
        universalProperty g u = chapter01InvertibleQuotientClassMk p ∧
          universalProperty (h ≫ g) ⟨h ≫ u.1, by sorry⟩ =
            chapter01InvertibleQuotientClassMk
              (chapter01PullbackInvertibleQuotientAlong g h p)
  /-- The universal line and quotient are the pullbacks of the displayed tautological data. -/
  universalProperty_compatible :
    ∀ {T : Scheme.{u}} (g : T ⟶ S)
      (u : {u : T ⟶ scheme // u ≫ projection = g}),
      ∃ p : Chapter01InvertibleQuotient E.carrier g,
        universalProperty g u = chapter01InvertibleQuotientClassMk p ∧
          ∃ e : p.lineBundle.module ≅
              (Scheme.Modules.pullback u.1).obj tautological.module,
            p.quotient ≫ e.hom =
              (Scheme.Modules.pullbackCongr u.2).inv.app E.carrier ≫
                (Scheme.Modules.pullbackComp u.1 projection).inv.app E.carrier ≫
                (Scheme.Modules.pullback u.1).map universalQuotient

theorem chapter01_projective_bundle_exists
    (S : Scheme.{u}) (E : Chapter01QuasiCoherentModule S) :
    Nonempty (Chapter01ProjectiveBundleData S E) := by
  sorry

noncomputable def chapter01ProjectiveBundleData
    (S : Scheme.{u}) (E : Chapter01QuasiCoherentModule S) :
    Chapter01ProjectiveBundleData S E :=
  Classical.choice (chapter01_projective_bundle_exists S E)

structure Chapter01FiniteProjectiveBundle (S : Scheme.{u}) (r : ℕ) where
  E : S.Modules
  finiteLocallyFree : Chapter01FiniteLocallyFree E
  locallyFreeRank : Chapter01LocallyFreeRank E (r + 1)
  scheme : Scheme.{u}
  projection : scheme ⟶ S
  tautological : scheme.Modules
  tautological_isLineBundle : Chapter01IsLineBundle tautological
  universalQuotient : (Scheme.Modules.pullback projection).obj E ⟶ tautological
  universalQuotient_is_epi : Epi universalQuotient
  projection_isProper : IsProper projection
  universal : ∀ {T : Scheme.{u}} (g : T ⟶ S),
    {u : T ⟶ scheme // u ≫ projection = g} ≃
      Chapter01InvertibleQuotientClass E g
  /-- The representing equivalence is natural under pullback of test schemes. -/
  universal_natural :
    ∀ {T U : Scheme.{u}} (g : T ⟶ S) (h : U ⟶ T)
      (u : {u : T ⟶ scheme // u ≫ projection = g}),
      ∃ p : Chapter01InvertibleQuotient E g,
        universal g u = chapter01InvertibleQuotientClassMk p ∧
          universal (h ≫ g)
              ⟨h ≫ u.1, by sorry⟩ =
            chapter01InvertibleQuotientClassMk
              (chapter01PullbackInvertibleQuotientAlong g h p)
  /-- The finite-rank universal quotient is identified with the pullback of the
  tautological line bundle and quotient. -/
  universal_pullback_compatible :
    ∀ {T : Scheme.{u}} (g : T ⟶ S)
      (u : {u : T ⟶ scheme // u ≫ projection = g}),
      ∃ p : Chapter01InvertibleQuotient E g,
        universal g u = chapter01InvertibleQuotientClassMk p ∧
          ∃ e : p.lineBundle.module ≅
              (Scheme.Modules.pullback u.1).obj tautological,
            p.quotient ≫ e.hom =
              (Scheme.Modules.pullbackCongr u.2).inv.app E ≫
                (Scheme.Modules.pullbackComp u.1 projection).inv.app E ≫
                (Scheme.Modules.pullback u.1).map universalQuotient

/-! The projective-bundle theorem also needs an existence interface.  The
record above packages the representing scheme; this declaration supplies the
finite locally free input from which that record is constructed. -/
theorem chapter01_finite_projective_bundle_exists
    {S : Scheme.{u}} {r : ℕ} (E : S.Modules)
    (hE : Chapter01FiniteLocallyFree E)
    (hr : Chapter01LocallyFreeRank E (r + 1)) :
    ∃ P : Chapter01FiniteProjectiveBundle S r, P.E = E := by
  sorry

abbrev Chapter01RelativeProjectiveSpace (S : Scheme.{u}) (r : ℕ) :=
  Chapter01FiniteProjectiveBundle S r

theorem chapter01_relative_degree_one_closed_immersion
    {S : Scheme.{u}} (𝒜 : Chapter01RelativeGradedAlgebra S)
    (h₀ : Chapter01RelativeDegreeZeroIsStructureSheaf 𝒜)
    (h : chapter01RelativeGeneratedInDegreeOneByFiniteType 𝒜) :
    ∃ (r : ℕ) (P : Chapter01RelativeProjectiveSpace S r)
      (ι : (chapter01RelativeProj 𝒜).scheme ⟶ P.scheme),
      IsClosedImmersion ι ∧
        ι ≫ P.projection =
          (chapter01RelativeProj 𝒜).projection := by
  sorry

/-! A presentation of a family by a genuine degree-one relative Proj.  The
comparison is part of the data so that later projective embeddings are derived
from the graded presentation rather than supplied as an unrelated witness. -/
structure Chapter01RelativeDegreeOneGradedPresentation
    {X S : Scheme.{u}} (f : X ⟶ S) where
  algebra : Chapter01RelativeGradedAlgebra S
  degreeZeroIsStructureSheaf :
    Chapter01RelativeDegreeZeroIsStructureSheaf algebra
  generatedInDegreeOne :
    chapter01RelativeGeneratedInDegreeOneByFiniteType algebra
  relativeProj : Chapter01RelativeProj algebra
  comparison : X ≅ relativeProj.scheme
  comparison_over : comparison.hom ≫ relativeProj.projection = f

structure Chapter01RelativeProjectiveEmbeddingData
    {X S : Scheme.{u}} (f : X ⟶ S) where
  rank : ℕ
  projectiveSpace : Chapter01RelativeProjectiveSpace S rank
  embedding : X ⟶ projectiveSpace.scheme
  embedding_closed : IsClosedImmersion embedding
  overBase : embedding ≫ projectiveSpace.projection = f

theorem chapter01_relative_degree_one_presentation_gives_projective_embedding
    {X S : Scheme.{u}} {f : X ⟶ S}
    (D : Chapter01RelativeDegreeOneGradedPresentation f) :
    Nonempty (Chapter01RelativeProjectiveEmbeddingData f) := by
  sorry

structure Chapter01RelativeGradedIdeal {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) where
  carrier : ∀ U : S.Opens, Ideal (𝒜.sections U)
  homogeneous : ∀ U, (carrier U).IsHomogeneous (𝒜.grading U)
  restriction_mem :
    ∀ {U V : S.Opens} (i : U ⟶ V) (x : 𝒜.sections V),
      x ∈ carrier V → 𝒜.restriction i x ∈ carrier U
  /-- Membership in the ideal is local for covers of an open.  This is the
  subpresheaf/sheaf condition omitted by a mere family of compatible ideals. -/
  carrier_local :
    ∀ (U : S.Opens) (ι : Type*) (V : ι → S.Opens)
      (iVU : ∀ i, V i ⟶ U) (_hcover : (⨆ i, V i) = U) (x : 𝒜.sections U),
      (∀ i, 𝒜.restriction (iVU i) x ∈ carrier (V i)) ↔ x ∈ carrier U

def chapter01RelativeGradedIdealComponent
    {S : Scheme.{u}} {𝒜 : Chapter01RelativeGradedAlgebra S}
    (I : Chapter01RelativeGradedIdeal 𝒜) (U : S.Opens) (n : ℕ) :
    AddSubgroup (𝒜.sections U).carrier where
  carrier := {x | x ∈ I.carrier U ∧ x ∈ 𝒜.grading U n}
  zero_mem' := ⟨(I.carrier U).zero_mem, (𝒜.grading U n).zero_mem⟩
  add_mem' := by
    intro x y hx hy
    exact ⟨(I.carrier U).add_mem hx.1 hy.1,
      (𝒜.grading U n).add_mem hx.2 hy.2⟩
  neg_mem' := by
    intro x hx
    exact ⟨(I.carrier U).neg_mem hx.1, (𝒜.grading U n).neg_mem hx.2⟩

def chapter01RelativeGradedIdealComponentRestriction
    {S : Scheme.{u}} {𝒜 : Chapter01RelativeGradedAlgebra S}
    (I : Chapter01RelativeGradedIdeal 𝒜) {U V : S.Opens} (i : U ⟶ V) (n : ℕ) :
    chapter01RelativeGradedIdealComponent I V n →+
      chapter01RelativeGradedIdealComponent I U n where
  toFun := fun x =>
    ⟨𝒜.restriction i x,
      ⟨I.restriction_mem i x x.property.1,
        𝒜.restriction_preserves i n x x.property.2⟩⟩
  map_zero' := by
    apply Subtype.ext
    exact (𝒜.restriction i).map_zero
  map_add' := by
    intro x y
    apply Subtype.ext
    exact (𝒜.restriction i).map_add x y

structure Chapter01RelativeGradedIdealQuasicoherentData {S : Scheme.{u}}
    {𝒜 : Chapter01RelativeGradedAlgebra S}
    (I : Chapter01RelativeGradedIdeal 𝒜) where
  component : ℕ → S.Modules
  component_isQuasicoherent : ∀ n, (component n).IsQuasicoherent
  component_sections : ∀ (n : ℕ) (U : S.Opens),
    AddCommGrpCat.of (chapter01RelativeGradedIdealComponent I U n) ≅
      (Scheme.Modules.presheaf (component n)).obj (Opposite.op U)
  component_sections_restriction :
    ∀ {U V : S.Opens} (i : U ⟶ V) (n : ℕ)
      (x : chapter01RelativeGradedIdealComponent I V n),
      (component_sections n U).hom
          (chapter01RelativeGradedIdealComponentRestriction I i n x) =
        (Scheme.Modules.presheaf (component n)).map i.op
          ((component_sections n V).hom x)
  /-- The component identifications preserve the natural degree-zero
  structure-sheaf action. -/
  component_sections_degree_zero_smul :
    ∀ (n : ℕ) (U : S.Opens)
      (r : (S.presheaf.obj (Opposite.op U)).carrier)
      (x : chapter01RelativeGradedIdealComponent I U n),
      ∃ y : chapter01RelativeGradedIdealComponent I U n,
        y.1 = 𝒜.degree_zero_map U r * x.1 ∧
          (component_sections n U).hom y =
            r • (component_sections n U).hom x

def Chapter01RelativeGradedIdealIsQuasicoherent {S : Scheme.{u}}
    {𝒜 : Chapter01RelativeGradedAlgebra S}
    (I : Chapter01RelativeGradedIdeal 𝒜) : Prop :=
  Nonempty (Chapter01RelativeGradedIdealQuasicoherentData I)

/-! The quotient construction is packaged together with the local quotient
maps.  The closed-immersion assertion is kept in its own theorem, so the
quotient record does not assume the geometric conclusion it is meant to prove. -/
structure Chapter01RelativeQuotientData {S : Scheme.{u}}
    {𝒜 : Chapter01RelativeGradedAlgebra S}
    (I : Chapter01RelativeGradedIdeal 𝒜)
    (_hI : Chapter01RelativeGradedIdealIsQuasicoherent I) where
  algebra : Chapter01RelativeGradedAlgebra S
  quotientMap : ∀ U : S.Opens, 𝒜.sections U →+* algebra.sections U
  /-- On affine opens the sectionwise map is the usual quotient map.  A
  sheaf quotient need not be sectionwise surjective on arbitrary opens. -/
  quotientMap_surjective : ∀ U, IsAffineOpen U → Function.Surjective (quotientMap U)
  quotientMap_kernel : ∀ U,
    RingHom.ker (quotientMap U) = I.carrier U
  quotientMap_restriction :
    ∀ {U V : S.Opens} (i : U ⟶ V),
      (algebra.restriction i).comp (quotientMap V) =
        (quotientMap U).comp (𝒜.restriction i)
  quotientMap_graded :
    ∀ (U : S.Opens) (n : ℕ) (x : 𝒜.sections U),
      x ∈ 𝒜.grading U n → quotientMap U x ∈ algebra.grading U n
  quotientMap_degree_zero :
    ∀ (U : S.Opens) (x : (S.presheaf.obj (Opposite.op U)).carrier),
      quotientMap U (𝒜.degree_zero_map U x) = algebra.degree_zero_map U x

noncomputable def chapter01RelativeQuotientData {S : Scheme.{u}}
    {𝒜 : Chapter01RelativeGradedAlgebra S}
    (I : Chapter01RelativeGradedIdeal 𝒜)
    (hI : Chapter01RelativeGradedIdealIsQuasicoherent I) :
    Chapter01RelativeQuotientData I hI :=
  by
    sorry

theorem chapter01_relative_quotient_exists {S : Scheme.{u}}
    {𝒜 : Chapter01RelativeGradedAlgebra S}
    (I : Chapter01RelativeGradedIdeal 𝒜)
    (hI : Chapter01RelativeGradedIdealIsQuasicoherent I) :
    Nonempty (Chapter01RelativeQuotientData I hI) := by
  sorry

noncomputable def chapter01RelativeQuotient {S : Scheme.{u}}
    {𝒜 : Chapter01RelativeGradedAlgebra S}
    (I : Chapter01RelativeGradedIdeal 𝒜)
    (hI : Chapter01RelativeGradedIdealIsQuasicoherent I) : Chapter01RelativeGradedAlgebra S :=
  (chapter01RelativeQuotientData I hI).algebra

theorem chapter01_relative_ideal_closed_immersion {S : Scheme.{u}}
    {𝒜 : Chapter01RelativeGradedAlgebra S}
    (I : Chapter01RelativeGradedIdeal 𝒜)
    (hI : Chapter01RelativeGradedIdealIsQuasicoherent I) :
    ∃ (ι : (chapter01RelativeProj (chapter01RelativeQuotient I hI)).scheme ⟶
      (chapter01RelativeProj 𝒜).scheme),
      IsClosedImmersion ι ∧
        ι ≫ (chapter01RelativeProj 𝒜).projection =
          (chapter01RelativeProj (chapter01RelativeQuotient I hI)).projection := by
  sorry

def chapter01Saturation {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    (I : HomogeneousIdeal 𝒜) : HomogeneousIdeal 𝒜 :=
  Ideal.homogeneousCore 𝒜
    (Ideal.span {a : A | ∃ n : ℕ, a ∈ 𝒜 n ∧
      ∃ N : ℕ, ∀ b : A,
        b ∈ (chapter01IrrelevantIdeal 𝒜) ^ N → b * a ∈ I.toIdeal})

theorem chapter01_saturation_characterization {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    (I : HomogeneousIdeal 𝒜) :
    ∀ (n : ℕ) (a : A), a ∈ 𝒜 n →
      (a ∈ chapter01Saturation 𝒜 I ↔
        ∃ N : ℕ, ∀ b : A, b ∈ (chapter01IrrelevantIdeal 𝒜) ^ N → b * a ∈ I.toIdeal) := by
  sorry

def Chapter01SameProjPointLocus {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    (I J : HomogeneousIdeal 𝒜) : Prop :=
  ∀ x : ProjectiveSpectrum 𝒜,
    I ≤ x.asHomogeneousIdeal ↔ J ≤ x.asHomogeneousIdeal

theorem chapter01_saturation_same_proj_point_locus {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] (I : HomogeneousIdeal 𝒜) :
    Chapter01SameProjPointLocus 𝒜 I (chapter01Saturation 𝒜 I) := by
  sorry

/-! The closed subscheme is represented by Mathlib's canonical ideal-sheaf
construction.  The affine ideals are obtained from homogeneous localization;
`IdealSheafData.ofIdeals` then supplies the unique compatible ideal sheaf. -/
noncomputable def chapter01ProjHomogeneousLocalizationIdeal
    {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    (I : HomogeneousIdeal 𝒜) {d : ℕ} (f : A)
    (_hf : f ∈ 𝒜 d) (_hd : 0 < d) :
    Ideal (HomogeneousLocalization.Away 𝒜 f) :=
  Ideal.span (Set.range fun z :
      Σ n : ℕ, {x : A // x ∈ I.toIdeal ∧ x ∈ 𝒜 (n • d)} =>
    HomogeneousLocalization.Away.mk 𝒜 _hf z.1 z.2.1 z.2.2.2)

/-! A standard chart is recorded as an affine open in order to state the
canonical ideal compatibility on the nose at the chart's section ring. -/
noncomputable def chapter01SchemeStandardAffineOpen
    {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    {d : ℕ} (f : A) (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    (AlgebraicGeometry.«Proj» 𝒜).affineOpens :=
  ⟨chapter01SchemeStandardOpen 𝒜 f,
    IsAffine.of_isIso (chapter01StandardChartIso 𝒜 hf hd).hom⟩

noncomputable def chapter01ProjCanonicalAffineIdeal
    {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    (I : HomogeneousIdeal 𝒜)
    (U : (AlgebraicGeometry.«Proj» 𝒜).affineOpens) :
    Ideal ((AlgebraicGeometry.«Proj» 𝒜).presheaf.obj (Opposite.op U.1)).carrier := by
  sorry

noncomputable def chapter01ProjCanonicalIdealSheaf
    {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    (I : HomogeneousIdeal 𝒜) :
    Scheme.IdealSheafData (AlgebraicGeometry.«Proj» 𝒜) :=
  Scheme.IdealSheafData.ofIdeals (chapter01ProjCanonicalAffineIdeal 𝒜 I)

structure Chapter01ProjClosedSubschemeInterface {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] where
  /-- The interface carries the canonical ideal-sheaf construction rather
  than being an empty witness unrelated to the homogeneous ideal. -/
  canonicalIdealSheaf : HomogeneousIdeal 𝒜 →
    Scheme.IdealSheafData (AlgebraicGeometry.«Proj» 𝒜)
  canonicalIdealSheaf_eq : ∀ I,
    canonicalIdealSheaf I = chapter01ProjCanonicalIdealSheaf 𝒜 I
  /-- On every standard chart the ideal sheaf is transported from the ideal
  generated by homogeneous localized fractions. -/
  canonicalIdealSheaf_standard_chart :
    ∀ (I : HomogeneousIdeal 𝒜) {d : ℕ} (f : A)
      (hf : f ∈ 𝒜 d) (hd : 0 < d),
      ∃ e : HomogeneousLocalization.Away 𝒜 f ≃+*
          ((AlgebraicGeometry.«Proj» 𝒜).presheaf.obj
            (Opposite.op (chapter01SchemeStandardOpen 𝒜 f))).carrier,
        (canonicalIdealSheaf I).ideal
            (chapter01SchemeStandardAffineOpen 𝒜 f hf hd) =
          Ideal.map e.toRingHom
            (chapter01ProjHomogeneousLocalizationIdeal 𝒜 I f hf hd)
  /-- Saturation invariance is attached to the canonical ideal-sheaf
  construction, rather than to an unrelated closed-subscheme witness. -/
  canonicalIdealSheaf_saturation :
    ∀ I : HomogeneousIdeal 𝒜,
      canonicalIdealSheaf (chapter01Saturation 𝒜 I) = canonicalIdealSheaf I

noncomputable def chapter01ProjClosedSubschemeInterface
    {A : Type*} [CommRing A]
    {𝒜 : ℕ → Submodule ℤ A} [GradedAlgebra 𝒜] :
    Chapter01ProjClosedSubschemeInterface 𝒜 :=
  { canonicalIdealSheaf := fun I => chapter01ProjCanonicalIdealSheaf 𝒜 I
    canonicalIdealSheaf_eq := by intro I; rfl
    canonicalIdealSheaf_standard_chart := by
      intro I d f hf hd
      sorry
    canonicalIdealSheaf_saturation := by
      intro I
      sorry }

namespace Chapter01ProjClosedSubschemeInterface

noncomputable def idealSheaf {A : Type*} [CommRing A]
    {𝒜 : ℕ → Submodule ℤ A} [GradedAlgebra 𝒜]
    (C : Chapter01ProjClosedSubschemeInterface 𝒜) (I : HomogeneousIdeal 𝒜) :=
  C.canonicalIdealSheaf I

abbrev scheme {A : Type*} [CommRing A]
    {𝒜 : ℕ → Submodule ℤ A} [GradedAlgebra 𝒜]
    (C : Chapter01ProjClosedSubschemeInterface 𝒜) (I : HomogeneousIdeal 𝒜) :=
  (C.idealSheaf I).subscheme

abbrev inclusion {A : Type*} [CommRing A]
    {𝒜 : ℕ → Submodule ℤ A} [GradedAlgebra 𝒜]
    (C : Chapter01ProjClosedSubschemeInterface 𝒜) (I : HomogeneousIdeal 𝒜) :=
  (C.idealSheaf I).subschemeι

theorem inclusion_closed {A : Type*} [CommRing A]
    {𝒜 : ℕ → Submodule ℤ A} [GradedAlgebra 𝒜]
    (C : Chapter01ProjClosedSubschemeInterface 𝒜) (I : HomogeneousIdeal 𝒜) :
    IsClosedImmersion (C.inclusion I) := by
  sorry

end Chapter01ProjClosedSubschemeInterface

def Chapter01SameProjClosedSubscheme {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    (C : Chapter01ProjClosedSubschemeInterface 𝒜)
    (I J : HomogeneousIdeal 𝒜) : Prop :=
  ∃ e : C.scheme I ≅ C.scheme J, e.hom ≫ C.inclusion J = C.inclusion I

theorem chapter01_saturation_same_proj_closed_subscheme
    {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    (C : Chapter01ProjClosedSubschemeInterface 𝒜)
    (I : HomogeneousIdeal 𝒜) :
    Chapter01SameProjClosedSubscheme 𝒜 C I (chapter01Saturation 𝒜 I) := by
  change ∃ e :
      (C.canonicalIdealSheaf I).subscheme ≅
        (C.canonicalIdealSheaf (chapter01Saturation 𝒜 I)).subscheme,
      e.hom ≫ (C.canonicalIdealSheaf (chapter01Saturation 𝒜 I)).subschemeι =
        (C.canonicalIdealSheaf I).subschemeι
  rw [C.canonicalIdealSheaf_saturation I]
  exact ⟨Iso.refl _, by simp⟩

/-! ### 1.4 Standard opens and base change -/

/-! Pullback is degreewise base change of the quasi-coherent components together
with the pulled-back affine chart model. -/
def chapter01RelativeProjBaseChange {S T : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) (g : T ⟶ S) : Scheme.{u} :=
  Limits.pullback (chapter01RelativeProj 𝒜).projection g

structure Chapter01RelativePullbackData {S T : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) (g : T ⟶ S) where
  algebra : Chapter01RelativeGradedAlgebra T
  /-- The pulled-back degreewise sheaves are identified with the components of
  the pulled-back graded algebra. -/
  component_base_change : ∀ n : ℕ,
    (Scheme.Modules.pullback g).obj (𝒜.component n) ≅ algebra.component n
  /-- Pullback of the structure-sheaf unit agrees with the unit of the
  pulled-back sheaf-valued graded algebra. -/
  unit_base_change :
    (Scheme.Modules.pullback g).obj (SheafOfModules.unit S.ringCatSheaf) ≅
      SheafOfModules.unit T.ringCatSheaf
  component_base_change_unit :
    unit_base_change.hom ≫ algebra.sheaf_unit =
      (Scheme.Modules.pullback g).map 𝒜.sheaf_unit ≫ (component_base_change 0).hom
  /-- The pullback/tensor comparison used to transport multiplication. -/
  multiplication_base_change : ∀ m n,
    chapter01SheafTensor ((Scheme.Modules.pullback g).obj (𝒜.component m))
        ((Scheme.Modules.pullback g).obj (𝒜.component n)) ≅
      (Scheme.Modules.pullback g).obj
        (chapter01SheafTensor (𝒜.component m) (𝒜.component n))
  component_base_change_multiplication : ∀ m n,
    (multiplication_base_change m n).hom ≫
        (Scheme.Modules.pullback g).map (𝒜.sheaf_multiplication m n) ≫
        (component_base_change (m + n)).hom =
      chapter01SheafTensorMap (component_base_change m).hom
          (component_base_change n).hom ≫
        algebra.sheaf_multiplication m n
  /-- The affine restriction maps and their degree preservation remain part of
  the pulled-back chart model. -/
  restriction_id : ∀ U : T.Opens,
    algebra.restriction (U := U) (V := U) (𝟙 U) = RingHom.id _
  restriction_comp :
    ∀ {U V W : T.Opens} (i : U ⟶ V) (j : V ⟶ W),
      (algebra.restriction (U := U) (V := V) i).comp
          (algebra.restriction (U := V) (V := W) j) =
        algebra.restriction (U := U) (V := W) (i ≫ j)
  restriction_preserves :
    ∀ {U V : T.Opens} (i : U ⟶ V) (n : ℕ) (x : algebra.sections V),
      x ∈ algebra.grading V n → algebra.restriction i x ∈ algebra.grading U n
  /-- The canonical comparison morphism between the pulled-back Proj and the
  Proj of the pulled-back sheaf-valued graded algebra. -/
  proj_base_change_comparison :
    chapter01RelativeProjBaseChange 𝒜 g ⟶
      (chapter01RelativeProj algebra).scheme

noncomputable def chapter01RelativePullbackData {S T : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) (g : T ⟶ S) :
    Chapter01RelativePullbackData 𝒜 g :=
  by
    sorry

theorem chapter01_relative_pullback_exists {S T : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) (g : T ⟶ S) :
    Nonempty (Chapter01RelativePullbackData 𝒜 g) := by
  sorry

noncomputable def chapter01RelativePullback {S T : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) (g : T ⟶ S) :
    Chapter01RelativeGradedAlgebra T :=
  (chapter01RelativePullbackData 𝒜 g).algebra

noncomputable def chapter01RelativeProjBaseChangeComparison {S T : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) (g : T ⟶ S) :
    chapter01RelativeProjBaseChange 𝒜 g ⟶
      (chapter01RelativeProj (chapter01RelativePullback 𝒜 g)).scheme :=
  (chapter01RelativePullbackData 𝒜 g).proj_base_change_comparison

theorem chapter01_relative_proj_base_change {S T : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) (g : T ⟶ S) :
    ∃ (e : chapter01RelativeProjBaseChange 𝒜 g ⟶
      (chapter01RelativeProj (chapter01RelativePullback 𝒜 g)).scheme),
      IsIso e ∧
        e ≫ (chapter01RelativeProj (chapter01RelativePullback 𝒜 g)).projection =
          Limits.pullback.snd (chapter01RelativeProj 𝒜).projection g := by
  refine ⟨chapter01RelativeProjBaseChangeComparison 𝒜 g, ?_⟩
  sorry

/- The ring-level chart statement is orientation-independent up to the canonical
commutativity isomorphism; Mathlib's tensor product uses `R' ⊗[R] A`. -/
instance chapter01HomogeneousLocalizationAlgebra {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (f : A) :
    Algebra R (HomogeneousLocalization.Away 𝒜 f) :=
  let h : R →+* HomogeneousLocalization.Away 𝒜 f :=
    (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f)).comp
      ((GradedRing.projZeroRingHom' 𝒜).comp (algebraMap R A))
  h.toAlgebra

/-! The relative chart base ring is the degree-zero part of the graded
algebra.  In particular, the scalar map used by the localization algebra
instance above agrees with the given `R`-algebra structure only when the
scalars are homogeneous of degree zero. -/
def chapter01ScalarsInDegreeZero {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] : Prop :=
  ∀ r : R, algebraMap R A r ∈ 𝒜 0

theorem chapter01_homogeneous_localization_base_change
    {R A R' : Type*} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R']
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (hR : chapter01ScalarsInDegreeZero 𝒜)
    {d : ℕ} {f : A} (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    Nonempty ((R' ⊗[R] HomogeneousLocalization.Away 𝒜 f) ≃+*
      HomogeneousLocalization.Away
        (fun n => (𝒜 n).baseChange R') (1 ⊗ₜ[R] f)) := by
  sorry

theorem chapter01_relative_proj_base_change_without_flatness {S T : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) (g : T ⟶ S) :
    ∃ (e : chapter01RelativeProjBaseChange 𝒜 g ⟶
      (chapter01RelativeProj (chapter01RelativePullback 𝒜 g)).scheme),
      IsIso e ∧
        e ≫ (chapter01RelativeProj (chapter01RelativePullback 𝒜 g)).projection =
          Limits.pullback.snd (chapter01RelativeProj 𝒜).projection g := by
  exact chapter01_relative_proj_base_change 𝒜 g

noncomputable def chapter01RelativeFiberAlgebra {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) (s : S) :
    Chapter01RelativeGradedAlgebra (AlgebraicGeometry.Spec (S.residueField s)) :=
  chapter01RelativePullback 𝒜 (S.fromSpecResidueField s)

theorem chapter01_relative_proj_fiber {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) (s : S) :
    ∃ (e : (chapter01RelativeProj 𝒜).projection.fiber s ⟶
      (chapter01RelativeProj (chapter01RelativeFiberAlgebra 𝒜 s)).scheme),
      IsIso e ∧
        e ≫ (chapter01RelativeProj (chapter01RelativeFiberAlgebra 𝒜 s)).projection =
          (chapter01RelativeProj 𝒜).projection.fiberToSpecResidueField s := by
  sorry

/-! ### 1.5 Twisting sheaves -/

def chapter01Shift {M : Type*} [AddCommGroup M]
    (𝓜 : ℤ → Submodule ℤ M) (n : ℤ) : ℤ → Submodule ℤ M :=
  fun q => 𝓜 (n + q)

@[simp] theorem chapter01_shift_apply {M : Type*} [AddCommGroup M]
    (𝓜 : ℤ → Submodule ℤ M)
    (n q : ℤ) : chapter01Shift 𝓜 n q = 𝓜 (n + q) :=
  rfl

instance chapter01NatVAddInt : VAdd ℕ ℤ where
  vadd n q := (n : ℤ) + q

structure Chapter01GradedModule
    {A M : Type*} [CommRing A] [AddCommGroup M]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    (𝓜 : ℤ → Submodule ℤ M) [Module A M] where
  gradedSMul : SetLike.GradedSMul 𝒜 𝓜
  decomposition : DirectSum.Decomposition 𝓜

def chapter01OrdinaryGradedComponents {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] : ℤ → Submodule ℤ A :=
  fun n => if _h : 0 ≤ n then 𝒜 n.toNat else ⊥

noncomputable def chapter01OrdinaryGradedModuleData {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] :
    Chapter01GradedModule 𝒜 (chapter01OrdinaryGradedComponents 𝒜) := by
  sorry

def chapter01RelativeGradedComponents {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) (U : S.Opens) :
    ℤ → Submodule ℤ (𝒜.sections U).carrier :=
  fun n => if _h : 0 ≤ n then 𝒜.grading U n.toNat else ⊥

noncomputable def chapter01RelativeGradedModuleData {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) (U : S.Opens) :
    Chapter01GradedModule (𝒜.grading U)
      (chapter01RelativeGradedComponents 𝒜 U) := by
  sorry

/-! The chart module is represented by localized fractions together with the
degree-zero witness for the declared shift `M(n)_q = M_(n+q)`.  This is a
type-level interface rather than an untyped placeholder. -/
noncomputable def chapter01ModuleAwayDegreeZero
    {A : Type uA} {M : Type uM} [CommRing A] [AddCommGroup M]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    (𝓜 : ℤ → Submodule ℤ M) [Module A M]
    (_G : Chapter01GradedModule 𝒜 𝓜) (n : ℤ)
    {d : ℕ} (f : A) (_hf : f ∈ 𝒜 d) (_hd : 0 < d) : Type (max uA uM) :=
  { z : LocalizedModule (Submonoid.powers f) M //
      ∃ (k : ℕ) (m : M),
        z = LocalizedModule.mk m
          (⟨f ^ k, (Submonoid.powers f).pow_mem (Submonoid.mem_powers f) k⟩ :
            Submonoid.powers f) ∧
           m ∈ 𝓜 (n + (k : ℤ) * (d : ℤ)) }

noncomputable instance chapter01ModuleAwayDegreeZeroAddCommGroup
    {A : Type uA} {M : Type uM} [CommRing A] [AddCommGroup M]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    (𝓜 : ℤ → Submodule ℤ M) [Module A M]
    (G : Chapter01GradedModule 𝒜 𝓜) (n : ℤ)
    {d : ℕ} (f : A) (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    AddCommGroup (chapter01ModuleAwayDegreeZero 𝒜 𝓜 G n f hf hd) := by
  sorry

noncomputable instance chapter01ModuleAwayDegreeZeroModule
    {A : Type uA} {M : Type uM} [CommRing A] [AddCommGroup M]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    (𝓜 : ℤ → Submodule ℤ M) [Module A M]
    (G : Chapter01GradedModule 𝒜 𝓜) (n : ℤ)
    {d : ℕ} (f : A) (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    Module (HomogeneousLocalization.Away 𝒜 f)
      (chapter01ModuleAwayDegreeZero 𝒜 𝓜 G n f hf hd) := by
  sorry

/-! A chart comparison is semilinear over the chart-ring isomorphism.  This
retains both the module structure of localized fractions and the module
structure on sections of the sheaf, rather than forgetting both to bare types. -/
structure Chapter01ChartModuleEquivalence
    (R R' M N : Type*) [Ring R] [Ring R']
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R' N] where
  ringEquiv : R ≃+* R'
  moduleEquiv : M ≃+ N
  map_smul : ∀ (c : R) (x : M),
    moduleEquiv (c • x) = ringEquiv c • moduleEquiv x

abbrev chapter01ChartRingRestrictionMap {X : Scheme.{u}}
    {U V : X.Opens} (i : U ⟶ V) :
    (X.ringCatSheaf.obj.obj (Opposite.op V)).carrier →+*
      (X.ringCatSheaf.obj.obj (Opposite.op U)).carrier :=
  (X.ringCatSheaf.obj.map i.op).hom

abbrev chapter01ChartModuleRestrictionMap {X : Scheme.{u}}
    (M : X.Modules) {U V : X.Opens} (i : U ⟶ V) :
    ((Scheme.Modules.presheaf M).obj (Opposite.op V)).carrier →+
      ((Scheme.Modules.presheaf M).obj (Opposite.op U)).carrier :=
  (((Scheme.Modules.toPresheafOfModules X).obj M).map i.op).hom.toAddMonoidHom

/-! The source-side module map is the homogeneous-fraction restriction map.
Its construction is kept as an explicit typed interface so all chart
comparisons use the same degree-zero localization model. -/
noncomputable def chapter01ModuleAwayDegreeZeroRestrictionMap
    {A : Type uA} {M : Type uM} [CommRing A] [AddCommGroup M]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    (𝓜 : ℤ → Submodule ℤ M) [Module A M]
    (G : Chapter01GradedModule 𝒜 𝓜) (n : ℤ)
    {d e : ℕ} (f : A) (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (g : A) (hg : g ∈ 𝒜 e) (he : 0 < e)
    (hfg : f * g ∈ 𝒜 (d + e)) :
    chapter01ModuleAwayDegreeZero 𝒜 𝓜 G n f hf hd →+
      chapter01ModuleAwayDegreeZero 𝒜 𝓜 G n (f * g) hfg
        (Nat.add_pos_right d he) := by
  sorry

/-! A chart comparison is compatible with restriction precisely when both its
ring and module squares commute and both restriction maps are semilinear. -/
def Chapter01ChartModuleRestrictionCompatible
    {R R' S S' M N P Q : Type*}
    [Ring R] [Ring R'] [Ring S] [Ring S']
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module R M] [Module R' N] [Module S P] [Module S' Q]
    (e : Chapter01ChartModuleEquivalence R R' M N)
    (e' : Chapter01ChartModuleEquivalence S S' P Q)
    (sourceRingMap : R →+* S) (targetRingMap : R' →+* S')
    (sourceModuleMap : M →+ P) (targetModuleMap : N →+ Q) : Prop :=
  (∀ (c : R) (x : M),
    sourceModuleMap (c • x) = sourceRingMap c • sourceModuleMap x) ∧
  (∀ (c : R') (x : N),
    targetModuleMap (c • x) = targetRingMap c • targetModuleMap x) ∧
  (∀ c, e'.ringEquiv (sourceRingMap c) =
    targetRingMap (e.ringEquiv c)) ∧
  (∀ x, e'.moduleEquiv (sourceModuleMap x) =
    targetModuleMap (e.moduleEquiv x))

/-! The overlap predicate includes the two-step and direct chart squares and
the cocycle equations for all four underlying restriction maps. -/
def Chapter01ChartModuleOverlapCompatible
    {R₀ R₁ R₂ R₀' R₁' R₂' M₀ M₁ M₂ N₀ N₁ N₂ : Type*}
    [Ring R₀] [Ring R₁] [Ring R₂] [Ring R₀'] [Ring R₁'] [Ring R₂']
    [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup M₂]
    [AddCommGroup N₀] [AddCommGroup N₁] [AddCommGroup N₂]
    [Module R₀ M₀] [Module R₁ M₁] [Module R₂ M₂]
    [Module R₀' N₀] [Module R₁' N₁] [Module R₂' N₂]
    (e₀ : Chapter01ChartModuleEquivalence R₀ R₀' M₀ N₀)
    (e₁ : Chapter01ChartModuleEquivalence R₁ R₁' M₁ N₁)
    (e₂ : Chapter01ChartModuleEquivalence R₂ R₂' M₂ N₂)
    (sourceRingMap₀₁ : R₀ →+* R₁) (sourceRingMap₁₂ : R₁ →+* R₂)
    (sourceRingMap₀₂ : R₀ →+* R₂)
    (targetRingMap₀₁ : R₀' →+* R₁') (targetRingMap₁₂ : R₁' →+* R₂')
    (targetRingMap₀₂ : R₀' →+* R₂')
    (sourceModuleMap₀₁ : M₀ →+ M₁) (sourceModuleMap₁₂ : M₁ →+ M₂)
    (sourceModuleMap₀₂ : M₀ →+ M₂)
    (targetModuleMap₀₁ : N₀ →+ N₁) (targetModuleMap₁₂ : N₁ →+ N₂)
    (targetModuleMap₀₂ : N₀ →+ N₂) : Prop :=
  Chapter01ChartModuleRestrictionCompatible e₀ e₁
      sourceRingMap₀₁ targetRingMap₀₁ sourceModuleMap₀₁ targetModuleMap₀₁ ∧
  Chapter01ChartModuleRestrictionCompatible e₁ e₂
      sourceRingMap₁₂ targetRingMap₁₂ sourceModuleMap₁₂ targetModuleMap₁₂ ∧
  Chapter01ChartModuleRestrictionCompatible e₀ e₂
      sourceRingMap₀₂ targetRingMap₀₂ sourceModuleMap₀₂ targetModuleMap₀₂ ∧
  sourceRingMap₀₂ = sourceRingMap₁₂.comp sourceRingMap₀₁ ∧
  targetRingMap₀₂ = targetRingMap₁₂.comp targetRingMap₀₁ ∧
  sourceModuleMap₀₂ = sourceModuleMap₁₂.comp sourceModuleMap₀₁ ∧
  targetModuleMap₀₂ = targetModuleMap₁₂.comp targetModuleMap₀₁

noncomputable def chapter01TwistedLocalSections
    {A : Type uA} {M : Type uM} [CommRing A] [AddCommGroup M]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    (𝓜 : ℤ → Submodule ℤ M) [Module A M]
    (G : Chapter01GradedModule 𝒜 𝓜) (n : ℤ)
    {d : ℕ} (f : A) (hf : f ∈ 𝒜 d) (hd : 0 < d) : Type (max uA uM) :=
  chapter01ModuleAwayDegreeZero 𝒜 𝓜 G n f hf hd

structure Chapter01SheafDualData {X : Scheme.{u}} (M : X.Modules)
    (hM : Chapter01IsLineBundle M) where
  dual : X.Modules
  dual_isQuasicoherent : dual.IsQuasicoherent
  dual_isLineBundle : Chapter01IsLineBundle dual
  evaluation : chapter01SheafTensor dual M ⟶ SheafOfModules.unit X.ringCatSheaf
  coevaluation : SheafOfModules.unit X.ringCatSheaf ⟶ chapter01SheafTensor M dual
  evaluation_isIso : IsIso evaluation
  left_triangle :
    (chapter01SheafTensorLeftUnitor M).inv ≫
        chapter01SheafTensorMap coevaluation (𝟙 M) ≫
        (chapter01SheafTensorAssociator M dual M).hom ≫
        chapter01SheafTensorMap (𝟙 M) evaluation ≫
        (chapter01SheafTensorRightUnitor M).hom = 𝟙 M
  right_triangle :
    (chapter01SheafTensorRightUnitor dual).inv ≫
        chapter01SheafTensorMap (𝟙 dual) coevaluation ≫
        (chapter01SheafTensorAssociator dual M dual).inv ≫
        chapter01SheafTensorMap evaluation (𝟙 dual) ≫
        (chapter01SheafTensorLeftUnitor dual).hom = 𝟙 dual

theorem chapter01_sheaf_dual_exists {X : Scheme.{u}} (M : X.Modules)
    (hM : Chapter01IsLineBundle M) :
    Nonempty (Chapter01SheafDualData M hM) := by
  sorry

noncomputable def chapter01SheafDual {X : Scheme.{u}}
    (M : X.Modules) (hM : Chapter01IsLineBundle M) : X.Modules := by
  sorry

structure Chapter01GradedModuleProjSheafification
    {A M : Type*} [CommRing A] [AddCommGroup M]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    (𝓜 : ℤ → Submodule ℤ M) [Module A M]
    (G : Chapter01GradedModule 𝒜 𝓜) (n : ℤ) where
  sheaf : (AlgebraicGeometry.«Proj» 𝒜).Modules
  sheaf_isQuasicoherent : sheaf.IsQuasicoherent
  chart : ∀ {d : ℕ} (f : A) (hf : f ∈ 𝒜 d) (hd : 0 < d),
    Chapter01ChartModuleEquivalence
      (HomogeneousLocalization.Away 𝒜 f)
      (((AlgebraicGeometry.«Proj» 𝒜).ringCatSheaf.obj.obj
        (Opposite.op (chapter01SchemeStandardOpen 𝒜 f))).carrier)
      (chapter01ModuleAwayDegreeZero 𝒜 𝓜 G n f hf hd)
      ((((Scheme.Modules.toPresheafOfModules (AlgebraicGeometry.«Proj» 𝒜)).obj sheaf).obj
        (Opposite.op (chapter01SchemeStandardOpen 𝒜 f))).carrier)

  /-- The canonical map from a graded component to the global sections of its
  twisted sheaf is part of the sheafification interface.  Without this field,
  the later direct-sum map would have no source-side map to use. -/
  globalSectionsMap :
    𝓜 n →+
      (((Scheme.Modules.presheaf sheaf).obj (Opposite.op ⊤)).carrier)

theorem chapter01_graded_module_proj_sheafification_exists
    {A M : Type*} [CommRing A] [AddCommGroup M]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    (𝓜 : ℤ → Submodule ℤ M) [Module A M]
    (G : Chapter01GradedModule 𝒜 𝓜) (n : ℤ) :
    Nonempty (Chapter01GradedModuleProjSheafification 𝒜 𝓜 G n) := by
  sorry

noncomputable def chapter01GradedModuleProjSheaf
    {A M : Type*} [CommRing A] [AddCommGroup M]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    (𝓜 : ℤ → Submodule ℤ M) [Module A M]
    (G : Chapter01GradedModule 𝒜 𝓜) (n : ℤ) :
    (AlgebraicGeometry.«Proj» 𝒜).Modules :=
  (Classical.choice (chapter01_graded_module_proj_sheafification_exists 𝒜 𝓜 G n)).sheaf

noncomputable def chapter01GradedModuleProjGlobalSectionsMap
    {A M : Type*} [CommRing A] [AddCommGroup M]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    (𝓜 : ℤ → Submodule ℤ M) [Module A M]
    (G : Chapter01GradedModule 𝒜 𝓜) (n : ℤ) :
    𝓜 n →+
      (((Scheme.Modules.presheaf (chapter01GradedModuleProjSheaf 𝒜 𝓜 G n)).obj
        (Opposite.op ⊤)).carrier) :=
  (Classical.choice (chapter01_graded_module_proj_sheafification_exists 𝒜 𝓜 G n)).globalSectionsMap

abbrev chapter01OrdinaryChartSections {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] (n : ℤ)
    {d : ℕ} (f : A) (hf : f ∈ 𝒜 d) (hd : 0 < d) :=
  chapter01ModuleAwayDegreeZero 𝒜 (chapter01OrdinaryGradedComponents 𝒜)
    (chapter01OrdinaryGradedModuleData 𝒜) n f hf hd

abbrev chapter01RelativeChartSections {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) (_P : Chapter01RelativeProj 𝒜)
    (n : ℤ) (U : S.Opens) (_hU : IsAffineOpen U) {d : ℕ}
    (f : 𝒜.sections U) (hf : f ∈ 𝒜.grading U d) (hd : 0 < d) :=
  chapter01ModuleAwayDegreeZero (𝒜.grading U)
    (chapter01RelativeGradedComponents 𝒜 U)
    (chapter01RelativeGradedModuleData 𝒜 U) n f hf hd

def chapter01GeneratedInDegreeOne {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] : Prop :=
  Algebra.adjoin (𝒜 0) {x : A | x ∈ 𝒜 1} = ⊤

noncomputable def chapter01OrdinaryChartOpenRestriction
    {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] (f g : A) :
    chapter01SchemeStandardOpen 𝒜 (f * g) ⟶
      chapter01SchemeStandardOpen 𝒜 f :=
  homOfLE (by
    rw [chapter01_scheme_standard_open_inter]
    exact inf_le_left)

structure Chapter01OrdinaryTwistingSheafFamily {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] where
  sheaf : ℤ → (AlgebraicGeometry.«Proj» 𝒜).Modules
  sheaf_isQuasicoherent : ∀ n, (sheaf n).IsQuasicoherent
  chart : ∀ (n : ℤ) {d : ℕ} (f : A) (hf : f ∈ 𝒜 d) (hd : 0 < d),
    Chapter01ChartModuleEquivalence
      (HomogeneousLocalization.Away 𝒜 f)
      (((AlgebraicGeometry.«Proj» 𝒜).ringCatSheaf.obj.obj
        (Opposite.op (chapter01SchemeStandardOpen 𝒜 f))).carrier)
      (chapter01OrdinaryChartSections 𝒜 n f hf hd)
      ((((Scheme.Modules.toPresheafOfModules (AlgebraicGeometry.«Proj» 𝒜)).obj (sheaf n)).obj
        (Opposite.op (chapter01SchemeStandardOpen 𝒜 f))).carrier)
  /-- The chart equivalences commute with the canonical restriction maps on
  standard-open overlaps. -/
  chart_restriction_compatibility :
    ∀ (n : ℤ) {d e : ℕ} (f g : A)
      (hf : f ∈ 𝒜 d) (hd : 0 < d)
      (hg : g ∈ 𝒜 e) (he : 0 < e)
      (hfg : f * g ∈ 𝒜 (d + e)),
      Chapter01ChartModuleRestrictionCompatible
        (chart n f hf hd)
        (chart n (f * g) hfg (Nat.add_pos_right d he))
        (chapter01_standard_chart_restriction_map 𝒜 hf hd hg he)
        (chapter01ChartRingRestrictionMap
          (chapter01OrdinaryChartOpenRestriction 𝒜 f g))
        (chapter01ModuleAwayDegreeZeroRestrictionMap
          𝒜 (chapter01OrdinaryGradedComponents 𝒜)
            (chapter01OrdinaryGradedModuleData 𝒜) n f hf hd g hg he hfg)
        (chapter01ChartModuleRestrictionMap (sheaf n)
          (chapter01OrdinaryChartOpenRestriction 𝒜 f g))
  /-- The restriction data satisfy the cocycle identity on triple overlaps;
  the direct restriction is the composite of the two standard restrictions.
  -/
  chart_overlap_compatibility :
    ∀ (n : ℤ) {d e k : ℕ} (f g h : A)
      (hf : f ∈ 𝒜 d) (hd : 0 < d)
      (hg : g ∈ 𝒜 e) (he : 0 < e)
      (hh : h ∈ 𝒜 k) (hk : 0 < k)
      (hfg : f * g ∈ 𝒜 (d + e))
      (hfgh : (f * g) * h ∈ 𝒜 ((d + e) + k)),
      let r01 := chapter01_standard_chart_restriction_map 𝒜 hf hd hg he
      let r12 := chapter01_standard_chart_restriction_map 𝒜 hfg
        (Nat.add_pos_right d he) hh hk
      let r01' := chapter01ChartRingRestrictionMap
        (chapter01OrdinaryChartOpenRestriction 𝒜 f g)
      let r12' := chapter01ChartRingRestrictionMap
        (chapter01OrdinaryChartOpenRestriction 𝒜 (f * g) h)
      let m01 := chapter01ModuleAwayDegreeZeroRestrictionMap
        𝒜 (chapter01OrdinaryGradedComponents 𝒜)
          (chapter01OrdinaryGradedModuleData 𝒜) n f hf hd g hg he hfg
      let m12 := chapter01ModuleAwayDegreeZeroRestrictionMap
        𝒜 (chapter01OrdinaryGradedComponents 𝒜)
          (chapter01OrdinaryGradedModuleData 𝒜) n (f * g) hfg
            (Nat.add_pos_right d he) h hh hk hfgh
      let m01' := chapter01ChartModuleRestrictionMap (sheaf n)
        (chapter01OrdinaryChartOpenRestriction 𝒜 f g)
      let m12' := chapter01ChartModuleRestrictionMap (sheaf n)
        (chapter01OrdinaryChartOpenRestriction 𝒜 (f * g) h)
      Chapter01ChartModuleOverlapCompatible
        (chart n f hf hd)
        (chart n (f * g) hfg (Nat.add_pos_right d he))
        (chart n ((f * g) * h) hfgh (Nat.add_pos_right (d + e) hk))
        r01 r12 (r12.comp r01)
        r01' r12' (r12'.comp r01')
        m01 m12 (m12.comp m01)
        m01' m12' (m12'.comp m01')
  unit_iso : sheaf 0 ≅ SheafOfModules.unit (AlgebraicGeometry.«Proj» 𝒜).ringCatSheaf
  /-- Twists tensor canonically only after the grading is generated in degree one.
  Without that hypothesis, weighted gradings can have noninvertible `O(1)`. -/
  tensor_iso : ∀ (h : chapter01GeneratedInDegreeOne 𝒜) (m n : ℤ),
    chapter01SheafTensor (sheaf m) (sheaf n) ≅ sheaf (m + n)
  tensor_unit_left : ∀ (h : chapter01GeneratedInDegreeOne 𝒜) (n : ℤ),
    chapter01SheafTensorMap unit_iso.hom (𝟙 (sheaf n)) ≫
        (chapter01SheafTensorLeftUnitor (sheaf n)).hom =
      (tensor_iso h 0 n).hom ≫ eqToHom (by sorry : sheaf (0 + n) = sheaf n)
  tensor_unit_right : ∀ (h : chapter01GeneratedInDegreeOne 𝒜) (n : ℤ),
    chapter01SheafTensorMap (𝟙 (sheaf n)) unit_iso.hom ≫
        (chapter01SheafTensorRightUnitor (sheaf n)).hom =
      (tensor_iso h n 0).hom ≫ eqToHom (by sorry : sheaf (n + 0) = sheaf n)
  tensor_assoc : ∀ (h : chapter01GeneratedInDegreeOne 𝒜) (m n k : ℤ),
    chapter01SheafTensorMap (tensor_iso h m n).hom (𝟙 (sheaf k)) ≫
        (tensor_iso h (m + n) k).hom ≫
        eqToHom (by sorry : sheaf ((m + n) + k) = sheaf (m + (n + k))) =
      (chapter01SheafTensorAssociator (sheaf m) (sheaf n) (sheaf k)).hom ≫
        chapter01SheafTensorMap (𝟙 (sheaf m)) (tensor_iso h n k).hom ≫
        (tensor_iso h m (n + k)).hom
  dual_data : ∀ (n : ℤ) (hM : Chapter01IsLineBundle (sheaf n)),
    Chapter01SheafDualData (sheaf n) hM
  dual_iso : ∀ (h : chapter01GeneratedInDegreeOne 𝒜) (n : ℤ)
    (hM : Chapter01IsLineBundle (sheaf n)),
    (dual_data n hM).dual ≅ sheaf (-n)
  line_bundle_one :
    chapter01GeneratedInDegreeOne 𝒜 → Chapter01IsLineBundle (sheaf 1)

noncomputable def chapter01OrdinaryTwistingSheafFamily {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] :
    Chapter01OrdinaryTwistingSheafFamily 𝒜 := by
  sorry

structure Chapter01OrdinaryProjSheafification {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] (n : ℤ) where
  family : Chapter01OrdinaryTwistingSheafFamily 𝒜
  sheaf : (AlgebraicGeometry.«Proj» 𝒜).Modules
  sheaf_eq : sheaf = family.sheaf n
  sheaf_isQuasicoherent : sheaf.IsQuasicoherent

theorem chapter01_ordinary_proj_sheafification_exists
    {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] (n : ℤ) :
    Nonempty (Chapter01OrdinaryProjSheafification 𝒜 n) := by
  sorry

noncomputable def chapter01OrdinaryTwistingSheaf {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] (n : ℤ) :
    (AlgebraicGeometry.«Proj» 𝒜).Modules :=
  (chapter01OrdinaryTwistingSheafFamily 𝒜).sheaf n

noncomputable def chapter01RelativeChartOpenRestriction
    {S : Scheme.{u}} (𝒜 : Chapter01RelativeGradedAlgebra S)
    (P : Chapter01RelativeProj 𝒜) {U : S.Opens} (hU : IsAffineOpen U)
    {d e : ℕ} (f g : 𝒜.sections U)
    (hf : f ∈ 𝒜.grading U d) (hd : 0 < d)
    (hg : g ∈ 𝒜.grading U e) (he : 0 < e)
    (hfg : f * g ∈ 𝒜.grading U (d + e)) :
    P.standardOpen U hU (d + e) (f * g) hfg (Nat.add_pos_right d he) ⟶
      P.standardOpen U hU d f hf hd :=
  homOfLE (by
    rw [P.standardOpen_mul U hU d e f g hf hd hg he hfg]
    exact inf_le_left)

structure Chapter01RelativeTwistingSheafFamily {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) (P : Chapter01RelativeProj 𝒜) where
  sheaf : ℤ → P.scheme.Modules
  sheaf_isQuasicoherent : ∀ n, (sheaf n).IsQuasicoherent
  chart : ∀ (n : ℤ) (U : S.Opens) (hU : IsAffineOpen U) {d : ℕ}
      (f : 𝒜.sections U) (hf : f ∈ 𝒜.grading U d) (hd : 0 < d),
    Chapter01ChartModuleEquivalence
      (HomogeneousLocalization.Away (𝒜.grading U) f)
      ((P.scheme.ringCatSheaf.obj.obj
        (Opposite.op (P.standardOpen U hU d f hf hd))).carrier)
      (chapter01RelativeChartSections 𝒜 P n U hU f hf hd)
      ((((Scheme.Modules.toPresheafOfModules P.scheme).obj (sheaf n)).obj
        (Opposite.op (P.standardOpen U hU d f hf hd))).carrier)
  /-- The relative chart equivalences commute with restriction along every
  standard-open overlap. -/
  chart_restriction_compatibility :
    ∀ (n : ℤ) (U : S.Opens) (hU : IsAffineOpen U) {d e : ℕ}
      (f g : 𝒜.sections U)
      (hf : f ∈ 𝒜.grading U d) (hd : 0 < d)
      (hg : g ∈ 𝒜.grading U e) (he : 0 < e)
      (hfg : f * g ∈ 𝒜.grading U (d + e)),
      Chapter01ChartModuleRestrictionCompatible
        (chart n U hU f hf hd)
        (chart n U hU (f * g) hfg (Nat.add_pos_right d he))
        (chapter01_standard_chart_restriction_map (𝒜.grading U) hf hd hg he)
        (chapter01ChartRingRestrictionMap
          (chapter01RelativeChartOpenRestriction 𝒜 P hU f g hf hd hg he hfg))
        (chapter01ModuleAwayDegreeZeroRestrictionMap
          (𝒜.grading U)
            (chapter01RelativeGradedComponents 𝒜 U)
            (chapter01RelativeGradedModuleData 𝒜 U) n f hf hd g hg he hfg)
        (chapter01ChartModuleRestrictionMap (sheaf n)
          (chapter01RelativeChartOpenRestriction 𝒜 P hU f g hf hd hg he hfg))
  /-- The relative restriction data satisfy the cocycle identity on triple
  standard-open overlaps. -/
  chart_overlap_compatibility :
    ∀ (n : ℤ) (U : S.Opens) (hU : IsAffineOpen U) {d e k : ℕ}
      (f g h : 𝒜.sections U)
      (hf : f ∈ 𝒜.grading U d) (hd : 0 < d)
      (hg : g ∈ 𝒜.grading U e) (he : 0 < e)
      (hh : h ∈ 𝒜.grading U k) (hk : 0 < k)
      (hfg : f * g ∈ 𝒜.grading U (d + e))
      (hfgh : (f * g) * h ∈ 𝒜.grading U ((d + e) + k)),
      let r01 := chapter01_standard_chart_restriction_map
        (𝒜.grading U) hf hd hg he
      let r12 := chapter01_standard_chart_restriction_map
        (𝒜.grading U) hfg (Nat.add_pos_right d he) hh hk
      let r01' := chapter01ChartRingRestrictionMap
        (chapter01RelativeChartOpenRestriction 𝒜 P hU f g hf hd hg he hfg)
      let r12' := chapter01ChartRingRestrictionMap
        (chapter01RelativeChartOpenRestriction 𝒜 P hU (f * g) h hfg
          (Nat.add_pos_right d he) hh hk hfgh)
      let m01 := chapter01ModuleAwayDegreeZeroRestrictionMap
        (𝒜.grading U)
          (chapter01RelativeGradedComponents 𝒜 U)
          (chapter01RelativeGradedModuleData 𝒜 U) n f hf hd g hg he hfg
      let m12 := chapter01ModuleAwayDegreeZeroRestrictionMap
        (𝒜.grading U)
          (chapter01RelativeGradedComponents 𝒜 U)
          (chapter01RelativeGradedModuleData 𝒜 U) n (f * g) hfg
            (Nat.add_pos_right d he) h hh hk hfgh
      let m01' := chapter01ChartModuleRestrictionMap (sheaf n)
        (chapter01RelativeChartOpenRestriction 𝒜 P hU f g hf hd hg he hfg)
      let m12' := chapter01ChartModuleRestrictionMap (sheaf n)
        (chapter01RelativeChartOpenRestriction 𝒜 P hU (f * g) h hfg
          (Nat.add_pos_right d he) hh hk hfgh)
      Chapter01ChartModuleOverlapCompatible
        (chart n U hU f hf hd)
        (chart n U hU (f * g) hfg (Nat.add_pos_right d he))
        (chart n U hU ((f * g) * h) hfgh
          (Nat.add_pos_right (d + e) hk))
        r01 r12 (r12.comp r01)
        r01' r12' (r12'.comp r01')
        m01 m12 (m12.comp m01)
        m01' m12' (m12'.comp m01')
  unit_iso : sheaf 0 ≅ SheafOfModules.unit P.scheme.ringCatSheaf
  /-- As in the ordinary case, tensor and dual identifications require
  degree-one generation. -/
  tensor_iso : ∀ (h : chapter01RelativeGeneratedInDegreeOneByFiniteType 𝒜)
    (m n : ℤ),
    chapter01SheafTensor (sheaf m) (sheaf n) ≅ sheaf (m + n)
  tensor_unit_left : ∀ (h : chapter01RelativeGeneratedInDegreeOneByFiniteType 𝒜)
    (n : ℤ),
    chapter01SheafTensorMap unit_iso.hom (𝟙 (sheaf n)) ≫
        (chapter01SheafTensorLeftUnitor (sheaf n)).hom =
      (tensor_iso h 0 n).hom ≫ eqToHom (by sorry : sheaf (0 + n) = sheaf n)
  tensor_unit_right : ∀ (h : chapter01RelativeGeneratedInDegreeOneByFiniteType 𝒜)
    (n : ℤ),
    chapter01SheafTensorMap (𝟙 (sheaf n)) unit_iso.hom ≫
        (chapter01SheafTensorRightUnitor (sheaf n)).hom =
      (tensor_iso h n 0).hom ≫ eqToHom (by sorry : sheaf (n + 0) = sheaf n)
  tensor_assoc : ∀ (h : chapter01RelativeGeneratedInDegreeOneByFiniteType 𝒜)
    (m n k : ℤ),
    chapter01SheafTensorMap (tensor_iso h m n).hom (𝟙 (sheaf k)) ≫
        (tensor_iso h (m + n) k).hom ≫
        eqToHom (by sorry : sheaf ((m + n) + k) = sheaf (m + (n + k))) =
      (chapter01SheafTensorAssociator (sheaf m) (sheaf n) (sheaf k)).hom ≫
        chapter01SheafTensorMap (𝟙 (sheaf m)) (tensor_iso h n k).hom ≫
        (tensor_iso h m (n + k)).hom
  dual_data : ∀ (n : ℤ) (hM : Chapter01IsLineBundle (sheaf n)),
    Chapter01SheafDualData (sheaf n) hM
  dual_iso : ∀ (h : chapter01RelativeGeneratedInDegreeOneByFiniteType 𝒜)
    (n : ℤ) (hM : Chapter01IsLineBundle (sheaf n)),
    (dual_data n hM).dual ≅ sheaf (-n)
  line_bundle_one :
    chapter01RelativeGeneratedInDegreeOneByFiniteType 𝒜 →
      Chapter01IsLineBundle (sheaf 1)

noncomputable def chapter01RelativeTwistingSheafFamily {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) (P : Chapter01RelativeProj 𝒜) :
    Chapter01RelativeTwistingSheafFamily 𝒜 P := by
  sorry

structure Chapter01RelativeProjSheafification {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S)
    (P : Chapter01RelativeProj 𝒜) (n : ℤ) where
  family : Chapter01RelativeTwistingSheafFamily 𝒜 P
  sheaf : P.scheme.Modules
  sheaf_eq : sheaf = family.sheaf n
  sheaf_isQuasicoherent : sheaf.IsQuasicoherent

theorem chapter01_relative_proj_sheafification_exists {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S)
    (P : Chapter01RelativeProj 𝒜) (n : ℤ) :
    Nonempty (Chapter01RelativeProjSheafification 𝒜 P n) := by
  sorry

noncomputable def chapter01RelativeTwistingSheaf {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S)
    (P : Chapter01RelativeProj 𝒜) (n : ℤ) : P.scheme.Modules :=
  (chapter01RelativeTwistingSheafFamily 𝒜 P).sheaf n

noncomputable def chapter01OrdinaryStructureTwist {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] :
    (AlgebraicGeometry.«Proj» 𝒜).Modules :=
  chapter01OrdinaryTwistingSheaf 𝒜 0

theorem chapter01_ordinary_structure_twist_iso {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] :
    Nonempty (chapter01OrdinaryStructureTwist 𝒜 ≅
      SheafOfModules.unit (AlgebraicGeometry.«Proj» 𝒜).ringCatSheaf) := by
  sorry

theorem chapter01_ordinary_twist_tensor_iso {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] (m n : ℤ) :
    chapter01GeneratedInDegreeOne 𝒜 →
    Nonempty (chapter01SheafTensor (chapter01OrdinaryTwistingSheaf 𝒜 m)
        (chapter01OrdinaryTwistingSheaf 𝒜 n) ≅
      chapter01OrdinaryTwistingSheaf 𝒜 (m + n)) := by
  sorry

theorem chapter01_ordinary_twist_dual_iso {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] (n : ℤ) :
    chapter01GeneratedInDegreeOne 𝒜 →
    ∀ hM : Chapter01IsLineBundle (chapter01OrdinaryTwistingSheaf 𝒜 n),
      Nonempty (((chapter01OrdinaryTwistingSheafFamily 𝒜).dual_data n hM).dual ≅
        chapter01OrdinaryTwistingSheaf 𝒜 (-n)) := by
  sorry

theorem chapter01_relative_twist_tensor_iso {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) (P : Chapter01RelativeProj 𝒜)
    (m n : ℤ) :
    chapter01RelativeGeneratedInDegreeOneByFiniteType 𝒜 →
    Nonempty (chapter01SheafTensor (chapter01RelativeTwistingSheaf 𝒜 P m)
        (chapter01RelativeTwistingSheaf 𝒜 P n) ≅
      chapter01RelativeTwistingSheaf 𝒜 P (m + n)) := by
  sorry

theorem chapter01_relative_twist_dual_iso {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) (P : Chapter01RelativeProj 𝒜)
    (n : ℤ) :
    chapter01RelativeGeneratedInDegreeOneByFiniteType 𝒜 →
    ∀ hM : Chapter01IsLineBundle (chapter01RelativeTwistingSheaf 𝒜 P n),
      Nonempty (((chapter01RelativeTwistingSheafFamily 𝒜 P).dual_data n hM).dual ≅
        chapter01RelativeTwistingSheaf 𝒜 P (-n)) := by
  sorry

theorem chapter01_ordinary_twist_one_is_line_bundle {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    (h : chapter01GeneratedInDegreeOne 𝒜) :
    Chapter01IsLineBundle (chapter01OrdinaryTwistingSheaf 𝒜 1) := by
  sorry

def chapter01GeneratedInDegreesDividing {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] (d : ℕ) : Prop :=
  Algebra.adjoin (𝒜 0)
      {x : A | ∃ n, 0 < n ∧ n ∣ d ∧ x ∈ 𝒜 n} = ⊤

def chapter01IsLineBundleOn {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) : Prop :=
  Chapter01IsLineBundle ((Scheme.Modules.restrictFunctor U.ι).obj M)

theorem chapter01_degree_d_twist_is_line_bundle_on_standard_chart
    {A : Type*} [CommRing A] (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    {d : ℕ} {f : A} (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    chapter01IsLineBundleOn (chapter01OrdinaryTwistingSheaf 𝒜 (d : ℤ))
      (chapter01SchemeStandardOpen 𝒜 f) := by
  sorry

theorem chapter01_degree_d_twist_is_line_bundle_of_generated_in_degrees_dividing
    {A : Type*} [CommRing A] (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    {d : ℕ} (hd : 0 < d)
    (hgen : chapter01GeneratedInDegreesDividing 𝒜 d) :
    Chapter01IsLineBundle (chapter01OrdinaryTwistingSheaf 𝒜 (d : ℤ)) := by
  sorry

def chapter01OOneMayFailToBeLineBundle
    {A : Type*} [CommRing A] (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] : Prop :=
  ¬ Chapter01IsLineBundle (chapter01OrdinaryTwistingSheaf 𝒜 1)

def chapter01PolynomialOOneMayFailToBeLineBundle
    {k : Type*} [CommRing k] {r : ℕ} {w : Fin (r + 1) → ℕ}
    (G : Chapter01PolynomialGradingData k r w) : Prop := by
  letI := G.graded
  exact chapter01OOneMayFailToBeLineBundle G.grading

theorem chapter01_weighted_grading_OOne_warning
    {k : Type*} [Field k]
    (G : Chapter01PolynomialGradingData k 0 (fun _ => 2)) :
    chapter01PolynomialOOneMayFailToBeLineBundle G := by
  sorry

def chapter01TwistedGlobalSectionsMap
    {M Γ : ℤ → Type*} [∀ n, AddCommGroup (M n)] [∀ n, AddCommGroup (Γ n)]
    (φ : ∀ n, M n →+ Γ n) :
    (⨁ n, M n) →+ (⨁ n, Γ n) :=
  DirectSum.toAddMonoid (fun n => (DirectSum.of (fun n => Γ n) n).comp (φ n))

theorem chapter01_twisted_global_sections_map_component
    {M Γ : ℤ → Type*} [∀ n, AddCommGroup (M n)] [∀ n, AddCommGroup (Γ n)]
    (φ : ∀ n, M n →+ Γ n) (n : ℤ) (x : M n) :
    chapter01TwistedGlobalSectionsMap φ (DirectSum.of (fun n => M n) n x) =
      DirectSum.of (fun n => Γ n) n (φ n x) := by
  simp [chapter01TwistedGlobalSectionsMap]

def chapter01TwistedGlobalSectionsMapFromDecomposition
    {M : Type*} [AddCommGroup M] (𝓜 : ℤ → Submodule ℤ M)
    [DirectSum.Decomposition 𝓜]
    {Γ : ℤ → Type*} [∀ n, AddCommGroup (Γ n)]
    (φ : ∀ n, 𝓜 n →+ Γ n) : M →+ (⨁ n, Γ n) :=
  (chapter01TwistedGlobalSectionsMap φ).comp (DirectSum.decomposeAddEquiv 𝓜).toAddHom

noncomputable def chapter01GradedModuleTwistedGlobalSectionsMap
    {A M : Type*} [CommRing A] [AddCommGroup M]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    (𝓜 : ℤ → Submodule ℤ M) [Module A M]
    (G : Chapter01GradedModule 𝒜 𝓜) :
    M →+
      (⨁ n : ℤ,
        (((Scheme.Modules.presheaf (chapter01GradedModuleProjSheaf 𝒜 𝓜 G n)).obj
          (Opposite.op ⊤)).carrier)) := by
  letI := G.decomposition
  exact chapter01TwistedGlobalSectionsMapFromDecomposition 𝓜
    (fun n => chapter01GradedModuleProjGlobalSectionsMap 𝒜 𝓜 G n)

/- The source's eventual-isomorphism claim applies after imposing the usual
noetherian/standard-graded and finite-generation hypotheses.  These predicates
keep that eventual property separate from the generic componentwise map. -/
def Chapter01EventuallyAnIsomorphism
    {M Γ : ℤ → Type*} [∀ n, AddCommGroup (M n)] [∀ n, AddCommGroup (Γ n)]
    (φ : ∀ n, M n →+ Γ n) : Prop :=
  ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → Function.Bijective (φ n)

def Chapter01SmallDegreeSaturationFailure
    {M Γ : ℤ → Type*} [∀ n, AddCommGroup (M n)] [∀ n, AddCommGroup (Γ n)]
    (φ : ∀ n, M n →+ Γ n) : Prop :=
  ∃ n₀ : ℤ,
    (∀ n, n₀ ≤ n → Function.Bijective (φ n)) ∧
      ∃ n, n < n₀ ∧ ¬ Function.Bijective (φ n)

theorem chapter01_graded_module_global_sections_eventually_isomorphism
    {A M : Type*} [CommRing A] [AddCommGroup M]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    (𝓜 : ℤ → Submodule ℤ M) [Module A M]
    (G : Chapter01GradedModule 𝒜 𝓜)
    [IsNoetherianRing A] [Module.Finite A M]
    (h : chapter01GeneratedInDegreeOne 𝒜) :
    Chapter01EventuallyAnIsomorphism
      (fun n => chapter01GradedModuleProjGlobalSectionsMap 𝒜 𝓜 G n) := by
  sorry

/-! ### 1.6 Veronese algebras and presentations -/

instance chapter01VeroneseGradedMonoid {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] (d : ℕ) :
    SetLike.GradedMonoid (fun n : ℕ => 𝒜 (n * d)) where
  one_mem := by
    simpa using (SetLike.one_mem_graded 𝒜)
  mul_mem := by
    intro i j x y hx hy
    simpa [Nat.add_mul] using (SetLike.mul_mem_graded hx hy)

abbrev chapter01Veronese {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] (d : ℕ) :=
  ⨁ n : ℕ, 𝒜 (n * d)

def chapter01VeroneseInclusion {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] (d : ℕ) :
    chapter01Veronese 𝒜 d →+* A :=
  DirectSum.coeRingHom (fun n : ℕ => 𝒜 (n * d))

def chapter01VeroneseComponent {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] (d n : ℕ)
    (x : 𝒜 (n * d)) : chapter01Veronese 𝒜 d :=
  DirectSum.of (fun n : ℕ => 𝒜 (n * d)) n x

@[simp] theorem chapter01_veronese_inclusion_component {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] (d n : ℕ)
    (x : 𝒜 (n * d)) :
    chapter01VeroneseInclusion 𝒜 d (chapter01VeroneseComponent 𝒜 d n x) = x := by
  exact DirectSum.coeRingHom_of _ _ _

theorem chapter01_veronese_inclusion_injective {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] {d : ℕ} (hd : 0 < d) :
    Function.Injective (chapter01VeroneseInclusion 𝒜 d) := by
  sorry

structure Chapter01VeroneseGradingData {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] (d : ℕ) where
  grading : ℕ → Submodule ℤ (chapter01Veronese 𝒜 d)
  graded : GradedAlgebra grading
  component_spec :
    ∀ n (x : chapter01Veronese 𝒜 d),
      x ∈ grading n ↔
        ∃ y : 𝒜 (n * d), chapter01VeroneseComponent 𝒜 d n y = x

def chapter01VeroneseGeneratedInDegreeOne {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] (d : ℕ) : Prop :=
  ∀ n (x : A), x ∈ 𝒜 (n * d) →
    x ∈ Algebra.adjoin (𝒜 0) (Set.range (fun y : 𝒜 d => (y : A)))

noncomputable def chapter01VeroneseProj {A : Type*} [CommRing A]
    {𝒜 : ℕ → Submodule ℤ A} [GradedAlgebra 𝒜] {d : ℕ}
    (V : Chapter01VeroneseGradingData 𝒜 d) : Scheme := by
  letI := V.graded
  exact AlgebraicGeometry.«Proj» V.grading

noncomputable def chapter01VeroneseTwistingSheaf {A : Type*} [CommRing A]
    {𝒜 : ℕ → Submodule ℤ A} [GradedAlgebra 𝒜] {d : ℕ}
    (V : Chapter01VeroneseGradingData 𝒜 d) (n : ℤ) :
    (chapter01VeroneseProj V).Modules := by
  letI := V.graded
  exact chapter01OrdinaryTwistingSheaf V.grading n

/- The Veronese comparison is available for every positive degree.  Degree-one
generation is used separately when one wants the new degree-one twist to be an
invertible sheaf.  The twist comparison is part of the chosen isomorphism,
since an arbitrary witness of scheme isomorphism need not preserve twists. -/
theorem chapter01_proj_veronese_iso_and_twist {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] {d : ℕ} (hd : 0 < d)
    (V : Chapter01VeroneseGradingData 𝒜 d) :
    ∃ e : AlgebraicGeometry.«Proj» 𝒜 ≅ chapter01VeroneseProj V,
      Nonempty ((Scheme.Modules.pullback e.hom).obj
        (chapter01VeroneseTwistingSheaf V 1) ≅
        chapter01OrdinaryTwistingSheaf 𝒜 (d : ℤ)) := by
  sorry

theorem chapter01_proj_veronese_iso {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] {d : ℕ} (hd : 0 < d)
    (V : Chapter01VeroneseGradingData 𝒜 d) :
    Nonempty (AlgebraicGeometry.«Proj» 𝒜 ≅ chapter01VeroneseProj V) := by
  exact ⟨(chapter01_proj_veronese_iso_and_twist 𝒜 hd V).choose⟩

noncomputable def chapter01ProjVeroneseIso {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] {d : ℕ} (hd : 0 < d)
    (V : Chapter01VeroneseGradingData 𝒜 d) :
    AlgebraicGeometry.«Proj» 𝒜 ≅ chapter01VeroneseProj V :=
  (chapter01_proj_veronese_iso_and_twist 𝒜 hd V).choose

theorem chapter01_veronese_twist_correspondence {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] {d : ℕ} (hd : 0 < d)
    (V : Chapter01VeroneseGradingData 𝒜 d) :
      Nonempty ((Scheme.Modules.pullback (chapter01ProjVeroneseIso 𝒜 hd V).hom).obj
        (chapter01VeroneseTwistingSheaf V 1) ≅
      chapter01OrdinaryTwistingSheaf 𝒜 (d : ℤ)) := by
  simpa [chapter01ProjVeroneseIso] using
    (chapter01_proj_veronese_iso_and_twist 𝒜 hd V).choose_spec

def chapter01FinitelyGeneratedGrading {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] : Prop :=
  ∃ r : ℕ, ∃ x : Fin r → A,
    (∀ i, ∃ n, 0 < n ∧ x i ∈ 𝒜 n) ∧
      Algebra.adjoin (𝒜 0) (Set.range x) = ⊤

theorem chapter01_veronese_eventually_generated_in_degree_one
    {A : Type*} [CommRing A] (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    (h : chapter01FinitelyGeneratedGrading 𝒜) :
    ∃ d₀ : ℕ, 0 < d₀ ∧
      ∀ d, d₀ ∣ d → chapter01VeroneseGeneratedInDegreeOne 𝒜 d := by
  sorry

def chapter01PolynomialEvaluation {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] {r : ℕ}
    (x : Fin (r + 1) → A) :
    MvPolynomial (Fin (r + 1)) (𝒜 0) →ₐ[𝒜 0] A :=
  MvPolynomial.aeval x

structure Chapter01DegreeOnePolynomialPresentation
    {A : Type*} [CommRing A] (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    {r : ℕ} (G : Chapter01PolynomialGradingData (𝒜 0) r (fun _ => 1)) where
  coordinates : Fin (r + 1) → A
  coordinate_degree_one : ∀ i, coordinates i ∈ 𝒜 1
  evaluation_surjective :
    Function.Surjective (chapter01PolynomialEvaluation 𝒜 coordinates)
  evaluation_is_graded :
    ∀ n p, p ∈ G.grading n → chapter01PolynomialEvaluation 𝒜 coordinates p ∈ 𝒜 n

theorem chapter01_degree_one_generators_give_polynomial_presentation
    {A : Type*} [CommRing A] (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    {r : ℕ} (x : Fin (r + 1) → A)
    (hx : ∀ i, x i ∈ 𝒜 1)
    (hgen : Algebra.adjoin (𝒜 0) (Set.range x) = ⊤)
    (G : Chapter01PolynomialGradingData (𝒜 0) r (fun _ => 1)) :
    Nonempty (Chapter01DegreeOnePolynomialPresentation 𝒜 G) := by
  sorry

instance chapter01PolynomialGradingDataGraded
    {k : Type*} [CommRing k] {r : ℕ} {w : Fin (r + 1) → ℕ}
    (G : Chapter01PolynomialGradingData k r w) : GradedAlgebra G.grading :=
  G.graded

def chapter01HomogeneousPresentationEquations
    {A : Type*} [CommRing A] (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    {r : ℕ} {G : Chapter01PolynomialGradingData (𝒜 0) r (fun _ => 1)}
  (P : Chapter01DegreeOnePolynomialPresentation 𝒜 G) :
    Ideal (MvPolynomial (Fin (r + 1)) (𝒜 0)) :=
  RingHom.ker (chapter01PolynomialEvaluation 𝒜 P.coordinates).toRingHom

theorem chapter01_presentation_equations_homogeneous
    {A : Type*} [CommRing A] (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    {r : ℕ} {G : Chapter01PolynomialGradingData (𝒜 0) r (fun _ => 1)}
    (P : Chapter01DegreeOnePolynomialPresentation 𝒜 G) :
    Ideal.IsHomogeneous G.grading
      (chapter01HomogeneousPresentationEquations 𝒜 P) := by
  sorry

/-! The closed immersion is induced by the homogeneous kernel, rather than
merely being some unrelated closed immersion into the same projective space. -/
structure Chapter01ProjectivePresentationClosedImmersionData
    {A : Type*} [CommRing A] (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    {r : ℕ} {G : Chapter01PolynomialGradingData (𝒜 0) r (fun _ => 1)}
    (P : Chapter01DegreeOnePolynomialPresentation 𝒜 G) where
  ideal : HomogeneousIdeal G.grading
  ideal_eq_equations :
    ideal.toIdeal = chapter01HomogeneousPresentationEquations 𝒜 P
  identification :
    AlgebraicGeometry.«Proj» 𝒜 ≅
      (Chapter01ProjClosedSubschemeInterface.scheme
        (chapter01ProjClosedSubschemeInterface (𝒜 := G.grading)) ideal)
  embedding : AlgebraicGeometry.«Proj» 𝒜 ⟶ chapter01PolynomialProj G
  embedding_closed : IsClosedImmersion embedding
  /-- The presentation is an embedding over the degree-zero coefficient ring. -/
  embedding_over :
    embedding ≫ chapter01ProjToBase G.grading
        (algebraMap (𝒜 0) (MvPolynomial (Fin (r + 1)) (𝒜 0))) =
      chapter01ProjToDegreeZero 𝒜
  embedding_factorization :
    identification.hom ≫
        (Chapter01ProjClosedSubschemeInterface.inclusion
          (chapter01ProjClosedSubschemeInterface (𝒜 := G.grading)) ideal) =
      embedding

theorem chapter01_projective_presentation_closed_immersion_data
    {A : Type*} [CommRing A] (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    {r : ℕ} {G : Chapter01PolynomialGradingData (𝒜 0) r (fun _ => 1)}
    (P : Chapter01DegreeOnePolynomialPresentation 𝒜 G) :
    Nonempty (Chapter01ProjectivePresentationClosedImmersionData 𝒜 P) := by
  sorry

theorem chapter01_projective_presentation_closed_immersion
    {A : Type*} [CommRing A] (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    {r : ℕ} {G : Chapter01PolynomialGradingData (𝒜 0) r (fun _ => 1)}
    (P : Chapter01DegreeOnePolynomialPresentation 𝒜 G) :
    ∃ ι : AlgebraicGeometry.«Proj» 𝒜 ⟶ chapter01PolynomialProj G,
      IsClosedImmersion ι ∧
        ι ≫ chapter01ProjToBase G.grading
            (algebraMap (𝒜 0) (MvPolynomial (Fin (r + 1)) (𝒜 0))) =
          chapter01ProjToDegreeZero 𝒜 := by
  rcases chapter01_projective_presentation_closed_immersion_data 𝒜 P with ⟨D⟩
  exact ⟨D.embedding, D.embedding_closed, D.embedding_over⟩

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter01
