import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.GradedAlgebra.FiniteType
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.GradedAlgebra.TensorProduct
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Book 8, Chapter 1: Projective geometry over a base

This file records the book-facing interfaces for relative Proj.  The ordinary
graded-ring statements are thin wrappers around Mathlib.  Relative Proj and
twisting sheaves are marked local dependency guesses because the pinned
Mathlib tree does not yet contain their sheaf-valued constructions.
-/

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter01

universe u

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

/- LOCAL_DEPENDENCY_GUESS: the pinned sheaf-module API has no tensor-product and
dual operations for arbitrary scheme modules.  These are the book-facing line
bundle operations and can be replaced by the canonical tensor construction when
the preceding sheaf-algebra development is merged. -/
noncomputable def chapter01LineBundleTensorPower {X : Scheme.{u}}
    (L : Chapter01LineBundle X) (n : ℕ) : Chapter01LineBundle X := by
  sorry

noncomputable def chapter01LineBundleDualPower {X : Scheme.{u}}
    (L : Chapter01LineBundle X) (n : ℕ) : Chapter01LineBundle X := by
  sorry

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

theorem chapter01_standard_chart_restriction_map {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    {m n : ℕ} {f g : A} (hf : f ∈ 𝒜 m) (hm : 0 < m)
    (hg : g ∈ 𝒜 n) (hn : 0 < n) :
    Nonempty (chapter01StandardChartRing 𝒜 f →+*
      chapter01StandardChartRing 𝒜 (f * g)) := by
  exact ⟨HomogeneousLocalization.awayMap 𝒜 hg rfl⟩

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
      ∀ m ∈ p.support, (∑ i, w i * m i) = n
  variable_degree : ∀ i, MvPolynomial.X i ∈ grading (w i)

noncomputable def chapter01PolynomialProj
    {k : Type*} [CommRing k] {r : ℕ} {w : Fin (r + 1) → ℕ}
    (G : Chapter01PolynomialGradingData k r w) : Scheme := by
  letI := G.graded
  exact AlgebraicGeometry.«Proj» G.grading

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

/- LOCAL_DEPENDENCY_GUESS: Mathlib has the ordinary Proj of an internally
graded ring, but not a quasi-coherent graded `𝒪_S`-algebra or its relative Proj.
This structure records the section rings, restriction maps, degree pieces, and
the degree-zero algebra maps needed by the book construction. -/
structure Chapter01RelativeGradedAlgebra (S : Scheme.{u}) where
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
  component : ℕ → S.Modules
  component_isQuasicoherent : ∀ n, (component n).IsQuasicoherent
  component_sections : ∀ (n : ℕ) (U : S.Opens),
    Nonempty (AddCommGrpCat.of (grading U n) ≅
      (Scheme.Modules.presheaf (component n)).obj (Opposite.op U))

instance chapter01RelativeGradedAlgebraGraded
    {S : Scheme.{u}} (𝒜 : Chapter01RelativeGradedAlgebra S) (U : S.Opens) :
    GradedAlgebra (𝒜.grading U) :=
  𝒜.graded U

abbrev chapter01RelativeSection {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) (U : S.Opens) :=
  𝒜.sections U

def chapter01RelativeDegreeZeroIsStructureSheaf {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) : Prop :=
  ∀ U, Nonempty (CommRingCat.of (𝒜.grading U 0) ≅
    S.presheaf.obj (Opposite.op U))

theorem chapter01_relative_multiplication_preserves_degree {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S)
    {U : S.Opens} {m n : ℕ} {x y : 𝒜.sections U}
    (hx : x ∈ 𝒜.grading U m) (hy : y ∈ 𝒜.grading U n) :
    x * y ∈ 𝒜.grading U (m + n) := by
  sorry

noncomputable def chapter01RelativeDegreeZeroLocalization {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) (U : S.Opens)
    {d : ℕ} (f : 𝒜.sections U) (hf : f ∈ 𝒜.grading U d) (hd : 0 < d) : CommRingCat.{u} := by
  sorry

structure Chapter01RelativeProj {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) where
  scheme : Scheme.{u}
  projection : scheme ⟶ S
  standardOpen : ∀ (U : S.Opens) (d : ℕ) (f : 𝒜.sections U),
    f ∈ 𝒜.grading U d → 0 < d → scheme.Opens
  standardOpen_over :
    ∀ (U : S.Opens) (d : ℕ) (f : 𝒜.sections U)
      (hf : f ∈ 𝒜.grading U d) (hd : 0 < d),
      standardOpen U d f hf hd ≤ projection ⁻¹ᵁ U
  standardOpen_cover :
    (⨆ (U : S.Opens) (d : ℕ) (f : 𝒜.sections U)
        (hf : f ∈ 𝒜.grading U d) (hd : 0 < d),
      standardOpen U d f hf hd) = ⊤
  standardOpen_mul :
    ∀ (U : S.Opens) (m n : ℕ) (f g : 𝒜.sections U)
      (hf : f ∈ 𝒜.grading U m) (hm : 0 < m)
      (hg : g ∈ 𝒜.grading U n) (hn : 0 < n)
      (hfg : f * g ∈ 𝒜.grading U (m + n)),
      standardOpen U (m + n) (f * g) hfg (Nat.add_pos_right m hn) =
        standardOpen U m f hf hm ⊓ standardOpen U n g hg hn
  standardOpen_chart :
    ∀ (U : S.Opens) (d : ℕ) (f : 𝒜.sections U)
      (hf : f ∈ 𝒜.grading U d) (hd : 0 < d),
      (standardOpen U d f hf hd).toScheme ≅
        AlgebraicGeometry.Spec
          (chapter01RelativeDegreeZeroLocalization 𝒜 U f hf hd)

/- LOCAL_DEPENDENCY_GUESS: this is the relative gluing theorem. -/
theorem chapter01_relative_proj_exists {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) :
    Nonempty (Chapter01RelativeProj 𝒜) := by
  sorry

noncomputable def chapter01RelativeProj {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) : Chapter01RelativeProj 𝒜 :=
  Classical.choice (chapter01_relative_proj_exists 𝒜)

theorem chapter01_relative_standard_open_inter {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) (P : Chapter01RelativeProj 𝒜)
    {U : S.Opens} {m n : ℕ} {f g : 𝒜.sections U}
    (hf : f ∈ 𝒜.grading U m) (hm : 0 < m)
    (hg : g ∈ 𝒜.grading U n) (hn : 0 < n)
    (hfg : f * g ∈ 𝒜.grading U (m + n)) :
    P.standardOpen U (m + n) (f * g) hfg (Nat.add_pos_right m hn) =
      P.standardOpen U m f hf hm ⊓ P.standardOpen U n g hg hn := by
  exact P.standardOpen_mul U m n f g hf hm hg hn hfg

def chapter01RelativeFinitePositiveGeneration {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) : Prop :=
  ∃ r : ℕ, ∃ x : Fin r → 𝒜.sections ⊤,
    (∀ i, ∃ n, 0 < n ∧ x i ∈ 𝒜.grading ⊤ n) ∧
      Algebra.adjoin (𝒜.grading ⊤ 0) (Set.range x) = ⊤

theorem chapter01_relative_proj_locally_of_finite_type {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S)
    (h : chapter01RelativeFinitePositiveGeneration 𝒜) :
    LocallyOfFiniteType (chapter01RelativeProj 𝒜).projection := by
  sorry

def chapter01RelativeGeneratedInDegreeOneByFiniteType {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) : Prop :=
  ∃ r : ℕ, ∃ x : Fin (r + 1) → 𝒜.sections ⊤,
    (∀ i, x i ∈ 𝒜.grading ⊤ 1) ∧
      Algebra.adjoin (𝒜.grading ⊤ 0) (Set.range x) = ⊤

/- LOCAL_DEPENDENCY_GUESS: this is the finite projective-space target used by
the relative degree-one embedding theorem. -/
noncomputable def chapter01RelativeProjectiveSpace (S : Scheme.{u}) (r : ℕ) : Scheme.{u} := by
  sorry

noncomputable def chapter01RelativeProjectiveSpaceProjection
    (S : Scheme.{u}) (r : ℕ) : chapter01RelativeProjectiveSpace S r ⟶ S := by
  sorry

theorem chapter01_relative_degree_one_closed_immersion
    {S : Scheme.{u}} (𝒜 : Chapter01RelativeGradedAlgebra S)
    (h : chapter01RelativeGeneratedInDegreeOneByFiniteType 𝒜) :
    ∃ (r : ℕ) (ι : (chapter01RelativeProj 𝒜).scheme ⟶
      chapter01RelativeProjectiveSpace S r),
      IsClosedImmersion ι ∧
        ι ≫ chapter01RelativeProjectiveSpaceProjection S r =
          (chapter01RelativeProj 𝒜).projection := by
  sorry

structure Chapter01RelativeGradedIdeal {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) where
  carrier : ∀ U : S.Opens, Ideal (𝒜.sections U)
  homogeneous : ∀ U, (carrier U).IsHomogeneous (𝒜.grading U)
  restriction_mem :
    ∀ {U V : S.Opens} (i : U ⟶ V) (x : 𝒜.sections V),
      x ∈ carrier V → 𝒜.restriction i x ∈ carrier U

noncomputable def chapter01RelativeQuotient {S : Scheme.{u}}
    {𝒜 : Chapter01RelativeGradedAlgebra S}
    (I : Chapter01RelativeGradedIdeal 𝒜) : Chapter01RelativeGradedAlgebra S := by
  sorry

theorem chapter01_relative_ideal_closed_immersion {S : Scheme.{u}}
    {𝒜 : Chapter01RelativeGradedAlgebra S}
    (I : Chapter01RelativeGradedIdeal 𝒜) :
    ∃ (Q : Chapter01RelativeProj (chapter01RelativeQuotient I))
      (ι : Q.scheme ⟶ (chapter01RelativeProj 𝒜).scheme),
      IsClosedImmersion ι ∧
        ι ≫ (chapter01RelativeProj 𝒜).projection = Q.projection := by
  sorry

def chapter01Saturation {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    (I : HomogeneousIdeal 𝒜) : HomogeneousIdeal 𝒜 := by
  sorry

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

/- LOCAL_DEPENDENCY_GUESS: the canonical relative/ordinary Proj quotient
construction should eventually supply this closed-subscheme interface.  The
point-locus field is enough for the set-theoretic saturation statement above,
but not for equality of scheme structures in the presence of nilpotents.
-/
structure Chapter01ProjClosedSubschemeInterface {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] where
  scheme : HomogeneousIdeal 𝒜 → Scheme
  inclusion : ∀ I, scheme I ⟶ AlgebraicGeometry.«Proj» 𝒜
  inclusion_closed : ∀ I, IsClosedImmersion (inclusion I)
  point_locus : ∀ I (x : ProjectiveSpectrum 𝒜),
    x ∈ Set.range (inclusion I) ↔ I ≤ x.asHomogeneousIdeal

def Chapter01SameProjClosedSubscheme {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    (C : Chapter01ProjClosedSubschemeInterface 𝒜)
    (I J : HomogeneousIdeal 𝒜) : Prop :=
  ∃ e : C.scheme I ≅ C.scheme J, e.hom ≫ C.inclusion J = C.inclusion I

/-! ### 1.4 Standard opens and base change -/

/- LOCAL_DEPENDENCY_GUESS: degreewise pullback of a relative graded algebra is
represented by this book-facing operation until sheaf-valued graded algebras are
available in the dependency graph. -/
noncomputable def chapter01RelativePullback {S T : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) (g : T ⟶ S) :
    Chapter01RelativeGradedAlgebra T := by
  sorry

def chapter01RelativeProjBaseChange {S T : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) (g : T ⟶ S) : Scheme.{u} :=
  Limits.pullback (chapter01RelativeProj 𝒜).projection g

theorem chapter01_relative_proj_base_change {S T : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) (g : T ⟶ S) :
    ∃ (Q : Chapter01RelativeProj (chapter01RelativePullback 𝒜 g))
      (e : chapter01RelativeProjBaseChange 𝒜 g ⟶ Q.scheme),
      IsIso e ∧
        e ≫ Q.projection =
          Limits.pullback.snd (chapter01RelativeProj 𝒜).projection g := by
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

theorem chapter01_homogeneous_localization_base_change
    {R A R' : Type*} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R']
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    {d : ℕ} {f : A} (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    Nonempty ((R' ⊗[R] HomogeneousLocalization.Away 𝒜 f) ≃+*
      HomogeneousLocalization.Away
        (fun n => (𝒜 n).baseChange R') (1 ⊗ₜ[R] f)) := by
  sorry

theorem chapter01_relative_proj_base_change_without_flatness {S T : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) (g : T ⟶ S) :
    ∃ (Q : Chapter01RelativeProj (chapter01RelativePullback 𝒜 g))
      (e : chapter01RelativeProjBaseChange 𝒜 g ⟶ Q.scheme),
      IsIso e ∧
        e ≫ Q.projection =
          Limits.pullback.snd (chapter01RelativeProj 𝒜).projection g := by
  exact chapter01_relative_proj_base_change 𝒜 g

noncomputable def chapter01RelativeFiberAlgebra {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) (s : S) :
    Chapter01RelativeGradedAlgebra (AlgebraicGeometry.Spec (S.residueField s)) :=
  chapter01RelativePullback 𝒜 (S.fromSpecResidueField s)

theorem chapter01_relative_proj_fiber {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S) (s : S) :
    ∃ (Q : Chapter01RelativeProj (chapter01RelativeFiberAlgebra 𝒜 s))
      (e : (chapter01RelativeProj 𝒜).projection.fiber s ⟶ Q.scheme),
      IsIso e ∧
        e ≫ Q.projection =
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

/- LOCAL_DEPENDENCY_GUESS: this type is the degree-zero part of the
homogeneous localization of the shifted graded module, written in the source
as `(M(n)_f)_0`. -/
noncomputable def chapter01ModuleAwayDegreeZero
    {A M : Type*} [CommRing A] [AddCommGroup M]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    (𝓜 : ℤ → Submodule ℤ M) [Module A M]
    (G : Chapter01GradedModule 𝒜 𝓜) (n : ℤ)
    {d : ℕ} (f : A) (hf : f ∈ 𝒜 d) (hd : 0 < d) : Type* := by
  sorry

noncomputable def chapter01TwistedLocalSections
    {A M : Type*} [CommRing A] [AddCommGroup M]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    (𝓜 : ℤ → Submodule ℤ M) [Module A M]
    (G : Chapter01GradedModule 𝒜 𝓜) (n : ℤ)
    {d : ℕ} (f : A) (hf : f ∈ 𝒜 d) (hd : 0 < d) : Type* :=
  chapter01ModuleAwayDegreeZero 𝒜 𝓜 G n f hf hd

/- LOCAL_DEPENDENCY_GUESS: Mathlib has the module and restriction categories,
but not the Proj sheafification of a graded module or the tensor/dual sheaf
operations needed for the twisting-sheaf construction. -/
noncomputable def chapter01SheafTensor {X : Scheme.{u}}
    (M N : X.Modules) : X.Modules := by
  sorry

noncomputable def chapter01SheafDual {X : Scheme.{u}}
    (M : X.Modules) : X.Modules := by
  sorry

noncomputable def chapter01OrdinaryTwistingSheaf {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] (n : ℤ) :
    (AlgebraicGeometry.«Proj» 𝒜).Modules := by
  sorry

noncomputable def chapter01RelativeTwistingSheaf {S : Scheme.{u}}
    (𝒜 : Chapter01RelativeGradedAlgebra S)
    (P : Chapter01RelativeProj 𝒜) (n : ℤ) : P.scheme.Modules := by
  sorry

noncomputable def chapter01OrdinaryStructureTwist {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] :
    (AlgebraicGeometry.«Proj» 𝒜).Modules :=
  chapter01OrdinaryTwistingSheaf 𝒜 0

theorem chapter01_ordinary_structure_twist_iso {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] :
    Nonempty (chapter01OrdinaryStructureTwist 𝒜 ≅
      SheafOfModules.unit (AlgebraicGeometry.«Proj» 𝒜).ringCatSheaf) := by
  sorry

def chapter01GeneratedInDegreeOne {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] : Prop :=
  Algebra.adjoin (𝒜 0) {x : A | x ∈ 𝒜 1} = ⊤

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
    Nonempty (chapter01SheafDual (chapter01OrdinaryTwistingSheaf 𝒜 n) ≅
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
    Nonempty (chapter01SheafDual (chapter01RelativeTwistingSheaf 𝒜 P n) ≅
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
    {d : ℕ} (h : chapter01GeneratedInDegreesDividing 𝒜 d)
    {f : A} (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    chapter01IsLineBundleOn (chapter01OrdinaryTwistingSheaf 𝒜 (d : ℤ))
      (chapter01SchemeStandardOpen 𝒜 f) := by
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

/- The source's eventual-isomorphism claim applies after imposing the usual
noetherian/standard-graded and finite-generation hypotheses.  These predicates
keep that eventual property separate from the generic componentwise map. -/
def Chapter01EventuallyAnIsomorphism
    {M Γ : ℤ → Type*} (φ : ∀ n, M n → Γ n) : Prop :=
  ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → Function.Bijective (φ n)

def Chapter01SmallDegreeSaturationFailure
    {M Γ : ℤ → Type*} (φ : ∀ n, M n → Γ n) : Prop :=
  ∃ n₀ : ℤ,
    (∀ n, n₀ ≤ n → Function.Bijective (φ n)) ∧
      ∃ n, n < n₀ ∧ ¬ Function.Bijective (φ n)

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

/- The Veronese comparison needs an admissible positive degree, expressed by
`chapter01VeroneseGeneratedInDegreeOne`; arbitrary positive degrees need not
give the same Proj.  The twist comparison is part of the chosen isomorphism,
since an arbitrary witness of scheme isomorphism need not preserve twists. -/
theorem chapter01_proj_veronese_iso_and_twist {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] {d : ℕ} (hd : 0 < d)
    (hgen : chapter01VeroneseGeneratedInDegreeOne 𝒜 d)
    (V : Chapter01VeroneseGradingData 𝒜 d) :
    ∃ e : AlgebraicGeometry.«Proj» 𝒜 ≅ chapter01VeroneseProj V,
      Nonempty ((Scheme.Modules.pullback e.hom).obj
        (chapter01VeroneseTwistingSheaf V 1) ≅
        chapter01OrdinaryTwistingSheaf 𝒜 (d : ℤ)) := by
  sorry

theorem chapter01_proj_veronese_iso {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] {d : ℕ} (hd : 0 < d)
    (hgen : chapter01VeroneseGeneratedInDegreeOne 𝒜 d)
    (V : Chapter01VeroneseGradingData 𝒜 d) :
    Nonempty (AlgebraicGeometry.«Proj» 𝒜 ≅ chapter01VeroneseProj V) := by
  exact ⟨(chapter01_proj_veronese_iso_and_twist 𝒜 hd hgen V).choose⟩

noncomputable def chapter01ProjVeroneseIso {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] {d : ℕ} (hd : 0 < d)
    (hgen : chapter01VeroneseGeneratedInDegreeOne 𝒜 d)
    (V : Chapter01VeroneseGradingData 𝒜 d) :
    AlgebraicGeometry.«Proj» 𝒜 ≅ chapter01VeroneseProj V :=
  (chapter01_proj_veronese_iso_and_twist 𝒜 hd hgen V).choose

theorem chapter01_veronese_twist_correspondence {A : Type*} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] {d : ℕ} (hd : 0 < d)
    (hgen : chapter01VeroneseGeneratedInDegreeOne 𝒜 d)
    (V : Chapter01VeroneseGradingData 𝒜 d) :
      Nonempty ((Scheme.Modules.pullback (chapter01ProjVeroneseIso 𝒜 hd hgen V).hom).obj
        (chapter01VeroneseTwistingSheaf V 1) ≅
      chapter01OrdinaryTwistingSheaf 𝒜 (d : ℤ)) := by
  simpa [chapter01ProjVeroneseIso] using
    (chapter01_proj_veronese_iso_and_twist 𝒜 hd hgen V).choose_spec

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

theorem chapter01_projective_presentation_closed_immersion
    {A : Type*} [CommRing A] (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    {r : ℕ} {G : Chapter01PolynomialGradingData (𝒜 0) r (fun _ => 1)}
    (P : Chapter01DegreeOnePolynomialPresentation 𝒜 G) :
    ∃ ι : AlgebraicGeometry.«Proj» 𝒜 ⟶ chapter01PolynomialProj G,
      IsClosedImmersion ι := by
  sorry

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter01
