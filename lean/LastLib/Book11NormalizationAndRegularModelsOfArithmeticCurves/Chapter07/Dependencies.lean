import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.RegularLocalRing.Defs
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.Dependencies
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03.Dependencies
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03.Section01CodimensionOneCycles

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03
open scoped AlgebraicGeometry BigOperators

universe u v

/-! ## Book-facing ideal and model interfaces -/

/- Mathlib's `IdealSheafData` is the pinned ideal-sheaf object.  The finite-generation
condition below is the affine-open formulation of coherence used in this chapter. -/
structure Chapter07CoherentIdeal (X : Scheme.{u}) where
  ideal : X.IdealSheafData
  finitelyGenerated : ∀ U : X.affineOpens, (ideal.ideal U).FG

instance {X : Scheme.{u}} : Coe (Chapter07CoherentIdeal X) X.IdealSheafData :=
  ⟨Chapter07CoherentIdeal.ideal⟩

def Chapter07CoherentIdeal.support {X : Scheme.{u}} (I : Chapter07CoherentIdeal X) : Set X :=
  I.ideal.support

theorem chapter07_coherentIdeal_support_isClosed {X : Scheme.{u}}
    (I : Chapter07CoherentIdeal X) : IsClosed I.support := by
  exact I.ideal.support.isClosed

noncomputable def chapter07UnitCoherentIdeal (X : Scheme.{u}) : Chapter07CoherentIdeal X where
  ideal := ⊤
  finitelyGenerated := by
    intro U
    exact Ideal.fg_top _

noncomputable def chapter07ZeroCoherentIdeal (X : Scheme.{u}) : Chapter07CoherentIdeal X where
  ideal := ⊥
  finitelyGenerated := by
    intro U
    exact Ideal.fg_bot

noncomputable def Chapter07CoherentIdeal.comap
    {X Y : Scheme.{u}} (I : Chapter07CoherentIdeal X) (f : Y ⟶ X) :
    Chapter07CoherentIdeal Y where
  ideal := I.ideal.comap f
  finitelyGenerated := by
    intro U
    sorry

@[simp]
theorem chapter07_coherentIdeal_comap_ideal
    {X Y : Scheme.{u}} (I : Chapter07CoherentIdeal X) (f : Y ⟶ X) :
    (I.comap f).ideal = I.ideal.comap f :=
  rfl

theorem chapter07_coherentIdeal_support_comap
    {X Y : Scheme.{u}} (I : Chapter07CoherentIdeal X) (f : Y ⟶ X) :
    (I.comap f).support = I.support.preimage f := by
  simpa [Chapter07CoherentIdeal.support] using
    congrArg (fun C : Closeds Y => (C : Set Y))
      (Scheme.IdealSheafData.support_comap I.ideal f)

noncomputable def chapter07AffineCoherentIdeal
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    Chapter07CoherentIdeal (Spec (.of A)) where
  ideal := Scheme.IdealSheafData.ofIdealTop I
  finitelyGenerated := by
    intro U
    sorry

/- The source uses “invertible ideal” in the ideal-sheaf sense: locally one regular
element generates the ideal.  This is also the exact hypothesis in the blowup
universal property. -/
def Chapter07IsInvertibleIdeal {X : Scheme.{u}} (I : X.IdealSheafData) : Prop :=
  ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ a : Γ(X, U),
    I.ideal U = Ideal.span {a} ∧ IsRegular a

theorem chapter07_isInvertibleIdeal_iff_locallyPrincipalRegular
    {X : Scheme.{u}} (I : X.IdealSheafData) :
    Chapter07IsInvertibleIdeal I ↔
      ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ a : Γ(X, U),
        I.ideal U = Ideal.span {a} ∧ IsRegular a :=
  Iff.rfl

def chapter07IdealPullback {X Y : Scheme.{u}}
    (I : X.IdealSheafData) (f : Y ⟶ X) : Y.IdealSheafData :=
  I.comap f

theorem chapter07IdealPullback_support
    {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : Y ⟶ X) :
    (chapter07IdealPullback I f).support = I.support.preimage f := by
  simpa using congrArg (fun C : Closeds Y => (C : Set Y))
    (Scheme.IdealSheafData.support_comap I f)

/-! ### Normality, regular surfaces, and finite centers -/

structure Chapter07NormalIntegralScheme (X : Scheme.{u}) : Prop where
  integral : IsIntegral X
  locallyNoetherian : IsLocallyNoetherian X
  integrallyClosed_stalk : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)

structure Chapter07RegularSurface (X : Scheme.{u}) : Prop where
  locallyNoetherian : IsLocallyNoetherian X
  regular_stalk : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)
  dimension_le_two : ∀ x : X, Order.coheight x ≤ 2
  has_two_dimensional_point : ∃ x : X, Order.coheight x = 2

def Chapter07ClosedRegularPoint {X : Scheme.{u}} (x : X) : Prop :=
  IsClosed ({x} : Set X) ∧ IsRegularLocalRing (X.presheaf.stalk x)

structure Chapter07FiniteClosedPointCenter
    {X : Scheme.{u}} (I : Chapter07CoherentIdeal X) where
  points : Finset X
  points_closed : ∀ x, x ∈ points → IsClosed ({x} : Set X)
  support_subset : ∀ x : X, x ∈ I.support → ∃ p, p ∈ points ∧ x = p

def Chapter07IsNonzeroIdeal {X : Scheme.{u}} (I : Chapter07CoherentIdeal X) : Prop :=
  I.ideal ≠ (⊥ : X.IdealSheafData)

/-! A small transport record avoids repeatedly losing the map to the common target when
comparing two relative constructions. -/
structure Chapter07SchemeIsoOver
    {Y Z X : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ X) where
  iso : Y ≅ Z
  over : iso.hom ≫ g = f

@[ext]
theorem chapter07SchemeIsoOver_ext
    {Y Z X : Scheme.{u}} {f : Y ⟶ X} {g : Z ⟶ X}
    {e₁ e₂ : Chapter07SchemeIsoOver f g}
    (h : e₁.iso = e₂.iso) : e₁ = e₂ := by
  cases e₁
  cases e₂
  cases h
  rfl

abbrev Chapter07IsProjectiveMorphism {Y X : Scheme.{u}} (f : Y ⟶ X) : Prop :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.IsProjectiveMorphism f

def Chapter07Birational {Y X : Scheme.{u}} (f : Y ⟶ X) : Prop :=
  ∃ U : X.Opens, Dense (U : Set X) ∧ IsIso (f ∣_ U)

def chapter07ExceptionalLocus {Y X : Scheme.{u}} (f : Y ⟶ X) : Set X :=
  {x | ¬ ∃ U : X.Opens, x ∈ U ∧ IsIso (f ∣_ U)}

structure Chapter07ExceptionalDivisor
    {Y X : Scheme.{u}} (f : Y ⟶ X) where
  divisor : Chapter03PrimeDivisor Y
  image_in_exceptional_locus : f '' divisor.support ⊆ chapter07ExceptionalLocus f

/-! ### Generic fibers and arithmetic surfaces -/

structure Chapter07GenericOpen (S : Scheme.{u}) where
  open : S.Opens
  dense : Dense (open : Set S)

def chapter07GenericFiber {X S : Scheme.{u}} (f : X ⟶ S) (η : S) : Scheme :=
  f.fiber η

/- LOCAL_DEPENDENCY_GUESS: the pullback map between the two displayed fibers is kept as a
chapter-facing morphism until the most convenient pinned `pullback.map` normal form is fixed. -/
noncomputable def chapter07GenericFiberMap
    {Y X S : Scheme.{u}} (g : Y ⟶ X) (f : X ⟶ S) (η : S) :
    (g ≫ f).fiber η ⟶ f.fiber η := by
  sorry

def Chapter07CenterDisjointFromGenericFiber
    {X S : Scheme.{u}} (f : X ⟶ S) (I : Chapter07CoherentIdeal X) (η : S) : Prop :=
  ∀ x : X, x ∈ I.support → f x ≠ η

def Chapter07CenterDisjointFromGenericOpen
    {X S : Scheme.{u}} (f : X ⟶ S) (I : Chapter07CoherentIdeal X)
    (G : Chapter07GenericOpen S) : Prop :=
  I.support ∩ f ⁻¹' (G.open : Set S) = ∅

structure Chapter07ArithmeticSurface where
  base : Scheme.{u}
  baseDedekind : Chapter03DedekindBase base
  model : Scheme.{u}
  structureMap : model ⟶ base
  flat : Flat structureMap
  projective : Chapter07IsProjectiveMorphism structureMap
  relativeCurve : Chapter03RelativeCurve structureMap
  generic : Chapter07GenericOpen base
  surfaceDimension : ∀ x : model, Order.coheight x ≤ 2

/-! ### Rees algebras and the affine Proj input -/

abbrev Chapter07ReesAlgebra (A : Type u) [CommRing A] (I : Ideal A) :=
  reesAlgebra I

noncomputable def chapter07ReesDegreeMap
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    (I ^ n : Type u) →ₗ[A] Chapter07ReesAlgebra A I where
  toFun a :=
    ⟨Polynomial.monomial n a.1, reesAlgebra.monomial_mem.mpr a.2⟩
  map_add' := by
    intro a b
    ext
    simp
  map_smul' := by
    intro r a
    ext
    simp [Algebra.smul_def]

def chapter07ReesDegree
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    Submodule A (Chapter07ReesAlgebra A I) :=
  Submodule.map (chapter07ReesDegreeMap A I n) ⊤

theorem chapter07_reesDegree_mem_iff
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ)
    (p : Chapter07ReesAlgebra A I) :
    p ∈ chapter07ReesDegree A I n ↔
      ∀ i, i ≠ n → p.1.coeff i = 0 := by
  sorry

/- The pinned Rees-algebra file supplies the subalgebra but not its internal grading.  The
following record is the minimal reusable bridge to Mathlib's `Proj` API. -/
structure Chapter07ReesGrading (A : Type u) [CommRing A] (I : Ideal A) where
  component : ℕ → Submodule A (Chapter07ReesAlgebra A I)
  component_eq : ∀ n, component n = chapter07ReesDegree A I n
  graded : GradedAlgebra component

noncomputable def chapter07CanonicalReesGrading
    (A : Type u) [CommRing A] (I : Ideal A) : Chapter07ReesGrading A I where
  component := chapter07ReesDegree A I
  component_eq := fun _ => rfl
  graded := by
    sorry

noncomputable def chapter07ReesProj
    (A : Type u) [CommRing A] (I : Ideal A) : Scheme :=
  let G := chapter07CanonicalReesGrading A I
  letI : GradedAlgebra G.component := G.graded
  AlgebraicGeometry.Proj G.component

/-! The integral closure of a Rees algebra is written over the polynomial ring itself.  The
degree-wise ideal and the normalized Rees grading are introduced in §7.3. -/
noncomputable def chapter07NormalizedReesAlgebra
    (A : Type u) [CommRing A] (I : Ideal A) : Subalgebra (Chapter07ReesAlgebra A I) A[X] :=
  integralClosure (Chapter07ReesAlgebra A I) A[X]

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07
