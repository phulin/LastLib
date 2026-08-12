import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.Polynomial.Basic

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped BigOperators Polynomial

universe u v

/-!
Shared interfaces for Chapter 11.

The checkout currently has no elaborated Book 8 Chapters 1--10.  The relative
scheme and quotient records below are therefore deliberately small bridges to
the canonical scheme APIs in Mathlib.  They record universal properties rather
than replacing them by hypotheses containing the conclusions of this chapter.
-/

/-- A scheme equipped with a chosen structural morphism to `S`. -/
structure RelativeScheme (S : Scheme.{u}) where
  carrier : Scheme.{u}
  structuralMap : carrier ⟶ S

namespace RelativeScheme

/-- A morphism in the book-facing slice of schemes over `S`. -/
structure Hom {S : Scheme.{u}} (X Y : RelativeScheme S) where
  hom : X.carrier ⟶ Y.carrier
  comm : hom ≫ Y.structuralMap = X.structuralMap

@[ext]
theorem Hom.ext {S : Scheme.{u}} {X Y : RelativeScheme S}
    {f g : RelativeScheme.Hom X Y}
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance (S : Scheme.{u}) : Category.{u} (RelativeScheme S) where
  Hom X Y := RelativeScheme.Hom X Y
  id X :=
    { hom := 𝟙 X.carrier
      comm := by simp }
  comp f g :=
    { hom := f.hom ≫ g.hom
      comm := by rw [Category.assoc, g.comm, f.comm] }

@[simp]
theorem id_hom {S : Scheme.{u}} (X : RelativeScheme S) :
    (𝟙 X : RelativeScheme.Hom X X).hom = 𝟙 X.carrier :=
  rfl

@[simp]
theorem comp_hom {S : Scheme.{u}} {X Y Z : RelativeScheme S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

/-- The base scheme viewed as an object over itself. -/
def base (S : Scheme.{u}) : RelativeScheme S where
  carrier := S
  structuralMap := 𝟙 S

/-- An isomorphism in the book-facing slice. -/
structure Iso {S : Scheme.{u}} (X Y : RelativeScheme S) where
  hom : X ⟶ Y
  inv : Y ⟶ X
  hom_inv_id : hom ≫ inv = 𝟙 X
  inv_hom_id : inv ≫ hom = 𝟙 Y

@[ext]
theorem Iso.ext {S : Scheme.{u}} {X Y : RelativeScheme S}
    {e e' : RelativeScheme.Iso X Y}
    (h : e.hom = e'.hom) : e = e' := by
  cases e with
  | mk hom inv hom_inv_id inv_hom_id =>
    cases e' with
    | mk hom' inv' hom_inv_id' inv_hom_id' =>
      cases h
      have hinv : inv = inv' := by
        calc
          inv = 𝟙 Y ≫ inv := by simp
          _ = (inv' ≫ hom) ≫ inv := by rw [inv_hom_id']
          _ = inv' ≫ (hom ≫ inv) := by simp only [Category.assoc]
          _ = inv' ≫ 𝟙 X := by rw [hom_inv_id]
          _ = inv' := by simp
      cases hinv
      rfl

@[simp]
theorem Iso.hom_inv_id_apply {S : Scheme.{u}} {X Y : RelativeScheme S}
    (e : RelativeScheme.Iso X Y) :
    e.hom ≫ e.inv = 𝟙 X :=
  e.hom_inv_id

@[simp]
theorem Iso.inv_hom_id_apply {S : Scheme.{u}} {X Y : RelativeScheme S}
    (e : RelativeScheme.Iso X Y) :
    e.inv ≫ e.hom = 𝟙 Y :=
  e.inv_hom_id

/-- Base change of a relative scheme along another object of the same slice. -/
def baseChange {S : Scheme.{u}} (X T : RelativeScheme S) : RelativeScheme T.carrier where
  carrier := pullback X.structuralMap T.structuralMap
  structuralMap := pullback.snd X.structuralMap T.structuralMap

/-- The canonical base change of a relative morphism. -/
def baseChangeHom {S : Scheme.{u}} {X Y : RelativeScheme S}
    (f : X ⟶ Y)
    (T : RelativeScheme S) : baseChange X T ⟶ baseChange Y T where
  hom := pullback.lift
    (pullback.fst X.structuralMap T.structuralMap ≫ f.hom)
    (pullback.snd X.structuralMap T.structuralMap)
    (by sorry)
  comm := by
    exact pullback.lift_snd _ _ _

@[simp]
theorem baseChangeHom_fst {S : Scheme.{u}} {X Y : RelativeScheme S}
    (f : X ⟶ Y)
    (T : RelativeScheme S) :
    (baseChangeHom f T).hom ≫ pullback.fst Y.structuralMap T.structuralMap =
      pullback.fst X.structuralMap T.structuralMap ≫ f.hom :=
  pullback.lift_fst _ _ _

@[simp]
theorem baseChangeHom_snd {S : Scheme.{u}} {X Y : RelativeScheme S}
    (f : X ⟶ Y)
    (T : RelativeScheme S) :
    (baseChangeHom f T).hom ≫ pullback.snd Y.structuralMap T.structuralMap =
      pullback.snd X.structuralMap T.structuralMap :=
  pullback.lift_snd _ _ _

end RelativeScheme

open RelativeScheme

/-- A binary product in the slice, expressed by its universal property. -/
structure RelativeProduct {S : Scheme.{u}} (X Y : RelativeScheme S) where
  carrier : RelativeScheme S
  fst : carrier ⟶ X
  snd : carrier ⟶ Y
  isProduct : ∀ {T : RelativeScheme S} (f : T ⟶ X)
    (g : T ⟶ Y),
    ∃! h : T ⟶ carrier, h ≫ fst = f ∧ h ≫ snd = g

theorem relativeProduct_exists {S : Scheme.{u}} (X Y : RelativeScheme S) :
    Nonempty (RelativeProduct X Y) := by
  sorry

noncomputable def relativeProduct {S : Scheme.{u}} (X Y : RelativeScheme S) :
    RelativeProduct X Y :=
  Classical.choice (relativeProduct_exists X Y)

noncomputable def RelativeProduct.lift {S : Scheme.{u}} {X Y T : RelativeScheme S}
    (P : RelativeProduct X Y) (f : T ⟶ X)
    (g : T ⟶ Y) : T ⟶ P.carrier :=
  (P.isProduct f g).choose

@[simp]
theorem RelativeProduct.lift_fst {S : Scheme.{u}} {X Y T : RelativeScheme S}
    (P : RelativeProduct X Y) (f : T ⟶ X)
    (g : T ⟶ Y) :
    P.lift f g ≫ P.fst = f :=
  by
    simpa [RelativeProduct.lift] using (P.isProduct f g).choose_spec.1.1

@[simp]
theorem RelativeProduct.lift_snd {S : Scheme.{u}} {X Y T : RelativeScheme S}
    (P : RelativeProduct X Y) (f : T ⟶ X)
    (g : T ⟶ Y) :
    P.lift f g ≫ P.snd = g :=
  by
    simpa [RelativeProduct.lift] using (P.isProduct f g).choose_spec.1.2

theorem RelativeProduct.lift_unique {S : Scheme.{u}} {X Y T : RelativeScheme S}
    (P : RelativeProduct X Y) (f : T ⟶ X)
    (g : T ⟶ Y)
    (h : T ⟶ P.carrier) (hf : h ≫ P.fst = f)
    (hg : h ≫ P.snd = g) :
    h = P.lift f g := by
  simpa [RelativeProduct.lift] using
    (P.isProduct f g).unique ⟨hf, hg⟩ (P.isProduct f g).choose_spec.1

/-- A chosen finite product of `d` copies of `X` in the slice. -/
structure RelativePower {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ) where
  carrier : RelativeScheme S
  projection : Fin d → (carrier ⟶ X)
  isPower : ∀ {T : RelativeScheme S} (f : Fin d → (T ⟶ X)),
    ∃! h : T ⟶ carrier, ∀ i, h ≫ projection i = f i
  permutation : Equiv.Perm (Fin d) → (carrier ⟶ carrier)
  permutation_one : permutation 1 = 𝟙 carrier
  permutation_mul : ∀ σ τ, permutation (σ * τ) = permutation σ ≫ permutation τ
  permutation_projection : ∀ (σ : Equiv.Perm (Fin d)) (i : Fin d),
    permutation σ ≫ projection i = projection (σ i)

theorem relativePower_exists {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ) :
    Nonempty (RelativePower X d) := by
  sorry

noncomputable def relativePower {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ) :
    RelativePower X d :=
  Classical.choice (relativePower_exists X d)

noncomputable def RelativePower.lift {S : Scheme.{u}} {X T : RelativeScheme S} {d : ℕ}
    (P : RelativePower X d) (f : Fin d → (T ⟶ X)) :
    T ⟶ P.carrier :=
  (P.isPower f).choose

@[simp]
theorem RelativePower.lift_projection {S : Scheme.{u}} {X T : RelativeScheme S} {d : ℕ}
    (P : RelativePower X d) (f : Fin d → (T ⟶ X)) (i : Fin d) :
    P.lift f ≫ P.projection i = f i :=
  by
    simpa [RelativePower.lift] using (P.isPower f).choose_spec.1 i

theorem RelativePower.lift_unique {S : Scheme.{u}} {X T : RelativeScheme S} {d : ℕ}
    (P : RelativePower X d) (f : Fin d → (T ⟶ X))
    (h : T ⟶ P.carrier)
    (hh : ∀ i, h ≫ P.projection i = f i) :
    h = P.lift f := by
  simpa [RelativePower.lift] using
    (P.isPower f).unique hh (P.isPower f).choose_spec.1

noncomputable def RelativePower.zero_power_iso {S : Scheme.{u}} (X : RelativeScheme S) :
    RelativeScheme.Iso (relativePower X 0).carrier (base S) := by
  sorry

noncomputable def RelativePower.one_power_iso {S : Scheme.{u}} (X : RelativeScheme S) :
    RelativeScheme.Iso (relativePower X 1).carrier X := by
  sorry

/-- A group action by automorphisms in the slice category. -/
structure RelativeAction {S : Scheme.{u}} (Y : RelativeScheme S) (G : Type v)
    [Group G] where
  hom : G → (Y ⟶ Y)
  one_hom : hom 1 = 𝟙 Y
  mul_hom : ∀ g h, hom (g * h) = hom g ≫ hom h
  isIso : ∀ g, IsIso (hom g).hom

def RelativeAction.baseChange {S : Scheme.{u}} {Y : RelativeScheme S} {G : Type v} [Group G]
    (act : RelativeAction Y G) (T : RelativeScheme S) :
    RelativeAction (RelativeScheme.baseChange Y T) G where
  hom := fun g => RelativeScheme.baseChangeHom (act.hom g) T
  one_hom := by
    apply RelativeScheme.Hom.ext
    sorry
  mul_hom := by
    intro g h
    apply RelativeScheme.Hom.ext
    sorry
  isIso := by
    intro g
    sorry

/-- The action is free when no nonidentity element fixes a relative point. -/
def RelativeAction.IsFree {S : Scheme.{u}} {Y : RelativeScheme S} {G : Type v} [Group G]
    (act : RelativeAction Y G) : Prop :=
  ∀ (T : RelativeScheme S) (x : T ⟶ Y) (g : G),
    x ≫ act.hom g = x → g = 1

noncomputable def RelativePower.permutationAction {S : Scheme.{u}} {X : RelativeScheme S} {d : ℕ}
    (P : RelativePower X d) : RelativeAction P.carrier (Equiv.Perm (Fin d)) where
  hom := P.permutation
  one_hom := P.permutation_one
  mul_hom := P.permutation_mul
  isIso := by
    intro σ
    sorry

theorem RelativePower.permutationAction_projection {S : Scheme.{u}} {X : RelativeScheme S} {d : ℕ}
    (P : RelativePower X d)
    (σ : Equiv.Perm (Fin d)) (i : Fin d) :
    (P.permutationAction.hom σ) ≫ P.projection i = P.projection (σ i) :=
  P.permutation_projection σ i

/-!
The following two declarations are the local dependency guesses needed for
the finite quotient theorem.  They are intentionally phrased as data rather
than as a proposition that already says a quotient exists.
-/

/- LOCAL_DEPENDENCY_GUESS: replace this ambient with the relative projective
   bundle interface from Book 8, Chapters 1--4 when it is available. -/
structure Chapter11ProjectiveSpaceOver (S : Scheme.{u}) (n : ℕ) where
  carrier : RelativeScheme S

/- LOCAL_DEPENDENCY_GUESS: the earlier chapters should provide the canonical
   notion of a quasi-projective morphism and its closed immersion into a
   relative projective space. -/
class Chapter11QuasiProjectiveOver {S : Scheme.{u}} (X : RelativeScheme S) where
  dimension : ℕ
  ambient : Chapter11ProjectiveSpaceOver S dimension
  embedding : X ⟶ ambient.carrier
  closed_immersion : IsClosedImmersion embedding.hom

/-- A categorical quotient in the slice, with its universal property. -/
structure RelativeCategoricalQuotient {S : Scheme.{u}} (Y : RelativeScheme S)
    (G : Type v) [Group G]
    (act : RelativeAction Y G) where
  carrier : RelativeScheme S
  quotientMap : Y ⟶ carrier
  invariant : ∀ g, act.hom g ≫ quotientMap = quotientMap
  universal : ∀ {Z : RelativeScheme S} (f : Y ⟶ Z),
    (∀ g, act.hom g ≫ f = f) →
      ∃! h : carrier ⟶ Z, quotientMap ≫ h = f

@[simp]
theorem RelativeCategoricalQuotient.quotientMap_invariant
    {S : Scheme.{u}} {Y : RelativeScheme S} {G : Type v} [Group G]
    {act : RelativeAction Y G}
    (Q : RelativeCategoricalQuotient Y G act) (g : G) :
    act.hom g ≫ Q.quotientMap = Q.quotientMap :=
  Q.invariant g

theorem RelativeCategoricalQuotient.factor_unique
    {S : Scheme.{u}} {Y : RelativeScheme S} {G : Type v} [Group G]
    {act : RelativeAction Y G}
    (Q : RelativeCategoricalQuotient Y G act)
    {Z : RelativeScheme S} (f : Y ⟶ Z)
    (hf : ∀ g, act.hom g ≫ f = f)
    (h k : Q.carrier ⟶ Z) (hh : Q.quotientMap ≫ h = f)
    (hk : Q.quotientMap ≫ k = f) : h = k := by
  exact (Q.universal f hf).unique hh hk

/-- The finite, integral, surjective quotient package used by this chapter. -/
structure RelativeFiniteGroupQuotient {S : Scheme.{u}} (Y : RelativeScheme S)
    (G : Type v) [Finite G] [Group G]
    (act : RelativeAction Y G) where
  quotient : RelativeCategoricalQuotient Y G act
  integral : IsIntegralHom quotient.quotientMap.hom
  finite : IsFinite quotient.quotientMap.hom
  surjective : Surjective quotient.quotientMap.hom
  flat_base_change :
    ∀ (T : RelativeScheme S), Flat T.structuralMap →
      ∃ QT : RelativeCategoricalQuotient
        (RelativeScheme.baseChange Y T) G (act.baseChange T),
        ∃ e : RelativeScheme.Iso (RelativeScheme.baseChange quotient.carrier T) QT.carrier,
          RelativeScheme.baseChangeHom quotient.quotientMap T ≫ e.hom = QT.quotientMap

abbrev RelativeFiniteGroupQuotient.carrier
    {S : Scheme.{u}} {Y : RelativeScheme S} {G : Type v} [Finite G] [Group G]
    {act : RelativeAction Y G}
    (Q : RelativeFiniteGroupQuotient Y G act) :
    RelativeScheme S :=
  Q.quotient.carrier

abbrev RelativeFiniteGroupQuotient.quotientMap
    {S : Scheme.{u}} {Y : RelativeScheme S} {G : Type v} [Finite G] [Group G]
    {act : RelativeAction Y G}
    (Q : RelativeFiniteGroupQuotient Y G act) :
    Y ⟶ Q.carrier :=
  Q.quotient.quotientMap

theorem finite_group_quotient_exists
    {S : Scheme.{u}} {Y : RelativeScheme S} {G : Type v} [Finite G] [Group G]
    (act : RelativeAction Y G)
    [Chapter11QuasiProjectiveOver Y] :
    Nonempty (RelativeFiniteGroupQuotient Y G act) := by
  sorry

noncomputable def finiteGroupQuotient
    {S : Scheme.{u}} {Y : RelativeScheme S} {G : Type v} [Finite G] [Group G]
    (act : RelativeAction Y G)
    [Chapter11QuasiProjectiveOver Y] :
    RelativeFiniteGroupQuotient Y G act :=
  Classical.choice (finite_group_quotient_exists act)

/-- The fppf condition used for a single scheme morphism. -/
def Chapter11Fppf {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  Flat f ∧ LocallyOfFinitePresentation f ∧ Surjective f

/-- The finite-type package for a scheme morphism. -/
def Chapter11FiniteType {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  QuasiCompact f ∧ LocallyOfFiniteType f

/-- Finite locally free of constant rank, expressed through Mathlib's rank API. -/
def Chapter11FiniteLocallyFreeOfRank {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) : Prop :=
  IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f ∧
    ∀ y : Y, Scheme.Hom.finrank f y = d

/-- An ideal sheaf is effective Cartier when it is locally generated by a regular element. -/
def _root_.AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier {X : Scheme.{u}}
    (I : X.IdealSheafData) : Prop :=
  ∀ (U : X.affineOpens) (x : U.1),
    ∃ (V : X.affineOpens) (f : Γ(X, V.1)),
      x.1 ∈ V.1 ∧ V ≤ U ∧ I.ideal V = Ideal.span ({f} : Set Γ(X, V.1)) ∧
        f ∈ nonZeroDivisors Γ(X, V.1)

/-- An effective Cartier divisor represented by its ideal sheaf. -/
structure EffectiveCartierDivisor (X : Scheme.{u}) where
  ideal : X.IdealSheafData
  isEffectiveCartier : ideal.IsEffectiveCartier

namespace EffectiveCartierDivisor

abbrev subscheme {X : Scheme.{u}} (D : EffectiveCartierDivisor X) : Scheme :=
  D.ideal.subscheme

abbrev inclusion {X : Scheme.{u}} (D : EffectiveCartierDivisor X) : D.subscheme ⟶ X :=
  D.ideal.subschemeι

def add {X : Scheme.{u}} (D E : EffectiveCartierDivisor X) : EffectiveCartierDivisor X where
  ideal := D.ideal * E.ideal
  isEffectiveCartier := by
    sorry

def sum {X : Scheme.{u}} {d : ℕ} (D : Fin d → EffectiveCartierDivisor X) :
    EffectiveCartierDivisor X where
  ideal := ∏ i, (D i).ideal
  isEffectiveCartier := by
    sorry

@[simp]
theorem sum_zero {X : Scheme.{u}} :
    (sum (d := 0) (fun i => Fin.elim0 i)).ideal = (1 : X.IdealSheafData) := by
  simp [sum]

theorem support_add {X : Scheme.{u}} (D E : EffectiveCartierDivisor X) :
    (D.add E).ideal.support = D.ideal.support ⊔ E.ideal.support := by
  simp [add]

end EffectiveCartierDivisor

/-- A degree-`d` relative effective Cartier divisor on `C_T`. -/
structure RelativeEffectiveCartierDivisor {S : Scheme.{u}}
    (C T : RelativeScheme S) (d : ℕ) where
  divisor : EffectiveCartierDivisor (pullback C.structuralMap T.structuralMap)
  finite_flat_rank :
    Chapter11FiniteLocallyFreeOfRank
      (divisor.inclusion ≫ pullback.snd C.structuralMap T.structuralMap) d

/-- A finite étale degree-`d` subscheme of `X_T`. -/
def Chapter11FiniteEtaleOfDegree {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) : Prop :=
  IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f ∧ Etale f ∧
    ∀ y : Y, Scheme.Hom.finrank f y = d

structure RelativeFiniteEtaleSubscheme {S : Scheme.{u}}
    (X T : RelativeScheme S) (d : ℕ) where
  carrier : Scheme.{u}
  mapToBase : carrier ⟶ T.carrier
  mapToX : carrier ⟶ pullback X.structuralMap T.structuralMap
  over_base : mapToX ≫ pullback.snd X.structuralMap T.structuralMap = mapToBase
  closed : IsClosedImmersion mapToX
  finite_etale : Chapter11FiniteEtaleOfDegree mapToBase d

/-- Sections that split a finite étale family after an étale cover. -/
def Chapter11SplitsAsDisjointSections {S : Scheme.{u}}
    {X T : RelativeScheme S} (d : ℕ) : Prop :=
  ∃ (U : Scheme.{u}) (u : U ⟶ T.carrier),
    Etale u ∧ Surjective u ∧
      ∃ (s : Fin d →
        (U ⟶ pullback (C := Scheme) X.structuralMap (u ≫ T.structuralMap))),
        Pairwise (fun i j => s i ≠ s j)

/-- A local monic equation with the basis `1,z,…,z^(d-1)`. -/
structure MonicPolynomialChart (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (d : ℕ) where
  parameter : A
  polynomial : R[X]
  monic : polynomial.Monic
  degree : polynomial.natDegree = d
  equation : Polynomial.aeval parameter polynomial = 0
  basis : Module.Basis (Fin d) R A
  basis_eq_power : ∀ i, basis i = parameter ^ (i : ℕ)

theorem MonicPolynomialChart.ext {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] {d : ℕ} {P Q : MonicPolynomialChart R A d}
    (hparameter : P.parameter = Q.parameter) (hpolynomial : P.polynomial = Q.polynomial) :
    P = Q := by
  sorry

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11
