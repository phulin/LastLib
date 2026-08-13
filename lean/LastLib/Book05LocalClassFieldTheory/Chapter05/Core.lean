import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Notation
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Abelianization.Finite
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree
import Mathlib.RepresentationTheory.Homological.Resolution
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.RingTheory.Norm.Defs

namespace LastLib.Book05LocalClassFieldTheory.Chapter05

noncomputable section

open CategoryTheory
open groupCohomology groupHomology
open scoped TensorProduct

/-!
## Shared interfaces for Chapter 5

The chapter uses the pinned Tate, group-homology, Galois, and quotient-group
interfaces directly.  The two genuinely local inputs which are not currently
provided by those Mathlib modules are kept as small records below: a cap
product operation and a normalized Brauer invariant.
-/

abbrev chapter05Abelianization (G : Type*) [Group G] := Abelianization G

abbrev chapter05CommutatorSubgroup (G : Type*) [Group G] : Subgroup G :=
  commutator G

def chapter05AbelianizationMap (G : Type*) [Group G] : G →* chapter05Abelianization G :=
  Abelianization.of

noncomputable def chapter05NormMap
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Lˣ →* Kˣ :=
  Units.map (Algebra.norm K (S := L))

def chapter05NormSubgroup
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Subgroup Kˣ :=
  (chapter05NormMap K L).range

def chapter05AlgebraMapUnits
    (K L : Type*) [Field K] [Field L] [Algebra K L] : Kˣ →* Lˣ :=
  Units.map (algebraMap K L)

def chapter05FixedUnitSubgroup
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] : Subgroup Lˣ :=
  { carrier := {x | ∀ σ : Gal(L / K), σ • x = x}
    one_mem' := by
      intro σ
      simp
    mul_mem' := by
      intro x y hx hy σ
      rw [smul_mul', hx σ, hy σ]
    inv_mem' := by
      intro x hx σ
      rw [smul_inv', hx σ]
  }

@[simp] theorem chapter05_mem_fixedUnitSubgroup_iff
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (x : Lˣ) :
    x ∈ chapter05FixedUnitSubgroup K L ↔
      ∀ σ : Gal(L / K), σ • x = x :=
  Iff.rfl

theorem chapter05FixedUnitSubgroup_eq_algebraMap_range
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    chapter05FixedUnitSubgroup K L =
      (chapter05AlgebraMapUnits K L).range := by
  sorry

abbrev chapter05NormQuotient
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :=
  Kˣ ⧸ chapter05NormSubgroup K L

def chapter05NormQuotientMk
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : Kˣ) : chapter05NormQuotient K L :=
  QuotientGroup.mk' (chapter05NormSubgroup K L) x

theorem chapter05NormQuotientMk_eq_one_iff
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : Kˣ) :
    chapter05NormQuotientMk K L x = 1 ↔ x ∈ chapter05NormSubgroup K L := by
  change QuotientGroup.mk' (chapter05NormSubgroup K L) x = 1 ↔
    x ∈ chapter05NormSubgroup K L
  exact QuotientGroup.eq_one_iff (N := chapter05NormSubgroup K L) x

def chapter05MaximalAbelianSubextension
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] : IntermediateField K L :=
  IntermediateField.fixedField (commutator (Gal(L / K)))

noncomputable def chapter05MaximalAbelianSubextension_galoisEquiv
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    Gal(chapter05MaximalAbelianSubextension K L / K) ≃*
      chapter05Abelianization (Gal(L / K)) := by
  sorry

abbrev chapter05CoefficientRep
    (K L : Type) [CommRing K] [CommRing L] [Algebra K L] :=
  Rep.ofAlgebraAutOnUnits K L

abbrev chapter05TateCohomology
    (G : Type) [Group G] [Fintype G] (A : Rep ℤ G) (r : ℤ) : ModuleCat ℤ :=
  (tateCohomologyFunctor (R := ℤ) (G := G) r).obj A

abbrev chapter05GroupCohomology
    (G : Type) [Group G] (A : Rep ℤ G) (n : ℕ) : ModuleCat ℤ :=
  groupCohomology A n

abbrev chapter05GroupHomology
    (G : Type) [Group G] (A : Rep ℤ G) (n : ℕ) : ModuleCat ℤ :=
  groupHomology A n

noncomputable def chapter05TateMinusTwoHomologyIso
    (G : Type) [Group G] [Fintype G] :
    chapter05TateCohomology G (Rep.trivial ℤ G ℤ) (-2) ≅
      chapter05GroupHomology G (Rep.trivial ℤ G ℤ) 1 :=
  (TateCohomology.isoGroupHomology (R := ℤ) (G := G) (-2) 1 (by decide)).app _

noncomputable def chapter05H1TensorAbelianizationIso
    (G : Type) [Group G] :
    chapter05GroupHomology G (Rep.trivial ℤ G ℤ) 1 ≃+
      Additive (chapter05Abelianization G) ⊗[ℤ] ℤ :=
  groupHomology.H1AddEquivOfIsTrivial (Rep.trivial ℤ G ℤ)

abbrev chapter05RationalResidue := ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)

def chapter05RationalResidueMk (q : ℚ) : chapter05RationalResidue :=
  QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ)) q

def chapter05RationalResidueOneOver (n : ℕ) : chapter05RationalResidue :=
  chapter05RationalResidueMk ((1 : ℚ) / (n : ℚ))

def chapter05RestrictTwoClass
    {G : Type} [Group G] {A : Rep ℤ G}
    (H : Subgroup G) (u : chapter05GroupCohomology G A 2) :
    chapter05GroupCohomology H (Rep.res H.subtype A) 2 :=
  groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype A)) 2 u

def chapter05Generates (A : ModuleCat ℤ) (x : A) : Prop :=
  Submodule.span ℤ {x} = ⊤

structure Chapter05CyclicGroupOfOrder
    (A : Type*) [AddCommGroup A] (n : ℕ) : Prop where
  finite : Finite A
  cyclic : IsAddCyclic A
  card_eq : Nat.card A = n

noncomputable instance chapter05SubgroupFintype
    {G : Type*} [Group G] [Fintype G] (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

/- LOCAL_DEPENDENCY_GUESS: Mathlib has the Tate complexes and their long
exact sequences, but not a cap-product operation with a chosen degree-two
class.  This record is the minimal book-facing interface for that operation;
it does not assume any isomorphism property. -/
structure Chapter05CapProduct
    (G : Type) [Group G] [Fintype G] (A : Rep ℤ G)
    (u : chapter05GroupCohomology G A 2) where
  cap : ∀ (H : Subgroup G) (r : ℤ),
    chapter05TateCohomology H (Rep.trivial ℤ H ℤ) r ⟶
      chapter05TateCohomology H (Rep.res H.subtype A) (r + 2)

def chapter05CapProductMap
    {G : Type} [Group G] [Fintype G] {A : Rep ℤ G}
    {u : chapter05GroupCohomology G A 2}
    (P : Chapter05CapProduct G A u) (H : Subgroup G) (r : ℤ) :
    chapter05TateCohomology H (Rep.trivial ℤ H ℤ) r ⟶
      chapter05TateCohomology H (Rep.res H.subtype A) (r + 2) :=
  P.cap H r

/- LOCAL_DEPENDENCY_GUESS: restriction to the top subgroup is equivalent to
the original representation, but the pinned Tate API does not expose the
corresponding change-of-group isomorphism. -/
structure Chapter05TopRestrictionTateIso
    (G : Type) [Group G] [Fintype G] (A : Rep ℤ G) where
  iso : ∀ r : ℤ,
    chapter05TateCohomology (⊤ : Subgroup G)
      (Rep.res (⊤ : Subgroup G).subtype A) r ≅
      chapter05TateCohomology G A r

/- LOCAL_DEPENDENCY_GUESS: the cap product at the top subgroup has a
   restricted trivial coefficient module in its source.  The existing
   top-restriction witness is indexed by the coefficient module of the
   fundamental class, so the trivial-coefficient change of subgroup must be
   exposed separately before the cap map can be composed with the degree
   minus-two homology identification. -/
structure Chapter05TopRestrictionTrivialTateIso
    (G : Type) [Group G] [Fintype G] where
  iso : ∀ r : ℤ,
    chapter05TateCohomology (⊤ : Subgroup G)
      (Rep.res (⊤ : Subgroup G).subtype (Rep.trivial ℤ G ℤ)) r ≅
      chapter05TateCohomology G (Rep.trivial ℤ G ℤ) r

structure Chapter05FundamentalTwoClass
    (G : Type) [Group G] [Fintype G] (A : Rep ℤ G) where
  /- The normalization is supplied by the local invariant system, whose
  subgroup restrictions are not definitionally the restriction to `⊤`. -/
  value : chapter05GroupCohomology G A 2

/- The standard augmentation is the `degree zero` map in the standard
resolution, so this record packages the exact two-extension used in the
Tate--Nakayama argument without introducing a second model of `ℤ[G]`. -/
structure Chapter05TwoExtension
    (G : Type) [Group G] (A : Rep ℤ G) where
  middle : Rep ℤ G
  inclusion : A ⟶ middle
  projection : middle ⟶ Rep.ofMulAction ℤ G (Fin 1 → G)
  inclusion_mono : Mono inclusion
  inclusion_projection : inclusion ≫ projection = 0
  projection_augmentation :
    projection ≫ Rep.standardComplex.ε ℤ G = 0
  augmentation_epi : Epi (Rep.standardComplex.ε ℤ G)
  middle_exact :
    (ShortComplex.mk inclusion projection inclusion_projection).Exact
  regular_exact :
    (ShortComplex.mk projection (Rep.standardComplex.ε ℤ G)
      projection_augmentation).Exact
  /- The two short exact stages of the two-extension.  The original maps are
     retained above for the book-facing `0 → A → middle → ℤ[G] → ℤ → 0`
     presentation; these fields expose the kernel of augmentation needed by
     the canonical long exact sequence in Tate cohomology. -/
  kernel : Rep ℤ G
  middle_to_kernel : middle ⟶ kernel
  kernel_to_regular : kernel ⟶ Rep.ofMulAction ℤ G (Fin 1 → G)
  middle_to_kernel_comp : middle_to_kernel ≫ kernel_to_regular = projection
  left_comp_zero : inclusion ≫ middle_to_kernel = 0
  right_comp_zero : kernel_to_regular ≫ Rep.standardComplex.ε ℤ G = 0
  left_shortExact :
    (ShortComplex.mk inclusion middle_to_kernel left_comp_zero).ShortExact
  right_shortExact :
    (ShortComplex.mk kernel_to_regular (Rep.standardComplex.ε ℤ G)
      right_comp_zero).ShortExact

/- The degree-two connecting morphism attached to the two short exact stages
   of a two-extension.  Restriction to a subgroup is performed before taking
   Tate cohomology, so this is the precise map used by Tate--Nakayama. -/
noncomputable def chapter05TwoExtensionConnecting
    {G : Type} [Group G] [Fintype G] {A : Rep ℤ G}
    (T : Chapter05TwoExtension G A) (H : Subgroup G) (r : ℤ) :
    chapter05TateCohomology H (Rep.trivial ℤ H ℤ) r ⟶
      chapter05TateCohomology H (Rep.res H.subtype A) (r + 2) := by
  let left : ShortComplex (Rep ℤ H) :=
    (ShortComplex.mk T.inclusion T.middle_to_kernel T.left_comp_zero).map
      (Rep.resFunctor H.subtype)
  let right : ShortComplex (Rep ℤ H) :=
    (ShortComplex.mk T.kernel_to_regular (Rep.standardComplex.ε ℤ G)
      T.right_comp_zero).map (Rep.resFunctor H.subtype)
  let trivialRestrictionIso :
      Rep.res H.subtype (Rep.trivial ℤ G ℤ) ≅ Rep.trivial ℤ H ℤ :=
    Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℤ ℤ) (by
      intro h
      ext
      simp))
  have hleft : left.ShortExact := by
    exact (Rep.shortExact_res H.subtype).2 T.left_shortExact
  have hright : right.ShortExact := by
    exact (Rep.shortExact_res H.subtype).2 T.right_shortExact
  change
    tateCohomology (Rep.trivial ℤ H ℤ) r ⟶
      tateCohomology (Rep.res H.subtype A) (r + 2)
  simpa [left, right, add_assoc] using
    ((tateCohomologyFunctor r).map trivialRestrictionIso.inv ≫
      TateCohomology.δ hright r ≫ TateCohomology.δ hleft (r + 1))

end

end LastLib.Book05LocalClassFieldTheory.Chapter05
