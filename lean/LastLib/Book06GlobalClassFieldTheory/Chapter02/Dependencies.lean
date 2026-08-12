import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.Section03ResidueActionAndInertia
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Section02FrobeniusInAnUnramifiedExtension
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Basic

namespace LastLib.Book06GlobalClassFieldTheory.Chapter02

noncomputable section

open scoped BigOperators Pointwise

universe u v w z

/-!
Shared interfaces for Chapter 2.

Book 4 and Book 5 are not yet present in this checkout.  The definitions below
keep their required interfaces explicit: a place is represented by its action
on a set of places, local class field theory is represented by its local norm
and reciprocity data, and the restricted product is represented by the usual
finite-integrality condition.  None of these interfaces contains a global
reciprocity conclusion.
-/

/-!
### Chosen places and decomposition groups
-/

/-- A place `extensionPlace` of the upper field above `basePlace`.

The `action_over_base` field says that the Galois action preserves the chosen
base place.  This is the abstract form of the fact that an automorphism of
`L/K` sends a place of `L` above `v` to another place above the same `v`.
-/
structure Chapter02ChosenPlace
    (G : Type u) [Group G] (V : Type v) (W : Type w) [MulAction G W] where
  basePlace : V
  extensionPlace : W
  restriction : W → V
  liesOver : restriction extensionPlace = basePlace
  action_over_base : ∀ (g : G) (x : W), restriction (g • x) = restriction x

@[ext]
theorem Chapter02ChosenPlace.ext
    {G : Type u} [Group G] {V : Type v} {W : Type w} [MulAction G W]
    {P Q : Chapter02ChosenPlace G V W}
    (hbase : P.basePlace = Q.basePlace)
    (hextension : P.extensionPlace = Q.extensionPlace)
    (hrestriction : P.restriction = Q.restriction)
    (hliesOver : HEq P.liesOver Q.liesOver)
    (haction : HEq P.action_over_base Q.action_over_base) :
    P = Q := by
  cases P
  cases Q
  simp_all

/-- The stabilizer definition of the decomposition group at a chosen place. -/
def chapter02DecompositionGroup
    {G : Type u} [Group G] {V : Type v} {W : Type w} [MulAction G W]
    (P : Chapter02ChosenPlace G V W) : Subgroup G :=
  MulAction.stabilizer G P.extensionPlace

@[simp]
theorem chapter02_mem_decompositionGroup_iff
    {G : Type u} [Group G] {V : Type v} {W : Type w} [MulAction G W]
    (P : Chapter02ChosenPlace G V W) (σ : G) :
    σ ∈ chapter02DecompositionGroup P ↔ σ • P.extensionPlace = P.extensionPlace := by
  rfl

/-- The chosen place obtained from `P` by replacing `w` with `τ w`. -/
def chapter02ConjugateChosenPlace
    {G : Type u} [Group G] {V : Type v} {W : Type w} [MulAction G W]
    (P : Chapter02ChosenPlace G V W) (τ : G) : Chapter02ChosenPlace G V W where
  basePlace := P.basePlace
  extensionPlace := τ • P.extensionPlace
  restriction := P.restriction
  liesOver := (P.action_over_base τ P.extensionPlace).trans P.liesOver
  action_over_base := P.action_over_base

theorem chapter02_decompositionGroup_conjugate
    {G : Type u} [Group G] {V : Type v} {W : Type w} [MulAction G W]
    (P : Chapter02ChosenPlace G V W) (τ : G) :
    chapter02DecompositionGroup (chapter02ConjugateChosenPlace P τ) =
      (chapter02DecompositionGroup P).map (MulAut.conj τ).toMonoidHom := by
  exact MulAction.stabilizer_smul_eq_stabilizer_map_conj τ P.extensionPlace

/-- The inertia subgroup at every upper place, with its conjugation compatibility.

DEPENDENCY_GUESS: this is the small bridge from the canonical valuation-ring or
prime-ideal inertia construction in the earlier local chapters to the abstract
place action used here.  Its fields are the subgroup containment and the usual
conjugation transport, not a global reciprocity statement.
-/
structure Chapter02InertiaSystem
    (G : Type u) [Group G] (W : Type v) [MulAction G W] where
  inertia : W → Subgroup G
  inertia_le_decomposition : ∀ x : W, inertia x ≤ MulAction.stabilizer G x
  conjugation : ∀ (τ : G) (x : W),
    (inertia x).map (MulAut.conj τ).toMonoidHom = inertia (τ • x)

@[ext]
theorem Chapter02InertiaSystem.ext
    {G : Type u} [Group G] {W : Type v} [MulAction G W]
    {S T : Chapter02InertiaSystem G W}
    (hinertia : S.inertia = T.inertia) : S = T := by
  cases S
  cases T
  simp_all

/-- Inertia viewed as a subgroup of the decomposition group at `P`. -/
def chapter02InertiaGroup
    {G : Type u} [Group G] {V : Type v} {W : Type w} [MulAction G W]
    (P : Chapter02ChosenPlace G V W) (S : Chapter02InertiaSystem G W) :
    Subgroup (chapter02DecompositionGroup P) :=
  (S.inertia P.extensionPlace).subgroupOf (chapter02DecompositionGroup P)

theorem chapter02_inertia_group_mem_decomposition
    {G : Type u} [Group G] {V : Type v} {W : Type w} [MulAction G W]
    (P : Chapter02ChosenPlace G V W) (S : Chapter02InertiaSystem G W) :
    ∀ i : chapter02InertiaGroup P S,
      ((i : chapter02DecompositionGroup P) : G) ∈
        chapter02DecompositionGroup P := by
  intro i
  exact i.1.property

theorem chapter02_inertia_conjugation
    {G : Type u} [Group G] {V : Type v} {W : Type w} [MulAction G W]
    (P : Chapter02ChosenPlace G V W) (S : Chapter02InertiaSystem G W) (τ : G) :
    S.inertia (τ • P.extensionPlace) =
      (S.inertia P.extensionPlace).map (MulAut.conj τ).toMonoidHom := by
  exact (S.conjugation τ P.extensionPlace).symm

theorem chapter02_decompositionGroup_choice_independent_of_abelianity
    {G : Type u} [CommGroup G] {V : Type v} {W : Type w} [MulAction G W]
    (P : Chapter02ChosenPlace G V W) (τ : G) :
    chapter02DecompositionGroup (chapter02ConjugateChosenPlace P τ) =
      chapter02DecompositionGroup P := by
  sorry

theorem chapter02_inertia_choice_independent_of_abelianity
    {G : Type u} [CommGroup G] {V : Type v} {W : Type w} [MulAction G W]
    (P : Chapter02ChosenPlace G V W) (S : Chapter02InertiaSystem G W) (τ : G) :
    S.inertia (τ • P.extensionPlace) = S.inertia P.extensionPlace := by
  sorry

/-!
### Local residue and reciprocity interfaces
-/

/--
The residue reduction datum at a finite place.  The map is the reduction map
`D_w → Gal(k_w/k_v)`, and its kernel is recorded as inertia.  Surjectivity is
kept as a separate field because it is the exactness/surjectivity part of the
local valuation-theoretic input.
-/
structure Chapter02ResidueActionData
    (D k l : Type*) [Group D] [Field k] [Field l] [Algebra k l] where
  finite_dimensional : FiniteDimensional k l
  galois : IsGalois k l
  inertia : Subgroup D
  reduction : D →* Gal(l / k)
  kernel_eq_inertia : reduction.ker = inertia
  inertia_normal : inertia.Normal
  reduction_surjective : Function.Surjective reduction

instance chapter02ResidueActionData.inertiaNormal
    {D k l : Type*} [Group D] [Field k] [Field l] [Algebra k l]
    (R : Chapter02ResidueActionData D k l) : R.inertia.Normal :=
  R.inertia_normal

@[ext]
theorem Chapter02ResidueActionData.ext
    {D k l : Type*} [Group D] [Field k] [Field l] [Algebra k l]
    {R S : Chapter02ResidueActionData D k l}
    (hfinite : R.finite_dimensional = S.finite_dimensional)
    (hgalois : R.galois = S.galois)
    (hinertia : R.inertia = S.inertia)
    (hred : R.reduction = S.reduction) : R = S := by
  cases R
  cases S
  simp_all

/-- The exact-sequence predicate for residue reduction. -/
def chapter02ResidueExactSequence
    {D k l : Type*} [Group D] [Field k] [Field l] [Algebra k l]
    (R : Chapter02ResidueActionData D k l) : Prop :=
  Function.MulExact R.inertia.subtype R.reduction

theorem chapter02_residue_exact_sequence
    {D k l : Type*} [Group D] [Field k] [Field l] [Algebra k l]
    (R : Chapter02ResidueActionData D k l) :
    chapter02ResidueExactSequence R := by
  change Function.MulExact R.inertia.subtype R.reduction
  apply MonoidHom.mulExact_iff.mpr
  rw [R.kernel_eq_inertia]
  exact (Subgroup.range_subtype _).symm

theorem chapter02_residue_kernel_membership_iff
    {D k l : Type*} [Group D] [Field k] [Field l] [Algebra k l]
    (R : Chapter02ResidueActionData D k l) (σ : D) :
    σ ∈ R.inertia ↔ R.reduction σ = 1 := by
  rw [← R.kernel_eq_inertia]
  rfl

/--
The local norm and reciprocity interface used by the Artin map.  The target of
local reciprocity is the canonical abelianization `Dᵃᵇ`; the abelian case
recovers a map to `D` by the canonical abelianization equivalence.

DEPENDENCY_GUESS: Book 5 is expected to provide these fields for the local
extension `L_w/K_v`, including the norm-kernel theorem, surjectivity, and the
unit/inertia comparison.  They are deliberately local facts and do not encode
the global product formula.
-/
structure Chapter02LocalReciprocityData
    (B E D : Type*) [CommGroup B] [CommGroup E] [Group D] where
  reciprocity : B →* Abelianization D
  norm : E →* B
  reciprocity_surjective : Function.Surjective reciprocity
  kernel_eq_norm_range : reciprocity.ker = norm.range
  unitSubgroup : Subgroup B
  extensionUnitSubgroup : Subgroup E
  norm_unit_mem : ∀ x : extensionUnitSubgroup, norm x ∈ unitSubgroup
  inertia : Subgroup D
  unit_image_eq_inertia :
    (reciprocity.comp unitSubgroup.subtype).range =
      inertia.map Abelianization.of
  unramified_unit_norm_surjective :
    inertia = ⊥ →
      Function.Surjective
        ((norm.comp extensionUnitSubgroup.subtype).codRestrict unitSubgroup
          (fun x => norm_unit_mem x))

@[ext]
theorem Chapter02LocalReciprocityData.ext
    {B E D : Type*} [CommGroup B] [CommGroup E] [Group D]
    {R S : Chapter02LocalReciprocityData B E D}
    (hreciprocity : R.reciprocity = S.reciprocity)
    (hnorm : R.norm = S.norm)
    (hunit : R.unitSubgroup = S.unitSubgroup)
    (hextensionUnit : R.extensionUnitSubgroup = S.extensionUnitSubgroup)
    (hinertia : R.inertia = S.inertia) : R = S := by
  cases R
  cases S
  simp_all

/-- The local norm on unit subgroups. -/
def chapter02LocalUnitNorm
    {B E D : Type*} [CommGroup B] [CommGroup E] [Group D]
    (R : Chapter02LocalReciprocityData B E D) :
    R.extensionUnitSubgroup →* R.unitSubgroup :=
  (R.norm.comp R.extensionUnitSubgroup.subtype).codRestrict R.unitSubgroup
    (fun x => R.norm_unit_mem x)

theorem chapter02_local_unit_norm_surjective
    {B E D : Type*} [CommGroup B] [CommGroup E] [Group D]
    (R : Chapter02LocalReciprocityData B E D) (_hI : R.inertia = ⊥) :
    Function.Surjective (chapter02LocalUnitNorm R) := by
  exact R.unramified_unit_norm_surjective _hI

/-- The local Artin map in the abelian decomposition group. -/
def chapter02LocalArtinMap
    {B E D : Type*} [CommGroup B] [CommGroup E] [CommGroup D]
    (R : Chapter02LocalReciprocityData B E D) : B →* D :=
  (Abelianization.equivOfComm.symm.toMonoidHom).comp R.reciprocity

theorem chapter02_local_artin_kernel_eq_norm_range
    {B E D : Type*} [CommGroup B] [CommGroup E] [CommGroup D]
    (R : Chapter02LocalReciprocityData B E D) :
    (chapter02LocalArtinMap R).ker = R.norm.range := by
  sorry

theorem chapter02_local_artin_surjective
    {B E D : Type*} [CommGroup B] [CommGroup E] [CommGroup D]
    (R : Chapter02LocalReciprocityData B E D) :
    Function.Surjective (chapter02LocalArtinMap R) := by
  sorry

theorem chapter02_local_artin_range_eq_top
    {B E D : Type*} [CommGroup B] [CommGroup E] [CommGroup D]
    (R : Chapter02LocalReciprocityData B E D) :
    (chapter02LocalArtinMap R).range = ⊤ := by
  exact (Subgroup.eq_top_iff' _).2 (chapter02_local_artin_surjective R)

theorem chapter02_local_artin_units_eq_inertia
    {B E D : Type*} [CommGroup B] [CommGroup E] [CommGroup D]
    (R : Chapter02LocalReciprocityData B E D) :
    ((chapter02LocalArtinMap R).comp R.unitSubgroup.subtype).range = R.inertia := by
  sorry

/-- The canonical abelianized local map in a possibly nonabelian ambient group. -/
def chapter02AbelianizedLocalArtinMap
    {B E G D : Type*} [CommGroup B] [CommGroup E] [Group G] [Group D]
    (inclusion : D →* G) (R : Chapter02LocalReciprocityData B E D) :
    B →* Abelianization G :=
  (Abelianization.map inclusion).comp R.reciprocity

theorem chapter02_abelianized_local_artin_choice_conjugation_invariant
    {B E G D : Type*} [CommGroup B] [CommGroup E] [Group G] [Group D]
    (inclusion : D →* G) (R : Chapter02LocalReciprocityData B E D)
    (c : G →* G) (hc : ∀ g, c g = g) :
    (Abelianization.map c).comp
        (chapter02AbelianizedLocalArtinMap inclusion R) =
      chapter02AbelianizedLocalArtinMap inclusion R := by
  sorry

/-!
### Discrete valuation and Frobenius interfaces
-/

/-- The valuation-theoretic decomposition of a local multiplicative group. -/
structure Chapter02DiscreteValuationData
    (B : Type*) [CommGroup B] (U : Subgroup B) where
  ord : B → ℤ
  ord_one : ord 1 = 0
  ord_mul : ∀ x y, ord (x * y) = ord x + ord y
  unit_iff_ord_zero : ∀ x, x ∈ U ↔ ord x = 0
  uniformizer : B
  ord_uniformizer : ord uniformizer = 1
  decomposition : ∀ x : B, ∃ u : U, x = (u : B) * uniformizer ^ (ord x)

@[ext]
theorem Chapter02DiscreteValuationData.ext
    {B : Type*} [CommGroup B] {U : Subgroup B}
    {V W : Chapter02DiscreteValuationData B U}
    (hord : V.ord = W.ord) (huniformizer : V.uniformizer = W.uniformizer) :
    V = W := by
  sorry

@[simp]
theorem chapter02_discrete_valuation_ord_uniformizer
    {B : Type*} [CommGroup B] {U : Subgroup B}
    (V : Chapter02DiscreteValuationData B U) :
    V.ord V.uniformizer = 1 :=
  V.ord_uniformizer

/-- Arithmetic residue Frobenius, using the normalization fixed in Book 2. -/
noncomputable def chapter02ArithmeticFrobenius
    {k l : Type*} [Field k] [Field l] [Fintype k] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l] : Gal(l / k) :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.chapter06ArithmeticFrobenius k l

theorem chapter02_arithmetic_frobenius_apply
    {k l : Type*} [Field k] [Field l] [Fintype k] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l] (x : l) :
    chapter02ArithmeticFrobenius (k := k) (l := l) x = x ^ Fintype.card k := by
  sorry

/- DEPENDENCY_GUESS: when a concrete completion API is unavailable, this
   equivalence is the minimal local interface for the canonical identification
   `D_w ≃ Gal(L_w/K_v)`. -/
structure Chapter02CompletionGaloisIdentification
    (D H : Type*) [Group D] [Group H] where
  equiv : D ≃* H

/-!
### Restricted products and idele classes
-/

/-- The integral subgroup at each place in a multiplicative restricted product. -/
structure Chapter02RestrictedProductData
    (V : Type u) (H : V → Type v) [∀ x, CommGroup (H x)] where
  isFinite : V → Prop
  integral : ∀ x : V, Subgroup (H x)

@[ext]
theorem Chapter02RestrictedProductData.ext
    {V : Type u} {H : V → Type v} [∀ x, CommGroup (H x)]
    {D E : Chapter02RestrictedProductData V H}
    (hfinite : D.isFinite = E.isFinite)
    (hintegral : D.integral = E.integral) : D = E := by
  sorry

/-- The subgroup of the full product consisting of ideles. -/
def chapter02IdeleSubgroup
    {V : Type u} {H : V → Type v} [∀ x, CommGroup (H x)]
    (D : Chapter02RestrictedProductData V H) : Subgroup (∀ x, H x) := by
  classical
  refine
    { carrier := {x | Set.Finite {v | D.isFinite v ∧ x v ∉ D.integral v}}
      one_mem' := by
        change Set.Finite {v | D.isFinite v ∧ (1 : ∀ x, H x) v ∉ D.integral v}
        have h : {v | D.isFinite v ∧ (1 : ∀ x, H x) v ∉ D.integral v} = ∅ := by
          ext v
          simp
        rw [h]
        exact Set.finite_empty
      mul_mem' := by
        sorry
      inv_mem' := by
        sorry }

/-- The idele group attached to the restricted product data. -/
abbrev chapter02Ideles
    {V : Type u} {H : V → Type v} [∀ x, CommGroup (H x)]
    (D : Chapter02RestrictedProductData V H) : Type _ :=
  chapter02IdeleSubgroup D

/-- The finite support of an idele away from the prescribed integral subgroups. -/
def chapter02IdeleSupport
    {V : Type u} {H : V → Type v} [∀ x, CommGroup (H x)]
    (D : Chapter02RestrictedProductData V H) (x : chapter02Ideles D) : Set V :=
  {v | D.isFinite v ∧ x.1 v ∉ D.integral v}

theorem chapter02IdeleSupport_finite
    {V : Type u} {H : V → Type v} [∀ x, CommGroup (H x)]
    (D : Chapter02RestrictedProductData V H) (x : chapter02Ideles D) :
    (chapter02IdeleSupport D x).Finite := by
  exact x.2

theorem chapter02_idele_mem_integral_iff_not_mem_support
    {V : Type u} {H : V → Type v} [∀ x, CommGroup (H x)]
    (D : Chapter02RestrictedProductData V H) (x : chapter02Ideles D) (v : V) :
    D.isFinite v → (x.1 v ∈ D.integral v ↔ v ∉ chapter02IdeleSupport D x) := by
  intro hv
  simp [chapter02IdeleSupport, hv]

/-- The local maps and finite ramification set used to multiply local symbols. -/
structure Chapter02GlobalArtinData
    {V : Type u} {H : V → Type v} [∀ x, CommGroup (H x)]
    (D : Chapter02RestrictedProductData V H) (G : Type w) [CommGroup G] where
  localArtin : ∀ v : V, H v →* G
  decomposition : V → Subgroup G
  local_artin_range : ∀ v : V, (localArtin v).range = decomposition v
  ramified : Finset V
  trivial_on_finite_integral_outside_ramified :
    ∀ {v : V}, D.isFinite v → v ∉ ramified → ∀ x : H v,
      x ∈ D.integral v → localArtin v x = 1
  trivial_at_infinite_outside_ramified :
    ∀ {v : V}, ¬ D.isFinite v → v ∉ ramified → ∀ x : H v, localArtin v x = 1

@[ext]
theorem Chapter02GlobalArtinData.ext
    {V : Type u} {H : V → Type v} [∀ x, CommGroup (H x)]
    {G : Type w} [CommGroup G] {D : Chapter02RestrictedProductData V H}
    {A B : Chapter02GlobalArtinData D G}
    (hlocal : A.localArtin = B.localArtin)
    (hdecomposition : A.decomposition = B.decomposition)
    (hramified : A.ramified = B.ramified) : A = B := by
  sorry

/-- The finite set on which the product defining global Artin is evaluated. -/
def chapter02GlobalArtinIndexSet
    {V : Type u} {H : V → Type v} [∀ x, CommGroup (H x)]
    {G : Type w} [CommGroup G]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G) (x : chapter02Ideles D) : Finset V := by
  classical
  exact A.ramified ∪ (chapter02IdeleSupport_finite D x).toFinset

/-- The finite product of local Artin factors. -/
def chapter02GlobalArtin
    {V : Type u} {H : V → Type v} [∀ x, CommGroup (H x)]
    {G : Type w} [CommGroup G]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G) (x : chapter02Ideles D) : G :=
  Finset.prod (chapter02GlobalArtinIndexSet A x)
    (fun v => A.localArtin v (x.1 v))

theorem chapter02_global_artin_factor_eq_one_outside_index_set
    {V : Type u} {H : V → Type v} [∀ x, CommGroup (H x)]
    {G : Type w} [CommGroup G]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G) (x : chapter02Ideles D) {v : V}
    (hv : v ∉ chapter02GlobalArtinIndexSet A x) :
    A.localArtin v (x.1 v) = 1 := by
  sorry

theorem chapter02_global_artin_eq_prod_of_contains_all_nontrivial_factors
    {V : Type u} {H : V → Type v} [∀ x, CommGroup (H x)]
    {G : Type w} [CommGroup G]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G) (x : chapter02Ideles D) (S : Finset V)
    (hS : ∀ v : V, v ∉ S → A.localArtin v (x.1 v) = 1) :
    chapter02GlobalArtin A x = Finset.prod S (fun v => A.localArtin v (x.1 v)) := by
  sorry

/-- The global Artin homomorphism on the idele group. -/
noncomputable def chapter02GlobalArtinHom
    {V : Type u} {H : V → Type v} [∀ x, CommGroup (H x)]
    {G : Type w} [CommGroup G]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G) : chapter02Ideles D →* G where
  toFun := chapter02GlobalArtin A
  map_one' := by
    sorry
  map_mul' x y := by
    sorry

@[simp]
theorem chapter02_global_artinHom_apply
    {V : Type u} {H : V → Type v} [∀ x, CommGroup (H x)]
    {G : Type w} [CommGroup G]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G) (x : chapter02Ideles D) :
    chapter02GlobalArtinHom A x = chapter02GlobalArtin A x :=
  rfl

/-- The local factor is the global map on a one-place idele. -/
def chapter02SingleIdele
    {V : Type u} {H : V → Type v} [∀ x, CommGroup (H x)]
    (D : Chapter02RestrictedProductData V H) (v : V) (a : H v) :
    chapter02Ideles D := by
  classical
  refine ⟨fun x => if h : x = v then h ▸ a else 1, ?_⟩
  apply Set.Finite.subset (Set.finite_singleton v)
  intro x hx
  by_contra hne
  have hne' : x ≠ v := by simpa using hne
  have hx' : (1 : H x) ∉ D.integral x := by
    simpa [hne'] using hx.2
  exact hx' (D.integral x).one_mem

theorem chapter02_global_artin_single_idele
    {V : Type u} {H : V → Type v} [∀ x, CommGroup (H x)]
    {G : Type w} [CommGroup G]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G) (v : V) (a : H v) :
    chapter02GlobalArtin A (chapter02SingleIdele D v a) = A.localArtin v a := by
  sorry

/-- The standard open subgroup used to prove continuity of global Artin. -/
def chapter02StandardArtinKernelSubgroup
    {V : Type u} {H : V → Type v} [∀ x, CommGroup (H x)]
    {G : Type w} [CommGroup G]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G) : Subgroup (chapter02Ideles D) := by
  classical
  refine
    { carrier := {x | ∀ v : V,
        if v ∈ A.ramified then x.1 v ∈ (A.localArtin v).ker
        else if D.isFinite v then x.1 v ∈ D.integral v else True}
      one_mem' := by
        intro v
        split_ifs <;> simp
      mul_mem' := by
        sorry
      inv_mem' := by
        sorry }

theorem chapter02_standard_artin_kernel_subgroup_le_kernel
    {V : Type u} {H : V → Type v} [∀ x, CommGroup (H x)]
    {G : Type w} [CommGroup G]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G) :
    chapter02StandardArtinKernelSubgroup A ≤ (chapter02GlobalArtinHom A).ker := by
  sorry

/--
The topology bridge expected from the restricted-product construction in the
adelic chapters.  Its fields state only the topological assertions used here.
DEPENDENCY_GUESS: replace this bridge with the canonical restricted-product
topology once Book 4 is reconciled.
-/
structure Chapter02GlobalArtinTopologyData
    {V : Type u} {H : V → Type v} [∀ x, CommGroup (H x)]
    {G : Type w} [CommGroup G]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G)
    [TopologicalSpace (chapter02Ideles D)] [TopologicalSpace G]
    [∀ x, TopologicalSpace (H x)] where
  standard_open :
    IsOpen (chapter02StandardArtinKernelSubgroup A : Set (chapter02Ideles D))
  local_artin_continuous : ∀ v : V, Continuous (A.localArtin v)

theorem chapter02_global_artin_continuous
    {V : Type u} {H : V → Type v} [∀ x, CommGroup (H x)]
    {G : Type w} [CommGroup G]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G)
    [TopologicalSpace (chapter02Ideles D)] [TopologicalSpace G]
    [∀ x, TopologicalSpace (H x)]
    (T : Chapter02GlobalArtinTopologyData A) :
    Continuous (chapter02GlobalArtinHom A) :=
  by
    sorry

/-- The diagonal localization data for principal ideles. -/
structure Chapter02PrincipalIdeleData
    (K : Type u) [Field K]
    {V : Type v} {H : V → Type w} [∀ x, CommGroup (H x)]
    (D : Chapter02RestrictedProductData V H) where
  localization : ∀ v : V, Kˣ →* H v
  principal : Kˣ →* chapter02Ideles D
  principal_component : ∀ (a : Kˣ) (v : V),
    (principal a).1 v = localization v a

@[ext]
theorem Chapter02PrincipalIdeleData.ext
    {K : Type u} [Field K]
    {V : Type v} {H : V → Type w} [∀ x, CommGroup (H x)]
    {D : Chapter02RestrictedProductData V H}
    {P Q : Chapter02PrincipalIdeleData K D}
    (hlocalization : P.localization = Q.localization)
    (hprincipal : P.principal = Q.principal) : P = Q := by
  sorry

@[simp]
theorem chapter02_principal_idele_component
    {K : Type u} [Field K]
    {V : Type v} {H : V → Type w} [∀ x, CommGroup (H x)]
    {D : Chapter02RestrictedProductData V H}
    (P : Chapter02PrincipalIdeleData K D) (a : Kˣ) (v : V) :
    (P.principal a).1 v = P.localization v a :=
  P.principal_component a v

/-- The principal subgroup in the idele group. -/
abbrev chapter02PrincipalSubgroup
    {K : Type u} [Field K]
    {V : Type v} {H : V → Type w} [∀ x, CommGroup (H x)]
    {D : Chapter02RestrictedProductData V H}
    (P : Chapter02PrincipalIdeleData K D) :
    Subgroup (chapter02Ideles D) :=
  P.principal.range

theorem chapter02_principal_subgroup_mem_iff
    {K : Type u} [Field K]
    {V : Type v} {H : V → Type w} [∀ x, CommGroup (H x)]
    {D : Chapter02RestrictedProductData V H}
    (P : Chapter02PrincipalIdeleData K D) (x : chapter02Ideles D) :
    x ∈ chapter02PrincipalSubgroup P ↔ ∃ a : Kˣ, P.principal a = x :=
  Iff.rfl

/-- The idele class group `C_K = I_K / Kˣ`, in the chosen abstract model. -/
abbrev chapter02IdeleClassGroup
    {K : Type u} [Field K]
    {V : Type v} {H : V → Type w} [∀ x, CommGroup (H x)]
    {D : Chapter02RestrictedProductData V H}
    (P : Chapter02PrincipalIdeleData K D) : Type _ :=
  chapter02Ideles D ⧸ chapter02PrincipalSubgroup P

/-- The quotient map from ideles to idele classes. -/
def chapter02IdeleClassProjection
    {K : Type u} [Field K]
    {V : Type v} {H : V → Type w} [∀ x, CommGroup (H x)]
    {D : Chapter02RestrictedProductData V H}
    (P : Chapter02PrincipalIdeleData K D) :
    chapter02Ideles D →* chapter02IdeleClassGroup P :=
  QuotientGroup.mk' (chapter02PrincipalSubgroup P)

theorem chapter02_idele_class_projection_eq_iff
    {K : Type u} [Field K]
    {V : Type v} {H : V → Type w} [∀ x, CommGroup (H x)]
    {D : Chapter02RestrictedProductData V H}
    (P : Chapter02PrincipalIdeleData K D) (x y : chapter02Ideles D) :
    chapter02IdeleClassProjection P x = chapter02IdeleClassProjection P y ↔
      ∃ z ∈ chapter02PrincipalSubgroup P, x * z = y := by
  change QuotientGroup.mk' (chapter02PrincipalSubgroup P) x =
      QuotientGroup.mk' (chapter02PrincipalSubgroup P) y ↔
        ∃ z ∈ chapter02PrincipalSubgroup P, x * z = y
  exact QuotientGroup.mk'_eq_mk' (chapter02PrincipalSubgroup P)

end

end LastLib.Book06GlobalClassFieldTheory.Chapter02
