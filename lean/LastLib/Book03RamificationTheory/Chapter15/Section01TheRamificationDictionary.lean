import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.Section05HigherRamificationBoundary
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.Topology.Basic

namespace LastLib.Book03RamificationTheory.Chapter15

noncomputable section

universe uG

open scoped BigOperators
open Ideal

/-! ## 15.1. Fields cut out by finite actions -/

/- The action-to-field interface is deliberately stated before the older
   finite-filtration compatibility layer below.  Continuity is represented by
   openness of the kernel, while the fixed-field construction itself only
   needs the finite Galois ambient extension. -/
structure Chapter15FiniteAction
    (Γ X : Type*) [Group Γ] [Finite X] [TopologicalSpace Γ] where
  action : Γ →* Equiv.Perm X
  kernel_open : IsOpen (action.ker : Set Γ)

def chapter15FiniteActionCutoutField
    {K L X : Type*} [Field K] [Field L] [Algebra K L]
    (ρ : Gal(L / K) →* Equiv.Perm X) : IntermediateField K L :=
  IntermediateField.fixedField ρ.ker

theorem chapter15_finite_action_cutout_field_is_fixed_field
    {K L X : Type*} [Field K] [Field L] [Algebra K L]
    (ρ : Gal(L / K) →* Equiv.Perm X) :
    chapter15FiniteActionCutoutField ρ = IntermediateField.fixedField ρ.ker := by
  sorry

structure Chapter15FiniteActionFieldData
    (K L X : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite X] where
  action : Gal(L / K) →* Equiv.Perm X
  cutout : IntermediateField K L
  cutout_eq_fixed_field :
    cutout = chapter15FiniteActionCutoutField action

theorem chapter15_finite_action_galois_group_equiv_image
    {K L X : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite X]
    (ρ : Gal(L / K) →* Equiv.Perm X) :
    Nonempty
      (Gal(chapter15FiniteActionCutoutField ρ / K) ≃* MonoidHom.range ρ) := by
  sorry

/-! The declarations below preserve the finite lower-filtration API used by
    later synthesis chapters.  They are not the organizing interface of
    Chapter 15; the source-facing cutout and arithmetic interfaces live in
    this chapter's four section files. -/

/--
A finite lower-numbered filtration of a finite group.  The cutoff is part of the
interface so that all displayed sums in this chapter are honest finite sums; the
value at and after the cutoff is the trivial subgroup.
-/
structure Chapter15LowerRamificationFiltration (G : Type*) [Group G] [Finite G] where
  /-- The ambient group is `G₋₁`; `group 0` is the inertia group. -/
  group : ℕ → Subgroup G
  descending : ∀ {i j : ℕ}, i ≤ j → group j ≤ group i
  normal : ∀ i : ℕ, (group i).Normal
  cutoff : ℕ
  trivial_at_cutoff : ∀ {i : ℕ}, cutoff ≤ i → group i = ⊥

/-- The successive quotient is a genuine group quotient, not merely a quotient of sets. -/
theorem chapter15_layer_normal
    {G : Type*} [Group G] [Finite G]
    (F : Chapter15LowerRamificationFiltration G) (i : ℕ) :
    ((F.group (i + 1)).subgroupOf (F.group i)).Normal := by
  apply (Subgroup.normal_subgroupOf_iff
    (F.descending (Nat.le_succ i))).2
  intro h k hh hk
  exact (F.normal (i + 1)).conj_mem h hh k

/-- The lower layer `G_i / G_(i+1)`, with the subgroup inclusion made explicit. -/
def chapter15Layer
    {G : Type*} [Group G] [Finite G]
    (F : Chapter15LowerRamificationFiltration G) (i : ℕ) : Type _ := by
  letI : ((F.group (i + 1)).subgroupOf (F.group i)).Normal :=
    chapter15_layer_normal F i
  exact F.group i ⧸ (F.group (i + 1)).subgroupOf (F.group i)

/-- The residue-symmetry quotient `G / G₀`. -/
def chapter15ResidueQuotient
    {G : Type*} [Group G] [Finite G]
    (F : Chapter15LowerRamificationFiltration G) : Type _ := by
  letI : (F.group 0).Normal := F.normal 0
  exact G ⧸ F.group 0

instance chapter15ResidueQuotientGroup
    {G : Type*} [Group G] [Finite G]
    (F : Chapter15LowerRamificationFiltration G) :
    Group (chapter15ResidueQuotient F) := by
  letI : (F.group 0).Normal := F.normal 0
  change Group (G ⧸ F.group 0)
  infer_instance

instance chapter15LayerGroup
    {G : Type*} [Group G] [Finite G]
    (F : Chapter15LowerRamificationFiltration G) (i : ℕ) :
    Group (chapter15Layer F i) := by
  letI : ((F.group (i + 1)).subgroupOf (F.group i)).Normal :=
    chapter15_layer_normal F i
  change Group (F.group i ⧸ (F.group (i + 1)).subgroupOf (F.group i))
  infer_instance

/-- The quotient `G/G₀` is identified with the Galois group of the residue extension. -/
def chapter15ResidueFieldSymmetry
    {G k l : Type*} [Group G] [Finite G] [Field k] [Field l]
    [Algebra k l]
    (F : Chapter15LowerRamificationFiltration G) : Prop :=
  Nonempty (chapter15ResidueQuotient F ≃* Gal(l / k))

/-- The tame quotient `G₀/G₁` is cyclic. -/
def chapter15TameLayerIsCyclic
    {G : Type*} [Group G] [Finite G]
    (F : Chapter15LowerRamificationFiltration G) : Prop :=
  letI : ((F.group 1).subgroupOf (F.group 0)).Normal :=
    chapter15_layer_normal F 0
  IsCyclic (chapter15Layer F 0)

/- The tame layer is not merely cyclic: its order is prime to the residue
   characteristic exponent. -/
def chapter15TameLayerPrimeToCharacteristic
    {G : Type*} [Group G] [Finite G]
    (p : ℕ) (F : Chapter15LowerRamificationFiltration G) : Prop :=
  Nat.Coprime p (Nat.card (chapter15Layer F 0))

/--
The positive-depth layers are modelled as additive vector spaces over the prime
field `ZMod p`.  `Additive` changes the multiplicative quotient notation into
the additive group used by the standard ramification dictionary.
-/
def chapter15WildLayerIsAdditiveOver
    {G : Type uG} {k : Type*} [Group G] [Finite G] [Field k]
    (p i : ℕ) [CharP k p]
(F : Chapter15LowerRamificationFiltration G) : Prop :=
  1 ≤ i ∧
    ∃ V : Type uG, ∃ hV : AddCommGroup V,
      (letI : AddCommGroup V := hV
        ∃ hM : Module (ZMod p) V,
          (letI : Module (ZMod p) V := hM
          Nonempty (Additive (chapter15Layer F i) ≃+ V)))

/- Mathlib records characteristic zero as `CharP k 0`, whereas the book's
characteristic exponent is `1` in that case. -/
def chapter15CharacteristicExponent
    (k : Type*) [Field k] (p : ℕ) : Prop :=
  (p = 1 ∧ CharP k 0) ∨ (1 < p ∧ CharP k p)

/--
The structural part of the finite-Galois ramification dictionary.  The
separability field is explicit because the clean residue quotient and the
cyclic/additive layer statements use it.
-/
structure Chapter15RamificationDictionary
    {G k l : Type*} [Group G] [Finite G] [Field k] [Field l]
    [Algebra k l] (p : ℕ)
    (F : Chapter15LowerRamificationFiltration G) where
  characteristic_exponent : chapter15CharacteristicExponent k p
  residue_extension_separable : Algebra.IsSeparable k l
  residue_symmetry : chapter15ResidueFieldSymmetry (k := k) (l := l) F
  tame_layer_cyclic : chapter15TameLayerIsCyclic F
  tame_layer_prime_to_characteristic :
    chapter15TameLayerPrimeToCharacteristic p F
  wild_layers_additive : ∀ i : ℕ, 1 ≤ i →
    (p = 1 ∧ F.group i = ⊥) ∨
      ∃ hchar : CharP k p,
        (letI : CharP k p := hchar
         chapter15WildLayerIsAdditiveOver (k := k) p i F)

/-- The lower ramification group from the earlier valuation-ring interface. -/
abbrev chapter15LowerRamificationGroup
    (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (i : ℕ) :
    Subgroup
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup K A) :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup K A (i + 1)

/-- In the zero-based Chapter 15 indexing, inertia is lower group `G₀`. -/
abbrev chapter15InertiaGroup
    (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) :
    Subgroup
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup K A) :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05InertiaGroup K A

/-- Membership in a lower group is exactly the congruence on all integral elements. -/
theorem chapter15_lower_ramification_group_mem_iff
    {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (i : ℕ)
    (σ :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup K A) :
    σ ∈ chapter15LowerRamificationGroup K A i ↔
      ∀ x : A, (σ • x - x) ∈ (IsLocalRing.maximalIdeal A) ^ (i + 1) := by
  rfl

theorem chapter15_first_lower_group_eq_inertia
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) :
    chapter15LowerRamificationGroup K A 0 = chapter15InertiaGroup K A := by
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FirstRamificationGroup_eq_inertia A

/-- Lower numbering restricts to a subgroup by intersection with every lower group. -/
noncomputable def chapter15RestrictLowerFiltration
    {G : Type*} [Group G] [Finite G]
    (F : Chapter15LowerRamificationFiltration G) (H : Subgroup G) :
    Chapter15LowerRamificationFiltration H :=
  { group := fun i => (F.group i).comap H.subtype
    descending := by
      intro i j hij
      exact Subgroup.comap_mono (F.descending hij)
    normal := by
      intro i
      exact (F.normal i).comap H.subtype
    cutoff := F.cutoff
    trivial_at_cutoff := by
      intro i hi
      rw [F.trivial_at_cutoff hi]
      exact (MonoidHom.comap_bot H.subtype).trans (Subgroup.ker_subtype H) }

@[simp]
theorem chapter15RestrictLowerFiltration_group
    {G : Type*} [Group G] [Finite G]
    (F : Chapter15LowerRamificationFiltration G) (H : Subgroup G) (i : ℕ) :
    (chapter15RestrictLowerFiltration F H).group i =
      (F.group i).comap H.subtype :=
  rfl

/- The quotient-compatibility predicates are part of the dictionary because
   later synthesis sections import this foundational interface directly. -/

/-- The lower-numbering compatibility condition that fails for arbitrary quotients. -/
def chapter15LowerQuotientCompatibility
    {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]
    (F : Chapter15LowerRamificationFiltration G)
    (FQ : Chapter15LowerRamificationFiltration Q)
    (π : G →* Q) : Prop :=
  ∀ i : ℕ, (F.group i).map π = FQ.group i

/-- The upper-numbering pushforward along a quotient map. -/
def chapter15UpperPushforward
    {G Q : Type*} [Group G] [Group Q]
    (U : ℝ → Subgroup G) (π : G →* Q) (r : ℝ) : Subgroup Q :=
  (U r).map π

/-
The Herbrand quotient interface: upper groups are compared after pushing them
forward, whereas lower groups require the stronger compatibility condition above.
-/
def chapter15UpperQuotientCompatibility
    {G Q : Type*} [Group G] [Group Q]
    (U : ℝ → Subgroup G) (UQ : ℝ → Subgroup Q) (π : G →* Q) : Prop :=
  ∀ r : ℝ, chapter15UpperPushforward U π r = UQ r

/-- The rational index weight used by the Herbrand integral. -/
def chapter15IndexWeight
    {G : Type*} [Group G] [Finite G]
    (F : Chapter15LowerRamificationFiltration G) (i : ℕ) : ℚ :=
  (Nat.card (F.group i) : ℚ) / (Nat.card (F.group 0) : ℚ)

/-- The finite lower-displacement sum `∑ᵢ (|Gᵢ| - 1)`. -/
def chapter15DifferentDisplacementSum
    {G : Type*} [Group G] [Finite G]
    (F : Chapter15LowerRamificationFiltration G) : ℕ :=
  ∑ i ∈ Finset.range F.cutoff, (Nat.card (F.group i) - 1)

/-- The residue-degree-weighted displacement sum for the discriminant exponent. -/
def chapter15DiscriminantDisplacementSum
    {G : Type*} [Group G] [Finite G]
    (F : Chapter15LowerRamificationFiltration G) (f : ℕ) : ℕ :=
  f * chapter15DifferentDisplacementSum F

/-- The Herbrand function, extended by the identity on negative inputs. -/
noncomputable def chapter15HerbrandFunction
    {G : Type*} [Group G] [Finite G]
    (F : Chapter15LowerRamificationFiltration G) (u : ℝ) : ℝ :=
  if u ≤ 0 then u else
    let t : ℝ := u
    let n : ℕ := Int.toNat ⌊t⌋
    (∑ i ∈ Finset.range n, (chapter15IndexWeight F (i + 1) : ℝ)) +
      (t - n) * (chapter15IndexWeight F (n + 1) : ℝ)

/-- Upper break coordinates are the Herbrand values of lower break coordinates. -/
def chapter15UpperBreak
    {G : Type*} [Group G] [Finite G]
    (F : Chapter15LowerRamificationFiltration G) (i : ℕ) : ℝ :=
  chapter15HerbrandFunction F i

/-- Fixed vectors for a subgroup in a linear representation. -/
def chapter15FixedSubspace
    {k G V : Type*} [Semiring k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (H : Subgroup G) : Submodule k V :=
  { carrier := {v | ∀ h : H, ρ h v = v}
    zero_mem' := by
      intro h
      simp
    add_mem' := by
      intro v w hv hw h
      rw [map_add, hv h, hw h]
    smul_mem' := by
      intro c v hv h
      rw [map_smul, hv h] }

/-- The codimension moved by a subgroup. -/
def chapter15Codimension
    {k G V : Type*} [DivisionRing k] [Group G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]
    (ρ : Representation k G V) (H : Subgroup G) : ℕ :=
  Module.finrank k V - Module.finrank k (chapter15FixedSubspace ρ H)

/-- The Artin conductor in the lower-numbered dictionary. -/
def chapter15ArtinConductor
    {k G V : Type*} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (F : Chapter15LowerRamificationFiltration G)
    (ρ : Representation k G V) : ℚ :=
  ∑ i ∈ Finset.range F.cutoff,
    (Nat.card (F.group i) : ℚ) / Nat.card (F.group 0) *
      (chapter15Codimension ρ (F.group i) : ℚ)

/-- The tame codimension, i.e. the zeroth summand of the Artin conductor. -/
def chapter15TameConductor
    {k G V : Type*} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (F : Chapter15LowerRamificationFiltration G)
    (ρ : Representation k G V) : ℚ :=
  (chapter15Codimension ρ (F.group 0) : ℚ)

/-- The positive-depth weighted area, i.e. the Swan conductor. -/
def chapter15SwanConductor
    {k G V : Type*} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (F : Chapter15LowerRamificationFiltration G)
    (ρ : Representation k G V) : ℚ :=
  ∑ i ∈ (Finset.range F.cutoff).filter (fun i => 1 ≤ i),
    (Nat.card (F.group i) : ℚ) / Nat.card (F.group 0) *
      (chapter15Codimension ρ (F.group i) : ℚ)

/-- Mathlib's different ideal, retained under the Chapter 15 name. -/
def chapter15DifferentIdeal
    (A B : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Algebra A B] [IsIntegrallyClosed A] [IsDedekindDomain B]
    [Module.IsTorsionFree A B] : Ideal B :=
  differentIdeal A B

/-- The downstairs ideal obtained by applying the relative ideal norm to the different. -/
noncomputable def chapter15RelativeDiscriminantIdeal
    (A B : Type*) [CommRing A] [CommRing B]
    [Algebra A B] [IsDedekindDomain A] [IsDedekindDomain B]
    [Module.Finite A B] [Module.IsTorsionFree A B] : Ideal A :=
  Ideal.relNorm A (chapter15DifferentIdeal A B)

/-- The different exponent at a selected prime. -/
noncomputable def chapter15DifferentExponent
    (A B : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Algebra A B] [IsIntegrallyClosed A] [IsDedekindDomain B]
    [Module.IsTorsionFree A B] (P : Ideal B) [P.IsPrime] : ℕ :=
  multiplicity P (chapter15DifferentIdeal A B)

/-- The discriminant exponent at a selected prime downstairs. -/
noncomputable def chapter15DiscriminantExponent
    (A B : Type*) [CommRing A] [CommRing B]
    [Algebra A B] [IsDedekindDomain A] [IsDedekindDomain B]
    [Module.Finite A B] [Module.IsTorsionFree A B] (p : Ideal A) [p.IsPrime] : ℕ :=
  multiplicity p (chapter15RelativeDiscriminantIdeal A B)

/-- The quotient of the residue action identifies `G/G₀` with residue-field symmetry. -/
theorem chapter15_residue_quotient_equiv_of_kernel
    {G Q : Type*} [Group G] [Finite G] [Group Q]
    (F : Chapter15LowerRamificationFiltration G) (ρ : G →* Q)
    (hker : MonoidHom.ker ρ = F.group 0)
    (hsurj : Function.Surjective ρ) :
    Nonempty (chapter15ResidueQuotient F ≃* Q) := by
  sorry

/-- The table's zeroth term is the tame codimension. -/
theorem chapter15_artin_conductor_eq_tame_add_swan
    {k G V : Type*} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (F : Chapter15LowerRamificationFiltration G)
    (ρ : Representation k G V) :
    chapter15ArtinConductor F ρ =
      chapter15TameConductor F ρ + chapter15SwanConductor F ρ := by
  sorry

end

end LastLib.Book03RamificationTheory.Chapter15
