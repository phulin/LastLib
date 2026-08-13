import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.KummerExtension
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Topology.Algebra.Group.Compact
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import LastLib.Book06GlobalClassFieldTheory.Chapter01.Dependencies
import LastLib.Book06GlobalClassFieldTheory.Chapter01.Section01OneGaloisActionSeenAtEveryPlace
import LastLib.Book06GlobalClassFieldTheory.Chapter05.Section01TheReciprocityIsomorphism

namespace LastLib.Book06GlobalClassFieldTheory.Chapter06

open scoped BigOperators IsMulCommutative

noncomputable section

universe uG uA

/-! # Shared interfaces for Book 6, Chapter 6

The pinned Mathlib snapshot has the ingredients used below (finite cyclic
modules, roots of unity, quotient groups, Galois groups, and continuous
cohomology), but it does not define the global idele class group or the
Poitou--Tate calculation for number fields.  The small structures in this
file keep those book-facing constructions explicit so that later proofs can
replace them by the canonical implementations without changing the chapter's
statements.
-/

/- The finite coefficient module A_n = ZMod n, with its additive structure. -/
abbrev Chapter06A (n : ℕ) : Type := ZMod n

/- The trivial action of a group on an additive coefficient module. -/
def chapter06TrivialAction
    (G M : Type*) [Group G] [AddCommGroup M] : G → M →+ M :=
  fun _ ↦ AddMonoidHom.id M

/- The Cartier-dual coefficient at a field. Its underlying group is the
subgroup of nth roots of unity in the unit group. -/
abbrev Chapter06CartierDual (K : Type*) [Field K] (n : ℕ) :=
  rootsOfUnity n K

/- The rational circle used for the target of the global invariant sum. -/
abbrev Chapter06QModZ : Type :=
  ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)

/- The n-torsion subgroup of Q/Z. It is the book-facing realization of
(1/n)Z/Z; using the torsion subgroup avoids choosing representatives in Q. -/
def chapter06OneOverNTorsion (n : ℕ) : AddSubgroup Chapter06QModZ where
  carrier := {x | n • x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change n • (x + y) = 0
    rw [nsmul_add, hx, hy, zero_add]
  neg_mem' := by
    intro x hx
    change n • (-x) = 0
    have hneg : ∀ m : ℕ, m • (-x) = -(m • x) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [succ_nsmul, succ_nsmul, ih, neg_add]
    rw [hneg n, hx, neg_zero]

/- 1/n Z / Z, represented as the n-torsion of Q/Z. -/
abbrev Chapter06OneOverNModOne (n : ℕ) : Type :=
  chapter06OneOverNTorsion n

/- The natural inclusion of the local invariant target into Q/Z. -/
def chapter06InvariantTargetInclusion (n : ℕ) :
    Chapter06OneOverNModOne n →+ Chapter06QModZ :=
  { toFun := fun x ↦ x.1
    map_zero' := rfl
    map_add' := by intro x y; rfl }

/- The standard finite target is canonically ZMod n. -/
noncomputable def chapter06_oneOverNModOne_equiv_zmod
    (n : ℕ) (hn : 0 < n) :
    Chapter06OneOverNModOne n ≃+ ZMod n := by
  sorry

/- The subgroup of nth powers in the multiplicative group of a field. -/
abbrev Chapter06NthPowerSubgroup (F : Type*) [Field F] (n : ℕ) : Subgroup Fˣ :=
  (powMonoidHom n : Fˣ →* Fˣ).range

/- Kummer classes, written additively so that they can be paired with
A_n-cohomology classes. Its underlying multiplicative quotient is the
canonical Fˣ/Fˣⁿ. -/
abbrev Chapter06KummerClassGroup (F : Type*) [Field F] (n : ℕ) :=
  Additive (Fˣ ⧸ Chapter06NthPowerSubgroup F n)

/- The class of a unit in Fˣ/Fˣⁿ. -/
def chapter06KummerClassMk
    {F : Type*} [Field F] (n : ℕ) (x : Fˣ) : Chapter06KummerClassGroup F n :=
  Additive.ofMul (QuotientGroup.mk' (Chapter06NthPowerSubgroup F n) x)

/- Restriction of Kummer classes along a field embedding. -/
noncomputable def chapter06KummerRestriction
    {K F : Type*} [Field K] [Field F] (n : ℕ) (f : K →+* F) :
    Chapter06KummerClassGroup K n →+ Chapter06KummerClassGroup F n :=
  let q : Kˣ ⧸ Chapter06NthPowerSubgroup K n →*
      Fˣ ⧸ Chapter06NthPowerSubgroup F n :=
    QuotientGroup.map (Chapter06NthPowerSubgroup K n)
      (Chapter06NthPowerSubgroup F n) (Units.map f.toMonoidHom) (by
        intro x hx
        rcases hx with ⟨y, rfl⟩
        exact ⟨Units.map f.toMonoidHom y, by simp⟩)
  q.toAdditive

theorem chapter06_kummer_restriction_mk
    {K F : Type*} [Field K] [Field F] (n : ℕ) (f : K →+* F) (x : Kˣ) :
    chapter06KummerRestriction n f (chapter06KummerClassMk n x) =
      chapter06KummerClassMk n (Units.map f.toMonoidHom x) := by
  sorry

/- A continuous finite-image character of a topological group. -/
structure Chapter06ContinuousFiniteImageCharacter
    (G : Type*) (B : Type*) [Group G] [CommGroup B]
    [TopologicalSpace G] [TopologicalSpace B] where
  hom : G →* B
  continuous' : Continuous hom
  finite_image : Set.Finite (Set.range hom)

instance Chapter06ContinuousFiniteImageCharacter.instCoeFun
    {G B : Type*} [Group G] [CommGroup B]
    [TopologicalSpace G] [TopologicalSpace B] :
    CoeFun (Chapter06ContinuousFiniteImageCharacter G B) (fun _ ↦ G → B) :=
  ⟨fun χ ↦ χ.hom⟩

/- A finite-order complex-valued character of an idele class group. -/
structure Chapter06ContinuousFiniteOrderCharacter
    (C : Type*) [CommGroup C] [TopologicalSpace C] where
  hom : C →* ℂˣ
  continuous' : Continuous hom
  finite_order : ∃ n : ℕ, 0 < n ∧ ∀ c, hom c ^ n = 1

instance Chapter06ContinuousFiniteOrderCharacter.instCoeFun
    {C : Type*} [CommGroup C] [TopologicalSpace C] :
    CoeFun (Chapter06ContinuousFiniteOrderCharacter C) (fun _ ↦ C → ℂˣ) :=
  ⟨fun χ ↦ χ.hom⟩

/- The kernel of a continuous finite-order character. -/
abbrev chapter06CharacterKernel
    {C : Type*} [CommGroup C] [TopologicalSpace C]
    (χ : Chapter06ContinuousFiniteOrderCharacter C) : Subgroup C :=
  χ.hom.ker

/- The topological idele class group interface used by the chapter.  The
   principal map is required to be trivial because the carrier is already
   the quotient by principal ideles. -/
class Chapter06IdeleClassGroup (K : Type*) [Field K] [NumberField K] where
  carrier : Type*
  [carrierCommGroup : CommGroup carrier]
  [carrierTopology : TopologicalSpace carrier]
  [carrierTopologicalGroup : IsTopologicalGroup carrier]
  [carrierLocallyCompact : LocallyCompactSpace carrier]
  [carrierT2Space : T2Space carrier]
  principal : Kˣ →* carrier
  principal_trivial : principal = 1

attribute [instance_reducible] Chapter06IdeleClassGroup.carrierCommGroup
  Chapter06IdeleClassGroup.carrierTopology

attribute [instance] Chapter06IdeleClassGroup.carrierCommGroup
  Chapter06IdeleClassGroup.carrierTopology
  Chapter06IdeleClassGroup.carrierTopologicalGroup
  Chapter06IdeleClassGroup.carrierLocallyCompact
  Chapter06IdeleClassGroup.carrierT2Space

/- The carrier denoted C_K in the book. -/
abbrev Chapter06C (K : Type*) [Field K] [NumberField K]
    [Chapter06IdeleClassGroup K] : Type :=
  (inferInstance : Chapter06IdeleClassGroup K).carrier

/- The principal idele class map. -/
abbrev chapter06PrincipalIdeleClass
    (K : Type*) [Field K] [NumberField K] [Chapter06IdeleClassGroup K] :
    Kˣ →* Chapter06C K :=
  (inferInstance : Chapter06IdeleClassGroup K).principal

/- A character of C_K together with the fact that it is trivial on
principal ideles. -/
structure Chapter06IdeleClassCharacter
    (K : Type*) [Field K] [NumberField K] [Chapter06IdeleClassGroup K] where
  hom : Chapter06C K →* ℂˣ
  continuous' : Continuous hom
  finite_order : ∃ n : ℕ, 0 < n ∧ ∀ c, hom c ^ n = 1
  trivial_on_principal : hom.comp (chapter06PrincipalIdeleClass K) = 1

instance Chapter06IdeleClassCharacter.instCoeFun
    (K : Type*) [Field K] [NumberField K] [Chapter06IdeleClassGroup K] :
    CoeFun (Chapter06IdeleClassCharacter K) (fun _ ↦ Chapter06C K → ℂˣ) :=
  ⟨fun χ ↦ χ.hom⟩

/- A trivial additive coefficient action, expressed without selecting a
particular implementation of the Galois cochain complex. -/
def Chapter06TrivialCoefficient (G M : Type*) [Group G] [AddCommGroup M] : Prop :=
  ∀ g : G, chapter06TrivialAction G M g = AddMonoidHom.id M

theorem chapter06_trivial_coefficient_module
    (G M : Type*) [Group G] [AddCommGroup M] :
    Chapter06TrivialCoefficient G M := by
  intro g
  rfl

theorem chapter06_A_n_trivial_action
    (G : Type*) [Group G] (n : ℕ) :
    Chapter06TrivialCoefficient G (Chapter06A n) :=
  chapter06_trivial_coefficient_module G (Chapter06A n)

/- Continuous A-valued characters of a topological group, viewed as the
degree-one cohomology of the trivial action. -/
noncomputable def chapter06ContinuousACharacterSubgroup
    (G : Type uG) (A : Type uA) [Group G] [AddCommGroup A]
    [TopologicalSpace G] [TopologicalSpace A] [IsTopologicalAddGroup A] :
    Subgroup (G →* Multiplicative A) where
  carrier := {f | Continuous f}
  one_mem' := by exact continuous_const
  mul_mem' := by
    intro f g hf hg
    exact hf.mul hg
  inv_mem' := by
    intro f hf
    exact hf.inv

/- The global/local H1 model for a trivial coefficient module. -/
abbrev Chapter06ContinuousACharacter
    (G : Type uG) (A : Type uA) [Group G] [AddCommGroup A]
    [TopologicalSpace G] [TopologicalSpace A] [IsTopologicalAddGroup A] :
    Type (max uG uA) :=
  Additive (↥(chapter06ContinuousACharacterSubgroup G A))

/- The absolute Galois group attached to a chosen separable closure. -/
abbrev Chapter06AbsoluteGaloisGroup
    (K Ks : Type*) [Field K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks] :=
  Gal(Ks / K)

/- The local place kinds relevant to the archimedean clauses of the theorem. -/
inductive Chapter06PlaceKind
  | finite
  | real
  | complex
  deriving DecidableEq

/- A restricted product represented as the additive subgroup of the full
product whose exceptional set is finite. The distinguished subgroups are the
unramified local terms. -/
def chapter06RestrictedProductSubgroup
    (ι : Type*) (H : ι → Type*)
    [∀ i, AddCommGroup (H i)] (U : ∀ i, AddSubgroup (H i)) :
    AddSubgroup (∀ i, H i) where
  carrier := {x | {i | x i ∉ U i}.Finite}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    refine (hx.union hy).subset ?_
    intro i hi
    change x i ∉ U i ∨ y i ∉ U i
    by_cases hxi : x i ∉ U i
    · exact Or.inl hxi
    by_cases hyi : y i ∉ U i
    · exact Or.inr hyi
    · exfalso
      apply hi
      exact (U i).add_mem (not_not.mp hxi) (not_not.mp hyi)
  neg_mem' := by
    intro x hx
    have hset : {i | -x i ∉ U i} = {i | x i ∉ U i} := by
      ext i
      simp
    simpa [hset] using hx

/- The restricted-product type. -/
abbrev Chapter06RestrictedProduct
    (ι : Type*) (H : ι → Type*)
    [∀ i, AddCommGroup (H i)] (U : ∀ i, AddSubgroup (H i)) :=
  ↥(chapter06RestrictedProductSubgroup ι H U)

instance Chapter06RestrictedProduct.instCoeFun
    {ι : Type*} {H : ι → Type*} [∀ i, AddCommGroup (H i)]
    {U : ∀ i, AddSubgroup (H i)} :
    CoeFun (Chapter06RestrictedProduct ι H U) (fun _ => ∀ i, H i) :=
  ⟨fun c => c.1⟩

@[ext]
theorem chapter06RestrictedProduct_ext
    {ι : Type*} {H : ι → Type*} [∀ i, AddCommGroup (H i)]
    {U : ∀ i, AddSubgroup (H i)}
    {x y : Chapter06RestrictedProduct ι H U}
    (h : ∀ i, x i = y i) : x = y := by
  apply Subtype.ext
  exact funext h

/- The finite exceptional set of a restricted-product element. -/
theorem chapter06RestrictedProductExceptionalFinite
    {ι : Type*} {H : ι → Type*} [∀ i, AddCommGroup (H i)]
    {U : ∀ i, AddSubgroup (H i)}
    (c : Chapter06RestrictedProduct ι H U) :
    Set.Finite {i | c i ∉ U i} :=
  c.property

/- Finite-support sum attached to a restricted product. -/
def chapter06RestrictedProductSum
    {ι : Type*} {H : ι → Type*} [∀ i, AddCommGroup (H i)]
    {U : ∀ i, AddSubgroup (H i)} {B : Type*} [AddCommGroup B]
    (c : Chapter06RestrictedProduct ι H U) (φ : ∀ i, H i → B)
    (_hφ : ∀ i (x : H i), x ∈ U i → φ i x = 0) : B :=
  Finset.sum (chapter06RestrictedProductExceptionalFinite c).toFinset
    (fun i => φ i (c i))

/- Finite-support product attached to a restricted product. -/
def chapter06RestrictedProductProduct
    {ι : Type*} {H : ι → Type*} [∀ i, AddCommGroup (H i)]
    {U : ∀ i, AddSubgroup (H i)} {B : Type*} [CommGroup B]
    (c : Chapter06RestrictedProduct ι H U) (φ : ∀ i, H i → B)
    (_hφ : ∀ i (x : H i), x ∈ U i → φ i x = 1) : B :=
  Finset.prod (chapter06RestrictedProductExceptionalFinite c).toFinset
    (fun i => φ i (c i))

/- Exactness at the middle of a sequence of additive groups. -/
def Chapter06ExactAtMiddle
    {A B C : Type*} [AddZeroClass A] [AddZeroClass B] [AddZeroClass C]
    (f : A →+ B) (g : B →+ C) : Prop :=
  Set.range f = g ⁻¹' ({0} : Set C)

/- A finite abelian extension inside a chosen separable closure, with its
idele-class norm map exposed as data. -/
structure Chapter06FiniteAbelianExtension
    (K Ks C : Type*) [Field K] [NumberField K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks]
    [CommGroup C] where
  field : IntermediateField K Ks
  [finite : FiniteDimensional K field]
  [abelian : IsAbelianGalois K field]
  galoisFinite : Finite (Gal(field / K))
  classGroup : Type
  [classGroupCommGroup : CommGroup classGroup]
  normMap : classGroup →* C

attribute [instance] Chapter06FiniteAbelianExtension.classGroupCommGroup

/- A canonical finite abelian extension package.  Unlike the chapter-facing
   placeholder above, this data is tied to the earlier global norm map, the
   actual local Artin maps on completions, and the finite class-formation
   input used by global reciprocity. -/
structure Chapter06FiniteAbelianExtensionData
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L] where
  normData : LastLib.Book06GlobalClassFieldTheory.Chapter01.GlobalNormInterface K L
  localArtinData :
    LastLib.Book06GlobalClassFieldTheory.Chapter01.FiniteLevelArtinData K L
  classFormationData :
    LastLib.Book06GlobalClassFieldTheory.Chapter05.Chapter05ClassFormationInput K L
      (LastLib.Book06GlobalClassFieldTheory.Chapter01.BookIdeleGroup K)
      (LastLib.Book06GlobalClassFieldTheory.Chapter01.BookIdeleGroup L)
      (LastLib.Book06GlobalClassFieldTheory.Chapter01.BookIdeleClassGroup K)
      (LastLib.Book06GlobalClassFieldTheory.Chapter01.BookIdeleClassGroup L)
  classFormation_ideleNorm :
    classFormationData.ideleNorm =
      LastLib.Book06GlobalClassFieldTheory.Chapter01.componentwiseIdeleNorm normData
  classFormation_classNorm :
    classFormationData.classNorm =
      LastLib.Book06GlobalClassFieldTheory.Chapter01.classNorm normData
  classFormation_classMapK :
    classFormationData.classMapK =
      LastLib.Book06GlobalClassFieldTheory.Chapter01.classQuotient (K := K)
  classFormation_classMapL :
    classFormationData.classMapL =
      LastLib.Book06GlobalClassFieldTheory.Chapter01.classQuotient (K := L)
  artin_kernel_eq_norm :
    LastLib.Book06GlobalClassFieldTheory.Chapter01.ArtinKernelIsClassNorm
      localArtinData normData
  artin_surjective :
    Function.Surjective
      (LastLib.Book06GlobalClassFieldTheory.Chapter01.classArtin localArtinData)
  class_artin_eq_class_formation :
    LastLib.Book06GlobalClassFieldTheory.Chapter01.classArtin localArtinData =
      LastLib.Book06GlobalClassFieldTheory.Chapter05.chapter05InputGlobalArtin
        classFormationData

abbrev chapter06CanonicalNormSubgroup
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    (E : Chapter06FiniteAbelianExtensionData K L) :
    Subgroup (LastLib.Book06GlobalClassFieldTheory.Chapter01.BookIdeleClassGroup K) :=
  LastLib.Book06GlobalClassFieldTheory.Chapter01.classNormGroup E.normData

def chapter06CanonicalLocalArtin
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    (E : Chapter06FiniteAbelianExtensionData K L)
    (v : LastLib.Book06GlobalClassFieldTheory.Chapter01.BookPlace K) :
    (LastLib.Book06GlobalClassFieldTheory.Chapter01.BookPlace.completion v)ˣ →*
      LastLib.Book06GlobalClassFieldTheory.Chapter01.GroupAbelianization
        (Gal(L / K)) :=
  E.localArtinData.localArtin v

noncomputable def chapter06CanonicalLocalArtinGalois
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    (E : Chapter06FiniteAbelianExtensionData K L)
    (v : LastLib.Book06GlobalClassFieldTheory.Chapter01.BookPlace K) :
    (LastLib.Book06GlobalClassFieldTheory.Chapter01.BookPlace.completion v)ˣ →*
      Gal(L / K) :=
  (Abelianization.equivOfComm (H := Gal(L / K))).symm.toMonoidHom.comp
      (chapter06CanonicalLocalArtin E v)

noncomputable def chapter06CanonicalClassArtinGalois
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    (E : Chapter06FiniteAbelianExtensionData K L) :
    LastLib.Book06GlobalClassFieldTheory.Chapter01.BookIdeleClassGroup K →*
      Gal(L / K) :=
  (Abelianization.equivOfComm (H := Gal(L / K))).symm.toMonoidHom.comp
      (LastLib.Book06GlobalClassFieldTheory.Chapter01.classArtin E.localArtinData)

/- The enrichment required when the earlier existence theorem supplies a norm
   realization and the local/class-formation data are supplied by the
   preceding reciprocity chapters. -/
structure Chapter06FiniteAbelianExtensionEnrichment
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    (N : LastLib.Book06GlobalClassFieldTheory.Chapter01.GlobalNormInterface K L)
    where
  data : Chapter06FiniteAbelianExtensionData K L
  normData_eq : data.normData = N

instance Chapter06FiniteAbelianExtension.instFiniteDimensional
    (K Ks C : Type*) [Field K] [NumberField K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks] [CommGroup C]
    (E : Chapter06FiniteAbelianExtension K Ks C) :
    FiniteDimensional K E.field :=
  E.finite

instance Chapter06FiniteAbelianExtension.instFiniteGalois
    (K Ks C : Type*) [Field K] [NumberField K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks]
    [CommGroup C] (E : Chapter06FiniteAbelianExtension K Ks C) :
    Finite (Gal(E.field / K)) :=
  E.galoisFinite

/- A cyclic extension is the character-field specialization of a finite
abelian extension. -/
structure Chapter06FiniteCyclicExtension
    (K Ks C : Type*) [Field K] [NumberField K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks]
    [CommGroup C] where
  extension : Chapter06FiniteAbelianExtension K Ks C
  cyclic : IsCyclic (Gal(extension.field / K))

/- The canonical restriction of an automorphism of the chosen separable
   closure to a finite Galois intermediate field. -/
noncomputable def chapter06GaloisRestriction
    {K Ks : Type*} [Field K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] (L : IntermediateField K Ks)
    [FiniteDimensional K L] [IsGalois K L] :
    Gal(Ks / K) →* Gal(L / K) := by
  haveI : Normal K L := IsGalois.to_normal
  exact AlgEquiv.restrictNormalHom L

/- Restriction when the Galois hypothesis is supplied as explicit field data. -/
noncomputable def chapter06AbelianGaloisRestriction
    {K Ks : Type*} [Field K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] (L : IntermediateField K Ks)
    [FiniteDimensional K L] (hL : IsAbelianGalois K L) :
    Gal(Ks / K) →* Gal(L / K) := by
  letI : IsAbelianGalois K L := hL
  exact chapter06GaloisRestriction L

/- The same restriction with the finite-extension witness supplying the
   Galois instance for its intermediate field. -/
noncomputable def chapter06FiniteExtensionRestriction
    {K Ks C : Type*} [Field K] [NumberField K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks] [CommGroup C]
    (E : Chapter06FiniteAbelianExtension K Ks C) :
    Gal(Ks / K) →* Gal(E.field / K) := by
  letI : IsAbelianGalois K E.field := E.abelian
  exact chapter06GaloisRestriction E.field

/- The norm subgroup attached to a norm homomorphism. -/
abbrev chapter06NormSubgroup
    {C D : Type*} [Group C] [Group D] (norm : D →* C) : Subgroup C :=
  norm.range

/- A finite reciprocity witness for one finite abelian extension. -/
/- LOCAL_DEPENDENCY_GUESS: the preceding chapter has not yet exposed a
   canonical topology-valued Artin map or the actual C_L-to-C_K idele norm in
   this worktree, so this boundary records the algebraic kernel/range data
   needed by Chapter 6. -/
structure Chapter06FiniteReciprocityWitness
    (K Ks C : Type*) [Field K] [NumberField K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks]
    [CommGroup C] [TopologicalSpace C] where
  extension : Chapter06FiniteAbelianExtension K Ks C
  artin : C →* Gal(extension.field / K)
  surjective_artin : Function.Surjective artin
  kernel_eq_norm : artin.ker = chapter06NormSubgroup extension.normMap
  /- A finite-target Artin map is continuous exactly when its kernel is open.
     Keeping this equivalent finite-quotient formulation avoids imposing an
     arbitrary topology on the finite Galois group in the interface. -/
  artin_kernel_open : IsOpen (artin.ker : Set C)

/- An open finite-index subgroup of the idele class group. -/
structure Chapter06OpenFiniteIndexSubgroup
    (C : Type*) [CommGroup C] [TopologicalSpace C] where
  subgroup : Subgroup C
  isOpen' : IsOpen (subgroup : Set C)
  finiteIndex' : subgroup.FiniteIndex

instance Chapter06OpenFiniteIndexSubgroup.instFiniteIndex
    {C : Type*} [CommGroup C] [TopologicalSpace C]
    (H : Chapter06OpenFiniteIndexSubgroup C) : H.subgroup.FiniteIndex :=
  H.finiteIndex'

instance Chapter06OpenFiniteIndexSubgroup.instFiniteQuotient
    {C : Type*} [CommGroup C] [TopologicalSpace C]
    (H : Chapter06OpenFiniteIndexSubgroup C) :
    Finite (C ⧸ H.subgroup) :=
  Subgroup.finiteIndex_iff_finite_quotient.mp H.finiteIndex'

/- Characters of the finite quotient attached to an open finite-index
subgroup. -/
abbrev Chapter06QuotientCharacter
    {C : Type*} [CommGroup C] [TopologicalSpace C]
    (H : Chapter06OpenFiniteIndexSubgroup C) :=
  (C ⧸ H.subgroup) →* ℂˣ

/- Lift a quotient character to the idele class group. -/
def chapter06LiftQuotientCharacter
    {C : Type*} [CommGroup C] [TopologicalSpace C]
    (H : Chapter06OpenFiniteIndexSubgroup C)
    (χ : Chapter06QuotientCharacter H) : C →* ℂˣ :=
  χ.comp (QuotientGroup.mk' H.subgroup)

/- The set of all finite quotient characters, lifted to C. -/
def chapter06LiftedQuotientCharacters
    {C : Type*} [CommGroup C] [TopologicalSpace C]
    (H : Chapter06OpenFiniteIndexSubgroup C) : Set (C →* ℂˣ) :=
  Set.range (chapter06LiftQuotientCharacter H)

theorem chapter06_lifted_quotient_character_finite_order
    {C : Type*} [CommGroup C] [TopologicalSpace C]
    (H : Chapter06OpenFiniteIndexSubgroup C)
    (χ : Chapter06QuotientCharacter H) :
    ∃ n : ℕ, 0 < n ∧
      ∀ c, (chapter06LiftQuotientCharacter H χ c) ^ n = 1 := by
  sorry

/- Openness of the subgroup makes every lifted finite-quotient character
   continuous on the idele-class topology. -/
theorem chapter06_lifted_quotient_character_continuous
    {C : Type*} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C]
    (H : Chapter06OpenFiniteIndexSubgroup C)
    (χ : Chapter06QuotientCharacter H) :
    Continuous (chapter06LiftQuotientCharacter H χ) := by
  sorry

/- The canonical fixed field of a finite character of the absolute Galois
group. -/
noncomputable def chapter06FixedFieldOfCharacter
    {K Ks : Type*} [Field K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks]
    {n : ℕ} (c : Gal(Ks / K) →* Multiplicative (Chapter06A n)) :
    IntermediateField K Ks :=
  IntermediateField.fixedField c.ker

theorem chapter06_mem_fixedField_of_character_iff
    {K Ks : Type*} [Field K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks]
    {n : ℕ} (c : Gal(Ks / K) →* Multiplicative (Chapter06A n)) (x : Ks) :
    x ∈ chapter06FixedFieldOfCharacter c ↔
      ∀ σ, c σ = 1 → σ x = x := by
  sorry

/- The finite extension degree used in the chapter's index formula.  This is
   deliberately the module-theoretic degree rather than the cardinality of a
   Galois group, so the index formula remains a substantive assertion. -/
def chapter06GaloisDegree
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : ℕ :=
  Module.finrank K L

/- A compositum of a family of intermediate fields. -/
noncomputable def chapter06Compositum
    {K Ks : Type*} [Field K] [Field Ks] [Algebra K Ks]
    {ι : Type*} (L : ι → IntermediateField K Ks) : IntermediateField K Ks :=
  sSup (Set.range L)

theorem chapter06_compositum_le_iff
    {K Ks : Type*} [Field K] [Field Ks] [Algebra K Ks]
    {ι : Type*} (L : ι → IntermediateField K Ks)
    (M : IntermediateField K Ks) :
    chapter06Compositum L ≤ M ↔ ∀ i, L i ≤ M := by
  sorry

/- A finite quotient character family used in the compositum construction. -/
structure Chapter06CharacterFieldAssignment
    (K Ks C : Type*) [Field K] [NumberField K] [Field Ks] [Algebra K Ks]
    [CommGroup C] where
  fieldOfCharacter : (C →* ℂˣ) → IntermediateField K Ks

/- The compositum field attached to an open subgroup and a character-field
assignment. -/
noncomputable def chapter06FieldOfOpenSubgroup
    {K Ks C : Type*} [Field K] [NumberField K] [Field Ks] [Algebra K Ks]
    [CommGroup C] [TopologicalSpace C]
    (H : Chapter06OpenFiniteIndexSubgroup C)
    (A : Chapter06CharacterFieldAssignment K Ks C) : IntermediateField K Ks :=
  sSup (A.fieldOfCharacter '' chapter06LiftedQuotientCharacters H)

/- The order-theoretic interface for the compositum of the character fields. -/
theorem chapter06_field_of_open_subgroup_le_iff
    {K Ks C : Type*} [Field K] [NumberField K] [Field Ks] [Algebra K Ks]
    [CommGroup C] [TopologicalSpace C]
    (H : Chapter06OpenFiniteIndexSubgroup C)
    (A : Chapter06CharacterFieldAssignment K Ks C)
    (M : IntermediateField K Ks) :
    chapter06FieldOfOpenSubgroup H A ≤ M ↔
      ∀ χ ∈ chapter06LiftedQuotientCharacters H,
        A.fieldOfCharacter χ ≤ M := by
  sorry

/- The finite character intersection behind the global existence theorem. -/
theorem chapter06_lifted_quotient_character_kernels_inf
    {C : Type*} [CommGroup C] [TopologicalSpace C]
    (H : Chapter06OpenFiniteIndexSubgroup C) :
    ⨅ χ ∈ chapter06LiftedQuotientCharacters H, χ.ker = H.subgroup := by
  sorry

end

end LastLib.Book06GlobalClassFieldTheory.Chapter06
