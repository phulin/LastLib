import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.Algebra.CharZero.Quotient
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.KummerExtension
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RepresentationTheory.Basic
import Mathlib.Topology.Algebra.Group.Compact
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import LastLib.Book06GlobalClassFieldTheory.Chapter01.Dependencies
import LastLib.Book06GlobalClassFieldTheory.Chapter01.Section01OneGaloisActionSeenAtEveryPlace
import LastLib.Book06GlobalClassFieldTheory.Chapter01.Section04ArchitectureOfTheProof
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

/- Canonical earlier-chapter interfaces for the same coefficient package.  The
   Chapter 6 names below keep the source notation readable while these aliases
   make the reuse of the Chapter 1 finite-Cartier API explicit. -/
abbrev Chapter06CanonicalA (n : ℕ) : Type :=
  LastLib.Book06GlobalClassFieldTheory.Chapter01.CartierConstantCoefficient n

abbrev Chapter06CanonicalKummerClassGroup
    (F : Type*) [Field F] (n : ℕ) :=
  LastLib.Book06GlobalClassFieldTheory.Chapter01.CartierKummerClassGroup F n

abbrev Chapter06CanonicalRestrictedProduct
    (ι : Type*) (H : ι → Type*) [∀ i, AddCommGroup (H i)]
    (U : ∀ i, AddSubgroup (H i)) :=
  LastLib.Book06GlobalClassFieldTheory.Chapter01.CartierRestrictedProduct ι H U

abbrev Chapter06CanonicalFiniteDualityStatement
    (K : Type*) [Field K] [NumberField K] (n : ℕ) :=
  LastLib.Book06GlobalClassFieldTheory.Chapter01.FiniteCartierDualityStatement K n

/- The canonical coefficient inclusion used by the exceptional
   Grunwald--Wang lift.  It is the additive map induced by the integer map
   z ↦ 2z, with the relation n ↦ 0 respected in `ZMod (2 * n)`. -/
noncomputable def chapter06CanonicalAEmbedding (n : ℕ) :
    Chapter06A n →+ Chapter06A (2 * n) := by
  let f : ℤ →+ Chapter06A (2 * n) :=
    { toFun := fun z => (2 : Chapter06A (2 * n)) * (z : Chapter06A (2 * n))
      map_zero' := by simp
      map_add' := by
        intro x y
        simp [mul_add] }
  exact ZMod.lift n ⟨f, by
    dsimp [f]
    have h : ((2 * (n : ℤ) : ℤ) : Chapter06A (2 * n)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * (n : ℤ)) (2 * n)).2
        (dvd_refl (2 * (n : ℤ)))
    simpa only [Int.cast_mul, Int.cast_ofNat] using h⟩

@[simp]
theorem chapter06CanonicalAEmbedding_intCast (n : ℕ) (z : ℤ) :
    chapter06CanonicalAEmbedding n (z : Chapter06A n) =
      (2 : Chapter06A (2 * n)) * (z : Chapter06A (2 * n)) := by
  simp [chapter06CanonicalAEmbedding]

theorem chapter06CanonicalAEmbedding_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (chapter06CanonicalAEmbedding n) := by
  have _hn : 0 < n := hn
  intro x y h
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
  obtain ⟨b, rfl⟩ := ZMod.intCast_surjective y
  rw [chapter06CanonicalAEmbedding_intCast, chapter06CanonicalAEmbedding_intCast] at h
  have h' : ((2 * a : ℤ) : Chapter06A (2 * n)) =
      ((2 * b : ℤ) : Chapter06A (2 * n)) := by
    simpa only [Int.cast_mul, Int.cast_ofNat] using h
  have hdiv : (2 * n : ℤ) ∣ 2 * b - 2 * a :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (2 * a) (2 * b) (2 * n)).mp h'
  rcases hdiv with ⟨k, hk⟩
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub a b n).mpr
  refine ⟨k, ?_⟩
  have hcancel : (2 : ℤ) * (b - a) = 2 * (n * k) := by
    calc
      (2 : ℤ) * (b - a) = 2 * b - 2 * a := by ring
      _ = (2 * n) * k := hk
      _ = 2 * (n * k) := by ring
  exact (mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) hcancel)

/- The trivial action of a group on an additive coefficient module. -/
def chapter06TrivialAction
    (G M : Type*) [Group G] [AddCommGroup M] : G → M →+ M :=
  fun _ ↦ AddMonoidHom.id M

/- The Cartier-dual coefficient at a field. Its underlying group is the
subgroup of nth roots of unity in the unit group. -/
abbrev Chapter06CartierDual (K : Type*) [Field K] (n : ℕ) :=
  rootsOfUnity n K

/- The geometric roots-of-unity group lives in the chosen separable closure;
   unlike `Chapter06CartierDual`, it does not assume that K contains the
   roots.  Its canonical Galois action is installed immediately below. -/
abbrev Chapter06GeometricCartierDual
    (K Ks : Type*) [Field K] [Field Ks] [Algebra K Ks] (n : ℕ) :=
  rootsOfUnity n Ks

/- The geometric roots are not merely a carrier: the chosen absolute Galois
   group acts on them by restricting its field automorphisms.  This is the
   coefficient action used by the twisted Cartier dual. -/
noncomputable instance chapter06GeometricCartierDualMulDistribMulAction
    (K Ks : Type*) [Field K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks] (n : ℕ) :
    MulDistribMulAction (Gal(Ks / K))
      (Chapter06GeometricCartierDual K Ks n) where
  smul σ ζ := restrictRootsOfUnity σ.toAlgHom n ζ
  one_smul ζ := by
    apply Subtype.ext
    apply Units.ext
    rfl
  mul_smul σ τ ζ := by
    apply Subtype.ext
    apply Units.ext
    rfl
  smul_one σ := by
    change restrictRootsOfUnity σ.toAlgHom n (1 : rootsOfUnity n Ks) = 1
    exact (restrictRootsOfUnity σ.toAlgHom n).map_one
  smul_mul σ ζ ξ := by
    change restrictRootsOfUnity σ.toAlgHom n (ζ * ξ) =
      restrictRootsOfUnity σ.toAlgHom n ζ * restrictRootsOfUnity σ.toAlgHom n ξ
    exact (restrictRootsOfUnity σ.toAlgHom n).map_mul ζ ξ

/- A representation-level form of the action, suitable for group-cohomology
   interfaces.  The base-field roots alias below remains reserved for the
   primitive-root self-duality specialization. -/
noncomputable def chapter06GeometricCartierDualRepresentation
    (K Ks : Type*) [Field K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks] (n : ℕ) :
    Representation ℤ (Gal(Ks / K))
      (Additive (Chapter06GeometricCartierDual K Ks n)) :=
  Representation.ofMulDistribMulAction (Gal(Ks / K))
    (Chapter06GeometricCartierDual K Ks n)

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
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  let q : Chapter06QModZ :=
    QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ)) ((1 : ℚ) / n)
  have hq : n • q = 0 := by
    dsimp [q]
    rw [← QuotientAddGroup.mk_nat_mul]
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff]
    refine ⟨1, ?_⟩
    field_simp [hn0]
    simp
  let u : Chapter06OneOverNModOne n := ⟨q, hq⟩
  let f : ℤ →+ Chapter06OneOverNModOne n :=
    { toFun := fun z => z • u
      map_zero' := by simp
      map_add' := by intro x y; simp [add_zsmul] }
  have hf : f (n : ℤ) = 0 := by
    change (n : ℤ) • u = 0
    apply Subtype.ext
    simpa [u] using hq
  let g : ZMod n →+ Chapter06OneOverNModOne n :=
    ZMod.lift n ⟨f, hf⟩
  have hg_inj : Function.Injective g := by
    change Function.Injective (ZMod.lift n ⟨f, hf⟩)
    apply (ZMod.lift_injective (n := n) (f := ⟨f, hf⟩)).2
    intro m hm
    have hmq : (m : ℤ) • q = 0 := by
      have hm' := congrArg Subtype.val hm
      simpa [f, u] using hm'
    dsimp [q] at hmq
    rw [← QuotientAddGroup.mk_int_mul] at hmq
    have hmem : (m : ℚ) * ((1 : ℚ) / n) ∈
        AddSubgroup.zmultiples (1 : ℚ) :=
      (QuotientAddGroup.eq_zero_iff _).mp hmq
    rw [AddSubgroup.mem_zmultiples_iff] at hmem
    rcases hmem with ⟨k, hk⟩
    have hmk : (m : ℚ) = (n : ℚ) * k := by
      field_simp [hn0] at hk
      simpa [smul_eq_mul, mul_comm] using hk.symm
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd m n).2
    refine ⟨k, ?_⟩
    exact_mod_cast hmk
  have hg_surj : Function.Surjective g := by
    intro x
    have hx : n • (x : Chapter06QModZ) = 0 := x.property
    have hx' : ∃ k : Fin n,
        (x : Chapter06QModZ) = 0 +
          (k : ℕ) • (((1 : ℚ) / (n : ℚ)) : Chapter06QModZ) := by
      apply (QuotientAddGroup.zmultiples_nsmul_eq_nsmul_iff
        (R := ℚ) (p := (1 : ℚ)) (ψ := (x : Chapter06QModZ))
        (θ := 0) (n := n) (Nat.ne_of_gt hn)).mp
      simpa using hx
    rcases hx' with ⟨k, hk⟩
    refine ⟨(((k : ℕ) : ℤ) : ZMod n), ?_⟩
    rw [show g (((k : ℕ) : ℤ) : ZMod n) = f ((k : ℕ) : ℤ) by
      simpa [g] using (ZMod.lift_coe n ⟨f, hf⟩ ((k : ℕ) : ℤ))]
    change ((k : ℕ) : ℤ) • u = x
    apply Subtype.ext
    simpa [u, q] using hk.symm
  exact (AddEquiv.ofBijective g ⟨hg_inj, hg_surj⟩).symm

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
  simp [chapter06KummerRestriction, chapter06KummerClassMk]

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
  /- The carrier is only an interface for the canonical quotient exposed by
     Chapter 1; it must not be an unrelated abstract topological group. -/
  canonical : carrier ≃* LastLib.Book06GlobalClassFieldTheory.Chapter01.BookIdeleClassGroup K
  canonical_continuous : Continuous canonical
  canonical_inverse_continuous : Continuous canonical.symm

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
  /- The finite witness is a quotient of the chosen absolute Galois group;
     this prevents an unrelated abstract finite group from being presented as
     the Galois group of `extension.field`. -/
  restriction_surjective :
    Function.Surjective (chapter06FiniteExtensionRestriction extension)
  field_eq_fixed :
    extension.field =
      IntermediateField.fixedField
        (chapter06FiniteExtensionRestriction extension).ker

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
  refine ⟨Nat.card (C ⧸ H.subgroup), Nat.card_pos, ?_⟩
  intro c
  change (χ (QuotientGroup.mk' H.subgroup c)) ^ Nat.card (C ⧸ H.subgroup) = 1
  rw [← χ.map_pow, pow_card_eq_one']
  exact χ.map_one

/- Openness of the subgroup makes every lifted finite-quotient character
   continuous on the idele-class topology. -/
theorem chapter06_lifted_quotient_character_continuous
    {C : Type*} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C]
    (H : Chapter06OpenFiniteIndexSubgroup C)
    (χ : Chapter06QuotientCharacter H) :
    Continuous (chapter06LiftQuotientCharacter H χ) := by
  have hdisc : DiscreteTopology (C ⧸ H.subgroup) := QuotientGroup.discreteTopology H.isOpen'
  change Continuous (χ.comp (QuotientGroup.mk' H.subgroup))
  exact (@continuous_of_discreteTopology (C ⧸ H.subgroup) _ hdisc ℂˣ _ χ).comp
    QuotientGroup.continuous_mk

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
  simp [chapter06FixedFieldOfCharacter, IntermediateField.mem_fixedField_iff]

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
  simp [chapter06Compositum]

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
  simp [chapter06FieldOfOpenSubgroup]

/- The finite character intersection behind the global existence theorem. -/
theorem chapter06_lifted_quotient_character_kernels_inf
    {C : Type*} [CommGroup C] [TopologicalSpace C]
    (H : Chapter06OpenFiniteIndexSubgroup C) :
    ⨅ χ ∈ chapter06LiftedQuotientCharacters H, χ.ker = H.subgroup := by
  ext x
  simp only [Subgroup.mem_iInf, chapter06LiftedQuotientCharacters, Set.mem_range,
    forall_exists_index, MonoidHom.mem_ker]
  have hsep :
      (∀ a : Chapter06QuotientCharacter H,
          a (QuotientGroup.mk' H.subgroup x) = 1) ↔
        QuotientGroup.mk' H.subgroup x = 1 := by
    simpa using
      (CommGroup.forall_apply_eq_apply_iff (C ⧸ H.subgroup) (M := ℂ)
        (g := QuotientGroup.mk' H.subgroup x) (g' := 1))
  constructor
  · intro hx
    have hchars : ∀ a : Chapter06QuotientCharacter H,
        (chapter06LiftQuotientCharacter H a) x = 1 := by
      intro a
      exact hx _ a rfl
    have hq : QuotientGroup.mk' H.subgroup x = 1 :=
      hsep.mp (by simpa [chapter06LiftQuotientCharacter] using hchars)
    exact (QuotientGroup.eq_one_iff x).mp hq
  · intro hx i a hai
    subst i
    have hq : QuotientGroup.mk' H.subgroup x = 1 :=
      (QuotientGroup.eq_one_iff x).mpr hx
    have hq' := congrArg a hq
    simpa [chapter06LiftQuotientCharacter] using hq'

end

end LastLib.Book06GlobalClassFieldTheory.Chapter06
