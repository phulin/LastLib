import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.Section01CoveringFamilies
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
## 2.3 Infinite families and size

The declarations here separate a valid family cover from the single coproduct morphism.  They also
make the set-sized and finite-product hypotheses visible in later APIs.
-/

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology
open scoped AlgebraicGeometry

universe u v

variable {S : Scheme.{u}} {I : Type v}

noncomputable def SchemeFamily.coproductMap
    (F : SchemeFamily S I) [Small.{u} I] :
    (∐ F.obj) ⟶ S :=
  Sigma.desc F.map

@[simp]
theorem SchemeFamily.ι_comp_coproductMap
    (F : SchemeFamily S I) [Small.{u} I] (i : I) :
    Sigma.ι F.obj i ≫ F.coproductMap = F.map i := by
  simp [SchemeFamily.coproductMap]

/-- An infinitely indexed family of redundant identity copies of one scheme. -/
def redundantIdentityFamily (S : Scheme.{u}) (I : Type v) : SchemeFamily S I where
  obj := fun _ ↦ S
  map := fun _ ↦ 𝟙 S

theorem redundantIdentityFamily_is_fpqc
    (S : Scheme.{u}) (I : Type v) [Nonempty I] :
    FpqcCoveringFamily (redundantIdentityFamily S I) := by
  classical
  let i₀ : I := Classical.choice (inferInstance : Nonempty I)
  refine ⟨?_, ?_⟩
  · intro i
    dsimp [redundantIdentityFamily]
    infer_instance
  · intro U hU
    refine ⟨⟨1, (fun _ : Fin 1 ↦ i₀), (fun _ ↦ U), (fun _ ↦ hU), ?_⟩⟩
    change (U : Set S) =
      ⋃ _ : Fin 1, (𝟙 S : S ⟶ S) '' (U : Set S)
    ext x
    constructor
    · intro hx
      exact Set.mem_iUnion.2 ⟨0, ⟨x, hx, rfl⟩⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨j, hj⟩
      rcases hj with ⟨y, hy, hxy⟩
      simpa only [Scheme.Hom.id_app] using hxy ▸ hy

theorem redundantIdentityFamily_is_fpqc_of_infinite
    (S : Scheme.{u}) (I : Type v) [Nonempty I] [Infinite I] :
    FpqcCoveringFamily (redundantIdentityFamily S I) := by
  exact redundantIdentityFamily_is_fpqc S I

theorem redundantIdentityFamily_coproductMap_not_quasiCompact
    (S : Scheme.{u}) (I : Type v) [Small.{u} I] [Infinite I] [Nonempty I]
    [Nonempty S] :
    ¬ QuasiCompact (redundantIdentityFamily S I).coproductMap := by
  intro hp
  let : QuasiCompact (redundantIdentityFamily S I).coproductMap := hp
  obtain ⟨s⟩ := (inferInstance : Nonempty S)
  obtain ⟨_, ⟨U, hU, rfl⟩, hsU, _⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open
      (a := s) (Set.mem_univ s) isOpen_univ
  have hV :=
    (redundantIdentityFamily S I).coproductMap.isCompact_preimage hU.isCompact
  have hopen : ∀ i : I,
      IsOpen (Set.range (Sigma.ι (redundantIdentityFamily S I).obj i)) := by
    intro i
    change IsOpen (Set.range
      (colimit.ι (Discrete.functor (redundantIdentityFamily S I).obj) ⟨i⟩))
    exact IsOpenImmersion.isOpen_range _
  have hcover :
      (((redundantIdentityFamily S I).coproductMap ⁻¹ᵁ U : Set _)) ⊆
        ⋃ i : I, Set.range (Sigma.ι (redundantIdentityFamily S I).obj i) := by
    intro x hx
    obtain ⟨i, y, hy⟩ :=
      (sigmaOpenCover (redundantIdentityFamily S I).obj).exists_eq x
    exact Set.mem_iUnion.2 ⟨i, ⟨y, hy⟩⟩
  obtain ⟨t, ht⟩ := hV.elim_finite_subcover
    (fun i : I ↦ Set.range (Sigma.ι (redundantIdentityFamily S I).obj i)) hopen hcover
  have huniv : (Set.univ : Set I) ⊆ (t : Set I) := by
    intro i hi
    let si : (redundantIdentityFamily S I).obj i := by
      simpa [redundantIdentityFamily] using s
    have hsi : si = s := by
      rfl
    have hxi : Sigma.ι (redundantIdentityFamily S I).obj i si ∈
        ((redundantIdentityFamily S I).coproductMap ⁻¹ᵁ U : Set _) := by
      change (redundantIdentityFamily S I).coproductMap
          (Sigma.ι (redundantIdentityFamily S I).obj i si) ∈ (U : Set S)
      rw [← Scheme.Hom.comp_apply]
      rw [SchemeFamily.ι_comp_coproductMap]
      change s ∈ (U : Set S)
      exact hsU
    rcases Set.mem_iUnion.1 (ht hxi) with ⟨j, hj⟩
    rcases Set.mem_iUnion.1 hj with ⟨hjT, hxj⟩
    rcases hxj with ⟨z, hz⟩
    have hij : i = j := by
      have hp :=
        (sigmaι_eq_iff (redundantIdentityFamily S I).obj i j si z).1 hz.symm
      exact congrArg Sigma.fst hp
    rw [hij]
    exact hjT
  exact Set.infinite_univ.not_finite ((Finset.finite_toSet t).subset huniv)

/-- The infinite disjoint union of affine schemes used in the family-level example. -/
noncomputable def disjointAffineScheme
    (A : I → CommRingCat.{u}) [Small.{u} I] : Scheme.{u} :=
  ∐ fun i ↦ Spec (A i)

noncomputable def disjointAffineComponentFamily
    (A : I → CommRingCat.{u}) [Small.{u} I] :
    SchemeFamily (disjointAffineScheme A) I where
  obj := fun i ↦ Spec (A i)
  map := fun i ↦ Sigma.ι (fun i ↦ Spec (A i)) i

def componentSupport
    (A : I → CommRingCat.{u}) [Small.{u} I]
    (U : (disjointAffineScheme A).Opens) : Set I :=
  {i | ((U : Set (disjointAffineScheme A)) ∩
      Set.range (Sigma.ι (fun j ↦ Spec (A j)) i)).Nonempty}

theorem componentSupport_finite_of_compactOpen
    (A : I → CommRingCat.{u}) [Small.{u} I]
    (U : (disjointAffineScheme A).Opens) (hU : IsCompact (U : Set (disjointAffineScheme A))) :
    (componentSupport A U).Finite := by
  have hopen : ∀ i : I,
      IsOpen (Set.range (Sigma.ι (fun j ↦ Spec (A j)) i)) := by
    intro i
    change IsOpen (Set.range
      (colimit.ι (Discrete.functor (fun j ↦ Spec (A j))) ⟨i⟩))
    exact IsOpenImmersion.isOpen_range _
  have hcover : (U : Set (disjointAffineScheme A)) ⊆
      ⋃ i : I, Set.range (Sigma.ι (fun j ↦ Spec (A j)) i) := by
    intro x hx
    obtain ⟨i, y, hy⟩ := (sigmaOpenCover (fun i ↦ Spec (A i))).exists_eq x
    exact Set.mem_iUnion.2 ⟨i, ⟨y, hy⟩⟩
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover
    (fun i : I ↦ Set.range (Sigma.ι (fun j ↦ Spec (A j)) i)) hopen hcover
  apply Set.Finite.subset (Finset.finite_toSet t)
  intro i hi
  rcases hi with ⟨x, hxU, hxrange⟩
  rcases hxrange with ⟨y, rfl⟩
  rcases Set.mem_iUnion.1 (ht hxU) with ⟨j, hj⟩
  rcases Set.mem_iUnion.1 hj with ⟨hjT, hxj⟩
  rcases hxj with ⟨z, hz⟩
  have hij : i = j := by
    have hp := (sigmaι_eq_iff (fun k ↦ Spec (A k)) i j y z).1 hz.symm
    exact congrArg Sigma.fst hp
  rw [hij]
  exact hjT

theorem disjointAffineComponentFamily_is_fpqc
    (A : I → CommRingCat.{u}) [Small.{u} I] :
    FpqcCoveringFamily (disjointAffineComponentFamily A) := by
  change FpqcCoveringFamily
    ({ obj := (fun i : I ↦ Spec (A i)), map :=
      (fun i : I ↦ Sigma.ι (fun i ↦ Spec (A i)) i) } :
      SchemeFamily (∐ (fun i ↦ Spec (A i))) I)
  apply zariskiCoveringFamily_is_fpqc
  refine ⟨?_, ?_⟩
  · intro i
    change IsOpenImmersion
      (colimit.ι (Discrete.functor (fun i ↦ Spec (A i))) ⟨i⟩)
    infer_instance
  · intro x
    obtain ⟨i, y, hy⟩ := (sigmaOpenCover (fun i ↦ Spec (A i))).exists_eq x
    exact ⟨i, y, hy⟩

theorem disjointAffineComponentFamily_coproductMap_eq_id
    (A : I → CommRingCat.{u}) [Small.{u} I] :
    (disjointAffineComponentFamily A).coproductMap =
      𝟙 (disjointAffineScheme A) := by
  change Sigma.desc (fun i ↦ Sigma.ι (fun i ↦ Spec (A i)) i) =
    𝟙 (∐ fun i ↦ Spec (A i))
  apply Sigma.hom_ext _ _
  intro i
  simp

/-- Adding identity members to an already fpqc family preserves the family-level fpqc condition. -/
def addRedundantMembers {S : Scheme.{u}} {I J : Type v}
    (F : SchemeFamily S I) : SchemeFamily S (I ⊕ J) where
  obj := fun ij ↦ match ij with
    | Sum.inl i => F.obj i
    | Sum.inr _ => S
  map := fun ij ↦ match ij with
    | Sum.inl i => F.map i
    | Sum.inr _ => 𝟙 S

theorem addRedundantMembers_is_fpqc
    {S : Scheme.{u}} {I J : Type v} {F : SchemeFamily S I}
    (hF : FpqcCoveringFamily F) :
    FpqcCoveringFamily (addRedundantMembers (J := J) F) := by
  refine (fpqcCoveringFamily_iff_affine_reductions
    (addRedundantMembers (J := J) F)).2 ?_
  refine ⟨?_, ?_⟩
  · intro ij
    cases ij with
    | inl i => exact hF.flat i
    | inr j =>
      change Flat (𝟙 S)
      infer_instance
  · intro U hU
    obtain ⟨R⟩ := hF.finite_reduction U hU.isCompact
    refine ⟨⟨R.cardinality, (fun k ↦ Sum.inl (R.member k)),
      (fun k ↦ R.sourceOpen k), (fun k ↦ R.quasiCompact k), ?_⟩⟩
    change (U : Set S) =
      ⋃ j : Fin R.cardinality,
        F.map (R.member j) '' (R.sourceOpen j : Set (F.obj (R.member j)))
    exact R.covers

theorem addRedundantMembers_is_fppf
    {S : Scheme.{u}} {I J : Type v} {F : SchemeFamily S I}
    (hF : FppfCoveringFamily F) :
    FppfCoveringFamily (addRedundantMembers (J := J) F) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s
    obtain ⟨i, x, hx⟩ := hF.jointly_surjective s
    exact ⟨Sum.inl i, x, hx⟩
  · intro ij
    cases ij with
    | inl i => exact hF.flat i
    | inr j =>
      change Flat (𝟙 S)
      infer_instance
  · intro ij
    cases ij with
    | inl i => exact hF.locally_of_finite_presentation i
    | inr j =>
      change LocallyOfFinitePresentation (𝟙 S)
      infer_instance

/-- A bundled sequence of flat modules whose infinite product is not flat. -/
structure FlatModuleSequence (R : Type u) [CommRing R] where
  moduleType : ℕ → Type u
  addCommMonoid : ∀ n, AddCommMonoid (moduleType n)
  module : ∀ n, Module R (moduleType n)
  flat : ∀ n,
    letI : AddCommMonoid (moduleType n) := addCommMonoid n
    letI : Module R (moduleType n) := module n
    Module.Flat R (moduleType n)
  product_not_flat :
    letI : ∀ n, AddCommMonoid (moduleType n) := addCommMonoid
    letI : ∀ n, Module R (moduleType n) := module
    ¬ Module.Flat R (∀ n, moduleType n)

def InfiniteProductFlatnessFailure : Prop :=
  ∃ (R : Type u) (hR : CommRing R), Nonempty (@FlatModuleSequence R hR)

theorem exists_infinite_product_of_flat_modules_not_flat :
    InfiniteProductFlatnessFailure.{u} := by
  classical
  refine ⟨TrivSqZeroExt (ULift.{u} ℚ) (ℕ →₀ ULift.{u} ℚ), inferInstance, ?_⟩
  refine ⟨(fun _ : ℕ ↦ TrivSqZeroExt (ULift.{u} ℚ) (ℕ →₀ ULift.{u} ℚ)),
    (fun _ ↦ inferInstance), (fun _ ↦ inferInstance), ?_, ?_⟩
  · intro n
    infer_instance
  · let : ∀ n : ℕ,
        AddCommMonoid (TrivSqZeroExt (ULift.{u} ℚ) (ℕ →₀ ULift.{u} ℚ)) :=
      fun _ ↦ inferInstance
    let : ∀ n : ℕ, Module (TrivSqZeroExt (ULift.{u} ℚ) (ℕ →₀ ULift.{u} ℚ))
        (TrivSqZeroExt (ULift.{u} ℚ) (ℕ →₀ ULift.{u} ℚ)) := fun _ ↦ inferInstance
    intro hflat
    let z : TrivSqZeroExt (ULift.{u} ℚ) (ℕ →₀ ULift.{u} ℚ) :=
      TrivSqZeroExt.inr (Finsupp.single 0 1)
    let f : Fin 1 → TrivSqZeroExt (ULift.{u} ℚ) (ℕ →₀ ULift.{u} ℚ) := fun _ ↦ z
    let x : Fin 1 →
        (∀ n : ℕ, TrivSqZeroExt (ULift.{u} ℚ) (ℕ →₀ ULift.{u} ℚ)) :=
      fun _ n ↦ TrivSqZeroExt.inr (Finsupp.single n 1)
    have hrel : ∑ i, f i • x i = 0 := by
      funext n
      simp [f, x, z, smul_eq_mul]
    obtain ⟨k, a, y, hxy, haf⟩ :=
      (Module.Flat.iff_forall_isTrivialRelation.mp hflat) hrel
    have hzero (j : Fin k) : (a 0 j).fst = 0 := by
      have hja : z * a 0 j = 0 := by
        simpa [f] using haf j
      have hjs := congrArg TrivSqZeroExt.snd hja
      have hje := congrArg (fun m : ℕ →₀ ULift.{u} ℚ ↦ m 0) hjs
      simpa [z, TrivSqZeroExt.snd_mul, Finsupp.single_apply] using hje
    let t : Finset ℕ := Finset.univ.biUnion (fun j => (a 0 j).snd.support)
    obtain ⟨n, _, hn⟩ := Set.Infinite.exists_notMem_finset
      (s := (Set.univ : Set ℕ)) Set.infinite_univ t
    have hsupport (j : Fin k) : (a 0 j).snd n = 0 := by
      by_contra hne
      apply hn
      exact Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _,
        Finsupp.mem_support_iff.2 hne⟩
    have hcoord := congrFun (hxy 0) n
    have hcoord' :
        TrivSqZeroExt.inr (Finsupp.single n 1) =
          ∑ j, a 0 j * y j n := by
      simpa [x, smul_eq_mul] using hcoord
    have hcoord_snd := congrArg TrivSqZeroExt.snd hcoord'
    have hcoord_eval := congrArg (fun m : ℕ →₀ ULift.{u} ℚ ↦ m n) hcoord_snd
    simp [TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul, hzero, hsupport] at hcoord_eval

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02
