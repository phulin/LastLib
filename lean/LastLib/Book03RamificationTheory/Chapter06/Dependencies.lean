import LastLib.Book03RamificationTheory.Chapter05.Section02HerbrandsQuotientTheorem
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Algebra.OpenSubgroup

namespace LastLib.Book03RamificationTheory.Chapter06

noncomputable section

open LastLib.Book03RamificationTheory.Chapter05
open scoped BigOperators

universe u v

/-!
Shared interfaces for Chapter 6, “Ramification in infinite Galois
extensions”.  A finite level uses the Chapter 5 upper-numbering profile, and
the ambient group is Mathlib's profinite group.  The compatibility field below
is the book-facing form of Herbrand's quotient theorem; the finite-field
realization is supplied by the earlier chapters in a later reconciliation.
-/

/-!
The quotient maps are kept explicit because they are used both for the
inverse-limit subgroup and for finite-level representation factorization.
-/

/-- The canonical profinite Galois group of an infinite Galois extension. -/
abbrev chapter06ProfiniteGaloisGroup
    (K E : Type*) [Field K] [Field E] [Algebra K E] [IsGalois K E] : ProfiniteGrp :=
  InfiniteGalois.profiniteGalGrp K E

/-- The quotient map attached to an open normal level of a profinite group. -/
def chapter06QuotientMap
    {P : ProfiniteGrp} (N : OpenNormalSubgroup P) : P →* (P ⧸ N.toSubgroup) :=
  QuotientGroup.mk' N.toSubgroup

/-- The transition map between two quotient levels `N ≤ M`. -/
def chapter06QuotientTransition
    {P : ProfiniteGrp} {N M : OpenNormalSubgroup P} (h : N ≤ M) :
    (P ⧸ N.toSubgroup) →* (P ⧸ M.toSubgroup) :=
  QuotientGroup.map N.toSubgroup M.toSubgroup (MonoidHom.id P) (by
    intro x hx
    exact h hx)

@[simp]
theorem chapter06QuotientMap_apply
    {P : ProfiniteGrp} (N : OpenNormalSubgroup P) (x : P) :
    chapter06QuotientMap N x = (x : P ⧸ N.toSubgroup) := rfl

@[simp]
theorem chapter06QuotientTransition_apply
    {P : ProfiniteGrp} {N M : OpenNormalSubgroup P} (h : N ≤ M) (x : P) :
    chapter06QuotientTransition h (chapter06QuotientMap N x) =
      chapter06QuotientMap M x := rfl

theorem chapter06QuotientTransition_comp_quotientMap
    {P : ProfiniteGrp} {N M : OpenNormalSubgroup P} (h : N ≤ M) :
    (chapter06QuotientTransition h).comp (chapter06QuotientMap N) =
      chapter06QuotientMap M := by
  ext x
  rfl

theorem chapter06QuotientMap_surjective
    {P : ProfiniteGrp} (N : OpenNormalSubgroup P) :
    Function.Surjective (chapter06QuotientMap N) := by
  exact QuotientGroup.mk'_surjective N.toSubgroup

theorem chapter06QuotientTransition_surjective
    {P : ProfiniteGrp} {N M : OpenNormalSubgroup P} (h : N ≤ M) :
    Function.Surjective (chapter06QuotientTransition h) := by
  intro y
  rcases QuotientGroup.mk'_surjective M.toSubgroup y with ⟨x, hx⟩
  refine ⟨chapter06QuotientMap N x, ?_⟩
  rw [chapter06QuotientTransition_apply]
  exact hx

/- LOCAL_DEPENDENCY_GUESS: the present checkout exposes the finite upper
profiles and Herbrand quotient theorem, but not a single canonical profinite
ramification-system object.  This record is the smallest interface that
records the finite profiles and their transition maps without assuming any
infinite-level conclusion. -/
structure Chapter06InfiniteUpperSystem (P : ProfiniteGrp) where
  upperProfile : ∀ N : OpenNormalSubgroup P,
    Chapter05RamificationFiltration (P ⧸ N.toSubgroup)
  herbrand_bijective : ∀ N : OpenNormalSubgroup P,
    Function.Bijective (chapter05HerbrandFunction (upperProfile N))
  transition_upper_map :
    ∀ {N M : OpenNormalSubgroup P} (h : N ≤ M) (v : ℝ),
      (chapter05UpperRamificationGroup (upperProfile N) v).map
          (chapter06QuotientTransition h) =
        chapter05UpperRamificationGroup (upperProfile M) v

namespace Chapter06InfiniteUpperSystem

variable {P : ProfiniteGrp}

@[ext]
theorem ext {S T : Chapter06InfiniteUpperSystem P}
    (h : S.upperProfile = T.upperProfile) : S = T := by
  cases S
  cases T
  cases h
  rfl

theorem transition_upper_map_at
    (S : Chapter06InfiniteUpperSystem P)
    {N M : OpenNormalSubgroup P} (h : N ≤ M) (v : ℝ) :
    (chapter05UpperRamificationGroup (S.upperProfile N) v).map
        (chapter06QuotientTransition h) =
      chapter05UpperRamificationGroup (S.upperProfile M) v :=
  S.transition_upper_map h v

end Chapter06InfiniteUpperSystem

/-!
The inverse limit is represented on the ambient group by the intersection of
all finite-level inverse images.  This is the concrete subgroup formulation
of the displayed `varprojlim_N (Γ/N)^v` in the source.
-/

def chapter06InfiniteUpperGroup
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P) (v : ℝ) : Subgroup P :=
  ⨅ N : OpenNormalSubgroup P,
    (chapter05UpperRamificationGroup (S.upperProfile N) v).comap
      (chapter06QuotientMap N)

theorem chapter06InfiniteUpperGroup_mem_iff
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P) (v : ℝ) (g : P) :
    g ∈ chapter06InfiniteUpperGroup S v ↔
      ∀ N : OpenNormalSubgroup P,
        chapter06QuotientMap N g ∈
          chapter05UpperRamificationGroup (S.upperProfile N) v := by
  simp [chapter06InfiniteUpperGroup]

@[simp]
theorem chapter06InfiniteUpperGroup_eq_inverse_image_iInf
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P) (v : ℝ) :
    chapter06InfiniteUpperGroup S v =
      ⨅ N : OpenNormalSubgroup P,
        (chapter05UpperRamificationGroup (S.upperProfile N) v).comap
          (chapter06QuotientMap N) := rfl

theorem chapter06InfiniteUpperGroup_closed
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P) (v : ℝ) :
    IsClosed (chapter06InfiniteUpperGroup S v : Set P) := by
  rw [show (chapter06InfiniteUpperGroup S v : Set P) =
      ⋂ N : OpenNormalSubgroup P,
        {g : P | chapter06QuotientMap N g ∈
          chapter05UpperRamificationGroup (S.upperProfile N) v} by
    ext g
    simp [chapter06InfiniteUpperGroup]]
  exact isClosed_iInter (fun N => by
    let _ : DiscreteTopology (P ⧸ N.toSubgroup) :=
      QuotientGroup.discreteTopology N.isOpen
    exact (Set.toFinite
      (chapter05UpperRamificationGroup (S.upperProfile N) v :
        Set (P ⧸ N.toSubgroup))).isClosed.preimage continuous_quot_mk)

def chapter06InfiniteUpperClosedSubgroup
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P) (v : ℝ) :
    ClosedSubgroup P :=
  { toSubgroup := chapter06InfiniteUpperGroup S v
    isClosed' := chapter06InfiniteUpperGroup_closed S v }

theorem chapter06InfiniteUpperGroup_normal
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P) (v : ℝ) :
    (chapter06InfiniteUpperGroup S v).Normal := by
  apply Subgroup.normal_iInf_normal
  intro N
  exact (chapter05_upper_group_normal (S.upperProfile N)
    (S.herbrand_bijective N) v).comap (chapter06QuotientMap N)

instance chapter06InfiniteUpperGroup_normal_instance
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P) (v : ℝ) :
    (chapter06InfiniteUpperGroup S v).Normal :=
  chapter06InfiniteUpperGroup_normal S v

theorem chapter06InfiniteUpperGroup_antitone
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P) :
    Antitone (chapter06InfiniteUpperGroup S) := by
  intro v w hvw g hg
  rw [chapter06InfiniteUpperGroup_mem_iff] at hg ⊢
  intro N
  exact (chapter05_upper_filtration_antitone (S.upperProfile N)
    (S.herbrand_bijective N) hvw) (hg N)

/- LOCAL_DEPENDENCY_GUESS: the image equality is the compactness/cofinality
bridge from the inverse-limit intersection to a finite quotient.  It is the
map form of the source's assertion that the finite quotient recovers its upper
group, and is kept separate from the definition of the intersection. -/
theorem chapter06InfiniteUpperGroup_map
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P)
    (N : OpenNormalSubgroup P) (v : ℝ) :
    (chapter06InfiniteUpperGroup S v).map (chapter06QuotientMap N) =
      chapter05UpperRamificationGroup (S.upperProfile N) v := by
  classical
  apply le_antisymm
  · intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨g, hg, rfl⟩
    exact (chapter06InfiniteUpperGroup_mem_iff S v g).mp hg N
  · intro y hy
    let fiber : Set P := {g : P | chapter06QuotientMap N g = y}
    let C : OpenNormalSubgroup P → Set P := fun M =>
      {g : P | chapter06QuotientMap M g ∈
        chapter05UpperRamificationGroup (S.upperProfile M) v}
    let _ : DiscreteTopology (P ⧸ N.toSubgroup) :=
      QuotientGroup.discreteTopology N.isOpen
    have hfiber : IsClosed fiber := by
      have hs : IsClosed ({y} : Set (P ⧸ N.toSubgroup)) :=
        isClosed_singleton
      exact hs.preimage continuous_quot_mk
    have hfiber_compact : IsCompact fiber := hfiber.isCompact
    have hC : ∀ M : OpenNormalSubgroup P, IsClosed (C M) := by
      intro M
      let _ : DiscreteTopology (P ⧸ M.toSubgroup) :=
        QuotientGroup.discreteTopology M.isOpen
      exact (Set.toFinite
        (chapter05UpperRamificationGroup (S.upperProfile M) v :
          Set (P ⧸ M.toSubgroup))).isClosed.preimage continuous_quot_mk
    have hcommon : ∀ u : Finset (OpenNormalSubgroup P),
        ∃ K : OpenNormalSubgroup P, K ≤ N ∧ ∀ M ∈ u, K ≤ M := by
      intro u
      induction u using Finset.induction_on with
      | empty =>
          exact ⟨N, le_rfl, by simp⟩
      | @insert M u hM ih =>
          rcases ih with ⟨K, hKN, hKu⟩
          refine ⟨K ⊓ M, inf_le_left.trans hKN, ?_⟩
          intro L hL
          simp only [Finset.mem_insert] at hL
          rcases hL with rfl | hL
          · exact inf_le_right
          · exact inf_le_left.trans (hKu L hL)
    have hfinite : ∀ u : Finset (OpenNormalSubgroup P),
        (fiber ∩ ⋂ M ∈ u, C M).Nonempty := by
      intro u
      rcases hcommon u with ⟨K, hKN, hKu⟩
      have hyK : y ∈
          (chapter05UpperRamificationGroup (S.upperProfile K) v).map
            (chapter06QuotientTransition hKN) := by
        rw [S.transition_upper_map_at hKN v]
        exact hy
      rcases Subgroup.mem_map.mp hyK with ⟨z, hz, hzy⟩
      rcases chapter06QuotientMap_surjective K z with ⟨g, hg⟩
      refine ⟨g, ?_, ?_⟩
      · change chapter06QuotientMap N g = y
        rw [← chapter06QuotientTransition_apply hKN g, hg, hzy]
      · simp only [Set.mem_iInter]
        intro M hM
        change chapter06QuotientMap M g ∈
          chapter05UpperRamificationGroup (S.upperProfile M) v
        rw [← chapter06QuotientTransition_apply (hKu M hM) g]
        rw [← S.transition_upper_map_at (hKu M hM) v]
        have hgK :
            chapter06QuotientMap K g ∈
              chapter05UpperRamificationGroup (S.upperProfile K) v := by
          simpa [hg] using hz
        exact Subgroup.mem_map.mpr ⟨chapter06QuotientMap K g, hgK, rfl⟩
    have hnonempty :
        (fiber ∩ ⋂ M : OpenNormalSubgroup P, C M).Nonempty :=
      hfiber_compact.inter_iInter_nonempty
        (fun M : OpenNormalSubgroup P => C M) hC hfinite
    rcases hnonempty with ⟨g, hgfiber, hgC⟩
    have hg : g ∈ chapter06InfiniteUpperGroup S v := by
      rw [chapter06InfiniteUpperGroup_mem_iff]
      intro M
      exact (Set.mem_iInter.mp hgC) M
    exact ⟨g, hg, hgfiber⟩

/-!
In the profinite convention a right limit is the closure of the union over
strictly larger indices.  The closure disappears after projection to a finite
quotient, but is retained in the ambient definition.
-/

def chapter06InfiniteUpperRightLimit
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P) (v : ℝ) : Subgroup P :=
  Subgroup.topologicalClosure (Subgroup.closure {g : P |
    ∃ w : ℝ, v < w ∧ g ∈ chapter06InfiniteUpperGroup S w})

abbrev chapter06InfiniteUpperGroupPlus
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P) (v : ℝ) : Subgroup P :=
  chapter06InfiniteUpperRightLimit S v

theorem chapter06InfiniteUpperRightLimit_closed
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P) (v : ℝ) :
    IsClosed (chapter06InfiniteUpperRightLimit S v : Set P) := by
  exact Subgroup.isClosed_topologicalClosure _

def chapter06InfiniteUpperRightLimitClosedSubgroup
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P) (v : ℝ) :
    ClosedSubgroup P :=
  { toSubgroup := chapter06InfiniteUpperRightLimit S v
    isClosed' := chapter06InfiniteUpperRightLimit_closed S v }

theorem chapter06InfiniteUpperRightLimit_normal
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P) (v : ℝ) :
    (chapter06InfiniteUpperRightLimit S v).Normal := by
  unfold chapter06InfiniteUpperRightLimit
  let _ : (Subgroup.closure {g : P |
      ∃ w : ℝ, v < w ∧ g ∈ chapter06InfiniteUpperGroup S w}).Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply le_antisymm le_top
    exact (Subgroup.le_normalizer_closure_iff).2 (by
      intro h _ g hg
      rcases hg with ⟨w, hw, hg⟩
      exact Subgroup.subset_closure
        (k := {g : P |
          ∃ w : ℝ, v < w ∧ g ∈ chapter06InfiniteUpperGroup S w})
        ⟨w, hw, (chapter06InfiniteUpperGroup_normal S w).conj_mem g hg h⟩)
  exact Subgroup.is_normal_topologicalClosure _

/- LOCAL_DEPENDENCY_GUESS: identifying the image of the ambient closure with
the finite right limit needs the cofinality/compactness bridge for the chosen
profinite Galois system.  It is recorded as an interface here rather than
being built into the definition of the infinite group. -/
theorem chapter06InfiniteUpperRightLimit_map
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P)
    (N : OpenNormalSubgroup P) (v : ℝ) :
    (chapter06InfiniteUpperRightLimit S v).map (chapter06QuotientMap N) =
      chapter05UpperRightLimit (S.upperProfile N) v := by
  rw [chapter05UpperRightLimit, chapter05RightLimit]
  let _ : DiscreteTopology (P ⧸ N.toSubgroup) :=
    QuotientGroup.discreteTopology N.isOpen
  let levels : Set (Subgroup (P ⧸ N.toSubgroup)) :=
    chapter05UpperRamificationGroup (S.upperProfile N) '' Set.Ioi v
  let Hsup : Subgroup (P ⧸ N.toSubgroup) := sSup levels
  change (chapter06InfiniteUpperRightLimit S v).map (chapter06QuotientMap N) = Hsup
  apply le_antisymm
  · apply (Subgroup.map_le_iff_le_comap).2
    apply Subgroup.topologicalClosure_minimal
    · apply (Subgroup.closure_le _).2
      rintro g ⟨w, hw, hg⟩
      have hq : chapter06QuotientMap N g ∈
          chapter05UpperRamificationGroup (S.upperProfile N) w :=
        (chapter06InfiniteUpperGroup_mem_iff S w g).mp hg N
      have hlevel :
          chapter05UpperRamificationGroup (S.upperProfile N) w ≤ Hsup :=
        le_sSup (show chapter05UpperRamificationGroup
            (S.upperProfile N) w ∈ levels from ⟨w, hw, rfl⟩)
      exact hlevel hq
    · have hclosed : IsClosed (Hsup : Set (P ⧸ N.toSubgroup)) :=
        (Set.toFinite (Hsup : Set (P ⧸ N.toSubgroup))).isClosed
      exact hclosed.preimage continuous_quot_mk
  · change (sSup levels : Subgroup (P ⧸ N.toSubgroup)) ≤
      Subgroup.map (chapter06QuotientMap N)
        (chapter06InfiniteUpperRightLimit S v)
    refine sSup_le ?_
    intro H hH
    rcases hH with ⟨w, hw, rfl⟩
    calc
      chapter05UpperRamificationGroup (S.upperProfile N) w =
          (chapter06InfiniteUpperGroup S w).map (chapter06QuotientMap N) :=
        (chapter06InfiniteUpperGroup_map S N w).symm
      _ ≤ Subgroup.map (chapter06QuotientMap N)
          (chapter06InfiniteUpperRightLimit S v) := by
        apply (Subgroup.map_le_iff_le_comap).2
        intro g hg
        apply Subgroup.mem_map.mpr
        refine ⟨g, ?_, rfl⟩
        change g ∈ Subgroup.topologicalClosure
          (Subgroup.closure {x : P | ∃ z : ℝ, v < z ∧
            x ∈ chapter06InfiniteUpperGroup S z})
        exact (Subgroup.le_topologicalClosure _)
          (Subgroup.subset_closure
            (k := {x : P | ∃ z : ℝ, v < z ∧
              x ∈ chapter06InfiniteUpperGroup S z}) ⟨w, hw, hg⟩)

/-!
The two distinguished groups are the zero and zero-plus upper groups.  The
tame quotient is introduced in Section 6.1 after its finite-level meanings.
-/

abbrev chapter06InertiaGroup
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P) : Subgroup P :=
  chapter06InfiniteUpperGroup S 0

abbrev chapter06WildInertiaGroup
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P) : Subgroup P :=
  chapter06InfiniteUpperGroupPlus S 0

theorem chapter06WildInertiaGroup_le_inertia
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P) :
    chapter06WildInertiaGroup S ≤ chapter06InertiaGroup S := by
  apply Subgroup.topologicalClosure_minimal
  · apply (Subgroup.closure_le _).2
    rintro g ⟨w, hw, hg⟩
    exact chapter06InfiniteUpperGroup_antitone S hw.le hg
  · exact chapter06InfiniteUpperGroup_closed S 0

theorem chapter06WildInertiaGroup_normal
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P) :
    (chapter06WildInertiaGroup S).Normal := by
  unfold chapter06WildInertiaGroup chapter06InfiniteUpperGroupPlus
    chapter06InfiniteUpperRightLimit
  let _ : (Subgroup.closure {g : P |
      ∃ w : ℝ, 0 < w ∧ g ∈ chapter06InfiniteUpperGroup S w}).Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply le_antisymm le_top
    exact (Subgroup.le_normalizer_closure_iff).2 (by
      intro h _ g hg
      rcases hg with ⟨w, hw, hg⟩
      exact Subgroup.subset_closure
        (k := {g : P |
          ∃ w : ℝ, 0 < w ∧ g ∈ chapter06InfiniteUpperGroup S w})
        ⟨w, hw, (chapter06InfiniteUpperGroup_normal S w).conj_mem g hg h⟩)
  exact Subgroup.is_normal_topologicalClosure _

instance chapter06WildInertiaGroup_normal_instance
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P) :
    (chapter06WildInertiaGroup S).Normal :=
  chapter06WildInertiaGroup_normal S

def chapter06TameQuotient
    {P : ProfiniteGrp.{u}} (S : Chapter06InfiniteUpperSystem P) : Type u :=
  chapter06InertiaGroup S ⧸
    (chapter06WildInertiaGroup S).subgroupOf (chapter06InertiaGroup S)

instance chapter06TameQuotient_group
    {P : ProfiniteGrp.{u}} (S : Chapter06InfiniteUpperSystem P) :
    Group (chapter06TameQuotient S) := by
  letI : (chapter06WildInertiaGroup S).Normal :=
    chapter06WildInertiaGroup_normal S
  change Group
    (chapter06InertiaGroup S ⧸
      (chapter06WildInertiaGroup S).subgroupOf (chapter06InertiaGroup S))
  infer_instance

noncomputable instance chapter06TameQuotient_topologicalSpace
    {P : ProfiniteGrp.{u}} (S : Chapter06InfiniteUpperSystem P) :
    TopologicalSpace (chapter06TameQuotient S) := by
  exact QuotientGroup.instTopologicalSpace _

/-!
Finite quotients used by the local ramification certificate.  Lower groups
are used because their normality is part of the finite profile interface;
Chapter 5 identifies the level-one lower group with the finite upper
zero-plus group after the Herbrand bijectivity supplied by `S`.
-/

abbrev chapter06FiniteLevelInertiaGroup
    {P : ProfiniteGrp.{u}} (S : Chapter06InfiniteUpperSystem P)
    (N : OpenNormalSubgroup P) : Subgroup (P ⧸ N.toSubgroup) :=
  (S.upperProfile N).lowerGroup 0

abbrev chapter06FiniteLevelWildInertiaGroup
    {P : ProfiniteGrp.{u}} (S : Chapter06InfiniteUpperSystem P)
    (N : OpenNormalSubgroup P) : Subgroup (P ⧸ N.toSubgroup) :=
  (S.upperProfile N).lowerGroup 1

def chapter06FiniteLevelTameQuotient
    {P : ProfiniteGrp.{u}} (S : Chapter06InfiniteUpperSystem P)
    (N : OpenNormalSubgroup P) : Type u :=
  chapter06FiniteLevelInertiaGroup S N ⧸
    (chapter06FiniteLevelWildInertiaGroup S N).subgroupOf
      (chapter06FiniteLevelInertiaGroup S N)

instance chapter06FiniteLevelTameQuotient_group
    {P : ProfiniteGrp.{u}} (S : Chapter06InfiniteUpperSystem P)
    (N : OpenNormalSubgroup P) :
    Group (chapter06FiniteLevelTameQuotient S N) := by
  letI : (chapter06FiniteLevelWildInertiaGroup S N).Normal :=
    (S.upperProfile N).lower_normal 1
  change Group
    (chapter06FiniteLevelInertiaGroup S N ⧸
      (chapter06FiniteLevelWildInertiaGroup S N).subgroupOf
        (chapter06FiniteLevelInertiaGroup S N))
  infer_instance

def chapter06ProPGroup (p : ℕ) (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∀ N : OpenNormalSubgroup G,
    ∃ r : ℕ, Finite (G ⧸ N.toSubgroup) ∧
      Nat.card (G ⧸ N.toSubgroup) = p ^ r

def chapter06ProPrimeTo (p : ℕ) (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∀ N : OpenNormalSubgroup G,
    Finite (G ⧸ N.toSubgroup) ∧
      Nat.Coprime p (Nat.card (G ⧸ N.toSubgroup))

def chapter06Procyclic (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∀ N : OpenNormalSubgroup G,
    Finite (G ⧸ N.toSubgroup) ∧ IsCyclic (G ⧸ N.toSubgroup)

/-!
This certificate supplies the finite local arithmetic and the cofinal kernel
maps needed to turn the compatible finite profiles into profinite statements.
Finite order facts alone would not control arbitrary open quotients of the
inverse-limit subgroups, hence the explicit cofinality fields.
-/
structure Chapter06FiniteLevelLocalRamificationInterface
    {P : ProfiniteGrp.{u}} (S : Chapter06InfiniteUpperSystem P) (p : ℕ) where
  tame_level_map :
    ∀ N : OpenNormalSubgroup P,
      chapter06TameQuotient S →*
        chapter06FiniteLevelTameQuotient S N
  tame_level_map_surjective :
    ∀ N : OpenNormalSubgroup P,
      Function.Surjective (tame_level_map N)
  tame_kernel_cofinal :
    ∀ H : OpenNormalSubgroup (chapter06TameQuotient S),
      ∃ N : OpenNormalSubgroup P,
        (tame_level_map N).ker ≤ H.toSubgroup
  tame_level_finite :
    ∀ N : OpenNormalSubgroup P,
      Finite (chapter06FiniteLevelTameQuotient S N)
  tame_level_prime_to :
    ∀ N : OpenNormalSubgroup P,
      Nat.Coprime p (Nat.card (chapter06FiniteLevelTameQuotient S N))
  tame_level_cyclic :
    ∀ N : OpenNormalSubgroup P,
      IsCyclic (chapter06FiniteLevelTameQuotient S N)
  wild_level_map :
    ∀ N : OpenNormalSubgroup P,
      chapter06WildInertiaGroup S →*
        chapter06FiniteLevelWildInertiaGroup S N
  wild_level_map_surjective :
    ∀ N : OpenNormalSubgroup P,
      Function.Surjective (wild_level_map N)
  wild_kernel_cofinal :
    ∀ H : OpenNormalSubgroup (chapter06WildInertiaGroup S),
      ∃ N : OpenNormalSubgroup P,
        (wild_level_map N).ker ≤ H.toSubgroup
  wild_level_finite :
    ∀ N : OpenNormalSubgroup P,
      Finite (chapter06FiniteLevelWildInertiaGroup S N)
  wild_level_p_power :
    ∀ N : OpenNormalSubgroup P,
      ∃ r : ℕ,
        Nat.card (chapter06FiniteLevelWildInertiaGroup S N) = p ^ r
  wild_level_trivial_of_characteristic_zero :
    p = 1 →
      ∀ N : OpenNormalSubgroup P,
        chapter06FiniteLevelWildInertiaGroup S N = ⊥

end

end LastLib.Book03RamificationTheory.Chapter06
