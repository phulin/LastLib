import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.Section05HigherRamificationBoundary
import LastLib.Book03RamificationTheory.Chapter02.Section01WhyDisplacementIsTheRightMeasurement
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Index
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace LastLib.Book03RamificationTheory.Chapter04

noncomputable section

open scoped BigOperators Pointwise

/-!
Shared interfaces for Chapter 4.

The subgroup and Herbrand statements use only the integer lower groups and their
monotonicity, so the local interface below remains the weakest reusable API for
abstract filtrations (and is retained for downstream users).  Chapter 2 already
exposes the canonical finite lower-filtration structure; the adapter immediately
following the extensionality theorem connects that stronger API to this one.  The
valuation-ring constructors at the end of this file connect the same interface to
Book 2's canonical congruence filtration.
-/

universe u v

/-- A finite-indexed lower ramification filtration, with the `-1` level equal to
the ambient group and the nonnegative levels supplied by `lower`. -/
structure Chapter04LowerFiltration (G : Type u) [Group G] where
  lower : ℕ → Subgroup G
  descending : ∀ n : ℕ, lower (n + 1) ≤ lower n

@[ext]
theorem Chapter04LowerFiltration.ext {G : Type u} [Group G]
    {F F' : Chapter04LowerFiltration G}
    (h : ∀ n : ℕ, F.lower n = F'.lower n) : F = F' := by
  cases F
  cases F'
  congr
  funext n
  exact h n

/-- Forget the displacement, normality, and eventual-triviality fields of the
canonical Chapter 2 filtration while retaining its lower groups. -/
def chapter04LowerFiltrationOfChapter02
    {G : Type u} [Group G] [Finite G]
    (F : LastLib.Book03RamificationTheory.Chapter02.Chapter02LowerFiltration G) :
    Chapter04LowerFiltration G where
  lower := F.group
  descending := F.descending

/-- The integer-indexed lower group associated to a nonnegative filtration.
All negative indices are sent to the `-1` level, as in the book. -/
def chapter04LowerGroup {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) (i : ℤ) : Subgroup G :=
  if i < 0 then ⊤ else F.lower i.toNat

@[simp]
theorem chapter04LowerGroup_neg_one {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) :
    chapter04LowerGroup F (-1) = ⊤ := by
  simp [chapter04LowerGroup]

theorem chapter04LowerGroup_of_nonnegative {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) {i : ℤ} (hi : 0 ≤ i) :
    chapter04LowerGroup F i = F.lower i.toNat := by
  simp [chapter04LowerGroup, not_lt.mpr hi]

theorem chapter04LowerFiltrationOfChapter02_lower_group
    {G : Type u} [Group G] [Finite G]
    (F : LastLib.Book03RamificationTheory.Chapter02.Chapter02LowerFiltration G)
    (i : ℤ) :
    chapter04LowerGroup (chapter04LowerFiltrationOfChapter02 F) i =
      LastLib.Book03RamificationTheory.Chapter02.chapter02IntegerLowerGroup F i := by
  rfl

theorem chapter04LowerFiltrationOfChapter02_lower_normal
    {G : Type u} [Group G] [Finite G]
    (F : LastLib.Book03RamificationTheory.Chapter02.Chapter02LowerFiltration G)
    (n : ℕ) :
    ((chapter04LowerFiltrationOfChapter02 F).lower n).Normal := by
  exact F.normal n

theorem chapter04LowerFiltrationOfChapter02_eventually_trivial
    {G : Type u} [Group G] [Finite G]
    (F : LastLib.Book03RamificationTheory.Chapter02.Chapter02LowerFiltration G) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (chapter04LowerFiltrationOfChapter02 F).lower n = ⊥ := by
  exact F.eventually_trivial

theorem chapter04LowerGroup_succ_le {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) (i : ℤ) (hi : -1 ≤ i) :
    chapter04LowerGroup F (i + 1) ≤ chapter04LowerGroup F i := by
  by_cases hneg : i < 0
  · have hi_eq : i = -1 := by omega
    subst i
    simp [chapter04LowerGroup]
  · have hi0 : 0 ≤ i := le_of_not_gt hneg
    have hi1 : 0 ≤ i + 1 := add_nonneg hi0 (by exact zero_le_one)
    rw [chapter04LowerGroup_of_nonnegative F hi1,
      chapter04LowerGroup_of_nonnegative F hi0]
    have hto : (i + 1).toNat = i.toNat + 1 := by
      apply Int.ofNat_inj.mp
      rw [Int.toNat_of_nonneg hi1]
      push_cast
      rw [Int.toNat_of_nonneg hi0]
    rw [hto]
    exact F.descending i.toNat

theorem chapter04LowerGroup_mono_anti {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) {i j : ℤ}
    (hi : -1 ≤ i) (hij : i ≤ j) :
    chapter04LowerGroup F j ≤ chapter04LowerGroup F i := by
  have hnat : ∀ a b : ℕ, a ≤ b → F.lower b ≤ F.lower a := by
    intro a b hab
    induction hab with
    | refl => exact le_rfl
    | @step b hab ih => exact (F.descending b).trans ih
  by_cases hjneg : j < 0
  · have hi_eq : i = -1 := by omega
    subst i
    simp [chapter04LowerGroup, hjneg]
  · have hj0 : 0 ≤ j := le_of_not_gt hjneg
    by_cases hineg : i < 0
    · have hi_eq : i = -1 := by omega
      subst i
      simp [chapter04LowerGroup]
    · have hi0 : 0 ≤ i := le_of_not_gt hineg
      rw [chapter04LowerGroup_of_nonnegative F hj0,
        chapter04LowerGroup_of_nonnegative F hi0]
      apply hnat
      exact_mod_cast (show (i.toNat : ℤ) ≤ (j.toNat : ℤ) by
        rw [Int.toNat_of_nonneg hi0, Int.toNat_of_nonneg hj0]
        exact hij)

/-- A jump of the integer lower filtration. -/
def chapter04LowerBreak {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) (i : ℤ) : Prop :=
  0 ≤ i ∧ chapter04LowerGroup F i ≠ chapter04LowerGroup F (i + 1)

/-- Restrict a lower filtration to a subgroup.  The resulting groups are
subgroups of the subgroup type, while `map subtype` recovers their ambient
intersection. -/
def chapter04SubgroupLowerFiltration {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) (H : Subgroup G) :
    Chapter04LowerFiltration H where
  lower n := (F.lower n).comap H.subtype
  descending := by
    intro n
    exact Subgroup.comap_mono (F.descending n)

theorem chapter04SubgroupLowerGroup_mem_iff {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) (H : Subgroup G) (i : ℤ) (σ : H) :
    σ ∈ chapter04LowerGroup (chapter04SubgroupLowerFiltration F H) i ↔
      (σ : G) ∈ chapter04LowerGroup F i := by
  by_cases hi : i < 0
  · simp [chapter04LowerGroup, hi]
  · simp [chapter04LowerGroup, hi, chapter04SubgroupLowerFiltration]; rfl

theorem chapter04SubgroupLowerGroup_map_eq_inf {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) (H : Subgroup G) (i : ℤ) :
    (chapter04LowerGroup (chapter04SubgroupLowerFiltration F H) i).map H.subtype =
      H ⊓ chapter04LowerGroup F i := by
  ext g
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨σ.property,
      (chapter04SubgroupLowerGroup_mem_iff F H i σ).mp hσ⟩
  · rintro ⟨hgH, hgF⟩
    let σ : H := ⟨g, hgH⟩
    refine ⟨σ, (chapter04SubgroupLowerGroup_mem_iff F H i σ).mpr hgF, rfl⟩

theorem chapter04SubgroupLowerBreak_implies_lowerBreak {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) (H : Subgroup G) (i : ℤ)
    (hbreak : chapter04LowerBreak (chapter04SubgroupLowerFiltration F H) i) :
    chapter04LowerBreak F i := by
  rcases hbreak with ⟨hi, hbreak⟩
  refine ⟨hi, ?_⟩
  intro heq
  apply hbreak
  ext σ
  rw [chapter04SubgroupLowerGroup_mem_iff F H i σ,
    chapter04SubgroupLowerGroup_mem_iff F H (i + 1) σ, heq]

/-- A break can disappear after restriction: the trivial subgroup sees no
nontrivial lower jump. -/
theorem chapter04LowerBreak_can_disappear {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) (i : ℤ)
    (hbreak : chapter04LowerBreak F i) :
    ∃ H : Subgroup G,
      ¬ chapter04LowerBreak (chapter04SubgroupLowerFiltration F H) i := by
  have hbreak_nonneg : 0 ≤ i := hbreak.1
  refine ⟨⊥, ?_⟩
  have hsub : ∀ S : Subgroup (⊥ : Subgroup G), S = ⊤ := by
    intro S
    apply top_unique
    intro σ hσ
    have hσ1 : σ = (1 : (⊥ : Subgroup G)) := by
      exact Subsingleton.elim _ _
    rw [hσ1]
    exact S.one_mem
  intro h
  rcases h with ⟨hi, hne⟩
  apply hne
  have hleft :
      chapter04LowerGroup (chapter04SubgroupLowerFiltration F (⊥ : Subgroup G)) i = ⊤ :=
    hsub _
  have hright :
      chapter04LowerGroup (chapter04SubgroupLowerFiltration F (⊥ : Subgroup G)) (i + 1) = ⊤ :=
    hsub _
  rw [hleft, hright]

/-- The lower cardinality profile, useful for comparing conjugate filtrations. -/
def chapter04LowerCardinalityProfile {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) : ℕ → ℕ :=
  fun n => Nat.card (F.lower n)

def chapter04SubgroupLowerCardinalityProfile {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) (H : Subgroup G) : ℕ → ℕ :=
  fun n => Nat.card ((F.lower n).comap H.subtype)

def chapter04ConjugateSubgroup {G : Type u} [Group G]
    (H : Subgroup G) (g : G) : Subgroup G :=
  H.map (MulAut.conj g).toMonoidHom

theorem chapter04_conjugate_subgroups_have_identical_lower_cardinality_profile
    {G : Type u} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) (H : Subgroup G) (g : G)
    (hconj : ∀ n : ℕ,
      (F.lower n).map (MulAut.conj g).toMonoidHom = F.lower n) :
    chapter04SubgroupLowerCardinalityProfile F
        (chapter04ConjugateSubgroup H g) =
      chapter04SubgroupLowerCardinalityProfile F H := by
  classical
  funext n
  change Nat.card ((F.lower n).comap (chapter04ConjugateSubgroup H g).subtype) =
    Nat.card ((F.lower n).comap H.subtype)
  let S := F.lower n
  let φ : G ≃* G := MulAut.conj g
  have hS : S.map φ.toMonoidHom = S := by
    simpa [S, φ] using hconj n
  have hSmem : ∀ z : G, z ∈ S.map φ.toMonoidHom ↔ z ∈ S := by
    intro z
    rw [hS]
  let H' : Subgroup G := H.map φ.toMonoidHom
  change Nat.card (S.comap H'.subtype) = Nat.card (S.comap H.subtype)
  let e : (S.comap H.subtype) → (S.comap H'.subtype) := fun x =>
    ⟨⟨φ x.1.1, by
        change φ x.1.1 ∈ H.map φ.toMonoidHom
        exact ⟨x.1.1, x.1.2, by simp⟩⟩,
      by
        have hxSmap : φ x.1.1 ∈ S.map φ.toMonoidHom :=
          ⟨x.1.1, x.2, by simp⟩
        have hxS : φ x.1.1 ∈ S := (hSmem _).mp hxSmap
        exact hxS⟩
  have he : Function.Bijective e := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      apply φ.injective
      simpa [e] using
        congrArg (fun z : H' => (z : G))
          (congrArg (fun z : S.comap H'.subtype => (z : H')) hxy)
    · intro y
      rcases y.1.2 with ⟨x, hx, hxy⟩
      have hyS : (y.1 : G) ∈ S := by
        exact y.2
      have hxy' : φ x = (y.1 : G) := by simpa using hxy
      have hxS : φ x ∈ S := by
        rw [hxy']
        exact hyS
      have hxm : φ x ∈ S.map φ.toMonoidHom := (hSmem _).mpr hxS
      rcases hxm with ⟨z, hz, hzx⟩
      have hzx' : z = x := φ.injective (by simpa using hzx)
      refine ⟨⟨⟨x, ?_⟩, ?_⟩, ?_⟩
      · exact hx
      · change x ∈ S
        simpa [hzx'] using hz
      · exact Subtype.ext (Subtype.ext (by simpa [e] using hxy))
  exact (Nat.card_congr (Equiv.ofBijective e he)).symm

/-- Conjugation transports a filtration by a group automorphism. -/
def chapter04ConjugateLowerFiltration {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) (g : G) :
    Chapter04LowerFiltration G where
  lower n := (F.lower n).map (MulAut.conj g).toMonoidHom
  descending := by
    intro n
    exact Subgroup.map_mono (F.descending n)

theorem chapter04ConjugateLowerCardinalityProfile_eq
    {G : Type u} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) (g : G) :
    chapter04LowerCardinalityProfile (chapter04ConjugateLowerFiltration F g) =
      chapter04LowerCardinalityProfile F := by
  funext n
  change Nat.card ((F.lower n).map (MulAut.conj g).toMonoidHom) =
    Nat.card (F.lower n)
  exact
    (Nat.card_congr
      (Subgroup.equivMapOfInjective (F.lower n)
        (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)).symm

theorem chapter04ConjugateLowerBreak_iff
    {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) (g : G) (i : ℤ) :
    chapter04LowerBreak (chapter04ConjugateLowerFiltration F g) i ↔
      chapter04LowerBreak F i := by
  let φ : G ≃* G := MulAut.conj g
  have hgroup : ∀ j : ℤ,
      chapter04LowerGroup (chapter04ConjugateLowerFiltration F g) j =
        (chapter04LowerGroup F j).map φ.toMonoidHom := by
    intro j
    by_cases hj : j < 0
    · simp [chapter04LowerGroup, hj, φ]
    · simp [chapter04LowerGroup, chapter04ConjugateLowerFiltration, hj, φ]
  have hmap_inj : ∀ A B : Subgroup G,
      A.map φ.toMonoidHom = B.map φ.toMonoidHom → A = B := by
    intro A B hab
    ext x
    constructor
    · intro hx
      have hxm : φ x ∈ B.map φ.toMonoidHom := by
        rw [← hab]
        exact ⟨x, hx, by simp⟩
      rcases hxm with ⟨y, hy, hyx⟩
      have hyx' : y = x := φ.injective (by simpa using hyx)
      simpa [hyx'] using hy
    · intro hx
      have hxm : φ x ∈ B.map φ.toMonoidHom := by
        exact ⟨x, hx, by simp⟩
      rw [← hab] at hxm
      rcases hxm with ⟨y, hy, hyx⟩
      have hyx' : y = x := φ.injective (by simpa using hyx)
      simpa [hyx'] using hy
  constructor
  · rintro ⟨hi, hne⟩
    refine ⟨hi, ?_⟩
    intro heq
    apply hne
    rw [hgroup i, hgroup (i + 1), heq]
  · rintro ⟨hi, hne⟩
    refine ⟨hi, ?_⟩
    intro heq
    apply hne
    apply hmap_inj
    rw [← hgroup i, ← hgroup (i + 1)]
    exact heq

/-- The real lower-index convention from §4.3: ceiling on nonnegative
indices, and the `-1` group on the negative interval. -/
def chapter04RealLowerGroup {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) (u : ℝ) : Subgroup G :=
  if u < 0 then ⊤ else F.lower (Int.ceil u).toNat

theorem chapter04RealLowerGroup_zero {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) :
    chapter04RealLowerGroup F 0 = F.lower 0 := by
  simp [chapter04RealLowerGroup]

theorem chapter04RealLowerGroup_neg {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) {u : ℝ}
    (hu : -1 ≤ u) (hu0 : u < 0) :
    chapter04RealLowerGroup F u = ⊤ := by
  have hu_domain : (-1 : ℝ) ≤ u := hu
  simp [chapter04RealLowerGroup, hu0]

theorem chapter04RealLowerGroup_on_right_closed_unit_interval
    {G : Type u} [Group G] (F : Chapter04LowerFiltration G) (m : ℕ)
    {x : ℝ} (hm : (m : ℝ) < x) (hm' : x ≤ (m + 1 : ℕ)) :
    chapter04RealLowerGroup F x = F.lower (m + 1) := by
  have hx0 : 0 ≤ x := by
    exact le_trans (Nat.cast_nonneg m) (le_of_lt hm)
  simp only [chapter04RealLowerGroup, if_neg (not_lt.mpr hx0)]
  have hceil : Int.ceil x = (m + 1 : ℤ) := by
    rw [Int.ceil_eq_iff]
    constructor
    · simpa using hm
    · simpa using hm'
  rw [hceil]
  simp

/-- The alternative floor convention, recorded so endpoint choices are
explicit rather than silently mixed. -/
def chapter04FloorRealLowerGroup {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) (u : ℝ) : Subgroup G :=
  if u < 0 then ⊤ else F.lower (Int.floor u).toNat

theorem chapter04FloorRealLowerGroup_on_left_closed_unit_interval
    {G : Type u} [Group G] (F : Chapter04LowerFiltration G) (m : ℕ)
    {x : ℝ} (hm : (m : ℝ) ≤ x) (hm' : x < (m + 1 : ℕ)) :
    chapter04FloorRealLowerGroup F x = F.lower m := by
  have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg m) hm
  simp only [chapter04FloorRealLowerGroup, if_neg (not_lt.mpr hx0)]
  have hfloor : Int.floor x = (m : ℤ) := by
    rw [Int.floor_eq_iff]
    constructor
    · simpa using hm
    · simpa using hm'
  rw [hfloor]
  simp

theorem chapter04RealLowerGroup_at_integer
    {G : Type u} [Group G] (F : Chapter04LowerFiltration G) (m : ℕ) :
    chapter04RealLowerGroup F m = F.lower m := by
  simp [chapter04RealLowerGroup]

/-- The reciprocal index appearing in Herbrand's integral. -/
def chapter04HerbrandIntegrand
    {G : Type u} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) (u : ℝ) : ℝ :=
  ((chapter04RealLowerGroup F u).relIndex (F.lower 0) : ℝ)⁻¹

/-- The Herbrand function on all real indices, with the identity extension on
negative indices.  Its ramification-theoretic domain is `[-1, ∞)`. -/
def chapter04HerbrandFunction
    {G : Type u} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) (u : ℝ) : ℝ :=
  if 0 ≤ u then
    ∫ t in (0 : ℝ)..u, chapter04HerbrandIntegrand F t
  else u

theorem chapter04HerbrandFunction_of_nonpositive
    {G : Type u} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) {u : ℝ} (hu : u ≤ 0) :
    chapter04HerbrandFunction F u = u := by
  by_cases hu0 : 0 ≤ u
  · have huzero : u = 0 := le_antisymm hu hu0
    subst u
    simp [chapter04HerbrandFunction]
  · simp [chapter04HerbrandFunction, hu0]

theorem chapter04HerbrandFunction_zero
    {G : Type u} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) :
    chapter04HerbrandFunction F 0 = 0 := by
  exact chapter04HerbrandFunction_of_nonpositive F le_rfl

/-- The book's inverse notation, defined after the homeomorphism theorem. -/
noncomputable def chapter04HerbrandInverse
    {G : Type u} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) : ℝ → ℝ :=
  Function.invFun (chapter04HerbrandFunction F)

/-- A piecewise-linear value used for the closed formula in §4.4. -/
def chapter04HerbrandPiecewiseValue
    {G : Type u} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) (m : ℕ) (u : ℝ) : ℝ :=
  (1 / (Nat.card (F.lower 0) : ℝ)) *
    (Finset.sum (Finset.Icc 1 m) (fun j => (Nat.card (F.lower j) : ℝ)) +
      (u - m) * Nat.card (F.lower (m + 1)))

def chapter04HerbrandSlope
    {G : Type u} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) (m : ℕ) : ℝ :=
  (Nat.card (F.lower (m + 1)) : ℝ) / Nat.card (F.lower 0)

/-- The valuation-ring realization of the lower filtration.  Book 2's group
`n` is the congruence modulo the `n`th maximal-ideal power, hence it is the
`(n + 1)`st lower group in the convention of this chapter. -/
def chapter04ValuationLowerFiltration
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) :
    Chapter04LowerFiltration
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup K A) where
  lower n :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup K A (n + 1)
  descending := by
    intro n
    simpa [Nat.add_assoc] using
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup_succ_le
        A (n + 1))

theorem chapter04ValuationLowerFiltration_zero_eq_inertia
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) :
    (chapter04ValuationLowerFiltration K A).lower 0 =
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05InertiaGroup K A := by
  simpa [chapter04ValuationLowerFiltration] using
    (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FirstRamificationGroup_eq_inertia
      A)

/-- The same valuation filtration transported into the ambient Galois group.
When the chosen valuation branch is unique, the decomposition subgroup is all
of `Gal(L / K)`, so this is exactly the source notation `Gᵢ`. -/
def chapter04GaloisLowerFiltration
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) : Chapter04LowerFiltration (Gal(L / K)) where
  lower n :=
    (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup
      K A (n + 1)).map
      (Subgroup.subtype
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
          K A))
  descending := by
    intro n
    exact Subgroup.map_mono
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup_succ_le
        A (n + 1))

theorem chapter04GaloisLowerFiltration_zero_eq_inertia
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) :
    (chapter04GaloisLowerFiltration K A).lower 0 =
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05InertiaGroupInG K A := by
  change
    (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup
      K A 1).map (Subgroup.subtype
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
          K A)) = _
  rw [LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FirstRamificationGroup_eq_inertia]
  rfl

/-- A branch preserved by every Galois automorphism has full decomposition
group, the field-theoretic hypothesis under which the ambient filtration really
has `G = Gal(L / K)` at level `-1`. -/
theorem chapter04_decomposition_group_eq_top_of_branch_preserved
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L)
    (hA : ∀ σ : Gal(L / K), σ • A = A) :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
        K A = ⊤ := by
  apply top_unique
  intro σ hσ
  exact
    (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.decomposition_group_membership_iff_valuation_ring_stable
      A σ).mpr (hA σ)

theorem chapter04ValuationLowerFiltration_neg_one_eq_top
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) :
    chapter04LowerGroup (chapter04ValuationLowerFiltration K A) (-1) = ⊤ := by
  exact chapter04LowerGroup_neg_one _

end
end LastLib.Book03RamificationTheory.Chapter04
