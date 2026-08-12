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
  sorry

theorem chapter06QuotientTransition_surjective
    {P : ProfiniteGrp} {N M : OpenNormalSubgroup P} (h : N ≤ M) :
    Function.Surjective (chapter06QuotientTransition h) := by
  sorry

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
  sorry

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
  sorry

def chapter06InfiniteUpperClosedSubgroup
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P) (v : ℝ) :
    ClosedSubgroup P :=
  { toSubgroup := chapter06InfiniteUpperGroup S v
    isClosed' := chapter06InfiniteUpperGroup_closed S v }

theorem chapter06InfiniteUpperGroup_normal
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P) (v : ℝ) :
    (chapter06InfiniteUpperGroup S v).Normal := by
  sorry

instance chapter06InfiniteUpperGroup_normal_instance
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P) (v : ℝ) :
    (chapter06InfiniteUpperGroup S v).Normal :=
  chapter06InfiniteUpperGroup_normal S v

theorem chapter06InfiniteUpperGroup_antitone
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P) :
    Antitone (chapter06InfiniteUpperGroup S) := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the image equality is the compactness/cofinality
bridge from the inverse-limit intersection to a finite quotient.  It is the
map form of the source's assertion that the finite quotient recovers its upper
group, and is kept separate from the definition of the intersection. -/
theorem chapter06InfiniteUpperGroup_map
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P)
    (N : OpenNormalSubgroup P) (v : ℝ) :
    (chapter06InfiniteUpperGroup S v).map (chapter06QuotientMap N) =
      chapter05UpperRamificationGroup (S.upperProfile N) v := by
  sorry

/-!
In the profinite convention a right limit is the closure of the union over
strictly larger indices.  The closure disappears after projection to a finite
quotient, but is retained in the ambient definition.
-/

def chapter06InfiniteUpperRightLimit
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P) (v : ℝ) : Subgroup P :=
  Subgroup.closure {g : P |
    ∃ w : ℝ, v < w ∧ g ∈ chapter06InfiniteUpperGroup S w}

abbrev chapter06InfiniteUpperGroupPlus
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P) (v : ℝ) : Subgroup P :=
  chapter06InfiniteUpperRightLimit S v

theorem chapter06InfiniteUpperRightLimit_closed
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P) (v : ℝ) :
    IsClosed (chapter06InfiniteUpperRightLimit S v : Set P) := by
  sorry

def chapter06InfiniteUpperRightLimitClosedSubgroup
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P) (v : ℝ) :
    ClosedSubgroup P :=
  { toSubgroup := chapter06InfiniteUpperRightLimit S v
    isClosed' := chapter06InfiniteUpperRightLimit_closed S v }

theorem chapter06InfiniteUpperRightLimit_normal
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P) (v : ℝ) :
    (chapter06InfiniteUpperRightLimit S v).Normal := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: identifying the image of the ambient closure with
the finite right limit needs the cofinality/compactness bridge for the chosen
profinite Galois system.  It is recorded as an interface here rather than
being built into the definition of the infinite group. -/
theorem chapter06InfiniteUpperRightLimit_map
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P)
    (N : OpenNormalSubgroup P) (v : ℝ) :
    (chapter06InfiniteUpperRightLimit S v).map (chapter06QuotientMap N) =
      chapter05UpperRightLimit (S.upperProfile N) v := by
  sorry

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
  sorry

theorem chapter06WildInertiaGroup_normal
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P) :
    (chapter06WildInertiaGroup S).Normal := by
  sorry

instance chapter06WildInertiaGroup_normal_instance
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P) :
    (chapter06WildInertiaGroup S).Normal :=
  chapter06WildInertiaGroup_normal S

end

end LastLib.Book03RamificationTheory.Chapter06
