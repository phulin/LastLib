import LastLib.Book03RamificationTheory.Chapter06.Dependencies
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.RepresentationTheory.Invariants
import Mathlib.Data.Finset.Sort

namespace LastLib.Book03RamificationTheory.Chapter06

noncomputable section

open LastLib.Book03RamificationTheory.Chapter05

open MeasureTheory

universe u v w

/-! ## 6.2. Finite-image representations need only finite levels -/

/- The source assumes continuity as well as finite image.  Since the target
 representation is kept algebraic here, openness of the kernel is the exact
 finite-quotient consequence of that continuity assumption and is recorded
 explicitly in the interface below. -/

/-- A finite-image representation of a profinite group with its open kernel. -/
structure Chapter06FiniteImageRepresentation
    (E : Type u) (P : ProfiniteGrp) (V : Type w)
    [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V] where
  toRepresentation : Representation E P V
  finite_image : (Set.range toRepresentation).Finite
  kernel_open : IsOpen (MonoidHom.ker toRepresentation : Set P)

namespace Chapter06FiniteImageRepresentation

variable {E : Type u} {P : ProfiniteGrp} {V : Type w}
variable [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]

instance : CoeFun (Chapter06FiniteImageRepresentation E P V)
    (fun _ => Representation E P V) :=
  ⟨Chapter06FiniteImageRepresentation.toRepresentation⟩

@[simp]
theorem coe_toRepresentation
    (ρ : Chapter06FiniteImageRepresentation E P V) :
    (ρ : Representation E P V) = ρ.toRepresentation := rfl

def kernel (ρ : Chapter06FiniteImageRepresentation E P V) : Subgroup P :=
  MonoidHom.ker ρ.toRepresentation

theorem kernel_isOpen (ρ : Chapter06FiniteImageRepresentation E P V) :
    IsOpen (ρ.kernel : Set P) := by
  exact ρ.kernel_open

theorem finite_image_range (ρ : Chapter06FiniteImageRepresentation E P V) :
    (Set.range ρ.toRepresentation).Finite :=
  ρ.finite_image

def ofFiniteLevel
    (N : OpenNormalSubgroup P) (ρ : Representation E (P ⧸ N.toSubgroup) V) :
    Chapter06FiniteImageRepresentation E P V where
  toRepresentation := ρ.comp (chapter06QuotientMap N)
  finite_image := by
    let _ : Finite (P ⧸ N.toSubgroup) :=
      Subgroup.quotient_finite_of_isOpen N.toOpenSubgroup.toSubgroup
        N.toOpenSubgroup.isOpen
    apply (Set.finite_range ρ).subset
    rintro x ⟨g, rfl⟩
    exact ⟨chapter06QuotientMap N g, rfl⟩
  kernel_open := by
    refine Subgroup.isOpen_mono ?_ N.toOpenSubgroup.isOpen
    intro x hx
    apply MonoidHom.mem_ker.mpr
    change ρ (chapter06QuotientMap N x) = 1
    have hq : chapter06QuotientMap N x = 1 := by
      rw [chapter06QuotientMap_apply]
      exact (QuotientGroup.eq_one_iff x).2 hx
    rw [hq]
    exact ρ.map_one

@[ext]
theorem ext {ρ σ : Chapter06FiniteImageRepresentation E P V}
    (h : ρ.toRepresentation = σ.toRepresentation) : ρ = σ := by
  cases ρ
  cases σ
  cases h
  rfl

end Chapter06FiniteImageRepresentation

/-!
A chosen open normal level supplies the finite quotient used for every
finite-level invariant.  The existence theorem below is the factorization
statement from the source; retaining the level in the witness makes later
quotient-comparison lemmas explicit.
-/

structure Chapter06FiniteLevelRepresentation
    {E : Type u} {P : ProfiniteGrp} {V : Type w}
    [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (ρ : Chapter06FiniteImageRepresentation E P V) where
  level : OpenNormalSubgroup P
  action : Representation E (P ⧸ level.toSubgroup) V
  factorization : ρ.toRepresentation =
    action.comp (chapter06QuotientMap level)

def Chapter06FiniteLevelRepresentation.ofFiniteLevel
    {E : Type u} {P : ProfiniteGrp} {V : Type w}
    [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (N : OpenNormalSubgroup P)
    (ρ : Representation E (P ⧸ N.toSubgroup) V) :
    Chapter06FiniteLevelRepresentation
      (Chapter06FiniteImageRepresentation.ofFiniteLevel N ρ) where
  level := N
  action := ρ
  factorization := by
    rfl

theorem chapter06FiniteImageRepresentation_factors
    {E : Type u} {P : ProfiniteGrp} {V : Type w}
    [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (ρ : Chapter06FiniteImageRepresentation E P V) :
    Nonempty (Chapter06FiniteLevelRepresentation ρ) := by
  let K : OpenNormalSubgroup P :=
    { toOpenSubgroup :=
        { toSubgroup := ρ.kernel
          isOpen' := ρ.kernel_isOpen }
      isNormal' := by
        change (MonoidHom.ker ρ.toRepresentation).Normal
        infer_instance }
  let _ : K.toSubgroup.Normal := K.isNormal'
  let _ : Representation.IsTrivial
      (ρ.toRepresentation.comp K.toSubgroup.subtype) := by
    constructor
    intro g
    change ρ.toRepresentation (g : P) = LinearMap.id
    ext v
    have hg : (g : P) ∈ ρ.kernel := g.property
    rw [MonoidHom.mem_ker.mpr hg]
    rfl
  refine ⟨{
    level := K
    action := Representation.ofQuotient ρ.toRepresentation K.toSubgroup
    factorization := by
      ext g v
      change ρ.toRepresentation g v =
        (Representation.ofQuotient ρ.toRepresentation K.toSubgroup)
          (chapter06QuotientMap K g) v
      simpa only [chapter06QuotientMap_apply] using
        (Representation.ofQuotient_coe_apply
          ρ.toRepresentation K.toSubgroup g v).symm
  }⟩

namespace Chapter06FiniteLevelRepresentation

variable {E : Type u} {P : ProfiniteGrp} {V : Type w}
variable [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]

theorem factorization_apply
    {ρ : Chapter06FiniteImageRepresentation E P V}
    (R : Chapter06FiniteLevelRepresentation ρ) (g : P) :
    ρ.toRepresentation g = R.action (chapter06QuotientMap R.level g) := by
  exact DFunLike.congr_fun R.factorization g

theorem kernel_acts_trivially
    {ρ : Chapter06FiniteImageRepresentation E P V}
    (R : Chapter06FiniteLevelRepresentation ρ) :
    ∀ g : P, g ∈ (chapter06QuotientMap R.level).ker →
      ρ.toRepresentation g = LinearMap.id := by
  intro g hg
  have hq : chapter06QuotientMap R.level g = 1 :=
    MonoidHom.mem_ker.mp hg
  calc
    ρ.toRepresentation g = R.action (chapter06QuotientMap R.level g) :=
      DFunLike.congr_fun R.factorization g
    _ = R.action 1 := by
      rw [hq]
    _ = LinearMap.id := by
      have hone : (1 : V →ₗ[E] V) = LinearMap.id := rfl
      exact (R.action.map_one).trans hone

@[ext (iff := false)]
theorem ext
    {ρ : Chapter06FiniteImageRepresentation E P V}
    {R T : Chapter06FiniteLevelRepresentation ρ}
    (hlevel : R.level = T.level) (haction : HEq R.action T.action) : R = T := by
  cases R
  cases T
  cases hlevel
  cases haction
  rfl

end Chapter06FiniteLevelRepresentation

def chapter06FiniteLevelProfile
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P)
    {E : Type u} {V : Type w} [Field E] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V]
    {ρ : Chapter06FiniteImageRepresentation E P V}
    (R : Chapter06FiniteLevelRepresentation ρ) :
    Chapter05RamificationFiltration (P ⧸ R.level.toSubgroup) :=
  S.upperProfile R.level

/-!
The following fixed-space API is the canonical invariant-space construction
used at every finite level.  The quotient comparison theorem is stated for an
arbitrary subgroup, so upper groups, inertia, and wild inertia all reuse it.
-/

def chapter06FixedSpace
    {E : Type u} {G : Type v} {V : Type w}
    [Field E] [Group G] [AddCommGroup V] [Module E V]
    (ρ : Representation E G V) (H : Subgroup G) : Submodule E V :=
  Representation.invariants (ρ.comp H.subtype)

namespace chapter06FixedSpace

variable {E : Type u} {G : Type v} {V : Type w}
variable [Field E] [Group G] [AddCommGroup V] [Module E V]

theorem mem_iff (ρ : Representation E G V) (H : Subgroup G) (v : V) :
    v ∈ chapter06FixedSpace ρ H ↔ ∀ h : H, ρ h v = v := by
  rfl

theorem comp_eq_map {H : Type*} [Group H]
    (ρ : Representation E G V) (φ : H →* G) (S : Subgroup H) :
    chapter06FixedSpace (ρ.comp φ) S =
      chapter06FixedSpace ρ (S.map φ) := by
  apply Submodule.ext
  intro v
  rw [mem_iff, mem_iff]
  constructor
  · intro h y
    rcases y.property with ⟨s, hs, hsy⟩
    let y' : S.map φ :=
      ⟨φ s, Subgroup.mem_map.mpr ⟨s, hs, rfl⟩⟩
    have hy : y = y' := by
      apply Subtype.ext
      exact hsy.symm
    simpa [hy] using h ⟨s, hs⟩
  · intro h s
    have hy := h
      (⟨φ s, Subgroup.mem_map.mpr ⟨s, s.property, rfl⟩⟩ : S.map φ)
    change ρ (φ s) v = v
    exact hy

theorem antitone {H K : Subgroup G} (ρ : Representation E G V)
    (hHK : H ≤ K) :
    chapter06FixedSpace ρ K ≤ chapter06FixedSpace ρ H := by
  intro v hv h
  rw [mem_iff] at hv
  exact hv (⟨(h : G), hHK h.property⟩ : K)

end chapter06FixedSpace

def chapter06FixedSpaceCodim
    {E : Type u} {G : Type v} {V : Type w}
    [Field E] [Group G] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V]
    (ρ : Representation E G V) (H : Subgroup G) : ℕ :=
  Module.finrank E (V ⧸ chapter06FixedSpace ρ H)

def chapter06FixedSpaceCodimReal
    {E : Type u} {G : Type v} {V : Type w}
    [Field E] [Group G] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V]
    (ρ : Representation E G V) (H : Subgroup G) : ℝ :=
  (chapter06FixedSpaceCodim ρ H : ℝ)

theorem chapter06FixedSpaceCodim_congr
    {E : Type u} {G : Type v} {V : Type w}
    [Field E] [Group G] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V]
    {ρ σ : Representation E G V} (hρ : ρ = σ) (H : Subgroup G) :
    chapter06FixedSpaceCodim ρ H = chapter06FixedSpaceCodim σ H := by
  cases hρ
  rfl

def chapter06UpperFixedSpaceCodim
    {E : Type u} {G : Type v} {V : Type w}
    [Field E] [Group G] [Finite G] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V]
    (D : Chapter05RamificationFiltration G)
    (ρ : Representation E G V) (v : ℝ) : ℕ :=
  chapter06FixedSpaceCodim ρ (chapter05UpperRamificationGroup D v)

def chapter06UpperFixedSpaceCodimReal
    {E : Type u} {G : Type v} {V : Type w}
    [Field E] [Group G] [Finite G] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V]
    (D : Chapter05RamificationFiltration G)
    (ρ : Representation E G V) (v : ℝ) : ℝ :=
  (chapter06UpperFixedSpaceCodim D ρ v : ℝ)

/-!
These wrappers make the source's “compute in the finite field cut out by the
representation” convention explicit.  They are definitions, not additional
infinite sums or limits.
-/

def chapter06FiniteLevelUpperFixedSpaceCodim
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P)
    {E : Type u} {V : Type w} [Field E] [AddCommGroup V]
    [Module E V] [FiniteDimensional E V]
    {ρ : Chapter06FiniteImageRepresentation E P V}
    (R : Chapter06FiniteLevelRepresentation ρ) (v : ℝ) : ℕ :=
  chapter06UpperFixedSpaceCodim (S.upperProfile R.level) R.action v

theorem chapter06UpperFixedSpaceCodim_transition
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P)
    {N M : OpenNormalSubgroup P} (h : N ≤ M)
    {E : Type u} {V : Type w} [Field E] [AddCommGroup V]
    [Module E V] [FiniteDimensional E V]
    (ρ : Representation E (P ⧸ M.toSubgroup) V) (v : ℝ) :
    chapter06UpperFixedSpaceCodim (S.upperProfile N)
        (ρ.comp (chapter06QuotientTransition h)) v =
      chapter06UpperFixedSpaceCodim (S.upperProfile M) ρ v := by
  unfold chapter06UpperFixedSpaceCodim chapter06FixedSpaceCodim
  rw [chapter06FixedSpace.comp_eq_map, S.transition_upper_map h v]

/-!
Representation breaks are defined from the jump behavior of the fixed-space
codimension function.  This is a book-facing definition, independent of an
enumeration of all real numbers, and its finite-level computation is explicit.
-/

def chapter06RepresentationUpperBreak
    {E : Type u} {G : Type v} {V : Type w}
    [Field E] [Group G] [Finite G] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V]
    (D : Chapter05RamificationFiltration G)
    (ρ : Representation E G V) (r : ℝ) : Prop :=
  0 ≤ r ∧
    ((r = 0 ∧
        chapter06FixedSpace ρ (chapter05UpperRightLimit D 0) ≠ ⊥) ∨
      (0 < r ∧
        ∀ ε : ℝ, 0 < ε →
          ∃ u w : ℝ,
            r - ε < u ∧ u ≤ r ∧ r < w ∧ w < r + ε ∧
              chapter06UpperFixedSpaceCodim D ρ u ≠
                chapter06UpperFixedSpaceCodim D ρ w))

def chapter06RepresentationUpperBreakSet
    {E : Type u} {G : Type v} {V : Type w}
    [Field E] [Group G] [Finite G] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V]
    (D : Chapter05RamificationFiltration G)
    (ρ : Representation E G V) : Set ℝ :=
  {r | chapter06RepresentationUpperBreak D ρ r}

theorem chapter06RepresentationUpperBreakSet_finite
    {E : Type u} {G : Type v} {V : Type w}
    [Field E] [Group G] [Finite G] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D))
    (ρ : Representation E G V) :
    (chapter06RepresentationUpperBreakSet D ρ).Finite := by
  classical
  let U : ℝ → Subgroup G := chapter05UpperRamificationGroup D
  have hUanti : Antitone U := by
    simpa [U] using chapter05_upper_filtration_antitone D hbij
  have hright_mem : ∀ r : ℝ, ∃ w : ℝ, r < w ∧
      U w = chapter05UpperRightLimit D r := by
    intro r
    let A : Set (Subgroup G) := U '' Set.Ioi r
    have hA_nonempty : A.Nonempty := by
      refine ⟨U (r + 1), ?_⟩
      exact ⟨r + 1, by norm_num, rfl⟩
    have hA_supClosed : SupClosed A := by
      intro H hH K hK
      rcases hH with ⟨x, hx, rfl⟩
      rcases hK with ⟨y, hy, rfl⟩
      by_cases hxy : x ≤ y
      · rw [sup_eq_left.mpr (hUanti hxy)]
        exact ⟨x, hx, rfl⟩
      · have hyx : y ≤ x := le_of_not_ge hxy
        rw [sup_eq_right.mpr (hUanti hyx)]
        exact ⟨y, hy, rfl⟩
    have hmem : sSup A ∈ A :=
      hA_supClosed.sSup_mem_of_nonempty (Set.toFinite A) hA_nonempty
        (by intro x hx; exact hx)
    rcases hmem with ⟨w, hw, hUw⟩
    exact ⟨w, hw, by simpa [A, U, chapter05UpperRightLimit, chapter05RightLimit] using hUw⟩
  have hleft_mem : ∀ {r : ℝ}, 0 < r → ∃ u : ℝ, u < r ∧ U u = U r := by
    intro r hr
    let A : Set (Subgroup G) := U '' Set.Ioo (-1 : ℝ) r
    have hA_nonempty : A.Nonempty := by
      refine ⟨U (r / 2), ?_⟩
      exact ⟨r / 2, by constructor <;> linarith, rfl⟩
    have hA_infClosed : InfClosed A := by
      intro H hH K hK
      rcases hH with ⟨x, hx, rfl⟩
      rcases hK with ⟨y, hy, rfl⟩
      by_cases hxy : x ≤ y
      · rw [inf_eq_right.mpr (hUanti hxy)]
        exact ⟨y, hy, rfl⟩
      · have hyx : y ≤ x := le_of_not_ge hxy
        rw [inf_eq_left.mpr (hUanti hyx)]
        exact ⟨x, hx, rfl⟩
    have hmem : sInf A ∈ A :=
      hA_infClosed.sInf_mem_of_nonempty (Set.toFinite A) hA_nonempty
        (by intro x hx; exact hx)
    rcases hmem with ⟨u, hu, hUu⟩
    have hleft : U r = sInf A := by
      simpa [A, U, chapter05LeftContinuousOnPositive] using
        ((chapter05_upper_filtration_left_continuous_on_positive D hbij) r hr)
    exact ⟨u, hu.2, hUu.trans hleft.symm⟩
  have hrepr_subset :
      chapter06RepresentationUpperBreakSet D ρ ⊆
        chapter05UpperBreakSet D ∪ ({0} : Set ℝ) := by
    intro r hr
    change chapter06RepresentationUpperBreak D ρ r at hr
    rcases hr with ⟨hr_nonneg, hcases⟩
    by_cases hr0 : r = 0
    · subst r
      exact Or.inr rfl
    · have hrpos : 0 < r := lt_of_le_of_ne hr_nonneg (Ne.symm hr0)
      left
      change chapter05UpperBreak D r
      rw [chapter05UpperBreak, if_neg (by linarith)]
      have hnot : U r ≠ chapter05UpperRightLimit D r := by
        intro heq
        obtain ⟨w₀, hw₀, hUw₀⟩ := hright_mem r
        obtain ⟨u₀, hu₀, hUu₀⟩ := hleft_mem hrpos
        have hε : 0 < min (r - u₀) (w₀ - r) := by
          exact lt_min (sub_pos.mpr hu₀) (sub_pos.mpr hw₀)
        rcases hcases with hzero | hpositive
        · exact (hr0 hzero.1).elim
        · rcases hpositive with ⟨_, hlocal⟩
          rcases hlocal (min (r - u₀) (w₀ - r)) hε with
            ⟨u, w, hu_left, hu_right, hw_left, hw_right, hcodim⟩
          have hu₀u : u₀ ≤ u := by
            have hmin : min (r - u₀) (w₀ - r) ≤ r - u₀ := min_le_left _ _
            linarith
          have huw : U u = U r := by
            apply le_antisymm
            · calc
                U u ≤ U u₀ := hUanti hu₀u
                _ = U r := hUu₀
            · exact hUanti hu_right
          have hww₀ : w ≤ w₀ := by
            have hmin : min (r - u₀) (w₀ - r) ≤ w₀ - r := min_le_right _ _
            linarith
          have hww : U w = U r := by
            apply le_antisymm
            · exact hUanti hw_left.le
            · calc
                U r = U w₀ := heq.trans hUw₀.symm
                _ ≤ U w := hUanti hww₀
          have hcodim_eq :
              chapter06UpperFixedSpaceCodim D ρ u =
                chapter06UpperFixedSpaceCodim D ρ w := by
            change chapter06FixedSpaceCodim ρ (U u) =
              chapter06FixedSpaceCodim ρ (U w)
            rw [huw, hww]
          exact hcodim hcodim_eq
      refine ⟨by linarith, ?_⟩
      simpa [U] using hnot
  exact (chapter05_upper_breaks_finite D hbij).union
    (Set.finite_singleton (0 : ℝ)) |>.subset hrepr_subset

theorem chapter06RepresentationUpperBreakSet_transition
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P)
    {N M : OpenNormalSubgroup P} (h : N ≤ M)
    {E : Type u} {V : Type w} [Field E] [AddCommGroup V]
    [Module E V] [FiniteDimensional E V]
    (ρ : Representation E (P ⧸ M.toSubgroup) V) :
    chapter06RepresentationUpperBreakSet (S.upperProfile N)
        (ρ.comp (chapter06QuotientTransition h)) =
      chapter06RepresentationUpperBreakSet (S.upperProfile M) ρ := by
  ext r
  change chapter06RepresentationUpperBreak (S.upperProfile N)
      (ρ.comp (chapter06QuotientTransition h)) r ↔
    chapter06RepresentationUpperBreak (S.upperProfile M) ρ r
  simp only [chapter06RepresentationUpperBreak]
  have hright :
      (chapter05UpperRightLimit (S.upperProfile N) 0).map
          (chapter06QuotientTransition h) =
        chapter05UpperRightLimit (S.upperProfile M) 0 := by
    rw [← chapter06InfiniteUpperRightLimit_map S N 0,
      ← chapter06InfiniteUpperRightLimit_map S M 0]
    rw [Subgroup.map_map]
    rw [chapter06QuotientTransition_comp_quotientMap h]
  have hfixed :
      chapter06FixedSpace (ρ.comp (chapter06QuotientTransition h))
          (chapter05UpperRightLimit (S.upperProfile N) 0) =
        chapter06FixedSpace ρ (chapter05UpperRightLimit (S.upperProfile M) 0) := by
    rw [chapter06FixedSpace.comp_eq_map, hright]
  constructor
  · rintro ⟨hr_nonneg, hcases⟩
    refine ⟨hr_nonneg, ?_⟩
    rcases hcases with hzero | hpositive
    · left
      rcases hzero with ⟨hr0, hne⟩
      exact ⟨hr0, by simpa [hfixed] using hne⟩
    · right
      refine ⟨hpositive.1, ?_⟩
      intro ε hε
      rcases hpositive.2 ε hε with
        ⟨u, w, hu_left, hu_right, hw_left, hw_right, hne⟩
      refine ⟨u, w, hu_left, hu_right, hw_left, hw_right, ?_⟩
      intro heq
      apply hne
      calc
        chapter06UpperFixedSpaceCodim (S.upperProfile N)
              (ρ.comp (chapter06QuotientTransition h)) u =
            chapter06UpperFixedSpaceCodim (S.upperProfile M) ρ u :=
          chapter06UpperFixedSpaceCodim_transition S h ρ u
        _ = chapter06UpperFixedSpaceCodim (S.upperProfile M) ρ w := by
          exact heq
        _ = chapter06UpperFixedSpaceCodim (S.upperProfile N)
              (ρ.comp (chapter06QuotientTransition h)) w :=
          (chapter06UpperFixedSpaceCodim_transition S h ρ w).symm
  · rintro ⟨hr_nonneg, hcases⟩
    refine ⟨hr_nonneg, ?_⟩
    rcases hcases with hzero | hpositive
    · left
      rcases hzero with ⟨hr0, hne⟩
      exact ⟨hr0, by simpa [hfixed] using hne⟩
    · right
      refine ⟨hpositive.1, ?_⟩
      intro ε hε
      rcases hpositive.2 ε hε with
        ⟨u, w, hu_left, hu_right, hw_left, hw_right, hne⟩
      refine ⟨u, w, hu_left, hu_right, hw_left, hw_right, ?_⟩
      intro heq
      apply hne
      calc
        chapter06UpperFixedSpaceCodim (S.upperProfile M) ρ u =
            chapter06UpperFixedSpaceCodim (S.upperProfile N)
              (ρ.comp (chapter06QuotientTransition h)) u :=
          (chapter06UpperFixedSpaceCodim_transition S h ρ u).symm
        _ = chapter06UpperFixedSpaceCodim (S.upperProfile N)
              (ρ.comp (chapter06QuotientTransition h)) w := by
          exact heq
        _ = chapter06UpperFixedSpaceCodim (S.upperProfile M) ρ w :=
          chapter06UpperFixedSpaceCodim_transition S h ρ w

/-!
The decomposition construction in Section 6.3 needs the finite chain of
fixed spaces before it chooses invariant complements.  This interface keeps
the three independent pieces of that argument visible: a break is exactly a
nontrivial fixed-space jump, the fixed spaces are locally constant between
successive breaks, and the sorted chain telescopes from wild-fixed vectors to
the whole representation.
-/
structure Chapter06RepresentationFixedSpaceChain
    {E : Type u} {G : Type v} {V : Type w}
    [Field E] [Group G] [Finite G] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V]
    (D : Chapter05RamificationFiltration G)
    (ρ : Representation E G V) where
  positiveBreaks : Finset ℝ
  positiveBreaks_spec :
    ∀ r, r ∈ positiveBreaks ↔
      0 < r ∧ chapter06RepresentationUpperBreak D ρ r
  fixed_space_jump_iff :
    ∀ {r : ℝ}, 0 < r →
      (chapter06RepresentationUpperBreak D ρ r ↔
        chapter06FixedSpace ρ (chapter05UpperRamificationGroup D r) ≠
          chapter06FixedSpace ρ (chapter05UpperRightLimit D r))
  fixed_space_monotone :
    Monotone (fun u : ℝ =>
      chapter06FixedSpace ρ (chapter05UpperRamificationGroup D u))
  locally_constant_off_breaks :
    ∀ {u w : ℝ}, 0 < u → u ≤ w →
      (∀ r ∈ positiveBreaks, ¬(u ≤ r ∧ r < w)) →
      chapter06FixedSpace ρ (chapter05UpperRamificationGroup D u) =
        chapter06FixedSpace ρ (chapter05UpperRamificationGroup D w)
  terminal_fixed_space :
    ∃ R : ℝ, ∀ u : ℝ, R < u →
      chapter06FixedSpace ρ (chapter05UpperRamificationGroup D u) = ⊤
  sorted_chain_telescopes :
    ∃ (n : ℕ) (chain : Fin (n + 1) → Submodule E V)
      (labels : Fin n → ℝ),
      chain 0 = chapter06FixedSpace ρ (chapter05UpperRightLimit D 0) ∧
      (∀ i : Fin n, chain i.succ =
        chapter06FixedSpace ρ (chapter05UpperRightLimit D (labels i))) ∧
      chain (Fin.last n) = ⊤ ∧
      StrictMono labels ∧
      (∀ i : Fin n, labels i ∈ positiveBreaks) ∧
      (∀ r, r ∈ positiveBreaks → ∃ i : Fin n, labels i = r) ∧
      Monotone chain ∧
      Module.finrank E V = Module.finrank E (chain 0) +
        ∑ i : Fin n,
          (Module.finrank E (chain i.succ) -
            Module.finrank E (chain i.castSucc))

theorem chapter06_representation_fixed_space_chain_exists
    {L : Type u} {G : Type v} {V : Type w}
    [Field L] [Group G] [Finite G] [AddCommGroup V] [Module L V]
    [FiniteDimensional L V]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D))
    (ρ : Representation L G V) :
    Nonempty (Chapter06RepresentationFixedSpaceChain D ρ) := by
  classical
  let U : ℝ → Subgroup G := chapter05UpperRamificationGroup D
  let F : ℝ → Submodule L V :=
    fun r => chapter06FixedSpace ρ (U r)
  let R : ℝ → Submodule L V :=
    fun r => chapter06FixedSpace ρ (chapter05UpperRightLimit D r)
  have hUanti : Antitone U := by
    simpa [U] using chapter05_upper_filtration_antitone D hbij
  have hFmono : Monotone F := by
    intro r s hrs
    exact chapter06FixedSpace.antitone ρ (hUanti hrs)
  have hright_mem : ∀ r : ℝ, ∃ w : ℝ, r < w ∧
      U w = chapter05UpperRightLimit D r := by
    intro r
    let A : Set (Subgroup G) := U '' Set.Ioi r
    have hA_nonempty : A.Nonempty := by
      refine ⟨U (r + 1), ?_⟩
      exact ⟨r + 1, by norm_num, rfl⟩
    have hA_supClosed : SupClosed A := by
      intro H hH K hK
      rcases hH with ⟨x, hx, rfl⟩
      rcases hK with ⟨y, hy, rfl⟩
      by_cases hxy : x ≤ y
      · rw [sup_eq_left.mpr (hUanti hxy)]
        exact ⟨x, hx, rfl⟩
      · have hyx : y ≤ x := le_of_not_ge hxy
        rw [sup_eq_right.mpr (hUanti hyx)]
        exact ⟨y, hy, rfl⟩
    have hmem : sSup A ∈ A :=
      hA_supClosed.sSup_mem_of_nonempty (Set.toFinite A) hA_nonempty
        (by intro x hx; exact hx)
    rcases hmem with ⟨w, hw, hUw⟩
    exact ⟨w, hw, by simpa [A, U, chapter05UpperRightLimit, chapter05RightLimit] using hUw⟩
  have hleft_mem : ∀ {r : ℝ}, 0 < r → ∃ u : ℝ, u < r ∧ U u = U r := by
    intro r hr
    let A : Set (Subgroup G) := U '' Set.Ioo (-1 : ℝ) r
    have hA_nonempty : A.Nonempty := by
      refine ⟨U (r / 2), ?_⟩
      exact ⟨r / 2, by constructor <;> linarith, rfl⟩
    have hA_infClosed : InfClosed A := by
      intro H hH K hK
      rcases hH with ⟨x, hx, rfl⟩
      rcases hK with ⟨y, hy, rfl⟩
      by_cases hxy : x ≤ y
      · rw [inf_eq_right.mpr (hUanti hxy)]
        exact ⟨y, hy, rfl⟩
      · have hyx : y ≤ x := le_of_not_ge hxy
        rw [inf_eq_left.mpr (hUanti hyx)]
        exact ⟨x, hx, rfl⟩
    have hmem : sInf A ∈ A :=
      hA_infClosed.sInf_mem_of_nonempty (Set.toFinite A) hA_nonempty
        (by intro x hx; exact hx)
    rcases hmem with ⟨u, hu, hUu⟩
    have hleft : U r = sInf A := by
      simpa [A, U, chapter05LeftContinuousOnPositive] using
        ((chapter05_upper_filtration_left_continuous_on_positive D hbij) r hr)
    exact ⟨u, hu.2, hUu.trans hleft.symm⟩
  have hright_upper : ∀ (r t : ℝ), r < t →
      U t ≤ chapter05UpperRightLimit D r := by
    intro r t hrt
    change U t ≤ sSup (U '' Set.Ioi r)
    exact le_sSup ⟨t, hrt, rfl⟩
  have hright_anti : Antitone (fun r : ℝ => chapter05UpperRightLimit D r) := by
    intro r s hrs
    change sSup (U '' Set.Ioi s) ≤ sSup (U '' Set.Ioi r)
    apply sSup_le
    intro H hH
    rcases hH with ⟨t, ht, rfl⟩
    exact le_sSup ⟨t, lt_of_le_of_lt hrs ht, rfl⟩
  have hRmono : Monotone R := by
    intro r s hrs
    exact chapter06FixedSpace.antitone ρ (hright_anti hrs)
  have hcodim_fixed_eq {r s : ℝ} (h : F r = F s) :
      chapter06UpperFixedSpaceCodim D ρ r =
        chapter06UpperFixedSpaceCodim D ρ s := by
    change Module.finrank L (V ⧸ F r) = Module.finrank L (V ⧸ F s)
    rw [h]
  have hfixed_eq_of_codim_eq {r s : ℝ} (hrs : r ≤ s)
      (hcodim : chapter06UpperFixedSpaceCodim D ρ r =
        chapter06UpperFixedSpaceCodim D ρ s) : F r = F s := by
    apply Submodule.eq_of_le_of_finrank_eq (hFmono hrs)
    change Module.finrank L (V ⧸ F r) = Module.finrank L (V ⧸ F s) at hcodim
    have hrank_r := Submodule.finrank_quotient_add_finrank (F r)
    have hrank_s := Submodule.finrank_quotient_add_finrank (F s)
    omega
  have hjump : ∀ {r : ℝ}, 0 < r →
      (chapter06RepresentationUpperBreak D ρ r ↔ F r ≠ R r) := by
    intro r hr
    constructor
    · intro hbreak
      rcases hbreak with ⟨_, hcases⟩
      rcases hcases with hzero | hpositive
      · exfalso
        linarith [hzero.1]
      · intro hEq
        obtain ⟨w₀, hw₀, hUw₀⟩ := hright_mem r
        obtain ⟨u₀, hu₀, hUu₀⟩ := hleft_mem hr
        let ε : ℝ := min (r - u₀) (w₀ - r)
        have hε : 0 < ε := by
          dsimp [ε]
          exact lt_min (sub_pos.mpr hu₀) (sub_pos.mpr hw₀)
        rcases hpositive.2 ε hε with
          ⟨u, w, hu_left, hu_right, hw_left, hw_right, hcodim⟩
        have hu₀u : u₀ ≤ u := by
          have hmin : ε ≤ r - u₀ := min_le_left _ _
          linarith
        have huw : U u = U r := by
          apply le_antisymm
          · calc
              U u ≤ U u₀ := hUanti hu₀u
              _ = U r := hUu₀
          · exact hUanti hu_right
        have hww₀ : w ≤ w₀ := by
          have hmin : ε ≤ w₀ - r := min_le_right _ _
          linarith
        have hww : U w = chapter05UpperRightLimit D r := by
          apply le_antisymm
          · exact (hright_upper r w hw_left)
          · calc
              chapter05UpperRightLimit D r = U w₀ := hUw₀.symm
              _ ≤ U w := hUanti hww₀
        apply hcodim
        have hFu : F u = F r := by
          dsimp [F]
          rw [huw]
        have hFw : F w = R r := by
          dsimp [F, R]
          rw [hww]
        exact hcodim_fixed_eq (hFu.trans (hEq.trans hFw.symm))
    · intro hne
      refine ⟨hr.le, Or.inr ⟨hr, ?_⟩⟩
      intro ε hε
      obtain ⟨w₀, hw₀, hUw₀⟩ := hright_mem r
      obtain ⟨u₀, hu₀, hUu₀⟩ := hleft_mem hr
      let u := max u₀ (r - ε / 2)
      let w := min w₀ (r + ε / 2)
      have hu_left : r - ε < u := by
        dsimp [u]
        exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
      have hu_right : u ≤ r := by
        dsimp [u]
        exact max_le hu₀.le (by linarith)
      have hw_left : r < w := by
        dsimp [w]
        exact lt_min hw₀ (by linarith)
      have hw_right : w < r + ε := by
        dsimp [w]
        exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
      have hcodim :
          chapter06UpperFixedSpaceCodim D ρ u ≠
            chapter06UpperFixedSpaceCodim D ρ w := by
        intro hcodim
        have hFu : F u = F r := by
          have hu₀u : u₀ ≤ u := by
            dsimp [u]
            exact le_max_left _ _
          have huw : U u = U r := by
            apply le_antisymm
            · calc
                U u ≤ U u₀ := hUanti hu₀u
                _ = U r := hUu₀
            · exact hUanti hu_right
          dsimp [F]
          rw [huw]
        have hFw : F w = R r := by
          have hww₀ : w ≤ w₀ := by
            dsimp [w]
            exact min_le_left _ _
          have hww : U w = chapter05UpperRightLimit D r := by
            apply le_antisymm
            · exact hright_upper r w hw_left
            · calc
                chapter05UpperRightLimit D r = U w₀ := hUw₀.symm
                _ ≤ U w := hUanti hww₀
          dsimp [F, R]
          rw [hww]
        have hFuw : F u = F w :=
          hfixed_eq_of_codim_eq (le_trans hu_right hw_left.le) hcodim
        apply hne
        exact hFu.symm.trans (hFuw.trans hFw)
      exact ⟨u, w, hu_left, hu_right, hw_left, hw_right, hcodim⟩
  let positiveBreaks : Finset ℝ :=
    (chapter06RepresentationUpperBreakSet_finite D hbij ρ).toFinset.filter
      (fun r => 0 < r)
  have hpositiveBreaks_spec : ∀ r, r ∈ positiveBreaks ↔
      0 < r ∧ chapter06RepresentationUpperBreak D ρ r := by
    intro r
    simp [positiveBreaks, chapter06RepresentationUpperBreakSet]
    exact and_comm
  have hlocal : ∀ {u w : ℝ}, 0 < u → u ≤ w →
      (∀ r ∈ positiveBreaks, ¬(u ≤ r ∧ r < w)) → F u = F w := by
    intro u w hu huw hno
    by_contra hne
    let S : Set ℝ := {x | u ≤ x ∧ x ≤ w ∧ F x = F u}
    have huS : u ∈ S := by exact ⟨le_rfl, huw, rfl⟩
    have hS_nonempty : S.Nonempty := ⟨u, huS⟩
    have hS_bdd : BddAbove S := ⟨w, by intro x hx; exact hx.2.1⟩
    let r : ℝ := sSup S
    have hu_r : u ≤ r := by
      exact le_csSup hS_bdd huS
    have hr_w : r ≤ w := by
      exact csSup_le hS_nonempty (by intro x hx; exact hx.2.1)
    obtain ⟨q, hq_w, hUq⟩ := hleft_mem (lt_of_lt_of_le hu huw)
    have hFq : F q = F w := by
      dsimp [F]
      rw [hUq]
    have hq_upper : ∀ x ∈ S, x ≤ q := by
      intro x hx
      by_contra hqx
      have hq_x : q ≤ x := le_of_not_ge hqx
      have hchain : F u ≤ F q := by simpa [hFq] using hFmono huw
      have hchain' : F q ≤ F x := hFmono hq_x
      have hq_eq : F q = F u := by
        apply le_antisymm
        · calc F q ≤ F x := hchain'
             _ = F u := hx.2.2
        · exact hchain
      exact hne (hFq.symm.trans hq_eq).symm
    have hr_q : r ≤ q := csSup_le hS_nonempty hq_upper
    have hr_lt_w : r < w := lt_of_le_of_lt hr_q hq_w
    have hr_mem : r ∈ S := by
      have hFr : F r = F u := by
        by_contra hFr
        obtain ⟨q', hq'_r, hUq'⟩ := hleft_mem (lt_of_lt_of_le hu hu_r)
        have hFq' : F q' = F r := by
          dsimp [F]
          rw [hUq']
        have hq'_upper : ∀ x ∈ S, x ≤ q' := by
          intro x hx
          by_contra hq'x
          have hq'_x : q' ≤ x := le_of_not_ge hq'x
          have hchain : F u ≤ F q' := by
            simpa [hFq'] using hFmono hu_r
          have hchain' : F q' ≤ F x := hFmono hq'_x
          have hq'_eq : F q' = F u := by
            apply le_antisymm
            · calc F q' ≤ F x := hchain'
                 _ = F u := hx.2.2
            · exact hchain
          exact hFr (hFq'.symm.trans hq'_eq)
        have : r ≤ q' := csSup_le hS_nonempty hq'_upper
        exact (not_lt_of_ge this) hq'_r
      exact ⟨hu_r, hr_w, hFr⟩
    have hnotbreak : ¬chapter06RepresentationUpperBreak D ρ r := by
      intro hbreak
      apply hno r
      · exact (hpositiveBreaks_spec r).2 ⟨lt_of_lt_of_le hu hu_r, hbreak⟩
      · exact ⟨hu_r, hr_lt_w⟩
    have hFrR : F r = R r := by
      by_contra hFrR
      exact hnotbreak ((hjump (lt_of_lt_of_le hu hu_r)).2 hFrR)
    obtain ⟨t, hrt, hUt⟩ := hright_mem r
    have hFt : F t = F u := by
      have hFtR : F t = R r := by
        dsimp [F, R]
        rw [hUt]
      exact hFtR.trans (hFrR ▸ hr_mem.2.2)
    by_cases htw : t ≤ w
    · have htS : t ∈ S := ⟨hu_r.trans (le_of_lt hrt), htw, hFt⟩
      have : t ≤ r := le_csSup hS_bdd htS
      exact (not_lt_of_ge this) hrt
    · have hwt : w < t := lt_of_not_ge htw
      have hFw : F w = F u := by
        apply le_antisymm
        · calc F w ≤ F t := hFmono hwt.le
             _ = F u := hFt
        · exact hFmono huw
      exact hne hFw.symm
  obtain ⟨B, hB⟩ := D.lower_eventually_trivial
  let b : ℕ := max B 1
  have hbtriv : D.lowerGroup (b : ℝ) = ⊥ := hB b (le_max_left _ _)
  have hbpos : 0 < b := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  have hb_dom : (-1 : ℝ) ≤ (b : ℝ) := by
    have hb_nonneg : (0 : ℝ) ≤ (b : ℝ) := by positivity
    linarith
  have hFbpos : 0 < chapter05HerbrandFunction D (b : ℝ) := by
    have hstrict :=
      (chapter05_herbrand_function_is_continuous_increasing_piecewise_linear D).2.1
    have h := hstrict (by norm_num : (0 : ℝ) ∈ Set.Ici (-1))
      hb_dom
      (by exact_mod_cast hbpos)
    simpa [chapter05_herbrand_function_zero D] using h
  have hterminal : ∃ R₀ : ℝ, ∀ u : ℝ, R₀ < u → F u = ⊤ := by
    refine ⟨chapter05HerbrandFunction D (b : ℝ), ?_⟩
    intro u hu
    have hu_pos : 0 < u := lt_of_lt_of_le hFbpos hu.le
    have hspec := chapter05_herbrand_inverse_spec D hbij u
    have hinv_dom : (-1 : ℝ) ≤ chapter05HerbrandInverse D u := by
      by_contra hnot
      have hinv_neg : chapter05HerbrandInverse D u < 0 := by linarith
      have hzero := chapter05_herbrand_function_of_nonpositive D hinv_neg.le
      linarith
    have hb_inv : (b : ℝ) < chapter05HerbrandInverse D u := by
      by_contra hnot
      have hle : chapter05HerbrandInverse D u ≤ (b : ℝ) := le_of_not_gt hnot
      have hFle : chapter05HerbrandFunction D
          (chapter05HerbrandInverse D u) ≤ chapter05HerbrandFunction D (b : ℝ) := by
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact ((chapter05_herbrand_function_is_continuous_increasing_piecewise_linear D).2.1
            hinv_dom hb_dom hlt).le
        · simp [heq]
      linarith
    have hUbot : chapter05UpperRamificationGroup D u = ⊥ := by
      rw [chapter05UpperRamificationGroup, if_pos (by linarith : (-1 : ℝ) ≤ u)]
      apply le_antisymm
      · rw [← hbtriv]
        exact D.lower_antitone hb_inv.le
      · exact bot_le
    change chapter06FixedSpace ρ (chapter05UpperRamificationGroup D u) = ⊤
    rw [hUbot]
    apply le_antisymm le_top
    intro v hv
    rw [chapter06FixedSpace.mem_iff]
    intro h
    have hh : (h : G) = 1 := Subgroup.mem_bot.mp h.property
    change ρ (h : G) v = v
    rw [hh, ρ.map_one]
    rfl
  let n : ℕ := positiveBreaks.card
  let labels : Fin n → ℝ :=
    positiveBreaks.orderEmbOfFin (by rfl)
  have hlabels_strict : StrictMono labels := by
    simpa [labels] using
      (positiveBreaks.orderEmbOfFin (by rfl)).strictMono
  have hlabels_mem : ∀ i : Fin n, labels i ∈ positiveBreaks := by
    intro i
    simp [labels]
  have hlabels_surj : ∀ r, r ∈ positiveBreaks → ∃ i : Fin n, labels i = r := by
    intro r hr
    have hrange : Set.range labels = (positiveBreaks : Set ℝ) := by
      simp [labels]
    have hrange_mem : r ∈ Set.range labels := by
      rw [hrange]
      exact hr
    exact hrange_mem
  let chain : Fin (n + 1) → Submodule L V :=
    Fin.cases (R 0) (fun i => R (labels i))
  have hchain_zero : chain 0 = R 0 := by
    simp [chain]
  have hchain_succ : ∀ i : Fin n, chain i.succ = R (labels i) := by
    intro i
    simp [chain]
  have hchain_mono : Monotone chain := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro hij
        exact le_rfl
      · intro hij
        simp [chain]
        exact hRmono ((hpositiveBreaks_spec (labels j)).mp (hlabels_mem j)).1.le
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro hij
        exfalso
        have hij' : (i.val + 1) ≤ 0 := Fin.le_iff_val_le_val.mp hij
        omega
      · intro hij
        simp [chain]
        apply hRmono
        apply hlabels_strict.monotone
        have hij' : (i.val + 1) ≤ (j.val + 1) :=
          Fin.le_iff_val_le_val.mp hij
        apply Fin.le_iff_val_le_val.mpr
        omega
  have hchain_last : chain (Fin.last n) = ⊤ := by
    obtain hlast0 | ⟨iLast, hiLast⟩ := (Fin.last n).eq_zero_or_eq_succ
    · have hn : n = 0 := by
        have hv := congrArg Fin.val hlast0
        simpa using hv
      have hempty : positiveBreaks = ∅ := by
        apply Finset.card_eq_zero.mp
        simpa [n] using hn
      obtain ⟨t, ht, hUt⟩ := hright_mem 0
      obtain ⟨R₀, hR₀⟩ := hterminal
      let W : ℝ := max (R₀ + 1) t
      have hRW : R₀ < W := by
        dsimp [W]
        exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
      have htW : t ≤ W := by
        dsimp [W]
        exact le_max_right _ _
      have hno : ∀ r ∈ positiveBreaks, ¬(t ≤ r ∧ r < W) := by
        intro r hr
        rw [hempty] at hr
        exact False.elim (by simp at hr)
      have htw : F t = F W := hlocal ht htW hno
      have hFt : F t = R 0 := by
        dsimp [F, R]
        rw [hUt]
      have htop : F W = ⊤ := hR₀ W hRW
      have hRtop : R 0 = ⊤ := hFt.symm.trans (htw.trans htop)
      rw [hlast0, hchain_zero]
      exact hRtop
    · let rLast : ℝ := labels iLast
      have hrLast : 0 < rLast := by
        exact (hpositiveBreaks_spec rLast).mp (hlabels_mem iLast) |>.1
      obtain ⟨t, ht, hUt⟩ := hright_mem rLast
      obtain ⟨R₀, hR₀⟩ := hterminal
      let W : ℝ := max (R₀ + 1) t
      have hRW : R₀ < W := by
        dsimp [W]
        exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
      have htW : t ≤ W := by
        dsimp [W]
        exact le_max_right _ _
      have hbreak_le : ∀ r, r ∈ positiveBreaks → r ≤ rLast := by
        intro r hr
        obtain ⟨j, hj⟩ := hlabels_surj r hr
        have hjsucc : j.succ ≤ Fin.last n := Fin.le_last _
        rw [hiLast] at hjsucc
        have hji' : j.val.succ ≤ iLast.val.succ :=
          Fin.le_iff_val_le_val.mp hjsucc
        have hji : j ≤ iLast := by
          apply Fin.le_iff_val_le_val.mpr
          exact Nat.succ_le_succ_iff.mp hji'
        have hlabel := hlabels_strict.monotone hji
        simpa [rLast, hj] using hlabel
      have hno : ∀ r ∈ positiveBreaks, ¬(t ≤ r ∧ r < W) := by
        intro r hr htr
        have hrlast := hbreak_le r hr
        linarith
      have htpos : 0 < t := lt_trans hrLast ht
      have htw : F t = F W := hlocal htpos htW hno
      have hFt : F t = R rLast := by
        dsimp [F, R]
        rw [hUt]
      have htop : F W = ⊤ := hR₀ W hRW
      have hRtop : R rLast = ⊤ := hFt.symm.trans (htw.trans htop)
      rw [hiLast, hchain_succ]
      exact hRtop
  have htelescopes : ∀ (m : ℕ) (c : Fin (m + 1) → Submodule L V),
      Monotone c →
      Module.finrank L (c (Fin.last m)) =
        Module.finrank L (c 0) +
          ∑ i : Fin m,
            (Module.finrank L (c i.succ) -
              Module.finrank L (c i.castSucc)) := by
    intro m
    induction m with
    | zero =>
        intro c hc
        simp
    | succ m ih =>
        intro c hc
        let c' : Fin (m + 1) → Submodule L V := fun i => c i.castSucc
        have hc' : Monotone c' := by
          intro i j hij
          exact hc (Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp hij))
        have hi := ih c' hc'
        have hle : Module.finrank L (c (Fin.last m).castSucc) ≤
            Module.finrank L (c (Fin.last m).succ) := by
          apply Submodule.finrank_mono
          have hfin : (Fin.last m).castSucc ≤ (Fin.last m).succ := by
            apply Fin.le_iff_val_le_val.mpr
            simp
          exact hc hfin
        rw [Fin.sum_univ_castSucc]
        dsimp [c'] at hi
        have hlast : (Fin.last (m + 1) : Fin (m + 1 + 1)) = (Fin.last m).succ := by
          apply Fin.ext
          simp
        rw [hlast]
        calc
          Module.finrank L (c (Fin.last m).succ) =
              Module.finrank L (c (Fin.last m).castSucc) +
                (Module.finrank L (c (Fin.last m).succ) -
                  Module.finrank L (c (Fin.last m).castSucc)) := by
            symm
            exact Nat.add_sub_of_le hle
          _ = (Module.finrank L (c 0) +
                ∑ i : Fin m,
                  (Module.finrank L (c i.castSucc.succ) -
                    Module.finrank L (c i.castSucc.castSucc))) +
                  (Module.finrank L (c (Fin.last m).succ) -
                  Module.finrank L (c (Fin.last m).castSucc)) := by
            simp only [hi]
            rfl
          _ = Module.finrank L (c 0) +
                (∑ i : Fin m,
                  (Module.finrank L (c i.castSucc.succ) -
                    Module.finrank L (c i.castSucc.castSucc)) +
                  (Module.finrank L (c (Fin.last m).succ) -
                    Module.finrank L (c (Fin.last m).castSucc))) := by
            simp [Nat.add_assoc]
  refine ⟨{
    positiveBreaks := positiveBreaks
    positiveBreaks_spec := hpositiveBreaks_spec
    fixed_space_jump_iff := by
      intro r hr
      exact hjump hr
    fixed_space_monotone := hFmono
    locally_constant_off_breaks := by
      intro u w hu huw hno
      exact hlocal hu huw hno
    terminal_fixed_space := hterminal
    sorted_chain_telescopes := by
      refine ⟨n, chain, labels, ?_, ?_, hchain_last, hlabels_strict,
        hlabels_mem, hlabels_surj, hchain_mono, ?_⟩
      · exact hchain_zero
      · exact hchain_succ
      · have htel := htelescopes n chain hchain_mono
        rw [hchain_last] at htel
        simpa using htel
  }⟩

/-!
The two conductor functionals used later are evaluated on the finite profile.
The integral is over positive upper depth; no infinite group sum is involved.
-/

def chapter06SwanConductor
    {E : Type u} {G : Type v} {V : Type w}
    [Field E] [Group G] [Finite G] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V]
    (D : Chapter05RamificationFiltration G)
    (ρ : Representation E G V) : ℝ :=
  ∫ v in Set.Ioi (0 : ℝ), chapter06UpperFixedSpaceCodimReal D ρ v

def chapter06ArtinConductor
    {E : Type u} {G : Type v} {V : Type w}
    [Field E] [Group G] [Finite G] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V]
    (D : Chapter05RamificationFiltration G)
    (ρ : Representation E G V) : ℝ :=
  chapter06UpperFixedSpaceCodimReal D ρ 0 + chapter06SwanConductor D ρ

def chapter06FiniteLevelUpperBreakSet
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P)
    {E : Type u} {V : Type w} [Field E] [AddCommGroup V]
    [Module E V] [FiniteDimensional E V]
    {ρ : Chapter06FiniteImageRepresentation E P V}
    (R : Chapter06FiniteLevelRepresentation ρ) : Set ℝ :=
  chapter06RepresentationUpperBreakSet (S.upperProfile R.level) R.action

def chapter06FiniteLevelSwanConductor
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P)
    {E : Type u} {V : Type w} [Field E] [AddCommGroup V]
    [Module E V] [FiniteDimensional E V]
    {ρ : Chapter06FiniteImageRepresentation E P V}
    (R : Chapter06FiniteLevelRepresentation ρ) : ℝ :=
  chapter06SwanConductor (S.upperProfile R.level) R.action

def chapter06FiniteLevelArtinConductor
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P)
    {E : Type u} {V : Type w} [Field E] [AddCommGroup V]
    [Module E V] [FiniteDimensional E V]
    {ρ : Chapter06FiniteImageRepresentation E P V}
    (R : Chapter06FiniteLevelRepresentation ρ) : ℝ :=
  chapter06ArtinConductor (S.upperProfile R.level) R.action

theorem chapter06SwanConductor_transition
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P)
    {N M : OpenNormalSubgroup P} (h : N ≤ M)
    {E : Type u} {V : Type w} [Field E] [AddCommGroup V]
    [Module E V] [FiniteDimensional E V]
    (ρ : Representation E (P ⧸ M.toSubgroup) V) :
    chapter06SwanConductor (S.upperProfile N)
        (ρ.comp (chapter06QuotientTransition h)) =
      chapter06SwanConductor (S.upperProfile M) ρ := by
  unfold chapter06SwanConductor
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun v => by
    change (chapter06UpperFixedSpaceCodim (S.upperProfile N)
        (ρ.comp (chapter06QuotientTransition h)) v : ℝ) =
      (chapter06UpperFixedSpaceCodim (S.upperProfile M) ρ v : ℝ)
    rw [chapter06UpperFixedSpaceCodim_transition S h ρ v])

theorem chapter06ArtinConductor_transition
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P)
    {N M : OpenNormalSubgroup P} (h : N ≤ M)
    {E : Type u} {V : Type w} [Field E] [AddCommGroup V]
    [Module E V] [FiniteDimensional E V]
    (ρ : Representation E (P ⧸ M.toSubgroup) V) :
    chapter06ArtinConductor (S.upperProfile N)
        (ρ.comp (chapter06QuotientTransition h)) =
      chapter06ArtinConductor (S.upperProfile M) ρ := by
  unfold chapter06ArtinConductor
  change (chapter06UpperFixedSpaceCodim (S.upperProfile N)
      (ρ.comp (chapter06QuotientTransition h)) 0 : ℝ) +
      chapter06SwanConductor (S.upperProfile N)
        (ρ.comp (chapter06QuotientTransition h)) =
    (chapter06UpperFixedSpaceCodim (S.upperProfile M) ρ 0 : ℝ) +
      chapter06SwanConductor (S.upperProfile M) ρ
  rw [chapter06UpperFixedSpaceCodim_transition S h ρ 0,
    chapter06SwanConductor_transition S h ρ]

end

end LastLib.Book03RamificationTheory.Chapter06
