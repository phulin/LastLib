import LastLib.Book03RamificationTheory.Chapter06.Dependencies
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.RepresentationTheory.Invariants

namespace LastLib.Book03RamificationTheory.Chapter06

noncomputable section

open LastLib.Book03RamificationTheory.Chapter05

open MeasureTheory

universe u v w

/-! ## 6.2. Finite-image representations need only finite levels -/

/- SOURCE_ISSUE (6.2): the source says that finite image implies an open
kernel.  For a profinite group this also uses continuity of the representation;
finite image alone is not enough for an arbitrary abstract representation.
The smallest principled correction is to record openness of the kernel as the
continuity input in the representation interface below. -/

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
