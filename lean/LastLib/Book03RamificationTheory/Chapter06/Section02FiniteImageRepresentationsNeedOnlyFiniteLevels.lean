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
    sorry
  kernel_open := by
    sorry

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
  sorry

namespace Chapter06FiniteLevelRepresentation

variable {E : Type u} {P : ProfiniteGrp} {V : Type w}
variable [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]

theorem factorization_apply
    {ρ : Chapter06FiniteImageRepresentation E P V}
    (R : Chapter06FiniteLevelRepresentation ρ) (g : P) :
    ρ.toRepresentation g = R.action (chapter06QuotientMap R.level g) := by
  sorry

theorem kernel_acts_trivially
    {ρ : Chapter06FiniteImageRepresentation E P V}
    (R : Chapter06FiniteLevelRepresentation ρ) :
    ∀ g : P, g ∈ (chapter06QuotientMap R.level).ker →
      ρ.toRepresentation g = LinearMap.id := by
  sorry

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
  sorry

theorem antitone {H K : Subgroup G} (ρ : Representation E G V)
    (hHK : H ≤ K) :
    chapter06FixedSpace ρ K ≤ chapter06FixedSpace ρ H := by
  sorry

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
  sorry

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
  sorry

theorem chapter06RepresentationUpperBreakSet_transition
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P)
    {N M : OpenNormalSubgroup P} (h : N ≤ M)
    {E : Type u} {V : Type w} [Field E] [AddCommGroup V]
    [Module E V] [FiniteDimensional E V]
    (ρ : Representation E (P ⧸ M.toSubgroup) V) :
    chapter06RepresentationUpperBreakSet (S.upperProfile N)
        (ρ.comp (chapter06QuotientTransition h)) =
      chapter06RepresentationUpperBreakSet (S.upperProfile M) ρ := by
  sorry

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
  sorry

theorem chapter06ArtinConductor_transition
    {P : ProfiniteGrp} (S : Chapter06InfiniteUpperSystem P)
    {N M : OpenNormalSubgroup P} (h : N ≤ M)
    {E : Type u} {V : Type w} [Field E] [AddCommGroup V]
    [Module E V] [FiniteDimensional E V]
    (ρ : Representation E (P ⧸ M.toSubgroup) V) :
    chapter06ArtinConductor (S.upperProfile N)
        (ρ.comp (chapter06QuotientTransition h)) =
      chapter06ArtinConductor (S.upperProfile M) ρ := by
  sorry

end

end LastLib.Book03RamificationTheory.Chapter06
