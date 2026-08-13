import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Maschke

namespace LastLib.Book03RamificationTheory.Chapter10

noncomputable section

open MeasureTheory
open scoped BigOperators

universe u v w

/-!
The following interfaces expose the finite conductor-facing data needed by
Chapter 10: a finite lower filtration, its upper reindexing, and a separable
residue hypothesis.  They deliberately avoid importing the larger field and
profinite constructions used by earlier chapters.  The ambient group is the
omitted lower group `G₋₁`; the indexed `group 0` is inertia `G₀`, so it must
not be identified with `⊤` in a quotient that has a nontrivial unramified part.
The fields describe the usual ramification data rather than assuming any
conductor identity.
-/

/-- A finite lower-numbered ramification filtration of a finite Galois quotient. -/
structure LowerRamificationFiltration
    (G : Type u) [Group G] [Fintype G] where
  group : ℕ → Subgroup G
  antitone : Antitone group
  normal : ∀ i, (group i).Normal
  cutoff : ℕ
  trivial_after : ∀ i, cutoff ≤ i → group i = ⊥

namespace LowerRamificationFiltration

variable {G : Type u} [Group G] [Fintype G]

/- The lower index `-1` is the ambient Galois quotient and is therefore not
   stored in the `ℕ`-indexed positive/inertial part of the filtration. -/
def group_neg_one (_F : LowerRamificationFiltration G) : Subgroup G := ⊤

@[simp] theorem group_neg_one_eq_top (F : LowerRamificationFiltration G) :
    F.group_neg_one = ⊤ := rfl

theorem group_zero_normal (F : LowerRamificationFiltration G) :
    (F.group 0).Normal := F.normal 0

theorem group_eq_bot_of_ge (F : LowerRamificationFiltration G)
    {i : ℕ} (hi : F.cutoff ≤ i) : F.group i = ⊥ :=
  F.trivial_after i hi

@[ext] theorem ext {F F' : LowerRamificationFiltration G}
    (hgroup : F.group = F'.group) (hcutoff : F.cutoff = F'.cutoff) : F = F' := by
  cases F
  cases F'
  cases hgroup
  cases hcutoff
  rfl

/-- The lower-numbering weight of the `i`th interval. -/
def weight (F : LowerRamificationFiltration G) (i : ℕ) : ℚ :=
  by
    classical
    exact (Fintype.card (F.group i) : ℚ) / (Fintype.card (F.group 0) : ℚ)

@[simp] theorem weight_zero (F : LowerRamificationFiltration G) :
    F.weight 0 = 1 := by
  simp [weight]

theorem weight_nonnegative (F : LowerRamificationFiltration G) (i : ℕ) :
    0 ≤ F.weight i := by
  classical
  exact div_nonneg (Fintype.card (F.group i)).cast_nonneg
    (Fintype.card (F.group 0)).cast_nonneg

end LowerRamificationFiltration

/--
The upper reindexing attached to a lower filtration.  `depth i` is the upper
depth of the boundary after the lower group `i`; on each open/closed interval
the upper group is the corresponding lower group.  This is the book-facing
interface to the Herbrand function from the earlier chapters.
-/
structure UpperRamificationFiltration
    {G : Type u} [Group G] [Fintype G]
    (lower : LowerRamificationFiltration G) where
  group : ℝ → Subgroup G
  depth : ℕ → ℝ
  depth_zero : depth 0 = 0
  depth_monotone : Monotone depth
  depth_step : ∀ {i : ℕ}, i < lower.cutoff →
    depth (i + 1) - depth i = (lower.weight (i + 1) : ℝ)
  group_zero : group 0 = lower.group 0
  group_on_interval : ∀ {i : ℕ} {v : ℝ}, i < lower.cutoff →
    depth i < v → v ≤ depth (i + 1) → group v = lower.group (i + 1)
  group_antitone : Antitone group
  group_normal : ∀ v, (group v).Normal
  group_trivial_after : ∀ {v : ℝ}, depth lower.cutoff < v → group v = ⊥

namespace UpperRamificationFiltration

variable {G : Type u} [Group G] [Fintype G]
variable {lower : LowerRamificationFiltration G}

@[simp] theorem depth_zero_eq_zero (U : UpperRamificationFiltration lower) :
    U.depth 0 = 0 := U.depth_zero

@[simp] theorem group_zero_eq_lower_zero (U : UpperRamificationFiltration lower) :
    U.group 0 = lower.group 0 := U.group_zero

theorem group_eq_bot_of_gt (U : UpperRamificationFiltration lower)
    {v : ℝ} (hv : U.depth lower.cutoff < v) : U.group v = ⊥ :=
  U.group_trivial_after hv

@[ext] theorem ext {U U' : UpperRamificationFiltration lower}
    (hgroup : U.group = U'.group) (hdepth : U.depth = U'.depth) : U = U' := by
  cases U
  cases U'
  cases hgroup
  cases hdepth
  rfl

end UpperRamificationFiltration

/-- A finite ramification quotient together with the separable-residue condition. -/
structure RamificationFiltration
    (G : Type u) [Group G] [Fintype G] where
  lower : LowerRamificationFiltration G
  upper : UpperRamificationFiltration lower
  residue_separable : Prop

namespace RamificationFiltration

variable {G : Type u} [Group G] [Fintype G]

/-- The excluded fierce case is the failure of separability of the residue extension. -/
def IsFierce (F : RamificationFiltration G) : Prop := ¬ F.residue_separable

theorem not_isFierce (F : RamificationFiltration G)
    (hseparable : F.residue_separable) : ¬ F.IsFierce := by
  exact fun h => h hseparable

@[ext] theorem ext {F F' : RamificationFiltration G}
    (hlower : F.lower = F'.lower) (hupper : HEq F.upper F'.upper)
    (hseparable : F.residue_separable = F'.residue_separable) : F = F' := by
  cases F
  cases F'
  cases hlower
  cases hupper
  cases hseparable
  rfl

end RamificationFiltration

/-- A finite-dimensional representation whose image is finite. -/
structure FiniteImageRepresentation
    (E : Type u) (G : Type v) (V : Type w)
    [Field E] [Group G] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] where
  toRepresentation : Representation E G V
  finite_image : (Set.range toRepresentation).Finite

namespace FiniteImageRepresentation

variable {E : Type u} {G : Type v} {V : Type w}
variable [Field E] [Group G] [AddCommGroup V] [Module E V]
  [FiniteDimensional E V]

instance : CoeFun (FiniteImageRepresentation E G V)
    (fun _ => Representation E G V) :=
  ⟨FiniteImageRepresentation.toRepresentation⟩

@[simp] theorem coe_toRepresentation (ρ : FiniteImageRepresentation E G V) :
    (ρ : Representation E G V) = ρ.toRepresentation := rfl

theorem finite_image_range (ρ : FiniteImageRepresentation E G V) :
    (Set.range ρ.toRepresentation).Finite := ρ.finite_image

def ofFiniteGroup [Fintype G] (ρ : Representation E G V) :
    FiniteImageRepresentation E G V where
  toRepresentation := ρ
  finite_image := Set.finite_range ρ

@[ext] theorem ext {ρ σ : FiniteImageRepresentation E G V}
    (h : ρ.toRepresentation = σ.toRepresentation) : ρ = σ := by
  cases ρ
  cases σ
  cases h
  rfl

def restrict {H : Type*} [Group H]
    (ρ : FiniteImageRepresentation E G V) (φ : H →* G) :
    FiniteImageRepresentation E H V where
  toRepresentation := ρ.toRepresentation.comp φ
  finite_image := ρ.finite_image.subset (Set.range_comp_subset_range φ ρ.toRepresentation)

@[simp] theorem restrict_toRepresentation {H : Type*} [Group H]
    (ρ : FiniteImageRepresentation E G V) (φ : H →* G) :
    (ρ.restrict φ).toRepresentation = ρ.toRepresentation.comp φ := rfl

end FiniteImageRepresentation

/--
A finite quotient through which a finite-image representation factors.  The
`RamificationFiltration` field is the local dependency guess for the finite
Galois quotient and is deliberately kept separate from the representation.
-/
structure FiniteQuotientRealization
    {E : Type u} {G : Type v} {V : Type w}
    [Field E] [Group G] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V]
    (ρ : FiniteImageRepresentation E G V)
    (Q : Type*) [Group Q] [Fintype Q] where
  /-- A quotient is onto; unused points of `Q` would change the filtration data. -/
  quotient : G →* Q
  quotient_surjective : Function.Surjective quotient
  action : Representation E Q V
  factorization : ρ.toRepresentation = action.comp quotient
  ramification : RamificationFiltration Q

namespace FiniteQuotientRealization

variable {E : Type u} {G : Type v} {V : Type w}
variable [Field E] [Group G] [AddCommGroup V] [Module E V]
  [FiniteDimensional E V]
variable (ρ : FiniteImageRepresentation E G V)
variable {Q : Type*} [Group Q] [Fintype Q]

theorem kernel_acts_trivially (R : FiniteQuotientRealization ρ Q) :
    ∀ g : G, g ∈ R.quotient.ker → ρ.toRepresentation g = LinearMap.id := by
  intro g hg
  rw [R.factorization]
  have hgq : R.quotient g = 1 := hg
  change R.action (R.quotient g) = LinearMap.id
  rw [hgq]
  exact R.action.map_one

theorem factorization_apply (R : FiniteQuotientRealization ρ Q) (g : G) :
    ρ.toRepresentation g = R.action (R.quotient g) := by
  simpa using congrArg (fun f : Representation E G V => f g) R.factorization

@[ext] theorem ext {R S : FiniteQuotientRealization ρ Q}
    (hquotient : R.quotient = S.quotient) (haction : R.action = S.action)
    (hramification : R.ramification = S.ramification) : R = S := by
  cases R
  cases S
  cases hquotient
  cases haction
  cases hramification
  rfl

end FiniteQuotientRealization

/-- The canonical fixed subspace `V^H` of a representation. -/
def fixedSpace
    {E : Type u} {G : Type v} {V : Type w}
    [Field E] [Group G] [AddCommGroup V] [Module E V]
    (ρ : Representation E G V) (H : Subgroup G) : Submodule E V :=
  Representation.invariants (ρ.comp H.subtype)

namespace fixedSpace

variable {E : Type u} {G : Type v} {V : Type w}
variable [Field E] [Group G] [AddCommGroup V] [Module E V]

theorem mem_iff (ρ : Representation E G V) (H : Subgroup G) (v : V) :
    v ∈ fixedSpace ρ H ↔ ∀ h : H, ρ h v = v := by
  simp [fixedSpace]

theorem antitone {H K : Subgroup G} (ρ : Representation E G V)
    (hHK : H ≤ K) : fixedSpace ρ K ≤ fixedSpace ρ H := by
  intro v hv
  rw [mem_iff] at hv ⊢
  intro h
  simpa using hv ⟨h, hHK h.property⟩

theorem top_of_trivial_on (ρ : Representation E G V) (H : Subgroup G)
    (h : ∀ g : H, ρ g = LinearMap.id) : fixedSpace ρ H = ⊤ := by
  apply top_unique
  intro v hv
  rw [mem_iff]
  intro g
  simp [h g]

theorem comp_eq_map {H : Type*} [Group H]
    (ρ : Representation E G V) (φ : H →* G) (S : Subgroup H) :
    fixedSpace (ρ.comp φ) S = fixedSpace ρ (S.map φ) := by
  ext v
  constructor
  · intro hv
    rw [mem_iff] at hv ⊢
    intro y
    rcases (Subgroup.mem_map.mp y.property) with ⟨x, hx, hxy⟩
    have hx' := hv ⟨x, hx⟩
    simpa [hxy] using hx'
  · intro hv
    rw [mem_iff] at hv ⊢
    intro x
    exact hv ⟨φ x, Subgroup.mem_map_of_mem φ x.property⟩

end fixedSpace

/-- Codimension of the fixed subspace, implemented by the canonical quotient. -/
def fixedSpaceCodim
    {E : Type u} {G : Type v} {V : Type w}
    [Field E] [Group G] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V]
    (ρ : Representation E G V) (H : Subgroup G) : ℕ :=
  Module.finrank E (V ⧸ fixedSpace ρ H)

def fixedSpaceCodimRat
    {E : Type u} {G : Type v} {V : Type w}
    [Field E] [Group G] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V]
    (ρ : Representation E G V) (H : Subgroup G) : ℚ :=
  (fixedSpaceCodim ρ H : ℚ)

def fixedSpaceCodimReal
    {E : Type u} {G : Type v} {V : Type w}
    [Field E] [Group G] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V]
    (ρ : Representation E G V) (H : Subgroup G) : ℝ :=
  (fixedSpaceCodim ρ H : ℝ)

namespace fixedSpaceCodim

variable {E : Type u} {G : Type v} {V : Type w}
variable [Field E] [Group G] [AddCommGroup V] [Module E V]
  [FiniteDimensional E V]

theorem eq_zero_iff (ρ : Representation E G V) (H : Subgroup G) :
    fixedSpaceCodim ρ H = 0 ↔ fixedSpace ρ H = ⊤ := by
  rw [fixedSpaceCodim, Submodule.finrank_quotient]
  constructor
  · intro h
    apply Submodule.eq_top_iff_finrank_eq.mpr
    exact Nat.le_antisymm (Submodule.finrank_le _) (Nat.sub_eq_zero_iff_le.mp h)
  · intro h
    rw [h, finrank_top, Nat.sub_self]

theorem antitone {H K : Subgroup G} (ρ : Representation E G V)
    (hHK : H ≤ K) : fixedSpaceCodim ρ H ≤ fixedSpaceCodim ρ K := by
  change Module.finrank E (V ⧸ fixedSpace ρ H) ≤
    Module.finrank E (V ⧸ fixedSpace ρ K)
  rw [Submodule.finrank_quotient, Submodule.finrank_quotient]
  exact Nat.sub_le_sub_left (Submodule.finrank_mono (fixedSpace.antitone ρ hHK)) _

theorem congr {ρ σ : Representation E G V} (hρ : ρ = σ) (H : Subgroup G) :
    fixedSpaceCodim ρ H = fixedSpaceCodim σ H := by
  cases hρ
  rfl

end fixedSpaceCodim

@[simp] theorem fixedSpaceCodimRat_eq_zero_iff
    {E : Type u} {G : Type v} {V : Type w}
    [Field E] [Group G] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V]
    (ρ : Representation E G V) (H : Subgroup G) :
    fixedSpaceCodimRat ρ H = 0 ↔ fixedSpace ρ H = ⊤ := by
  simpa [fixedSpaceCodimRat] using fixedSpaceCodim.eq_zero_iff ρ H

theorem fixedSpaceCodimRat_nonnegative
    {E : Type u} {G : Type v} {V : Type w}
    [Field E] [Group G] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V]
    (ρ : Representation E G V) (H : Subgroup G) :
    0 ≤ fixedSpaceCodimRat ρ H := by
  exact (fixedSpaceCodim ρ H).cast_nonneg

@[simp] theorem fixedSpaceCodimReal_eq_zero_iff
    {E : Type u} {G : Type v} {V : Type w}
    [Field E] [Group G] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V]
    (ρ : Representation E G V) (H : Subgroup G) :
    fixedSpaceCodimReal ρ H = 0 ↔ fixedSpace ρ H = ⊤ := by
  simpa [fixedSpaceCodimReal] using fixedSpaceCodim.eq_zero_iff ρ H

theorem fixedSpaceCodimReal_nonnegative
    {E : Type u} {G : Type v} {V : Type w}
    [Field E] [Group G] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V]
    (ρ : Representation E G V) (H : Subgroup G) :
    0 ≤ fixedSpaceCodimReal ρ H := by
  exact (fixedSpaceCodim ρ H).cast_nonneg

/- The ambient type `G` represents `G₋₁`; these aliases therefore expose the
   inertial groups used in the conductor formulas rather than the full
   quotient group. -/
def inertiaGroup {G : Type u} [Group G] [Fintype G]
    (F : RamificationFiltration G) : Subgroup G := F.lower.group 0

def wildRamificationGroup {G : Type u} [Group G] [Fintype G]
    (F : RamificationFiltration G) : Subgroup G := F.lower.group 1

@[simp] theorem inertiaGroup_eq_lower_zero
    {G : Type u} [Group G] [Fintype G] (F : RamificationFiltration G) :
    inertiaGroup F = F.lower.group 0 := rfl

/-- The fixed-space codimension as a function of upper depth. -/
def upperFixedSpaceFunction
    {E : Type u} {G : Type v} {V : Type w}
    [Field E] [Group G] [Fintype G] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V]
    (F : RamificationFiltration G) (ρ : Representation E G V) : ℝ → ℝ :=
  fun v => fixedSpaceCodimReal ρ (F.upper.group v)

/-- The upper-depth area on `[0, ∞)`, written as a set integral in `ℝ`. -/
def upperDepthArea
    {E : Type u} {G : Type v} {V : Type w}
    [Field E] [Group G] [Fintype G] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V]
  (F : RamificationFiltration G) (ρ : Representation E G V) : ℝ :=
  ∫ v in Set.Ici (0 : ℝ), upperFixedSpaceFunction F ρ v

/-!
The piecewise upper filtration is measurable and has bounded support on the
nonnegative half-line.  This is the analytic support interface used by the
Swan-as-area theorem; it is kept here because the representation type is not
part of the filtration data itself.
-/
theorem upperFixedSpaceFunction_integrable_restrict
    {E : Type u} {G : Type v} {V : Type w}
    [Field E] [Group G] [Fintype G] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V]
    (F : RamificationFiltration G) (ρ : Representation E G V) :
    Integrable (upperFixedSpaceFunction F ρ)
      (volume.restrict (Set.Ici (0 : ℝ))) := by
  have hanti : Antitone (upperFixedSpaceFunction F ρ) := by
    intro v w hvw
    unfold upperFixedSpaceFunction
    change (fixedSpaceCodim ρ (F.upper.group w) : ℝ) ≤
      (fixedSpaceCodim ρ (F.upper.group v) : ℝ)
    exact_mod_cast fixedSpaceCodim.antitone ρ (F.upper.group_antitone hvw)
  have hfixed_bot : fixedSpace ρ (⊥ : Subgroup G) = ⊤ := by
    apply fixedSpace.top_of_trivial_on
    intro g
    have hg : (g : G) = 1 := by
      exact congrArg Subtype.val (Subsingleton.elim g (1 : (⊥ : Subgroup G)))
    rw [hg]
    simpa only [Module.End.one_eq_id] using ρ.map_one
  let B : ℝ := F.upper.depth F.lower.cutoff
  have hB : 0 ≤ B := by
    dsimp [B]
    rw [← F.upper.depth_zero]
    exact F.upper.depth_monotone (Nat.zero_le _)
  have hzero : ∀ {v : ℝ}, B < v → upperFixedSpaceFunction F ρ v = 0 := by
    intro v hv
    rw [upperFixedSpaceFunction, F.upper.group_eq_bot_of_gt hv]
    exact (fixedSpaceCodimReal_eq_zero_iff ρ (⊥ : Subgroup G)).2 hfixed_bot
  have hbound : ∀ v : ℝ,
      ‖upperFixedSpaceFunction F ρ v‖ ≤ (Module.finrank E V : ℝ) := by
    intro v
    change |fixedSpaceCodimReal ρ (F.upper.group v)| ≤ (Module.finrank E V : ℝ)
    rw [abs_of_nonneg (fixedSpaceCodimReal_nonnegative ρ (F.upper.group v))]
    change (fixedSpaceCodim ρ (F.upper.group v) : ℝ) ≤
      (Module.finrank E V : ℝ)
    exact_mod_cast Submodule.finrank_quotient_le (fixedSpace ρ (F.upper.group v))
  have h_on : IntegrableOn (upperFixedSpaceFunction F ρ) (Set.Icc 0 B)
      (volume.restrict (Set.Ici (0 : ℝ))) := by
    refine IntegrableOn.of_bound (μ := volume.restrict (Set.Ici (0 : ℝ)))
      (s := Set.Icc 0 B) ?_ ?_ (Module.finrank E V : ℝ) ?_
    · rw [Measure.restrict_apply measurableSet_Icc]
      exact (measure_mono Set.inter_subset_left).trans_lt measure_Icc_lt_top
    · exact hanti.measurable.aestronglyMeasurable
    · exact Filter.Eventually.of_forall hbound
  apply h_on.integrable_of_ae_notMem_eq_zero
  filter_upwards [ae_restrict_mem measurableSet_Ici] with v hv hnot
  by_cases hvB : v ≤ B
  · exact False.elim (hnot ⟨hv, hvB⟩)
  · exact hzero (lt_of_not_ge hvB)

theorem upperDepthArea_congr_ae
    {f g : ℝ → ℝ}
    (hfg : f =ᵐ[volume.restrict (Set.Ici (0 : ℝ))] g) :
    (∫ v in Set.Ici (0 : ℝ), f v) = ∫ v in Set.Ici (0 : ℝ), g v := by
  exact integral_congr_ae hfg

/-- A quotient map to which Herbrand's upper-numbering quotient theorem applies. -/
structure HerbrandQuotientData
    {Gbig : Type u} {Gsmall : Type v}
    [Group Gbig] [Fintype Gbig] [Group Gsmall] [Fintype Gsmall]
    (Fbig : RamificationFiltration Gbig)
    (Fsmall : RamificationFiltration Gsmall) where
  projection : Gbig →* Gsmall
  surjective : Function.Surjective projection
  upper_map : ∀ v : ℝ,
    (Fbig.upper.group v).map projection = Fsmall.upper.group v

namespace HerbrandQuotientData

variable {Gbig : Type u} {Gsmall : Type v}
variable [Group Gbig] [Fintype Gbig] [Group Gsmall] [Fintype Gsmall]
variable {Fbig : RamificationFiltration Gbig} {Fsmall : RamificationFiltration Gsmall}

theorem upper_map_eq (C : HerbrandQuotientData Fbig Fsmall) (v : ℝ) :
    (Fbig.upper.group v).map C.projection = Fsmall.upper.group v :=
  C.upper_map v

end HerbrandQuotientData

end
end LastLib.Book03RamificationTheory.Chapter10
