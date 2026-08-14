import LastLib.Book03RamificationTheory.Chapter06.Section02FiniteImageRepresentationsNeedOnlyFiniteLevels
import LastLib.Book03RamificationTheory.Chapter05.Section06HasseArfAndTheLimitsOfIntegrality
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.RepresentationTheory.Maschke

namespace LastLib.Book03RamificationTheory.Chapter06

noncomputable section

open LastLib.Book03RamificationTheory.Chapter05

open scoped BigOperators

universe u v w

/-! ## 6.3. Finite upper-break decompositions -/

/-!
The finite quotient is the group on which Maschke's theorem is applied.  The
coefficient field may be chosen after a scalar extension; the decomposition
record below is formulated over the resulting coefficient field itself.
-/

theorem chapter06_finite_group_representation_is_semisimple
    {L : Type u} {G : Type v} {V : Type w}
    [Field L] [CharZero L] [Group G] [Fintype G]
    [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (ρ : Representation L G V) :
    Representation.IsSemisimpleRepresentation ρ := by
  infer_instance

theorem chapter06_finite_image_level_action_is_semisimple
    {E : Type u} {P : ProfiniteGrp} {V : Type w}
    [Field E] [CharZero E] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V]
    {ρ : Chapter06FiniteImageRepresentation E P V}
    (R : Chapter06FiniteLevelRepresentation ρ) :
    Representation.IsSemisimpleRepresentation R.action := by
  let _ : Fintype (P ⧸ R.level.toSubgroup) := Fintype.ofFinite _
  infer_instance

def chapter06SubmoduleInvariant
    {L : Type u} {G : Type v} {V : Type w}
    [Field L] [Group G] [AddCommGroup V] [Module L V]
    (ρ : Representation L G V) (W : Submodule L V) : Prop :=
  ∀ g : G, ∀ x : V, x ∈ W → ρ g x ∈ W

def chapter06SubgroupActsTriviallyOn
    {L : Type u} {G : Type v} {V : Type w}
    [Field L] [Group G] [AddCommGroup V] [Module L V]
    (ρ : Representation L G V) (H : Subgroup G)
    (W : Submodule L V) : Prop :=
  ∀ g : H, ∀ x : V, x ∈ W → ρ (g : G) x = x

theorem chapter06_invariant_complement_exists
    {L : Type u} {G : Type v} {V : Type w}
    [Field L] [CharZero L] [Group G] [Fintype G]
    [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (ρ : Representation L G V) (W : Submodule L V)
    (hW : chapter06SubmoduleInvariant ρ W) :
    ∃ C : Submodule L V,
      chapter06SubmoduleInvariant ρ C ∧
        W ⊓ C = ⊥ ∧ W ⊔ C = ⊤ := by
  let _ : Representation.IsSemisimpleRepresentation ρ :=
    chapter06_finite_group_representation_is_semisimple ρ
  have hle : ∀ g : G, W ≤ W.comap (ρ g) := by
    intro g x hx
    exact hW g x hx
  let σ : Subrepresentation ρ :=
    { toSubmodule := W
      apply_mem_toSubmodule := by
        intro g x hx
        exact hle g hx }
  obtain ⟨τ, hτ⟩ := exists_isCompl σ
  refine ⟨τ.toSubmodule, ?_, ?_, ?_⟩
  · intro g x hx
    exact τ.apply_mem_toSubmodule g hx
  · simpa [σ] using congrArg Subrepresentation.toSubmodule hτ.inf_eq_bot
  · simpa [σ] using congrArg Subrepresentation.toSubmodule hτ.codisjoint.eq_top

theorem chapter06_fixedSpace_invariant_of_normal
    {L : Type u} {G : Type v} {V : Type w}
    [Field L] [Group G] [AddCommGroup V] [Module L V]
    (ρ : Representation L G V) (H : Subgroup G) [H.Normal] :
    chapter06SubmoduleInvariant ρ (chapter06FixedSpace ρ H) := by
  exact fun g x hx => (Representation.le_comap_invariants ρ H g) hx

theorem chapter06_upper_fixedSpace_invariant
    {L : Type u} {G : Type v} {V : Type w}
    [Field L] [Group G] [Finite G] [AddCommGroup V] [Module L V]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D))
    (ρ : Representation L G V) (u : ℝ) :
    chapter06SubmoduleInvariant ρ
      (chapter06FixedSpace ρ (chapter05UpperRamificationGroup D u)) := by
  let _ : (chapter05UpperRamificationGroup D u).Normal :=
    chapter05_upper_group_normal D hbij u
  unfold chapter06SubmoduleInvariant
  intro g x hx
  change x ∈ Representation.invariants
      (ρ.comp (chapter05UpperRamificationGroup D u)) at hx
  change ρ g x ∈ Representation.invariants
      (ρ.comp (chapter05UpperRamificationGroup D u))
  have hle := Representation.le_comap_invariants ρ
      (chapter05UpperRamificationGroup D u) g
  exact hle hx

theorem chapter06_upper_fixedSpace_chain
    {L : Type u} {G : Type v} {V : Type w}
    [Field L] [Group G] [Finite G] [AddCommGroup V] [Module L V]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D))
    (ρ : Representation L G V) {u w : ℝ} (huw : u ≤ w) :
    chapter06FixedSpace ρ (chapter05UpperRamificationGroup D u) ≤
      chapter06FixedSpace ρ (chapter05UpperRamificationGroup D w) := by
  exact chapter06FixedSpace.antitone ρ
    ((chapter05_upper_filtration_antitone D hbij) huw)

/-!
This record is the finite, source-order version of
`V = ⨁ V(r)`.  Its fields state the normality/stability, wild-inertia piece,
positive-break conditions, and finite support needed by the conductor formula.
-/

structure Chapter06UpperBreakDecomposition
    {L : Type u} {G : Type v} {V : Type w}
    [Field L] [Group G] [Finite G] [AddCommGroup V] [Module L V]
    [FiniteDimensional L V]
    (D : Chapter05RamificationFiltration G)
    (ρ : Representation L G V) where
  breaks : Finset ℝ
  piece : ℝ → Submodule L V
  breaks_nonnegative : ∀ r ∈ breaks, 0 ≤ r
  breaks_characterization :
    ∀ r, r ∈ breaks ↔ chapter06RepresentationUpperBreak D ρ r
  piece_nonzero_iff_mem : ∀ r, piece r ≠ ⊥ ↔ r ∈ breaks
  pieces_internal : DirectSum.IsInternal piece
  pieces_invariant : ∀ r, chapter06SubmoduleInvariant ρ (piece r)
  zero_piece_eq_wild_fixed :
    piece 0 = chapter06FixedSpace ρ (chapter05UpperRightLimit D 0)
  positive_piece_right_limit_fixed :
    ∀ {r : ℝ}, r ∈ breaks → 0 < r →
      chapter06SubgroupActsTriviallyOn ρ
        (chapter05UpperRightLimit D r) (piece r)
  positive_piece_upper_fixed_bottom :
    ∀ {r : ℝ}, r ∈ breaks → 0 < r →
      piece r ⊓ chapter06FixedSpace ρ
        (chapter05UpperRamificationGroup D r) = ⊥
  positive_piece_action_threshold :
    ∀ {r : ℝ}, r ∈ breaks → 0 < r → ∀ u : ℝ,
      chapter06SubgroupActsTriviallyOn ρ
        (chapter05UpperRamificationGroup D u) (piece r) ↔ r < u

namespace Chapter06UpperBreakDecomposition

variable {L : Type u} {G : Type v} {V : Type w}
variable [Field L] [Group G] [Finite G] [AddCommGroup V] [Module L V]
  [FiniteDimensional L V]
variable {D : Chapter05RamificationFiltration G}
variable {ρ : Representation L G V}

@[ext]
theorem ext
    {B C : Chapter06UpperBreakDecomposition D ρ}
    (hbreaks : B.breaks = C.breaks) (hpiece : B.piece = C.piece) : B = C := by
  cases B
  cases C
  cases hbreaks
  cases hpiece
  rfl

def positiveBreaks (B : Chapter06UpperBreakDecomposition D ρ) : Finset ℝ := by
  classical
  exact B.breaks.filter (fun r => 0 < r)

@[simp]
theorem mem_positiveBreaks (B : Chapter06UpperBreakDecomposition D ρ)
    {r : ℝ} : r ∈ B.positiveBreaks ↔ r ∈ B.breaks ∧ 0 < r := by
  classical
  simp [positiveBreaks]

theorem piece_eq_bot_of_not_mem
    (B : Chapter06UpperBreakDecomposition D ρ) {r : ℝ}
    (hr : r ∉ B.breaks) : B.piece r = ⊥ := by
  by_contra hne
  exact hr ((B.piece_nonzero_iff_mem r).mp hne)

end Chapter06UpperBreakDecomposition

theorem chapter06_upper_break_decomposition_exists
    {L : Type u} {G : Type v} {V : Type w}
    [Field L] [CharZero L] [Group G] [Fintype G]
    [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D))
    (ρ : Representation L G V) :
    Nonempty (Chapter06UpperBreakDecomposition D ρ) := by
  sorry

/-!
The fixed-space contribution of one positive-break piece is the step
function described in the source.  The total fixed-space codimension is the
sum of these contributions because the pieces form an internal direct sum.
-/

def chapter06PieceFixedSpaceCodim
    {L : Type u} {G : Type v} {V : Type w}
    [Field L] [Group G] [AddCommGroup V] [Module L V]
    [FiniteDimensional L V]
    (ρ : Representation L G V) (W : Submodule L V)
    (H : Subgroup G) : ℕ :=
  Module.finrank L W -
    Module.finrank L (W ⊓ chapter06FixedSpace ρ H : Submodule L V)

theorem chapter06_piece_fixedSpaceCodim_step
    {L : Type u} {G : Type v} {V : Type w}
    [Field L] [Group G] [Finite G] [AddCommGroup V] [Module L V]
    [FiniteDimensional L V]
    {D : Chapter05RamificationFiltration G}
    {ρ : Representation L G V}
    (B : Chapter06UpperBreakDecomposition D ρ)
    {r : ℝ} (hr : r ∈ B.breaks) (hr_pos : 0 < r) (u : ℝ) :
    chapter06PieceFixedSpaceCodim ρ (B.piece r)
        (chapter05UpperRamificationGroup D u) =
      if u ≤ r then Module.finrank L (B.piece r) else 0 := by
  by_cases hur : u ≤ r
  · have hchain :=
      chapter06_upper_fixedSpace_chain D
        (chapter05_herbrand_bijective_of_filtration D) ρ hur
    have hinter :
        B.piece r ⊓ chapter06FixedSpace ρ
            (chapter05UpperRamificationGroup D u) = ⊥ := by
      apply le_antisymm
      · exact le_trans (inf_le_inf_left _ hchain)
          (B.positive_piece_upper_fixed_bottom hr hr_pos).le
      · exact bot_le
    rw [if_pos hur, chapter06PieceFixedSpaceCodim, hinter]
    simp
  · have hru : r < u := lt_of_not_ge hur
    have htriv :=
      (B.positive_piece_action_threshold hr hr_pos u).mpr hru
    have hle :
        B.piece r ≤ chapter06FixedSpace ρ
            (chapter05UpperRamificationGroup D u) := by
      intro x hx
      rw [chapter06FixedSpace.mem_iff]
      intro g
      exact htriv g x hx
    rw [if_neg hur, chapter06PieceFixedSpaceCodim, inf_eq_left.mpr hle]
    simp

theorem chapter06_upper_fixedSpaceCodim_decomposition
    {L : Type u} {G : Type v} {V : Type w}
    [Field L] [Group G] [Finite G] [AddCommGroup V] [Module L V]
    [FiniteDimensional L V]
    {D : Chapter05RamificationFiltration G}
    {ρ : Representation L G V}
    (B : Chapter06UpperBreakDecomposition D ρ) (u : ℝ) :
    chapter06UpperFixedSpaceCodim D ρ u =
      ∑ r ∈ B.breaks,
        chapter06PieceFixedSpaceCodim ρ (B.piece r)
          (chapter05UpperRamificationGroup D u) := by
  classical
  let P : B.breaks → Submodule L V := fun r => B.piece r
  have hP_indep : iSupIndep P := by
    change iSupIndep (B.piece ∘ (fun r : B.breaks => (r : ℝ)))
    simpa only [Function.comp_apply] using
      B.pieces_internal.submodule_iSupIndep.comp Subtype.val_injective
  have hP_span : (⨆ r : B.breaks, P r) = ⊤ := by
    rw [iSup_subtype]
    rw [← B.pieces_internal.submodule_iSup_eq_top]
    refine le_antisymm ?_ ?_
    · exact iSup₂_le fun r hr => le_iSup (fun r : ℝ => B.piece r) r
    · refine iSup_le fun r => ?_
      by_cases hr : r ∈ B.breaks
      · exact le_iSup_of_le r (le_iSup_of_le hr le_rfl)
      · rw [B.piece_eq_bot_of_not_mem hr]
        exact bot_le
  have hP_internal : DirectSum.IsInternal P :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hP_indep hP_span
  let _ : DirectSum.Decomposition P := hP_internal.chooseDecomposition
  let H : Subgroup G := chapter05UpperRamificationGroup D u
  let F : Submodule L V := chapter06FixedSpace ρ H
  let Q : B.breaks → Submodule L V := fun r => P r ⊓ F
  have hQ_indep : iSupIndep Q :=
    hP_indep.mono (fun r => inf_le_left)
  have hhom : ∀ x : V, x ∈ F → ∀ i : B.breaks,
      (DirectSum.decompose P x i : V) ∈ F := by
    intro x hx i
    rw [chapter06FixedSpace.mem_iff] at hx ⊢
    intro g
    let f : ∀ j : B.breaks, P j →ₗ[L] P j := fun j =>
      ((ρ (g : G)).comp (P j).subtype).codRestrict (P j) (by
        intro y
        exact B.pieces_invariant (j : ℝ) (g : G) y
          (by simp [P] using y.property))
    have hmap :
        (DirectSum.decomposeLinearEquiv P) ∘ₗ (ρ (g : G)) =
          (DirectSum.lmap f) ∘ₗ (DirectSum.decomposeLinearEquiv P) := by
      apply DirectSum.decompose_lhom_ext P
      intro j
      apply LinearMap.ext
      intro y
      apply DirectSum.ext
      intro i'
      simp only [LinearMap.comp_apply]
      change (DirectSum.decomposeLinearEquiv P
          ((ρ (g : G)) ((P j).subtype y)) i') =
        (DirectSum.lmap f
          (DirectSum.decomposeLinearEquiv P ((P j).subtype y)) i')
      have hy : (ρ (g : G)) ((P j).subtype y) = (f j y : V) := by rfl
      rw [hy, DirectSum.decomposeLinearEquiv_apply_coe]
      simp [f]
    have hcomp := congrArg (fun z => (z i : V))
      (DFunLike.congr_fun hmap x)
    simp only [LinearMap.comp_apply] at hcomp
    rw [hx g] at hcomp
    simp only [DirectSum.lmap_apply] at hcomp
    change ((DirectSum.decomposeLinearEquiv P x) i : V) =
      (f i ((DirectSum.decomposeLinearEquiv P x) i) : V) at hcomp
    have hfi :
        (f i ((DirectSum.decomposeLinearEquiv P x) i) : V) =
          (ρ (g : G)) ((DirectSum.decomposeLinearEquiv P x) i : V) := by rfl
    rw [hfi] at hcomp
    exact hcomp.symm
  have hQ_span : (⨆ r : B.breaks, Q r) = F := by
    apply le_antisymm
    · exact iSup_le fun r => inf_le_right
    · intro x hx
      rw [← DirectSum.sum_support_decompose P x]
      exact sum_mem fun i hi => by
        exact (le_iSup Q i) ⟨(DirectSum.decompose P x i).property, hhom x hx i⟩
  let Q' : B.breaks → Submodule L F := fun r => (Q r).comap F.subtype
  have hcomap_disjoint :
      ∀ {A B : Submodule L V}, Disjoint A B →
        Disjoint (A.comap F.subtype) (B.comap F.subtype) := by
    intro A B h
    rw [disjoint_iff, ← Submodule.comap_inf, h.eq_bot]
    simp
  have hQ'_indep : iSupIndep Q' := by
    intro i
    let R : Submodule L V :=
      iSup (fun j : B.breaks => iSup (fun _ : j ≠ i => Q j))
    let R' : Submodule L F :=
      iSup (fun j : B.breaks =>
        iSup (fun _ : j ≠ i => (Q j).comap F.subtype))
    change Disjoint ((Q i).comap F.subtype) R'
    have hrest : R' ≤ R.comap F.subtype := by
      refine iSup_le fun j => iSup_le fun hj => ?_
      exact Submodule.comap_mono
        (le_iSup_of_le j (le_iSup_of_le hj le_rfl))
    exact (hcomap_disjoint (hQ_indep i)).mono_right hrest
  have hmapQ :
      (⨆ r : B.breaks, Q' r).map F.subtype = ⨆ r : B.breaks, Q r := by
    rw [Submodule.map_iSup]
    apply iSup_congr
    intro r
    rw [Submodule.map_comap_subtype]
    exact inf_eq_right.mpr inf_le_right
  have hQ'_span : (⨆ r : B.breaks, Q' r) = ⊤ := by
    apply top_unique
    intro x hx
    have hxV : F.subtype x ∈ (⨆ r : B.breaks, Q r) := by
      rw [hQ_span]
      exact x.property
    have hxmap :
        F.subtype x ∈ (⨆ r : B.breaks, Q' r).map F.subtype := by
      rw [hmapQ]
      exact hxV
    have hxcomap :
        x ∈ ((⨆ r : B.breaks, Q' r).map F.subtype).comap F.subtype :=
      hxmap
    rw [Submodule.comap_map_eq_of_injective Subtype.coe_injective] at hxcomap
    exact hxcomap
  have hQ'_internal : DirectSum.IsInternal Q' :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      hQ'_indep hQ'_span
  let _ : DirectSum.Decomposition Q' := hQ'_internal.chooseDecomposition
  have hPfin :
      Module.finrank L V = ∑ r : B.breaks, Module.finrank L (P r) := by
    rw [LinearEquiv.finrank_eq (DirectSum.decomposeLinearEquiv P)]
    simp
  have hFfin :
      Module.finrank L F = ∑ r : B.breaks, Module.finrank L (Q' r) := by
    rw [LinearEquiv.finrank_eq (DirectSum.decomposeLinearEquiv Q')]
    simp
  have hQfin : ∀ r : B.breaks,
      Module.finrank L (Q' r) = Module.finrank L (Q r) := by
    intro r
    rw [← Submodule.finrank_map_subtype_eq F (Q' r)]
    rw [Submodule.map_comap_subtype]
    rw [inf_eq_right.mpr inf_le_right]
  have hFfinQ :
      Module.finrank L F = ∑ r : B.breaks, Module.finrank L (Q r) := by
    simpa only [hQfin] using hFfin
  have hquot := Submodule.finrank_quotient_add_finrank F
  rw [hPfin, hFfinQ] at hquot
  have hcodim :
      Module.finrank L (V ⧸ F) =
        (∑ r : B.breaks, Module.finrank L (P r)) -
          (∑ r : B.breaks, Module.finrank L (Q r)) :=
    Nat.eq_sub_of_add_eq hquot
  let Qreal : ℝ → Submodule L V := fun r => (B.piece r) ⊓ F
  have hsumP :
      (∑ r : B.breaks, Module.finrank L (P r)) =
        ∑ r ∈ B.breaks, Module.finrank L (B.piece r) := by
    rw [← B.breaks.sum_attach]
    simp [P]
  have hsumQ :
      (∑ r : B.breaks, Module.finrank L (Q r)) =
        ∑ r ∈ B.breaks, Module.finrank L (Qreal r) := by
    rw [← B.breaks.sum_attach]
    simp [P, Q, Qreal]
  have hcodim_target :
      Module.finrank L (V ⧸ F) =
        (∑ r ∈ B.breaks, Module.finrank L (B.piece r)) -
          ∑ r ∈ B.breaks, Module.finrank L (Qreal r) := by
    rw [← hsumP, ← hsumQ]
    exact hcodim
  have hsum :
      (∑ r ∈ B.breaks,
        (Module.finrank L (B.piece r) - Module.finrank L (Qreal r))) =
      (∑ r ∈ B.breaks, Module.finrank L (B.piece r)) -
        ∑ r ∈ B.breaks, Module.finrank L (Qreal r) := by
    exact Finset.sum_tsub_distrib B.breaks
      (fun r hr =>
        Submodule.finrank_mono (show Qreal r ≤ B.piece r from inf_le_left))
  have htarget :
      Module.finrank L (V ⧸ F) =
        ∑ r ∈ B.breaks,
          (Module.finrank L (B.piece r) - Module.finrank L (Qreal r)) := by
    rw [hsum]
    exact hcodim_target
  simpa [chapter06UpperFixedSpaceCodim, chapter06FixedSpaceCodim,
      chapter06PieceFixedSpaceCodim, Qreal, F, H] using htarget

theorem chapter06_swan_conductor_sum_formula
    {L : Type u} {G : Type v} {V : Type w}
    [Field L] [Group G] [Finite G] [AddCommGroup V] [Module L V]
    [FiniteDimensional L V]
    {D : Chapter05RamificationFiltration G}
    {ρ : Representation L G V}
    (B : Chapter06UpperBreakDecomposition D ρ) :
    chapter06SwanConductor D ρ =
      ∑ r ∈ B.positiveBreaks,
        (r : ℝ) * (Module.finrank L (B.piece r) : ℝ) := by
  sorry

/-!
The following predicates separate the arithmetic content of break labels
from the decomposition itself.  The finite-level Hasse--Arf result from the
earlier chapters can supply the group-break hypothesis; the transfer to a
representation is independent of any infinite sum.
-/

def chapter06AllGroupUpperBreaksIntegral
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) : Prop :=
  ∀ r : ℝ, chapter05UpperBreak D r →
    ∃ n : ℤ, (n : ℝ) = r

def chapter06AllGroupUpperBreaksRational
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) : Prop :=
  ∀ r : ℝ, chapter05UpperBreak D r →
    ∃ q : ℚ, (q : ℝ) = r

def chapter06AllRepresentationBreaksIntegral
    {L : Type u} {G : Type v} {V : Type w}
    [Field L] [Group G] [Finite G] [AddCommGroup V] [Module L V]
    [FiniteDimensional L V]
    (D : Chapter05RamificationFiltration G)
    (ρ : Representation L G V) : Prop :=
  ∀ r : ℝ, chapter06RepresentationUpperBreak D ρ r →
    ∃ n : ℤ, (n : ℝ) = r

def chapter06AllRepresentationBreaksRational
    {L : Type u} {G : Type v} {V : Type w}
    [Field L] [Group G] [Finite G] [AddCommGroup V] [Module L V]
    [FiniteDimensional L V]
    (D : Chapter05RamificationFiltration G)
    (ρ : Representation L G V) : Prop :=
  ∀ r : ℝ, chapter06RepresentationUpperBreak D ρ r →
    ∃ q : ℚ, (q : ℝ) = r

theorem chapter06_abelian_representation_breaks_integral
    {L : Type u} {G : Type v} {V : Type w}
    [Field L] [Group G] [Finite G] [AddCommGroup V] [Module L V]
    [FiniteDimensional L V]
    (D : Chapter05RamificationFiltration G)
    (ρ : Representation L G V)
    (habelian : ∀ g h : G, g * h = h * g)
    (hhasse_arf : chapter06AllGroupUpperBreaksIntegral D) :
    chapter06AllRepresentationBreaksIntegral D ρ := by
  sorry

theorem chapter06_representation_breaks_rational
    {L : Type u} {G : Type v} {V : Type w}
    [Field L] [Group G] [Finite G] [AddCommGroup V] [Module L V]
    [FiniteDimensional L V]
    (D : Chapter05RamificationFiltration G)
    (ρ : Representation L G V)
    (hgroup : chapter06AllGroupUpperBreaksRational D) :
    chapter06AllRepresentationBreaksRational D ρ := by
  sorry

def chapter06TotalSwanConductorIntegral
    {L : Type u} {G : Type v} {V : Type w}
    [Field L] [Group G] [Finite G] [AddCommGroup V] [Module L V]
    [FiniteDimensional L V]
    (D : Chapter05RamificationFiltration G)
    (ρ : Representation L G V) : Prop :=
  ∃ n : ℤ, (n : ℝ) = chapter06SwanConductor D ρ

/-- The source-facing integrality API for a finite-image representation on a
realized finite local Galois profile. -/
theorem chapter06_finite_image_representation_total_swan_conductor_integral
    {K L F V : Type*}
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] [Finite (L ≃ₐ[K] L)]
    [Field F] [CharZero F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V]
    (D : Chapter05LocalGaloisUpperData K L)
    (ρ : Representation F (L ≃ₐ[K] L) V)
    (hperfect :
      PerfectField (IsLocalRing.ResidueField D.vK.toValuation.valuationSubring)) :
    chapter06TotalSwanConductorIntegral D.profile ρ := by
  sorry

theorem chapter06_swan_conductor_rational_of_rational_breaks
    {L : Type u} {G : Type v} {V : Type w}
    [Field L] [Group G] [Finite G] [AddCommGroup V] [Module L V]
    [FiniteDimensional L V]
    {D : Chapter05RamificationFiltration G}
    {ρ : Representation L G V}
    (B : Chapter06UpperBreakDecomposition D ρ)
    (hrational : chapter06AllRepresentationBreaksRational D ρ) :
    ∃ q : ℚ, (q : ℝ) = chapter06SwanConductor D ρ := by
  sorry

/-!
The integral total Swan assertion for a general nonabelian representation is
exposed by the finite local Galois profile API above; its proof is the later
Artin-character theorem.  In contrast, the rational conductor statement above
is already the finite-break consequence available in this chapter.  Separability
of one chosen residue level is therefore enough for the decomposition and
rational formula, but does not supply the integral conclusion.
-/

end

end LastLib.Book03RamificationTheory.Chapter06
