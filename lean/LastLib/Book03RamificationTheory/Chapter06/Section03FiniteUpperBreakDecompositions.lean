import LastLib.Book03RamificationTheory.Chapter06.Section02FiniteImageRepresentationsNeedOnlyFiniteLevels
import LastLib.Book03RamificationTheory.Chapter05.Section06HasseArfAndTheLimitsOfIntegrality
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.RepresentationTheory.Maschke

namespace LastLib.Book03RamificationTheory.Chapter06

noncomputable section

open LastLib.Book03RamificationTheory.Chapter05
open MeasureTheory

open scoped BigOperators DirectSum

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
  let W' : Subrepresentation ρ :=
    { toSubmodule := W
      apply_mem_toSubmodule := by
        intro g x hx
        exact hW g x hx }
  let hsemisimple : Representation.IsSemisimpleRepresentation ρ :=
    chapter06_finite_group_representation_is_semisimple ρ
  obtain ⟨C', hC'⟩ := hsemisimple.exists_isCompl W'
  let C : Submodule L V := C'.toSubmodule
  refine ⟨C, ?_, ?_, ?_⟩
  · intro g x hx
    exact C'.apply_mem_toSubmodule g hx
  · change (W' ⊓ C').toSubmodule = (⊥ : Subrepresentation ρ).toSubmodule
    exact congrArg Subrepresentation.toSubmodule hC'.inf_eq_bot
  · change (W' ⊔ C').toSubmodule = (⊤ : Subrepresentation ρ).toSubmodule
    exact congrArg Subrepresentation.toSubmodule hC'.sup_eq_top

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
  let H : Subgroup G := chapter05UpperRamificationGroup D u
  let hnormal : H.Normal := chapter05_upper_group_normal D hbij u
  exact @chapter06_fixedSpace_invariant_of_normal L G V _ _ _ _ ρ H hnormal

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

theorem chapter06_upper_break_decomposition_exists_from_fixed_space_chain
    {L : Type u} {G : Type v} {V : Type w}
    [Field L] [CharZero L] [Group G] [Fintype G]
    [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D))
    (ρ : Representation L G V)
    (C : Chapter06RepresentationFixedSpaceChain D ρ) :
    Nonempty (Chapter06UpperBreakDecomposition D ρ) := by
  classical
  obtain ⟨n, chain, labels, hchain_zero, hchain_succ, hchain_last,
    hlabels_strict, hlabels_mem, hlabels_surj, hchain_mono, htel⟩ :=
    C.sorted_chain_telescopes
  have hright_normal : ∀ r : ℝ,
      (chapter05UpperRightLimit D r).Normal := by
    intro r
    unfold chapter05UpperRightLimit chapter05RightLimit
    apply Subgroup.sSup_normal
    intro H hH
    rcases hH with ⟨w, hw, rfl⟩
    exact chapter05_upper_group_normal D hbij w
  have hchain_invariant : ∀ i : Fin (n + 1),
      chapter06SubmoduleInvariant ρ (chain i) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [hchain_zero]
      exact @chapter06_fixedSpace_invariant_of_normal L G V _ _ _ _ ρ
        (chapter05UpperRightLimit D 0) (hright_normal 0)
    · rw [hchain_succ i]
      exact @chapter06_fixedSpace_invariant_of_normal L G V _ _ _ _ ρ
        (chapter05UpperRightLimit D (labels i)) (hright_normal (labels i))
  have hcomplement_exists : ∀ i : Fin n,
      ∃ Q : Submodule L V,
        chapter06SubmoduleInvariant ρ Q ∧
          chain i.castSucc ⊓ Q = ⊥ ∧ chain i.castSucc ⊔ Q = ⊤ := by
    intro i
    exact chapter06_invariant_complement_exists ρ (chain i.castSucc)
      (hchain_invariant i.castSucc)
  choose Q hQ_invariant hQ_inf hQ_sup using hcomplement_exists
  let P : Fin (n + 1) → Submodule L V :=
    Fin.cases (chain 0) (fun i => chain i.succ ⊓ Q i)
  have hP_zero : P 0 = chain 0 := by
    simp [P]
  have hP_succ : ∀ i : Fin n, P i.succ = chain i.succ ⊓ Q i := by
    intro i
    simp [P]
  have hstep_le : ∀ i : Fin n, chain i.castSucc ≤ chain i.succ := by
    intro i
    apply hchain_mono
    apply Fin.le_iff_val_le_val.mpr
    simp
  have hP_inf : ∀ i : Fin n, chain i.castSucc ⊓ P i.succ = ⊥ := by
    intro i
    rw [hP_succ, ← inf_assoc, inf_of_le_left (hstep_le i), hQ_inf i]
  have hP_sup : ∀ i : Fin n, chain i.castSucc ⊔ P i.succ = chain i.succ := by
    intro i
    rw [hP_succ]
    calc
      chain i.castSucc ⊔ (chain i.succ ⊓ Q i) =
          chain i.castSucc ⊔ (Q i ⊓ chain i.succ) := by rw [inf_comm]
      _ = (chain i.castSucc ⊔ Q i) ⊓ chain i.succ :=
        (sup_inf_assoc_of_le (Q i) (hstep_le i)).symm
      _ = chain i.succ := by rw [hQ_sup i, top_inf_eq]
  have hP_invariant : ∀ i : Fin (n + 1),
      chapter06SubmoduleInvariant ρ (P i) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [hP_zero]
      exact hchain_invariant 0
    · rw [hP_succ]
      intro g x hx
      exact ⟨hchain_invariant i.succ g x hx.1, hQ_invariant i g x hx.2⟩
  let S : Submodule L V := ⨆ i : Fin (n + 1), P i
  have hchain_le_S : ∀ k : Fin (n + 1), chain k ≤ S := by
    intro k
    induction k using Fin.induction with
    | zero =>
        change chain 0 ≤ ⨆ i : Fin (n + 1), P i
        rw [← hP_zero]
        exact le_iSup P 0
    | succ k ih =>
        rw [← hP_sup k]
        exact sup_le ih (le_iSup P k.succ)
  have hP_span : S = ⊤ := by
    apply top_unique
    rw [← hchain_last]
    exact hchain_le_S (Fin.last n)
  have hP_rank_step : ∀ i : Fin n,
      Module.finrank L (chain i.succ) =
        Module.finrank L (chain i.castSucc) + Module.finrank L (P i.succ) := by
    intro i
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (chain i.castSucc) (P i.succ)
    rw [hP_sup i, hP_inf i, finrank_bot, add_zero] at h
    exact h
  have hP_rank_telescope : ∀ (m : ℕ)
      (c : Fin (m + 1) → Submodule L V)
      (p : Fin (m + 1) → Submodule L V),
      p 0 = c 0 →
      (∀ i : Fin m, Module.finrank L (c i.succ) =
        Module.finrank L (c i.castSucc) + Module.finrank L (p i.succ)) →
      Module.finrank L (c 0) +
          ∑ i : Fin m,
            (Module.finrank L (c i.succ) -
              Module.finrank L (c i.castSucc)) =
        ∑ i : Fin (m + 1), Module.finrank L (p i) := by
    intro m
    induction m with
    | zero =>
        intro c p hp hstep
        simp only [Fin.sum_univ_zero]
        exact congrArg (fun q : Submodule L V => Module.finrank L q) hp.symm
    | succ m ih =>
        intro c p hp hstep
        let c' : Fin (m + 1) → Submodule L V := fun i => c i.castSucc
        let p' : Fin (m + 1) → Submodule L V := fun i => p i.castSucc
        have hp' : p' 0 = c' 0 := by
          simpa [c', p'] using hp
        have hstep' : ∀ i : Fin m, Module.finrank L (c' i.succ) =
            Module.finrank L (c' i.castSucc) + Module.finrank L (p' i.succ) := by
          intro i
          simpa [c', p'] using hstep i.castSucc
        have hi := ih c' p' hp' hstep'
        dsimp [c', p'] at hi
        have hlast := hstep (Fin.last m)
        have hlast_p : Module.finrank L (p (Fin.last (m + 1))) =
            Module.finrank L (c (Fin.last m).succ) -
              Module.finrank L (c (Fin.last m).castSucc) := by
          have hle : Module.finrank L (c (Fin.last m).castSucc) ≤
              Module.finrank L (c (Fin.last m).succ) := by
            rw [hlast]
            exact Nat.le_add_right _ _
          have hlast' : (Fin.last (m + 1) : Fin (m + 1 + 1)) =
              (Fin.last m).succ := by
            apply Fin.ext
            simp
          rw [hlast']
          omega
        have hsum_c :
            (∑ i : Fin (m + 1),
                (Module.finrank L (c i.succ) -
                  Module.finrank L (c i.castSucc))) =
              (∑ i : Fin m,
                (Module.finrank L (c i.castSucc.succ) -
                  Module.finrank L (c i.castSucc.castSucc))) +
                (Module.finrank L (c (Fin.last m).succ) -
                  Module.finrank L (c (Fin.last m).castSucc)) := by
          simpa using (Fin.sum_univ_castSucc
            (fun i : Fin (m + 1) =>
              Module.finrank L (c i.succ) - Module.finrank L (c i.castSucc)))
        have hsum_p :
            (∑ i : Fin (m + 1 + 1), Module.finrank L (p i)) =
          (∑ i : Fin (m + 1), Module.finrank L (p i.castSucc)) +
                Module.finrank L (p (Fin.last (m + 1))) := by
          simpa using (Fin.sum_univ_castSucc
            (fun i : Fin (m + 1 + 1) => Module.finrank L (p i)))
        rw [hsum_c, hsum_p]
        calc
          Module.finrank L (c 0) +
                ((∑ i : Fin m,
                  (Module.finrank L (c i.castSucc.succ) -
                    Module.finrank L (c i.castSucc.castSucc))) +
                  (Module.finrank L (c (Fin.last m).succ) -
                    Module.finrank L (c (Fin.last m).castSucc))) =
              (Module.finrank L (c 0) +
                ∑ i : Fin m,
                  (Module.finrank L (c i.castSucc.succ) -
                    Module.finrank L (c i.castSucc.castSucc))) +
                  (Module.finrank L (c (Fin.last m).succ) -
                    Module.finrank L (c (Fin.last m).castSucc)) := by
            simp [Nat.add_assoc]
          _ = (∑ i : Fin (m + 1), Module.finrank L (p i.castSucc)) +
                (Module.finrank L (c (Fin.last m).succ) -
                  Module.finrank L (c (Fin.last m).castSucc)) := by
            exact congrArg
              (fun x : ℕ => x +
                (Module.finrank L (c (Fin.last m).succ) -
                  Module.finrank L (c (Fin.last m).castSucc))) hi
          _ = (∑ i : Fin (m + 1), Module.finrank L (p i.castSucc)) +
                Module.finrank L (p (Fin.last (m + 1))) := by
            rw [hlast_p]
  have hP_rank : Module.finrank L V =
      ∑ i : Fin (n + 1), Module.finrank L (P i) := by
    rw [htel]
    exact hP_rank_telescope n chain P hP_zero hP_rank_step
  have hP_internal : DirectSum.IsInternal P := by
    have hP_range : LinearMap.range (DirectSum.coeLinearMap P) = ⊤ := by
      rw [DirectSum.range_coeLinearMap]
      exact hP_span
    have hP_dim : Module.finrank L (⨁ i : Fin (n + 1), P i) =
        Module.finrank L V := by
      rw [Module.finrank_directSum]
      exact hP_rank.symm
    have hP_ker : LinearMap.ker (DirectSum.coeLinearMap P) = ⊥ :=
      (LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank hP_dim).2 hP_range
    have hP_injective : Function.Injective (DirectSum.coeLinearMap P) := by
      rw [← LinearMap.ker_eq_bot]
      exact hP_ker
    have hP_surjective : Function.Surjective (DirectSum.coeLinearMap P) := by
      rw [← LinearMap.range_eq_top]
      exact hP_range
    exact ⟨hP_injective, hP_surjective⟩
  let U : ℝ → Subgroup G := chapter05UpperRamificationGroup D
  let F : ℝ → Submodule L V := fun r => chapter06FixedSpace ρ (U r)
  let R : ℝ → Submodule L V := fun r =>
    chapter06FixedSpace ρ (chapter05UpperRightLimit D r)
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
    exact ⟨w, hw, by
      simpa [A, U, chapter05UpperRightLimit, chapter05RightLimit] using hUw⟩
  have hright_upper : ∀ (r t : ℝ), r < t →
      U t ≤ chapter05UpperRightLimit D r := by
    intro r t hrt
    change U t ≤ sSup (U '' Set.Ioi r)
    exact le_sSup ⟨t, hrt, rfl⟩
  have hprior_fixed : ∀ i : Fin n,
      chain i.castSucc = F (labels i) := by
    intro i
    have hn : n ≠ 0 := by
      intro hn
      subst n
      exact Fin.elim0 i
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rcases i.eq_zero_or_eq_succ with rfl | ⟨k, rfl⟩
    · change chain 0 = F (labels 0)
      have hr : 0 < labels 0 :=
        (C.positiveBreaks_spec (labels 0)).mp (hlabels_mem 0) |>.1
      obtain ⟨w, hw, hUw⟩ := hright_mem 0
      have hFwR : F w = R 0 := by
        dsimp [F, R]
        rw [hUw]
      have hRF : R 0 = F (labels 0) := by
        by_cases hwr : w < labels 0
        · have hno : ∀ q ∈ C.positiveBreaks,
              ¬(w ≤ q ∧ q < labels 0) := by
            intro q hq hqint
            obtain ⟨j, hjq⟩ := hlabels_surj q hq
            have hj0 : (0 : Fin (m + 1)) ≤ j := Fin.zero_le j
            have hmon := hlabels_strict.monotone hj0
            have hq_ge : labels 0 ≤ q := by
              simpa [hjq] using hmon
            have hq_lt : q < labels 0 := hqint.2
            exact (not_lt_of_ge hq_ge) hq_lt
          have hconst := C.locally_constant_off_breaks
            (u := w) (w := labels 0) hw hwr.le hno
          have hWF : F w = F (labels 0) := by
            simpa [F, U] using hconst
          exact hFwR.symm.trans hWF
        · have hrl : labels 0 ≤ w := le_of_not_gt hwr
          have hRF_le : R 0 ≤ F (labels 0) := by
            apply chapter06FixedSpace.antitone ρ
            exact hright_upper 0 (labels 0) hr
          have hFR_le : F (labels 0) ≤ R 0 := by
            have hUw_le : U w ≤ U (labels 0) := hUanti hrl
            exact (by
              have hFF : F (labels 0) ≤ F w :=
                chapter06FixedSpace.antitone ρ hUw_le
              exact hFF.trans_eq hFwR)
          exact le_antisymm hFR_le hRF_le |>.symm
      calc
        chain 0 = R 0 := by simpa [R] using hchain_zero
        _ = F (labels 0) := hRF
    · change chain (Fin.castSucc (Fin.succ k)) = F (labels (Fin.succ k))
      have hr : 0 < labels (Fin.succ k) :=
        (C.positiveBreaks_spec (labels (Fin.succ k))).mp
          (hlabels_mem (Fin.succ k)) |>.1
      have hprev : labels k.castSucc < labels (Fin.succ k) :=
        hlabels_strict (by exact Fin.castSucc_lt_succ)
      obtain ⟨w, hw, hUw⟩ := hright_mem (labels k.castSucc)
      have hprev_pos : 0 < labels k.castSucc :=
        (C.positiveBreaks_spec (labels k.castSucc)).mp
          (hlabels_mem k.castSucc) |>.1
      have hwpos : 0 < w := lt_trans hprev_pos hw
      have hFwR : F w = R (labels k.castSucc) := by
        dsimp [F, R]
        rw [hUw]
      have hRF : R (labels k.castSucc) = F (labels (Fin.succ k)) := by
        by_cases hwr : w < labels (Fin.succ k)
        · have hno : ∀ q ∈ C.positiveBreaks,
              ¬(w ≤ q ∧ q < labels (Fin.succ k)) := by
            intro q hq hqint
            obtain ⟨j, hjq⟩ := hlabels_surj q hq
            have hj_lt_val : j.val < k.val + 1 := by
              by_contra hnot
              have hle_val : k.val + 1 ≤ j.val := le_of_not_gt hnot
              have hle : Fin.succ k ≤ j :=
                Fin.le_iff_val_le_val.mpr (by simpa using hle_val)
              have hmon := hlabels_strict.monotone hle
              have hq_ge : labels (Fin.succ k) ≤ q := by
                simpa [hjq] using hmon
              exact (not_lt_of_ge hq_ge) hqint.2
            have hk_lt_val : k.val < j.val := by
              by_contra hnot
              have hle_val : j.val ≤ k.val := le_of_not_gt hnot
              have hle : j ≤ k.castSucc :=
                Fin.le_iff_val_le_val.mpr (by simpa using hle_val)
              have hmon := hlabels_strict.monotone hle
              have hq_le : q ≤ labels k.castSucc := by
                simpa [hjq] using hmon
              have hq_gt : labels k.castSucc < q :=
                lt_of_lt_of_le hw hqint.1
              exact (not_lt_of_ge hq_le) hq_gt
            omega
          have hconst := C.locally_constant_off_breaks
            (u := w) (w := labels (Fin.succ k)) hwpos hwr.le hno
          have hWF : F w = F (labels (Fin.succ k)) := by
            simpa [F, U] using hconst
          exact hFwR.symm.trans hWF
        · have hrl : labels (Fin.succ k) ≤ w := le_of_not_gt hwr
          have hRF_le : R (labels k.castSucc) ≤ F (labels (Fin.succ k)) := by
            apply chapter06FixedSpace.antitone ρ
            exact hright_upper (labels k.castSucc) (labels (Fin.succ k)) hprev
          have hFR_le : F (labels (Fin.succ k)) ≤ R (labels k.castSucc) := by
            have hUw_le : U w ≤ U (labels (Fin.succ k)) := hUanti hrl
            have hFF : F (labels (Fin.succ k)) ≤ F w :=
              chapter06FixedSpace.antitone ρ hUw_le
            exact hFF.trans_eq hFwR
          exact le_antisymm hFR_le hRF_le |>.symm
      have hidx : (Fin.castSucc (Fin.succ k) : Fin ((m + 1) + 1)) =
          (Fin.succ (Fin.castSucc k) : Fin ((m + 1) + 1)) := by
        apply Fin.ext
        rfl
      calc
        chain (Fin.castSucc (Fin.succ k)) =
            chain (Fin.succ (Fin.castSucc k)) := by rw [hidx]
        _ = R (labels k.castSucc) := by
          simpa [R] using hchain_succ (Fin.castSucc k)
        _ = F (labels (Fin.succ k)) := hRF
  have hchain_jump : ∀ i : Fin n, chain i.castSucc ≠ chain i.succ := by
    intro i heq
    have hr : 0 < labels i :=
      (C.positiveBreaks_spec (labels i)).mp (hlabels_mem i) |>.1
    have hbreak := (C.positiveBreaks_spec (labels i)).mp (hlabels_mem i) |>.2
    apply (C.fixed_space_jump_iff hr).mp hbreak
    calc
      chapter06FixedSpace ρ (chapter05UpperRamificationGroup D (labels i)) =
          chain i.castSucc := by
            simpa [F, U] using (hprior_fixed i).symm
      _ = chain i.succ := heq
      _ = chapter06FixedSpace ρ (chapter05UpperRightLimit D (labels i)) :=
        hchain_succ i
  have hP_nonzero : ∀ i : Fin n, P i.succ ≠ ⊥ := by
    intro i hzero
    apply hchain_jump i
    have hsup := hP_sup i
    rw [hzero, sup_bot_eq] at hsup
    exact hsup
  have hzero_break : chapter06RepresentationUpperBreak D ρ 0 ↔
      chain 0 ≠ ⊥ := by
    rw [hchain_zero]
    simp [chapter06RepresentationUpperBreak]
  let index : ∀ r : ℝ, r ∈ C.positiveBreaks → Fin n := fun r hr =>
    Classical.choose (hlabels_surj r hr)
  have hindex_spec : ∀ (r : ℝ) (hr : r ∈ C.positiveBreaks),
      labels (index r hr) = r := by
    intro r hr
    dsimp [index]
    exact Classical.choose_spec (hlabels_surj r hr)
  let breaks : Finset ℝ :=
    if chain 0 = ⊥ then C.positiveBreaks else insert 0 C.positiveBreaks
  have hbreaks_characterization : ∀ r : ℝ,
      r ∈ breaks ↔ chapter06RepresentationUpperBreak D ρ r := by
    intro r
    by_cases hr0 : r = 0
    · subst r
      have hpos_zero : (0 : ℝ) ∉ C.positiveBreaks := by
        intro h
        exact (lt_irrefl (0 : ℝ)) (C.positiveBreaks_spec 0 |>.mp h |>.1)
      have hmem_zero : (0 : ℝ) ∈ breaks ↔ chain 0 ≠ ⊥ := by
        by_cases hbot : chain 0 = ⊥
        · simp [breaks, hbot, hpos_zero]
        · simp [breaks, hbot, hpos_zero]
      exact hmem_zero.trans hzero_break.symm
    · have hmem_pos : r ∈ C.positiveBreaks ↔
          chapter06RepresentationUpperBreak D ρ r := by
        rw [C.positiveBreaks_spec]
        constructor
        · rintro ⟨_, hbreak⟩
          exact hbreak
        · intro hbreak
          exact ⟨lt_of_le_of_ne hbreak.1 (Ne.symm hr0), hbreak⟩
      have hmem_breaks : r ∈ breaks ↔ r ∈ C.positiveBreaks := by
        by_cases hbot : chain 0 = ⊥
        · simp [breaks, hbot]
        · simp [breaks, hbot, hr0]
      exact hmem_breaks.trans hmem_pos
  have hbreaks_nonnegative : ∀ r ∈ breaks, 0 ≤ r := by
    intro r hr
    exact (hbreaks_characterization r).mp hr |>.1
  let piece : ℝ → Submodule L V := fun r =>
    if hr0 : r = 0 then P 0
    else if hr : r ∈ C.positiveBreaks then P (index r hr).succ
    else ⊥
  have hpiece_zero : piece 0 = chain 0 := by
    simp [piece, hP_zero]
  have hpiece_pos : ∀ {r : ℝ} (hr : r ∈ C.positiveBreaks),
      piece r = P (index r hr).succ := by
    intro r hr
    have hr0 : r ≠ 0 := by
      intro h
      subst r
      exact (lt_irrefl (0 : ℝ)) (C.positiveBreaks_spec 0 |>.mp hr |>.1)
    simp [piece, hr0, hr]
  have hP_right_fixed : ∀ i : Fin n,
      chapter06SubgroupActsTriviallyOn ρ
        (chapter05UpperRightLimit D (labels i)) (P i.succ) := by
    intro i g x hx
    have hPle : P i.succ ≤ chain i.succ := by
      rw [hP_succ]
      exact inf_le_left
    have hxchain : x ∈ chain i.succ := hPle hx
    have hxright : x ∈ chapter06FixedSpace ρ
        (chapter05UpperRightLimit D (labels i)) := by
      rw [← hchain_succ i]
      exact hxchain
    exact (chapter06FixedSpace.mem_iff ρ
      (chapter05UpperRightLimit D (labels i)) x).mp hxright g
  have hP_bottom : ∀ i : Fin n,
      P i.succ ⊓ chapter06FixedSpace ρ
          (chapter05UpperRamificationGroup D (labels i)) = ⊥ := by
    intro i
    have hprior : chain i.castSucc =
        chapter06FixedSpace ρ (chapter05UpperRamificationGroup D (labels i)) := by
      simpa [F, U] using hprior_fixed i
    rw [← hprior, inf_comm]
    exact hP_inf i
  have hpiece_nonzero_iff : ∀ r : ℝ, piece r ≠ ⊥ ↔ r ∈ breaks := by
    intro r
    by_cases hr0 : r = 0
    · subst r
      calc
        piece 0 ≠ ⊥ ↔ chain 0 ≠ ⊥ := by rw [hpiece_zero]
        _ ↔ chapter06RepresentationUpperBreak D ρ 0 := hzero_break.symm
        _ ↔ 0 ∈ breaks := (hbreaks_characterization 0).symm
    · by_cases hpos : r ∈ C.positiveBreaks
      · have hpne : P (index r hpos).succ ≠ ⊥ := hP_nonzero (index r hpos)
        have hbmem : r ∈ breaks := by
          apply (hbreaks_characterization r).2
          exact (C.positiveBreaks_spec r).mp hpos |>.2
        constructor
        · intro _
          exact hbmem
        · intro _
          rw [hpiece_pos hpos]
          exact hpne
      · have hbnot : r ∉ breaks := by
          intro hb
          have hbreak := (hbreaks_characterization r).mp hb
          apply hpos
          exact (C.positiveBreaks_spec r).mpr
            ⟨lt_of_le_of_ne hbreak.1 (Ne.symm hr0), hbreak⟩
        rw [show piece r = ⊥ by simp [piece, hr0, hpos]]
        simp [hbnot]
  have hpiece_invariant : ∀ r : ℝ,
      chapter06SubmoduleInvariant ρ (piece r) := by
    intro r
    by_cases hr0 : r = 0
    · rw [show piece r = piece 0 by rw [hr0]]
      rw [hpiece_zero]
      exact hchain_invariant 0
    · by_cases hpos : r ∈ C.positiveBreaks
      · rw [hpiece_pos hpos]
        exact hP_invariant (index r hpos).succ
      · simp [piece, hr0, hpos]
        intro g x hx
        have hx0 : x = 0 := by simpa using hx
        subst x
        simp
  let ι : Type := {r : ℝ // piece r ≠ ⊥}
  have hι_zero_or_pos : ∀ r : ι,
      (r : ℝ) = 0 ∨ (r : ℝ) ∈ C.positiveBreaks := by
    intro r
    by_cases hr0 : (r : ℝ) = 0
    · exact Or.inl hr0
    · have hbreak : (r : ℝ) ∈ breaks :=
        (hpiece_nonzero_iff (r : ℝ)).mp r.property
      have hupper := (hbreaks_characterization (r : ℝ)).mp hbreak
      exact Or.inr ((C.positiveBreaks_spec (r : ℝ)).mpr
        ⟨lt_of_le_of_ne hupper.1 (Ne.symm hr0), hupper⟩)
  let A : ι → Submodule L V := fun r => piece r
  let f : ι → Fin (n + 1) := fun r =>
    if hr0 : (r : ℝ) = 0 then 0
    else if hr : (r : ℝ) ∈ C.positiveBreaks then
      (index (r : ℝ) hr).succ
    else 0
  have hpositive_ne_zero : ∀ {r : ℝ}, r ∈ C.positiveBreaks → r ≠ 0 := by
    intro r hr hzero
    have hlt : (0 : ℝ) < 0 := by
      simpa [hzero] using (C.positiveBreaks_spec r |>.mp hr |>.1)
    exact (lt_irrefl (0 : ℝ)) hlt
  have hA_eq : ∀ r : ι, A r = P (f r) := by
    intro r
    rcases hι_zero_or_pos r with hr0 | hr
    · simp [A, f, hr0, piece]
    · have hr0 : (r : ℝ) ≠ 0 := by
        exact hpositive_ne_zero hr
      simp [A, f, hr0, hr, piece]
  have hf_inj : Function.Injective f := by
    intro r s hrs
    rcases hι_zero_or_pos r with hr0 | hr
    · rcases hι_zero_or_pos s with hs0 | hs
      · apply Subtype.ext
        exact hr0.trans hs0.symm
      · have hval := congrArg Fin.val hrs
        have hs0 : (s : ℝ) ≠ 0 := by
          exact hpositive_ne_zero hs
        simp [f, hr0, hs0, hs] at hval
    · rcases hι_zero_or_pos s with hs0 | hs
      · have hval := congrArg Fin.val hrs
        have hr0 : (r : ℝ) ≠ 0 := by
          exact hpositive_ne_zero hr
        simp [f, hr0, hs0, hr] at hval
      · have hidx : index (r : ℝ) hr = index (s : ℝ) hs := by
          apply Fin.ext
          have hval := congrArg Fin.val hrs
          have hr0 : (r : ℝ) ≠ 0 := by
            exact hpositive_ne_zero hr
          have hs0 : (s : ℝ) ≠ 0 := by
            exact hpositive_ne_zero hs
          simpa [f, hr0, hs0, hr, hs] using hval
        apply Subtype.ext
        calc
          (r : ℝ) = labels (index (r : ℝ) hr) :=
            (hindex_spec (r : ℝ) hr).symm
          _ = labels (index (s : ℝ) hs) := by rw [hidx]
          _ = (s : ℝ) := hindex_spec (s : ℝ) hs
  have hA_indep : iSupIndep A := by
    have hcomp : iSupIndep (P ∘ f) :=
      hP_internal.submodule_iSupIndep.comp hf_inj
    have hfun : A = P ∘ f := by
      funext r
      exact hA_eq r
    rw [hfun]
    exact hcomp
  have hP_le_A : ∀ i : Fin (n + 1), P i ≤ ⨆ r : ι, A r := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · by_cases hP0 : P 0 = ⊥
      · rw [hP0]
        exact bot_le
      · have hz : piece 0 ≠ ⊥ := by
          rw [hpiece_zero]
          exact hP0
        let r0 : ι := ⟨0, hz⟩
        have hA0 : A r0 = P 0 := by
          change piece (r0 : ℝ) = P 0
          dsimp [r0]
          exact hpiece_zero
        rw [← hA0]
        exact le_iSup A r0
    · have hj : labels j ∈ C.positiveBreaks := hlabels_mem j
      have hpne : piece (labels j) ≠ ⊥ := by
        rw [hpiece_pos hj]
        exact hP_nonzero (index (labels j) hj)
      let rj : ι := ⟨labels j, hpne⟩
      have hidx : index (labels j) hj = j := by
        apply hlabels_strict.injective
        exact hindex_spec (labels j) hj
      have hAj : A rj = P j.succ := by
        change piece (rj : ℝ) = P j.succ
        dsimp [rj]
        rw [hpiece_pos hj, hidx]
      rw [← hAj]
      exact le_iSup A rj
  have hA_span : (⨆ r : ι, A r) = (⊤ : Submodule L V) := by
    apply top_unique
    rw [← hP_span]
    change (⨆ i : Fin (n + 1), P i) ≤ ⨆ r : ι, A r
    exact iSup_le hP_le_A
  have hA_internal : DirectSum.IsInternal A :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hA_indep hA_span
  have hpieces_internal : DirectSum.IsInternal piece := by
    have hnonbot : DirectSum.IsInternal
        (fun r : {r : ℝ // piece r ≠ ⊥} => piece r) := by
      simpa [A, ι] using hA_internal
    exact (DirectSum.isInternal_ne_bot_iff).mp hnonbot
  have hP_le_right : ∀ i : Fin n, P i.succ ≤
      chapter06FixedSpace ρ (chapter05UpperRightLimit D (labels i)) := by
    intro i
    have hPle : P i.succ ≤ chain i.succ := by
      rw [hP_succ]
      exact inf_le_left
    rw [← hchain_succ i]
    exact hPle
  have hpiece_right_fixed : ∀ {r : ℝ}, r ∈ breaks → 0 < r →
      chapter06SubgroupActsTriviallyOn ρ
        (chapter05UpperRightLimit D r) (piece r) := by
    intro r hr hpos
    have hpositive : r ∈ C.positiveBreaks := by
      apply (C.positiveBreaks_spec r).mpr
      exact ⟨hpos, (hbreaks_characterization r).mp hr⟩
    rw [hpiece_pos hpositive]
    intro g x hx
    have hxright : x ∈ chapter06FixedSpace ρ
        (chapter05UpperRightLimit D r) := by
      rw [← hindex_spec r hpositive]
      exact hP_le_right (index r hpositive) hx
    exact (chapter06FixedSpace.mem_iff ρ
      (chapter05UpperRightLimit D r) x).mp hxright g
  have hpiece_upper_bottom : ∀ {r : ℝ}, r ∈ breaks → 0 < r →
      piece r ⊓ chapter06FixedSpace ρ
          (chapter05UpperRamificationGroup D r) = ⊥ := by
    intro r hr hpos
    have hpositive : r ∈ C.positiveBreaks := by
      apply (C.positiveBreaks_spec r).mpr
      exact ⟨hpos, (hbreaks_characterization r).mp hr⟩
    rw [hpiece_pos hpositive]
    calc
      P (index r hpositive).succ ⊓
          chapter06FixedSpace ρ (chapter05UpperRamificationGroup D r) =
          P (index r hpositive).succ ⊓
            chapter06FixedSpace ρ
              (chapter05UpperRamificationGroup D (labels (index r hpositive))) := by
        rw [hindex_spec r hpositive]
      _ = ⊥ := hP_bottom (index r hpositive)
  have hpiece_threshold : ∀ {r : ℝ}, r ∈ breaks → 0 < r → ∀ u : ℝ,
      chapter06SubgroupActsTriviallyOn ρ
        (chapter05UpperRamificationGroup D u) (piece r) ↔ r < u := by
    intro r hr hpos u
    have hpositive : r ∈ C.positiveBreaks := by
      apply (C.positiveBreaks_spec r).mpr
      exact ⟨hpos, (hbreaks_characterization r).mp hr⟩
    rw [hpiece_pos hpositive]
    constructor
    · intro htriv
      by_contra hnot
      have hur : u ≤ r := le_of_not_gt hnot
      have hUle : U r ≤ U u := hUanti hur
      have hfixed_le : chapter06FixedSpace ρ (U u) ≤
          chapter06FixedSpace ρ (U r) :=
        chapter06FixedSpace.antitone ρ hUle
      have hPle : P (index r hpositive).succ ≤
          chapter06FixedSpace ρ (U u) := by
        intro x hx
        rw [chapter06FixedSpace.mem_iff]
        intro g
        exact htriv g x hx
      have hPbot : P (index r hpositive).succ = ⊥ := by
        apply le_antisymm
        · intro x hx
          have hxupper : x ∈ chapter06FixedSpace ρ (U r) :=
            hfixed_le (hPle hx)
          have hxinf : x ∈ P (index r hpositive).succ ⊓
              chapter06FixedSpace ρ (U r) := ⟨hx, hxupper⟩
          have hxinf' : x ∈ P (index r hpositive).succ ⊓
              chapter06FixedSpace ρ
                (chapter05UpperRamificationGroup D (labels (index r hpositive))) := by
            rw [hindex_spec r hpositive]
            exact hxinf
          rw [hP_bottom (index r hpositive)] at hxinf'
          exact hxinf'
        · exact bot_le
      exact (hP_nonzero (index r hpositive)) hPbot
    · intro hru
      have hUright : U u ≤ chapter05UpperRightLimit D r :=
        hright_upper r u hru
      have hfixed_le : chapter06FixedSpace ρ
          (chapter05UpperRightLimit D r) ≤
          chapter06FixedSpace ρ (U u) :=
        chapter06FixedSpace.antitone ρ hUright
      intro g x hx
      have hxright : x ∈ chapter06FixedSpace ρ
          (chapter05UpperRightLimit D r) := by
        rw [← hindex_spec r hpositive]
        exact hP_le_right (index r hpositive) hx
      have hxu : x ∈ chapter06FixedSpace ρ (U u) := hfixed_le hxright
      exact (chapter06FixedSpace.mem_iff ρ (U u) x).mp hxu g
  refine ⟨{
    breaks := breaks
    piece := piece
    breaks_nonnegative := hbreaks_nonnegative
    breaks_characterization := hbreaks_characterization
    piece_nonzero_iff_mem := hpiece_nonzero_iff
    pieces_internal := hpieces_internal
    pieces_invariant := hpiece_invariant
    zero_piece_eq_wild_fixed := by
      calc
        piece 0 = chain 0 := hpiece_zero
        _ = chapter06FixedSpace ρ (chapter05UpperRightLimit D 0) := hchain_zero
    positive_piece_right_limit_fixed := hpiece_right_fixed
    positive_piece_upper_fixed_bottom := hpiece_upper_bottom
    positive_piece_action_threshold := hpiece_threshold
  }⟩

theorem chapter06_upper_break_decomposition_exists
    {L : Type u} {G : Type v} {V : Type w}
    [Field L] [CharZero L] [Group G] [Fintype G]
    [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D))
    (ρ : Representation L G V) :
    Nonempty (Chapter06UpperBreakDecomposition D ρ) := by
  obtain ⟨C⟩ := chapter06_representation_fixed_space_chain_exists D hbij ρ
  exact chapter06_upper_break_decomposition_exists_from_fixed_space_chain
    D hbij ρ C

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
  let ι : Type := {r : ℝ // r ∈ B.breaks}
  let A : ι → Submodule L V := fun r => B.piece r
  have hA_indep : iSupIndep A := by
    exact B.pieces_internal.submodule_iSupIndep.comp Subtype.coe_injective
  have hA_span : (⨆ r : ι, A r) = (⊤ : Submodule L V) := by
    have hrestrict : (⨆ r : ι, A r) = ⨆ r : ℝ, B.piece r := by
      apply le_antisymm
      · exact iSup_le fun r => le_iSup_of_le (r : ℝ) (by
          simp [A])
      · refine iSup_le fun r => ?_
        by_cases hr : r ∈ B.breaks
        · exact le_iSup_of_le ⟨r, hr⟩ (by simp [A])
        · rw [B.piece_eq_bot_of_not_mem hr]
          exact bot_le
    rw [hrestrict]
    exact B.pieces_internal.submodule_iSup_eq_top
  have hA : DirectSum.IsInternal A :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hA_indep hA_span
  have hA_bij : Function.Bijective (DirectSum.coeLinearMap A) := by
    exact hA
  let H : Subgroup G := chapter05UpperRamificationGroup D u
  let F : Submodule L V := chapter06FixedSpace ρ H
  let A0 : ι → Submodule L V := fun r => A r ⊓ F
  have hA0_indep : iSupIndep A0 := by
    exact hA_indep.mono (fun r => inf_le_left)
  have hA0_span : (⨆ r : ι, A0 r) = F := by
    apply le_antisymm
    · exact iSup_le fun r => inf_le_right
    · intro x hx
      let e : (⨁ r : ι, A r) ≃ₗ[L] V :=
        LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hA_bij
      let y : (⨁ r : ι, A r) := e.symm x
      have hy_mem : ∀ r : ι, (y r : V) ∈ F := by
        intro r
        change ∀ g : H, ρ (g : G) (y r : V) = y r
        intro g
        let φ : ∀ r : ι, A r →ₗ[L] A r := fun r =>
          ((ρ (g : G)).comp (A r).subtype).codRestrict (A r) (by
            intro z
            simpa [A] using B.pieces_invariant (r : ℝ) (g : G)
              (z : V) z.property)
        let T : (⨁ r : ι, A r) →ₗ[L] (⨁ r : ι, A r) := DirectSum.lmap φ
        have hT : (ρ (g : G)).comp (DirectSum.coeLinearMap A) =
            (DirectSum.coeLinearMap A).comp T := by
          apply DirectSum.linearMap_ext
          intro r
          ext z
          simp [T, φ]
        have hyT : y = T y := by
          apply e.injective
          dsimp [e]
          have hcoey : (DirectSum.coeLinearMap A) y = x := by
            simp [e, y]
          have hTy := congrArg (fun f : (⨁ r : ι, A r) →ₗ[L] V => f y) hT
          calc
            (DirectSum.coeLinearMap A) y = x := hcoey
            _ = ρ (g : G) x := ((chapter06FixedSpace.mem_iff ρ H x).mp hx g).symm
            _ = ρ (g : G) ((DirectSum.coeLinearMap A) y) :=
              congrArg (ρ (g : G)) hcoey.symm
            _ = (DirectSum.coeLinearMap A) (T y) := hTy
        have hyT_r := congrArg (fun z : (⨁ r : ι, A r) => z r) hyT
        exact (congrArg Subtype.val (by simpa [T, φ] using hyT_r)).symm
      rw [Submodule.mem_iSup_iff_exists_dfinsupp']
      let z : (⨁ r : ι, A0 r) :=
        DFinsupp.mk y.support (fun r =>
          ⟨y r, ⟨(y r).property, hy_mem r⟩⟩)
      refine ⟨z, ?_⟩
      have hxy : x = (DirectSum.coeLinearMap A) y := by
        simp [e, y]
      rw [hxy, DirectSum.coeLinearMap_eq_dfinsuppSum]
      simp only [z, DFinsupp.sum]
      rw [Finset.sum_subset DFinsupp.support_mk_subset]
      · apply Finset.sum_congr rfl
        intro r hr
        rw [DFinsupp.mk_of_mem hr]
      · intro r _ hr
        rw [DFinsupp.notMem_support_iff.mp hr]
        rfl
  have hA0F : DirectSum.IsInternal
      (fun r : ι => (A0 r).comap F.subtype) := by
    let s : Type := (Set.univ : Set ι)
    have hspan_univ : (⨆ i ∈ (Set.univ : Set ι), A0 i) = F := by
      simpa using hA0_span
    have htmp' : DirectSum.IsInternal
        (fun i : s => (A0 i).comap F.subtype) := by
      have htmp'' := DirectSum.isInternal_biSup_submodule_of_iSupIndep
        (A := A0) (s := (Set.univ : Set ι))
        (hA0_indep.comp Subtype.coe_injective)
      rw [hspan_univ] at htmp''
      exact htmp''
    let C : ι → Submodule L F := fun r => (A0 r).comap F.subtype
    let e : ι ≃ s := (Equiv.Set.univ ι).symm
    let eDS := DirectSum.lequivCongrLeft L (M := fun r => ↥(C r)) e
    have htmp : DirectSum.IsInternal
        (fun i : s => C (e.symm i)) := by
      simpa [C, e, Equiv.Set.univ] using htmp'
    have hcomp : (DirectSum.coeLinearMap (fun i : s => C (e.symm i))).comp
        eDS.toLinearMap = DirectSum.coeLinearMap C := by
      apply DirectSum.linearMap_ext
      intro i
      ext x
      simp only [LinearMap.comp_apply]
      change (((DirectSum.coeLinearMap (fun i : s => C (e.symm i)))
          (eDS (DirectSum.lof L ι (fun i => ↥(C i)) i x))) : V) =
        (((DirectSum.coeLinearMap C)
          (DirectSum.lof L ι (fun i => ↥(C i)) i x)) : V)
      dsimp [eDS]
      let hindex : e.symm (e i) = i := e.symm_apply_apply i
      let y' : C (e.symm (e i)) :=
        cast (congrArg (fun j => ↥(C j)) hindex.symm) x
      have hlof := DirectSum.lequivCongrLeft_lof (R := L)
        (M := fun j : ι => ↥(C j)) (e := e)
        hindex.symm x y' (by simp [y'])
      rw [hlof]
      simp only [DirectSum.coeLinearMap_lof]
      have hy' : (y' : V) = (x : V) := by
        dsimp [y']
        cases hindex
        rfl
      exact hy'
    have hC : DirectSum.IsInternal C := by
      have hbij : Function.Bijective (DirectSum.coeLinearMap C) := by
        constructor
        · intro x y hxy
          refine eDS.injective ?_
          refine htmp.injective ?_
          calc
            (DirectSum.coeLinearMap (fun i : s => C (e.symm i))) (eDS x) =
                (DirectSum.coeLinearMap C) x := by
              simpa using congrArg (fun f => f x) hcomp
            _ = (DirectSum.coeLinearMap C) y := hxy
            _ = (DirectSum.coeLinearMap (fun i : s => C (e.symm i))) (eDS y) := by
              symm
              simpa using congrArg (fun f => f y) hcomp
        · intro x
          obtain ⟨y, hy⟩ := htmp.surjective x
          refine ⟨eDS.symm y, ?_⟩
          have hcomp' := congrArg
            (fun f => f (eDS.symm y)) hcomp
          simp only [LinearMap.comp_apply] at hcomp'
          change (DirectSum.coeLinearMap (fun i : s => C (e.symm i)))
              (eDS (eDS.symm y)) =
            (DirectSum.coeLinearMap C) (eDS.symm y) at hcomp'
          rw [eDS.apply_symm_apply] at hcomp'
          exact hcomp'.symm.trans hy
      change Function.Bijective (DirectSum.coeLinearMap C)
      exact hbij
    exact hC
  have hdimV : Module.finrank L V =
      ∑ r : ι, Module.finrank L (A r) := by
    let e : (⨁ r : ι, A r) ≃ₗ[L] V :=
      LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hA_bij
    rw [← LinearEquiv.finrank_eq e, Module.finrank_directSum]
  have hdimF : Module.finrank L F =
      ∑ r : ι, Module.finrank L (A0 r) := by
    let C : ι → Submodule L F := fun r =>
      (A0 r).comap F.subtype
    have hC_bij : Function.Bijective (DirectSum.coeLinearMap C) := by
      change DirectSum.IsInternal C at hA0F
      exact hA0F
    let e : (⨁ r : ι, C r) ≃ₗ[L] F :=
      LinearEquiv.ofBijective (DirectSum.coeLinearMap C) hC_bij
    rw [← LinearEquiv.finrank_eq e, Module.finrank_directSum]
    apply Finset.sum_congr rfl
    intro r _
    simpa [C] using LinearEquiv.finrank_eq
      (Submodule.comapSubtypeEquivOfLe (p := A0 r) (q := F) (by
        exact inf_le_right))
  change Module.finrank L (V ⧸ F) =
    ∑ r ∈ B.breaks,
      chapter06PieceFixedSpaceCodim ρ (B.piece r) H
  have hdimV' := hdimV
  simp only [A] at hdimV'
  have hdimF' := hdimF
  simp only [A0, A] at hdimF'
  dsimp [ι] at hdimV' hdimF'
  rw [Submodule.finrank_quotient, hdimV', hdimF']
  rw [Finset.sum_attach B.breaks
    (fun r : ℝ => Module.finrank L (B.piece r))]
  rw [Finset.sum_attach B.breaks
    (fun r : ℝ => Module.finrank L
      (B.piece r ⊓ F : Submodule L V))]
  simp only [chapter06PieceFixedSpaceCodim]
  have hle (r : ℝ) (hr : r ∈ B.breaks) :
      Module.finrank L (B.piece r ⊓ F : Submodule L V) ≤
        Module.finrank L (B.piece r) := by
    exact Submodule.finrank_mono inf_le_left
  have hsum :
      (∑ r ∈ B.breaks, Module.finrank L
        (B.piece r ⊓ F : Submodule L V)) ≤
        ∑ r ∈ B.breaks, Module.finrank L (B.piece r) := by
    exact Finset.sum_le_sum (fun r hr => hle r hr)
  apply (tsub_eq_iff_eq_add_of_le hsum).2
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  exact (Nat.sub_add_cancel (hle r hr)).symm

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
  classical
  have hzero (v : ℝ) (hv : 0 < v) :
      chapter06PieceFixedSpaceCodim ρ (B.piece 0)
          (chapter05UpperRamificationGroup D v) = 0 := by
    have hle : chapter05UpperRamificationGroup D v ≤
        chapter05UpperRightLimit D 0 := by
      unfold chapter05UpperRightLimit chapter05RightLimit
      exact le_sSup ⟨v, hv, rfl⟩
    have hfix : B.piece 0 ≤ chapter06FixedSpace ρ
        (chapter05UpperRamificationGroup D v) := by
      rw [B.zero_piece_eq_wild_fixed]
      exact chapter06FixedSpace.antitone ρ hle
    rw [chapter06PieceFixedSpaceCodim, inf_eq_left.mpr hfix, Nat.sub_self]
  have hcodim (v : ℝ) (hv : 0 < v) :
      chapter06UpperFixedSpaceCodimReal D ρ v =
        ∑ r ∈ B.positiveBreaks,
          if v ≤ r then (Module.finrank L (B.piece r) : ℝ) else 0 := by
    rw [chapter06UpperFixedSpaceCodimReal,
      chapter06_upper_fixedSpaceCodim_decomposition B v, Nat.cast_sum]
    have hfull :
        (∑ r ∈ B.breaks,
            (chapter06PieceFixedSpaceCodim ρ (B.piece r)
              (chapter05UpperRamificationGroup D v) : ℝ)) =
          ∑ r ∈ B.breaks,
            if 0 < r then
              (if v ≤ r then (Module.finrank L (B.piece r) : ℝ) else 0)
            else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      by_cases hr_pos : 0 < r
      · rw [if_pos hr_pos,
          chapter06_piece_fixedSpaceCodim_step B hr hr_pos v]
        simp
      · have hr_zero : r = 0 := le_antisymm (le_of_not_gt hr_pos)
          (B.breaks_nonnegative r hr)
        subst r
        rw [hzero v hv]
        simp
    calc
      (∑ r ∈ B.breaks,
          (chapter06PieceFixedSpaceCodim ρ (B.piece r)
            (chapter05UpperRamificationGroup D v) : ℝ)) =
          ∑ r ∈ B.breaks,
            if 0 < r then
              (if v ≤ r then (Module.finrank L (B.piece r) : ℝ) else 0)
            else 0 := hfull
      _ = ∑ r ∈ B.positiveBreaks,
          if v ≤ r then (Module.finrank L (B.piece r) : ℝ) else 0 := by
        rw [Chapter06UpperBreakDecomposition.positiveBreaks,
          Finset.sum_filter]
  have hstep_integrable (r : ℝ) (hr : r ∈ B.positiveBreaks) :
      Integrable
        (fun v : ℝ =>
          if v ≤ r then (Module.finrank L (B.piece r) : ℝ) else 0)
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
    let c : ℝ := (Module.finrank L (B.piece r) : ℝ)
    have hconst : IntegrableOn (fun _ : ℝ => c) (Set.Ioc (0 : ℝ) r) :=
      integrableOn_const measure_Ioc_lt_top.ne
    have hind : Integrable
        ((Set.Ioc (0 : ℝ) r).indicator (fun _ : ℝ => c)) :=
      hconst.integrable_indicator measurableSet_Ioc
    have hres : IntegrableOn
        ((Set.Ioc (0 : ℝ) r).indicator (fun _ : ℝ => c))
        (Set.Ioi (0 : ℝ)) := hind.integrableOn
    apply hres.congr_fun
    · intro v hv
      by_cases hvr : v ≤ r
      · have hmem : v ∈ Set.Ioc (0 : ℝ) r := ⟨hv, hvr⟩
        simp [Set.indicator, hmem, hvr, c]
      · have hmem : v ∉ Set.Ioc (0 : ℝ) r := by
          simp [hvr]
        simp [Set.indicator, hmem, hvr, c]
    · exact measurableSet_Ioi
  have hstep (r : ℝ) (hr_pos : 0 < r) (c : ℝ) :
      (∫ v in Set.Ioi (0 : ℝ), if v ≤ r then c else 0) = r * c := by
    calc
      (∫ v in Set.Ioi (0 : ℝ), if v ≤ r then c else 0) =
          ∫ v in Set.Ioi (0 : ℝ),
            (Set.Ioc (0 : ℝ) r).indicator (fun _ : ℝ => c) v := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro v hv
        by_cases hvr : v ≤ r
        · have hmem : v ∈ Set.Ioc (0 : ℝ) r := ⟨hv, hvr⟩
          simp [Set.indicator, hmem, hvr]
        · have hmem : v ∉ Set.Ioc (0 : ℝ) r := by
            simp [hvr]
          simp [Set.indicator, hmem, hvr]
      _ = ∫ v in Set.Ioi (0 : ℝ) ∩ Set.Ioc (0 : ℝ) r,
          (fun _ : ℝ => c) v := by
        rw [setIntegral_indicator measurableSet_Ioc]
      _ = ∫ v in Set.Ioc (0 : ℝ) r, c := by
        rw [show Set.Ioi (0 : ℝ) ∩ Set.Ioc (0 : ℝ) r = Set.Ioc 0 r by
          ext v
          simp]
      _ = volume.real (Set.Ioc (0 : ℝ) r) • c := setIntegral_const c
      _ = r * c := by
        simp [hr_pos.le, smul_eq_mul]
  calc
    chapter06SwanConductor D ρ =
        ∫ v in Set.Ioi (0 : ℝ),
          ∑ r ∈ B.positiveBreaks,
            if v ≤ r then (Module.finrank L (B.piece r) : ℝ) else 0 := by
      unfold chapter06SwanConductor
      apply setIntegral_congr_ae measurableSet_Ioi
      exact Filter.Eventually.of_forall (fun v hv => hcodim v hv)
    _ = ∑ r ∈ B.positiveBreaks,
        ∫ v in Set.Ioi (0 : ℝ),
          if v ≤ r then (Module.finrank L (B.piece r) : ℝ) else 0 := by
      rw [integral_finsetSum]
      intro r hr
      exact hstep_integrable r hr
    _ = ∑ r ∈ B.positiveBreaks,
        (r : ℝ) * (Module.finrank L (B.piece r) : ℝ) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact hstep r (B.mem_positiveBreaks.mp hr).2
        (Module.finrank L (B.piece r) : ℝ)

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

/-!
The preceding Chapter 5 API proves rationality for every valid finite
Herbrand profile.  Exposing that fact here keeps the representation-level
statement source-facing instead of making users supply a property already
forced by `Chapter05RamificationFiltration`.
-/

theorem chapter06_all_group_upper_breaks_rational
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) :
    chapter06AllGroupUpperBreaksRational D := by
  intro r hr
  exact chapter05_upper_break_is_rational D
    (chapter05_herbrand_bijective_of_filtration D) hr

private theorem chapter06_representation_break_is_group_break_or_zero
    {L : Type u} {G : Type v} {V : Type w}
    [Field L] [Group G] [Finite G] [AddCommGroup V] [Module L V]
    [FiniteDimensional L V]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D))
    (ρ : Representation L G V) {r : ℝ}
    (hr : chapter06RepresentationUpperBreak D ρ r) :
    r = 0 ∨ chapter05UpperBreak D r := by
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
  change chapter06RepresentationUpperBreak D ρ r at hr
  rcases hr with ⟨hr_nonneg, hcases⟩
  by_cases hr0 : r = 0
  · exact Or.inl hr0
  · have hrpos : 0 < r := lt_of_le_of_ne hr_nonneg (Ne.symm hr0)
    right
    rw [chapter05UpperBreak, if_neg (by linarith)]
    refine ⟨by linarith, ?_⟩
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
    simpa [U] using hnot

theorem chapter06_abelian_representation_breaks_integral
    {L : Type u} {G : Type v} {V : Type w}
    [Field L] [Group G] [Finite G] [AddCommGroup V] [Module L V]
    [FiniteDimensional L V]
    (D : Chapter05RamificationFiltration G)
    (ρ : Representation L G V)
    (habelian : ∀ g h : G, g * h = h * g)
    (hhasse_arf : chapter06AllGroupUpperBreaksIntegral D) :
    chapter06AllRepresentationBreaksIntegral D ρ := by
  have _hcomm : (1 : G) * 1 = 1 * 1 := habelian 1 1
  intro r hr
  rcases chapter06_representation_break_is_group_break_or_zero D
      (chapter05_herbrand_bijective_of_filtration D) ρ hr with hr0 | hr_group
  · refine ⟨0, ?_⟩
    simp [hr0]
  · exact hhasse_arf r hr_group

theorem chapter06_representation_breaks_rational
    {L : Type u} {G : Type v} {V : Type w}
    [Field L] [Group G] [Finite G] [AddCommGroup V] [Module L V]
    [FiniteDimensional L V]
    (D : Chapter05RamificationFiltration G)
    (ρ : Representation L G V)
    (hgroup : chapter06AllGroupUpperBreaksRational D) :
    chapter06AllRepresentationBreaksRational D ρ := by
  intro r hr
  rcases chapter06_representation_break_is_group_break_or_zero D
      (chapter05_herbrand_bijective_of_filtration D) ρ hr with hr0 | hr_group
  · refine ⟨0, ?_⟩
    simp [hr0]
  · exact hgroup r hr_group

theorem chapter06_representation_breaks_rational_of_filtration
    {L : Type u} {G : Type v} {V : Type w}
    [Field L] [Group G] [Finite G] [AddCommGroup V] [Module L V]
    [FiniteDimensional L V]
    (D : Chapter05RamificationFiltration G)
    (ρ : Representation L G V) :
    chapter06AllRepresentationBreaksRational D ρ := by
  exact chapter06_representation_breaks_rational D ρ
    (chapter06_all_group_upper_breaks_rational D)

/-!
The local Hasse--Arf interface from Chapter 5 supplies the group-break
hypothesis used by the abstract representation transfer above.  These two
bridges state the source's perfect-residue specialization explicitly.
-/

theorem chapter06_local_group_upper_breaks_integral
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    (D : Chapter05LocalGaloisUpperData K L)
    (habelian : ∀ σ τ : Gal(L / K), σ * τ = τ * σ)
    [PerfectField (IsLocalRing.ResidueField D.vK.toValuation.valuationSubring)] :
    chapter06AllGroupUpperBreaksIntegral D.profile := by
  intro r hr
  exact chapter05_hasse_arf_upper_break_integer D habelian hr

theorem chapter06_local_abelian_representation_breaks_integral
    {K L F V : Type*}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    [Field F] [CharZero F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V]
    (D : Chapter05LocalGaloisUpperData K L)
    (ρ : Representation F (Gal(L / K)) V)
    (habelian : ∀ σ τ : Gal(L / K), σ * τ = τ * σ)
    [PerfectField (IsLocalRing.ResidueField D.vK.toValuation.valuationSubring)] :
    chapter06AllRepresentationBreaksIntegral D.profile ρ := by
  exact chapter06_abelian_representation_breaks_integral D.profile ρ habelian
    (chapter06_local_group_upper_breaks_integral D habelian)

def chapter06TotalSwanConductorIntegral
    {L : Type u} {G : Type v} {V : Type w}
    [Field L] [Group G] [Finite G] [AddCommGroup V] [Module L V]
    [FiniteDimensional L V]
    (D : Chapter05RamificationFiltration G)
    (ρ : Representation L G V) : Prop :=
  ∃ n : ℤ, (n : ℝ) = chapter06SwanConductor D ρ

theorem chapter06_swan_conductor_rational_of_rational_breaks
    {L : Type u} {G : Type v} {V : Type w}
    [Field L] [Group G] [Finite G] [AddCommGroup V] [Module L V]
    [FiniteDimensional L V]
    {D : Chapter05RamificationFiltration G}
    {ρ : Representation L G V}
    (B : Chapter06UpperBreakDecomposition D ρ)
    (hrational : chapter06AllRepresentationBreaksRational D ρ) :
    ∃ q : ℚ, (q : ℝ) = chapter06SwanConductor D ρ := by
  classical
  let qfun : ℝ → ℚ := fun r =>
    if h : r ∈ B.positiveBreaks then
      Classical.choose (hrational r
        ((B.breaks_characterization r).mp
          ((Chapter06UpperBreakDecomposition.mem_positiveBreaks B).mp h).1))
    else 0
  let q : ℚ := ∑ r ∈ B.positiveBreaks,
    qfun r * (Module.finrank L (B.piece r) : ℚ)
  refine ⟨q, ?_⟩
  rw [chapter06_swan_conductor_sum_formula B]
  simp only [q, Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast]
  apply Finset.sum_congr rfl
  intro r hr
  have hq := Classical.choose_spec (hrational r
    ((B.breaks_characterization r).mp
      ((Chapter06UpperBreakDecomposition.mem_positiveBreaks B).mp hr).1))
  simp only [qfun, dif_pos hr]
  rw [hq]

/-!
The predicate `chapter06TotalSwanConductorIntegral` is retained as the explicit
interface consumed by the later Artin-character theorem.  Chapter 6 itself
only proves the rational finite-break formula above; separability of one chosen
residue level does not supply general nonabelian integrality.
-/

end

end LastLib.Book03RamificationTheory.Chapter06
