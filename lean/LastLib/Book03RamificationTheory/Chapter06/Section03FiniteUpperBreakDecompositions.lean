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
  sorry

theorem chapter06_finite_image_level_action_is_semisimple
    {E : Type u} {P : ProfiniteGrp} {V : Type w}
    [Field E] [CharZero E] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V]
    {ρ : Chapter06FiniteImageRepresentation E P V}
    (R : Chapter06FiniteLevelRepresentation ρ) :
    Representation.IsSemisimpleRepresentation R.action := by
  sorry

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
  sorry

theorem chapter06_fixedSpace_invariant_of_normal
    {L : Type u} {G : Type v} {V : Type w}
    [Field L] [Group G] [AddCommGroup V] [Module L V]
    (ρ : Representation L G V) (H : Subgroup G) [H.Normal] :
    chapter06SubmoduleInvariant ρ (chapter06FixedSpace ρ H) := by
  sorry

theorem chapter06_upper_fixedSpace_invariant
    {L : Type u} {G : Type v} {V : Type w}
    [Field L] [Group G] [Finite G] [AddCommGroup V] [Module L V]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D))
    (ρ : Representation L G V) (u : ℝ) :
    chapter06SubmoduleInvariant ρ
      (chapter06FixedSpace ρ (chapter05UpperRamificationGroup D u)) := by
  sorry

theorem chapter06_upper_fixedSpace_chain
    {L : Type u} {G : Type v} {V : Type w}
    [Field L] [Group G] [Finite G] [AddCommGroup V] [Module L V]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D))
    (ρ : Representation L G V) {u w : ℝ} (huw : u ≤ w) :
    chapter06FixedSpace ρ (chapter05UpperRamificationGroup D u) ≤
      chapter06FixedSpace ρ (chapter05UpperRamificationGroup D w) := by
  sorry

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
  sorry

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
      if 0 < u ∧ u ≤ r then Module.finrank L (B.piece r) else 0 := by
  sorry

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
  sorry

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

/- LOCAL_DEPENDENCY_GUESS: the Artin-character integrality theorem is proved
later in the book and is not available in the earlier checkout.  This
finite-local statement records the intended theorem at the canonical
Chapter 5 local-Galois interface without assuming its conclusion as data. -/
theorem chapter06_total_swan_conductor_integral_of_artin_character_theorem
    {K M E : Type*} [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M]
    {V : Type*} [Field E] [CharZero E] [AddCommGroup V]
    [Module E V] [FiniteDimensional E V]
    (F : Chapter05LocalGaloisUpperData K M)
    [Algebra (IsLocalRing.ResidueField F.vK.toValuation.valuationSubring)
      (IsLocalRing.ResidueField F.vL.toValuation.valuationSubring)]
    [PerfectField (IsLocalRing.ResidueField F.vK.toValuation.valuationSubring)]
    (hresidue_separable :
      Algebra.IsSeparable
        (IsLocalRing.ResidueField F.vK.toValuation.valuationSubring)
        (IsLocalRing.ResidueField F.vL.toValuation.valuationSubring))
    (ρ : Representation E (Gal(M / K)) V) :
    chapter06TotalSwanConductorIntegral F.profile ρ := by
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
deliberately exposed as a proposition rather than asserted here: its proof is
the later Artin-character theorem.  In contrast, the rational conductor
statement above is already the finite-break consequence available in this
chapter.  Separability of one chosen residue level is therefore enough for
the decomposition and rational formula, but does not supply the integral
conclusion.
-/

end

end LastLib.Book03RamificationTheory.Chapter06
