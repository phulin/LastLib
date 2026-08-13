import LastLib.Book04AdelesAndIdeles.Chapter06.Section03ACompactFundamentalSet

namespace LastLib.Book04AdelesAndIdeles.Chapter06

noncomputable section

/-! # Book 4, Chapter 6, Section 6.5: The rational fundamental domain -/

universe uFin uHat

/-- The closed rational archimedean cell `[0, 1]`. -/
def chapter06RationalArchimedeanCell : Set ℝ := Set.Icc (0 : ℝ) 1

def chapter06RationalHalfOpenCell : Set ℝ := Set.Ico (0 : ℝ) 1

variable {Af : Type uFin} {Ohat : Type uHat}
variable [AddCommGroup Af] [AddCommGroup Ohat]
  [TopologicalSpace Af] [TopologicalSpace Ohat]

/-- The rational version of `D × Ohat`, with the finite integral embedding
left explicit so that the boundary identification is visible. -/
def chapter06RationalFundamentalSet
    (P : Chapter06AdeleData ℚ ℤ ℝ Af Ohat) : Set (ℝ × Af) :=
  chapter06FundamentalSet P chapter06RationalArchimedeanCell

theorem chapter06_rational_global_infinite_coordinate
    (P : Chapter06AdeleData ℚ ℤ ℝ Af Ohat)
    (hone : P.globalToInfinite (1 : ℚ) = (1 : ℝ)) (q : ℚ) :
    P.globalToInfinite q = (q : ℝ) := by
  simpa [hone] using map_ratCast_smul P.globalToInfinite ℚ ℝ q 1

/-- The closed rational cell still surjects onto the quotient. -/
theorem chapter06_rational_fundamental_set_surjective
    (P : Chapter06AdeleData ℚ ℤ ℝ Af Ohat)
    (hone : P.globalToInfinite (1 : ℚ) = (1 : ℝ)) :
    Function.Surjective
      (chapter06FundamentalSetQuotientMap P chapter06RationalArchimedeanCell) := by
  let D : Chapter06ArchimedeanCell P :=
    { carrier := chapter06RationalArchimedeanCell
      compact := isCompact_Icc
      covers := by
        intro x
        refine ⟨Int.floor x, ?_⟩
        have hfloor : P.integerToInfinite (Int.floor x) =
            ((Int.floor x : ℚ) : ℝ) := by
          calc
            P.integerToInfinite (Int.floor x) =
                P.globalToInfinite (P.integerToGlobal (Int.floor x)) := by simp
            _ = P.globalToInfinite (Int.floor x : ℚ) := by simp
            _ = ((Int.floor x : ℚ) : ℝ) :=
              chapter06_rational_global_infinite_coordinate P hone _
        rw [hfloor]
        constructor
        · exact sub_nonneg.mpr (Int.floor_le x)
        · apply sub_le_iff_le_add.mpr
          simpa [add_comm] using (Int.lt_floor_add_one x).le }
  simpa [D, chapter06RationalFundamentalSet] using
    chapter06_fundamental_set_quotient_surjective P D

/-- The half-open interval is the standard almost-everywhere choice of
representatives; its boundary is intentionally not identified globally here. -/
theorem chapter06_rational_half_open_cell_subset
    : chapter06RationalHalfOpenCell ⊆ chapter06RationalArchimedeanCell := by
  intro x hx
  exact ⟨hx.1, hx.2.le⟩

/-- The two endpoint representatives differ by the diagonal rational integer.
The finite coordinate is written with the same integer added, so the diagonal
action is visible in both components. -/
theorem chapter06_rational_boundary_representatives
    (P : Chapter06AdeleData ℚ ℤ ℝ Af Ohat) (u : Ohat)
    (hone : P.globalToInfinite (1 : ℚ) = (1 : ℝ)) :
    chapter06AdeleQuotientMap P
        (0, P.finiteIntegralEmbedding u) =
      chapter06AdeleQuotientMap P
        (1, P.finiteIntegralEmbedding u + P.globalToFinite 1) := by
  refine (chapter06AdeleQuotientMap_eq_iff P _ _).2 ?_
  change ∃ a : ℚ, chapter06Diagonal P a =
    (0, P.finiteIntegralEmbedding u) -
      (1, P.finiteIntegralEmbedding u + P.globalToFinite 1)
  refine ⟨(-1 : ℚ), ?_⟩
  change (P.globalToInfinite (-1), P.globalToFinite (-1)) =
    (0, P.finiteIntegralEmbedding u) -
      (1, P.finiteIntegralEmbedding u + P.globalToFinite 1)
  apply Prod.ext
  · simpa [sub_eq_add_neg] using
      (chapter06_rational_global_infinite_coordinate P hone (-1 : ℚ))
  · simp [sub_eq_add_neg]

theorem chapter06_rational_boundary_representatives_are_in_fundamental_set
    (P : Chapter06AdeleData ℚ ℤ ℝ Af Ohat) (u : Ohat) :
    (0, P.finiteIntegralEmbedding u) ∈ chapter06RationalFundamentalSet P ∧
      (1, P.finiteIntegralEmbedding u + P.globalToFinite 1) ∈
        chapter06RationalFundamentalSet P := by
  constructor
  · change (0 : ℝ) ∈ Set.Icc 0 1 ∧
      ∃ v : Ohat, P.finiteIntegralEmbedding v = P.finiteIntegralEmbedding u
    exact ⟨by norm_num, ⟨u, rfl⟩⟩
  · change (1 : ℝ) ∈ Set.Icc 0 1 ∧
      ∃ v : Ohat, P.finiteIntegralEmbedding v =
        P.finiteIntegralEmbedding u + P.globalToFinite 1
    refine ⟨by norm_num, ⟨u + P.integerToFinite 1, ?_⟩⟩
    simp

/- The source's final “not finite and not discrete” sentence is a theorem about
the concrete rational adele topology.  It is intentionally not stated for the
generic adapter above: arbitrary `Af` and `Ohat` types do not determine that
topology, and adding the desired infinitude or nondiscreteness as hypotheses
would make the declaration vacuous. -/

end

end LastLib.Book04AdelesAndIdeles.Chapter06
