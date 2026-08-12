import LastLib.Book04AdelesAndIdeles.Chapter06.Section04AQuotientModelWithIntegralGluing

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

/-- The closed rational cell still surjects onto the quotient. -/
theorem chapter06_rational_fundamental_set_surjective
    (P : Chapter06AdeleData ℚ ℤ ℝ Af Ohat) :
    Function.Surjective
      (chapter06FundamentalSetQuotientMap P chapter06RationalArchimedeanCell) := by
  sorry

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
    (P : Chapter06AdeleData ℚ ℤ ℝ Af Ohat) (u : Ohat) :
    chapter06AdeleQuotientMap P
        (0, P.finiteIntegralEmbedding u) =
      chapter06AdeleQuotientMap P
        (1, P.finiteIntegralEmbedding u + P.globalToFinite 1) := by
  sorry

theorem chapter06_rational_boundary_representatives_are_in_fundamental_set
    (P : Chapter06AdeleData ℚ ℤ ℝ Af Ohat) (u : Ohat) :
    (0, P.finiteIntegralEmbedding u) ∈ chapter06RationalFundamentalSet P ∧
      (1, P.finiteIntegralEmbedding u + P.globalToFinite 1) ∈
        chapter06RationalFundamentalSet P := by
  sorry

/-- The compact rational quotient is neither finite nor discrete once the
archimedean circle and its finite directions are retained.  The infinitude
and nondiscreteness inputs are exposed explicitly because they belong to the
earlier adelic topology API. -/
theorem chapter06_adelic_quotient_not_finite_or_discrete
    {K : Type*} {O : Type*} {KInf : Type*} {Af : Type*} {Ohat : Type*}
    [Field K] [CommRing O] [AddCommGroup KInf] [AddCommGroup Af]
    [AddCommGroup Ohat] [TopologicalSpace KInf] [TopologicalSpace Af]
    [TopologicalSpace Ohat]
    (P : Chapter06AdeleData K O KInf Af Ohat)
    (hinfinite : Infinite (Chapter06AdeleQuotient P))
    (hnondiscrete : ¬ DiscreteTopology (Chapter06AdeleQuotient P)) :
    ¬ Finite (Chapter06AdeleQuotient P) ∧
      ¬ DiscreteTopology (Chapter06AdeleQuotient P) := by
  sorry

/- The quotient is compact but the source's “not finite and not discrete”
warning is retained as a boundary comment: these properties depend on the
archimedean and finite-adele instances supplied by the preceding chapters. -/

end

end LastLib.Book04AdelesAndIdeles.Chapter06
