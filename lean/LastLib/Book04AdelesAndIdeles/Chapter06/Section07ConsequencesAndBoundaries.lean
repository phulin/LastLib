import LastLib.Book04AdelesAndIdeles.Chapter06.Section06AdditiveHaarMeasureAndCovolume

namespace LastLib.Book04AdelesAndIdeles.Chapter06

noncomputable section

/-! # Book 4, Chapter 6, Section 6.7: Consequences and boundaries -/

universe uK uO uInf uFin uHat

variable {K : Type uK} {O : Type uO} {KInf : Type uInf} {Af : Type uFin}
  {Ohat : Type uHat}
variable [Field K] [CommRing O] [AddCommGroup KInf] [AddCommGroup Af]
  [AddCommGroup Ohat] [TopologicalSpace KInf] [TopologicalSpace Af]
  [TopologicalSpace Ohat]

/- The function-field analogue is deliberately not introduced here: the source
explicitly says that the complete-curve version is neither asserted nor used
in this number-field proof. -/

theorem chapter06_additive_local_global_compactness
    (P : Chapter06AdeleData K O KInf Af Ohat)
    (D : Chapter06ArchimedeanCell P)
    (hdiscrete : Chapter06DiscreteEmbedding (chapter06Diagonal P)) :
    Chapter06DiscreteEmbedding (chapter06Diagonal P) ∧
      CompactSpace (Chapter06AdeleQuotient P) := by
  exact ⟨hdiscrete, chapter06_adelic_quotient_compact P D⟩

theorem chapter06_finite_diagonal_is_dense
    (P : Chapter06AdeleData K O KInf Af Ohat) :
    Dense (Set.range P.globalToFinite) :=
  P.finite_diagonal_dense

/-- Omitting the archimedean factor leaves a dense proper diagonal, so the
finite-adelic quotient cannot be Hausdorff. -/
theorem chapter06_finite_adelic_quotient_not_hausdorff
    (P : Chapter06AdeleData K O KInf Af Ohat)
    [IsTopologicalAddGroup Af] [T2Space Af] :
    ¬ T2Space (Af ⧸ chapter06ImageSubgroup P.globalToFinite) := by
  sorry

abbrev chapter06CountableUnrestrictedRealProduct : Type := ℕ → ℝ

/-- The model unrestricted product with an infinite noncompact tail is not
locally compact. -/
theorem chapter06_countable_unrestricted_real_product_not_locally_compact :
    ¬ LocallyCompactSpace chapter06CountableUnrestrictedRealProduct := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter06
