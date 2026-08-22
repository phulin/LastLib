import LastLib.Book04AdelesAndIdeles.Chapter06.Section03ACompactFundamentalSet

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
    [IsTopologicalAddGroup KInf] [IsTopologicalAddGroup Af]
    [T2Space KInf] [T2Space Af]
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
    ¬ T2Space (Af ⧸ P.globalToFinite.range) := by
  intro hT2
  let _ : T2Space (Af ⧸ P.globalToFinite.range) := hT2
  have hclosed : IsClosed
      (P.globalToFinite.range : Set Af) :=
    (QuotientAddGroup.t1Space_iff).1
      (inferInstance : T1Space (Af ⧸ P.globalToFinite.range))
  have hclosed_range : IsClosed (Set.range P.globalToFinite) := by
    simpa using hclosed
  apply P.finite_diagonal_not_surjective
  calc
    Set.range P.globalToFinite = closure (Set.range P.globalToFinite) :=
      hclosed_range.closure_eq.symm
    _ = Set.univ := P.finite_diagonal_dense.closure_eq

abbrev chapter06CountableUnrestrictedRealProduct : Type := ℕ → ℝ

/-- The model unrestricted product with an infinite noncompact tail is not
locally compact. -/
theorem chapter06_countable_unrestricted_real_product_not_locally_compact :
    ¬ LocallyCompactSpace chapter06CountableUnrestrictedRealProduct := by
  intro hcompact
  let _ : LocallyCompactSpace chapter06CountableUnrestrictedRealProduct := hcompact
  let _ : FiniteDimensional ℝ chapter06CountableUnrestrictedRealProduct :=
    FiniteDimensional.of_locallyCompactSpace ℝ
  let v : ℕ → chapter06CountableUnrestrictedRealProduct :=
    fun n => Pi.single n (1 : ℝ)
  have hli : LinearIndependent ℝ v := by
    simpa [v] using Pi.linearIndependent_single_one ℕ ℝ
  exact (Module.Finite.not_linearIndependent_of_infinite v) hli

end

end LastLib.Book04AdelesAndIdeles.Chapter06
