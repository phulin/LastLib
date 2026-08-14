import LastLib.Book04AdelesAndIdeles.Chapter06.Section03ACompactFundamentalSet

namespace LastLib.Book04AdelesAndIdeles.Chapter06

noncomputable section

/-! # Book 4, Chapter 6, Section 6.4: A quotient model with integral gluing -/

universe uK uO uInf uFin uHat

variable {K : Type uK} {O : Type uO} {KInf : Type uInf} {Af : Type uFin}
  {Ohat : Type uHat}
variable [Field K] [CommRing O] [AddCommGroup KInf] [AddCommGroup Af]
  [AddCommGroup Ohat] [TopologicalSpace KInf] [TopologicalSpace Af]
  [TopologicalSpace Ohat]

/-- The integral-gluing subgroup is exactly the kernel of the restricted
surjection to the adelic quotient. -/
theorem chapter06_integral_gluing_kernel
    (P : Chapter06AdeleData K O KInf Af Ohat) :
    chapter06IntegralGluingSubgroup P =
      AddMonoidHom.ker (chapter06IntegralGluingMap P) := by
  ext x
  constructor
  · rintro ⟨a, ha⟩
    change chapter06IntegralGluingMap P x = 0
    have hglobal : chapter06IntegralGluingToAdele P x ∈
        chapter06GlobalSubgroup P := by
      refine (mem_chapter06ImageSubgroup (chapter06Diagonal P)
        (chapter06IntegralGluingToAdele P x)).2 ⟨P.integerToGlobal a, ?_⟩
      rw [← ha]
      simp
    rw [← chapter06AdeleQuotientMap_ker P] at hglobal
    exact hglobal
  · intro hx
    have hmem : chapter06IntegralGluingToAdele P x ∈
        chapter06GlobalSubgroup P := by
      rw [← chapter06AdeleQuotientMap_ker P]
      exact hx
    rcases hmem with ⟨a, ha⟩
    rcases (P.finite_integrality_characterization a).1 (by
      refine ⟨x.2, ?_⟩
      exact (congrArg Prod.snd ha).symm) with ⟨o, ho⟩
    refine ⟨o, ?_⟩
    apply Prod.ext
    · calc
        P.integerToInfinite o = P.globalToInfinite (P.integerToGlobal o) := by
          simp
        _ = P.globalToInfinite a := by rw [ho]
        _ = x.1 := congrArg Prod.fst ha
    · apply P.finiteIntegral_embedding.injective
      calc
        P.finiteIntegralEmbedding (P.integerToFinite o) =
            P.globalToFinite (P.integerToGlobal o) := by simp
        _ = P.globalToFinite a := by rw [ho]
        _ = P.finiteIntegralEmbedding x.2 := congrArg Prod.snd ha

/-- The composite `K∞ × Ohat → A_K → A_K/K` is surjective. -/
theorem chapter06_integral_gluing_surjective
    (P : Chapter06AdeleData K O KInf Af Ohat) :
    Function.Surjective (chapter06IntegralGluingMap P) := by
  intro y
  rcases chapter06AdeleQuotientMap_surjective P y with ⟨z, rfl⟩
  rcases P.finite_principal_parts z.2 with ⟨a, u, hu⟩
  refine ⟨(z.1 - P.globalToInfinite a, u), ?_⟩
  change chapter06AdeleQuotientMap P
      (z.1 - P.globalToInfinite a, P.finiteIntegralEmbedding u) =
    chapter06AdeleQuotientMap P z
  apply (chapter06AdeleQuotientMap_eq_iff P _ _).2
  refine ⟨-a, ?_⟩
  apply Prod.ext
  · simp
  · simp only [chapter06Diagonal_apply, map_neg, sub_eq_add_neg]
    dsimp
    rw [hu]
    abel

abbrev Chapter06IntegralGluingQuotient
    (P : Chapter06AdeleData K O KInf Af Ohat) :=
  (KInf × Ohat) ⧸ chapter06IntegralGluingSubgroup P

/-- The algebraic quotient model with diagonal integral gluing. -/
noncomputable def chapter06IntegralGluingEquiv
    (P : Chapter06AdeleData K O KInf Af Ohat)
    (hsurj : Function.Surjective (chapter06IntegralGluingMap P))
    (hker : chapter06IntegralGluingSubgroup P =
      AddMonoidHom.ker (chapter06IntegralGluingMap P)) :
    Chapter06IntegralGluingQuotient P ≃+
      Chapter06AdeleQuotient P :=
  QuotientAddGroup.liftEquiv (chapter06IntegralGluingSubgroup P) hsurj hker

@[simp] theorem chapter06IntegralGluingEquiv_mk
    (P : Chapter06AdeleData K O KInf Af Ohat)
    (hsurj : Function.Surjective (chapter06IntegralGluingMap P))
    (hker : chapter06IntegralGluingSubgroup P =
      AddMonoidHom.ker (chapter06IntegralGluingMap P))
    (x : KInf × Ohat) :
    chapter06IntegralGluingEquiv P hsurj hker
        (QuotientAddGroup.mk' (chapter06IntegralGluingSubgroup P) x) =
      chapter06IntegralGluingMap P x := by
  rfl

/-- Translation by an algebraic integer is the diagonal action used in the
integral-gluing quotient. -/
def chapter06IntegralTranslation
    (P : Chapter06AdeleData K O KInf Af Ohat) (a : O)
    (x : KInf × Ohat) : KInf × Ohat :=
  x + chapter06IntegralDiagonal P a

@[simp] theorem chapter06IntegralTranslation_apply
    (P : Chapter06AdeleData K O KInf Af Ohat) (a : O)
    (x : KInf × Ohat) :
    chapter06IntegralTranslation P a x =
      (x.1 + P.integerToInfinite a, x.2 + P.integerToFinite a) := rfl

theorem chapter06_integral_gluing_relation_iff
    (P : Chapter06AdeleData K O KInf Af Ohat)
    (x y : KInf × Ohat) :
    QuotientAddGroup.mk' (chapter06IntegralGluingSubgroup P) x =
        QuotientAddGroup.mk' (chapter06IntegralGluingSubgroup P) y ↔
      ∃ a : O, x + chapter06IntegralDiagonal P a = y := by
  constructor
  · intro hxy
    have hmem : x - y ∈ chapter06IntegralGluingSubgroup P :=
      (QuotientAddGroup.eq_iff_sub_mem).1 hxy
    rcases hmem with ⟨a, ha⟩
    refine ⟨-a, ?_⟩
    calc
      x + chapter06IntegralDiagonal P (-a) =
          x - chapter06IntegralDiagonal P a := by
        rw [map_neg]
        rw [sub_eq_add_neg]
      _ = y := by
        rw [ha]
        abel
  · rintro ⟨a, ha⟩
    apply (QuotientAddGroup.eq_iff_sub_mem).2
    refine ⟨-a, ?_⟩
    rw [map_neg]
    rw [← ha]
    abel

/-- The restricted map is open because the integral finite part is an open
subgroup and the adelic quotient map is open. -/
theorem chapter06_integral_gluing_map_is_open
    (P : Chapter06AdeleData K O KInf Af Ohat)
    [IsTopologicalAddGroup KInf] [IsTopologicalAddGroup Af]
    [IsTopologicalAddGroup Ohat] :
    IsOpenMap (chapter06IntegralGluingMap P) := by
  have hprod : Topology.IsOpenEmbedding
      (fun x : KInf × Ohat => (x.1, P.finiteIntegralEmbedding x.2)) := by
    refine ⟨Topology.IsEmbedding.id.prodMap P.finiteIntegral_embedding, ?_⟩
    have hrange : Set.range
        (fun x : KInf × Ohat => (x.1, P.finiteIntegralEmbedding x.2)) =
        Set.univ ×ˢ Set.range P.finiteIntegralEmbedding := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨Set.mem_univ _, ⟨x.2, rfl⟩⟩
      · rintro ⟨hz1, ⟨u, hu⟩⟩
        refine ⟨(z.1, u), ?_⟩
        simp [hu]
    rw [hrange]
    exact isOpen_univ.prod P.finiteIntegral_range_open
  have hq : IsOpenMap (chapter06AdeleQuotientMap P) := by
    change IsOpenMap (QuotientAddGroup.mk'
      (chapter06GlobalSubgroup P))
    exact QuotientAddGroup.isOpenMap_coe
  simpa [chapter06IntegralGluingMap, Function.comp_def] using
    hq.comp hprod.isOpenMap

/-- The algebraic quotient equivalence is a homeomorphism for the quotient
topologies. -/
theorem chapter06_integral_gluing_homeomorph
    (P : Chapter06AdeleData K O KInf Af Ohat)
    [IsTopologicalAddGroup KInf] [IsTopologicalAddGroup Af]
    [IsTopologicalAddGroup Ohat]
    (hker : chapter06IntegralGluingSubgroup P =
      AddMonoidHom.ker (chapter06IntegralGluingMap P)) :
    ∃ e : Chapter06IntegralGluingQuotient P ≃ₜ Chapter06AdeleQuotient P,
      ∀ x : KInf × Ohat,
        e (QuotientAddGroup.mk' (chapter06IntegralGluingSubgroup P) x) =
          chapter06IntegralGluingMap P x := by
  let hsurj := chapter06_integral_gluing_surjective P
  let e := chapter06IntegralGluingEquiv P hsurj hker
  have hcont_gluing : Continuous (chapter06IntegralGluingMap P) := by
    apply QuotientAddGroup.continuous_mk.comp
    have hto : Continuous
        (fun x : KInf × Ohat => (x.1, P.finiteIntegralEmbedding x.2)) :=
      continuous_fst.prodMk
        (P.finiteIntegral_embedding.continuous.comp continuous_snd)
    simpa [chapter06IntegralGluingToAdele] using hto
  have hcont : Continuous (e :
      Chapter06IntegralGluingQuotient P → Chapter06AdeleQuotient P) := by
    apply (QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff).1
    have heq : (e : Chapter06IntegralGluingQuotient P → Chapter06AdeleQuotient P) ∘
        (QuotientAddGroup.mk : (KInf × Ohat) →
          Chapter06IntegralGluingQuotient P) =
        chapter06IntegralGluingMap P := by
      funext x
      exact chapter06IntegralGluingEquiv_mk P hsurj hker x
    rw [heq]
    exact hcont_gluing
  have hopen : IsOpenMap (e :
      Chapter06IntegralGluingQuotient P → Chapter06AdeleQuotient P) := by
    apply (QuotientAddGroup.isOpenQuotientMap_mk.isOpenMap_iff).2
    have heq : (e : Chapter06IntegralGluingQuotient P → Chapter06AdeleQuotient P) ∘
        (QuotientAddGroup.mk : (KInf × Ohat) →
          Chapter06IntegralGluingQuotient P) =
        chapter06IntegralGluingMap P := by
      funext x
      exact chapter06IntegralGluingEquiv_mk P hsurj hker x
    rw [heq]
    exact chapter06_integral_gluing_map_is_open P
  refine ⟨e.toEquiv.toHomeomorphOfContinuousOpen hcont hopen, ?_⟩
  intro x
  exact chapter06IntegralGluingEquiv_mk P hsurj hker x

/-- The integral-gluing model is compact, as it is homeomorphic to the
    compact adelic quotient. -/
theorem chapter06_integral_gluing_quotient_compact
    (P : Chapter06AdeleData K O KInf Af Ohat)
    (D : Chapter06ArchimedeanCell P)
    [IsTopologicalAddGroup KInf] [IsTopologicalAddGroup Af]
    [IsTopologicalAddGroup Ohat] :
    CompactSpace (Chapter06IntegralGluingQuotient P) := by
  let _ : CompactSpace (Chapter06AdeleQuotient P) :=
    chapter06_adelic_quotient_compact P D
  rcases chapter06_integral_gluing_homeomorph P
      (chapter06_integral_gluing_kernel P) with ⟨e, he⟩
  refine ⟨?_⟩
  simpa using
    (e.isCompact_preimage.mpr
      (isCompact_univ : IsCompact
        (Set.univ : Set (Chapter06AdeleQuotient P))))

end

end LastLib.Book04AdelesAndIdeles.Chapter06
