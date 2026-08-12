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
  sorry

/-- The composite `K∞ × Ohat → A_K → A_K/K` is surjective. -/
theorem chapter06_integral_gluing_surjective
    (P : Chapter06AdeleData K O KInf Af Ohat)
    (D : Chapter06ArchimedeanCell P) :
    Function.Surjective (chapter06IntegralGluingMap P) := by
  sorry

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
  sorry

/-- The restricted map is open because the integral finite part is an open
subgroup and the adelic quotient map is open. -/
theorem chapter06_integral_gluing_map_is_open
    (P : Chapter06AdeleData K O KInf Af Ohat)
    [IsTopologicalAddGroup KInf] [IsTopologicalAddGroup Af]
    [IsTopologicalAddGroup Ohat] :
    IsOpenMap (chapter06IntegralGluingMap P) := by
  sorry

/-- The algebraic quotient equivalence is a homeomorphism for the quotient
topologies. -/
theorem chapter06_integral_gluing_homeomorph
    (P : Chapter06AdeleData K O KInf Af Ohat)
    (D : Chapter06ArchimedeanCell P)
    [IsTopologicalAddGroup KInf] [IsTopologicalAddGroup Af]
    [IsTopologicalAddGroup Ohat]
    (hker : chapter06IntegralGluingSubgroup P =
      AddMonoidHom.ker (chapter06IntegralGluingMap P)) :
    Nonempty
      (Chapter06IntegralGluingQuotient P ≃ₜ Chapter06AdeleQuotient P) := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter06
