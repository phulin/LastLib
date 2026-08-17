import LastLib.Book05LocalClassFieldTheory.Chapter09.Dependencies

namespace LastLib.Book05LocalClassFieldTheory.Chapter09

noncomputable section

open CategoryTheory
open LastLib.Book05LocalClassFieldTheory.Chapter05

/-!
## 9.2 Norm corresponds to Galois inclusion
-/

/--
Theorem 9.1 (norm–inclusion compatibility).

This is the equality represented by the first reciprocity square:
`rec_K ∘ N_{L/K} = i_* ∘ rec_L`.
-/
theorem chapter09_norm_inclusion_compatibility
    (K L Ks : Type) [Field K] [Field L] [Field Ks]
    [Algebra K L] [Algebra K Ks] [Algebra L Ks]
    [IsScalarTower K L Ks] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (T : Chapter09FiniteSeparableExtension K L Ks)
    (R : Chapter09ReciprocitySystem K L Ks T) :
    R.recK.reciprocity.comp (chapter09NormHom K L) =
      (chapter09GaloisInclusionAbelianization K L Ks).comp R.recL.reciprocity := by
  sorry

theorem chapter09_norm_inclusion_compatibility_apply
    (K L Ks : Type) [Field K] [Field L] [Field Ks]
    [Algebra K L] [Algebra K Ks] [Algebra L Ks]
    [IsScalarTower K L Ks] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (T : Chapter09FiniteSeparableExtension K L Ks)
    (R : Chapter09ReciprocitySystem K L Ks T) (x : Lˣ) :
    R.recK.reciprocity (chapter09NormHom K L x) =
      chapter09GaloisInclusionAbelianization K L Ks (R.recL.reciprocity x) := by
  simpa only [MonoidHom.comp_apply] using
    DFunLike.congr_fun (chapter09_norm_inclusion_compatibility K L Ks T R) x

/-!
The proof of Theorem 9.1 uses the finite-level restriction of the fundamental
class and the two corestriction maps from Section 5.2.  Mathlib's pinned Tate
cohomology API does not package those maps, so this record keeps their native
types and records exactly the finite-level identities used here.
-/

structure Chapter09FiniteNormInclusionData
    (G : Type) [Group G] [Fintype G]
    (H : Subgroup G) (A : Rep ℤ G) where
  fundamentalClassG : chapter05GroupCohomology G A 2
  fundamentalClassH :
    chapter05GroupCohomology H (Rep.res H.subtype A) 2
  /- These are the degree `-2` cap maps after the top-subgroup
     identifications supplied by the finite-level class-formation data. -/
  capProductG :
    chapter05TateCohomology G (Rep.trivial ℤ G ℤ) (-2) ⟶
      chapter05TateCohomology G A 0
  capProductH :
    chapter05TateCohomology H (Rep.trivial ℤ H ℤ) (-2) ⟶
      chapter05TateCohomology H (Rep.res H.subtype A) 0
  corestrictionMinusTwo :
    chapter05TateCohomology H (Rep.trivial ℤ H ℤ) (-2) ⟶
      chapter05TateCohomology G (Rep.trivial ℤ G ℤ) (-2)
  corestrictionZero :
    chapter05TateCohomology H (Rep.res H.subtype A) 0 ⟶
      chapter05TateCohomology G A 0
  fundamentalClass_restriction :
    chapter05RestrictTwoClass H fundamentalClassG = fundamentalClassH
  corestrictionMinusTwo_on_H1 :
    ∀ z : chapter05GroupHomology H (Rep.trivial ℤ H ℤ) 1,
      (chapter05H1AbelianizationIso G)
          ((chapter05_tate_minus_two_is_homology G).hom
            (corestrictionMinusTwo
              ((chapter05_tate_minus_two_is_homology H).inv z))) =
        Additive.ofMul
          (Abelianization.map H.subtype
            ((chapter05H1AbelianizationIso H) z))
  projection_formula :
    ∀ z : chapter05TateCohomology H (Rep.trivial ℤ H ℤ) (-2),
      corestrictionZero (capProductH z) =
        capProductG (corestrictionMinusTwo z)

theorem chapter09_finite_fundamental_class_restriction
    {G : Type} [Group G] [Fintype G]
    {H : Subgroup G} {A : Rep ℤ G}
    (D : Chapter09FiniteNormInclusionData G H A) :
    chapter05RestrictTwoClass H D.fundamentalClassG = D.fundamentalClassH :=
  D.fundamentalClass_restriction

theorem chapter09_finite_corestriction_on_H1
    {G : Type} [Group G] [Fintype G]
    {H : Subgroup G} {A : Rep ℤ G}
    (D : Chapter09FiniteNormInclusionData G H A)
    (z : chapter05GroupHomology H (Rep.trivial ℤ H ℤ) 1) :
    (chapter05H1AbelianizationIso G)
        ((chapter05_tate_minus_two_is_homology G).hom
          (D.corestrictionMinusTwo
            ((chapter05_tate_minus_two_is_homology H).inv z))) =
      Additive.ofMul
        (Abelianization.map H.subtype
          ((chapter05H1AbelianizationIso H) z)) :=
  D.corestrictionMinusTwo_on_H1 z

theorem chapter09_finite_norm_inclusion_projection_formula
    {G : Type} [Group G] [Fintype G]
    {H : Subgroup G} {A : Rep ℤ G}
    (D : Chapter09FiniteNormInclusionData G H A)
    (z : chapter05TateCohomology H (Rep.trivial ℤ H ℤ) (-2)) :
    D.corestrictionZero (D.capProductH z) =
      D.capProductG (D.corestrictionMinusTwo z) :=
  D.projection_formula z

/- The degree-zero corestriction is the multiplicative field norm on the
fixed-point representative, hence also on the corresponding norm quotient. -/

structure Chapter09FiniteDegreeZeroNormData
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] where
  corestriction : Lˣ →* Kˣ
  corestriction_is_norm : corestriction = chapter09NormHom K L

theorem chapter09_finite_degree_zero_corestriction_is_norm
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (D : Chapter09FiniteDegreeZeroNormData K L) :
    D.corestriction = chapter09NormHom K L :=
  D.corestriction_is_norm

/- In normalized valuations, the unramified exponent check is the special case
of the norm-valuation formula with residue degree `f` and a uniformizer of
value one. -/

theorem chapter09_unramified_norm_uniformizer_valuation
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    {vK : AddValuation K (WithTop ℤ)}
    {vL : AddValuation L (WithTop ℤ)} (f : ℕ)
    (hformula : ∀ x : L, x ≠ 0 →
      vK (Algebra.norm K x) = (f : WithTop ℤ) * vL x)
    (πL : L) (hπL : πL ≠ 0) (hvalue : vL πL = 1) :
    vK (Algebra.norm K πL) = (f : WithTop ℤ) := by
  rw [hformula πL hπL, hvalue]
  simp

end

end LastLib.Book05LocalClassFieldTheory.Chapter09
