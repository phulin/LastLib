import LastLib.Book05LocalClassFieldTheory.Chapter08.Dependencies

namespace LastLib.Book05LocalClassFieldTheory.Chapter08

noncomputable section

open scoped IsMulCommutative Pointwise

/-! ## 8.4. The unit and ramification theorem -/

/- LOCAL_DEPENDENCY_GUESS: this is the exact numerical output of the earlier
  norm-index lemma (Lemma 6.4).  It records only the index equality, not the
  subgroup equality proved below. -/
structure Chapter08UnitRamificationInput
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))] [CommGroup (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L)
    (F : Chapter08RamificationFiltration (Gal(L / K))) where
  upper_bijective : Function.Bijective (chapter08HerbrandFunction F)
  index_formula : ∀ n : ℕ,
    ((chapter08UnitNormProduct X.base.valuation X.valuation n).comap
        (chapter08UnitFiltration X.base.valuation 0).subtype).index =
      (chapter08UpperGroup F n).relIndex (chapter08UpperGroup F 0)
  units_norm_from_fixed_field : ∀ n : ℕ,
    chapter08UnitFiltration X.base.valuation n ≤
      chapter08NormSubgroup K
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FixedField
          (K := K) (L := L) (chapter08UpperGroup F n))

theorem chapter08_unit_index_formula
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))] [CommGroup (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L)
    (F : Chapter08RamificationFiltration (Gal(L / K)))
    (P : Chapter08UnitRamificationInput X F) (n : ℕ) :
    ((chapter08UnitNormProduct X.base.valuation X.valuation n).comap
        (chapter08UnitFiltration X.base.valuation 0).subtype).index =
      (chapter08UpperGroup F n).relIndex (chapter08UpperGroup F 0) :=
  P.index_formula n

def chapter08FullNormUnitProduct
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (n : ℕ) : Subgroup Kˣ :=
  chapter08NormSubgroup K L ⊔ chapter08UnitFiltration vK n

theorem chapter08_unit_and_upper_ramification
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L)
    (D : Chapter08FiniteReciprocityData K L)
    (F : Chapter08RamificationFiltration (Gal(L / K)))
    (P : Chapter08UnitRamificationInput X F) (n : ℕ) :
    (chapter08UnitFiltration X.base.valuation n).map
        (chapter08FiniteReciprocityMap D) =
      chapter08UpperGroup F n := by
  sorry

theorem chapter08_unit_and_upper_ramification_preimage
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L)
    (D : Chapter08FiniteReciprocityData K L)
    (F : Chapter08RamificationFiltration (Gal(L / K)))
    (P : Chapter08UnitRamificationInput X F) (n : ℕ) :
    (chapter08FiniteReciprocityMap D).ker ⊔
        (chapter08UnitFiltration X.base.valuation n) =
      (chapter08UpperGroup F n).comap
        (chapter08FiniteReciprocityMap D) := by
  sorry

theorem chapter08_unit_and_upper_ramification_preimage_norm_form
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L)
    (D : Chapter08FiniteReciprocityData K L)
    (F : Chapter08RamificationFiltration (Gal(L / K)))
    (P : Chapter08UnitRamificationInput X F) (n : ℕ) :
    (chapter08UpperGroup F n).comap
        (chapter08FiniteReciprocityMap D) =
      chapter08FullNormUnitProduct (K := K) (L := L) X.base.valuation n := by
  sorry

theorem chapter08_unit_ramification_at_zero_is_inertia
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L)
    (D : Chapter08FiniteReciprocityData K L)
    (F : Chapter08RamificationFiltration (Gal(L / K)))
    (P : Chapter08UnitRamificationInput X F)
    (hinertia : chapter08UpperGroup F 0 = chapter08FiniteInertia X) :
    (chapter08UnitFiltration X.base.valuation 0).map
        (chapter08FiniteReciprocityMap D) =
      chapter08FiniteInertia X := by
  sorry

/- The quotient theorem from the preceding section is the formal reason the
   right-hand filtration is upper numbered.  A lower-numbered analogue is not
   supplied as a compatibility theorem. -/
theorem chapter08_upper_numbering_is_the_quotient_compatible_choice
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (S : LastLib.Book03RamificationTheory.Chapter05.Chapter05QuotientRamificationSetup
      G H)
    (hup : Function.Bijective (chapter08HerbrandFunction S.upstairs))
    (hdown : Function.Bijective (chapter08HerbrandFunction S.downstairs))
    {v : ℝ} (hv : (-1 : ℝ) ≤ v) :
    chapter08UpperGroup S.downstairs v =
      (chapter08UpperGroup S.upstairs v).map (QuotientGroup.mk' H) :=
  by
    sorry

end

end LastLib.Book05LocalClassFieldTheory.Chapter08
