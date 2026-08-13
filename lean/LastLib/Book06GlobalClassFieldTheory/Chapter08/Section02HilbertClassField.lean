import LastLib.Book06GlobalClassFieldTheory.Chapter08.Dependencies

namespace LastLib.Book06GlobalClassFieldTheory.Chapter08

noncomputable section

open NumberField

universe u

/-! ## 8.2. The Hilbert class field -/

theorem chapter08_hilbert_modulus_is_trivial
    {K : Type u} [Field K] [NumberField K] :
    chapter08TrivialModulus K =
      { finitePart := (⊤ : Ideal (𝓞 K)),
        finitePart_ne_bot := by simp,
        infinitePart := ∅ } := by
  rfl

noncomputable def chapter08_hilbert_galois_group_equiv_class_group
    {K : Type u} [Field K] [NumberField K]
    (H : Chapter08HilbertClassFieldData K) :
    letI : Field H.carrier := H.carrierField
    letI : Algebra K H.carrier := H.carrierAlgebra
    letI : NumberField H.carrier := H.carrierNumberField
    letI : FiniteDimensional K H.carrier := H.carrierFinite
    letI : IsAbelianGalois K H.carrier := H.carrierAbelianGalois
    Gal(chapter08HilbertClassField H / K) ≃* chapter08OrdinaryClassGroup K := by
  exact H.classGroupEquiv.symm

noncomputable def chapter08_hilbert_class_group_equiv_galois_group
    {K : Type u} [Field K] [NumberField K]
    (H : Chapter08HilbertClassFieldData K) :
    letI : Field H.carrier := H.carrierField
    letI : Algebra K H.carrier := H.carrierAlgebra
    letI : NumberField H.carrier := H.carrierNumberField
    letI : FiniteDimensional K H.carrier := H.carrierFinite
    letI : IsAbelianGalois K H.carrier := H.carrierAbelianGalois
    chapter08OrdinaryClassGroup K ≃* Gal(chapter08HilbertClassField H / K) := by
  exact H.classGroupEquiv

theorem chapter08_hilbert_unramified_at_every_finite_place
    {K : Type u} [Field K] [NumberField K]
    (H : Chapter08HilbertClassFieldData K) :
    letI : Field H.carrier := H.carrierField
    letI : Algebra K H.carrier := H.carrierAlgebra
    letI : NumberField H.carrier := H.carrierNumberField
    letI : FiniteDimensional K H.carrier := H.carrierFinite
    letI : IsAbelianGalois K H.carrier := H.carrierAbelianGalois
    letI : Algebra (𝓞 K) (𝓞 H.carrier) := inferInstance
    chapter08UnramifiedAtFinitePlaces K (chapter08HilbertClassField H) := by
  exact H.unramifiedAtFinite

theorem chapter08_hilbert_real_places_stay_real
    {K : Type u} [Field K] [NumberField K]
    (H : Chapter08HilbertClassFieldData K) :
    letI : Field H.carrier := H.carrierField
    letI : Algebra K H.carrier := H.carrierAlgebra
    letI : NumberField H.carrier := H.carrierNumberField
    letI : FiniteDimensional K H.carrier := H.carrierFinite
    letI : IsAbelianGalois K H.carrier := H.carrierAbelianGalois
    chapter08RealPlacesStayReal K (chapter08HilbertClassField H) := by
  exact H.realPlacesStayReal

theorem chapter08_hilbert_is_maximal_finite_unramified_real_preserving
    {K : Type u} [Field K] [NumberField K]
    (H : Chapter08HilbertClassFieldData K)
    {L : Type u} [Field L] [NumberField L] [Algebra K L]
    [Algebra (𝓞 K) (𝓞 L)] [FiniteDimensional K L] [IsAbelianGalois K L]
    (hunram : chapter08UnramifiedAtFinitePlaces K L)
    (hreal : chapter08RealPlacesStayReal K L) :
    letI : Field H.carrier := H.carrierField
    letI : Algebra K H.carrier := H.carrierAlgebra
    letI : NumberField H.carrier := H.carrierNumberField
    letI : FiniteDimensional K H.carrier := H.carrierFinite
    letI : IsAbelianGalois K H.carrier := H.carrierAbelianGalois
    chapter08ExtensionContained K L (chapter08HilbertClassField H) := by
  sorry

noncomputable def chapter08_narrow_hilbert_galois_group_equiv_narrow_class_group
    {K : Type u} [Field K] [NumberField K]
    (N : Chapter08NarrowClassGroupData K)
    (H : Chapter08NarrowHilbertClassFieldData K N) :
    letI : Field H.carrier := H.carrierField
    letI : Algebra K H.carrier := H.carrierAlgebra
    letI : NumberField H.carrier := H.carrierNumberField
    letI : FiniteDimensional K H.carrier := H.carrierFinite
    letI : IsAbelianGalois K H.carrier := H.carrierAbelianGalois
    chapter08NarrowClassGroup N ≃*
      Gal(chapter08NarrowHilbertClassField H / K) := by
  exact H.narrowClassGroupEquiv

theorem chapter08_narrow_hilbert_is_maximal_finite_unramified
    {K : Type u} [Field K] [NumberField K]
    (N : Chapter08NarrowClassGroupData K)
    (H : Chapter08NarrowHilbertClassFieldData K N)
    {L : Type u} [Field L] [NumberField L] [Algebra K L]
    [Algebra (𝓞 K) (𝓞 L)] [FiniteDimensional K L] [IsAbelianGalois K L]
    (hunram : chapter08UnramifiedAtFinitePlaces K L) :
    letI : Field H.carrier := H.carrierField
    letI : Algebra K H.carrier := H.carrierAlgebra
    letI : NumberField H.carrier := H.carrierNumberField
    letI : FiniteDimensional K H.carrier := H.carrierFinite
    letI : IsAbelianGalois K H.carrier := H.carrierAbelianGalois
    chapter08ExtensionContained K L (chapter08NarrowHilbertClassField H) := by
  sorry

/- The narrow field permits complexification at real places; no real-place
condition is intentionally added to the maximality statement above. -/
theorem chapter08_narrow_hilbert_forgets_infinite_unramified_condition
    {K : Type u} [Field K] [NumberField K]
    (N : Chapter08NarrowClassGroupData K)
    (H : Chapter08NarrowHilbertClassFieldData K N) :
    letI : Field H.carrier := H.carrierField
    letI : Algebra K H.carrier := H.carrierAlgebra
    letI : NumberField H.carrier := H.carrierNumberField
    letI : FiniteDimensional K H.carrier := H.carrierFinite
    letI : IsAbelianGalois K H.carrier := H.carrierAbelianGalois
    letI : Algebra (𝓞 K) (𝓞 H.carrier) := inferInstance
    chapter08UnramifiedAtFinitePlaces K (chapter08NarrowHilbertClassField H) := by
  exact H.unramifiedAtFinite

end
end LastLib.Book06GlobalClassFieldTheory.Chapter08
