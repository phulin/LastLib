import LastLib.Book04AdelesAndIdeles.Chapter01.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter01

open Module NumberField NumberField.InfinitePlace
open scoped nonZeroDivisors
open scoped Classical

noncomputable section

/-! ## 1.5 Ideal lattices and discriminants -/

variable (K : Type*) [Field K] [NumberField K]

theorem chapter01_discriminant_trace_determinant :
    chapter01Discriminant K =
      (Algebra.traceMatrix ℤ (NumberField.RingOfIntegers.basis K)).det := by
  rfl

theorem chapter01_discriminant_ne_zero :
    chapter01Discriminant K ≠ 0 := by
  exact NumberField.discr_ne_zero K

theorem chapter01_discriminant_independent_of_integral_basis
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ (𝓞 K)) :
    Algebra.discr ℤ b = chapter01Discriminant K := by
  exact NumberField.discr_eq_discr K b

theorem chapter01_integer_ideal_index_is_norm (I : Ideal (𝓞 K)) :
    Submodule.cardQuot I = chapter01AbsoluteIdealNorm I := by
  rfl

theorem chapter01_integer_lattice_covolume :
    ZLattice.covolume (E := chapter01MinkowskiSpace K)
        (NumberField.mixedEmbedding.integerLattice K) =
      (2⁻¹ : ℝ) ^ chapter01ComplexPlaceCount K *
        Real.sqrt |chapter01Discriminant K| := by
  simpa [chapter01ComplexPlaceCount, chapter01Discriminant] using
    (NumberField.mixedEmbedding.covolume_integerLattice K)

theorem chapter01_fractional_ideal_lattice_covolume
    (I : chapter01FractionalIdealGroup K) :
    ZLattice.covolume (E := chapter01MinkowskiSpace K)
        (NumberField.mixedEmbedding.idealLattice K I) =
      (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
        (2⁻¹ : ℝ) ^ chapter01ComplexPlaceCount K *
          Real.sqrt |chapter01Discriminant K| := by
  simpa [chapter01ComplexPlaceCount, chapter01Discriminant] using
    (NumberField.mixedEmbedding.covolume_idealLattice K I)

theorem chapter01_integral_ideal_lattice_covolume
    (I : (Ideal (𝓞 K))⁰) :
    ZLattice.covolume
        (E := chapter01MinkowskiSpace K)
        (NumberField.mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K I)) =
      ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℚ) : ℝ) *
          (2⁻¹ : ℝ) ^ chapter01ComplexPlaceCount K *
          Real.sqrt |chapter01Discriminant K| := by
  simpa [chapter01ComplexPlaceCount, chapter01Discriminant,
    FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm] using
    (NumberField.mixedEmbedding.covolume_idealLattice K (FractionalIdeal.mk0 K I))

theorem chapter01_fractional_basis_determinant_abs_norm
    (I : chapter01FractionalIdealGroup K)
    (e : (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) ≃
      (Module.Free.ChooseBasisIndex ℤ I)) :
    |(NumberField.integralBasis K).det
        ((NumberField.basisOfFractionalIdeal K I).reindex e.symm)| =
      FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) := by
  exact NumberField.det_basisOfFractionalIdeal_eq_absNorm K I e

end

end LastLib.Book04AdelesAndIdeles.Chapter01
