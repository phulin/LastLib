import LastLib.Book05LocalClassFieldTheory.Chapter09.Dependencies

namespace LastLib.Book05LocalClassFieldTheory.Chapter09

noncomputable section

/-!
## 9.2 Norm corresponds to Galois inclusion
-/

/--
Theorem 9.1 (norm–inclusion compatibility).

This is the equality represented by the first reciprocity square:
`rec_K ∘ N_{L/K} = i_* ∘ rec_L`.
-/
theorem chapter09_norm_inclusion_compatibility
    (K L Ks : Type*) [Field K] [Field L] [Field Ks]
    [Algebra K L] [Algebra K Ks] [Algebra L Ks]
    [IsScalarTower K L Ks] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (T : Chapter09FiniteSeparableExtension K L Ks)
    (R : Chapter09ReciprocitySystem K L Ks T) :
    R.recK.comp (chapter09NormHom K L) =
      (chapter09GaloisInclusionAbelianization K L Ks).comp R.recL := by
  sorry

theorem chapter09_norm_inclusion_compatibility_apply
    (K L Ks : Type*) [Field K] [Field L] [Field Ks]
    [Algebra K L] [Algebra K Ks] [Algebra L Ks]
    [IsScalarTower K L Ks] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (T : Chapter09FiniteSeparableExtension K L Ks)
    (R : Chapter09ReciprocitySystem K L Ks T) (x : Lˣ) :
    R.recK (chapter09NormHom K L x) =
      chapter09GaloisInclusionAbelianization K L Ks (R.recL x) := by
  simpa only [MonoidHom.comp_apply] using
    DFunLike.congr_fun (chapter09_norm_inclusion_compatibility K L Ks T R) x

end

end LastLib.Book05LocalClassFieldTheory.Chapter09
