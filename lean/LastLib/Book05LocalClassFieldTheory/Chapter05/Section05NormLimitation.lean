import Mathlib.Data.Fintype.Order
import LastLib.Book05LocalClassFieldTheory.Chapter05.Core

namespace LastLib.Book05LocalClassFieldTheory.Chapter05

noncomputable section

/-!
### 5.5. Norm limitation
-/

abbrev chapter05MaximalAbelianField
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :=
  chapter05MaximalAbelianSubextension K L

theorem chapter05_norm_limitation
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    chapter05NormSubgroup K L =
      chapter05NormSubgroup K (chapter05MaximalAbelianField K L) := by
  sorry

def chapter05NormIndex
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Finite (chapter05NormQuotient K L)] : ℕ :=
  Nat.card (chapter05NormQuotient K L)

theorem chapter05_norm_index_eq_maximal_abelian_degree
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Finite (chapter05NormQuotient K L)] :
    chapter05NormIndex K L =
      Module.finrank K (chapter05MaximalAbelianField K L) := by
  sorry

theorem chapter05_norm_index_eq_abelianization_card
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Finite (chapter05NormQuotient K L)] :
    chapter05NormIndex K L =
      Nat.card (chapter05Abelianization (Gal(L / K))) := by
  sorry

theorem chapter05_norm_limitation_index_formula
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Finite (chapter05NormQuotient K L)] :
    Nat.card (chapter05NormQuotient K L) =
      Module.finrank K (chapter05MaximalAbelianField K L) ∧
      Nat.card (chapter05NormQuotient K L) =
        Nat.card (chapter05Abelianization (Gal(L / K))) := by
  sorry

theorem chapter05_abelian_norm_index_eq_extension_degree
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))] [CommGroup (Gal(L / K))]
    [Finite (chapter05NormQuotient K L)] :
    chapter05NormIndex K L = Module.finrank K L := by
  sorry

/- The following declarations record the nonabelian warning from the source
without pretending that the extension degree is the norm index. -/
abbrev chapter05S3 := Equiv.Perm (Fin 3)

theorem chapter05S3_card : Nat.card chapter05S3 = 6 := by
  sorry

theorem chapter05S3_abelianization_card :
    Nat.card (chapter05Abelianization chapter05S3) = 2 := by
  sorry

theorem chapter05S3_norm_index_is_not_group_card :
    Nat.card (chapter05Abelianization chapter05S3) ≠ Nat.card chapter05S3 := by
  rw [chapter05S3_abelianization_card, chapter05S3_card]
  decide

/- SOURCE WARNING encoded by the API boundary: the norm-limitation theorem
above has `IsGalois K L`; no corresponding fixed-field equality is asserted
for a merely finite separable non-Galois extension. -/

end

end LastLib.Book05LocalClassFieldTheory.Chapter05
