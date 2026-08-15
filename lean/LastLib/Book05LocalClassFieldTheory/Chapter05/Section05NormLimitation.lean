import Mathlib.Data.Fintype.Order
import Mathlib.Algebra.Algebra.Tower
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.RingTheory.Norm.Transitivity
import LastLib.Book05LocalClassFieldTheory.Chapter05.Core
import LastLib.Book05LocalClassFieldTheory.Chapter05.Section03ClassFormation
import LastLib.Book05LocalClassFieldTheory.Chapter05.Section04FiniteArtinMap

namespace LastLib.Book05LocalClassFieldTheory.Chapter05

noncomputable section

open scoped IsMulCommutative commutatorElement

/-!
### 5.5. Norm limitation
-/

abbrev chapter05MaximalAbelianField
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :=
  chapter05MaximalAbelianSubextension K L

theorem chapter05_norm_map_transitive
    (K L M : Type*) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] [FiniteDimensional K L]
    [FiniteDimensional L M] [FiniteDimensional K M] :
    chapter05NormMap K M =
      (chapter05NormMap K L).comp (chapter05NormMap L M) := by
  ext x
  change Algebra.norm K (x : M) =
    Algebra.norm K (Algebra.norm L (x : M))
  exact (Algebra.norm_norm (R := K) (S := L) (a := (x : M))).symm

theorem chapter05_norm_subgroup_mono_of_tower
    (K L M : Type*) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] [FiniteDimensional K L]
    [FiniteDimensional L M] [FiniteDimensional K M] :
    chapter05NormSubgroup K M ≤ chapter05NormSubgroup K L := by
  rintro x ⟨y, rfl⟩
  change ∃ z : Lˣ, chapter05NormMap K L z = chapter05NormMap K M y
  refine ⟨chapter05NormMap L M y, ?_⟩
  have h := congrArg (fun f : Mˣ →* Kˣ => f y)
    (chapter05_norm_map_transitive K L M)
  simpa only [MonoidHom.coe_comp, Function.comp_apply] using h.symm

theorem chapter05_norm_limitation
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    [Fintype (Gal(chapter05MaximalAbelianField K L / K))]
    (D : Chapter05LocalClassFormationData K L)
    (DM : Chapter05LocalClassFormationData K
      (chapter05MaximalAbelianField K L)) :
    chapter05NormSubgroup K L =
      chapter05NormSubgroup K (chapter05MaximalAbelianField K L) := by
  have hle := chapter05_norm_subgroup_mono_of_tower
    K (chapter05MaximalAbelianField K L) L
  have hfinite : Finite (chapter05NormQuotient K
      (chapter05MaximalAbelianField K L)) :=
    chapter05FiniteNormQuotient DM
  have hindex_ne : (chapter05NormSubgroup K
      (chapter05MaximalAbelianField K L)).index ≠ 0 :=
    @Subgroup.index_ne_zero_of_finite Kˣ _
      (chapter05NormSubgroup K (chapter05MaximalAbelianField K L)) hfinite
  have hcard : Nat.card (chapter05NormQuotient K L) =
      Nat.card (chapter05NormQuotient K
        (chapter05MaximalAbelianField K L)) := by
    calc
      Nat.card (chapter05NormQuotient K L) =
          Nat.card (chapter05Abelianization (Gal(L / K))) :=
        Nat.card_congr (chapter05FiniteArtinQuotientEquiv D).toEquiv
      _ = Nat.card (Gal(chapter05MaximalAbelianField K L / K)) :=
        (Nat.card_congr
          (chapter05MaximalAbelianSubextension_galoisEquiv K L).toEquiv).symm
      _ = Nat.card (chapter05Abelianization
          (Gal(chapter05MaximalAbelianField K L / K))) :=
        Nat.card_congr (Abelianization.equivOfComm).toEquiv
      _ = Nat.card (chapter05NormQuotient K
          (chapter05MaximalAbelianField K L)) :=
        (Nat.card_congr (chapter05FiniteArtinQuotientEquiv DM).toEquiv).symm
  have hindex : (chapter05NormSubgroup K L).index =
      (chapter05NormSubgroup K
        (chapter05MaximalAbelianField K L)).index := by
    change Nat.card (chapter05NormQuotient K L) =
      Nat.card (chapter05NormQuotient K
        (chapter05MaximalAbelianField K L))
    exact hcard
  have hrel := Subgroup.relIndex_mul_index hle
  have hrel_one : (chapter05NormSubgroup K L).relIndex
      (chapter05NormSubgroup K
        (chapter05MaximalAbelianField K L)) = 1 := by
    apply Nat.eq_of_mul_eq_mul_right
      (Nat.pos_of_ne_zero hindex_ne)
    simpa [hindex] using hrel
  exact le_antisymm hle (Subgroup.relIndex_eq_one.mp hrel_one)

def chapter05NormIndex
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : ℕ :=
  Nat.card (chapter05NormQuotient K L)

theorem chapter05_norm_index_eq_maximal_abelian_degree
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    [Fintype (Gal(chapter05MaximalAbelianField K L / K))]
    (D : Chapter05LocalClassFormationData K L)
    (DM : Chapter05LocalClassFormationData K
      (chapter05MaximalAbelianField K L)) :
    chapter05NormIndex K L =
      Module.finrank K (chapter05MaximalAbelianField K L) := by
  change Nat.card (Kˣ ⧸ chapter05NormSubgroup K L) =
    Module.finrank K (chapter05MaximalAbelianField K L)
  rw [chapter05_norm_limitation K L D DM]
  calc
    Nat.card (chapter05NormQuotient K
        (chapter05MaximalAbelianField K L)) =
        Nat.card (chapter05Abelianization
          (Gal(chapter05MaximalAbelianField K L / K))) :=
      Nat.card_congr (chapter05FiniteArtinQuotientEquiv DM).toEquiv
    _ = Nat.card (Gal(chapter05MaximalAbelianField K L / K)) := by
      exact (Nat.card_congr (Abelianization.equivOfComm).toEquiv).symm
    _ = Module.finrank K (chapter05MaximalAbelianField K L) :=
      chapter05_galois_group_card_eq_degree K
        (chapter05MaximalAbelianField K L)

theorem chapter05_norm_index_eq_abelianization_card
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L) :
    chapter05NormIndex K L =
      Nat.card (chapter05Abelianization (Gal(L / K))) := by
  change Nat.card (chapter05NormQuotient K L) =
    Nat.card (chapter05Abelianization (Gal(L / K)))
  exact Nat.card_congr (chapter05FiniteArtinQuotientEquiv D).toEquiv

theorem chapter05_norm_limitation_index_formula
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    [Fintype (Gal(chapter05MaximalAbelianField K L / K))]
    (D : Chapter05LocalClassFormationData K L)
    (DM : Chapter05LocalClassFormationData K
      (chapter05MaximalAbelianField K L)) :
      Nat.card (chapter05NormQuotient K L) =
        Module.finrank K (chapter05MaximalAbelianField K L) ∧
      Nat.card (chapter05NormQuotient K L) =
        Nat.card (chapter05Abelianization (Gal(L / K))) := by
  constructor
  · simpa [chapter05NormIndex] using
      (chapter05_norm_index_eq_maximal_abelian_degree K L D DM)
  · simpa [chapter05NormIndex] using
      (chapter05_norm_index_eq_abelianization_card K L D)

theorem chapter05_abelian_norm_index_eq_extension_degree
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L) :
    chapter05NormIndex K L = Module.finrank K L := by
  change Nat.card (chapter05NormQuotient K L) = Module.finrank K L
  calc
    Nat.card (chapter05NormQuotient K L) =
        Nat.card (chapter05Abelianization (Gal(L / K))) :=
      Nat.card_congr (chapter05FiniteArtinQuotientEquiv D).toEquiv
    _ = Nat.card (Gal(L / K)) := by
      exact (Nat.card_congr (Abelianization.equivOfComm).toEquiv).symm
    _ = Module.finrank K L := chapter05_galois_group_card_eq_degree K L

/- The following declarations record the nonabelian warning from the source
without pretending that the extension degree is the norm index. -/
abbrev chapter05S3 := Equiv.Perm (Fin 3)

theorem chapter05S3_card : Nat.card chapter05S3 = 6 := by
  simp [chapter05S3, Fintype.card_perm]
  decide

theorem chapter05S3_abelianization_card :
    Nat.card (chapter05Abelianization chapter05S3) = 2 := by
  change (commutator (Equiv.Perm (Fin 3))).index = 2
  have hle : commutator (Equiv.Perm (Fin 3)) ≤
      alternatingGroup (Fin 3) := by
    rw [commutator_eq_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨g, h, rfl⟩
    change Equiv.Perm.sign ⁅g, h⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
  let a : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let b : Equiv.Perm (Fin 3) := Equiv.swap 1 2
  have hmem : ⁅a, b⁆ ∈ commutator (Equiv.Perm (Fin 3)) := by
    change ⁅a, b⁆ ∈ ⁅(⊤ : Subgroup (Equiv.Perm (Fin 3))), ⊤⁆
    exact Subgroup.commutator_mem_commutator trivial trivial
  have hnot : ⁅a, b⁆ ≠ 1 := by
    dsimp [a, b]
    decide
  have hnonbot :
      (commutator (Equiv.Perm (Fin 3))).subgroupOf
        (alternatingGroup (Fin 3)) ≠ ⊥ := by
    intro hbot
    let c : alternatingGroup (Fin 3) := ⟨⁅a, b⁆, hle hmem⟩
    have hc : c ∈ (commutator (Equiv.Perm (Fin 3))).subgroupOf
        (alternatingGroup (Fin 3)) := by
      rw [Subgroup.mem_subgroupOf]
      exact hmem
    have hc0 : c ∈ (⊥ : Subgroup (alternatingGroup (Fin 3))) := hbot ▸ hc
    have hc_eq : c = 1 := by simpa using hc0
    apply hnot
    simpa [c] using congrArg Subtype.val hc_eq
  have hAcard : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  have hprime : Nat.Prime (Nat.card (alternatingGroup (Fin 3))) := by
    rw [hAcard]
    decide
  rcases @Subgroup.eq_bot_or_eq_top_of_prime_card
      (alternatingGroup (Fin 3)) _
      ((commutator (Equiv.Perm (Fin 3))).subgroupOf
        (alternatingGroup (Fin 3))) ⟨hprime⟩ with hbot | htop
  · exact (hnonbot hbot).elim
  · have hcomm : commutator (Equiv.Perm (Fin 3)) =
        alternatingGroup (Fin 3) :=
      le_antisymm hle (Subgroup.subgroupOf_eq_top.mp htop)
    rw [hcomm, alternatingGroup.index_eq_two]

theorem chapter05S3_norm_index_is_not_group_card :
    Nat.card (chapter05Abelianization chapter05S3) ≠ Nat.card chapter05S3 := by
  rw [chapter05S3_abelianization_card, chapter05S3_card]
  decide

theorem chapter05_s3_norm_index_ne_extension_degree
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L)
    (e : Gal(L / K) ≃* chapter05S3) :
    chapter05NormIndex K L ≠ Module.finrank K L := by
  intro h
  have hab : Nat.card (chapter05Abelianization (Gal(L / K))) =
      Nat.card (Gal(L / K)) := by
    calc
      Nat.card (chapter05Abelianization (Gal(L / K))) =
          chapter05NormIndex K L :=
        (chapter05_norm_index_eq_abelianization_card K L D).symm
      _ = Module.finrank K L := h
      _ = Nat.card (Gal(L / K)) :=
        (chapter05_galois_group_card_eq_degree K L).symm
  apply chapter05S3_norm_index_is_not_group_card
  calc
    Nat.card (chapter05Abelianization chapter05S3) =
        Nat.card (chapter05Abelianization (Gal(L / K))) :=
      (Nat.card_congr e.abelianizationCongr.toEquiv).symm
    _ = Nat.card (Gal(L / K)) := hab
    _ = Nat.card chapter05S3 := Nat.card_congr e.toEquiv

/- SOURCE WARNING encoded by the API boundary: the norm-limitation theorem
above has `IsGalois K L`; no corresponding fixed-field equality is asserted
for a merely finite separable non-Galois extension. -/

end

end LastLib.Book05LocalClassFieldTheory.Chapter05
