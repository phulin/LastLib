import LastLib.Book06GlobalClassFieldTheory.Chapter05.Dependencies
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.OpenSubgroup

namespace LastLib.Book06GlobalClassFieldTheory.Chapter05

noncomputable section

open scoped Pointwise

/-! ## 5.3. Compatibility in quotients and towers -/

/-
DEPENDENCY_GUESS: `Chapter05AbelianExtensionNormLattice` is the temporary
book-facing interface for the finite abelian extension lattice and its open
idele norm subgroups.  The reconciled existence/classification API should
replace this interface; its operations are compositum/intersection and its
norm map is the actual idelic norm subgroup.
-/

universe uC uC' uC'' uG uG' uE uUK uUL

/-- The restriction square for two finite abelian levels over the same base. -/
structure Chapter05ArtinRestrictionSquare
    (C : Type uC) (G_L : Type uG) (G_E : Type uG')
    [CommGroup C] [CommGroup G_L] [CommGroup G_E] where
  artinL : C →* G_L
  artinE : C →* G_E
  restriction : G_L →* G_E
  restriction_surjective : Function.Surjective restriction
  commutes : restriction.comp artinL = artinE

theorem chapter05_artin_restriction_square
    {C : Type uC} {G_L : Type uG} {G_E : Type uG'}
    [CommGroup C] [CommGroup G_L] [CommGroup G_E]
    (S : Chapter05ArtinRestrictionSquare C G_L G_E) :
    S.restriction.comp S.artinL = S.artinE := by
  exact S.commutes

theorem chapter05_artin_restriction_kernel_le
    {C : Type uC} {G_L : Type uG} {G_E : Type uG'}
    [CommGroup C] [CommGroup G_L] [CommGroup G_E]
    (S : Chapter05ArtinRestrictionSquare C G_L G_E) :
    S.artinL.ker ≤ S.artinE.ker := by
  exact chapter05_artin_kernel_le_of_factorization
    S.artinL S.artinE S.restriction S.commutes

theorem chapter05_restriction_norm_subgroups_reverse_inclusion
    {C : Type uC} {G_L : Type uG} {G_E : Type uG'}
    [CommGroup C] [CommGroup G_L] [CommGroup G_E]
    (S : Chapter05ArtinRestrictionSquare C G_L G_E)
    (normSubgroupL normSubgroupE : Subgroup C)
    (hL : S.artinL.ker = normSubgroupL)
    (hE : S.artinE.ker = normSubgroupE) :
    normSubgroupL ≤ normSubgroupE := by
  rw [← hL, ← hE]
  exact chapter05_artin_restriction_kernel_le S

/-! Restriction maps in a three-level tower compose as expected. -/
structure Chapter05RestrictionTowerData
    {G_L : Type uG} {G_E : Type uG'} {G_K : Type uG''}
    [CommGroup G_L] [CommGroup G_E] [CommGroup G_K] where
  restrictionLE : G_L →* G_E
  restrictionEK : G_E →* G_K
  restrictionLK : G_L →* G_K
  transitive : restrictionEK.comp restrictionLE = restrictionLK

theorem chapter05_restriction_maps_are_transitive
    {G_L : Type uG} {G_E : Type uG'} {G_K : Type uG''}
    [CommGroup G_L] [CommGroup G_E] [CommGroup G_K]
    (T : Chapter05RestrictionTowerData
      (G_L := G_L) (G_E := G_E) (G_K := G_K)) :
    T.restrictionEK.comp T.restrictionLE = T.restrictionLK := by
  exact T.transitive

/-- The norm maps in a tower of finite extensions. -/
structure Chapter05TowerNormData
    (C_K : Type uC) (C_E : Type uC') (C_L : Type uC'')
    [CommGroup C_K] [CommGroup C_E] [CommGroup C_L] where
  normLE : C_L →* C_E
  normEK : C_E →* C_K
  normLK : C_L →* C_K
  transitive : normEK.comp normLE = normLK
  normSubgroupE : Subgroup C_K
  normSubgroupL : Subgroup C_K
  normSubgroupE_eq_range : normSubgroupE = Subgroup.map normEK ⊤
  normSubgroupL_eq_range : normSubgroupL = Subgroup.map normLK ⊤

theorem chapter05_idele_norms_are_transitive
    {C_K : Type uC} {C_E : Type uC'} {C_L : Type uC''}
    [CommGroup C_K] [CommGroup C_E] [CommGroup C_L]
    (T : Chapter05TowerNormData C_K C_E C_L) :
    T.normEK.comp T.normLE = T.normLK := by
  exact T.transitive

theorem chapter05_tower_norm_subgroups_reverse_inclusion
    {C_K : Type uC} {C_E : Type uC'} {C_L : Type uC''}
    [CommGroup C_K] [CommGroup C_E] [CommGroup C_L]
    (T : Chapter05TowerNormData C_K C_E C_L) :
    T.normSubgroupL ≤ T.normSubgroupE := by
  rw [T.normSubgroupL_eq_range, T.normSubgroupE_eq_range, ← T.transitive]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  exact Subgroup.mem_map_of_mem T.normEK (Subgroup.mem_top _)

/-- The field/norm order interface used by the finite abelian class-field
lattice.  `fieldLe E L` means `E ⊆ L`. -/
structure Chapter05AbelianExtensionNormLattice
    (E : Type uE) (C : Type uC) [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] where
  fieldLe : E → E → Prop
  compositum : E → E → E
  intersection : E → E → E
  normSubgroup : E → Subgroup C
  inclusion_iff_norm_reverse :
    ∀ A B, fieldLe A B ↔ normSubgroup B ≤ normSubgroup A
  compositum_norm_intersection :
    ∀ A B, normSubgroup (compositum A B) = normSubgroup A ⊓ normSubgroup B
  intersection_norm_product :
    ∀ A B, (normSubgroup (intersection A B) : Set C) =
      (normSubgroup A : Set C) * (normSubgroup B : Set C)
  normSubgroup_open : ∀ A, IsOpen (normSubgroup A : Set C)
  normSubgroup_finiteIndex : ∀ A, (normSubgroup A).FiniteIndex

theorem chapter05_norm_subgroups_reverse_inclusion_iff
    {E : Type uE} {C : Type uC} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C]
    (N : Chapter05AbelianExtensionNormLattice E C) (A B : E) :
    N.fieldLe A B ↔ N.normSubgroup B ≤ N.normSubgroup A := by
  exact N.inclusion_iff_norm_reverse A B

theorem chapter05_compositum_norm_subgroup
    {E : Type uE} {C : Type uC} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C]
    (N : Chapter05AbelianExtensionNormLattice E C) (A B : E) :
    N.normSubgroup (N.compositum A B) =
      N.normSubgroup A ⊓ N.normSubgroup B := by
  exact N.compositum_norm_intersection A B

theorem chapter05_intersection_norm_subgroup
    {E : Type uE} {C : Type uC} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C]
    (N : Chapter05AbelianExtensionNormLattice E C) (A B : E) :
    (N.normSubgroup (N.intersection A B) : Set C) =
      (N.normSubgroup A : Set C) * (N.normSubgroup B : Set C) := by
  exact N.intersection_norm_product A B

theorem chapter05_norm_subgroup_product_open
    {E : Type uE} {C : Type uC} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C]
    (N : Chapter05AbelianExtensionNormLattice E C) (A B : E) :
    IsOpen ((N.normSubgroup A : Set C) * (N.normSubgroup B : Set C)) := by
  rw [← N.intersection_norm_product A B]
  exact N.normSubgroup_open (N.intersection A B)

theorem chapter05_norm_subgroup_product_closed
    {E : Type uE} {C : Type uC} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C]
    (N : Chapter05AbelianExtensionNormLattice E C) (A B : E) :
    IsClosed ((N.normSubgroup A : Set C) * (N.normSubgroup B : Set C)) := by
  rw [← N.intersection_norm_product A B]
  exact Subgroup.isClosed_of_isOpen _ (N.normSubgroup_open (N.intersection A B))

/-- The finite-level norm square for an arbitrary extension in a common
separable closure. -/
structure Chapter05NormInclusionArtinSquare
    (C_K : Type uC) (C_L : Type uC') (G_K : Type uG) (G_L : Type uG')
    [CommGroup C_K] [CommGroup C_L] [CommGroup G_K] [CommGroup G_L] where
  artinK : C_K →* G_K
  artinL : C_L →* G_L
  norm : C_L →* C_K
  inclusion : G_L →* G_K
  inclusion_injective : Function.Injective inclusion
  commutes : artinK.comp norm = inclusion.comp artinL

theorem chapter05_norm_corresponds_to_galois_inclusion
    {C_K : Type uC} {C_L : Type uC'} {G_K : Type uG} {G_L : Type uG'}
    [CommGroup C_K] [CommGroup C_L] [CommGroup G_K] [CommGroup G_L]
    (S : Chapter05NormInclusionArtinSquare C_K C_L G_K G_L) :
    S.artinK.comp S.norm = S.inclusion.comp S.artinL := by
  exact S.commutes

/-- A scalar idele map together with the componentwise description above each
base place. -/
structure Chapter05ScalarIdeleInclusion
    (I_K : Type uC) (I_L : Type uC') (V_K : Type uE) (V_L : Type uE)
    (U_K : V_K → Type uUK) (U_L : V_L → Type uUL)
    [CommGroup I_K] [CommGroup I_L] [∀ v, CommGroup (U_K v)]
    [∀ w, CommGroup (U_L w)] where
  basePlace : V_L → V_K
  scalarInclusion : I_K →* I_L
  scalar_inclusion_injective : Function.Injective scalarInclusion
  componentK : ∀ v, I_K →* U_K v
  componentL : ∀ w, I_L →* U_L w
  localScalar : ∀ w, U_K (basePlace w) →* U_L w
  componentwise :
    ∀ x w, componentL w (scalarInclusion x) =
      localScalar w (componentK (basePlace w) x)

theorem chapter05_scalar_idele_componentwise
    {I_K : Type uC} {I_L : Type uC'} {V_K : Type uE} {V_L : Type uE}
    {U_K : V_K → Type uUK} {U_L : V_L → Type uUL}
    [CommGroup I_K] [CommGroup I_L] [∀ v, CommGroup (U_K v)]
    [∀ w, CommGroup (U_L w)]
    (S : Chapter05ScalarIdeleInclusion I_K I_L V_K V_L U_K U_L)
    (x : I_K) (w : V_L) :
    S.componentL w (S.scalarInclusion x) =
      S.localScalar w (S.componentK (S.basePlace w) x) := by
  exact S.componentwise x w

/-- The transfer square in the opposite direction. -/
structure Chapter05ArtinTransferSquare
    (C_K : Type uC) (C_L : Type uC') (G_K : Type uG) (G_L : Type uG')
    [CommGroup C_K] [CommGroup C_L] [CommGroup G_K] [CommGroup G_L] where
  artinK : C_K →* G_K
  artinL : C_L →* G_L
  scalarInclusion : C_K →* C_L
  transfer : G_K →* G_L
  commutes : artinL.comp scalarInclusion = transfer.comp artinK

theorem chapter05_scalar_inclusion_corresponds_to_transfer
    {C_K : Type uC} {C_L : Type uC'} {G_K : Type uG} {G_L : Type uG'}
    [CommGroup C_K] [CommGroup C_L] [CommGroup G_K] [CommGroup G_L]
    (S : Chapter05ArtinTransferSquare C_K C_L G_K G_L) :
    S.artinL.comp S.scalarInclusion = S.transfer.comp S.artinK := by
  exact S.commutes

/-! Transfer maps in a three-level tower compose as expected. -/
structure Chapter05TransferTowerData
    {G_K : Type uG} {G_E : Type uG'} {G_L : Type uG''}
    [CommGroup G_K] [CommGroup G_E] [CommGroup G_L] where
  transferKE : G_K →* G_E
  transferEL : G_E →* G_L
  transferKL : G_K →* G_L
  transitive : transferEL.comp transferKE = transferKL

theorem chapter05_transfer_maps_are_transitive
    {G_K : Type uG} {G_E : Type uG'} {G_L : Type uG''}
    [CommGroup G_K] [CommGroup G_E] [CommGroup G_L]
    (T : Chapter05TransferTowerData
      (G_K := G_K) (G_E := G_E) (G_L := G_L)) :
    T.transferEL.comp T.transferKE = T.transferKL := by
  exact T.transitive

end

end LastLib.Book06GlobalClassFieldTheory.Chapter05
