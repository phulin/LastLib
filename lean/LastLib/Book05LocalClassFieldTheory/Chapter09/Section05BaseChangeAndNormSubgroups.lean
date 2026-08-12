import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.GroupTheory.QuotientGroup.Defs

import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section07ConcreteFiniteExtensions
import LastLib.Book03RamificationTheory.Chapter05.Section03TowerTransitivity
import LastLib.Book05LocalClassFieldTheory.Chapter09.Dependencies

namespace LastLib.Book05LocalClassFieldTheory.Chapter09

noncomputable section

/-!
## 9.5 Base change and norm subgroups
-/

/-!
The following record expresses that `EL` is the compositum of `E` and `L`
inside the chosen overfield.  Its generated-subalgebra field is the universal
field-theoretic content needed by the base-change statements; it does not
assume any norm or reciprocity conclusion.
-/

structure Chapter09Compositum
    (K E L EL : Type*) [Field K] [Field E] [Field L] [Field EL]
    [Algebra K E] [Algebra K L] [Algebra E EL] [Algebra L EL]
    [Algebra K EL] [IsScalarTower K E EL] [IsScalarTower K L EL] where
  generated :
    Algebra.adjoin K
        (Set.range (algebraMap E EL) ∪ Set.range (algebraMap L EL)) = ⊤

/- LOCAL_DEPENDENCY_GUESS: the preceding finite-extension API supplies the
standard finiteness and abelian-compositum theorems for this generated field. -/
theorem chapter09_compositum_finite_over_L
    (K E L EL : Type*) [Field K] [Field E] [Field L] [Field EL]
    [Algebra K E] [Algebra K L] [Algebra E EL] [Algebra L EL]
    [Algebra K EL] [IsScalarTower K E EL] [IsScalarTower K L EL]
    [FiniteDimensional K E] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsAbelianGalois K E]
    (C : Chapter09Compositum K E L EL) :
    FiniteDimensional L EL := by
  sorry

theorem chapter09_compositum_is_abelian
    (K E L EL : Type*) [Field K] [Field E] [Field L] [Field EL]
    [Algebra K E] [Algebra K L] [Algebra E EL] [Algebra L EL]
    [Algebra K EL] [IsScalarTower K E EL] [IsScalarTower K L EL]
    [FiniteDimensional K E] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsAbelianGalois K E]
    (C : Chapter09Compositum K E L EL) :
    IsAbelianGalois L EL := by
  sorry

/-- The finite reciprocity character supplied by a quotient equivalence. -/
def chapter09ReciprocityCharacter
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (R : Chapter09FiniteAbelianReciprocity K L) :
    Kˣ →* Gal(L / K) :=
  R.quotientEquiv.toMonoidHom.comp
    (QuotientGroup.mk' (chapter09NormSubgroup K L))

theorem chapter09ReciprocityCharacter_ker
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (R : Chapter09FiniteAbelianReciprocity K L) :
    (chapter09ReciprocityCharacter K L R).ker = chapter09NormSubgroup K L := by
  sorry

/-!
The restriction of automorphisms of `EL/L` to `E` is represented as an
injective homomorphism into `Gal(E/K)`.  This direction is intentional: the
abstract abelianization of `Gal(EL/L)` is not treated as a subgroup of the
abelianization of an absolute Galois group.
-/

/- LOCAL_DEPENDENCY_GUESS: the preceding Galois API supplies the restriction
embedding from the compositum extension to `E/K`. -/
structure Chapter09BaseChangeData
    (K E L EL : Type*) [Field K] [Field E] [Field L] [Field EL]
    [Algebra K E] [Algebra K L] [Algebra E EL] [Algebra L EL]
    [Algebra K EL] [IsScalarTower K E EL] [IsScalarTower K L EL]
    [FiniteDimensional K E] [FiniteDimensional K L] [FiniteDimensional L EL]
    [Algebra.IsSeparable K L] [IsAbelianGalois K E]
    [IsAbelianGalois L EL] where
  compositum : Chapter09Compositum K E L EL
  reciprocity_E : Chapter09FiniteAbelianReciprocity K E
  reciprocity_EL : Chapter09FiniteAbelianReciprocity L EL
  restrictionEmbedding : Gal(EL / L) →* Gal(E / K)
  restrictionEmbedding_injective : Function.Injective restrictionEmbedding

theorem chapter09_base_change_character_compatibility
    (K E L EL : Type*) [Field K] [Field E] [Field L] [Field EL]
    [Algebra K E] [Algebra K L] [Algebra E EL] [Algebra L EL]
    [Algebra K EL] [IsScalarTower K E EL] [IsScalarTower K L EL]
    [FiniteDimensional K E] [FiniteDimensional K L] [FiniteDimensional L EL]
    [Algebra.IsSeparable K L] [IsAbelianGalois K E] [IsAbelianGalois L EL]
    (D : Chapter09BaseChangeData K E L EL) :
    D.restrictionEmbedding.comp
        (chapter09ReciprocityCharacter L EL D.reciprocity_EL) =
      (chapter09ReciprocityCharacter K E D.reciprocity_E).comp
        (chapter09NormHom K L) := by
  sorry

theorem chapter09_base_change_character_compatibility_apply
    (K E L EL : Type*) [Field K] [Field E] [Field L] [Field EL]
    [Algebra K E] [Algebra K L] [Algebra E EL] [Algebra L EL]
    [Algebra K EL] [IsScalarTower K E EL] [IsScalarTower K L EL]
    [FiniteDimensional K E] [FiniteDimensional K L] [FiniteDimensional L EL]
    [Algebra.IsSeparable K L] [IsAbelianGalois K E] [IsAbelianGalois L EL]
    (D : Chapter09BaseChangeData K E L EL) (x : Lˣ) :
    D.restrictionEmbedding
        (chapter09ReciprocityCharacter L EL D.reciprocity_EL x) =
      chapter09ReciprocityCharacter K E D.reciprocity_E
        (chapter09NormHom K L x) := by
  simpa only [MonoidHom.comp_apply] using
    DFunLike.congr_fun (chapter09_base_change_character_compatibility K E L EL D) x

/-- The norm subgroup of the compositum extension is the reciprocity kernel. -/
theorem chapter09_base_change_normSubgroup_eq_reciprocity_kernel
    (K E L EL : Type*) [Field K] [Field E] [Field L] [Field EL]
    [Algebra K E] [Algebra K L] [Algebra E EL] [Algebra L EL]
    [Algebra K EL] [IsScalarTower K E EL] [IsScalarTower K L EL]
    [FiniteDimensional K E] [FiniteDimensional K L] [FiniteDimensional L EL]
    [Algebra.IsSeparable K L] [IsAbelianGalois K E] [IsAbelianGalois L EL]
    (D : Chapter09BaseChangeData K E L EL) :
    chapter09NormSubgroup L EL =
      (chapter09ReciprocityCharacter L EL D.reciprocity_EL).ker := by
  exact (chapter09ReciprocityCharacter_ker L EL D.reciprocity_EL).symm

/-- The base-change norm subgroup as an inverse image under the old field norm. -/
def chapter09BaseChangeNormSubgroup
    (K E L : Type*) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L]
    [FiniteDimensional K E] [FiniteDimensional K L] :
    Subgroup Lˣ :=
  (chapter09NormSubgroup K E).comap (chapter09NormHom K L)

theorem chapter09_base_change_normSubgroup_eq_norm_comap
    (K E L EL : Type*) [Field K] [Field E] [Field L] [Field EL]
    [Algebra K E] [Algebra K L] [Algebra E EL] [Algebra L EL]
    [Algebra K EL] [IsScalarTower K E EL] [IsScalarTower K L EL]
    [FiniteDimensional K E] [FiniteDimensional K L] [FiniteDimensional L EL]
    [Algebra.IsSeparable K L] [IsAbelianGalois K E] [IsAbelianGalois L EL]
    (D : Chapter09BaseChangeData K E L EL) :
    chapter09NormSubgroup L EL =
      chapter09BaseChangeNormSubgroup K E L := by
  sorry

theorem chapter09_base_change_norm_mem_iff
    (K E L EL : Type*) [Field K] [Field E] [Field L] [Field EL]
    [Algebra K E] [Algebra K L] [Algebra E EL] [Algebra L EL]
    [Algebra K EL] [IsScalarTower K E EL] [IsScalarTower K L EL]
    [FiniteDimensional K E] [FiniteDimensional K L] [FiniteDimensional L EL]
    [Algebra.IsSeparable K L] [IsAbelianGalois K E] [IsAbelianGalois L EL]
    (D : Chapter09BaseChangeData K E L EL) (x : Lˣ) :
    x ∈ chapter09NormSubgroup L EL ↔
      chapter09NormHom K L x ∈ chapter09NormSubgroup K E := by
  rw [chapter09_base_change_normSubgroup_eq_norm_comap K E L EL D]
  rfl

/-!
The final ramification paragraph uses the earlier finite-extension profile and
Herbrand interfaces.  The profile records the invariant compatibilities that
an unramified base-change theorem supplies; the resulting total-ramification
statement is then independent of any special case split in the reciprocity
diagrams.
-/

/- LOCAL_DEPENDENCY_GUESS: the preceding local-field chapters supply the
invariant profile of an unramified base change. -/
def chapter09UnramifiedBaseChangeProfile
    (base p p' :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10FiniteExtensionProfile) :
    Prop :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10Unramified base ∧
    p'.degree = p.degree ∧
    p'.ramificationIndex = p.ramificationIndex ∧
    p'.residueDegree = p.residueDegree

theorem chapter09_total_ramification_preserved_under_unramified_base_change
    (base p p' :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10FiniteExtensionProfile)
    (hbase : chapter09UnramifiedBaseChangeProfile base p p')
    (htotal :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10TotallyRamified p) :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10TotallyRamified p' := by
  rcases hbase with ⟨_, hdegree, hramification, hresidue⟩
  rcases htotal with ⟨htotal_ramification, htotal_residue⟩
  exact ⟨by simpa [hdegree, hramification] using htotal_ramification,
    hresidue.trans htotal_residue⟩

theorem chapter09_herbrand_reindexing_compatibility
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (T : LastLib.Book03RamificationTheory.Chapter05.Chapter05HerbrandTowerSetup G H)
    (hLK : Function.Bijective
      (LastLib.Book03RamificationTheory.Chapter05.chapter05HerbrandFunction
        T.quotientSetup.upstairs))
    (hLM : Function.Bijective
      (LastLib.Book03RamificationTheory.Chapter05.chapter05HerbrandFunction
        T.subextension))
    (hMK : Function.Bijective
      (LastLib.Book03RamificationTheory.Chapter05.chapter05HerbrandFunction
        T.quotientSetup.downstairs))
    {u : ℝ} (hu : (-1 : ℝ) ≤ u) :
    LastLib.Book03RamificationTheory.Chapter05.chapter05HerbrandFunction
        T.quotientSetup.upstairs u =
      LastLib.Book03RamificationTheory.Chapter05.chapter05HerbrandFunction
        T.quotientSetup.downstairs
          (LastLib.Book03RamificationTheory.Chapter05.chapter05HerbrandFunction
            T.subextension u) := by
  exact LastLib.Book03RamificationTheory.Chapter05.chapter05_herbrand_tower_transitivity
    H T hLK hLM hMK hu

theorem chapter09_upper_ramification_quotient_compatibility
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (S : LastLib.Book03RamificationTheory.Chapter05.Chapter05QuotientRamificationSetup G H)
    (hup : Function.Bijective
      (LastLib.Book03RamificationTheory.Chapter05.chapter05HerbrandFunction S.upstairs))
    (hdown : Function.Bijective
      (LastLib.Book03RamificationTheory.Chapter05.chapter05HerbrandFunction S.downstairs))
    {v : ℝ} (hv : (-1 : ℝ) ≤ v) :
    LastLib.Book03RamificationTheory.Chapter05.chapter05UpperRamificationGroup
        S.downstairs v =
      LastLib.Book03RamificationTheory.Chapter05.chapter05UpperQuotientImage H S.upstairs v := by
  exact LastLib.Book03RamificationTheory.Chapter05.chapter05_herbrand_quotient_theorem
    H S hup hdown hv

/-!
The following generic image/preimage interface records the final warning in
the source: an image inside an abelianization is a range of the induced map;
it is not a coercion of the abstract abelianization of the source group into
the target abelianization.
-/

def chapter09AbelianizedImage
    {H G : Type*} [Group H] [Group G] (f : H →* G) :
    Subgroup (Abelianization G) :=
  (Abelianization.map f).range

def chapter09ReciprocityPreimageOfAbelianizedImage
    {K H G : Type*} [Group H] [Group G] [CommGroup K]
    (rec : K →* Abelianization G) (f : H →* G) : Subgroup K :=
  (chapter09AbelianizedImage f).comap rec

theorem chapter09_mem_reciprocityPreimageOfAbelianizedImage_iff
    {K H G : Type*} [Group H] [Group G] [CommGroup K]
    (rec : K →* Abelianization G) (f : H →* G) (x : K) :
    x ∈ chapter09ReciprocityPreimageOfAbelianizedImage rec f ↔
      ∃ z : Abelianization H, Abelianization.map f z = rec x := by
  rfl

theorem chapter09_mem_reciprocityPreimageOfAbelianizedImage_of_group_element_iff
    {K H G : Type*} [Group H] [Group G] [CommGroup K]
    (rec : K →* Abelianization G) (f : H →* G) (x : K) :
    x ∈ chapter09ReciprocityPreimageOfAbelianizedImage rec f ↔
      ∃ y : H, Abelianization.map f (Abelianization.of y) = rec x := by
  sorry

end

end LastLib.Book05LocalClassFieldTheory.Chapter09
