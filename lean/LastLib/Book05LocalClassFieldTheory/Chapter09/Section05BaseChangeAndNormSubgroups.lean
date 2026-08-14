import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs

import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section07ConcreteFiniteExtensions
import LastLib.Book03RamificationTheory.Chapter05.Section03TowerTransitivity
import LastLib.Book05LocalClassFieldTheory.Chapter09.Dependencies
import LastLib.Book05LocalClassFieldTheory.Chapter09.Section02NormCorrespondsToGaloisInclusion

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
  let e : E →ₐ[K] EL := IsScalarTower.toAlgHom K E EL
  let l : L →ₐ[K] EL := IsScalarTower.toAlgHom K L EL
  let E' : IntermediateField K EL := e.fieldRange
  let L' : IntermediateField K EL := l.fieldRange
  have hE' : FiniteDimensional K E' := by
    dsimp [E']
    exact LinearEquiv.finiteDimensional e.equivFieldRange.toLinearEquiv
  have hL' : FiniteDimensional K L' := by
    dsimp [L']
    exact LinearEquiv.finiteDimensional l.equivFieldRange.toLinearEquiv
  let _ : FiniteDimensional K E' := hE'
  let _ : FiniteDimensional K L' := hL'
  have he : e.range = Algebra.adjoin K (Set.range (algebraMap E EL)) := by
    apply le_antisymm
    · rintro x ⟨y, rfl⟩
      exact Algebra.subset_adjoin ⟨y, rfl⟩
    · exact Algebra.adjoin_le (by
        rintro x ⟨y, rfl⟩
        exact ⟨y, rfl⟩)
  have hl : l.range = Algebra.adjoin K (Set.range (algebraMap L EL)) := by
    apply le_antisymm
    · rintro x ⟨y, rfl⟩
      exact Algebra.subset_adjoin ⟨y, rfl⟩
    · exact Algebra.adjoin_le (by
        rintro x ⟨y, rfl⟩
        exact ⟨y, rfl⟩)
  have hsup : E' ⊔ L' = ⊤ := by
    apply IntermediateField.toSubalgebra_injective
    rw [IntermediateField.sup_toSubalgebra_of_left E' L']
    change e.range ⊔ l.range = ⊤
    rw [he, hl, ← Algebra.adjoin_union]
    exact C.generated
  have htop : FiniteDimensional K (⊤ : IntermediateField K EL) := by
    rw [← hsup]
    infer_instance
  let _ : FiniteDimensional K EL :=
    (IntermediateField.topEquiv (F := K) (E := EL)).toLinearEquiv.finiteDimensional
  exact Module.Finite.of_restrictScalars_finite K L EL

theorem chapter09_compositum_is_abelian
    (K E L EL : Type*) [Field K] [Field E] [Field L] [Field EL]
    [Algebra K E] [Algebra K L] [Algebra E EL] [Algebra L EL]
    [Algebra K EL] [IsScalarTower K E EL] [IsScalarTower K L EL]
    [FiniteDimensional K E] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsAbelianGalois K E]
    (C : Chapter09Compositum K E L EL) :
    IsAbelianGalois L EL := by
  let e : E →ₐ[K] EL := IsScalarTower.toAlgHom K E EL
  let l : L →ₐ[K] EL := IsScalarTower.toAlgHom K L EL
  let E' : IntermediateField K EL := e.fieldRange
  let L' : IntermediateField K EL := l.fieldRange
  have hE' : FiniteDimensional K E' := by
    dsimp [E']
    exact LinearEquiv.finiteDimensional e.equivFieldRange.toLinearEquiv
  have hL' : FiniteDimensional K L' := by
    dsimp [L']
    exact LinearEquiv.finiteDimensional l.equivFieldRange.toLinearEquiv
  have hsup : E' ⊔ L' = ⊤ := by
    let _ : FiniteDimensional K E' := hE'
    let _ : FiniteDimensional K L' := hL'
    have he : e.range = Algebra.adjoin K (Set.range (algebraMap E EL)) := by
      apply le_antisymm
      · rintro x ⟨y, rfl⟩
        exact Algebra.subset_adjoin ⟨y, rfl⟩
      · exact Algebra.adjoin_le (by
          rintro x ⟨y, rfl⟩
          exact ⟨y, rfl⟩)
    have hl : l.range = Algebra.adjoin K (Set.range (algebraMap L EL)) := by
      apply le_antisymm
      · rintro x ⟨y, rfl⟩
        exact Algebra.subset_adjoin ⟨y, rfl⟩
      · exact Algebra.adjoin_le (by
          rintro x ⟨y, rfl⟩
          exact ⟨y, rfl⟩)
    apply IntermediateField.toSubalgebra_injective
    rw [IntermediateField.sup_toSubalgebra_of_left E' L']
    change e.range ⊔ l.range = ⊤
    rw [he, hl, ← Algebra.adjoin_union]
    exact C.generated
  have hAE' : IsAbelianGalois K E' :=
    IsAbelianGalois.of_algHom e.equivFieldRange.symm.toAlgHom
  let _ : IsAbelianGalois K E' := hAE'
  have hcommE (a b : Gal(E' / K)) : a * b = b * a :=
    hAE'.is_comm.comm a b
  have hG : IsGalois L' EL :=
    IsGalois.sup_right E' L' hsup
  have hf : Function.Injective
      (IntermediateField.restrictRestrictAlgEquivMapHom K E' L' EL) :=
    IntermediateField.restrictRestrictAlgEquivMapHom_injective E' L' hsup
  have hcomm' (σ τ : Gal(EL / L')) : σ * τ = τ * σ := by
    apply hf
    simpa only [map_mul] using
      hcommE
        ((IntermediateField.restrictRestrictAlgEquivMapHom K E' L' EL) σ)
        ((IntermediateField.restrictRestrictAlgEquivMapHom K E' L' EL) τ)
  have hAb' : IsAbelianGalois L' EL := by
    exact { toIsGalois := hG, is_comm := ⟨hcomm'⟩ }
  let eL : L ≃ₐ[K] L' := l.equivFieldRange
  have heL_apply (y : L) : (eL y : EL) = algebraMap L EL y := by
    rfl
  let t : Gal(EL / L) →* Gal(EL / L') :=
    { toFun := fun σ =>
        { σ with
          commutes' := by
            intro x
            obtain ⟨y, hy⟩ := x.property
            have hx : algebraMap L' EL x = algebraMap L EL y := by
              calc
                algebraMap L' EL x = (x : EL) := rfl
                _ = l y := hy.symm
                _ = algebraMap L EL y := by rfl
            rw [hx]
            exact σ.commutes y }
      map_one' := by rfl
      map_mul' := by intro σ τ; rfl }
  have ht : Function.Injective t := by
    intro σ τ h
    apply AlgEquiv.ext
    intro x
    have hx := congrArg (fun ρ : Gal(EL / L') => ρ x) h
    change σ x = τ x at hx
    exact hx
  have hcomm (σ τ : Gal(EL / L)) : σ * τ = τ * σ := by
    apply ht
    simpa only [map_mul] using hAb'.is_comm.comm (t σ) (t τ)
  have hcomp :
      (algebraMap L EL).comp eL.symm.toRingHom =
        (RingHom.id EL).comp (algebraMap L' EL) := by
    ext x
    change algebraMap L EL (eL.symm x) = (x : EL)
    calc
      algebraMap L EL (eL.symm x) = (eL (eL.symm x) : EL) :=
        (heL_apply (eL.symm x)).symm
      _ = (x : EL) := congrArg (fun z : L' => (z : EL)) (eL.apply_symm_apply x)
  have hG_L : IsGalois L EL := by
    let _ : IsGalois L' EL := hG
    exact IsGalois.of_equiv_equiv (f := eL.symm.toRingEquiv)
      (g := RingEquiv.refl EL) hcomp
  exact { toIsGalois := hG_L, is_comm := ⟨hcomm⟩ }

/-- The finite reciprocity character supplied by a quotient equivalence. -/
def chapter09ReciprocityCharacter
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (R : Chapter09FiniteAbelianReciprocity K L) :
  Kˣ →* Gal(L / K) :=
  R.quotientEquiv.toMonoidHom.comp
    (QuotientGroup.mk' (chapter09NormSubgroup K L))

theorem chapter09ReciprocityCharacter_ker
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (R : Chapter09FiniteAbelianReciprocity K L) :
    (chapter09ReciprocityCharacter K L R).ker = chapter09NormSubgroup K L := by
  change (R.quotientEquiv.toMonoidHom.comp
    (QuotientGroup.mk'
      (LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05NormSubgroup K L))).ker = _
  calc
    _ = (QuotientGroup.mk'
      (LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05NormSubgroup K L)).ker := by
      apply MonoidHom.ker_comp_of_injective
      exact R.quotientEquiv.injective
    _ = _ := QuotientGroup.ker_mk' _

/-!
The restriction of automorphisms of `EL/L` to `E` is represented as an
injective homomorphism into `Gal(E/K)`.  This direction is intentional: the
abstract abelianization of `Gal(EL/L)` is not treated as a subgroup of the
abelianization of an absolute Galois group.
-/

/- LOCAL_DEPENDENCY_GUESS: the preceding Galois API supplies the restriction
embedding from the compositum extension to `E/K`. -/
structure Chapter09BaseChangeData
    (K E L EL : Type) [Field K] [Field E] [Field L] [Field EL]
    [Algebra K E] [Algebra K L] [Algebra E EL] [Algebra L EL]
    [Algebra K EL] [IsScalarTower K E EL] [IsScalarTower K L EL]
    [FiniteDimensional K E] [FiniteDimensional K L] [FiniteDimensional L EL]
    [Algebra.IsSeparable K L] [IsAbelianGalois K E]
    [IsAbelianGalois L EL] where
  compositum : Chapter09Compositum K E L EL
  reciprocity_E : Chapter09FiniteAbelianReciprocity K E
  reciprocity_EL : Chapter09FiniteAbelianReciprocity L EL
  restrictionEmbedding : Gal(EL / L) →* Gal(E / K)
  /-- The chosen embedding of `EL/L` automorphisms is the actual restriction
      to the `E`-factor of the compositum.  Without this field an arbitrary
      injective homomorphism into `Gal(E/K)` could be supplied instead. -/
  restrictionEmbedding_spec :
    ∀ (σ : Gal(EL / L)) (x : E),
      algebraMap E EL (restrictionEmbedding σ x) =
        σ (algebraMap E EL x)
  restrictionEmbedding_injective : Function.Injective restrictionEmbedding

/- The common normalized reciprocity system in the theorem below ties the two
  finite characters to actual restriction maps in one separable closure. -/

theorem chapter09_base_change_character_compatibility
    (K E L EL : Type) [Field K] [Field E] [Field L] [Field EL]
    [Algebra K E] [Algebra K L] [Algebra E EL] [Algebra L EL]
    [Algebra K EL] [IsScalarTower K E EL] [IsScalarTower K L EL]
    [FiniteDimensional K E] [FiniteDimensional K L] [FiniteDimensional L EL]
    [Algebra.IsSeparable K L] [IsAbelianGalois K E] [IsAbelianGalois L EL]
    (Ks : Type) [Field Ks]
    [Algebra K Ks] [Algebra L Ks] [Algebra E Ks] [Algebra EL Ks]
    [IsScalarTower K L Ks] [IsScalarTower L EL Ks]
    [IsScalarTower K E Ks] [IsScalarTower E EL Ks]
    (T : Chapter09FiniteSeparableExtension K L Ks)
    (R : Chapter09ReciprocitySystem K L Ks T)
    (D : Chapter09BaseChangeData K E L EL) :
    D.restrictionEmbedding.comp
        (chapter09ReciprocityCharacter L EL D.reciprocity_EL) =
      (chapter09ReciprocityCharacter K E D.reciprocity_E).comp
        (chapter09NormHom K L) := by
  sorry

theorem chapter09_base_change_character_compatibility_apply
    (K E L EL : Type) [Field K] [Field E] [Field L] [Field EL]
    [Algebra K E] [Algebra K L] [Algebra E EL] [Algebra L EL]
    [Algebra K EL] [IsScalarTower K E EL] [IsScalarTower K L EL]
    [FiniteDimensional K E] [FiniteDimensional K L] [FiniteDimensional L EL]
    [Algebra.IsSeparable K L] [IsAbelianGalois K E] [IsAbelianGalois L EL]
    (Ks : Type) [Field Ks]
    [Algebra K Ks] [Algebra L Ks] [Algebra E Ks] [Algebra EL Ks]
    [IsScalarTower K L Ks] [IsScalarTower L EL Ks]
    [IsScalarTower K E Ks] [IsScalarTower E EL Ks]
    (T : Chapter09FiniteSeparableExtension K L Ks)
    (R : Chapter09ReciprocitySystem K L Ks T)
    (D : Chapter09BaseChangeData K E L EL) (x : Lˣ) :
    D.restrictionEmbedding
        (chapter09ReciprocityCharacter L EL D.reciprocity_EL x) =
      chapter09ReciprocityCharacter K E D.reciprocity_E
        (chapter09NormHom K L x) := by
  simpa only [MonoidHom.comp_apply] using
    DFunLike.congr_fun
      (chapter09_base_change_character_compatibility K E L EL Ks T R D) x

/-- The norm subgroup of the compositum extension is the reciprocity kernel. -/
theorem chapter09_base_change_normSubgroup_eq_reciprocity_kernel
    (K E L EL : Type) [Field K] [Field E] [Field L] [Field EL]
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
    (K E L : Type) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L]
    [FiniteDimensional K E] [FiniteDimensional K L] :
    Subgroup Lˣ :=
  (chapter09NormSubgroup K E).comap (chapter09NormHom K L)

theorem chapter09_base_change_normSubgroup_eq_norm_comap
    (K E L EL : Type) [Field K] [Field E] [Field L] [Field EL]
    [Algebra K E] [Algebra K L] [Algebra E EL] [Algebra L EL]
    [Algebra K EL] [IsScalarTower K E EL] [IsScalarTower K L EL]
    [FiniteDimensional K E] [FiniteDimensional K L] [FiniteDimensional L EL]
    [Algebra.IsSeparable K L] [IsAbelianGalois K E] [IsAbelianGalois L EL]
    (Ks : Type) [Field Ks]
    [Algebra K Ks] [Algebra L Ks] [Algebra E Ks] [Algebra EL Ks]
    [IsScalarTower K L Ks] [IsScalarTower L EL Ks]
    [IsScalarTower K E Ks] [IsScalarTower E EL Ks]
    (T : Chapter09FiniteSeparableExtension K L Ks)
    (R : Chapter09ReciprocitySystem K L Ks T)
    (D : Chapter09BaseChangeData K E L EL) :
    chapter09NormSubgroup L EL =
      chapter09BaseChangeNormSubgroup K E L := by
  sorry

theorem chapter09_base_change_norm_mem_iff
    (K E L EL : Type) [Field K] [Field E] [Field L] [Field EL]
    [Algebra K E] [Algebra K L] [Algebra E EL] [Algebra L EL]
    [Algebra K EL] [IsScalarTower K E EL] [IsScalarTower K L EL]
    [FiniteDimensional K E] [FiniteDimensional K L] [FiniteDimensional L EL]
    [Algebra.IsSeparable K L] [IsAbelianGalois K E] [IsAbelianGalois L EL]
    (Ks : Type) [Field Ks]
    [Algebra K Ks] [Algebra L Ks] [Algebra E Ks] [Algebra EL Ks]
    [IsScalarTower K L Ks] [IsScalarTower L EL Ks]
    [IsScalarTower K E Ks] [IsScalarTower E EL Ks]
    (T : Chapter09FiniteSeparableExtension K L Ks)
    (R : Chapter09ReciprocitySystem K L Ks T)
    (D : Chapter09BaseChangeData K E L EL) (x : Lˣ) :
    x ∈ chapter09NormSubgroup L EL ↔
      chapter09NormHom K L x ∈ chapter09NormSubgroup K E := by
  rw [chapter09_base_change_normSubgroup_eq_norm_comap K E L EL Ks T R D]
  rfl

/-!
The final ramification paragraph uses the earlier finite-extension profile and
Herbrand interfaces.  The profile records the invariant compatibilities that
an unramified base-change theorem supplies; the resulting total-ramification
statement is then independent of any special case split in the reciprocity
diagrams.
-/

/- The earlier concrete-extension API keeps both the field square and the
profile realizations together; the theorem below consumes that canonical data
directly instead of replacing it by a numerical proposition. -/

theorem chapter09_total_ramification_preserved_under_unramified_base_change
    {K L K' L' ΓK ΓL ΓK' ΓL' : Type*}
    [Field K] [Field L] [Field K'] [Field L']
    [Algebra K L] [Algebra K K'] [Algebra K L']
    [Algebra L L'] [Algebra K' L']
    [IsScalarTower K L L'] [IsScalarTower K K' L']
    [FiniteDimensional K L] [FiniteDimensional K K']
    [FiniteDimensional K' L'] [FiniteDimensional L L']
    [Algebra.IsSeparable K K'] [Algebra.IsSeparable K L]
    [Algebra.IsSeparable K' L']
    [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓL]
    [LinearOrderedCommGroupWithZero ΓK']
    [LinearOrderedCommGroupWithZero ΓL']
    (vK : Valuation K ΓK) (vL : Valuation L ΓL)
    (vK' : Valuation K' ΓK') (vL' : Valuation L' ΓL')
    (hL : vK.IsEquiv (vL.comap (algebraMap K L)))
    (hK' : vK.IsEquiv (vK'.comap (algebraMap K K')))
    (hL' : vK'.IsEquiv (vL'.comap (algebraMap K' L')))
    (hLL' : vL.IsEquiv (vL'.comap (algebraMap L L')))
    (D :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10UnramifiedBaseChangeData
        vK vL vK' vL' hL hK' hL' hLL')
    (htotal :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10TotallyRamified
        D.extensionProfile) :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10TotallyRamified
      D.changedProfile := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_total_ramification_preserved_under_unramified_base_change
    D.baseProfile D.extensionProfile D.changedProfile
    (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_unramified_base_change_profile_of_data
      vK vL vK' vL' hL hK' hL' hLL' D htotal)
    htotal

/- The Herbrand tower is the field/profile realization for the ramification
part: `T.quotientSetup.local_field_realization` retains the actual valued
fields, extensions, and orbit-polynomial data.  The result below consumes that
setup through the canonical Chapter 3 tower theorem rather than adding a
second numerical Herbrand profile. -/
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
  constructor
  · rintro ⟨z, hz⟩
    refine QuotientGroup.induction_on z ?_ hz
    intro y hy
    exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨Abelianization.of y, hy⟩

end

end LastLib.Book05LocalClassFieldTheory.Chapter09
