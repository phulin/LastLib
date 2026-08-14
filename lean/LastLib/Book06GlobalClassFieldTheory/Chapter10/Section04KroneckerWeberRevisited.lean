import LastLib.Book06GlobalClassFieldTheory.Chapter10.Dependencies
import LastLib.Book06GlobalClassFieldTheory.Chapter10.Section02ConnectedComponentOfTheIdeleClassGroup
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois

namespace LastLib.Book06GlobalClassFieldTheory.Chapter10

noncomputable section

open CategoryTheory
open Opposite

universe u v

/-!
## 10.4. Kronecker--Weber revisited
-/

/- LOCAL_DEPENDENCY_GUESS: the roots of unity in a chosen abelian closure are
the canonical cyclotomic generators. -/
structure Chapter10CyclotomicTowerData
    (Qab : Type u) [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab] where
  rootOfUnity : Chapter10PositiveNatural → Qab
  primitive_root : ∀ m, IsPrimitiveRoot (rootOfUnity m) m.1
  /-- The chosen primitive roots form a compatible cyclotomic tower. -/
  rootOfUnity_compat :
    ∀ {m n : Chapter10PositiveNatural}, n.1 ∣ m.1 →
      rootOfUnity m ^ (m.1 / n.1) = rootOfUnity n

namespace Chapter10CyclotomicTowerData

variable {Qab : Type u} [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab]

/-- The finite Galois field denoted by `ℚ(ζ_m)` in the chosen closure. -/
noncomputable def cyclotomicField
    (D : Chapter10CyclotomicTowerData Qab)
    (m : Chapter10PositiveNatural) :
    FiniteGaloisIntermediateField ℚ Qab :=
  FiniteGaloisIntermediateField.adjoin ℚ {D.rootOfUnity m}

theorem rootOfUnity_mem_cyclotomicField
    (D : Chapter10CyclotomicTowerData Qab)
    (m : Chapter10PositiveNatural) :
    D.rootOfUnity m ∈ (D.cyclotomicField m).toIntermediateField := by
  exact FiniteGaloisIntermediateField.subset_adjoin ℚ _ (by simp)

/- The compatibility of the selected roots also makes the generated fields a
cofinal directed tower, rather than merely a family of unrelated finite
extensions. -/
theorem cyclotomicField_mono_of_dvd
    (D : Chapter10CyclotomicTowerData Qab)
    {m n : Chapter10PositiveNatural} (h : n.1 ∣ m.1) :
    D.cyclotomicField n ≤ D.cyclotomicField m := by
  apply FiniteGaloisIntermediateField.adjoin_simple_le_iff.mpr
  rw [← D.rootOfUnity_compat h]
  exact pow_mem (D.rootOfUnity_mem_cyclotomicField m) _

end Chapter10CyclotomicTowerData

noncomputable def chapter10CyclotomicProfiniteFunctor :
    Chapter10PositiveNaturalᵒᵖ ⥤ ProfiniteGrp :=
  chapter10CyclotomicUnitFunctor ⋙ forget₂ FiniteGrp ProfiniteGrp

noncomputable def chapter10CyclotomicCoordinate
    (m : Chapter10PositiveNatural) :
    (chapter10CyclotomicProfiniteFunctor.obj (Opposite.op m) : Type) ≃*
      (ZMod m.1)ˣ := by
  change (ZMod m.1)ˣ ≃* (ZMod m.1)ˣ
  exact MulEquiv.refl _

structure Chapter10KroneckerWeberData
    (Qab : Type u) [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab] where
  closure : Chapter10AbelianClosureData ℚ Qab
  cyclotomic : Chapter10CyclotomicTowerData Qab
  /-- Every finite abelian subextension is contained in a selected
    cyclotomic field. -/
  cyclotomic_cofinal :
    ∀ (L : FiniteGaloisIntermediateField ℚ Qab),
      chapter10IsAbelianFiniteGaloisExtension L →
        ∃ m, L ≤ cyclotomic.cyclotomicField m
  complexConjugation : Gal(Qab / ℚ)
  complexConjugation_on_roots :
    ∀ m, complexConjugation (cyclotomic.rootOfUnity m) =
      (cyclotomic.rootOfUnity m)⁻¹

/- The inverse-limit identification must remember which coordinates encode the
  action on the selected roots.  An arbitrary topological group equivalence
  with the same target is not enough for the later root-action statements. -/
noncomputable def chapter10CyclotomicExponentOf
    {Qab : Type u} [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab]
    (e : Gal(Qab / ℚ) ≃ₜ* chapter10CyclotomicUnitInverseLimit)
    (σ : Gal(Qab / ℚ)) (m : Chapter10PositiveNatural) : ℕ := by
  let _ : NeZero m.1 := ⟨Nat.ne_of_gt m.2⟩
  exact ((chapter10CyclotomicCoordinate m
    ((e σ).val (Opposite.op m)) : (ZMod m.1)ˣ) : ZMod m.1).val

/- This is the action-compatible form of the cyclotomic inverse-limit
  theorem.  The compatibility is part of the interface because it is needed
  to interpret the coordinates, not merely to identify the abstract groups. -/
structure Chapter10CyclotomicGaloisUnitAction
    {Qab : Type u} [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab]
    (D : Chapter10KroneckerWeberData Qab) where
  equiv : Gal(Qab / ℚ) ≃ₜ* chapter10CyclotomicUnitInverseLimit
  root_action : ∀ (σ : Gal(Qab / ℚ)) (m : Chapter10PositiveNatural),
    σ (D.cyclotomic.rootOfUnity m) =
      D.cyclotomic.rootOfUnity m ^ chapter10CyclotomicExponentOf equiv σ m

def chapter10CyclotomicFieldUnion
    {Qab : Type u} [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab]
    (D : Chapter10CyclotomicTowerData Qab) : Set Qab :=
  {x | ∃ m, x ∈ (D.cyclotomicField m).toIntermediateField}

private theorem chapter10CyclotomicField_eq_adjoin
    {Qab : Type u} [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab]
    (D : Chapter10CyclotomicTowerData Qab) (m : Chapter10PositiveNatural) :
    (D.cyclotomicField m).toIntermediateField =
      IntermediateField.adjoin ℚ {D.rootOfUnity m} := by
  let _ : NeZero m.1 := ⟨Nat.ne_of_gt m.2⟩
  let _ : Algebra ℚ (IntermediateField.adjoin ℚ {D.rootOfUnity m}) :=
    (IntermediateField.adjoin ℚ {D.rootOfUnity m}).algebra'
  let _ : IsCyclotomicExtension {m.1} ℚ
      (IntermediateField.adjoin ℚ {D.rootOfUnity m}) :=
    (D.primitive_root m).intermediateField_adjoin_isCyclotomicExtension ℚ
  let _ : IsGalois ℚ (IntermediateField.adjoin ℚ {D.rootOfUnity m}) :=
    IsCyclotomicExtension.isGalois {m.1} ℚ _
  apply le_antisymm
  · change (FiniteGaloisIntermediateField.adjoin ℚ
      ({D.rootOfUnity m} : Set Qab)).toIntermediateField ≤ _
    rw [FiniteGaloisIntermediateField.adjoin_val]
    apply IntermediateField.normalClosure_le_iff_of_normal.mpr
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact IntermediateField.subset_adjoin ℚ _ (by simp)
  · exact IntermediateField.le_normalClosure _

private noncomputable def chapter10RootActionCoordinate
    {Qab : Type u} [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab]
    (D : Chapter10KroneckerWeberData Qab) (m : Chapter10PositiveNatural) :
    Gal(Qab / ℚ) →* (ZMod m.1)ˣ := by
  let _ : NeZero m.1 := ⟨Nat.ne_of_gt m.2⟩
  exact (D.cyclotomic.primitive_root m).autToPow ℚ

private theorem chapter10RootActionCoordinate_spec
    {Qab : Type u} [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab]
    (D : Chapter10KroneckerWeberData Qab) (m : Chapter10PositiveNatural)
    (σ : Gal(Qab / ℚ)) :
    D.cyclotomic.rootOfUnity m ^
        (chapter10RootActionCoordinate D m σ : ZMod m.1).val =
      σ (D.cyclotomic.rootOfUnity m) := by
  let _ : NeZero m.1 := ⟨Nat.ne_of_gt m.2⟩
  exact IsPrimitiveRoot.autToPow_spec ℚ (D.cyclotomic.primitive_root m) σ

private theorem chapter10RootActionCoordinate_compat
    {Qab : Type u} [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab]
    (D : Chapter10KroneckerWeberData Qab)
    {m n : Chapter10PositiveNatural} (h : n.1 ∣ m.1)
    (σ : Gal(Qab / ℚ)) :
    ZMod.unitsMap h (chapter10RootActionCoordinate D m σ) =
      chapter10RootActionCoordinate D n σ := by
  let _ : NeZero m.1 := ⟨Nat.ne_of_gt m.2⟩
  let _ : NeZero n.1 := ⟨Nat.ne_of_gt n.2⟩
  apply Units.ext
  rw [ZMod.unitsMap_val]
  have hpow :
      D.cyclotomic.rootOfUnity n ^
          (chapter10RootActionCoordinate D m σ : ZMod m.1).val =
        D.cyclotomic.rootOfUnity n ^
          (chapter10RootActionCoordinate D n σ : ZMod n.1).val := by
    calc
      D.cyclotomic.rootOfUnity n ^
          (chapter10RootActionCoordinate D m σ : ZMod m.1).val =
          (D.cyclotomic.rootOfUnity m ^ (m.1 / n.1)) ^
            (chapter10RootActionCoordinate D m σ : ZMod m.1).val := by
              rw [D.cyclotomic.rootOfUnity_compat h]
      _ = (D.cyclotomic.rootOfUnity m ^
            (chapter10RootActionCoordinate D m σ : ZMod m.1).val) ^
            (m.1 / n.1) := by
              rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ = (σ (D.cyclotomic.rootOfUnity m)) ^ (m.1 / n.1) := by
              rw [chapter10RootActionCoordinate_spec]
      _ = σ (D.cyclotomic.rootOfUnity m ^ (m.1 / n.1)) := by
              rw [map_pow]
      _ = σ (D.cyclotomic.rootOfUnity n) := by
              rw [D.cyclotomic.rootOfUnity_compat h]
      _ = D.cyclotomic.rootOfUnity n ^
          (chapter10RootActionCoordinate D n σ : ZMod n.1).val := by
              rw [chapter10RootActionCoordinate_spec]
  rw [← ZMod.natCast_val (R := ZMod n.1)
      (chapter10RootActionCoordinate D m σ : ZMod m.1),
    ← ZMod.natCast_zmod_val
      (chapter10RootActionCoordinate D n σ : ZMod n.1)]
  have hmod :=
    ((D.cyclotomic.primitive_root n).isOfFinOrder (NeZero.ne n.1)).pow_inj_mod.mp hpow
  rw [← (D.cyclotomic.primitive_root n).eq_orderOf] at hmod
  exact (ZMod.natCast_eq_natCast_iff _ _ _).2 <|
    hmod

private noncomputable def chapter10RootActionLimitMap
    {Qab : Type u} [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab]
    (D : Chapter10KroneckerWeberData Qab) :
    Gal(Qab / ℚ) →* chapter10CyclotomicUnitInverseLimit := by
  let e : Gal(Qab / ℚ) →* chapter10CyclotomicUnitInverseLimit :=
    { toFun := fun σ =>
        { val := fun m => chapter10RootActionCoordinate D m.unop σ
          property := by
            intro m n f
            change ZMod.unitsMap
                (show n.unop.1 ∣ m.unop.1 from leOfHom f.unop)
                (chapter10RootActionCoordinate D m.unop σ) =
              chapter10RootActionCoordinate D n.unop σ
            exact chapter10RootActionCoordinate_compat D
              (show n.unop.1 ∣ m.unop.1 from leOfHom f.unop) σ }
      map_one' := by
        apply ProfiniteGrp.limit_ext
        intro m
        change chapter10RootActionCoordinate D m.unop 1 = 1
        exact map_one (chapter10RootActionCoordinate D m.unop)
      map_mul' := by
        intro σ τ
        apply ProfiniteGrp.limit_ext
        intro m
        change chapter10RootActionCoordinate D m.unop (σ * τ) =
          chapter10RootActionCoordinate D m.unop σ *
            chapter10RootActionCoordinate D m.unop τ
        exact map_mul (chapter10RootActionCoordinate D m.unop) σ τ }
  exact e

private noncomputable def chapter10RootActionCoordinateViaRestriction
    {Qab : Type u} [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab]
    (D : Chapter10KroneckerWeberData Qab) (m : Chapter10PositiveNatural) :
    Gal(Qab / ℚ) →* (ZMod m.1)ˣ := by
  let K := D.cyclotomic.cyclotomicField m
  let _ : Algebra ℚ K := K.toIntermediateField.algebra'
  let ζ : K := ⟨D.cyclotomic.rootOfUnity m,
    Chapter10CyclotomicTowerData.rootOfUnity_mem_cyclotomicField D.cyclotomic m⟩
  let _ : NeZero m.1 := ⟨Nat.ne_of_gt m.2⟩
  have hζ : IsPrimitiveRoot ζ m.1 := by
    apply (IsPrimitiveRoot.coe_submonoidClass_iff).mp
    simpa [ζ] using D.cyclotomic.primitive_root m
  exact (IsPrimitiveRoot.autToPow ℚ hζ).comp (chapter10RestrictionMap K)

private theorem chapter10RootActionCoordinate_restrict
    {Qab : Type u} [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab]
    (D : Chapter10KroneckerWeberData Qab) (m : Chapter10PositiveNatural) :
    chapter10RootActionCoordinate D m =
      chapter10RootActionCoordinateViaRestriction D m := by
  let K := D.cyclotomic.cyclotomicField m
  let _ : Algebra ℚ K := K.toIntermediateField.algebra'
  let ζ : K := ⟨D.cyclotomic.rootOfUnity m,
    Chapter10CyclotomicTowerData.rootOfUnity_mem_cyclotomicField D.cyclotomic m⟩
  let _ : NeZero m.1 := ⟨Nat.ne_of_gt m.2⟩
  have hζ : IsPrimitiveRoot ζ m.1 := by
    apply (IsPrimitiveRoot.coe_submonoidClass_iff).mp
    simpa [ζ] using D.cyclotomic.primitive_root m
  apply MonoidHom.ext
  intro σ
  apply Units.ext
  rw [← ZMod.natCast_zmod_val
    (chapter10RootActionCoordinate D m σ : ZMod m.1),
    ← ZMod.natCast_zmod_val
      (chapter10RootActionCoordinateViaRestriction D m σ : ZMod m.1)]
  apply (ZMod.natCast_eq_natCast_iff _ _ _).2
  have hleft := chapter10RootActionCoordinate_spec D m σ
  have hright := IsPrimitiveRoot.autToPow ℚ hζ (chapter10RestrictionMap K σ)
  have hright' :
      D.cyclotomic.rootOfUnity m ^
          (IsPrimitiveRoot.autToPow ℚ hζ (chapter10RestrictionMap K σ) :
            ZMod m.1).val =
        σ (D.cyclotomic.rootOfUnity m) := by
    have hright0 := congrArg Subtype.val
      (IsPrimitiveRoot.autToPow_spec ℚ hζ (chapter10RestrictionMap K σ))
    simpa only [ζ, K, chapter10RestrictionMap,
      AlgEquiv.restrictNormalHom_apply, Subtype.coe_mk,
      IntermediateField.coe_pow, map_pow] using hright0
  have hpow := hleft.trans hright'.symm
  have hmod :=
    ((D.cyclotomic.primitive_root m).isOfFinOrder (NeZero.ne m.1)).pow_inj_mod.mp hpow
  rw [← (D.cyclotomic.primitive_root m).eq_orderOf] at hmod
  exact hmod

private theorem chapter10RootActionLimitMap_continuous
    {Qab : Type u} [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab]
    (D : Chapter10KroneckerWeberData Qab) :
    Continuous (chapter10RootActionLimitMap D) := by
  apply Continuous.subtype_mk
  refine continuous_pi
    (T := fun m =>
      ((chapter10CyclotomicProfiniteFunctor.obj m).toProfinite.toTop.str))
    (fun m => ?_)
  rw [chapter10RootActionCoordinate_restrict]
  let K := D.cyclotomic.cyclotomicField m.unop
  let _ : Algebra ℚ K := K.toIntermediateField.algebra'
  let ζ : K := ⟨D.cyclotomic.rootOfUnity m.unop,
    Chapter10CyclotomicTowerData.rootOfUnity_mem_cyclotomicField
      D.cyclotomic m.unop⟩
  have hζ : IsPrimitiveRoot ζ m.unop.1 := by
    apply (IsPrimitiveRoot.coe_submonoidClass_iff).mp
    simpa [ζ] using D.cyclotomic.primitive_root m.unop
  let _ : NeZero m.unop.1 := ⟨Nat.ne_of_gt m.unop.2⟩
  let _ : TopologicalSpace (ZMod m.unop.1)ˣ :=
    (chapter10CyclotomicProfiniteFunctor.obj m).toProfinite.toTop.str
  have hauto : Continuous (IsPrimitiveRoot.autToPow ℚ hζ) :=
    continuous_of_discreteTopology
  change Continuous ((IsPrimitiveRoot.autToPow ℚ hζ).comp
    (chapter10RestrictionMap K))
  exact hauto.comp <| by
    change Continuous (AlgEquiv.restrictNormalHom
      (F := ℚ) (K₁ := Qab) K.toIntermediateField)
    exact InfiniteGalois.restrictNormalHom_continuous K.toIntermediateField

private theorem chapter10RootActionLimitMap_denseRange
    {Qab : Type u} [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab]
    (D : Chapter10KroneckerWeberData Qab) :
    DenseRange (chapter10RootActionLimitMap D) := by
  classical
  apply dense_iff_inter_open.mpr
  rintro U ⟨s, hsO, hsv⟩ ⟨⟨spc, hspc⟩, uDefaultSpec⟩
  dsimp only [chapter10CyclotomicUnitInverseLimit] at U hsv uDefaultSpec ⊢
  have hpre : ⟨spc, hspc⟩ ∈ Subtype.val ⁻¹' s := hsv.symm ▸ uDefaultSpec
  have hspc_s : spc ∈ s := hpre
  rcases (isOpen_pi_iff.mp hsO) _ hspc_s with ⟨J, fJ, hJ1, hJ2⟩
  let n : Chapter10PositiveNatural :=
    ⟨J.lcm (fun j => j.unop.1), by
      have hne : J.lcm (fun j => j.unop.1) ≠ 0 := by
        apply (Finset.lcm_ne_zero_iff).mpr
        intro j hj
        exact Nat.ne_of_gt j.unop.2
      exact Nat.pos_of_ne_zero hne⟩
  let K := D.cyclotomic.cyclotomicField n
  let _ : Algebra ℚ K := K.toIntermediateField.algebra'
  let _ : IsGalois ℚ K := K.isGalois
  let _ : Normal ℚ K := IsGalois.to_normal
  let _ : NeZero n.1 := ⟨Nat.ne_of_gt n.2⟩
  let ζ : K := ⟨D.cyclotomic.rootOfUnity n,
    Chapter10CyclotomicTowerData.rootOfUnity_mem_cyclotomicField D.cyclotomic n⟩
  have hζ : IsPrimitiveRoot ζ n.1 := by
    apply (IsPrimitiveRoot.coe_submonoidClass_iff).mp
    simpa [ζ] using D.cyclotomic.primitive_root n
  let _ : IsCyclotomicExtension {n.1} ℚ K :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin
      n.1 ℚ Qab K.toIntermediateField
      (D.cyclotomic.primitive_root n)).2
      (chapter10CyclotomicField_eq_adjoin D.cyclotomic n)
  let u : (ZMod n.1)ˣ :=
    chapter10CyclotomicCoordinate n (spc (Opposite.op n))
  let ζ₀ : K := IsCyclotomicExtension.zeta n.1 ℚ K
  have hζ₀ : IsPrimitiveRoot ζ₀ n.1 := by
    simp [ζ₀]
  let τ : Gal(K / ℚ) :=
    (IsCyclotomicExtension.autEquivPow K
      (Polynomial.cyclotomic.irreducible_rat (NeZero.pos n.1))).symm u
  have hτcoord :
      (IsCyclotomicExtension.zeta_spec n.1 ℚ K).autToPow ℚ τ = u := by
    have h :=
      (IsCyclotomicExtension.autEquivPow K
        (Polynomial.cyclotomic.irreducible_rat (NeZero.pos n.1))).apply_symm_apply u
    simpa only [τ, ζ₀, IsCyclotomicExtension.autEquivPow_apply,
      OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe] using h
  have hτzeta₀ : ζ₀ ^ (u : ZMod n.1).val = τ ζ₀ := by
    have h := IsPrimitiveRoot.autToPow_spec ℚ (IsCyclotomicExtension.zeta_spec n.1 ℚ K) τ
    rw [hτcoord] at h
    exact h
  have hτroot : τ ζ = ζ ^ (u : ZMod n.1).val := by
    obtain ⟨k, -, hk⟩ :=
      (IsCyclotomicExtension.zeta_spec n.1 ℚ K).eq_pow_of_pow_eq_one hζ.pow_eq_one
    calc
      τ ζ = τ (ζ₀ ^ k) := by rw [hk]
      _ = (τ ζ₀) ^ k := by rw [map_pow]
      _ = (ζ₀ ^ (u : ZMod n.1).val) ^ k := by rw [hτzeta₀]
      _ = (ζ₀ ^ k) ^ (u : ZMod n.1).val := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ = ζ ^ (u : ZMod n.1).val := by rw [← hk]
  obtain ⟨σ, hσ⟩ :=
    AlgEquiv.restrictNormalHom_surjective
      (F := ℚ) (K₁ := K.toIntermediateField) (E := Qab) τ
  have hroot_n :
      σ (D.cyclotomic.rootOfUnity n) =
        D.cyclotomic.rootOfUnity n ^ (u : ZMod n.1).val := by
    calc
      σ (D.cyclotomic.rootOfUnity n) =
          (chapter10RestrictionMap K σ) ζ := by
            simp only [chapter10RestrictionMap,
              AlgEquiv.restrictNormalHom_apply, ζ]
      _ = τ ζ := by
        rw [show chapter10RestrictionMap K σ = τ by
          simpa [chapter10RestrictionMap] using hσ]
      _ = ζ ^ (u : ZMod n.1).val := by
        exact congrArg Subtype.val hτroot
  have hcoord_n :
      chapter10RootActionCoordinate D n σ = u := by
    apply Units.ext
    rw [← ZMod.natCast_zmod_val
      (chapter10RootActionCoordinate D n σ : ZMod n.1),
      ← ZMod.natCast_zmod_val (u : ZMod n.1)]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    have hpow := (chapter10RootActionCoordinate_spec D n σ).trans hroot_n
    have hmod :=
      ((D.cyclotomic.primitive_root n).isOfFinOrder (NeZero.ne n.1)).pow_inj_mod.mp
        hpow
    rw [← (D.cyclotomic.primitive_root n).eq_orderOf] at hmod
    exact hmod
  use chapter10RootActionLimitMap D σ
  refine ⟨?_, σ, rfl⟩
  rw [← hsv]
  apply hJ2
  intro a ha
  let f : Opposite.op n ⟶ a :=
    CategoryTheory.opHomOfLE (Finset.dvd_lcm (s := J)
      (f := fun j => j.unop.1) ha)
  have hf : a.unop.1 ∣ n.1 := leOfHom f.unop
  have hcoord_a :
      chapter10RootActionCoordinate D a.unop σ =
        spc a := by
    have he := (chapter10RootActionLimitMap D σ).property f
    have hx := hspc f
    change ZMod.unitsMap hf (chapter10RootActionCoordinate D n σ) =
      chapter10RootActionCoordinate D a.unop σ at he
    change ZMod.unitsMap hf
        (chapter10CyclotomicCoordinate n (spc (Opposite.op n))) = spc a at hx
    rw [hcoord_n] at he
    have hx' : ZMod.unitsMap hf u =
        spc a := by
      simpa [u] using hx
    exact he.symm.trans hx'
  change chapter10RootActionCoordinate D a.unop σ ∈ fJ a
  exact Set.mem_of_eq_of_mem hcoord_a (hJ1 a ha).right

/- The Kronecker--Weber assertion is exposed as a theorem, with its cofinality
input carried by the chosen data. -/
theorem chapter10_kronecker_weber_finite_containment
    {Qab : Type u} [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab]
    (D : Chapter10KroneckerWeberData Qab)
    (L : FiniteGaloisIntermediateField ℚ Qab)
    (hL : chapter10IsAbelianFiniteGaloisExtension L) :
    ∃ m, L ≤ D.cyclotomic.cyclotomicField m := by
  exact D.cyclotomic_cofinal L hL

theorem chapter10_Q_ab_eq_union_cyclotomic
    {Qab : Type u} [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab]
    (D : Chapter10KroneckerWeberData Qab) :
    chapter10CyclotomicFieldUnion D.cyclotomic = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  obtain ⟨L, hL, hx⟩ := D.closure.finite_abelian_subextension x
  obtain ⟨m, hm⟩ := chapter10_kronecker_weber_finite_containment D L hL
  exact ⟨m, hm hx⟩

private theorem chapter10RootActionLimitMap_injective
    {Qab : Type u} [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab]
    (D : Chapter10KroneckerWeberData Qab) :
    Function.Injective (chapter10RootActionLimitMap D) := by
  intro σ τ hστ
  apply AlgEquiv.ext
  intro x
  have hx : x ∈ chapter10CyclotomicFieldUnion D.cyclotomic := by
    rw [chapter10_Q_ab_eq_union_cyclotomic D]
    trivial
  obtain ⟨m, hm⟩ := hx
  have hcoord := congrArg
    (fun z : chapter10CyclotomicUnitInverseLimit =>
      z.val (Opposite.op m)) hστ
  change chapter10RootActionCoordinate D m σ =
    chapter10RootActionCoordinate D m τ at hcoord
  have hroot :
      σ (D.cyclotomic.rootOfUnity m) =
        τ (D.cyclotomic.rootOfUnity m) := by
    calc
      σ (D.cyclotomic.rootOfUnity m) =
          D.cyclotomic.rootOfUnity m ^
            (chapter10RootActionCoordinate D m σ : ZMod m.1).val :=
        (chapter10RootActionCoordinate_spec D m σ).symm
      _ = D.cyclotomic.rootOfUnity m ^
          (chapter10RootActionCoordinate D m τ : ZMod m.1).val := by
            rw [hcoord]
      _ = τ (D.cyclotomic.rootOfUnity m) :=
        chapter10RootActionCoordinate_spec D m τ
  have hm' : x ∈ IntermediateField.adjoin ℚ
      {D.cyclotomic.rootOfUnity m} := by
    rw [← chapter10CyclotomicField_eq_adjoin D.cyclotomic m]
    exact hm
  have h_agree : ∀ y : Qab, y ∈ IntermediateField.adjoin ℚ
      {D.cyclotomic.rootOfUnity m} → σ y = τ y := by
    intro y hy
    induction hy using IntermediateField.adjoin_induction with
    | mem y hy =>
        rw [Set.mem_singleton_iff] at hy
        subst y
        exact hroot
    | algebraMap y =>
        exact (σ.commutes y).trans (τ.commutes y).symm
    | add y z hy hz ihy ihz =>
        rw [map_add, map_add, ihy, ihz]
    | mul y z hy hz ihy ihz =>
        rw [map_mul, map_mul, ihy, ihz]
    | inv y hy ihy =>
        rw [map_inv₀, map_inv₀, ihy]
  exact h_agree x hm'

theorem chapter10_Q_ab_galois_group_is_profinite_units_with_action
    {Qab : Type u} [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab]
    (D : Chapter10KroneckerWeberData Qab) :
    Nonempty (Chapter10CyclotomicGaloisUnitAction D) := by
  have hcont : Continuous (chapter10RootActionLimitMap D) :=
    chapter10RootActionLimitMap_continuous D
  have hinj : Function.Injective (chapter10RootActionLimitMap D) :=
    chapter10RootActionLimitMap_injective D
  have hdense : Dense (Set.range (chapter10RootActionLimitMap D)) :=
    chapter10RootActionLimitMap_denseRange D
  have hclosed : IsClosedMap (chapter10RootActionLimitMap D) :=
    @Continuous.isClosedMap _ _ _ _ inferInstance inferInstance
      (chapter10RootActionLimitMap D) hcont
  have hsurj : Function.Surjective (chapter10RootActionLimitMap D) := by
    rw [← Set.range_eq_univ]
    calc
      Set.range (chapter10RootActionLimitMap D) =
          closure (Set.range (chapter10RootActionLimitMap D)) :=
        hclosed.isClosed_range.closure_eq.symm
      _ = Set.univ := hdense.closure_eq
  let e : Gal(Qab / ℚ) ≃*
      chapter10CyclotomicUnitInverseLimit :=
    MulEquiv.ofBijective (chapter10RootActionLimitMap D) ⟨hinj, hsurj⟩
  have hef : (e : Gal(Qab / ℚ) →
      chapter10CyclotomicUnitInverseLimit) =
        chapter10RootActionLimitMap D := by
    funext σ
    exact MulEquiv.ofBijective_apply
      (chapter10RootActionLimitMap D) ⟨hinj, hsurj⟩ σ
  let eTop : Gal(Qab / ℚ) ≃ₜ
      chapter10CyclotomicUnitInverseLimit :=
    @Continuous.homeoOfEquivCompactToT2 _ _ _ _ inferInstance inferInstance e
      (by
        change Continuous (e : Gal(Qab / ℚ) →
          chapter10CyclotomicUnitInverseLimit)
        rw [hef]
        exact hcont)
  let eC : Gal(Qab / ℚ) ≃ₜ*
      chapter10CyclotomicUnitInverseLimit :=
    ContinuousMulEquiv.mk' eTop (by
      intro σ τ
      change chapter10RootActionLimitMap D (σ * τ) =
        chapter10RootActionLimitMap D σ * chapter10RootActionLimitMap D τ
      exact map_mul (chapter10RootActionLimitMap D) σ τ)
  refine ⟨⟨eC, ?_⟩⟩
  intro σ m
  change σ (D.cyclotomic.rootOfUnity m) =
    D.cyclotomic.rootOfUnity m ^
      (chapter10RootActionCoordinate D m σ : ZMod m.1).val
  exact (chapter10RootActionCoordinate_spec D m σ).symm

theorem chapter10_Q_ab_galois_group_is_profinite_units
    {Qab : Type u} [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab]
    (D : Chapter10KroneckerWeberData Qab) :
    Nonempty (Gal(Qab / ℚ) ≃ₜ* chapter10CyclotomicUnitInverseLimit) := by
  obtain ⟨A⟩ := chapter10_Q_ab_galois_group_is_profinite_units_with_action D
  exact ⟨A.equiv⟩

/-- The cyclotomic Galois action, written as the inverse limit of the unit
groups `(ℤ/mℤ)ˣ`. -/
noncomputable def chapter10CyclotomicGaloisUnitEquiv
    {Qab : Type u} [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab]
    (D : Chapter10KroneckerWeberData Qab) :
    Gal(Qab / ℚ) ≃ₜ* chapter10CyclotomicUnitInverseLimit :=
  (Classical.choice
    (chapter10_Q_ab_galois_group_is_profinite_units_with_action D)).equiv

/- The coordinate interpretation is the bridge from the abstract inverse
limit to the chosen roots of unity.  The representative `val` is harmless
because the root has order `m.1`. -/
noncomputable def chapter10CyclotomicExponent
    {Qab : Type u} [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab]
    (D : Chapter10KroneckerWeberData Qab)
    (σ : Gal(Qab / ℚ)) (m : Chapter10PositiveNatural) : ℕ := by
  exact chapter10CyclotomicExponentOf (chapter10CyclotomicGaloisUnitEquiv D) σ m

theorem chapter10CyclotomicGaloisUnitEquiv_root_action
    {Qab : Type u} [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab]
    (D : Chapter10KroneckerWeberData Qab) (σ : Gal(Qab / ℚ))
    (m : Chapter10PositiveNatural) :
    σ (D.cyclotomic.rootOfUnity m) =
      D.cyclotomic.rootOfUnity m ^ chapter10CyclotomicExponent D σ m := by
  simpa [chapter10CyclotomicExponent, chapter10CyclotomicGaloisUnitEquiv,
    chapter10CyclotomicExponentOf] using
    (Classical.choice
      (chapter10_Q_ab_galois_group_is_profinite_units_with_action D)).root_action σ m

theorem chapter10_complex_conjugation_corresponds_to_minus_one
    {Qab : Type u} [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab]
    (D : Chapter10KroneckerWeberData Qab) :
    chapter10CyclotomicGaloisUnitEquiv D D.complexConjugation =
      chapter10CyclotomicMinusOne := by
  apply ProfiniteGrp.limit_ext
  intro m
  apply Units.ext
  simp [chapter10CyclotomicMinusOne, chapter10CyclotomicUnitInverseLimit,
    chapter10CyclotomicUnitFunctor]
  let u : (ZMod m.unop.1)ˣ :=
    (chapter10CyclotomicGaloisUnitEquiv D D.complexConjugation).val m
  change (u : ZMod m.unop.1) = (-1 : ZMod m.unop.1)
  have hroot := chapter10CyclotomicGaloisUnitEquiv_root_action D
    D.complexConjugation m.unop
  rw [D.complexConjugation_on_roots] at hroot
  have hprim := D.cyclotomic.primitive_root m.unop
  have hexp :
      chapter10CyclotomicExponent D D.complexConjugation m.unop = u.val.val := by
    rfl
  have hpow :
      D.cyclotomic.rootOfUnity m.unop ^
          (chapter10CyclotomicExponent D D.complexConjugation m.unop + 1) = 1 := by
    rw [pow_succ, ← hroot]
    simp [hprim.ne_zero (Nat.ne_of_gt m.unop.2)]
  have hdiv :
      m.unop.1 ∣ u.val.val + 1 := by
    rw [← hexp]
    exact (hprim.pow_eq_one_iff_dvd _).mp hpow
  have hzero : ((u.val.val + 1 : ℕ) : ZMod m.unop.1) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact hdiv
  calc
    (u : ZMod m.unop.1) =
        (((u : ZMod m.unop.1).val : ℕ) : ZMod m.unop.1) := by
      symm
      exact @ZMod.natCast_zmod_val m.unop.1
        ⟨Nat.ne_of_gt m.unop.2⟩ _
    _ = ((u.val.val + 1 : ℕ) : ZMod m.unop.1) - 1 := by
      simp [Nat.cast_add, add_comm]
    _ = -1 := by rw [hzero]; simp

theorem chapter10_positive_real_component_of_CQ_in_global_kernel
    {C : Type u} {Qab : Type v} [CommGroup C] [TopologicalSpace C] [T2Space C]
    [IsTopologicalGroup C] [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab]
    (T : Chapter10IdeleClassTopologyData C)
    (F : Chapter10FiniteArtinFamily C ℚ Qab)
    (R : Chapter10FiniteReciprocityData F) :
    T.positiveRealComponent ≤ (chapter10GlobalArtinMap F).ker := by
  simpa only [← chapter10_globalArtinMap_kernel_eq_identityComponent T F R] using
    (chapter10_positiveRealComponent_le_identityComponent T)

theorem chapter10_ray_class_field_union_replaces_cyclotomic_union
    {K : Type u} {Kab : Type v} [Field K] [NumberField K] [Field Kab]
    [Algebra K Kab] [IsGalois K Kab]
    (A : Chapter10AbelianClosureData K Kab)
    (R : Chapter10RayClassFieldSystem K Kab) :
    chapter10RayClassFieldUnion R = Set.univ :=
  chapter10RayClassFieldUnion_eq_univ A R

theorem chapter10_every_finite_abelian_extension_is_in_a_ray_class_field
    {K : Type u} {Kab : Type v} [Field K] [NumberField K] [Field Kab]
    [Algebra K Kab] [IsGalois K Kab]
    (R : Chapter10RayClassFieldSystem K Kab)
    (L : FiniteGaloisIntermediateField K Kab)
    (hL : chapter10IsAbelianFiniteGaloisExtension L) :
    ∃ m, L ≤ R.rayField m :=
  R.contains_every_finite_abelian L hL

/- SOURCE_NOTE: the sentence that no equally elementary roots-of-unity family
works for a general number field is a qualitative warning, not a standalone
mathematical assertion. The precise replacement is the ray-class-field union
and conductor containment theorems above. -/

end

end LastLib.Book06GlobalClassFieldTheory.Chapter10
