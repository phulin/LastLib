import LastLib.Book06GlobalClassFieldTheory.Chapter03.Dependencies
import Mathlib.Topology.Instances.NNReal.Lemmas

namespace LastLib.Book06GlobalClassFieldTheory.Chapter03

noncomputable section

open Filter Set
open scoped BigOperators RestrictedProduct

/-!
## 3.2. Norm groups are open and have finite index

The local norm statements are kept separate from the global finiteness argument.  In
particular, the latter is formulated for the class group, not for the idèle group.
-/

/-- The local norm subgroup attached to a place of `K` and a place above it. -/
def chapter03LocalNormGroup
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (v : Chapter03Place K)
    (w : Chapter03Place L) : Subgroup (S_K.localFactor v).carrier :=
  MonoidHom.range (N.localNorm v w)

@[simp] theorem chapter03_mem_localNormGroup_iff
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (v : Chapter03Place K)
    (w : Chapter03Place L) (x : (S_K.localFactor v).carrier) :
    x ∈ chapter03LocalNormGroup N v w ↔
      ∃ y : (S_L.localFactor w).carrier, N.localNorm v w y = x :=
  Iff.rfl

theorem chapter03_local_norm_group_open
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (v : Chapter03Place K)
    (w : Chapter03Place L) (hw : w ∈ N.above v) :
    IsOpen (chapter03LocalNormGroup N v w : Set (S_K.localFactor v).carrier) := by
  exact N.localNorm_range_isOpen v w hw

theorem chapter03_local_norm_on_units_surjective
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) {v : Chapter03Place K}
    (hv : S_K.finitePlace v) (hu : N.unramified v)
    (w : Chapter03Place L) (hw : w ∈ N.above v)
    (x : (S_K.localFactor v).carrier) (hx : x ∈ (S_K.localFactor v).unit) :
    ∃ y : (S_L.localFactor w).carrier,
      y ∈ (S_L.localFactor w).unit ∧ N.localNorm v w y = x := by
  exact N.localNorm_units_surjective hv hu w hw x hx

theorem chapter03_local_units_le_norm_group
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) {v : Chapter03Place K}
    (hv : S_K.finitePlace v) (hu : N.unramified v)
    (w : Chapter03Place L) (hw : w ∈ N.above v) :
    (S_K.localFactor v).unit ≤ chapter03LocalNormGroup N v w := by
  intro x hx
  rcases N.localNorm_units_surjective hv hu w hw x hx with ⟨y, _, hy⟩
  exact ⟨y, hy⟩

theorem chapter03_eventually_finite_unramified
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) :
    ∀ᶠ v in cofinite, S_K.finitePlace v ∧ N.unramified v :=
  N.eventually_finite_unramified

/-- The idèle norm subgroup in the base idèle group. -/
def chapter03IdeleNormSubgroup
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) : Subgroup (Chapter03Ideles S_K) :=
  (chapter03IdeleNorm N).range

theorem chapter03_mem_ideleNormSubgroup_iff
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (x : Chapter03Ideles S_K) :
    x ∈ chapter03IdeleNormSubgroup N ↔
      ∃ y : Chapter03Ideles S_L, chapter03IdeleNorm N y = x := by
  rfl

/- The following quotient is deliberately retained as an obstruction object.  The diagonal
principal-idèle contribution is not removed here, so no finite-index or Galois identification
is asserted for it. -/
abbrev Chapter03IdeleNormQuotient
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) :=
  Chapter03Ideles S_K ⧸ chapter03IdeleNormSubgroup N

theorem chapter03_ideleNorm_range_contains_basic_open
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) :
    ∃ U : OpenSubgroup (Chapter03Ideles S_K),
      (U : Subgroup (Chapter03Ideles S_K)) ≤ chapter03IdeleNormSubgroup N := by
  classical
  have hgood : ∀ᶠ v in cofinite, S_K.finitePlace v ∧ N.unramified v :=
    N.eventually_finite_unramified
  let bad : Set (Chapter03Place K) :=
    {v | ¬ (S_K.finitePlace v ∧ N.unramified v)}
  have hbad : bad.Finite := by
    exact Filter.eventually_cofinite.mp (by simpa [bad] using hgood)
  let badFin : Finset (Chapter03Place K) := hbad.toFinset
  let w₀ : ∀ v : Chapter03Place K, Chapter03Place L :=
    fun v => Classical.choose (N.above_nonempty v)
  have hw₀ : ∀ v, w₀ v ∈ N.above v := by
    intro v
    exact Classical.choose_spec (N.above_nonempty v)
  let W : ∀ v : Chapter03Place K, Subgroup (S_K.localFactor v).carrier :=
    fun v => if v ∈ bad then chapter03LocalNormGroup N v (w₀ v)
      else (S_K.localFactor v).unit
  have hWopen : ∀ v, IsOpen (W v : Set (S_K.localFactor v).carrier) := by
    intro v
    by_cases hv : v ∈ bad
    · simp only [W, if_pos hv]
      change IsOpen (MonoidHom.range (N.localNorm v (w₀ v)) :
        Set (S_K.localFactor v).carrier)
      exact N.localNorm_range_isOpen v (w₀ v) (hw₀ v)
    · simpa [W, hv] using (S_K.localFactor v).unit_isOpen
  let U : Subgroup (Chapter03Ideles S_K) := {
    carrier := {x |
      (∀ v, x v ∈ (S_K.localFactor v).unit) ∧
        (∀ v ∈ badFin, x v ∈ W v)}
    one_mem' := by
      constructor
      · intro v
        exact (S_K.localFactor v).unit.one_mem
      · intro v hv
        exact (W v).one_mem
    mul_mem' := by
      intro x y hx hy
      refine ⟨?_, ?_⟩
      · intro v
        change x v * y v ∈ (S_K.localFactor v).unit
        exact (S_K.localFactor v).unit.mul_mem (hx.1 v) (hy.1 v)
      · intro v hv
        change x v * y v ∈ W v
        exact (W v).mul_mem (hx.2 v hv) (hy.2 v hv)
    inv_mem' := by
      intro x hx
      refine ⟨?_, ?_⟩
      · intro v
        change (x v)⁻¹ ∈ (S_K.localFactor v).unit
        exact (S_K.localFactor v).unit.inv_mem (hx.1 v)
      · intro v hv
        change (x v)⁻¹ ∈ W v
        exact (W v).inv_mem (hx.2 v hv) }
  have hUopen : IsOpen (U : Set (Chapter03Ideles S_K)) := by
    have hunitOpen : IsOpen {x : Chapter03Ideles S_K |
        ∀ v, x v ∈ (S_K.localFactor v).unit} :=
      RestrictedProduct.isOpen_forall_mem
        (R := fun v => (S_K.localFactor v).carrier)
        (A := fun v => (S_K.localFactor v).unit)
        (fun v => (S_K.localFactor v).unit_isOpen)
    have hbadOpen : IsOpen (⋂ v ∈ badFin,
        {x : Chapter03Ideles S_K | x v ∈ W v}) :=
      isOpen_biInter_finset (fun v hv =>
        (hWopen v).preimage (RestrictedProduct.continuous_eval v))
    have hset : (U : Set (Chapter03Ideles S_K)) =
        {x : Chapter03Ideles S_K | ∀ v, x v ∈ (S_K.localFactor v).unit} ∩
          ⋂ v ∈ badFin, {x : Chapter03Ideles S_K | x v ∈ W v} := by
      ext x
      simp [U]
    rw [hset]
    exact hunitOpen.inter hbadOpen
  refine ⟨⟨U, hUopen⟩, ?_⟩
  intro x hx
  change (∀ v, x v ∈ (S_K.localFactor v).unit) ∧
    (∀ v ∈ badFin, x v ∈ W v) at hx
  have hy₀ : ∀ v, ∃ y : (S_L.localFactor (w₀ v)).carrier,
      (¬ v ∈ bad → y ∈ (S_L.localFactor (w₀ v)).unit) ∧
        N.localNorm v (w₀ v) y = x v := by
    intro v
    by_cases hv : v ∈ bad
    · have hxv : x v ∈ chapter03LocalNormGroup N v (w₀ v) := by
        have hxW := hx.2 v (by simpa [badFin] using hv)
        simpa [W, hv] using hxW
      rcases (chapter03_mem_localNormGroup_iff N v (w₀ v) (x v)).1 hxv with ⟨y, hy⟩
      exact ⟨y, fun hnot => False.elim (hnot hv), hy⟩
    · have hvgood : S_K.finitePlace v ∧ N.unramified v := by
        apply Classical.not_not.mp
        simpa [bad] using hv
      rcases N.localNorm_units_surjective hvgood.1 hvgood.2 (w₀ v) (hw₀ v)
        (x v) (hx.1 v) with ⟨y, hyu, hy⟩
      exact ⟨y, fun _ => hyu, hy⟩
  let z : ∀ v, ∀ w : Chapter03Place L, (S_L.localFactor w).carrier :=
    fun v w => if h : w = w₀ v then h ▸ Classical.choose (hy₀ v) else 1
  have hz : ∀ v, (N.above v).prod (fun w => N.localNorm v w (z v w)) = x v := by
    intro v
    rw [Finset.prod_eq_single_of_mem (w₀ v) (hw₀ v)]
    · simpa [z] using (Classical.choose_spec (hy₀ v)).2
    · intro w hw hne
      simp [z, hne]
  have hbelow : Filter.Tendsto N.below cofinite cofinite :=
    Filter.Tendsto.cofinite_of_finite_preimage_singleton (fun v => by
      refine (N.above v).finite_toSet.subset ?_
      intro w hw
      exact (N.mem_above_iff v w).2 (by simpa using hw))
  let y : Chapter03Ideles S_L :=
    ⟨fun w => z (N.below w) w, by
      have hgood' : ∀ᶠ w in cofinite, ¬ N.below w ∈ bad := by
        filter_upwards [hbelow hgood] with w hw
        simpa [bad] using hw
      filter_upwards [hgood'] with w hw
      generalize hv : N.below w = v
      by_cases heq : w = w₀ v
      · change (dite (w = w₀ v)
          (fun h => h ▸ Classical.choose (hy₀ v)) (fun _ => 1)) ∈
            (S_L.localFactor w).unit
        split
        · next h =>
            have hwv : v ∉ bad := by simpa only [hv] using hw
            cases h
            exact (Classical.choose_spec (hy₀ v)).1 hwv
        · next h => exact (h heq).elim
      · change (dite (w = w₀ v)
          (fun h => h ▸ Classical.choose (hy₀ v)) (fun _ => 1)) ∈
            (S_L.localFactor w).unit
        split
        · next h => exact (heq h).elim
        · next _ => exact (S_L.localFactor w).unit.one_mem⟩
  refine ⟨y, ?_⟩
  apply RestrictedProduct.ext
  intro v
  rw [chapter03IdeleNorm_apply]
  calc
    (N.above v).prod (fun w => N.localNorm v w (y w)) =
        (N.above v).prod (fun w => N.localNorm v w (z v w)) := by
      apply Finset.prod_congr rfl
      intro w hw
      have hwbelow : N.below w = v := (N.mem_above_iff v w).1 hw
      change N.localNorm v w (z (N.below w) w) = N.localNorm v w (z v w)
      rw [hwbelow]
    _ = x v := hz v

theorem chapter03_ideleNorm_range_isOpen
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) :
    IsOpen (chapter03IdeleNormSubgroup N : Set (Chapter03Ideles S_K)) := by
  obtain ⟨U, hU⟩ := chapter03_ideleNorm_range_contains_basic_open N
  exact Subgroup.isOpen_mono hU U.isOpen

/-- The image of the idèle norm after passing to idèle classes. -/
def chapter03NormClassSubgroup
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) : Subgroup (Chapter03ClassGroup S_K) :=
  (chapter03ClassNorm N).range

theorem chapter03_normClassSubgroup_eq_principal_times_ideleNorm_quotient
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) :
    chapter03NormClassSubgroup N =
      Subgroup.map (QuotientGroup.mk' (chapter03PrincipalSubgroup S_K))
        (chapter03PrincipalSubgroup S_K ⊔ chapter03IdeleNormSubgroup N) := by
  ext c
  constructor
  · rintro ⟨d, rfl⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
      (chapter03PrincipalSubgroup S_L) d
    rw [chapter03ClassNorm_mk]
    exact Subgroup.mem_map_of_mem _
      (Subgroup.mem_sup_right ⟨y, rfl⟩)
  · intro hc
    rcases Subgroup.mem_map.mp hc with ⟨x, hx, rfl⟩
    rcases Subgroup.mem_sup.mp hx with ⟨p, hp, n, hn, hpn⟩
    rcases hp with ⟨a, ha⟩
    rcases hn with ⟨y, hy⟩
    rw [← hpn]
    refine ⟨QuotientGroup.mk' (chapter03PrincipalSubgroup S_L) y, ?_⟩
    rw [chapter03ClassNorm_mk]
    rw [← hy, ← ha, map_mul, chapter03_class_of_principal, one_mul]

abbrev Chapter03ClassNormQuotient
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) :=
  Chapter03ClassGroup S_K ⧸ chapter03NormClassSubgroup N

theorem chapter03_classNorm_range_isOpen
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) :
    IsOpen (chapter03NormClassSubgroup N : Set (Chapter03ClassGroup S_K)) := by
  obtain ⟨U, hU⟩ := chapter03_ideleNorm_range_contains_basic_open N
  have hmap : Subgroup.map (QuotientGroup.mk' (chapter03PrincipalSubgroup S_K))
      (U : Subgroup (Chapter03Ideles S_K)) ≤ chapter03NormClassSubgroup N := by
    rw [chapter03_normClassSubgroup_eq_principal_times_ideleNorm_quotient]
    exact Subgroup.map_mono (le_trans hU le_sup_right)
  apply Subgroup.isOpen_mono hmap
  rw [Subgroup.coe_map]
  exact QuotientGroup.isOpenMap_coe (U : Set (Chapter03Ideles S_K)) U.isOpen

theorem chapter03_classNorm_range_isClosed
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) :
    IsClosed (chapter03NormClassSubgroup N : Set (Chapter03ClassGroup S_K)) := by
  exact Subgroup.isClosed_of_isOpen _ (chapter03_classNorm_range_isOpen N)

/-!
### The module direction and the compact norm-one part

The next map is the descended normalized idèle-module map.  Its kernel is the book's
`C_K^1`; this isolates the compact factor used in the finite-index argument.
-/

/-- The positive-power map occurring on a real archimedean module coordinate. -/
def chapter03PositivePower (n : ℕ) : Chapter03PositiveReals →* Chapter03PositiveReals where
  toFun x := x ^ n
  map_one' := by simp
  map_mul' x y := by simp [mul_pow]

theorem chapter03_positivePower_surjective {n : ℕ} (hn : 0 < n) :
    Function.Surjective (chapter03PositivePower n) := by
  intro x
  let r : NNReal := (NNReal.powOrderIso n hn.ne').symm x.val
  have hr : r ≠ 0 := by
    intro hr
    have hx0 : (x : NNReal) = 0 := by
      calc
        (x : NNReal) = (NNReal.powOrderIso n hn.ne') r := by
          symm
          simp [r]
        _ = 0 := by
          rw [hr]
          change (NNReal.powOrderIso n hn.ne') (⊥ : NNReal) = ⊥
          exact (NNReal.powOrderIso n hn.ne').map_bot
    exact (Units.ne_zero x) hx0
  refine ⟨Units.mk0 r hr, ?_⟩
  ext
  unfold chapter03PositivePower
  dsimp only [MonoidHom.coe_mk]
  simp
  have hpow : r ^ n = x.val := by
    change (NNReal.powOrderIso n hn.ne') r = x.val
    dsimp [r]
    exact (NNReal.powOrderIso n hn.ne').apply_symm_apply x.val
  exact_mod_cast hpow

noncomputable def chapter03ClassModuleNorm
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03AdelicModuleData N) :
    Chapter03ClassGroup S_K →* Chapter03PositiveReals :=
  QuotientGroup.lift (chapter03PrincipalSubgroup S_K) A.baseModuleNorm (by
    intro x hx
    rcases hx with ⟨a, rfl⟩
    exact A.base_principal_norm_one a)

@[simp] theorem chapter03ClassModuleNorm_mk
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03AdelicModuleData N) (y : Chapter03Ideles S_K) :
    chapter03ClassModuleNorm A
        (QuotientGroup.mk' (chapter03PrincipalSubgroup S_K) y) = A.baseModuleNorm y := by
  rfl

theorem chapter03_classModuleNorm_continuous
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03AdelicModuleData N) :
    Continuous (chapter03ClassModuleNorm A) := by
  apply QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.continuous_iff.mpr
  have hcomp : Continuous A.baseModuleNorm := A.baseModuleNorm_continuous
  convert hcomp using 1
  funext x
  change chapter03ClassModuleNorm A
    (QuotientGroup.mk' (chapter03PrincipalSubgroup S_K) x) = _
  exact chapter03ClassModuleNorm_mk A x

def chapter03ClassModuleOneSubgroup
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03AdelicModuleData N) : Subgroup (Chapter03ClassGroup S_K) :=
  (chapter03ClassModuleNorm A).ker

def chapter03_classModule_quotient_positiveReal
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03AdelicModuleData N) :
    Prop :=
  ∃ e : (Chapter03ClassGroup S_K ⧸ chapter03ClassModuleOneSubgroup A) ≃*
      Chapter03PositiveReals,
    ∀ c : Chapter03ClassGroup S_K,
      e (QuotientGroup.mk' (chapter03ClassModuleOneSubgroup A) c) =
        chapter03ClassModuleNorm A c

theorem chapter03_classModuleNorm_surjective
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03AdelicModuleData N) :
    Function.Surjective (chapter03ClassModuleNorm A) := by
  intro x
  rcases A.baseModuleNorm_surjective x with ⟨y, hy⟩
  refine ⟨QuotientGroup.mk' (chapter03PrincipalSubgroup S_K) y, ?_⟩
  rw [chapter03ClassModuleNorm_mk]
  exact hy

theorem chapter03_classModule_quotient_positiveReal_of_surjective
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03AdelicModuleData N) :
    chapter03_classModule_quotient_positiveReal A := by
  refine ⟨QuotientGroup.quotientKerEquivOfSurjective
      (chapter03ClassModuleNorm A)
      (chapter03_classModuleNorm_surjective A), ?_⟩
  intro c
  exact QuotientGroup.kerLift_mk (chapter03ClassModuleNorm A) c

/- The field-data structure now carries the canonical idèle comparison and the module structure
is required to transport the canonical module.  The predicate names are retained for dependent
interfaces, while the canonical theorem APIs below provide the unconditional chapter-facing
assertions. -/
def chapter03_classModuleOne_compact
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03AdelicModuleData N) :
    Prop :=
  IsCompact (chapter03ClassModuleOneSubgroup A : Set (Chapter03ClassGroup S_K))

def chapter03_classNorm_coset_has_module_one_representative
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03AdelicModuleData N) (c : Chapter03ClassGroup S_K) :
    Prop :=
    ∃ c₁ : Chapter03ClassGroup S_K, ∃ n : Chapter03ClassGroup S_K,
      c₁ ∈ chapter03ClassModuleOneSubgroup A ∧
      n ∈ chapter03NormClassSubgroup N ∧ c = c₁ * n

/- The positive module direction is reached through the norm: if `c` has module
value `t`, choose an extension idèle whose module value is `t`, and divide by
its class norm.  This is the algebraic bridge used before compactness enters
the finite-index argument. -/
theorem chapter03_classNorm_coset_has_module_one_representative_of_module_surjective
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03AdelicModuleData N) (c : Chapter03ClassGroup S_K) :
    chapter03_classNorm_coset_has_module_one_representative A c := by
  classical
  rcases QuotientGroup.mk'_surjective (chapter03PrincipalSubgroup S_K) c with ⟨x, rfl⟩
  rcases A.topModuleNorm_surjective (A.baseModuleNorm x) with ⟨y, hy⟩
  let n : Chapter03ClassGroup S_K :=
    chapter03ClassNorm N (QuotientGroup.mk' (chapter03PrincipalSubgroup S_L) y)
  let c₁ : Chapter03ClassGroup S_K :=
    QuotientGroup.mk' (chapter03PrincipalSubgroup S_K) x * n⁻¹
  refine ⟨c₁, n, ?_, ?_, ?_⟩
  · change chapter03ClassModuleNorm A c₁ = 1
    simp only [c₁, n, map_mul, map_inv, chapter03ClassModuleNorm_mk,
      chapter03ClassNorm_mk]
    rw [A.module_norm_compatibility, ← hy]
    simp
  · exact ⟨QuotientGroup.mk' (chapter03PrincipalSubgroup S_L) y, rfl⟩
  · simp [c₁, n]

def chapter03_classNormQuotient_compact
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L} :
    Prop :=
  IsCompact (Set.univ : Set (Chapter03ClassNormQuotient N))

/- Compactness of the module-one subgroup descends to the norm quotient once
the preceding representative lemma has been supplied.  Keeping this as a
separate bridge makes the topology used by the finite-index argument
explicit. -/
theorem chapter03_classNormQuotient_compact_of_module_one_compact
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03AdelicModuleData N)
    (hcompact : chapter03_classModuleOne_compact A) :
    chapter03_classNormQuotient_compact (N := N) := by
  classical
  change IsCompact (chapter03ClassModuleOneSubgroup A :
    Set (Chapter03ClassGroup S_K)) at hcompact
  let H : Subgroup (Chapter03ClassGroup S_K) := chapter03NormClassSubgroup N
  let q : Chapter03ClassGroup S_K →*
      (Chapter03ClassGroup S_K ⧸ H) := QuotientGroup.mk' H
  have himage : IsCompact
      (q '' (chapter03ClassModuleOneSubgroup A :
        Set (Chapter03ClassGroup S_K))) :=
    hcompact.image QuotientGroup.continuous_mk
  have hsurj :
      q '' (chapter03ClassModuleOneSubgroup A :
        Set (Chapter03ClassGroup S_K)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    rcases QuotientGroup.mk'_surjective H z with ⟨c, rfl⟩
    rcases chapter03_classNorm_coset_has_module_one_representative_of_module_surjective
      A c with ⟨c₁, n, hc₁, hn, hcn⟩
    refine ⟨c₁, hc₁, ?_⟩
    rw [hcn]
    change q c₁ = q (c₁ * n)
    have hnq : q n = 1 := by
      change (QuotientGroup.mk' H) n = 1
      exact (QuotientGroup.eq_one_iff n).2 (by simpa [H] using hn)
    rw [map_mul, hnq]
    exact (mul_one (q c₁)).symm
  change IsCompact (Set.univ : Set (Chapter03ClassNormQuotient N))
  rw [← hsurj]
  exact himage

/- An open subgroup with compact quotient has finite index.  The openness
theorem above supplies the discreteness of the quotient; this declaration is
the finite-index form used by the book. -/
theorem chapter03_normClassSubgroup_finiteIndex_of_compact_quotient
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (hcompact : chapter03_classNormQuotient_compact (N := N)) :
    (chapter03NormClassSubgroup N).FiniteIndex := by
  classical
  change IsCompact (Set.univ : Set (Chapter03ClassNormQuotient N)) at hcompact
  let hcompactSpace : CompactSpace (Chapter03ClassNormQuotient N) := ⟨hcompact⟩
  let hdiscrete : DiscreteTopology (Chapter03ClassNormQuotient N) :=
    QuotientGroup.discreteTopology (chapter03_classNorm_range_isOpen N)
  let hfinite : Finite (Chapter03ClassNormQuotient N) :=
    @finite_of_compact_of_discrete (Chapter03ClassNormQuotient N) _
      hcompactSpace hdiscrete
  exact ⟨@Subgroup.index_ne_zero_of_finite _ _ (chapter03NormClassSubgroup N) hfinite⟩

theorem chapter03_normClassSubgroup_finiteIndex_of_module_one_compact
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03AdelicModuleData N)
    (hcompact : chapter03_classModuleOne_compact A) :
    (chapter03NormClassSubgroup N).FiniteIndex := by
  exact chapter03_normClassSubgroup_finiteIndex_of_compact_quotient
    (chapter03_classNormQuotient_compact_of_module_one_compact A hcompact)

theorem chapter03_classNormQuotient_finite_of_compact_quotient
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (hcompact : chapter03_classNormQuotient_compact (N := N)) :
    Finite (Chapter03ClassNormQuotient N) := by
  classical
  change IsCompact (Set.univ : Set (Chapter03ClassNormQuotient N)) at hcompact
  let hcompactSpace : CompactSpace (Chapter03ClassNormQuotient N) := ⟨hcompact⟩
  let hdiscrete : DiscreteTopology (Chapter03ClassNormQuotient N) :=
    QuotientGroup.discreteTopology (chapter03_classNorm_range_isOpen N)
  exact @finite_of_compact_of_discrete (Chapter03ClassNormQuotient N) _
    hcompactSpace hdiscrete

def chapter03_normClassSubgroup_finiteIndex
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L} :
    Prop :=
  (chapter03NormClassSubgroup N).FiniteIndex

def chapter03_classNormQuotient_finite
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L} :
    Prop :=
  Finite (Chapter03ClassNormQuotient N)

/- The canonical bridges in `Chapter03FieldIdeleData` and `Chapter03AdelicModuleData` make these
theorem APIs available without treating the target propositions as hypotheses. -/
theorem chapter03_classModuleOne_compact_canonical
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03AdelicModuleData N) :
    chapter03_classModuleOne_compact A := by
  classical
  change IsCompact (chapter03ClassModuleOneSubgroup A :
    Set (Chapter03ClassGroup S_K))
  let P : Subgroup (Chapter03Ideles S_K) := chapter03PrincipalSubgroup S_K
  let Q : Subgroup
      (LastLib.Book06GlobalClassFieldTheory.Chapter01.BookIdeleGroup K) :=
    LastLib.Book06GlobalClassFieldTheory.Chapter01.principalIdeleSubgroup K
  have hPQ : P.map S_K.canonicalIdele = Q := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      rcases hy with ⟨a, rfl⟩
      refine ⟨a, ?_⟩
      change LastLib.Book06GlobalClassFieldTheory.Chapter01.principalIdele a =
        S_K.canonicalIdele (chapter03PrincipalIdele S_K a)
      exact (S_K.canonicalIdele_principal a).symm
    · intro hx
      rcases hx with ⟨a, rfl⟩
      apply Subgroup.mem_map.mpr
      refine ⟨chapter03PrincipalIdele S_K a, ⟨a, rfl⟩, ?_⟩
      change S_K.canonicalIdele (chapter03PrincipalIdele S_K a) =
        LastLib.Book06GlobalClassFieldTheory.Chapter01.principalIdele a
      exact S_K.canonicalIdele_principal a
  let e : Chapter03ClassGroup S_K ≃*
      LastLib.Book06GlobalClassFieldTheory.Chapter01.BookIdeleClassGroup K :=
    QuotientGroup.congr P Q S_K.canonicalIdele hPQ
  have hecont : Continuous e := by
    apply QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.continuous_iff.mpr
    change Continuous (fun x => QuotientGroup.mk' Q (S_K.canonicalIdele x))
    exact QuotientGroup.continuous_mk.comp S_K.canonicalIdele_continuous
  have hecont_symm : Continuous e.symm := by
    apply QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.continuous_iff.mpr
    change Continuous (fun x => QuotientGroup.mk' P (S_K.canonicalIdele.symm x))
    exact QuotientGroup.continuous_mk.comp S_K.canonicalIdele_inverse_continuous
  have hmodule :
      (LastLib.Book06GlobalClassFieldTheory.Chapter01.classModule (K := K)).comp e =
        A.canonicalPositiveReal.toMonoidHom.comp (chapter03ClassModuleNorm A) := by
    apply QuotientGroup.monoidHom_ext
    apply MonoidHom.ext
    intro x
    simp only [MonoidHom.comp_apply, e, chapter03ClassModuleNorm_mk]
    change LastLib.Book06GlobalClassFieldTheory.Chapter01.classModule
          (QuotientGroup.mk' Q (S_K.canonicalIdele x)) =
      A.canonicalPositiveReal (A.baseModuleNorm x)
    change LastLib.Book06GlobalClassFieldTheory.Chapter01.ideleModule
          (S_K.canonicalIdele x) =
      A.canonicalPositiveReal (A.baseModuleNorm x)
    exact (A.baseModuleNorm_canonical x).symm
  have hker :
      e '' (chapter03ClassModuleOneSubgroup A : Set (Chapter03ClassGroup S_K)) =
        (LastLib.Book06GlobalClassFieldTheory.Chapter01.classModuleOneSubgroup K :
          Set (LastLib.Book06GlobalClassFieldTheory.Chapter01.BookIdeleClassGroup K)) := by
    ext z
    constructor
    · rintro ⟨c, hc, rfl⟩
      change (LastLib.Book06GlobalClassFieldTheory.Chapter01.classModule (K := K)).comp e c = 1
      rw [hmodule]
      change A.canonicalPositiveReal (chapter03ClassModuleNorm A c) = 1
      rw [show chapter03ClassModuleNorm A c = 1 from hc]
      simp
    · intro hz
      rcases e.surjective z with ⟨c, rfl⟩
      refine ⟨c, ?_, rfl⟩
      change chapter03ClassModuleNorm A c = 1
      apply A.canonicalPositiveReal.injective
      rw [map_one]
      change (LastLib.Book06GlobalClassFieldTheory.Chapter01.classModule (K := K)).comp e c = 1 at hz
      rw [hmodule] at hz
      exact hz
  have hcompactCanonical : IsCompact
      (LastLib.Book06GlobalClassFieldTheory.Chapter01.classModuleOneSubgroup K :
        Set (LastLib.Book06GlobalClassFieldTheory.Chapter01.BookIdeleClassGroup K)) :=
    LastLib.Book06GlobalClassFieldTheory.Chapter01.classModule_kernel_compact (K := K)
  have himage : IsCompact
      (e.symm ''
        (LastLib.Book06GlobalClassFieldTheory.Chapter01.classModuleOneSubgroup K :
          Set (LastLib.Book06GlobalClassFieldTheory.Chapter01.BookIdeleClassGroup K))) :=
    hcompactCanonical.image hecont_symm
  have himage_eq : e.symm ''
        (LastLib.Book06GlobalClassFieldTheory.Chapter01.classModuleOneSubgroup K :
          Set (LastLib.Book06GlobalClassFieldTheory.Chapter01.BookIdeleClassGroup K)) =
      (chapter03ClassModuleOneSubgroup A : Set (Chapter03ClassGroup S_K)) := by
    rw [← hker]
    ext c
    constructor
    · rintro ⟨z, hz, rfl⟩
      rcases hz with ⟨c', hc', hzc'⟩
      have hce : e.symm z = c' := by
        rw [← hzc']
        exact e.symm_apply_apply c'
      rw [hce]
      exact hc'
    · intro hc
      refine ⟨e c, ?_, e.symm_apply_apply c⟩
      exact ⟨c, hc, rfl⟩
  rw [himage_eq] at himage
  exact himage

theorem chapter03_classNormQuotient_compact_canonical
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03AdelicModuleData N) :
    chapter03_classNormQuotient_compact (N := N) := by
  exact chapter03_classNormQuotient_compact_of_module_one_compact A
    (chapter03_classModuleOne_compact_canonical A)

theorem chapter03_normClassSubgroup_finiteIndex_canonical
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03AdelicModuleData N) :
    (chapter03NormClassSubgroup N).FiniteIndex := by
  exact chapter03_normClassSubgroup_finiteIndex_of_compact_quotient
    (chapter03_classNormQuotient_compact_canonical A)

theorem chapter03_classNormQuotient_finite_canonical
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03AdelicModuleData N) :
    Finite (Chapter03ClassNormQuotient N) := by
  exact chapter03_classNormQuotient_finite_of_compact_quotient
    (chapter03_classNormQuotient_compact_canonical A)

end
end LastLib.Book06GlobalClassFieldTheory.Chapter03
