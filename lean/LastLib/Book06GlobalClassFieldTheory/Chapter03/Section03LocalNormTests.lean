import LastLib.Book06GlobalClassFieldTheory.Chapter03.Section02OpenNormGroups

namespace LastLib.Book06GlobalClassFieldTheory.Chapter03

noncomputable section

open Filter Set
open scoped BigOperators RestrictedProduct IsMulCommutative

/-!
## 3.3. Local norm tests and the global kernel
-/

/-- The finite product of local factors above a fixed place. -/
abbrev Chapter03LocalNormFiber
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (v : Chapter03Place K) :=
  ∀ w : {w // w ∈ N.above v}, (S_L.localFactor w.1).carrier

/-- The product local norm at one place. -/
noncomputable def chapter03LocalNormAt
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (v : Chapter03Place K) :
    Chapter03LocalNormFiber N v →* (S_K.localFactor v).carrier where
  toFun z := ∏ w : {w // w ∈ N.above v}, N.localNorm v w.1 (z w)
  map_one' := by
    classical
    simp
  map_mul' x y := by
    classical
    simp [Finset.prod_mul_distrib]

theorem chapter03LocalNormAt_apply
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (v : Chapter03Place K)
    (z : Chapter03LocalNormFiber N v) :
    chapter03LocalNormAt N v z =
      ∏ w : {w // w ∈ N.above v}, N.localNorm v w.1 (z w) :=
  rfl

/-- Coordinatewise local solvability of the principal element `a` as an idèle norm. -/
def chapter03IsLocalElementNorm
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (a : Units K) : Prop :=
  ∀ v : Chapter03Place K,
    ∃ z : Chapter03LocalNormFiber N v,
      chapter03LocalNormAt N v z = S_K.embedding v a

/-- The global principal idèle is an idèle norm. -/
def chapter03IsIdeleElementNorm
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (a : Units K) : Prop :=
  ∃ y : Chapter03Ideles S_L,
    chapter03IdeleNorm N y = chapter03PrincipalIdeleHom S_K a

theorem chapter03_isIdeleElementNorm_iff_mem_ideleNormSubgroup
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (a : Units K) :
    chapter03IsIdeleElementNorm N a ↔
      chapter03PrincipalIdeleHom S_K a ∈ chapter03IdeleNormSubgroup N := by
  rfl

theorem chapter03_principal_idele_norm_iff_local
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (a : Units K) :
    chapter03IsIdeleElementNorm N a ↔ chapter03IsLocalElementNorm N a := by
  classical
  constructor
  · rintro ⟨y, hy⟩ v
    let z : Chapter03LocalNormFiber N v := fun w => y w.1
    refine ⟨z, ?_⟩
    have hv := congrArg (fun x : Chapter03Ideles S_K => x v) hy
    rw [chapter03LocalNormAt_apply]
    rw [Finset.univ_eq_attach]
    simp only [z]
    exact (Finset.prod_attach (N.above v)
      (fun w => N.localNorm v w (y w))).trans (by
        simpa [chapter03IdeleNorm_apply] using hv)
  · intro hlocal
    let good : Chapter03Place K → Prop := fun v =>
      S_K.finitePlace v ∧ N.unramified v ∧
        S_K.embedding v a ∈ (S_K.localFactor v).unit
    have hgood : ∀ᶠ v in cofinite, good v := by
      filter_upwards [N.eventually_finite_unramified,
        S_K.embedding_eventually_mem_unit a] with v hv hx
      exact ⟨hv.1, hv.2, hx⟩
    have hunit_vector : ∀ v, good v →
        ∃ z : Chapter03LocalNormFiber N v,
          (∀ w, z w ∈ (S_L.localFactor w.1).unit) ∧
            chapter03LocalNormAt N v z = S_K.embedding v a := by
      intro v hv
      let w₀ : {w // w ∈ N.above v} :=
        ⟨Classical.choose (N.above_nonempty v),
          Classical.choose_spec (N.above_nonempty v)⟩
      let y₀ : (S_L.localFactor w₀.1).carrier :=
        Classical.choose (N.localNorm_units_surjective hv.1 hv.2.1 w₀.1 w₀.2
          (S_K.embedding v a) hv.2.2)
      have hy₀ := Classical.choose_spec (N.localNorm_units_surjective hv.1 hv.2.1 w₀.1 w₀.2
        (S_K.embedding v a) hv.2.2)
      let z : Chapter03LocalNormFiber N v := fun w =>
        if h : w = w₀ then h ▸ y₀ else 1
      refine ⟨z, ?_, ?_⟩
      · intro w
        by_cases h : w = w₀
        · subst w
          simpa [z] using hy₀.1
        · simp [z, h]
      · rw [chapter03LocalNormAt_apply]
        rw [Finset.prod_eq_single_of_mem w₀ (Finset.mem_univ w₀)]
        · simpa [z] using hy₀.2
        · intro w hw hne
          simp [z, hne]
    let z : ∀ v, Chapter03LocalNormFiber N v := fun v =>
      if hv : good v then Classical.choose (hunit_vector v hv)
      else Classical.choose (hlocal v)
    have hz : ∀ v, chapter03LocalNormAt N v (z v) = S_K.embedding v a := by
      intro v
      by_cases hv : good v
      · simpa [z, hv] using (Classical.choose_spec (hunit_vector v hv)).2
      · simpa [z, hv] using (Classical.choose_spec (hlocal v))
    have hbelow : Filter.Tendsto N.below cofinite cofinite :=
      Filter.Tendsto.cofinite_of_finite_preimage_singleton (fun v => by
        refine (N.above v).finite_toSet.subset ?_
        intro w hw
        exact (N.mem_above_iff v w).2 (by simpa using hw))
    let y : Chapter03Ideles S_L :=
      ⟨fun w => z (N.below w)
          ⟨w, (N.mem_above_iff (N.below w) w).2 rfl⟩, by
        have hgood' : ∀ᶠ w in cofinite, good (N.below w) := hbelow hgood
        filter_upwards [hgood'] with w hw
        have hunit := (Classical.choose_spec
          (hunit_vector (N.below w) hw)).1
          ⟨w, (N.mem_above_iff (N.below w) w).2 rfl⟩
        have hzgood : z (N.below w) =
            Classical.choose (hunit_vector (N.below w) hw) := by
          exact dif_pos hw
        rw [hzgood]
        exact hunit⟩
    refine ⟨y, ?_⟩
    apply RestrictedProduct.ext
    intro v
    rw [chapter03IdeleNorm_apply]
    calc
      (N.above v).prod (fun w => N.localNorm v w (y w)) =
          (N.above v).attach.prod
            (fun w => N.localNorm v w.1 (z v w)) := by
        rw [← Finset.prod_attach (N.above v)
          (fun w => N.localNorm v w (y w))]
        apply Finset.prod_congr rfl
        intro w _
        rcases w with ⟨w, hwmem⟩
        have hwbelow : N.below w = v :=
          (N.mem_above_iff v w).1 hwmem
        change N.localNorm v w
            (z (N.below w)
              ⟨w, (N.mem_above_iff (N.below w) w).2 rfl⟩) =
          N.localNorm v w (z v ⟨w, hwmem⟩)
        cases hwbelow
        rfl
      _ = S_K.embedding v a := by
        have hv := hz v
        rw [chapter03LocalNormAt_apply] at hv
        rw [Finset.univ_eq_attach] at hv
        exact hv

/-- The field norm on global units, as the multiplicative homomorphism used by principal
idèles. -/
noncomputable def chapter03ElementNorm
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (_N : Chapter03NormData S_K S_L) : Units L →* Units K :=
  LastLib.Book06GlobalClassFieldTheory.Chapter01.fieldNormUnits K L

def chapter03ElementNormSubgroup
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) : Subgroup (Units K) :=
  (chapter03ElementNorm N).range

theorem chapter03_elementNorm_mem_iff
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (a : Units K) :
    a ∈ chapter03ElementNormSubgroup N ↔
      ∃ b : Units L, chapter03ElementNorm N b = a := by
  rfl

/- A field norm supplies compatible local preimages through the principal norm
component identity.  These implications keep the element, local-element, and
idele-element notions distinct while recording the direction that is always
valid. -/
theorem chapter03_elementNorm_implies_localElementNorm
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (a : Units K)
    (h : a ∈ chapter03ElementNormSubgroup N) :
    chapter03IsLocalElementNorm N a := by
  classical
  rcases (chapter03_elementNorm_mem_iff N a).1 h with ⟨b, hb⟩
  intro v
  let z : Chapter03LocalNormFiber N v := fun w => S_L.embedding w b
  refine ⟨z, ?_⟩
  rw [chapter03LocalNormAt_apply]
  rw [Finset.univ_eq_attach]
  simp only [z]
  exact (Finset.prod_attach (N.above v)
    (fun w => N.localNorm v w (S_L.embedding w b))).trans (by
      rw [← hb]
      exact N.principal_norm_component b v)

theorem chapter03_elementNorm_implies_ideleElementNorm
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (a : Units K)
    (h : a ∈ chapter03ElementNormSubgroup N) :
    chapter03IsIdeleElementNorm N a := by
  rcases (chapter03_elementNorm_mem_iff N a).1 h with ⟨b, hb⟩
  refine ⟨chapter03PrincipalIdeleHom S_L b, ?_⟩
  rw [chapter03_ideleNorm_principal]
  rw [← hb]
  rfl

/- A class norm is intentionally a separate predicate from an element norm. -/
def chapter03IsClassNorm
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (c : Chapter03ClassGroup S_K) : Prop :=
  ∃ d : Chapter03ClassGroup S_L, chapter03ClassNorm N d = c

theorem chapter03_isClassNorm_iff_mem_normClassSubgroup
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (c : Chapter03ClassGroup S_K) :
    chapter03IsClassNorm N c ↔ c ∈ chapter03NormClassSubgroup N := by
  rfl

@[simp] theorem chapter03_principal_class_is_identity
    {K : Type*} [Field K] [NumberField K]
    {S_K : Chapter03FieldIdeleData K} (a : Units K) :
    (QuotientGroup.mk' (chapter03PrincipalSubgroup S_K)
      (chapter03PrincipalIdeleHom S_K a)) = 1 := by
  exact chapter03_class_of_principal S_K a

theorem chapter03_principal_class_is_classNorm
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (a : Units K) :
    chapter03IsClassNorm N
      (QuotientGroup.mk' (chapter03PrincipalSubgroup S_K)
        (chapter03PrincipalIdeleHom S_K a)) := by
  refine ⟨1, ?_⟩
  rw [map_one]
  exact (chapter03_principal_class_is_identity a).symm

/-!
The theorem below records the local norm test for principal elements.  Its proof uses the
eventual unit-surjectivity in `Chapter03NormData` to patch local preimages into a restricted
product.  This is exactly where the element statement differs from the automatic principal
class statement above.
-/

theorem chapter03_principal_idele_is_norm_iff_local_test
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (a : Units K) :
    chapter03IsIdeleElementNorm N a ↔
      ∀ v : Chapter03Place K, ∃ z : Chapter03LocalNormFiber N v,
        chapter03LocalNormAt N v z = S_K.embedding v a := by
  exact chapter03_principal_idele_norm_iff_local N a

/-!
### Reciprocity and the one-sided global kernel inclusion
-/

theorem chapter03_local_reciprocity_kills_norm
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03ArtinReciprocityData N) (v : Chapter03Place K)
    (w : Chapter03Place L) (hw : w ∈ N.above v)
    (x : (S_L.localFactor w).carrier) :
    A.localArtin v (N.localNorm v w x) = 1 := by
  rw [A.localArtin_canonical v w hw]
  rw [N.localNorm_canonical v w hw x]
  rw [← A.localReciprocity_norm v w hw]
  exact chapter03_abelianized_local_artin_kills_norm
    (A.localDecompositionGroup v w).subtype (A.localReciprocity v w hw)
      (S_L.canonicalFactor w x)

theorem chapter03_artin_norm_idele
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03ArtinReciprocityData N) (y : Chapter03Ideles S_L) :
    A.globalArtin (chapter03IdeleNorm N y) = 1 := by
  obtain ⟨s, hs, hprod⟩ := A.globalArtin_local_product (chapter03IdeleNorm N y)
  rw [hprod]
  apply Finset.prod_eq_one
  intro v hv
  rw [chapter03IdeleNorm_apply]
  rw [map_prod]
  apply Finset.prod_eq_one
  intro w hw
  exact chapter03_local_reciprocity_kills_norm A v w hw (y w)

theorem chapter03_classNorm_range_le_artin_kernel
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03ArtinReciprocityData N) :
    (chapter03ClassNorm N).range ≤ (chapter03ClassArtin A).ker := by
  intro c hc
  rcases hc with ⟨d, rfl⟩
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
    (chapter03PrincipalSubgroup S_L) d
  rw [MonoidHom.mem_ker, chapter03ClassNorm_mk, chapter03ClassArtin_mk]
  exact chapter03_artin_norm_idele A y

/- The reverse inclusion is deliberately absent: it is the global norm theorem deferred to the
class-formation argument, and it cannot be proved by independent coordinatewise tests. -/

end
end LastLib.Book06GlobalClassFieldTheory.Chapter03
