import LastLib.Book06GlobalClassFieldTheory.Chapter02.Dependencies
import LastLib.Book06GlobalClassFieldTheory.Chapter05.Dependencies
import LastLib.Book06GlobalClassFieldTheory.Chapter09.Section01TheKnotBetweenLocalAndGlobalNorms

namespace LastLib.Book06GlobalClassFieldTheory.Chapter09


noncomputable section

/-!
The maximal abelian subextension of a finite Galois extension is the fixed field
of the commutator subgroup.  This definition is canonical and is used for the
global norm limitation theorem.
-/
def chapter09GlobalMaximalAbelianSubextension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    IntermediateField K L :=
  IntermediateField.fixedField (commutator (Gal(L / K)))

instance chapter09GlobalMaximalAbelianSubextension.isGalois
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    IsGalois K (chapter09GlobalMaximalAbelianSubextension (K := K) (L := L)) := by
  unfold chapter09GlobalMaximalAbelianSubextension
  infer_instance

def chapter09GlobalGaloisAbelianization
    (K L : Type*) [Field K] [Field L] [Algebra K L] [IsGalois K L] : Type _ :=
  Abelianization (Gal(L / K))

/-!
For a local decomposition group identified with the local Galois group, the
local maximal abelian subextension is the fixed field of the image of its
commutator subgroup.
-/
def chapter09LocalMaximalAbelianSubextension
    {K_v L_w D : Type*} [Field K_v] [Field L_w] [Algebra K_v L_w]
    [Group D] (e : D ≃* Gal(L_w / K_v)) :
    IntermediateField K_v L_w :=
  IntermediateField.fixedField ((commutator D).map e.toMonoidHom)

theorem chapter09_local_maximal_abelian_subextension_eq_canonical
    {K_v L_w D : Type*} [Field K_v] [Field L_w] [Algebra K_v L_w]
    [Group D] (e : D ≃* Gal(L_w / K_v)) :
    chapter09LocalMaximalAbelianSubextension (K_v := K_v) (L_w := L_w) e =
      IntermediateField.fixedField (commutator (Gal(L_w / K_v))) := by
  unfold chapter09LocalMaximalAbelianSubextension
  rw [map_commutator_eq, e.toMonoidHom.range_eq_top_of_surjective e.surjective]
  rfl

def chapter09LocalFieldNormSubgroup
    (K_v L_w : Type*) [Field K_v] [Field L_w] [Algebra K_v L_w]
    [FiniteDimensional K_v L_w] : Subgroup K_vˣ :=
  chapter09FieldNormSubgroup K_v L_w

/-!
The local norm-limitation argument uses the local reciprocity quotient for the
extension and for its maximal abelian subextension.  The two quotient maps
must be compared with one common abelianized target; this is the local
counterpart of `Chapter09GlobalClassFormationData` below.
-/
structure Chapter09LocalClassFormationData
    {K_v L_w D : Type*} [Field K_v] [Field L_w] [Algebra K_v L_w]
    [FiniteDimensional K_v L_w] [IsGalois K_v L_w] [Group D]
    (e : D ≃* Gal(L_w / K_v)) where
  artin : K_vˣ →* Abelianization (Gal(L_w / K_v))
  leftReciprocity :
    (K_vˣ ⧸ chapter09LocalFieldNormSubgroup K_v L_w) ≃*
      Abelianization (Gal(L_w / K_v))
  rightReciprocity :
    (K_vˣ ⧸ chapter09LocalFieldNormSubgroup K_v
      (chapter09LocalMaximalAbelianSubextension (K_v := K_v) (L_w := L_w) e)) ≃*
      Abelianization (Gal(L_w / K_v))
  leftReciprocity_compatibility :
    leftReciprocity.toMonoidHom.comp
        (QuotientGroup.mk'
          (chapter09LocalFieldNormSubgroup K_v L_w)) = artin
  rightReciprocity_compatibility :
    rightReciprocity.toMonoidHom.comp
        (QuotientGroup.mk'
          (chapter09LocalFieldNormSubgroup K_v
        (chapter09LocalMaximalAbelianSubextension
              (K_v := K_v) (L_w := L_w) e))) = artin

/-!
The preceding local reciprocity interface already gives the quotient
equivalence needed here.  This bridge only transports its kernel from the
recorded local norm to the canonical field norm; it does not assume norm
limitation.
-/
noncomputable def chapter09LocalQuotientEquivOfReciprocity
    {K_v E D : Type*} [Field K_v] [Field E] [Algebra K_v E]
    [FiniteDimensional K_v E] [Group D]
    (R : LastLib.Book06GlobalClassFieldTheory.Chapter02.Chapter02LocalReciprocityData
      K_vˣ Eˣ D)
    (h : R.norm = chapter09FieldNormUnitHom K_v E) :
    (K_vˣ ⧸ chapter09LocalFieldNormSubgroup K_v E) ≃*
      Abelianization D := by
  have hker : R.reciprocity.ker = chapter09LocalFieldNormSubgroup K_v E := by
    rw [R.kernel_eq_norm_range, h]
    rfl
  exact
    (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective R.reciprocity
        R.reciprocity_surjective)

/-!
This is the local finite-reciprocity input in the form consumed by the
chapter's common class-formation record.  The target of the right-hand map is
the same abelianization because the maximal abelian local field is the fixed
field of the commutator subgroup.
-/
structure Chapter09LocalFiniteReciprocityBridge
    {K_v L_w D : Type*} [Field K_v] [Field L_w] [Algebra K_v L_w]
    [FiniteDimensional K_v L_w] [IsGalois K_v L_w] [Group D]
    (e : D ≃* Gal(L_w / K_v)) where
  left : LastLib.Book06GlobalClassFieldTheory.Chapter02.Chapter02LocalReciprocityData
    K_vˣ L_wˣ (Gal(L_w / K_v))
  right : LastLib.Book06GlobalClassFieldTheory.Chapter02.Chapter02LocalReciprocityData
    K_vˣ
      (chapter09LocalMaximalAbelianSubextension
        (K_v := K_v) (L_w := L_w) e)ˣ (Gal(L_w / K_v))
  left_norm : left.norm = chapter09FieldNormUnitHom K_v L_w
  right_norm : right.norm = chapter09FieldNormUnitHom K_v
    (chapter09LocalMaximalAbelianSubextension
      (K_v := K_v) (L_w := L_w) e)
  reciprocity_eq : left.reciprocity = right.reciprocity

noncomputable def Chapter09LocalFiniteReciprocityBridge.toClassFormationData
    {K_v L_w D : Type*} [Field K_v] [Field L_w] [Algebra K_v L_w]
    [FiniteDimensional K_v L_w] [IsGalois K_v L_w] [Group D]
    (e : D ≃* Gal(L_w / K_v))
    (B : Chapter09LocalFiniteReciprocityBridge e) :
    Chapter09LocalClassFormationData e :=
  { artin := B.left.reciprocity
    leftReciprocity := chapter09LocalQuotientEquivOfReciprocity B.left B.left_norm
    rightReciprocity :=
      chapter09LocalQuotientEquivOfReciprocity
        (K_v := K_v)
        (E := chapter09LocalMaximalAbelianSubextension
          (K_v := K_v) (L_w := L_w) e)
        B.right B.right_norm
    leftReciprocity_compatibility := by sorry
    rightReciprocity_compatibility := by sorry }

theorem chapter09_local_maximal_abelian_subextension_def
    {K_v L_w D : Type*} [Field K_v] [Field L_w] [Algebra K_v L_w]
    [Group D] (e : D ≃* Gal(L_w / K_v)) :
    chapter09LocalMaximalAbelianSubextension (K_v := K_v) (L_w := L_w) e =
      IntermediateField.fixedField ((commutator D).map e.toMonoidHom) := by
  rfl

/-!
The comparison data below uses one common base idele class group.  For an
intermediate field `M`, the descent map expresses the norm from `L` to `M`;
its two compatibility equations are the functoriality bridges used to
compare the two class norms.  The maximal-abelian specialization and its
finite-reciprocity input are supplied separately below.  Norm maps on ideles
are not generally surjective, so no surjectivity is built into this datum.
-/
structure Chapter09ClassNormComparisonData
    (K L I_K I_L I_M : Type*)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [CommGroup I_K] [CommGroup I_L] [CommGroup I_M]
    (M : IntermediateField K L) where
  basePrincipal : Kˣ →* I_K
  basePrincipal_injective : Function.Injective basePrincipal
  principalL : Lˣ →* I_L
  principalL_injective : Function.Injective principalL
  principalM : Mˣ →* I_M
  principalM_injective : Function.Injective principalM
  ideleNormL : I_L →* I_K
  ideleNormM : I_M →* I_K
  left_norm_compatibility :
    ideleNormL.comp principalL =
      basePrincipal.comp (chapter09FieldNormUnitHom K L)
  right_norm_compatibility :
    ideleNormM.comp principalM =
      basePrincipal.comp (chapter09FieldNormUnitHom K M)
  descent : I_L →* I_M
  principal_descent_compatibility :
    descent.comp principalL =
      principalM.comp (chapter09FieldNormUnitHom M L)
  ideleNorm_descent_compatibility :
    ideleNormM.comp descent = ideleNormL

def chapter09ClassNormComparisonData.leftIdeleData
    {K L I_K I_L I_M : Type*}
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [CommGroup I_K] [CommGroup I_L] [CommGroup I_M]
    {M : IntermediateField K L}
    (C : Chapter09ClassNormComparisonData K L I_K I_L I_M M) :
    Chapter09IdeleNormData K L I_K I_L :=
  { principalK := C.basePrincipal
    principalL := C.principalL
    ideleNorm := C.ideleNormL
    principalK_injective := C.basePrincipal_injective
    principalL_injective := C.principalL_injective
    norm_compatibility := C.left_norm_compatibility }

def chapter09ClassNormComparisonData.rightIdeleData
    {K L I_K I_L I_M : Type*}
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [CommGroup I_K] [CommGroup I_L] [CommGroup I_M]
    {M : IntermediateField K L}
    (C : Chapter09ClassNormComparisonData K L I_K I_L I_M M) :
    Chapter09IdeleNormData K M I_K I_M :=
  { principalK := C.basePrincipal
    principalL := C.principalM
    ideleNorm := C.ideleNormM
    principalK_injective := C.basePrincipal_injective
    principalL_injective := C.principalM_injective
    norm_compatibility := C.right_norm_compatibility }

abbrev chapter09CommonIdeleClassGroup
    {K I_K : Type*} [Field K] [CommGroup I_K]
    (principalK : Kˣ →* I_K) : Type _ :=
  I_K ⧸ principalK.range

def chapter09CommonClassNormGroup
    {K I_K I_L : Type*} [Field K] [CommGroup I_K] [CommGroup I_L]
    (principalK : Kˣ →* I_K) (ideleNorm : I_L →* I_K) :
    Subgroup (chapter09CommonIdeleClassGroup principalK) :=
  ((QuotientGroup.mk' principalK.range).comp ideleNorm).range

theorem chapter09_common_class_norm_group_left
    {K L I_K I_L I_M : Type*}
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [CommGroup I_K] [CommGroup I_L] [CommGroup I_M]
    {M : IntermediateField K L}
    (C : Chapter09ClassNormComparisonData K L I_K I_L I_M M) :
    chapter09ClassNormGroup (chapter09ClassNormComparisonData.leftIdeleData C) =
      chapter09CommonClassNormGroup C.basePrincipal C.ideleNormL := by
  rfl

theorem chapter09_common_class_norm_group_right
    {K L I_K I_L I_M : Type*}
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [CommGroup I_K] [CommGroup I_L] [CommGroup I_M]
    {M : IntermediateField K L}
    (C : Chapter09ClassNormComparisonData K L I_K I_L I_M M) :
    chapter09ClassNormGroup (chapter09ClassNormComparisonData.rightIdeleData C) =
      chapter09CommonClassNormGroup C.basePrincipal C.ideleNormM := by
  rfl

/-!
The displayed descent compatibility gives only the easy inclusion of class
norm ranges.  Equality is the separate global norm-limitation theorem; it is
not a formal consequence of surjectivity of the idele norm.
-/
theorem chapter09_common_class_norm_group_left_le_right
    {K L I_K I_L I_M : Type*}
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [CommGroup I_K] [CommGroup I_L] [CommGroup I_M]
    {M : IntermediateField K L}
    (C : Chapter09ClassNormComparisonData K L I_K I_L I_M M) :
    chapter09CommonClassNormGroup C.basePrincipal C.ideleNormL ≤
      chapter09CommonClassNormGroup C.basePrincipal C.ideleNormM := by
  sorry

/-!
The functorial comparison record alone supplies only the inclusion above.  The
reverse inclusion and the degree computation use finite reciprocity for the two
class-norm quotients.  This record exposes that missing, reusable interface:
both quotient maps are identified with one common finite target, and the target
has the degree of the maximal abelian subextension.
-/
structure Chapter09GlobalClassFormationData
    {K L I_K I_L I_M : Type*}
    [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L]
    [FiniteDimensional K L] [IsGalois K L] [Fintype (Gal(L / K))]
    [CommGroup I_K] [CommGroup I_L] [CommGroup I_M]
    (C : Chapter09ClassNormComparisonData K L I_K I_L I_M
      (chapter09GlobalMaximalAbelianSubextension (K := K) (L := L))) where
  artin : chapter09CommonIdeleClassGroup C.basePrincipal →*
    Abelianization (Gal(L / K))
  leftReciprocity :
    (chapter09CommonIdeleClassGroup C.basePrincipal ⧸
      chapter09CommonClassNormGroup C.basePrincipal C.ideleNormL) ≃*
        Abelianization (Gal(L / K))
  rightReciprocity :
    (chapter09CommonIdeleClassGroup C.basePrincipal ⧸
      chapter09CommonClassNormGroup C.basePrincipal C.ideleNormM) ≃*
        Abelianization (Gal(L / K))
  leftReciprocity_compatibility :
    leftReciprocity.toMonoidHom.comp
        (QuotientGroup.mk'
          (chapter09CommonClassNormGroup C.basePrincipal C.ideleNormL)) = artin
  rightReciprocity_compatibility :
    rightReciprocity.toMonoidHom.comp
        (QuotientGroup.mk'
          (chapter09CommonClassNormGroup C.basePrincipal C.ideleNormM)) = artin

/-!
The finite reciprocity records from Chapter 5 use the same quotient, but keep
the cap-product equivalence in the direction opposite to the reciprocity map.
The following bridge makes the quotient identifications and the comparison of
the two abelianized Galois targets explicit.
-/
structure Chapter09GlobalFiniteReciprocityBridge
    {K L I_K I_L I_M C_L C_M : Type*}
    [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L]
    [FiniteDimensional K L] [IsGalois K L] [Fintype (Gal(L / K))]
    [CommGroup I_K] [CommGroup I_L] [CommGroup I_M]
    [CommGroup C_L] [CommGroup C_M]
    (C : Chapter09ClassNormComparisonData K L I_K I_L I_M
      (chapter09GlobalMaximalAbelianSubextension (K := K) (L := L))) where
  left : LastLib.Book06GlobalClassFieldTheory.Chapter05.Chapter05ClassFormationInput
    K L I_K I_L (chapter09CommonIdeleClassGroup C.basePrincipal) C_L
  right : LastLib.Book06GlobalClassFieldTheory.Chapter05.Chapter05ClassFormationInput
    K (chapter09GlobalMaximalAbelianSubextension (K := K) (L := L)) I_K I_M
      (chapter09CommonIdeleClassGroup C.basePrincipal) C_M
  left_classMapK : left.classMapK = QuotientGroup.mk' C.basePrincipal.range
  right_classMapK : right.classMapK = QuotientGroup.mk' C.basePrincipal.range
  left_classMapL_surjective : Function.Surjective left.classMapL
  right_classMapL_surjective : Function.Surjective right.classMapL
  right_target_equiv :
    Abelianization (Gal(
      chapter09GlobalMaximalAbelianSubextension (K := K) (L := L) / K)) ≃*
      Abelianization (Gal(L / K))
  right_artin_compatibility :
    right_target_equiv.toMonoidHom.comp
        (LastLib.Book06GlobalClassFieldTheory.Chapter05.chapter05InputGlobalArtin
          right) =
      LastLib.Book06GlobalClassFieldTheory.Chapter05.chapter05InputGlobalArtin left

noncomputable def Chapter09GlobalFiniteReciprocityBridge.toClassFormationData
    {K L I_K I_L I_M C_L C_M : Type*}
    [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L]
    [FiniteDimensional K L] [IsGalois K L] [Fintype (Gal(L / K))]
    [CommGroup I_K] [CommGroup I_L] [CommGroup I_M]
    [CommGroup C_L] [CommGroup C_M]
    (C : Chapter09ClassNormComparisonData K L I_K I_L I_M
      (chapter09GlobalMaximalAbelianSubextension (K := K) (L := L)))
    (B : Chapter09GlobalFiniteReciprocityBridge
      (C_L := C_L) (C_M := C_M) C) :
    Chapter09GlobalClassFormationData C := by
  have hleft :
      LastLib.Book06GlobalClassFieldTheory.Chapter05.chapter05InputNormSubgroup
          B.left =
        chapter09CommonClassNormGroup C.basePrincipal C.ideleNormL := by
    sorry
  have hright :
      LastLib.Book06GlobalClassFieldTheory.Chapter05.chapter05InputNormSubgroup
          B.right =
        chapter09CommonClassNormGroup C.basePrincipal C.ideleNormM := by
    sorry
  refine
    { artin :=
        LastLib.Book06GlobalClassFieldTheory.Chapter05.chapter05InputGlobalArtin
          B.left
      leftReciprocity :=
        (QuotientGroup.quotientMulEquivOfEq hleft).symm.trans
          (LastLib.Book06GlobalClassFieldTheory.Chapter05.chapter05InputCapProductEquiv
            B.left).symm
      rightReciprocity :=
        ((QuotientGroup.quotientMulEquivOfEq hright).symm.trans
          (LastLib.Book06GlobalClassFieldTheory.Chapter05.chapter05InputCapProductEquiv
            B.right).symm).trans B.right_target_equiv
      leftReciprocity_compatibility := by sorry
      rightReciprocity_compatibility := by sorry }

theorem chapter09_global_class_norm_limitation
    {K L I_K I_L I_M : Type*}
    [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L]
    [FiniteDimensional K L] [IsGalois K L] [Fintype (Gal(L / K))]
    [CommGroup I_K] [CommGroup I_L] [CommGroup I_M]
    (C : Chapter09ClassNormComparisonData K L I_K I_L I_M
      (chapter09GlobalMaximalAbelianSubextension (K := K) (L := L)))
    (R : Chapter09GlobalClassFormationData C) :
    chapter09CommonClassNormGroup C.basePrincipal C.ideleNormL =
      chapter09CommonClassNormGroup C.basePrincipal C.ideleNormM := by
  sorry

theorem chapter09_global_class_norm_limitation_of_finite_reciprocity
    {K L I_K I_L I_M C_L C_M : Type*}
    [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L]
    [FiniteDimensional K L] [IsGalois K L] [Fintype (Gal(L / K))]
    [CommGroup I_K] [CommGroup I_L] [CommGroup I_M]
    [CommGroup C_L] [CommGroup C_M]
    (C : Chapter09ClassNormComparisonData K L I_K I_L I_M
      (chapter09GlobalMaximalAbelianSubextension (K := K) (L := L)))
    (B : Chapter09GlobalFiniteReciprocityBridge
      (C_L := C_L) (C_M := C_M) C) :
    chapter09CommonClassNormGroup C.basePrincipal C.ideleNormL =
      chapter09CommonClassNormGroup C.basePrincipal C.ideleNormM := by
  exact chapter09_global_class_norm_limitation C B.toClassFormationData

theorem chapter09_global_class_norm_limitation_for_maximal_abelian
    {K L I_K I_L I_M : Type*}
    [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L]
    [FiniteDimensional K L] [IsGalois K L] [Fintype (Gal(L / K))]
    [CommGroup I_K] [CommGroup I_L] [CommGroup I_M]
    (C : Chapter09ClassNormComparisonData K L I_K I_L I_M
      (chapter09GlobalMaximalAbelianSubextension (K := K) (L := L)))
    (R : Chapter09GlobalClassFormationData C) :
    chapter09CommonClassNormGroup C.basePrincipal C.ideleNormL =
      chapter09CommonClassNormGroup C.basePrincipal C.ideleNormM := by
  exact chapter09_global_class_norm_limitation C R

/-!
The index statement is phrased with `Module.finrank` for the canonical fixed
field `M/K` and with the canonical abelianization for the abstract
group-theoretic degree.
-/
theorem chapter09_global_class_norm_index
    {K L I_K I_L I_M : Type*}
    [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L]
    [FiniteDimensional K L]
    [IsGalois K L] [Fintype (Gal(L / K))]
    [CommGroup I_K] [CommGroup I_L] [CommGroup I_M]
    (C : Chapter09ClassNormComparisonData K L I_K I_L I_M
      (chapter09GlobalMaximalAbelianSubextension (K := K) (L := L)))
    (R : Chapter09GlobalClassFormationData C) :
    (chapter09CommonClassNormGroup C.basePrincipal C.ideleNormL).index =
        Module.finrank K
          (chapter09GlobalMaximalAbelianSubextension (K := K) (L := L)) ∧
      Module.finrank K
          (chapter09GlobalMaximalAbelianSubextension (K := K) (L := L)) =
        Nat.card (Abelianization (Gal(L / K))) := by
  sorry

theorem chapter09_global_class_norm_index_as_abelianization
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L]
    [FiniteDimensional K L] [IsGalois K L] [Fintype (Gal(L / K))] :
    Module.finrank K
        (chapter09GlobalMaximalAbelianSubextension (K := K) (L := L)) =
      Nat.card (chapter09GlobalGaloisAbelianization K L) := by
  sorry

theorem chapter09_local_norm_limitation
    {K_v L_w D : Type*} [Field K_v] [Field L_w] [Algebra K_v L_w]
    [FiniteDimensional K_v L_w] [IsGalois K_v L_w] [Group D]
    (e : D ≃* Gal(L_w / K_v))
    (R : Chapter09LocalClassFormationData e) :
    chapter09LocalFieldNormSubgroup K_v L_w =
      chapter09LocalFieldNormSubgroup K_v
        (chapter09LocalMaximalAbelianSubextension (K_v := K_v) (L_w := L_w) e) := by
  sorry

/-!
The global fixed-field construction and the local fixed-field construction
are intentionally separate.  No declaration below identifies a completion of
the global maximal abelian field with the local maximal abelian field.
-/
def chapter09LocalGlobalMaximalAbelianComparison
    {K_v L_w : Type*} [Field K_v] [Field L_w] [Algebra K_v L_w]
    (localMax globalCandidate : IntermediateField K_v L_w) : Prop :=
  Nonempty (localMax ≃ₐ[K_v] globalCandidate)

def chapter09LocalGlobalMaximalAbelianAgreement
    {K L D : Type*} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] [Group D] (e : D ≃* Gal(L / K))
    (globalCandidate : IntermediateField K L) : Prop :=
  chapter09LocalGlobalMaximalAbelianComparison
    (chapter09LocalMaximalAbelianSubextension (K_v := K) (L_w := L) e)
    globalCandidate

/-!
For a non-Galois extension there is no canonical use of the preceding global
definition.  A chosen Galois closure gives a field in the closure, but a
separate descent and norm comparison is still required to make a statement
about the original extension.
-/
structure Chapter09GaloisClosureData
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] where
  closure : Type*
  [closureField : Field closure]
  [closureAlgebra : Algebra K closure]
  embedding : L →ₐ[K] closure
  [closureFiniteDimensional : FiniteDimensional K closure]
  [closure_isGalois : IsGalois K closure]
  closure_generated_by_conjugates :
    IntermediateField.adjoin K
        (⋃ σ : Gal(closure / K), σ '' Set.range embedding) = ⊤

def chapter09GaloisClosureMaximalAbelianSubextension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (C : Chapter09GaloisClosureData K L) :
    (letI := C.closureField
     letI := C.closureAlgebra
     IntermediateField K C.closure) :=
  letI := C.closureField
  letI := C.closureAlgebra
  letI := C.closureFiniteDimensional
  letI := C.closure_isGalois
  IntermediateField.fixedField (commutator (Gal(C.closure / K)))

end

end LastLib.Book06GlobalClassFieldTheory.Chapter09
