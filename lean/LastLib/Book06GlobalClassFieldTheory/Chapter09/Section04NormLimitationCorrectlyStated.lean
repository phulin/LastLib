import LastLib.Book06GlobalClassFieldTheory.Chapter09.Section03WhyCyclicityCannotBeDropped

namespace LastLib.Book06GlobalClassFieldTheory.Chapter09

noncomputable section

/-!
The maximal abelian subextension of a finite Galois extension is the fixed field
of the commutator subgroup.  This definition is canonical and is used for the
global norm limitation theorem.
-/
def chapter09GlobalMaximalAbelianSubextension
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    IntermediateField K L :=
  IntermediateField.fixedField (commutator (Gal(L / K)))

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

def chapter09LocalFieldNormSubgroup
    (K_v L_w : Type*) [Field K_v] [Field L_w] [Algebra K_v L_w]
    [FiniteDimensional K_v L_w] : Subgroup K_vˣ :=
  chapter09FieldNormSubgroup K_v L_w

theorem chapter09_local_maximal_abelian_subextension_def
    {K_v L_w D : Type*} [Field K_v] [Field L_w] [Algebra K_v L_w]
    [Group D] (e : D ≃* Gal(L_w / K_v)) :
    chapter09LocalMaximalAbelianSubextension (K_v := K_v) (L_w := L_w) e =
      IntermediateField.fixedField ((commutator D).map e.toMonoidHom) := by
  rfl

/-!
The comparison data below uses one common base idele class group.  The
descent map expresses the norm from `L` to its maximal abelian subextension
`M`; its two compatibility equations are the functoriality bridges used to
compare the two class norms.
-/
structure Chapter09ClassNormComparisonData
    (K L I_K I_L I_M : Type*)
    [Field K] [Field L] [Algebra K L]
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
  descent_surjective : Function.Surjective descent
  principal_descent_compatibility :
    descent.comp principalL =
      principalM.comp (chapter09FieldNormUnitHom M L)
  ideleNorm_descent_compatibility :
    ideleNormM.comp descent = ideleNormL

def chapter09ClassNormComparisonData.leftIdeleData
    {K L I_K I_L I_M : Type*}
    [Field K] [Field L] [Algebra K L]
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
    [Field K] [Field L] [Algebra K L]
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
    [Field K] [Field L] [Algebra K L]
    [CommGroup I_K] [CommGroup I_L] [CommGroup I_M]
    {M : IntermediateField K L}
    (C : Chapter09ClassNormComparisonData K L I_K I_L I_M M) :
    chapter09ClassNormGroup (chapter09ClassNormComparisonData.leftIdeleData C) =
      chapter09CommonClassNormGroup C.basePrincipal C.ideleNormL := by
  rfl

theorem chapter09_common_class_norm_group_right
    {K L I_K I_L I_M : Type*}
    [Field K] [Field L] [Algebra K L]
    [CommGroup I_K] [CommGroup I_L] [CommGroup I_M]
    {M : IntermediateField K L}
    (C : Chapter09ClassNormComparisonData K L I_K I_L I_M M) :
    chapter09ClassNormGroup (chapter09ClassNormComparisonData.rightIdeleData C) =
      chapter09CommonClassNormGroup C.basePrincipal C.ideleNormM := by
  rfl

theorem chapter09_global_class_norm_limitation
    {K L I_K I_L I_M : Type*}
    [Field K] [Field L] [Algebra K L]
    [CommGroup I_K] [CommGroup I_L] [CommGroup I_M]
    {M : IntermediateField K L}
    (C : Chapter09ClassNormComparisonData K L I_K I_L I_M M) :
    chapter09CommonClassNormGroup C.basePrincipal C.ideleNormL =
      chapter09CommonClassNormGroup C.basePrincipal C.ideleNormM := by
  sorry

theorem chapter09_global_class_norm_limitation_for_maximal_abelian
    {K L I_K I_L I_M : Type*}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Fintype (Gal(L / K))]
    [CommGroup I_K] [CommGroup I_L] [CommGroup I_M]
    (C : Chapter09ClassNormComparisonData K L I_K I_L I_M
      (chapter09GlobalMaximalAbelianSubextension (K := K) (L := L))) :
    chapter09CommonClassNormGroup C.basePrincipal C.ideleNormL =
      chapter09CommonClassNormGroup C.basePrincipal C.ideleNormM := by
  exact chapter09_global_class_norm_limitation C

/-!
The index statement is phrased with `Module.finrank` for the canonical fixed
field `M/K` and with the canonical abelianization for the abstract
group-theoretic degree.
-/
theorem chapter09_global_class_norm_index
    {K L I_K I_L I_M : Type*}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [IsGalois K L] [Fintype (Gal(L / K))]
    [CommGroup I_K] [CommGroup I_L] [CommGroup I_M]
    (C : Chapter09ClassNormComparisonData K L I_K I_L I_M
      (chapter09GlobalMaximalAbelianSubextension (K := K) (L := L))) :
    (chapter09CommonClassNormGroup C.basePrincipal C.ideleNormL).index =
        Module.finrank K
          (chapter09GlobalMaximalAbelianSubextension (K := K) (L := L)) ∧
      Module.finrank K
          (chapter09GlobalMaximalAbelianSubextension (K := K) (L := L)) =
        Nat.card (Abelianization (Gal(L / K))) := by
  sorry

theorem chapter09_global_class_norm_index_as_abelianization
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Fintype (Gal(L / K))] :
    Module.finrank K
        (chapter09GlobalMaximalAbelianSubextension (K := K) (L := L)) =
      Nat.card (chapter09GlobalGaloisAbelianization K L) := by
  sorry

theorem chapter09_local_norm_limitation
    {K_v L_w D : Type*} [Field K_v] [Field L_w] [Algebra K_v L_w]
    [FiniteDimensional K_v L_w] [IsGalois K_v L_w] [Group D]
    (e : D ≃* Gal(L_w / K_v)) :
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
    (K L : Type*) [Field K] [Field L] [Algebra K L] where
  closure : Type*
  [closureField : Field closure]
  [closureAlgebra : Algebra K closure]
  embedding : L →ₐ[K] closure
  closure_isGalois : IsGalois K closure

def chapter09GaloisClosureMaximalAbelianSubextension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (C : Chapter09GaloisClosureData K L) :
    (letI := C.closureField
     letI := C.closureAlgebra
     IntermediateField K C.closure) :=
  letI := C.closureField
  letI := C.closureAlgebra
  letI := C.closure_isGalois
  IntermediateField.fixedField (commutator (Gal(C.closure / K)))

end

end LastLib.Book06GlobalClassFieldTheory.Chapter09
