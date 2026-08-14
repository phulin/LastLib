import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter03.Dependencies

/-!
# 3.2 The Amitsur equalizer
-/

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter03

open scoped TensorProduct

theorem chapter03_amitsur_unit_injective
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] :
    Function.Injective (Algebra.linearMap A B) := by
  exact FaithfulSMul.algebraMap_injective A B

theorem chapter03_amitsur_exact
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] :
    Function.Exact (Algebra.linearMap A B) (chapter03AmitsurDifference A B) := by
  apply LinearMap.exact_iff.mpr
  have h : Function.Exact (Algebra.linearMap A B)
      (Algebra.TensorProduct.includeLeftSubRight A B) :=
    Algebra.IsEffective.of_faithfullyFlat A B
  rw [LinearMap.exact_iff] at h
  have heq : Algebra.TensorProduct.includeLeftSubRight A B =
      -(chapter03AmitsurDifference A B) := by
    ext b
    change b ⊗ₜ[A] (1 : B) - (1 : B) ⊗ₜ[A] b =
      -((1 : B) ⊗ₜ[A] b - b ⊗ₜ[A] (1 : B))
    abel
  calc
    (chapter03AmitsurDifference A B).ker =
        (-(chapter03AmitsurDifference A B)).ker := by
      ext x
      change (chapter03AmitsurDifference A B) x = 0 ↔
        -(chapter03AmitsurDifference A B x) = 0
      exact neg_eq_zero.symm
    _ = (Algebra.TensorProduct.includeLeftSubRight A B).ker :=
      congrArg LinearMap.ker heq.symm
    _ = (Algebra.linearMap A B).range := h

theorem chapter03_amitsur_equalizer_eq_range
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] :
    chapter03AmitsurEqualizer A B = Set.range (algebraMap A B) := by
  have h := Algebra.IsEffective.eqLocus_includeLeft_includeRight
    (R := A) (S := B) (Algebra.IsEffective.of_faithfullyFlat A B)
  ext b
  have hb := Set.ext_iff.mp h b
  change b ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] b ↔
    b ∈ Set.range (algebraMap A B) at hb
  change chapter03AmitsurD0 A B b = chapter03AmitsurD1 A B b ↔
    b ∈ Set.range (algebraMap A B)
  rw [chapter03AmitsurD0_apply, chapter03AmitsurD1_apply]
  constructor
  · intro h'
    exact hb.mp h'.symm
  · intro h'
    exact (hb.mpr h').symm

theorem chapter03_amitsur_equalizer_iff
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] (b : B) :
    b ∈ chapter03AmitsurEqualizer A B ↔ ∃ a : A, algebraMap A B a = b := by
  rw [chapter03_amitsur_equalizer_eq_range]
  rfl

theorem chapter03_module_amitsur_augmentation_injective
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module.FaithfullyFlat A B] :
    Function.Injective (chapter03ModuleAmitsurAugmentation A B M) := by
  exact Module.FaithfullyFlat.tensorProduct_mk_injective M

theorem chapter03_module_amitsur_exact
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module.FaithfullyFlat A B] :
    Function.Exact (chapter03ModuleAmitsurAugmentation A B M)
      (chapter03ModuleAmitsurDifference A B M) := by
  let F := (chapter03ModuleAmitsurAugmentation A B M).lTensor B
  let G := (chapter03ModuleAmitsurDifference A B M).lTensor B
  let L : B ⊗[A] (B ⊗[A] M) →ₗ[A] B ⊗[A] M :=
    (LinearMap.mul' A B).rTensor M ∘ₗ (TensorProduct.assoc A B B M).symm.toLinearMap
  let K : B ⊗[A] ((B ⊗[A] B) ⊗[A] M) →ₗ[A] B ⊗[A] (B ⊗[A] M) :=
    (TensorProduct.assoc A B B M).toLinearMap ∘ₗ
      (TensorProduct.map (LinearMap.mul' A B) (LinearMap.id : B →ₗ[A] B)).rTensor M ∘ₗ
        (TensorProduct.assoc A B B B).symm.toLinearMap.rTensor M ∘ₗ
          (TensorProduct.assoc A B (B ⊗[A] B) M).symm.toLinearMap
  have hK_tmul (a x y : B) (m : M) :
      K (a ⊗ₜ[A] ((x ⊗ₜ[A] y) ⊗ₜ[A] m)) =
        (a * x) ⊗ₜ[A] (y ⊗ₜ[A] m) := by
    simp [K, LinearMap.comp_apply, LinearMap.rTensor, TensorProduct.map,
      TensorProduct.assoc, LinearMap.mul']
  have hKG : K.comp G = LinearMap.id - F.comp L := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp [K, G, F, L, chapter03ModuleAmitsurDifference,
        chapter03ModuleAmitsurD0, chapter03ModuleAmitsurD1]
    | add x y hx hy =>
        simp only [map_add, hx, hy]
    | tmul a z =>
        induction z using TensorProduct.induction_on with
        | zero => simp [K, G, F, L, chapter03ModuleAmitsurDifference,
            chapter03ModuleAmitsurD0, chapter03ModuleAmitsurD1]
        | add x y hx hy =>
            simp only [TensorProduct.tmul_add, map_add, hx, hy]
        | tmul b c =>
            change K (a ⊗ₜ[A]
                (((1 : B) ⊗ₜ[A] b - b ⊗ₜ[A] (1 : B)) ⊗ₜ[A] c)) =
              a ⊗ₜ[A] (b ⊗ₜ[A] c) -
                (a * b) ⊗ₜ[A] ((1 : B) ⊗ₜ[A] c)
            rw [TensorProduct.sub_tmul, TensorProduct.tmul_sub, map_sub,
              hK_tmul, hK_tmul]
            simp
  have hGF : G.comp F = 0 := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy =>
        simp only [map_add, hx, hy]
    | tmul b m =>
        change
          (LinearMap.lTensor B (chapter03ModuleAmitsurDifference A B M))
              (LinearMap.lTensor B (chapter03ModuleAmitsurAugmentation A B M)
                (b ⊗ₜ[A] m)) = 0
        rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul]
        simp [chapter03ModuleAmitsurAugmentation, chapter03TensorUnitMap,
          chapter03ModuleAmitsurDifference, chapter03ModuleAmitsurD0,
          chapter03ModuleAmitsurD1]
        change
          b ⊗ₜ[A]
              (((1 : B) ⊗ₜ[A] (1 : B)) ⊗ₜ[A] m -
                ((1 : B) ⊗ₜ[A] (1 : B)) ⊗ₜ[A] m) = 0
        simp
  have hex : Function.Exact F G := by
    apply LinearMap.exact_of_comp_of_mem_range
    · exact hGF
    · intro z hz
      have hk : K (G z) = 0 := congrArg K hz
      have hz' : z - F (L z) = 0 := by
        simpa [LinearMap.comp_apply] using (LinearMap.congr_fun hKG z).symm.trans hk
      exact ⟨L z, (sub_eq_zero.mp hz').symm⟩
  simpa [F, G] using Module.FaithfullyFlat.lTensor_reflects_exact A B _ _ hex

theorem chapter03_module_amitsur_equalizer_eq_range
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module.FaithfullyFlat A B] :
    {x : B ⊗[A] M | chapter03AmitsurInvariant A B M x} =
      Set.range (chapter03ModuleAmitsurAugmentation A B M) := by
  have h := chapter03_module_amitsur_exact (A := A) (B := B) (M := M)
  rw [LinearMap.exact_iff] at h
  ext x
  constructor
  · intro hx
    have hxker : x ∈ (chapter03ModuleAmitsurDifference A B M).ker :=
      (chapter03AmitsurInvariant_iff_mem A B M x).mp hx
    rw [h] at hxker
    exact hxker
  · intro hx
    have hxrange : x ∈ (chapter03ModuleAmitsurAugmentation A B M).range := hx
    rw [← h] at hxrange
    exact (chapter03AmitsurInvariant_iff_mem A B M x).mpr hxrange

private def chapter03AmitsurContraction
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (n : ℕ) :
    B ⊗[A] Chapter03AmitsurTensor A B (n + 1) →ₗ[A]
      B ⊗[A] Chapter03AmitsurTensor A B n :=
  (LinearMap.mul' A B).rTensor (Chapter03AmitsurTensor A B n) ∘ₗ
    (TensorProduct.assoc A B B (Chapter03AmitsurTensor A B n)).symm.toLinearMap

private theorem chapter03AmitsurContraction_mk_one
    {A B X : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup X] [Module A X] :
    ((LinearMap.mul' A B).rTensor (B ⊗[A] X) ∘ₗ
        (TensorProduct.assoc A B B (B ⊗[A] X)).symm.toLinearMap).comp
        (LinearMap.lTensor B (TensorProduct.mk A B (B ⊗[A] X) 1)) =
      LinearMap.id := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
          simp only [TensorProduct.tmul_add, map_add, hx, hy]
      | tmul b y =>
          change (a * (1 : B)) ⊗ₜ[A] (b ⊗ₜ[A] y) =
            a ⊗ₜ[A] (b ⊗ₜ[A] y)
          simp

private theorem chapter03AmitsurContraction_face_zero
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (n : ℕ) :
    (chapter03AmitsurContraction (A := A) (B := B) (n + 1)).comp
        (LinearMap.lTensor B (chapter03AmitsurFace A B (n + 1) 0)) =
      LinearMap.id := by
  have hface : chapter03AmitsurFace A B (n + 1) 0 =
      TensorProduct.mk A B (Chapter03AmitsurTensor A B (n + 1)) 1 := by
    rfl
  rw [hface]
  exact chapter03AmitsurContraction_mk_one
    (A := A) (B := B) (X := Chapter03AmitsurTensor A B n)

private theorem chapter03AmitsurContraction_lTensor
    {A B X Y : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    (f : X →ₗ[A] Y) :
    ((LinearMap.mul' A B).rTensor Y ∘ₗ
        (TensorProduct.assoc A B B Y).symm.toLinearMap).comp
        (LinearMap.lTensor B (f.lTensor B)) =
      (LinearMap.lTensor B f).comp
        ((LinearMap.mul' A B).rTensor X ∘ₗ
          (TensorProduct.assoc A B B X).symm.toLinearMap) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
          rw [TensorProduct.tmul_add]
          simp only [map_add, hx, hy]
      | tmul b x =>
          change (a * b) ⊗ₜ[A] f x = (a * b) ⊗ₜ[A] f x
          rfl

private theorem chapter03AmitsurContraction_face_succ
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (n : ℕ) (i : Fin (n + 2)) :
    (chapter03AmitsurContraction (A := A) (B := B) (n + 1)).comp
        (LinearMap.lTensor B (chapter03AmitsurFace A B (n + 1) i.succ)) =
      (LinearMap.lTensor B (chapter03AmitsurFace A B n i)).comp
        (chapter03AmitsurContraction (A := A) (B := B) n) := by
  have hface : chapter03AmitsurFace A B (n + 1) i.succ =
      (chapter03AmitsurFace A B n i).lTensor B := by
    rfl
  rw [hface]
  exact chapter03AmitsurContraction_lTensor
    (A := A) (B := B) (f := chapter03AmitsurFace A B n i)

private theorem chapter03AmitsurContraction_boundary
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (n : ℕ) :
    (chapter03AmitsurContraction (A := A) (B := B) (n + 1)).comp
        (LinearMap.lTensor B (chapter03AmitsurBoundary A B
          (chapter03AmitsurFace A B) (n + 1))) =
      LinearMap.id -
        (LinearMap.lTensor B (chapter03AmitsurBoundary A B
          (chapter03AmitsurFace A B) n)).comp
          (chapter03AmitsurContraction (A := A) (B := B) n) := by
  have hsum_succ :
      LinearMap.lTensor B (∑ i : Fin (n + 3),
          (-1 : A) ^ (i : ℕ) • chapter03AmitsurFace A B (n + 1) i) =
        ∑ i : Fin (n + 3), (-1 : A) ^ (i : ℕ) •
          LinearMap.lTensor B (chapter03AmitsurFace A B (n + 1) i) := by
    change (LinearMap.lTensorHom B) (∑ i : Fin (n + 3),
        (-1 : A) ^ (i : ℕ) • chapter03AmitsurFace A B (n + 1) i) = _
    simpa only [map_smul, LinearMap.coe_lTensorHom] using
      (map_sum (LinearMap.lTensorHom B)
        (fun i : Fin (n + 3) => (-1 : A) ^ (i : ℕ) •
          chapter03AmitsurFace A B (n + 1) i) Finset.univ)
  have hsum :
      LinearMap.lTensor B (∑ i : Fin (n + 2),
          (-1 : A) ^ (i : ℕ) • chapter03AmitsurFace A B n i) =
        ∑ i : Fin (n + 2), (-1 : A) ^ (i : ℕ) •
          LinearMap.lTensor B (chapter03AmitsurFace A B n i) := by
    change (LinearMap.lTensorHom B) (∑ i : Fin (n + 2),
        (-1 : A) ^ (i : ℕ) • chapter03AmitsurFace A B n i) = _
    simpa only [map_smul, LinearMap.coe_lTensorHom] using
      (map_sum (LinearMap.lTensorHom B)
        (fun i : Fin (n + 2) => (-1 : A) ^ (i : ℕ) •
          chapter03AmitsurFace A B n i) Finset.univ)
  rw [show chapter03AmitsurBoundary A B (chapter03AmitsurFace A B) (n + 1) =
      ∑ i : Fin (n + 3), (-1 : A) ^ (i : ℕ) •
        chapter03AmitsurFace A B (n + 1) i by rfl,
    show chapter03AmitsurBoundary A B (chapter03AmitsurFace A B) n =
      ∑ i : Fin (n + 2), (-1 : A) ^ (i : ℕ) •
        chapter03AmitsurFace A B n i by rfl,
    hsum_succ, hsum]
  rw [Fin.sum_univ_succ]
  have hleft :
      (chapter03AmitsurContraction (A := A) (B := B) (n + 1)).comp
          (∑ i : Fin (n + 2), (-1 : A) ^ (i.succ : ℕ) •
            LinearMap.lTensor B (chapter03AmitsurFace A B (n + 1) i.succ)) =
        ∑ i : Fin (n + 2),
          (chapter03AmitsurContraction (A := A) (B := B) (n + 1)).comp
            ((-1 : A) ^ (i.succ : ℕ) •
              LinearMap.lTensor B (chapter03AmitsurFace A B (n + 1) i.succ)) := by
    apply LinearMap.ext
    intro z
    simp only [LinearMap.coe_comp, LinearMap.coe_sum, Finset.sum_apply,
      Function.comp_apply]
    rw [map_sum]
  have hright :
      (∑ i : Fin (n + 2), (-1 : A) ^ (i : ℕ) •
          LinearMap.lTensor B (chapter03AmitsurFace A B n i)).comp
          (chapter03AmitsurContraction (A := A) (B := B) n) =
        ∑ i : Fin (n + 2),
          ((-1 : A) ^ (i : ℕ) •
            LinearMap.lTensor B (chapter03AmitsurFace A B n i)).comp
            (chapter03AmitsurContraction (A := A) (B := B) n) := by
    apply LinearMap.ext
    intro z
    simp only [LinearMap.coe_comp, LinearMap.coe_sum, Finset.sum_apply,
      Function.comp_apply]
  rw [LinearMap.comp_add, hleft, hright]
  simp only [Fin.val_zero, pow_zero]
  rw [one_smul, chapter03AmitsurContraction_face_zero]
  have hcomp :
      (∑ i : Fin (n + 2),
          (chapter03AmitsurContraction (A := A) (B := B) (n + 1)).comp
            ((-1 : A) ^ (i.succ : ℕ) •
              LinearMap.lTensor B (chapter03AmitsurFace A B (n + 1) i.succ))) =
        - ∑ i : Fin (n + 2),
          ((-1 : A) ^ (i : ℕ) •
            LinearMap.lTensor B (chapter03AmitsurFace A B n i)).comp
            (chapter03AmitsurContraction (A := A) (B := B) n) := by
    calc
      (∑ i : Fin (n + 2),
          (chapter03AmitsurContraction (A := A) (B := B) (n + 1)).comp
            ((-1 : A) ^ (i.succ : ℕ) •
              LinearMap.lTensor B (chapter03AmitsurFace A B (n + 1) i.succ))) =
          ∑ i : Fin (n + 2), (-1 : A) ^ (i.succ : ℕ) •
            ((chapter03AmitsurContraction (A := A) (B := B) (n + 1)).comp
              (LinearMap.lTensor B (chapter03AmitsurFace A B (n + 1) i.succ))) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [LinearMap.comp_smul]
      _ = ∑ i : Fin (n + 2), (-1 : A) ^ (i.succ : ℕ) •
            ((LinearMap.lTensor B (chapter03AmitsurFace A B n i)).comp
              (chapter03AmitsurContraction (A := A) (B := B) n)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [chapter03AmitsurContraction_face_succ]
      _ = - ∑ i : Fin (n + 2),
          ((-1 : A) ^ (i : ℕ) •
            LinearMap.lTensor B (chapter03AmitsurFace A B n i)).comp
            (chapter03AmitsurContraction (A := A) (B := B) n) := by
        calc
          (∑ i : Fin (n + 2), (-1 : A) ^ (i.succ : ℕ) •
              ((LinearMap.lTensor B (chapter03AmitsurFace A B n i)).comp
                (chapter03AmitsurContraction (A := A) (B := B) n))) =
              ∑ i : Fin (n + 2), -
                (((-1 : A) ^ (i : ℕ) •
                  LinearMap.lTensor B (chapter03AmitsurFace A B n i)).comp
                  (chapter03AmitsurContraction (A := A) (B := B) n)) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [LinearMap.smul_comp]
            apply LinearMap.ext
            intro z
            change
              ((-1 : A) ^ (i.succ : ℕ)) •
                  (((LinearMap.lTensor B (chapter03AmitsurFace A B n i)).comp
                    (chapter03AmitsurContraction (A := A) (B := B) n)) z) =
                -(((-1 : A) ^ (i : ℕ)) •
                  (((LinearMap.lTensor B (chapter03AmitsurFace A B n i)).comp
                    (chapter03AmitsurContraction (A := A) (B := B) n)) z))
            rw [Fin.val_succ, pow_succ]
            simp only [mul_one, mul_neg]
            exact neg_smul ((-1 : A) ^ (i : ℕ))
              (((LinearMap.lTensor B (chapter03AmitsurFace A B n i)).comp
                (chapter03AmitsurContraction (A := A) (B := B) n)) z)
          _ = - ∑ i : Fin (n + 2),
              ((-1 : A) ^ (i : ℕ) •
                LinearMap.lTensor B (chapter03AmitsurFace A B n i)).comp
                (chapter03AmitsurContraction (A := A) (B := B) n) := by
            apply LinearMap.ext
            intro z
            apply congrArg
              (fun f :
                (B ⊗[A] Chapter03AmitsurTensor A B (n + 1) →ₗ[A]
                  B ⊗[A] Chapter03AmitsurTensor A B (n + 1)) => f z)
            exact Finset.sum_neg_distrib
              (s := (Finset.univ : Finset (Fin (n + 2))))
              (fun i : Fin (n + 2) =>
                ((-1 : A) ^ (i : ℕ) •
                  LinearMap.lTensor B (chapter03AmitsurFace A B n i)).comp
                  (chapter03AmitsurContraction (A := A) (B := B) n))
  rw [hcomp]
  rfl

private theorem chapter03TensorUnit_lTensor
    {A B X Y : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    (f : X →ₗ[A] Y) :
    (TensorProduct.mk A B (B ⊗[A] Y) 1).comp (f.lTensor B) =
      ((f.lTensor B).lTensor B).comp
        (TensorProduct.mk A B (B ⊗[A] X) 1) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b x =>
      change (1 : B) ⊗ₜ[A] (b ⊗ₜ[A] f x) =
        (1 : B) ⊗ₜ[A] (b ⊗ₜ[A] f x)
      rfl

private theorem chapter03TensorUnit_naturality
    {A B X Y : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    (f : X →ₗ[A] B ⊗[A] Y) :
    (TensorProduct.mk A B (B ⊗[A] Y) 1).comp f =
      (f.lTensor B).comp (TensorProduct.mk A B X 1) := by
  apply LinearMap.ext
  intro x
  change (1 : B) ⊗ₜ[A] f x = (1 : B) ⊗ₜ[A] f x
  rfl

private theorem chapter03TensorUnit_comp
    {A B X : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup X] [Module A X] :
    (TensorProduct.mk A B (B ⊗[A] X) 1).comp
        (TensorProduct.mk A B X 1) =
      ((TensorProduct.mk A B X 1).lTensor B).comp
        (TensorProduct.mk A B X 1) := by
  apply LinearMap.ext
  intro x
  change (1 : B) ⊗ₜ[A] ((1 : B) ⊗ₜ[A] x) =
    (1 : B) ⊗ₜ[A] ((1 : B) ⊗ₜ[A] x)
  rfl

private theorem chapter03AmitsurFace_comp_aux
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 3)) (k : Fin (n + 2))
    (h : (j : ℕ) ≤ (i : ℕ)) (hk : (k : ℕ) = (j : ℕ)) :
    (chapter03AmitsurFace A B (n + 1) j).comp
        (chapter03AmitsurFace A B n i) =
      (chapter03AmitsurFace A B (n + 1) i.succ).comp
        (chapter03AmitsurFace A B n k) := by
  revert i j k h hk
  induction n with
  | zero =>
      intro i j k
      fin_cases i <;> fin_cases j <;> fin_cases k <;>
        intro h hk <;>
          simp_all [chapter03AmitsurFace, Fin.cases, Fin.induction] <;> rfl
  | succ n ih =>
      intro i j k
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · refine Fin.cases ?_ (fun k => ?_) k
          · intro h hk
            norm_num at h hk ⊢
            rfl
          · intro h hk
            norm_num at hk
        · refine Fin.cases ?_ (fun k => ?_) k
          · intro h hk
            norm_num at h
          · intro h hk
            norm_num at h
      · refine Fin.cases ?_ (fun j => ?_) j
        · refine Fin.cases ?_ (fun k => ?_) k
          · intro h hk
            norm_num at hk
            rfl
          · intro h hk
            norm_num at hk
        · refine Fin.cases ?_ (fun k => ?_) k
          · intro h hk
            norm_num at hk
          · intro h hk
            norm_num at h hk ⊢
            have hi := ih i j k h hk
            have hi' := congrArg (fun q => q.lTensor B) hi
            change
              (LinearMap.lTensor B (chapter03AmitsurFace A B (n + 1) j)).comp
                  (LinearMap.lTensor B (chapter03AmitsurFace A B n i)) =
                (LinearMap.lTensor B
                    (chapter03AmitsurFace A B (n + 1) i.succ)).comp
                  (LinearMap.lTensor B (chapter03AmitsurFace A B n k))
            simpa only [LinearMap.lTensor_comp] using hi'

private theorem chapter03AmitsurFace_comp
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 3))
    (h : (j : ℕ) ≤ (i : ℕ)) :
    (chapter03AmitsurFace A B (n + 1) j).comp
        (chapter03AmitsurFace A B n i) =
      (chapter03AmitsurFace A B (n + 1) i.succ).comp
        (chapter03AmitsurFace A B n
          (Fin.castLT j (lt_of_le_of_lt h (Fin.is_lt i)))) := by
  exact chapter03AmitsurFace_comp_aux n i j
    (Fin.castLT j (lt_of_le_of_lt h (Fin.is_lt i))) h rfl

private theorem chapter03_amitsur_higher_differential_square
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] :
    ∀ n : ℕ,
      (chapter03AmitsurBoundary A B (chapter03AmitsurFace A B) (n + 1)).comp
          (chapter03AmitsurBoundary A B (chapter03AmitsurFace A B) n) = 0 := by
  intro n
  rw [show chapter03AmitsurBoundary A B (chapter03AmitsurFace A B) (n + 1) =
        ∑ i : Fin (n + 3), (-1 : A) ^ (i : ℕ) •
          chapter03AmitsurFace A B (n + 1) i by rfl,
    show chapter03AmitsurBoundary A B (chapter03AmitsurFace A B) n =
        ∑ i : Fin (n + 2), (-1 : A) ^ (i : ℕ) •
          chapter03AmitsurFace A B n i by rfl]
  apply LinearMap.ext
  intro z
  simp only [LinearMap.coe_comp, LinearMap.coe_sum, Finset.sum_apply,
    Function.comp_apply]
  simp_rw [map_sum, LinearMap.smul_apply]
  simp only [map_smul, smul_smul]
  rw [Finset.sum_comm, ← Finset.sum_product']
  simp only [LinearMap.zero_apply]
  let P := Fin (n + 2) × Fin (n + 3)
  let S : Finset P := {ij : P | (ij.2 : ℕ) ≤ (ij.1 : ℕ)}
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl S,
    ← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  let φ : ∀ ij : P, ij ∈ S → P := fun ij hij =>
    (Fin.castLT ij.2
      (lt_of_le_of_lt (Finset.mem_filter.mp hij).right (Fin.is_lt ij.1)),
      ij.1.succ)
  apply Finset.sum_bij φ
  · intro ij hij
    simp_rw [S, φ, Finset.compl_filter, Finset.mem_filter_univ,
      Fin.val_succ, Fin.val_castLT] at hij ⊢
    omega
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ] using congr_arg Prod.snd h,
      by simpa [φ, Fin.castSucc_castLT] using
        congrArg Fin.castSucc (congr_arg Prod.fst h)⟩
  · rintro ⟨i', j'⟩ hij'
    simp_rw [S, Finset.compl_filter, Finset.mem_filter_univ, not_le] at hij'
    refine ⟨(j'.pred <| ?_, Fin.castSucc i'), ?_, ?_⟩
    · rintro rfl
      simp only [Fin.val_zero, not_lt_zero] at hij'
    · simpa [S] using Nat.le_sub_one_of_lt hij'
    · simp [φ, Fin.succ_pred]
  · rintro ⟨i, j⟩ hij
    dsimp [φ]
    have hji : (j : ℕ) ≤ (i : ℕ) := by
      simpa [S] using hij
    have hv := congrArg (fun f => f z)
      (chapter03AmitsurFace_comp n i j hji)
    change (chapter03AmitsurFace A B (n + 1) j)
        ((chapter03AmitsurFace A B n i) z) =
      (chapter03AmitsurFace A B (n + 1) i.succ)
        ((chapter03AmitsurFace A B n (j.castLT _)) z) at hv
    have hscalar :
        (-1 : A) ^ (j : ℕ) * (-1 : A) ^ (i : ℕ) =
          - ((-1 : A) ^ ((i : ℕ) + 1) * (-1 : A) ^ (j : ℕ)) := by
      simp only [pow_succ]
      ring
    calc
      ((-1 : A) ^ (j : ℕ) * (-1 : A) ^ (i : ℕ)) •
          (chapter03AmitsurFace A B (n + 1) j)
            ((chapter03AmitsurFace A B n i) z) =
          ((-1 : A) ^ (j : ℕ) * (-1 : A) ^ (i : ℕ)) •
            (chapter03AmitsurFace A B (n + 1) i.succ)
              ((chapter03AmitsurFace A B n (j.castLT _)) z) := by
        rw [hv]
      _ = (-((-1 : A) ^ ((i : ℕ) + 1) * (-1 : A) ^ (j : ℕ))) •
            (chapter03AmitsurFace A B (n + 1) i.succ)
              ((chapter03AmitsurFace A B n (j.castLT _)) z) := by
        rw [hscalar]
      _ = -(((-1 : A) ^ ((i : ℕ) + 1) * (-1 : A) ^ (j : ℕ)) •
            (chapter03AmitsurFace A B (n + 1) i.succ)
              ((chapter03AmitsurFace A B n (j.castLT _)) z)) := by
        rw [neg_smul]

theorem chapter03_amitsur_higher_complex_exact
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] :
    Chapter03AmitsurFaceFamilyMatchesLowDegree A B (chapter03AmitsurFace A B) ∧
      Chapter03AmitsurDifferentialSquaresToZero A B (chapter03AmitsurFace A B) ∧
      Chapter03AmitsurPositiveExact A B (chapter03AmitsurFace A B) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor <;> rfl
  · exact chapter03_amitsur_higher_differential_square (A := A) (B := B)
  · intro n
    let F := chapter03AmitsurBoundary A B (chapter03AmitsurFace A B) n
    let G := chapter03AmitsurBoundary A B (chapter03AmitsurFace A B) (n + 1)
    let L := chapter03AmitsurContraction (A := A) (B := B) n
    let K := chapter03AmitsurContraction (A := A) (B := B) (n + 1)
    have hsq :=
      chapter03_amitsur_higher_differential_square (A := A) (B := B) n
    have hGF : (LinearMap.lTensor B G).comp (LinearMap.lTensor B F) = 0 := by
      have hsq' := congrArg (fun q => LinearMap.lTensor B q) hsq
      simpa only [F, G, LinearMap.lTensor_comp, LinearMap.lTensor_zero] using hsq'
    have hKG : K.comp (LinearMap.lTensor B G) =
        LinearMap.id - (LinearMap.lTensor B F).comp L := by
      simpa only [F, G, K, L] using
        (chapter03AmitsurContraction_boundary (A := A) (B := B) n)
    have hex : Function.Exact (LinearMap.lTensor B F) (LinearMap.lTensor B G) := by
      apply LinearMap.exact_of_comp_of_mem_range
      · exact hGF
      · intro z hz
        have hk : K ((LinearMap.lTensor B G) z) = 0 := congrArg K hz
        have hz' : z - (LinearMap.lTensor B F) (L z) = 0 := by
          simpa only [LinearMap.comp_apply, LinearMap.sub_apply,
            LinearMap.id_apply] using (LinearMap.congr_fun hKG z).symm.trans hk
        exact ⟨L z, (sub_eq_zero.mp hz').symm⟩
    simpa only [F, G] using
      Module.FaithfullyFlat.lTensor_reflects_exact A B _ _ hex

private theorem chapter03_module_amitsur_boundary_eq_rTensor
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] (n : ℕ) :
    chapter03ModuleAmitsurBoundary A B M (chapter03ModuleAmitsurFace A B M) n =
      (chapter03AmitsurBoundary A B (chapter03AmitsurFace A B) n).rTensor M := by
  change (∑ i : Fin (n + 2), (-1 : A) ^ (i : ℕ) •
      LinearMap.rTensor M (chapter03AmitsurFace A B n i)) =
    (LinearMap.rTensorHom M) (∑ i : Fin (n + 2), (-1 : A) ^ (i : ℕ) •
      chapter03AmitsurFace A B n i)
  simpa only [map_smul, LinearMap.coe_rTensorHom] using
    (map_sum (LinearMap.rTensorHom M)
      (fun i : Fin (n + 2) => (-1 : A) ^ (i : ℕ) •
        chapter03AmitsurFace A B n i) Finset.univ).symm

private def chapter03ModuleAmitsurContraction
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] (n : ℕ) :
    B ⊗[A] (Chapter03AmitsurTensor A B (n + 1) ⊗[A] M) →ₗ[A]
      B ⊗[A] (Chapter03AmitsurTensor A B n ⊗[A] M) :=
  (TensorProduct.assoc A B (Chapter03AmitsurTensor A B n) M).toLinearMap ∘ₗ
    (chapter03AmitsurContraction (A := A) (B := B) n).rTensor M ∘ₗ
      (TensorProduct.assoc A B (Chapter03AmitsurTensor A B (n + 1)) M).symm.toLinearMap

private theorem chapter03ModuleAmitsurContraction_boundary
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] (n : ℕ) :
    (chapter03ModuleAmitsurContraction (A := A) (B := B) (M := M) (n + 1)).comp
        (LinearMap.lTensor B
          (chapter03ModuleAmitsurBoundary A B M
            (chapter03ModuleAmitsurFace A B M) (n + 1))) =
      LinearMap.id -
        (LinearMap.lTensor B
          (chapter03ModuleAmitsurBoundary A B M
            (chapter03ModuleAmitsurFace A B M) n)).comp
          (chapter03ModuleAmitsurContraction (A := A) (B := B) (M := M) n) := by
  rw [chapter03_module_amitsur_boundary_eq_rTensor (A := A) (B := B) (M := M)
      (n + 1),
    chapter03_module_amitsur_boundary_eq_rTensor (A := A) (B := B) (M := M) n]
  let C := chapter03AmitsurContraction (A := A) (B := B) n
  let C' := chapter03AmitsurContraction (A := A) (B := B) (n + 1)
  let D := chapter03AmitsurBoundary A B (chapter03AmitsurFace A B) n
  let D' := chapter03AmitsurBoundary A B (chapter03AmitsurFace A B) (n + 1)
  have hD' := LinearMap.rTensor_lTensor_comp_assoc_symm (R := A) (P := B)
    (Q := M) (x := D')
  have hD := LinearMap.rTensor_lTensor_comp_assoc_symm (R := A) (P := B)
    (Q := M) (x := D)
  have hC := chapter03AmitsurContraction_boundary (A := A) (B := B) n
  simp only [chapter03ModuleAmitsurContraction, LinearMap.comp_assoc]
  rw [← hD']
  rw [← LinearMap.comp_assoc
    (TensorProduct.assoc A B (Chapter03AmitsurTensor A B (n + 1)) M).symm.toLinearMap
    (LinearMap.rTensor M (LinearMap.lTensor B D'))
    (LinearMap.rTensor M (chapter03AmitsurContraction (A := A) (B := B) (n + 1)))]
  rw [← LinearMap.rTensor_comp, hC, LinearMap.rTensor_sub,
    LinearMap.rTensor_id, LinearMap.rTensor_comp]
  have hD1 :
      (TensorProduct.assoc A B (Chapter03AmitsurTensor A B (n + 1)) M).toLinearMap.comp
          ((LinearMap.rTensor M (LinearMap.lTensor B D)).comp
            (TensorProduct.assoc A B (Chapter03AmitsurTensor A B n) M).symm.toLinearMap) =
        LinearMap.lTensor B (LinearMap.rTensor M D) := by
    exact (LinearEquiv.eq_toLinearMap_symm_comp
      (e₁₂ := TensorProduct.assoc A B (Chapter03AmitsurTensor A B (n + 1)) M)
      (f := (LinearMap.rTensor M (LinearMap.lTensor B D)).comp
        (TensorProduct.assoc A B (Chapter03AmitsurTensor A B n) M).symm.toLinearMap)
      (g := LinearMap.lTensor B (LinearMap.rTensor M D))).mp hD
  have hDtransport :
      (TensorProduct.assoc A B (Chapter03AmitsurTensor A B (n + 1)) M).toLinearMap.comp
          (LinearMap.rTensor M (LinearMap.lTensor B D)) =
        (LinearMap.lTensor B (LinearMap.rTensor M D)).comp
          (TensorProduct.assoc A B (Chapter03AmitsurTensor A B n) M).toLinearMap := by
    calc
      (TensorProduct.assoc A B (Chapter03AmitsurTensor A B (n + 1)) M).toLinearMap.comp
            (LinearMap.rTensor M (LinearMap.lTensor B D)) =
          ((TensorProduct.assoc A B (Chapter03AmitsurTensor A B (n + 1)) M).toLinearMap.comp
              (LinearMap.rTensor M (LinearMap.lTensor B D))).comp
            ((TensorProduct.assoc A B (Chapter03AmitsurTensor A B n) M).symm.toLinearMap.comp
              (TensorProduct.assoc A B (Chapter03AmitsurTensor A B n) M).toLinearMap) := by
              rw [LinearEquiv.symm_comp, LinearMap.comp_id]
      _ = ((TensorProduct.assoc A B (Chapter03AmitsurTensor A B (n + 1)) M).toLinearMap.comp
              ((LinearMap.rTensor M (LinearMap.lTensor B D)).comp
                (TensorProduct.assoc A B (Chapter03AmitsurTensor A B n) M).symm.toLinearMap)).comp
            (TensorProduct.assoc A B (Chapter03AmitsurTensor A B n) M).toLinearMap := by
              simp only [LinearMap.comp_assoc]
      _ = (LinearMap.lTensor B (LinearMap.rTensor M D)).comp
            (TensorProduct.assoc A B (Chapter03AmitsurTensor A B n) M).toLinearMap := by
              rw [hD1]
  apply LinearMap.ext
  intro z
  change
    (TensorProduct.assoc A B (Chapter03AmitsurTensor A B (n + 1)) M)
        ((TensorProduct.assoc A B (Chapter03AmitsurTensor A B (n + 1)) M).symm z -
          (LinearMap.rTensor M (LinearMap.lTensor B D))
            ((LinearMap.rTensor M C)
              ((TensorProduct.assoc A B (Chapter03AmitsurTensor A B (n + 1)) M).symm z))) =
      z -
        (LinearMap.lTensor B (LinearMap.rTensor M D))
          ((TensorProduct.assoc A B (Chapter03AmitsurTensor A B n) M)
            ((LinearMap.rTensor M C)
              ((TensorProduct.assoc A B (Chapter03AmitsurTensor A B (n + 1)) M).symm z)))
  have htransport := LinearMap.congr_fun hDtransport
    ((LinearMap.rTensor M C)
      ((TensorProduct.assoc A B (Chapter03AmitsurTensor A B (n + 1)) M).symm z))
  change
    (TensorProduct.assoc A B (Chapter03AmitsurTensor A B (n + 1)) M)
        ((LinearMap.rTensor M (LinearMap.lTensor B D))
          ((LinearMap.rTensor M C)
            ((TensorProduct.assoc A B (Chapter03AmitsurTensor A B (n + 1)) M).symm z))) =
      (LinearMap.lTensor B (LinearMap.rTensor M D))
        ((TensorProduct.assoc A B (Chapter03AmitsurTensor A B n) M)
          ((LinearMap.rTensor M C)
            ((TensorProduct.assoc A B (Chapter03AmitsurTensor A B (n + 1)) M).symm z))) at htransport
  rw [map_sub, LinearEquiv.apply_symm_apply]
  exact congrArg (fun x => z - x) htransport

theorem chapter03_module_amitsur_higher_complex_exact
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module.FaithfullyFlat A B] :
    Chapter03ModuleAmitsurDifferentialSquaresToZero A B M
        (chapter03ModuleAmitsurFace A B M) ∧
      Chapter03ModuleAmitsurPositiveExact A B M
        (chapter03ModuleAmitsurFace A B M) := by
  constructor
  · intro n
    rw [chapter03_module_amitsur_boundary_eq_rTensor (A := A) (B := B) (M := M)
      (n + 1),
      chapter03_module_amitsur_boundary_eq_rTensor (A := A) (B := B) (M := M) n]
    have hsq :=
      chapter03_amitsur_higher_differential_square (A := A) (B := B) n
    have hsq' := congrArg (fun q => q.rTensor M) hsq
    simpa only [LinearMap.rTensor_comp, LinearMap.rTensor_zero] using hsq'
  · intro n
    let F := chapter03AmitsurBoundary A B (chapter03AmitsurFace A B) n
    let G := chapter03AmitsurBoundary A B (chapter03AmitsurFace A B) (n + 1)
    let C := chapter03ModuleAmitsurContraction (A := A) (B := B) (M := M) n
    let C' := chapter03ModuleAmitsurContraction (A := A) (B := B) (M := M) (n + 1)
    rw [chapter03_module_amitsur_boundary_eq_rTensor (A := A) (B := B) (M := M)
      (n + 1),
      chapter03_module_amitsur_boundary_eq_rTensor (A := A) (B := B) (M := M) n]
    have hsq :=
      chapter03_amitsur_higher_differential_square (A := A) (B := B) n
    have hsq' := congrArg (fun q => q.rTensor M) hsq
    have hGF :
        (LinearMap.lTensor B (LinearMap.rTensor M G)).comp
            (LinearMap.lTensor B (LinearMap.rTensor M F)) = 0 := by
      have hmodsq :
          (LinearMap.rTensor M G).comp (LinearMap.rTensor M F) = 0 := by
        simpa only [F, G, LinearMap.rTensor_comp, LinearMap.rTensor_zero] using hsq'
      have hmodsq' := congrArg (fun q => LinearMap.lTensor B q) hmodsq
      simpa only [LinearMap.lTensor_comp, LinearMap.lTensor_zero] using hmodsq'
    have hKraw :=
      chapter03ModuleAmitsurContraction_boundary (A := A) (B := B) (M := M) n
    rw [chapter03_module_amitsur_boundary_eq_rTensor (A := A) (B := B) (M := M)
      (n + 1),
      chapter03_module_amitsur_boundary_eq_rTensor (A := A) (B := B) (M := M) n] at hKraw
    have hKG :
        C'.comp (LinearMap.lTensor B (LinearMap.rTensor M G)) =
          LinearMap.id -
            (LinearMap.lTensor B (LinearMap.rTensor M F)).comp C := by
      simpa only [C, C', F, G] using hKraw
    have hex :
        Function.Exact (LinearMap.lTensor B (LinearMap.rTensor M F))
          (LinearMap.lTensor B (LinearMap.rTensor M G)) := by
      apply LinearMap.exact_of_comp_of_mem_range
      · exact hGF
      · intro z hz
        have hk : C' ((LinearMap.lTensor B (LinearMap.rTensor M G)) z) = 0 :=
          congrArg C' hz
        have hz' : z - (LinearMap.lTensor B (LinearMap.rTensor M F)) (C z) = 0 := by
          simpa only [LinearMap.comp_apply, LinearMap.sub_apply,
            LinearMap.id_apply] using (LinearMap.congr_fun hKG z).symm.trans hk
        exact ⟨C z, (sub_eq_zero.mp hz').symm⟩
    simpa only [F, G] using
      Module.FaithfullyFlat.lTensor_reflects_exact A B _ _ hex

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter03
