import LastLib.Book04AdelesAndIdeles.Chapter11.Dependencies
import LastLib.Book04AdelesAndIdeles.Chapter08.Section86

namespace LastLib.Book04AdelesAndIdeles.Chapter11

open NumberField

noncomputable section

open scoped Classical

variable {K : Type*} [Field K] [NumberField K]

/-! ## 11.1 Why ideals need local unit data -/

theorem chapter11_modulus_finite_part_is_finitely_supported (m : RayModulus K) :
    (m.finiteExponent.support : Set
      (IsDedekindDomain.HeightOneSpectrum (𝓞 K))).Finite := by
  exact RayModulus.finiteExponent_support_finite m

theorem chapter11_modulus_selected_archimedean_places_are_real (m : RayModulus K) :
    ∀ v ∈ m.infinitePart, NumberField.InfinitePlace.IsReal v := by
  exact m.infinitePart_isReal

theorem chapter11_modulus_has_no_complex_sign_component (m : RayModulus K) :
    ∀ v, NumberField.InfinitePlace.IsComplex v → v ∉ m.infinitePart := by
  intro v hv hmem
  exact (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hv)
    (m.infinitePart_isReal v hmem)

theorem chapter11_modulus_is_finite_part_times_real_part (m : RayModulus K) :
    m.finiteIdeal =
      Finset.prod m.finiteExponent.support (fun v => v.asIdeal ^ m.finiteExponent v) := by
  rfl

abbrev Chapter11NarrowClassGroup (K : Type*) [Field K] [NumberField K] :=
  LastLib.Book04AdelesAndIdeles.Chapter08.Chapter08NarrowClassGroup K

theorem chapter11_trivial_modulus_ray_class_group_equiv_ordinary_class_group
    (K : Type*) [Field K] [NumberField K] :
    Nonempty
      (chapter11RayClassGroup (RayModulus.trivial (K := K)) ≃*
        Chapter11OrdinaryClassGroup K) := by
  let f : Chapter11IdeleGroup K →* Chapter11OrdinaryClassGroup K :=
    (ClassGroup.mk K).comp (chapter11CanonicalIdeleIdealMap K).toIdeal
  have hsurj : Function.Surjective f := by
    intro c
    refine ClassGroup.induction (R := 𝓞 K) K (fun I => ?_) c
    obtain ⟨x, hx⟩ := (chapter11CanonicalIdeleIdealMap K).surjective I
    exact ⟨x, congrArg (ClassGroup.mk K) hx⟩
  have hker :
      chapter11PrincipalIdeleSubgroup (K := K) ⊔
          chapter11RayUnitSubgroup (RayModulus.trivial (K := K)) = f.ker := by
    ext x
    constructor
    · intro hx
      apply (MonoidHom.mem_ker).2
      rcases Subgroup.mem_sup.mp hx with ⟨y, hy, z, hz, rfl⟩
      rcases hy with ⟨a, rfl⟩
      have hpa :
          (chapter11CanonicalIdeleIdealMap K).toIdeal
              (chapter11PrincipalIdeleHom (K := K) a) =
            toPrincipalIdeal (𝓞 K) K a :=
        (chapter11CanonicalIdeleIdealMap K).map_principal a
      have hzfull : z ∈ chapter11FullFiniteUnitSubgroup (K := K) := by
        simpa [chapter11FullFiniteUnitSubgroup, RayModulus.trivial] using hz
      have hz' : (chapter11CanonicalIdeleIdealMap K).toIdeal z = 1 := by
        exact MonoidHom.mem_ker.mp (show z ∈
          (chapter11CanonicalIdeleIdealMap K).toIdeal.ker by
          rw [(chapter11CanonicalIdeleIdealMap K).kernel_eq_full_finite_units]
          exact hzfull)
      change ClassGroup.mk K
        ((chapter11CanonicalIdeleIdealMap K).toIdeal
          (chapter11PrincipalIdeleHom (K := K) a * z)) = 1
      rw [map_mul, hpa, hz', mul_one]
      apply (ClassGroup.mk_eq_one_iff).2
      refine ⟨(a : K), ?_⟩
      simp [coe_toPrincipalIdeal]
    · intro hx
      change ClassGroup.mk K ((chapter11CanonicalIdeleIdealMap K).toIdeal x) = 1 at hx
      have hclass' := congrArg (ClassGroup.equiv K) hx
      rw [ClassGroup.equiv_mk, map_one] at hclass'
      let I : Chapter11FractionalIdealUnitGroup K :=
        (chapter11CanonicalIdeleIdealMap K).toIdeal x
      have hI :
          QuotientGroup.mk' (toPrincipalIdeal (𝓞 K) K).range I = 1 := by
        simpa [I] using hclass'
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hI
      obtain ⟨a, ha⟩ := hI
      have hpa :
          (chapter11CanonicalIdeleIdealMap K).toIdeal
              (chapter11PrincipalIdeleHom (K := K) a) =
            toPrincipalIdeal (𝓞 K) K a :=
        (chapter11CanonicalIdeleIdealMap K).map_principal a
      let y : Chapter11IdeleGroup K :=
        x * (chapter11PrincipalIdeleHom (K := K) a)⁻¹
      have hyideal : (chapter11CanonicalIdeleIdealMap K).toIdeal y = 1 := by
        simp [y]
        rw [hpa, ha]
        change I * I⁻¹ = 1
        simp
      have hy : y ∈ chapter11FullFiniteUnitSubgroup (K := K) := by
        rw [← (chapter11CanonicalIdeleIdealMap K).kernel_eq_full_finite_units]
        exact (MonoidHom.mem_ker).2 hyideal
      apply Subgroup.mem_sup.mpr
      refine ⟨chapter11PrincipalIdeleHom (K := K) a,
        ⟨a, rfl⟩, y, hy, ?_⟩
      simp [y, mul_left_comm]
  exact ⟨QuotientGroup.liftEquiv
    (chapter11PrincipalIdeleSubgroup (K := K) ⊔
      chapter11RayUnitSubgroup (RayModulus.trivial (K := K))) hsurj hker⟩

theorem chapter11_narrow_modulus_ray_class_group_equiv_narrow_class_group
    (K : Type*) [Field K] [NumberField K] :
    Nonempty
      (chapter11RayClassGroup (RayModulus.narrow (K := K)) ≃*
        Chapter11NarrowClassGroup K) := by
  have hfactor : ∀ {a b : Kˣ},
      LastLib.Book04AdelesAndIdeles.Chapter08.chapter08SignOfUnit a =
        LastLib.Book04AdelesAndIdeles.Chapter08.chapter08SignOfUnit b →
      ∃ d : LastLib.Book04AdelesAndIdeles.Chapter08.chapter08TotallyPositiveElements K,
        b = a * d := by
    intro a b hab
    let d : Kˣ := a⁻¹ * b
    have hd : d ∈
        LastLib.Book04AdelesAndIdeles.Chapter08.chapter08TotallyPositiveElements K := by
      intro w
      have hs := congrArg (fun z : SignTypeˣ => (z : SignType))
        (congrFun hab w)
      change SignType.sign
          (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08RealEmbedding w (a : K)) =
        SignType.sign
          (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08RealEmbedding w (b : K)) at hs
      have ha0 :
          LastLib.Book04AdelesAndIdeles.Chapter08.chapter08RealEmbedding w (a : K) ≠ 0 :=
        (map_ne_zero
          (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08RealEmbedding w)).2 a.ne_zero
      have hsign_inv : SignType.sign
          ((LastLib.Book04AdelesAndIdeles.Chapter08.chapter08RealEmbedding w (a : K))⁻¹) =
          SignType.sign
            (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08RealEmbedding w (a : K)) := by
        by_cases hpos : 0 <
            LastLib.Book04AdelesAndIdeles.Chapter08.chapter08RealEmbedding w (a : K)
        · rw [sign_pos (inv_pos.mpr hpos), sign_pos hpos]
        · have hneg :
              LastLib.Book04AdelesAndIdeles.Chapter08.chapter08RealEmbedding w (a : K) < 0 :=
            lt_of_le_of_ne (le_of_not_gt hpos) ha0
          rw [sign_neg (inv_lt_zero'.2 hneg), sign_neg hneg]
      have hsign : SignType.sign
          (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08RealEmbedding w (d : K)) = 1 := by
        simp [d, map_mul, map_inv₀, sign_mul]
        rw [hsign_inv, hs]
        rcases SignType.trichotomy
            (SignType.sign
              (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08RealEmbedding w (b : K))) with
          hneg | hzero | hpos
        · rw [hneg]
          simp
        · exact False.elim ((sign_ne_zero).2
            ((map_ne_zero
              (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08RealEmbedding w)).2
                b.ne_zero) hzero)
        · rw [hpos]
          simp
      exact sign_eq_one_iff.mp hsign
    refine ⟨⟨d, hd⟩, ?_⟩
    simp [d]
  have hcomm : ∀ a b :
      LastLib.Book04AdelesAndIdeles.Chapter08.Chapter08NarrowClassGroup K, a * b = b * a := by
    intro a b
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective
      (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08TotallyPositivePrincipalIdeals K) a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective
      (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08TotallyPositivePrincipalIdeals K) b
    change QuotientGroup.mk'
        (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08TotallyPositivePrincipalIdeals K)
          (a * b) =
      QuotientGroup.mk'
        (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08TotallyPositivePrincipalIdeals K)
          (b * a)
    rw [mul_comm]
  let q : Chapter11FractionalIdealUnitGroup K →*
      LastLib.Book04AdelesAndIdeles.Chapter08.Chapter08NarrowClassGroup K :=
    QuotientGroup.mk'
      (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08TotallyPositivePrincipalIdeals K)
  let signMap : Chapter11IdeleGroup K →*
      LastLib.Book04AdelesAndIdeles.Chapter08.Chapter08SignGroup K :=
    { toFun := fun x w =>
        chapter11RealSignComponent K w.1 w.2 x
      map_one' := by
        funext w
        simp
      map_mul' := by
        intro x y
        funext w
        simp }
  let signClassMap : Chapter11IdeleGroup K →*
      LastLib.Book04AdelesAndIdeles.Chapter08.Chapter08NarrowClassGroup K :=
    (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08SignToNarrowClass K).comp signMap
  let signClassInvMap : Chapter11IdeleGroup K →*
      LastLib.Book04AdelesAndIdeles.Chapter08.Chapter08NarrowClassGroup K :=
    MonoidHom.mk' (fun x => (signClassMap x)⁻¹) (by
      intro x y
      rw [signClassMap.map_mul]
      calc
        (signClassMap x * signClassMap y)⁻¹ =
            (signClassMap y)⁻¹ * (signClassMap x)⁻¹ :=
          @DivisionMonoid.mul_inv_rev _
            (QuotientGroup.Quotient.commGroup
              (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08TotallyPositivePrincipalIdeals K)).toDivisionMonoid
            _ _
        _ = (signClassMap x)⁻¹ * (signClassMap y)⁻¹ :=
          hcomm _ _)
  let f : Chapter11IdeleGroup K →*
      LastLib.Book04AdelesAndIdeles.Chapter08.Chapter08NarrowClassGroup K :=
    MonoidHom.mk' (fun x =>
      q ((chapter11CanonicalIdeleIdealMap K).toIdeal x) * signClassInvMap x) (by
      intro x y
      rw [signClassInvMap.map_mul,
        (chapter11CanonicalIdeleIdealMap K).toIdeal.map_mul, q.map_mul]
      calc
        q ((chapter11CanonicalIdeleIdealMap K).toIdeal x) *
              q ((chapter11CanonicalIdeleIdealMap K).toIdeal y) *
              (signClassInvMap x * signClassInvMap y) =
            (q ((chapter11CanonicalIdeleIdealMap K).toIdeal x) *
                signClassInvMap x) *
              (q ((chapter11CanonicalIdeleIdealMap K).toIdeal y) *
                signClassInvMap y) := by
          calc
            q ((chapter11CanonicalIdeleIdealMap K).toIdeal x) *
                  q ((chapter11CanonicalIdeleIdealMap K).toIdeal y) *
                  (signClassInvMap x * signClassInvMap y) =
                q ((chapter11CanonicalIdeleIdealMap K).toIdeal x) *
                  (q ((chapter11CanonicalIdeleIdealMap K).toIdeal y) *
                    signClassInvMap x) * signClassInvMap y := by
                      simp only [mul_assoc]
            _ = q ((chapter11CanonicalIdeleIdealMap K).toIdeal x) *
                  (signClassInvMap x *
                    q ((chapter11CanonicalIdeleIdealMap K).toIdeal y)) *
                  signClassInvMap y := by
                      rw [hcomm
                        (q ((chapter11CanonicalIdeleIdealMap K).toIdeal y))
                        (signClassInvMap x)]
            _ = (q ((chapter11CanonicalIdeleIdealMap K).toIdeal x) *
                  signClassInvMap x) *
                (q ((chapter11CanonicalIdeleIdealMap K).toIdeal y) *
                  signClassInvMap y) := by
                      simp only [mul_assoc])
  have hprincipal : ∀ a : Kˣ,
      q (toPrincipalIdeal (𝓞 K) K a) =
        LastLib.Book04AdelesAndIdeles.Chapter08.chapter08SignToNarrowClass K
          (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08SignOfUnit a) := by
    intro a
    let b : Kˣ :=
      LastLib.Book04AdelesAndIdeles.Chapter08.chapter08SignRepresentative
        (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08SignOfUnit a)
    obtain ⟨d, hd⟩ := hfactor (a := a) (b := b)
      (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08SignRepresentative_sign
        (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08SignOfUnit a)).symm
    change QuotientGroup.mk'
        (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08TotallyPositivePrincipalIdeals K)
        (toPrincipalIdeal (𝓞 K) K a) =
      QuotientGroup.mk'
        (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08TotallyPositivePrincipalIdeals K)
        (toPrincipalIdeal (𝓞 K) K b)
    apply (QuotientGroup.mk'_eq_mk'
      (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08TotallyPositivePrincipalIdeals K)).2
    refine ⟨toPrincipalIdeal (𝓞 K) K (d : Kˣ), ⟨d, rfl⟩, ?_⟩
    simpa [b, mul_assoc, mul_comm, mul_left_comm] using
      (congrArg (toPrincipalIdeal (𝓞 K) K) hd).symm
  have hsign_principal : ∀ a : Kˣ,
      signMap (chapter11PrincipalIdeleHom (K := K) a) =
        LastLib.Book04AdelesAndIdeles.Chapter08.chapter08SignOfUnit a := by
    intro a
    funext w
    apply Units.ext
    change SignType.sign
        (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
          ((algebraMap K (NumberField.InfiniteAdeleRing K) (a : K)) w.1)) =
      SignType.sign
        (NumberField.InfinitePlace.embedding_of_isReal w.2 (a : K))
    rw [NumberField.InfiniteAdeleRing.algebraMap_apply]
    rw [NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe]
    simp [WithAbs.equiv]
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨I, rfl⟩ := QuotientGroup.mk'_surjective
      (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08TotallyPositivePrincipalIdeals K) z
    obtain ⟨y, hy⟩ :=
      LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_idele_ideal_surjective K I
    let x : Chapter11IdeleGroup K :=
      (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K).symm (1, y)
    have hxideal : (chapter11CanonicalIdeleIdealMap K).toIdeal x = I := by
      change LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleIdealMap K y = I
      exact hy
    have hsignx : signMap x = 1 := by
      funext w
      apply Units.ext
      have hfirst :
          (((x : Chapter11IdeleGroup K) : Chapter11AdeleRing K).1 w.1) = 1 := by
        change (((((LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K).symm
          (1, y) :
          LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09Idele K) :
            LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09Adele K).1 w.1)) = 1
        rfl
      change SignType.sign
          (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
            (((x : Chapter11IdeleGroup K) : Chapter11AdeleRing K).1 w.1)) = 1
      rw [hfirst]
      simp
    refine ⟨x, ?_⟩
    change q ((chapter11CanonicalIdeleIdealMap K).toIdeal x) *
        (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08SignToNarrowClass K
          (signMap x))⁻¹ =
      QuotientGroup.mk'
        (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08TotallyPositivePrincipalIdeals K) I
    rw [hxideal, hsignx]
    simp only [q, map_one, inv_one]
    exact (QuotientGroup.Quotient.commGroup
      (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08TotallyPositivePrincipalIdeals K)).mul_one _
  have hfull_of_narrow : ∀ {z : Chapter11IdeleGroup K},
      z ∈ chapter11RayUnitSubgroup (RayModulus.narrow (K := K)) →
        z ∈ chapter11FullFiniteUnitSubgroup (K := K) := by
    intro z hz
    change
      (∀ v, chapter11IdeleFiniteComponent K v z ∈
        chapter11FiniteLocalUnitGroup K v 0) ∧ _
    change
        (∀ v, chapter11IdeleFiniteComponent K v z ∈
        chapter11FiniteLocalUnitGroup K v
          ((RayModulus.narrow (K := K)).finiteExponent v)) ∧ _ at hz
    constructor
    · intro v
      simpa [RayModulus.narrow] using hz.1 v
    · simp [RayModulus.trivial]
  have hker :
      chapter11PrincipalIdeleSubgroup (K := K) ⊔
          chapter11RayUnitSubgroup (RayModulus.narrow (K := K)) = f.ker := by
    ext x
    constructor
    · intro hx
      apply (MonoidHom.mem_ker).2
      rcases Subgroup.mem_sup.mp hx with ⟨y, hy, z, hz, rfl⟩
      rcases hy with ⟨a, rfl⟩
      have hzfull := hfull_of_narrow hz
      have hzideal : (chapter11CanonicalIdeleIdealMap K).toIdeal z = 1 := by
        exact MonoidHom.mem_ker.mp (show z ∈
          (chapter11CanonicalIdeleIdealMap K).toIdeal.ker by
          rw [(chapter11CanonicalIdeleIdealMap K).kernel_eq_full_finite_units]
          exact hzfull)
      have hsignz : signMap z = 1 := by
        funext w
        exact hz.2 w.1 (by
          simp [RayModulus.narrow, w.2])
      change q ((chapter11CanonicalIdeleIdealMap K).toIdeal
          (chapter11PrincipalIdeleHom (K := K) a * z)) *
        (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08SignToNarrowClass K
          (signMap (chapter11PrincipalIdeleHom (K := K) a * z)))⁻¹ = 1
      rw [(chapter11CanonicalIdeleIdealMap K).toIdeal.map_mul,
        (chapter11CanonicalIdeleIdealMap K).map_principal, hzideal, mul_one,
        signMap.map_mul, hsign_principal, hsignz]
      simp only [mul_one]
      rw [hprincipal]
      simp
    · intro hx
      change q ((chapter11CanonicalIdeleIdealMap K).toIdeal x) *
          (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08SignToNarrowClass K
            (signMap x))⁻¹ = 1 at hx
      let s : LastLib.Book04AdelesAndIdeles.Chapter08.Chapter08SignGroup K := signMap x
      let b : Kˣ :=
        LastLib.Book04AdelesAndIdeles.Chapter08.chapter08SignRepresentative s
      have hq : q ((chapter11CanonicalIdeleIdealMap K).toIdeal x) =
          LastLib.Book04AdelesAndIdeles.Chapter08.chapter08SignToNarrowClass K s := by
        have hx' : q ((chapter11CanonicalIdeleIdealMap K).toIdeal x) *
            (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08SignToNarrowClass K s)⁻¹ = 1 := by
          simpa [s] using hx
        calc
          q ((chapter11CanonicalIdeleIdealMap K).toIdeal x) =
              q ((chapter11CanonicalIdeleIdealMap K).toIdeal x) *
                (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08SignToNarrowClass K s)⁻¹ *
                  LastLib.Book04AdelesAndIdeles.Chapter08.chapter08SignToNarrowClass K s := by
                    simp [mul_assoc]
          _ = 1 * LastLib.Book04AdelesAndIdeles.Chapter08.chapter08SignToNarrowClass K s := by
            rw [hx']
          _ = LastLib.Book04AdelesAndIdeles.Chapter08.chapter08SignToNarrowClass K s := by
            exact (QuotientGroup.Quotient.commGroup
              (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08TotallyPositivePrincipalIdeals K)).one_mul _
      have hqb : q (toPrincipalIdeal (𝓞 K) K b) =
          LastLib.Book04AdelesAndIdeles.Chapter08.chapter08SignToNarrowClass K s := by
        rw [hprincipal b]
        simpa [b, s] using
          congrArg (fun t : LastLib.Book04AdelesAndIdeles.Chapter08.Chapter08SignGroup K =>
            LastLib.Book04AdelesAndIdeles.Chapter08.chapter08SignToNarrowClass K t)
            (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08SignRepresentative_sign s)
      have hquot : q ((chapter11CanonicalIdeleIdealMap K).toIdeal x) =
          q (toPrincipalIdeal (𝓞 K) K b) := hq.trans hqb.symm
      let I : Chapter11FractionalIdealUnitGroup K :=
        (chapter11CanonicalIdeleIdealMap K).toIdeal x
      have hquot' : QuotientGroup.mk'
          (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08TotallyPositivePrincipalIdeals K) I =
          QuotientGroup.mk'
            (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08TotallyPositivePrincipalIdeals K)
              (toPrincipalIdeal (𝓞 K) K b) := by
        simpa [q, I] using hquot
      rw [QuotientGroup.mk'_eq_mk'] at hquot'
      obtain ⟨z, hz, hrel⟩ := hquot'
      rcases hz with ⟨d, rfl⟩
      have hd : (d : Kˣ) ∈
          LastLib.Book04AdelesAndIdeles.Chapter08.chapter08TotallyPositiveElements K :=
        d.property
      let a : Kˣ := b * (d : Kˣ)⁻¹
      have hI : I = toPrincipalIdeal (𝓞 K) K a := by
        have hrel' : I * toPrincipalIdeal (𝓞 K) K (d : Kˣ) =
            toPrincipalIdeal (𝓞 K) K b := by
          simpa [LastLib.Book04AdelesAndIdeles.Chapter08.chapter08TotallyPositivePrincipalHom]
            using hrel
        calc
          I = I * toPrincipalIdeal (𝓞 K) K (d : Kˣ) *
              (toPrincipalIdeal (𝓞 K) K (d : Kˣ))⁻¹ := by simp [mul_assoc]
          _ = toPrincipalIdeal (𝓞 K) K b *
              (toPrincipalIdeal (𝓞 K) K (d : Kˣ))⁻¹ := by rw [hrel']
          _ = toPrincipalIdeal (𝓞 K) K a := by simp [a]
      let y : Chapter11IdeleGroup K :=
        x * (chapter11PrincipalIdeleHom (K := K) a)⁻¹
      have hyideal : (chapter11CanonicalIdeleIdealMap K).toIdeal y = 1 := by
        dsimp [y]
        rw [(chapter11CanonicalIdeleIdealMap K).toIdeal.map_mul,
          map_inv, (chapter11CanonicalIdeleIdealMap K).map_principal]
        change I * (toPrincipalIdeal (𝓞 K) K a)⁻¹ = 1
        rw [hI]
        simp
      have hyfull : y ∈ chapter11FullFiniteUnitSubgroup (K := K) := by
        have hyker : y ∈ (chapter11CanonicalIdeleIdealMap K).toIdeal.ker :=
          (MonoidHom.mem_ker).2 hyideal
        rw [(chapter11CanonicalIdeleIdealMap K).kernel_eq_full_finite_units] at hyker
        exact hyker
      have hsigna :
          LastLib.Book04AdelesAndIdeles.Chapter08.chapter08SignOfUnit a = s := by
        have hsignb :=
          LastLib.Book04AdelesAndIdeles.Chapter08.chapter08SignRepresentative_sign s
        funext w
        apply Units.ext
        have hdp : 0 <
            LastLib.Book04AdelesAndIdeles.Chapter08.chapter08RealEmbedding w
              ((d : Kˣ) : K) :=
          hd w
        have hdpinv : 0 <
            (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08RealEmbedding w
              ((d : Kˣ) : K))⁻¹ :=
          inv_pos.mpr hdp
        change SignType.sign
            (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08RealEmbedding w (a : K)) =
          (s w : SignType)
        rw [show (a : K) = (b : K) * (((d : Kˣ) : K)⁻¹) by simp [a]]
        rw [map_mul, map_inv₀]
        rw [sign_mul, sign_pos hdpinv, mul_one]
        exact congrArg (fun t : SignTypeˣ => (t : SignType))
          (congrFun hsignb w)
      have hsigny : signMap y = 1 := by
        dsimp [y]
        rw [signMap.map_mul, map_inv, show signMap x = s by rfl,
          hsign_principal, hsigna]
        simp
      apply Subgroup.mem_sup.mpr
      refine ⟨chapter11PrincipalIdeleHom (K := K) a,
        ⟨a, rfl⟩, y, ?_, ?_⟩
      · change
          (∀ v, chapter11IdeleFiniteComponent K v y ∈
            chapter11FiniteLocalUnitGroup K v
              ((RayModulus.narrow (K := K)).finiteExponent v)) ∧ _
        constructor
        · intro v
          simpa [RayModulus.narrow, RayModulus.trivial] using hyfull.1 v
        · intro v hv
          exact congrFun hsigny ⟨v, (RayModulus.narrow (K := K)).infinitePart_isReal v hv⟩
      · simp [y]
  exact ⟨QuotientGroup.liftEquiv
    (chapter11PrincipalIdeleSubgroup (K := K) ⊔
      chapter11RayUnitSubgroup (RayModulus.narrow (K := K))) hsurj hker⟩

theorem chapter11_trivial_modulus_has_no_finite_or_infinite_condition
    (K : Type*) [Field K] [NumberField K] :
    (RayModulus.trivial (K := K)).finiteExponent = 0 ∧
      (RayModulus.trivial (K := K)).infinitePart = ∅ := by
  simp [RayModulus.trivial]

theorem chapter11_narrow_modulus_has_all_real_places
    (K : Type*) [Field K] [NumberField K] :
    (RayModulus.narrow (K := K)).finiteExponent = 0 ∧
      (RayModulus.narrow (K := K)).infinitePart =
        Finset.univ.filter NumberField.InfinitePlace.IsReal := by
  simp [RayModulus.narrow]

end
