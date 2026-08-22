import LastLib.Book04AdelesAndIdeles.Chapter08.Dependencies
import Mathlib.Data.Sign.Basic

namespace LastLib.Book04AdelesAndIdeles.Chapter08

noncomputable section

open scoped BigOperators nonZeroDivisors RestrictedProduct
open IsDedekindDomain NumberField

/-! ## 8.6 Ordinary and narrow ideal classes -/

abbrev Chapter08RealPlaces (K : Type*) [Field K] [NumberField K] :=
  {w : NumberField.InfinitePlace K // w.IsReal}

abbrev Chapter08SignGroup (K : Type*) [Field K] [NumberField K] :=
  Chapter08RealPlaces K → SignTypeˣ

noncomputable def chapter08RealEmbedding
    {K : Type*} [Field K] [NumberField K]
    (w : Chapter08RealPlaces K) : K →+* ℝ :=
  NumberField.InfinitePlace.embedding_of_isReal w.2

noncomputable def chapter08SignOfUnit
    {K : Type*} [Field K] [NumberField K]
  (a : Kˣ) (w : Chapter08RealPlaces K) : SignTypeˣ :=
  Units.mk0 (SignType.sign (chapter08RealEmbedding w (a : K))) (by
    exact (sign_ne_zero).2 ((map_ne_zero (chapter08RealEmbedding w)).2 a.ne_zero))

def chapter08SignHom (K : Type*) [Field K] [NumberField K] :
    (Chapter08Integers K)ˣ →* Chapter08SignGroup K where
  toFun := fun u w => chapter08SignOfUnit (Units.map (algebraMap (Chapter08Integers K) K) u) w
  map_one' := by
    funext w
    apply Units.ext
    simp [chapter08SignOfUnit]
  map_mul' := by
    intro x y
    funext w
    apply Units.ext
    simp [chapter08SignOfUnit, sign_mul]

def chapter08TotallyPositiveElements (K : Type*) [Field K] [NumberField K] :
    Subgroup Kˣ where
  carrier := {a | ∀ w : Chapter08RealPlaces K,
    0 < chapter08RealEmbedding w (a : K)}
  one_mem' := by
    intro w
    simp [chapter08RealEmbedding]
  mul_mem' := by
    intro a b ha hb w
    simpa [chapter08RealEmbedding] using mul_pos (ha w) (hb w)
  inv_mem' := by
    intro a ha w
    simpa [chapter08RealEmbedding] using inv_pos.mpr (ha w)

def chapter08TotallyPositivePrincipalHom (K : Type*) [Field K] [NumberField K] :
    chapter08TotallyPositiveElements K →* Chapter08IdealGroup K :=
  (toPrincipalIdeal (Chapter08Integers K) K).comp
    (chapter08TotallyPositiveElements K).subtype

def chapter08TotallyPositivePrincipalIdeals (K : Type*) [Field K] [NumberField K] :
    Subgroup (Chapter08IdealGroup K) :=
  MonoidHom.range (chapter08TotallyPositivePrincipalHom K)

abbrev Chapter08NarrowClassGroup (K : Type*) [Field K] [NumberField K] :=
  Chapter08IdealGroup K ⧸ chapter08TotallyPositivePrincipalIdeals K

abbrev Chapter08OrdinaryIdealQuotient (K : Type*) [Field K] [NumberField K] :=
  Chapter08IdealGroup K ⧸ (toPrincipalIdeal (Chapter08Integers K) K).range

def chapter08NarrowToOrdinary (K : Type*) [Field K] [NumberField K] :
    Chapter08NarrowClassGroup K →* Chapter08OrdinaryIdealQuotient K :=
  QuotientGroup.lift (chapter08TotallyPositivePrincipalIdeals K)
    (QuotientGroup.mk' (toPrincipalIdeal (Chapter08Integers K) K).range) (by
      intro x hx
      rcases hx with ⟨a, rfl⟩
      rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact ⟨a, rfl⟩)

theorem chapter08_narrow_to_ordinary_surjective
    (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (chapter08NarrowToOrdinary K) := by
  intro y
  obtain ⟨I, rfl⟩ := QuotientGroup.mk'_surjective
    ((toPrincipalIdeal (Chapter08Integers K) K).range) y
  refine ⟨QuotientGroup.mk' (chapter08TotallyPositivePrincipalIdeals K) I, ?_⟩
  rfl

def chapter08NarrowToClassGroup (K : Type*) [Field K] [NumberField K] :
    Chapter08NarrowClassGroup K →* Chapter08OrdinaryClassGroup K :=
  (ClassGroup.equiv K).symm.toMonoidHom.comp (chapter08NarrowToOrdinary K)

theorem chapter08_narrow_to_class_group_surjective
    (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (chapter08NarrowToClassGroup K) := by
  exact (ClassGroup.equiv K).symm.surjective.comp
    (chapter08_narrow_to_ordinary_surjective K)

/-! Weak approximation supplies a field element with any prescribed real sign pattern.  This is
the bridge needed to define the sign-to-narrow-class map. -/

theorem chapter08_sign_pattern_realization
    (K : Type*) [Field K] [NumberField K]
    (s : Chapter08SignGroup K) :
    ∃ a : Kˣ, chapter08SignOfUnit a = s := by
  classical
  let U : Set ((w : NumberField.InfinitePlace K) → WithAbs w.1) :=
    Set.univ.pi (fun w =>
      if hw : w.IsReal then
        ((chapter08RealEmbedding ⟨w, hw⟩).comp
          (WithAbs.equiv w.1).toRingHom) ⁻¹'
          (if (s ⟨w, hw⟩ : SignType) = 1 then (Set.Ioi (0 : ℝ) : Set ℝ)
            else (Set.Iio (0 : ℝ) : Set ℝ))
      else
        ({0} : Set (WithAbs w.1))ᶜ)
  have hUopen : IsOpen U := by
    apply isOpen_set_pi Set.finite_univ
    intro w hw
    by_cases hreal : w.IsReal
    · by_cases hspos : (s ⟨w, hreal⟩ : SignType) = 1
      · simpa [chapter08RealEmbedding, hreal, hspos] using isOpen_Ioi.preimage
          (w.isometry_embedding_of_isReal hreal).continuous
      · simpa [chapter08RealEmbedding, hreal, hspos] using isOpen_Iio.preimage
          (w.isometry_embedding_of_isReal hreal).continuous
    · simp [hreal]
  let f : (w : NumberField.InfinitePlace K) → WithAbs w.1 := fun w =>
    if hw : w.IsReal then
      if (s ⟨w, hw⟩ : SignType) = 1 then (1 : WithAbs w.1) else -1
    else 1
  have hfU : f ∈ U := by
    intro w hw
    dsimp [f]
    split_ifs with hreal hspos
    · change (0 : ℝ) <
        (chapter08RealEmbedding ⟨w, hreal⟩)
          (WithAbs.equiv w.1 (1 : WithAbs w.1))
      simp
    · change (chapter08RealEmbedding ⟨w, hreal⟩)
          (WithAbs.equiv w.1 (-1 : WithAbs w.1)) < (0 : ℝ)
      simp
    · exact one_ne_zero
  obtain ⟨a, haU⟩ :=
    (NumberField.InfinitePlace.denseRange_algebraMap_pi K).exists_mem_open hUopen
      ⟨f, hfU⟩
  have ha : a ≠ 0 := by
    intro haz
    let w : NumberField.InfinitePlace K :=
      Classical.choice (inferInstance : Nonempty (NumberField.InfinitePlace K))
    have hcoord := haU w (Set.mem_univ w)
    rw [haz, map_zero] at hcoord
    have hreal_or : w.IsReal ∨ ¬w.IsReal := em w.IsReal
    rcases hreal_or with hreal | hnotreal
    · dsimp [U] at hcoord
      by_cases hspos : (s ⟨w, hreal⟩ : SignType) = 1
      · simp [hreal, hspos] at hcoord
      · simp [hreal, hspos] at hcoord
    · dsimp [U] at hcoord
      simp only [dif_neg hnotreal] at hcoord
      exact hcoord rfl
  refine ⟨Units.mk0 a ha, ?_⟩
  funext w
  apply Units.ext
  have hcoord := haU w.1 (Set.mem_univ w.1)
  have hsign : SignType.sign
      (chapter08RealEmbedding w (a : K)) = (s w : SignType) := by
    by_cases hspos : (s w : SignType) = 1
    · have hpos : 0 < chapter08RealEmbedding w (a : K) := by
        have h := hcoord
        simp only [dif_pos w.2, hspos] at h
        change (0 : ℝ) <
          (chapter08RealEmbedding w)
            (WithAbs.equiv w.1.1 ((algebraMap K (WithAbs w.1.1)) a))
        simpa [chapter08RealEmbedding, hspos] using h
      rw [sign_pos hpos]
      exact hspos.symm
    · have hneg : chapter08RealEmbedding w (a : K) < 0 := by
        have h := hcoord
        simp only [dif_pos w.2, hspos] at h
        change (chapter08RealEmbedding w)
            (WithAbs.equiv w.1.1 ((algebraMap K (WithAbs w.1.1)) a)) < (0 : ℝ)
        simpa [chapter08RealEmbedding, hspos] using h
      rw [sign_neg hneg]
      have hsneg : (s w : SignType) = -1 := by
        rcases SignType.trichotomy (s w : SignType) with hneg | hzero | hpos
        · exact hneg
        · exact False.elim ((s w).ne_zero hzero)
        · exact False.elim (hspos hpos)
      exact hsneg.symm
  simpa [chapter08SignOfUnit] using hsign

noncomputable def chapter08SignRepresentative
    {K : Type*} [Field K] [NumberField K]
    (s : Chapter08SignGroup K) : Kˣ :=
  Classical.choose (chapter08_sign_pattern_realization K s)

theorem chapter08SignRepresentative_sign
    {K : Type*} [Field K] [NumberField K]
    (s : Chapter08SignGroup K) :
    chapter08SignOfUnit (chapter08SignRepresentative s) = s := by
  exact Classical.choose_spec (chapter08_sign_pattern_realization K s)

def chapter08SignToNarrowClass (K : Type*) [Field K] [NumberField K] :
    Chapter08SignGroup K →* Chapter08NarrowClassGroup K where
  toFun := fun s =>
    QuotientGroup.mk' (chapter08TotallyPositivePrincipalIdeals K)
      (toPrincipalIdeal (Chapter08Integers K) K (chapter08SignRepresentative s))
  map_one' := by
    have ha : chapter08SignRepresentative (1 : Chapter08SignGroup K) ∈
        chapter08TotallyPositiveElements K := by
      intro w
      have hs := congrFun
        (chapter08SignRepresentative_sign (1 : Chapter08SignGroup K)) w
      have hs' := congrArg (fun z : SignTypeˣ => (z : SignType)) hs
      change SignType.sign (chapter08RealEmbedding w
        (chapter08SignRepresentative (1 : Chapter08SignGroup K) : K)) = 1 at hs'
      exact sign_eq_one_iff.mp hs'
    apply (QuotientGroup.eq_one_iff _).2
    refine ⟨⟨chapter08SignRepresentative (1 : Chapter08SignGroup K), ha⟩, ?_⟩
    rfl
  map_mul' := by
    intro s t
    change ((toPrincipalIdeal (Chapter08Integers K) K
      (chapter08SignRepresentative (s * t))) : Chapter08NarrowClassGroup K) =
      ((toPrincipalIdeal (Chapter08Integers K) K
        (chapter08SignRepresentative s)) : Chapter08NarrowClassGroup K) *
        ((toPrincipalIdeal (Chapter08Integers K) K
          (chapter08SignRepresentative t)) : Chapter08NarrowClassGroup K)
    rw [← QuotientGroup.mk_mul]
    apply (QuotientGroup.mk'_eq_mk' (chapter08TotallyPositivePrincipalIdeals K)).2
    let d : Kˣ :=
      (chapter08SignRepresentative (s * t))⁻¹ *
        chapter08SignRepresentative s * chapter08SignRepresentative t
    have hd : d ∈ chapter08TotallyPositiveElements K := by
      intro w
      have hst := congrArg (fun z : SignTypeˣ => (z : SignType))
        (congrFun (chapter08SignRepresentative_sign (s * t)) w)
      have hs := congrArg (fun z : SignTypeˣ => (z : SignType))
        (congrFun (chapter08SignRepresentative_sign s) w)
      have ht := congrArg (fun z : SignTypeˣ => (z : SignType))
        (congrFun (chapter08SignRepresentative_sign t) w)
      change SignType.sign (chapter08RealEmbedding w
        (chapter08SignRepresentative (s * t) : K)) =
        (s w : SignType) * (t w : SignType) at hst
      change SignType.sign (chapter08RealEmbedding w
        (chapter08SignRepresentative s : K)) = (s w : SignType) at hs
      change SignType.sign (chapter08RealEmbedding w
        (chapter08SignRepresentative t : K)) = (t w : SignType) at ht
      have hz : chapter08RealEmbedding w
          (chapter08SignRepresentative (s * t) : K) ≠ 0 :=
        (map_ne_zero (chapter08RealEmbedding w)).2
          (chapter08SignRepresentative (s * t)).ne_zero
      have hsign_inv : SignType.sign
          ((chapter08RealEmbedding w
            (chapter08SignRepresentative (s * t) : K))⁻¹) =
          SignType.sign (chapter08RealEmbedding w
            (chapter08SignRepresentative (s * t) : K)) := by
        by_cases hpos : 0 < chapter08RealEmbedding w
            (chapter08SignRepresentative (s * t) : K)
        · rw [sign_pos (inv_pos.mpr hpos), sign_pos hpos]
        · have hneg : chapter08RealEmbedding w
              (chapter08SignRepresentative (s * t) : K) < 0 :=
            lt_of_le_of_ne (le_of_not_gt hpos) hz
          rw [sign_neg (inv_lt_zero'.2 hneg), sign_neg hneg]
      have hsign : SignType.sign (chapter08RealEmbedding w (d : K)) = 1 := by
        simp [d, map_mul, map_inv₀, sign_mul, hs, ht, mul_assoc]
        rw [hsign_inv, hst]
        exact inv_mul_cancel₀ (mul_ne_zero (s w).ne_zero (t w).ne_zero)
      exact sign_eq_one_iff.mp hsign
    refine ⟨toPrincipalIdeal (Chapter08Integers K) K d, ?_, ?_⟩
    · exact ⟨⟨d, hd⟩, rfl⟩
    · simp [d, mul_assoc]

theorem chapter08_sign_narrow_exact
    (K : Type*) [Field K] [NumberField K] :
    chapter08IsExact (chapter08SignHom K) (chapter08SignToNarrowClass K) ∧
      chapter08IsExact (chapter08SignToNarrowClass K) (chapter08NarrowToOrdinary K) ∧
      Function.Surjective (chapter08NarrowToOrdinary K) := by
  have hfactor : ∀ {a b : Kˣ},
      chapter08SignOfUnit a = chapter08SignOfUnit b →
        ∃ d : chapter08TotallyPositiveElements K, b = a * d := by
    intro a b hab
    let d : Kˣ := a⁻¹ * b
    have hd : d ∈ chapter08TotallyPositiveElements K := by
      intro w
      have hs := congrArg (fun z : SignTypeˣ => (z : SignType))
        (congrFun hab w)
      change SignType.sign (chapter08RealEmbedding w (a : K)) =
        SignType.sign (chapter08RealEmbedding w (b : K)) at hs
      have ha0 : chapter08RealEmbedding w (a : K) ≠ 0 :=
        (map_ne_zero (chapter08RealEmbedding w)).2 a.ne_zero
      have hsign_inv : SignType.sign
          ((chapter08RealEmbedding w (a : K))⁻¹) =
          SignType.sign (chapter08RealEmbedding w (a : K)) := by
        by_cases hpos : 0 < chapter08RealEmbedding w (a : K)
        · rw [sign_pos (inv_pos.mpr hpos), sign_pos hpos]
        · have hneg : chapter08RealEmbedding w (a : K) < 0 :=
            lt_of_le_of_ne (le_of_not_gt hpos) ha0
          rw [sign_neg (inv_lt_zero'.2 hneg), sign_neg hneg]
      have hsign : SignType.sign (chapter08RealEmbedding w (d : K)) = 1 := by
        simp [d, map_mul, map_inv₀, sign_mul]
        rw [hsign_inv, hs]
        rcases SignType.trichotomy
            (SignType.sign (chapter08RealEmbedding w (b : K))) with hneg | hzero | hpos
        · rw [hneg]
          simp
        · exact False.elim ((sign_ne_zero).2
            ((map_ne_zero (chapter08RealEmbedding w)).2 b.ne_zero) hzero)
        · rw [hpos]
          simp
      exact sign_eq_one_iff.mp hsign
    refine ⟨⟨d, hd⟩, ?_⟩
    simp [d]
  have hglobal : ∀ {c : Kˣ},
      toPrincipalIdeal (Chapter08Integers K) K c = 1 →
        ∃ u : (Chapter08Integers K)ˣ,
          c = Units.map (algebraMap (Chapter08Integers K) K).toMonoidHom u := by
    intro c hc
    have hspan : Submodule.span (Chapter08Integers K) {(c : K)} = 1 := by
      have hcoe := congrArg (fun I : Chapter08IdealGroup K =>
        ((I : Chapter08FractionalIdeal K) :
          Submodule (Chapter08Integers K) K)) hc
      simpa [coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton] using hcoe
    obtain ⟨u, hu⟩ := (Submodule.span_singleton_eq_one_iff).1 hspan
    refine ⟨u, ?_⟩
    apply Units.ext
    simpa using hu
  constructor
  · rw [chapter08IsExact]
    apply le_antisymm
    · rintro q ⟨u, rfl⟩
      change chapter08SignToNarrowClass K (chapter08SignHom K u) = 1
      apply (QuotientGroup.eq_one_iff _).2
      let b : Kˣ := Units.map (algebraMap (Chapter08Integers K) K).toMonoidHom u
      let a : Kˣ := chapter08SignRepresentative (chapter08SignHom K u)
      have hsign : chapter08SignOfUnit b = chapter08SignOfUnit a := by
        have h := chapter08SignRepresentative_sign
          (chapter08SignHom K u)
        simpa [a, b, chapter08SignHom] using h.symm
      obtain ⟨d, hda⟩ := hfactor hsign
      have hd : (d : Kˣ) ∈ chapter08TotallyPositiveElements K := d.property
      have hb : toPrincipalIdeal (Chapter08Integers K) K b = 1 := by
        apply Units.ext
        apply FractionalIdeal.coeToSubmodule_injective
        have hspan : Submodule.span (Chapter08Integers K)
            {((algebraMap (Chapter08Integers K) K) (u : Chapter08Integers K))} = 1 :=
          (Submodule.span_singleton_eq_one_iff).2 ⟨u, rfl⟩
        simpa [b, coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton] using hspan
      change toPrincipalIdeal (Chapter08Integers K) K a ∈
        chapter08TotallyPositivePrincipalIdeals K
      rw [hda, map_mul, hb, one_mul]
      exact ⟨d, rfl⟩
    · rintro q hq
      let a : Kˣ := chapter08SignRepresentative q
      have hqa : QuotientGroup.mk'
          (chapter08TotallyPositivePrincipalIdeals K)
          (toPrincipalIdeal (Chapter08Integers K) K a) = 1 := by
        simpa [a, chapter08SignToNarrowClass] using hq
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hqa
      obtain ⟨d, hda⟩ := hqa
      have hd : (d : Kˣ) ∈ chapter08TotallyPositiveElements K := d.property
      change toPrincipalIdeal (Chapter08Integers K) K (d : Kˣ) =
        toPrincipalIdeal (Chapter08Integers K) K a at hda
      have hc : toPrincipalIdeal (Chapter08Integers K) K
          ((d : Kˣ)⁻¹ * a) = 1 := by
        simp [hda]
      obtain ⟨u, hu⟩ := hglobal hc
      refine ⟨u, ?_⟩
      have ha : a = (d : Kˣ) *
          Units.map (algebraMap (Chapter08Integers K) K).toMonoidHom u := by
        calc
          a = (d : Kˣ) * ((d : Kˣ)⁻¹ * a) := by simp
          _ = (d : Kˣ) *
              Units.map (algebraMap (Chapter08Integers K) K).toMonoidHom u := by
            rw [hu]
      have hsign : chapter08SignOfUnit
          (Units.map (algebraMap (Chapter08Integers K) K).toMonoidHom u) =
          chapter08SignOfUnit a := by
        funext w
        apply Units.ext
        change SignType.sign
            (chapter08RealEmbedding w
              (Units.map (algebraMap (Chapter08Integers K) K).toMonoidHom u : K)) =
          SignType.sign (chapter08RealEmbedding w (a : K))
        rw [ha]
        simp [map_mul, sign_mul, sign_pos (hd w)]
      have hrep := chapter08SignRepresentative_sign q
      simpa [chapter08SignHom] using hsign.trans hrep
  constructor
  · rw [chapter08IsExact]
    apply le_antisymm
    · rintro q ⟨s, rfl⟩
      change chapter08NarrowToOrdinary K
          (chapter08SignToNarrowClass K s) = 1
      change QuotientGroup.mk' (toPrincipalIdeal (Chapter08Integers K) K).range
        (toPrincipalIdeal (Chapter08Integers K) K
          (chapter08SignRepresentative s)) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact ⟨chapter08SignRepresentative s, rfl⟩
    · rintro q hq
      obtain ⟨I, rfl⟩ := QuotientGroup.mk'_surjective
        (chapter08TotallyPositivePrincipalIdeals K) q
      change QuotientGroup.mk' (toPrincipalIdeal (Chapter08Integers K) K).range I = 1 at hq
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hq
      obtain ⟨a, rfl⟩ := hq
      refine ⟨chapter08SignOfUnit a, ?_⟩
      obtain ⟨d, hda⟩ := hfactor
        (chapter08SignRepresentative_sign (chapter08SignOfUnit a))
      have hd : (d : Kˣ) ∈ chapter08TotallyPositiveElements K := d.property
      change QuotientGroup.mk' (chapter08TotallyPositivePrincipalIdeals K)
          (toPrincipalIdeal (Chapter08Integers K) K
            (chapter08SignRepresentative (chapter08SignOfUnit a))) =
        QuotientGroup.mk' (chapter08TotallyPositivePrincipalIdeals K)
          (toPrincipalIdeal (Chapter08Integers K) K a)
      apply (QuotientGroup.mk'_eq_mk' (chapter08TotallyPositivePrincipalIdeals K)).2
      refine ⟨toPrincipalIdeal (Chapter08Integers K) K d,
        ⟨⟨d, hd⟩, rfl⟩, ?_⟩
      simpa only [map_mul] using
        congrArg (toPrincipalIdeal (Chapter08Integers K) K) hda.symm
  exact chapter08_narrow_to_ordinary_surjective K

theorem chapter08_narrow_class_group_maps_onto_ordinary
    (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (chapter08NarrowToClassGroup K) :=
  chapter08_narrow_to_class_group_surjective K

theorem chapter08_narrow_equals_ordinary_of_sign_surjective
    (K : Type*) [Field K] [NumberField K]
    (hs : Function.Surjective (chapter08SignHom K)) :
    Function.Bijective (chapter08NarrowToOrdinary K) := by
  have hex := chapter08_sign_narrow_exact K
  have hrange : MonoidHom.range (chapter08SignHom K) = ⊤ := by
    apply le_antisymm le_top
    intro s _
    obtain ⟨u, hu⟩ := hs s
    exact ⟨u, hu⟩
  have hkerSign : MonoidHom.ker (chapter08SignToNarrowClass K) = ⊤ := by
    rw [← hex.1, hrange]
  have hsignTo : chapter08SignToNarrowClass K = 1 :=
    (MonoidHom.ker_eq_top_iff.mp hkerSign)
  have hkerOrd : MonoidHom.ker (chapter08NarrowToOrdinary K) = ⊥ := by
    rw [← hex.2.1, hsignTo]
    simp
  refine ⟨(MonoidHom.ker_eq_bot_iff _).mp hkerOrd, ?_⟩
  exact chapter08_narrow_to_ordinary_surjective K

def chapter08RealQuadratic (K : Type*) [Field K] [NumberField K] : Prop :=
  Module.finrank ℚ K = 2 ∧ Nonempty (Chapter08RealPlaces K)

def chapter08UnitNormMinusOne (K : Type*) [Field K] [NumberField K] : Prop :=
  ∃ u : (Chapter08Integers K)ˣ, Algebra.norm ℚ (u : K) = -1

theorem chapter08_real_quadratic_norm_minus_one_gives_all_signs
    (K : Type*) [Field K] [NumberField K]
    (hquadratic : chapter08RealQuadratic K)
    (hnorm : chapter08UnitNormMinusOne K) :
    Function.Surjective (chapter08SignHom K) := by
  classical
  rcases hquadratic with ⟨hfinrank, hreal⟩
  have hrank := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [hfinrank] at hrank
  have hrealpos : 0 < NumberField.InfinitePlace.nrRealPlaces K :=
    Fintype.card_pos_iff.mpr hreal
  have hcomplex : NumberField.InfinitePlace.nrComplexPlaces K = 0 := by
    omega
  have hrealcard : NumberField.InfinitePlace.nrRealPlaces K = 2 := by
    omega
  let E := {φ : K →+* ℂ // ComplexEmbedding.IsReal φ}
  have hcardE : Fintype.card E = 2 := by
    change Fintype.card {φ : K →+* ℂ // ComplexEmbedding.IsReal φ} = 2
    rw [NumberField.InfinitePlace.card_real_embeddings K, hrealcard]
  obtain ⟨p₁, p₂, hp₁₂, huniv⟩ :=
    Finset.card_eq_two.mp (show (Finset.univ : Finset E).card = 2 by
      simpa using hcardE)
  let w₁ : Chapter08RealPlaces K := NumberField.InfinitePlace.mkReal p₁
  let w₂ : Chapter08RealPlaces K := NumberField.InfinitePlace.mkReal p₂
  have hwcases (w : Chapter08RealPlaces K) : w = w₁ ∨ w = w₂ := by
    have hp : (NumberField.InfinitePlace.mkReal (K := K)).symm w = p₁ ∨
        (NumberField.InfinitePlace.mkReal (K := K)).symm w = p₂ := by
      have hwmem : (NumberField.InfinitePlace.mkReal (K := K)).symm w ∈
          (Finset.univ : Finset E) := Finset.mem_univ _
      rw [huniv] at hwmem
      simpa using hwmem
    rcases hp with hp | hp
    · left
      simpa [w₁] using congrArg (NumberField.InfinitePlace.mkReal (K := K)) hp
    · right
      simpa [w₂] using congrArg (NumberField.InfinitePlace.mkReal (K := K)) hp
  have hcomplexEmpty : IsEmpty
      {φ : K →+* ℂ // ¬ComplexEmbedding.IsReal φ} := by
    constructor
    intro φ
    have hw : NumberField.InfinitePlace.IsComplex
        (NumberField.InfinitePlace.mk φ.1) :=
      (NumberField.InfinitePlace.isComplex_mk_iff).2 φ.2
    have hcpos : 0 < NumberField.InfinitePlace.nrComplexPlaces K :=
      Fintype.card_pos_iff.mpr ⟨⟨NumberField.InfinitePlace.mk φ.1, hw⟩⟩
    rw [hcomplex] at hcpos
    omega
  have hallreal (φ : K →+* ℂ) : ComplexEmbedding.IsReal φ := by
    by_contra hφ
    exact @IsEmpty.false _ hcomplexEmpty ⟨φ, hφ⟩
  obtain ⟨u, hu⟩ := hnorm
  let a : Kˣ := Units.map (algebraMap (Chapter08Integers K) K) u
  have haNorm : Algebra.norm ℚ (a : K) = -1 := by
    simpa [a] using hu
  have hnormC : algebraMap ℚ ℂ (Algebra.norm ℚ (a : K)) =
      ∏ φ : K →+* ℂ, φ (a : K) := by
    calc
      algebraMap ℚ ℂ (Algebra.norm ℚ (a : K)) =
          ∏ σ : K →ₐ[ℚ] ℂ, σ (a : K) :=
        Algebra.norm_eq_prod_embeddings ℚ ℂ (a : K)
      _ = ∏ φ : K →+* ℂ, φ (a : K) := by
        rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ)
          (fun φ : K →+* ℂ => φ (a : K))
          (fun σ : K →ₐ[ℚ] ℂ => σ (a : K))]
        intro φ
        simp [RingHom.equivRatAlgHom_apply]
  have hprodE : ∏ p : E, p.1 (a : K) = p₁.1 (a : K) * p₂.1 (a : K) := by
    rw [huniv]
    simp [hp₁₂]
  have hcomplexprod :
      ∏ φ : {φ : K →+* ℂ // ¬ComplexEmbedding.IsReal φ}, φ.1 (a : K) = 1 :=
    letI : IsEmpty {φ : K →+* ℂ // ¬ComplexEmbedding.IsReal φ} := hcomplexEmpty
    Fintype.prod_empty _
  have hprodall : ∏ φ : K →+* ℂ, φ (a : K) = p₁.1 (a : K) * p₂.1 (a : K) := by
    calc
      ∏ φ : K →+* ℂ, φ (a : K) =
          (∏ p : E, p.1 (a : K)) *
            ∏ q : {φ : K →+* ℂ // ¬ComplexEmbedding.IsReal φ}, q.1 (a : K) := by
        symm
        exact Fintype.prod_subtype_mul_prod_subtype
          (fun φ : K →+* ℂ => ComplexEmbedding.IsReal φ)
          (fun φ => φ (a : K))
      _ = p₁.1 (a : K) * p₂.1 (a : K) := by rw [hcomplexprod, mul_one, hprodE]
  have hprodC : p₁.1 (a : K) * p₂.1 (a : K) = (-1 : ℂ) := by
    calc
      p₁.1 (a : K) * p₂.1 (a : K) = ∏ φ : K →+* ℂ, φ (a : K) := hprodall.symm
      _ = algebraMap ℚ ℂ (Algebra.norm ℚ (a : K)) := hnormC.symm
      _ = -1 := by rw [haNorm]; norm_num
  have hpVal (p : E) :
      (chapter08RealEmbedding (NumberField.InfinitePlace.mkReal p) (a : K) : ℂ) =
        p.1 (a : K) := by
      rw [chapter08RealEmbedding,
      NumberField.InfinitePlace.embedding_of_isReal_apply,
      NumberField.InfinitePlace.mkReal_coe,
      NumberField.InfinitePlace.embedding_mk_eq_of_isReal p.2]
  have hprodR :
      chapter08RealEmbedding w₁ (a : K) * chapter08RealEmbedding w₂ (a : K) = -1 := by
    apply Complex.ofReal_injective
    simpa [w₁, w₂, hpVal] using hprodC
  have hsignprod :
      SignType.sign (chapter08RealEmbedding w₁ (a : K)) *
        SignType.sign (chapter08RealEmbedding w₂ (a : K)) = (-1 : SignType) := by
    rw [← sign_mul, hprodR]
    norm_num
  let t : Chapter08SignGroup K := chapter08SignHom K u
  have htprod : (t w₁ : SignType) * (t w₂ : SignType) = (-1 : SignType) := by
    change SignType.sign (chapter08RealEmbedding w₁ (a : K)) *
      SignType.sign (chapter08RealEmbedding w₂ (a : K)) = (-1 : SignType)
    exact hsignprod
  have hunit_sign_cases (q : SignTypeˣ) :
      (q : SignType) = -1 ∨ (q : SignType) = 1 := by
    rcases SignType.trichotomy (q : SignType) with hneg | hzero | hpos
    · exact Or.inl hneg
    · exact False.elim (q.ne_zero hzero)
    · exact Or.inr hpos
  have hnegone : chapter08SignHom K (-1 : (Chapter08Integers K)ˣ) =
      (-1 : Chapter08SignGroup K) := by
    ext w
    simp [chapter08SignHom, chapter08SignOfUnit, chapter08RealEmbedding]
  have hminus : chapter08SignHom K ((-1 : (Chapter08Integers K)ˣ) * u) =
      (-1 : Chapter08SignGroup K) * t := by
    rw [map_mul, hnegone]
  have hminus_val (w : Chapter08RealPlaces K) :
      (chapter08SignHom K ((-1 : (Chapter08Integers K)ˣ) * u) w : SignType) =
        -(t w : SignType) := by
    have h := congrArg (fun z : Chapter08SignGroup K => (z w : SignType)) hminus
    simpa using h
  intro s
  have htarget_cases (w : Chapter08RealPlaces K) :
      (s w : SignType) = -1 ∨ (s w : SignType) = 1 := hunit_sign_cases (s w)
  by_cases hsame : (s w₁ : SignType) = (s w₂ : SignType)
  · rcases htarget_cases w₁ with hsneg | hspos
    · refine ⟨(-1 : (Chapter08Integers K)ˣ), ?_⟩
      funext w
      rcases hwcases w with rfl | rfl
      · apply Units.ext
        have h := congrArg (fun z : Chapter08SignGroup K => (z w₁ : SignType)) hnegone
        simpa [hsneg] using h
      · apply Units.ext
        have h := congrArg (fun z : Chapter08SignGroup K => (z w₂ : SignType)) hnegone
        have hsneg₂ : (s w₂ : SignType) = -1 := hsneg ▸ hsame.symm
        simpa [hsneg₂] using h
    · refine ⟨(1 : (Chapter08Integers K)ˣ), ?_⟩
      funext w
      rcases hwcases w with rfl | rfl
      · apply Units.ext
        simp [chapter08SignHom, chapter08SignOfUnit, chapter08RealEmbedding,
          hspos]
      · apply Units.ext
        have hspos₂ : (s w₂ : SignType) = 1 := hspos ▸ hsame.symm
        simp [chapter08SignHom, chapter08SignOfUnit, chapter08RealEmbedding,
          hspos₂]
  · have htargetprod :
        (s w₁ : SignType) * (s w₂ : SignType) = (-1 : SignType) := by
      rcases htarget_cases w₁ with hsneg | hspos <;>
        rcases htarget_cases w₂ with hsneg₂ | hspos₂ <;>
          simp_all
    by_cases hmatch : (s w₁ : SignType) = (t w₁ : SignType)
    · have hmatch₂ : (s w₂ : SignType) = (t w₂ : SignType) := by
        apply mul_left_cancel₀ (t w₁).ne_zero
        calc
          (t w₁ : SignType) * (s w₂ : SignType) =
              (s w₁ : SignType) * (s w₂ : SignType) := by rw [hmatch]
          _ = -1 := htargetprod
          _ = (t w₁ : SignType) * (t w₂ : SignType) := htprod.symm
      refine ⟨u, ?_⟩
      funext w
      rcases hwcases w with rfl | rfl
      · apply Units.ext
        exact hmatch.symm
      · apply Units.ext
        exact hmatch₂.symm
    · have hnegmatch : (s w₁ : SignType) = -(t w₁ : SignType) := by
        rcases htarget_cases w₁ with hsneg | hspos <;>
          rcases hunit_sign_cases (t w₁) with htneg | htpos <;>
            simp_all
      have hnegmatch₂ : (s w₂ : SignType) = -(t w₂ : SignType) := by
        have heq : (-(t w₁ : SignType)) * (s w₂ : SignType) =
            (t w₁ : SignType) * (t w₂ : SignType) := by
          rw [← hnegmatch, htargetprod, htprod]
        have heq' := congrArg Neg.neg heq
        apply mul_left_cancel₀ (t w₁).ne_zero
        simpa [mul_neg] using heq'
      refine ⟨(-1 : (Chapter08Integers K)ˣ) * u, ?_⟩
      funext w
      rcases hwcases w with rfl | rfl
      · apply Units.ext
        exact (hminus_val w₁).trans hnegmatch.symm
      · apply Units.ext
        exact (hminus_val w₂).trans hnegmatch₂.symm

def chapter08FullRealSignImage (K : Type*) [Field K] [NumberField K] : Prop :=
  Function.Surjective (chapter08SignHom K)

theorem chapter08_full_sign_image_implies_ordinary_narrow_agree
    (K : Type*) [Field K] [NumberField K]
    (h : chapter08FullRealSignImage K) :
    Function.Bijective (chapter08NarrowToOrdinary K) :=
  chapter08_narrow_equals_ordinary_of_sign_surjective K h

def chapter08PositiveInfiniteIdeles (K : Type*) [Field K] [NumberField K] :
    Subgroup (Chapter08InfiniteIdeles K) where
  carrier := {x | ∀ w : Chapter08RealPlaces K,
      0 < NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
      (x.1 w.1)}
  one_mem' := by
    intro w
    simp only [Units.val_one]
    change 0 < NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
      (1 : w.1.Completion)
    rw [map_one]
    norm_num
  mul_mem' := by
    intro x y hx hy w
    change 0 < NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
      (x.1 w.1 * y.1 w.1)
    rw [map_mul]
    exact mul_pos (hx w) (hy w)
  inv_mem' := by
    intro x hx w
    have hcoord : ((x⁻¹ : Chapter08InfiniteIdeles K) : Chapter08InfiniteAdeles K) w.1 =
        (x.1 w.1)⁻¹ :=
      eq_inv_of_mul_eq_one_right (congr_fun x.val_inv w.1)
    rw [hcoord, map_inv₀]
    exact inv_pos.mpr (hx w)

def chapter08InfiniteIdeleSignHom (K : Type*) [Field K] [NumberField K] :
    Chapter08InfiniteIdeles K →* Chapter08SignGroup K where
  toFun := fun x w =>
      Units.mk0
      (SignType.sign
        (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (x.1 w.1))) (by
          apply (sign_ne_zero).2
          apply (map_ne_zero
            (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2)).2
          intro hx
          have hmul := congr_fun x.val_inv w.1
          change x.1 w.1 * x.inv w.1 = 1 at hmul
          rw [hx, zero_mul] at hmul
          exact zero_ne_one hmul)
  map_one' := by
    funext w
    apply Units.ext
    simp only [Units.val_one]
    change SignType.sign
      (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
        (1 : w.1.Completion)) = 1
    rw [map_one]
    simp
  map_mul' := by
    intro x y
    funext w
    apply Units.ext
    change SignType.sign
      (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
        (x.1 w.1 * y.1 w.1)) =
      SignType.sign
          (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
            (x.1 w.1)) *
        SignType.sign
          (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
            (y.1 w.1))
    rw [map_mul, sign_mul]

theorem chapter08_infinite_idele_sign_kernel
    (K : Type*) [Field K] [NumberField K] :
    MonoidHom.ker (chapter08InfiniteIdeleSignHom K) =
      chapter08PositiveInfiniteIdeles K := by
  ext x
  constructor
  · intro hx
    change chapter08InfiniteIdeleSignHom K x = 1 at hx
    intro w
    have hsign := congrArg (fun z : SignTypeˣ => (z : SignType))
      (congrFun hx w)
    change SignType.sign
      (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
        (x.1 w.1)) = 1 at hsign
    exact sign_eq_one_iff.mp hsign
  · intro hx
    change chapter08InfiniteIdeleSignHom K x = 1
    funext w
    apply Units.ext
    change SignType.sign
      (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
        (x.1 w.1)) = 1
    exact sign_pos (hx w)

/-! The complex coordinates have no sign quotient here; their arguments remain continuous data. -/

/-! The connected-component quotient at a real place has two elements and no valuation coordinate. -/

def chapter08PositiveRealUnits : Subgroup ℝˣ where
  carrier := {u | 0 < (u : ℝ)}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    simpa using mul_pos hx hy
  inv_mem' := by
    intro x hx
    change 0 < (x : ℝ) at hx
    change 0 < ((x⁻¹ : ℝˣ) : ℝ)
    simpa using inv_pos.mpr hx

def chapter08RealUnitSignHom : ℝˣ →* SignTypeˣ where
  toFun := fun u => Units.mk0 (SignType.sign (u : ℝ)) (by
    exact (sign_ne_zero).2 u.ne_zero)
  map_one' := by
    apply Units.ext
    simp
  map_mul' := by
    intro x y
    apply Units.ext
    simp [sign_mul]

theorem chapter08_real_unit_sign_surjective :
    Function.Surjective chapter08RealUnitSignHom := by
  intro s
  have hs : (s : SignType) = -1 ∨ (s : SignType) = 1 := by
    rcases SignType.trichotomy (s : SignType) with hs | hs | hs
    · exact Or.inl hs
    · exact False.elim (s.ne_zero hs)
    · exact Or.inr hs
  rcases hs with hs | hs
  · refine ⟨(-1 : ℝˣ), ?_⟩
    apply Units.ext
    simp [chapter08RealUnitSignHom, hs]
  · refine ⟨(1 : ℝˣ), ?_⟩
    apply Units.ext
    simp [chapter08RealUnitSignHom, hs]

theorem chapter08_real_unit_sign_kernel :
    MonoidHom.ker chapter08RealUnitSignHom = chapter08PositiveRealUnits := by
  ext x
  constructor
  · intro hx
    change chapter08RealUnitSignHom x = 1 at hx
    have hsign := congrArg (fun u : SignTypeˣ => (u : SignType)) hx
    change SignType.sign (x : ℝ) = 1 at hsign
    change 0 < (x : ℝ)
    exact sign_eq_one_iff.mp hsign
  · intro hx
    change 0 < (x : ℝ) at hx
    change chapter08RealUnitSignHom x = 1
    apply Units.ext
    simp [chapter08RealUnitSignHom, sign_pos hx]

noncomputable def chapter08RealUnitComponentQuotientEquiv :
    (ℝˣ ⧸ chapter08PositiveRealUnits) ≃* SignTypeˣ :=
  QuotientGroup.liftEquiv chapter08PositiveRealUnits
    chapter08_real_unit_sign_surjective (chapter08_real_unit_sign_kernel).symm

theorem chapter08_real_component_quotient_is_sign_group :
    Nonempty ((ℝˣ ⧸ chapter08PositiveRealUnits) ≃* SignTypeˣ) := by
  exact ⟨chapter08RealUnitComponentQuotientEquiv⟩

end

end LastLib.Book04AdelesAndIdeles.Chapter08
