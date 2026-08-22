import LastLib.Book03RamificationTheory.Chapter01.Section05TheMaximalTameStage

namespace LastLib.Book03RamificationTheory.Chapter01

noncomputable section

open scoped BigOperators WithZero

/-! ## 1.6. The shape of a tame Galois group -/

/- The finite-field presentation needs the residue reduction and the tame
   character to be attached to the same group.  Keeping these as input data
   avoids treating an arbitrary normal subgroup of an unrelated finite group
   as inertia. -/
structure Chapter01FiniteTameGroupInput
    (G k l : Type*) [Group G] [Finite G] [Field k] [Field l]
    [Algebra k l] (I : Subgroup G) [I.Normal] where
  residue_reduction : G →* Gal(l / k)
  residue_reduction_surjective : Function.Surjective residue_reduction
  kernel_eq_inertia : MonoidHom.ker residue_reduction = I
  tame_character : I →* lˣ
  tame_character_injective : Function.Injective tame_character
  conjugation_compatibility :
    ∀ g : G, ∀ i j : I,
      (j : G) = g * (i : G) * g⁻¹ →
        tame_character j =
          Units.map (residue_reduction g).toRingEquiv.toMonoidHom
            (tame_character i)

/-- A tame finite residue field gives the displayed Frobenius/tame-inertia
 presentation, with the order relation left explicit.  The input package
 identifies the residue quotient and the tame character with the same
 subgroup of the ambient Galois group. -/
theorem chapter01_tame_group_presentation_exists
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Finite (chapter01GaloisGroup K L)]
    [Algebra k l] [FiniteDimensional k l] [Fintype k] [Finite l]
    [Algebra.IsAlgebraic k l]
    (I : Subgroup (chapter01GaloisGroup K L)) [I.Normal]
    (q e f : ℕ) (hq : Fintype.card k = q)
    (hf : Module.finrank k l = f)
    (hI : Nat.card I = e)
    (_hresidue_separable : Algebra.IsSeparable k l)
    (_htame : Nat.Coprime e (chapter01CharacteristicExponent k))
    (hdata : Chapter01FiniteTameGroupInput
      (chapter01GaloisGroup K L) k l I) :
    Nonempty (Chapter01FiniteTameGroupPresentation
      (chapter01GaloisGroup K L) I q e f) := by
  let _ : Fintype l := Fintype.ofFinite l
  let hcyclic : IsCyclic I :=
    isCyclic_of_injective hdata.tame_character hdata.tame_character_injective
  obtain ⟨tau, htau⟩ :=
    (Subgroup.isCyclic_iff_exists_zpowers_eq_top I).mp
      hcyclic
  have htau_mem : tau ∈ I := by
    rw [← htau]
    exact Subgroup.mem_zpowers tau
  have htau_order : orderOf tau = e := by
    rw [← Nat.card_zpowers tau, htau, hI]
  have hqpos : 0 < q := by
    rw [← hq]
    exact Fintype.card_pos
  have hepos : 0 < e := by
    rw [← hI]
    exact Nat.card_pos
  let phi : Gal(l / k) := chapter01ArithmeticFrobenius k l
  obtain ⟨F, hF⟩ := hdata.residue_reduction_surjective phi
  have hphi_order : orderOf phi = f := by
    simpa [phi, chapter01ArithmeticFrobenius] using
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.chapter06_arithmetic_frobenius_order
        k l f hf
  have hphi_pow : phi ^ f = 1 := by
    rw [← hphi_order]
    exact pow_orderOf_eq_one phi
  have hF_pow_mem_kernel : F ^ f ∈ MonoidHom.ker hdata.residue_reduction := by
    rw [MonoidHom.mem_ker]
    rw [map_pow, hF, hphi_pow]
  have hF_pow_mem_I : F ^ f ∈ I := by
    rw [← hdata.kernel_eq_inertia]
    exact hF_pow_mem_kernel
  let hi : I := ⟨tau, htau_mem⟩
  have hconj_mem : F * tau * F⁻¹ ∈ I :=
    (inferInstance : I.Normal).conj_mem tau htau_mem F
  let hj : I := ⟨F * tau * F⁻¹, hconj_mem⟩
  have hchar := hdata.conjugation_compatibility F hi hj (by rfl)
  have hmap :
      Units.map (hdata.residue_reduction F).toRingEquiv.toMonoidHom
          (hdata.tame_character hi) =
        (hdata.tame_character hi) ^ q := by
    rw [hF]
    apply Units.ext
    change phi (hdata.tame_character hi : l) =
      (hdata.tame_character hi : l) ^ q
    simpa [phi, chapter01ArithmeticFrobenius, hq] using
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.chapter06_arithmetic_frobenius_apply
        k l (hdata.tame_character hi : l)
  have hchar_pow : hdata.tame_character hj =
      hdata.tame_character (hi ^ q) := by
    calc
      hdata.tame_character hj =
          Units.map (hdata.residue_reduction F).toRingEquiv.toMonoidHom
            (hdata.tame_character hi) := hchar
      _ = (hdata.tame_character hi) ^ q := hmap
      _ = hdata.tame_character (hi ^ q) :=
        (hdata.tame_character.map_pow hi q).symm
  have hconj : F * tau * F⁻¹ = tau ^ q := by
    have heq : hj = hi ^ q := hdata.tame_character_injective hchar_pow
    simpa [hi, hj] using congrArg Subtype.val heq
  have hF_pow_mem_zpowers : F ^ f ∈ Subgroup.zpowers tau := by
    rw [htau]
    exact hF_pow_mem_I
  have hF_pow_mem_powers : F ^ f ∈ Submonoid.powers tau :=
    (isOfFinOrder_of_finite tau).mem_powers_iff_mem_zpowers.mpr hF_pow_mem_zpowers
  obtain ⟨a, ha⟩ := hF_pow_mem_powers
  let C : Subgroup (chapter01GaloisGroup K L) :=
    Subgroup.closure ({F, tau} : Set (chapter01GaloisGroup K L))
  have hFC : F ∈ C := by
    exact Subgroup.subset_closure (by simp)
  have htauC : tau ∈ C := by
    exact Subgroup.subset_closure (by simp)
  have hIleC : I ≤ C := by
    rw [← htau]
    exact Subgroup.zpowers_le.mpr htauC
  have hFzleC : Subgroup.zpowers F ≤ C :=
    Subgroup.zpowers_le.mpr hFC
  have hphizpowers :
      Subgroup.zpowers phi = (⊤ : Subgroup (Gal(l / k))) := by
    simpa [phi, chapter01ArithmeticFrobenius] using
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.chapter06_arithmetic_frobenius_zpowers_eq_top
        k l
  have hCtop : C = ⊤ := by
    apply top_unique
    intro g hg
    have hquot : hdata.residue_reduction g ∈ Subgroup.zpowers phi := by
      rw [hphizpowers]
      exact Subgroup.mem_top _
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hquot
    have hFn : F ^ n ∈ C :=
      hFzleC (Subgroup.zpow_mem_zpowers F n)
    have hker : F ^ n * g⁻¹ ∈ MonoidHom.ker hdata.residue_reduction := by
      rw [MonoidHom.mem_ker]
      rw [map_mul, map_zpow, hF, hn]
      simp
    have hIelem : F ^ n * g⁻¹ ∈ I := by
      rw [← hdata.kernel_eq_inertia]
      exact hker
    have hx := C.mul_mem (C.inv_mem (hIleC hIelem)) hFn
    simpa [mul_assoc] using hx
  refine ⟨{
    frobenius := F
    tameGenerator := tau
    tameGenerator_mem := htau_mem
    tameGenerator_order_positive := hepos
    tameGenerator_order := htau_order
    residue_degree_positive := by
      rw [← hphi_order]
      exact orderOf_pos _
    residue_card_positive := hqpos
    inertia_generated := htau
    group_generated := hCtop
    conjugation := hconj
    frobenius_power := ⟨a, ha.symm⟩
  }⟩

/-- In the arithmetic convention, conjugation acts on a tame generator by the
`q`th power. -/
theorem chapter01_arithmetic_frobenius_conjugation
    {G : Type*} [Group G] [Finite G]
    {I : Subgroup G} [I.Normal] (q e f : ℕ)
    (D : Chapter01FiniteTameGroupPresentation G I q e f) :
    D.frobenius * D.tameGenerator * D.frobenius⁻¹ =
      D.tameGenerator ^ q := D.conjugation

/- The order relation in the presentation gives the displayed relation
`τ^e = 1` from the source. -/
theorem chapter01_tame_generator_pow_eq_one
    {G : Type*} [Group G] [Finite G]
    {I : Subgroup G} [I.Normal] (q e f : ℕ)
    (D : Chapter01FiniteTameGroupPresentation G I q e f) :
    D.tameGenerator ^ e = 1 := by
  calc
    D.tameGenerator ^ e = D.tameGenerator ^ orderOf D.tameGenerator := by
      exact congrArg (fun n : ℕ => D.tameGenerator ^ n) D.tameGenerator_order.symm
    _ = 1 := pow_orderOf_eq_one D.tameGenerator

/- The exponent in `F^f = τ^a` is unique modulo the tame order. -/
theorem chapter01_frobenius_power_exponent_unique_mod
    {G : Type*} [Group G] [Finite G]
    {I : Subgroup G} [I.Normal] (q e f : ℕ)
    (D : Chapter01FiniteTameGroupPresentation G I q e f)
    {a b : ℕ}
    (ha : D.frobenius ^ f = D.tameGenerator ^ a)
    (hb : D.frobenius ^ f = D.tameGenerator ^ b) :
    Nat.ModEq e a b := by
  have hpow : D.tameGenerator ^ a = D.tameGenerator ^ b := ha.symm.trans hb
  rw [Nat.modEq_iff_dvd]
  by_cases hab : a ≤ b
  · have hpowdiff : D.tameGenerator ^ (b - a) = 1 := by
      calc
        D.tameGenerator ^ (b - a) =
            (D.tameGenerator ^ a)⁻¹ * D.tameGenerator ^ b := by
              rw [← Nat.add_sub_of_le hab, pow_add]
              simp
        _ = 1 := by rw [← hpow]; simp
    have hd : orderOf D.tameGenerator ∣ b - a :=
      orderOf_dvd_of_pow_eq_one hpowdiff
    have hd' : e ∣ b - a := by simpa [D.tameGenerator_order] using hd
    exact_mod_cast hd'
  · have hba : b ≤ a := Nat.le_of_not_ge hab
    have hpowdiff : D.tameGenerator ^ (a - b) = 1 := by
      calc
        D.tameGenerator ^ (a - b) =
            (D.tameGenerator ^ b)⁻¹ * D.tameGenerator ^ a := by
              rw [← Nat.add_sub_of_le hba, pow_add]
              simp
        _ = 1 := by rw [hpow]; simp
    have hd : orderOf D.tameGenerator ∣ a - b :=
      orderOf_dvd_of_pow_eq_one hpowdiff
    have hd' : e ∣ a - b := by simpa [D.tameGenerator_order] using hd
    have hcast : (e : ℤ) ∣ (a : ℤ) - (b : ℤ) := by
      rw [← Int.ofNat_sub hba]
      exact_mod_cast hd'
    rw [← neg_sub]
    exact dvd_neg.mpr hcast

/- Compatibility of Frobenius conjugation with `F^f ∈ I`. -/
theorem chapter01_frobenius_power_compatibility
    {G : Type*} [Group G] [Finite G]
    {I : Subgroup G} [I.Normal] (q e f : ℕ)
    (D : Chapter01FiniteTameGroupPresentation G I q e f) :
    Nat.ModEq e (q ^ f) 1 := by
  let conjHom : ∀ g : G, G →* G := fun g =>
    { toFun := fun x => g * x * g⁻¹
      map_one' := by simp
      map_mul' := by
        intro x y
        simp [mul_assoc] }
  have hconj_pow_aux (n : ℕ) :
      (D.frobenius ^ n * D.tameGenerator * (D.frobenius ^ n)⁻¹) ^ q =
        D.frobenius ^ n * (D.tameGenerator ^ q) *
          (D.frobenius ^ n)⁻¹ := by
    change ((conjHom (D.frobenius ^ n)) D.tameGenerator) ^ q =
      (conjHom (D.frobenius ^ n)) (D.tameGenerator ^ q)
    exact (map_pow (conjHom (D.frobenius ^ n)) D.tameGenerator q).symm
  have hconj_pow : ∀ n : ℕ,
      D.frobenius ^ n * D.tameGenerator * (D.frobenius ^ n)⁻¹ =
        D.tameGenerator ^ (q ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          D.frobenius ^ (n + 1) * D.tameGenerator *
              (D.frobenius ^ (n + 1))⁻¹ =
              D.frobenius ^ n *
                (D.frobenius * D.tameGenerator * D.frobenius⁻¹) *
                (D.frobenius ^ n)⁻¹ := by
                  simp [pow_succ, mul_assoc]
          _ = D.frobenius ^ n * (D.tameGenerator ^ q) *
                (D.frobenius ^ n)⁻¹ := by rw [D.conjugation]
          _ = (D.frobenius ^ n * D.tameGenerator *
                (D.frobenius ^ n)⁻¹) ^ q := by
                  exact (hconj_pow_aux n).symm
          _ = D.tameGenerator ^ (q ^ n * q) := by
                rw [ih, pow_mul]
          _ = D.tameGenerator ^ (q ^ (n + 1)) := by
                rw [pow_succ]
  obtain ⟨a, ha⟩ := D.frobenius_power
  have hleft : D.frobenius ^ f * D.tameGenerator *
      (D.frobenius ^ f)⁻¹ = D.tameGenerator := by
    rw [ha]
    have hcomm : Commute (D.tameGenerator ^ a) D.tameGenerator :=
      (Commute.refl D.tameGenerator).pow_left a
    calc
      D.tameGenerator ^ a * D.tameGenerator *
          (D.tameGenerator ^ a)⁻¹ =
          D.tameGenerator * D.tameGenerator ^ a *
            (D.tameGenerator ^ a)⁻¹ := by rw [hcomm.eq]
      _ = D.tameGenerator := by simp
  have hpow : D.tameGenerator ^ (q ^ f) = D.tameGenerator := by
    calc
      D.tameGenerator ^ (q ^ f) =
          D.frobenius ^ f * D.tameGenerator * (D.frobenius ^ f)⁻¹ :=
        (hconj_pow f).symm
      _ = D.tameGenerator := hleft
  have hqf : 1 ≤ q ^ f := by
    exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero f (Nat.ne_of_gt D.residue_card_positive))
  have hpowdiff : D.tameGenerator ^ (q ^ f - 1) = 1 := by
    calc
      D.tameGenerator ^ (q ^ f - 1) =
          (D.tameGenerator ^ 1)⁻¹ * D.tameGenerator ^ (q ^ f) := by
            rw [← Nat.add_sub_of_le hqf, pow_add]
            simp
      _ = 1 := by rw [hpow]; simp
  have hd : orderOf D.tameGenerator ∣ q ^ f - 1 :=
    orderOf_dvd_of_pow_eq_one hpowdiff
  have hd' : e ∣ q ^ f - 1 := by simpa [D.tameGenerator_order] using hd
  rw [Nat.modEq_iff_dvd]
  have hcast : (e : ℤ) ∣ (q ^ f : ℤ) - 1 := by
    exact_mod_cast hd'
  have hneg : (1 : ℤ) - (q ^ f : ℤ) = -((q ^ f : ℤ) - 1) := by ring
  change (e : ℤ) ∣ (1 : ℤ) - (q ^ f : ℤ)
  rw [hneg]
  exact dvd_neg.mpr hcast

/-- Geometric Frobenius reverses the conjugation convention. -/
theorem chapter01_geometric_frobenius_conjugation
    {G : Type*} [Group G] [Finite G]
    {I : Subgroup G} [I.Normal] (q e f : ℕ)
    (D : Chapter01FiniteTameGroupPresentation G I q e f) :
    ∃ r : ℕ,
      D.frobenius⁻¹ * D.tameGenerator * D.frobenius =
        D.tameGenerator ^ r := by
  have hI : D.frobenius⁻¹ * D.tameGenerator * D.frobenius ∈ I := by
    simpa using
      (inferInstance : I.Normal).conj_mem D.tameGenerator D.tameGenerator_mem
        D.frobenius⁻¹
  have hz : D.frobenius⁻¹ * D.tameGenerator * D.frobenius ∈
      Subgroup.zpowers D.tameGenerator := by
    rw [D.inertia_generated]
    exact hI
  have hp : D.frobenius⁻¹ * D.tameGenerator * D.frobenius ∈
      Submonoid.powers D.tameGenerator :=
    (isOfFinOrder_of_finite D.tameGenerator).mem_powers_iff_mem_zpowers.mpr hz
  obtain ⟨r, hr⟩ := hp
  exact ⟨r, hr.symm⟩

/-- The tame filtration has only the ambient, tame-inertia, and trivial levels. -/
def chapter01TameRamificationGroup
    {G : Type*} [Group G] (I : Subgroup G) (i : ℤ) : Subgroup G :=
  if i < 0 then ⊤ else if i = 0 then I else ⊥

@[simp] theorem chapter01_tame_ramification_group_neg_one
    {G : Type*} [Group G] (I : Subgroup G) :
    chapter01TameRamificationGroup I (-1) = ⊤ := by
  simp [chapter01TameRamificationGroup]

@[simp] theorem chapter01_tame_ramification_group_zero
    {G : Type*} [Group G] (I : Subgroup G) :
    chapter01TameRamificationGroup I 0 = I := by
  simp [chapter01TameRamificationGroup]

@[simp] theorem chapter01_tame_ramification_group_one
    {G : Type*} [Group G] (I : Subgroup G) :
    chapter01TameRamificationGroup I 1 = ⊥ := by
  simp [chapter01TameRamificationGroup]

/-- Data expressing that conjugation carries the tame character through the
natural residue action. -/
-- LOCAL_DEPENDENCY_GUESS: a valuation-level naturality theorem should
-- construct this package from the inertia character and residue action; the
-- compatibility is kept as data until that earlier interface is available.
structure Chapter01TameCharacterConjugationData
    {G I l : Type*} [Group G] [Group I] [Field l]
    (I' : Subgroup G) [I'.Normal] where
  tameCharacter : I →* lˣ
  inclusion : I →* G
  residueAction : G →* RingAut l
  inclusion_injective : Function.Injective inclusion
  inclusion_range : inclusion.range = I'
  stable : ∀ g : G, ∀ i : I,
    g * inclusion i * g⁻¹ ∈ I'
  conjugateCharacter : I' →* lˣ
  compatibility : ∀ g : G, ∀ i : I,
    conjugateCharacter ⟨g * inclusion i * g⁻¹, stable g i⟩ =
      Units.map (residueAction g).toRingHom.toMonoidHom (tameCharacter i)

/-- The conjugation-compatibility eliminator. -/
theorem chapter01_tame_character_conjugation_compatibility
    {G I l : Type*} [Group G] [Group I] [Field l]
    (I' : Subgroup G) [I'.Normal]
    (D : Chapter01TameCharacterConjugationData (G := G) (I := I) (l := l) I') :
    ∀ g : G, ∀ i : I,
      D.conjugateCharacter ⟨g * D.inclusion i * g⁻¹, D.stable g i⟩ =
        Units.map (D.residueAction g).toRingHom.toMonoidHom (D.tameCharacter i) :=
  D.compatibility

end

end LastLib.Book03RamificationTheory.Chapter01
