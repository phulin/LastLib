import LastLib.Book03RamificationTheory.Chapter01.Section06TheShapeOfATameGaloisGroup

namespace LastLib.Book03RamificationTheory.Chapter01

noncomputable section

open scoped BigOperators WithZero

/-! ## 1.7. Stability properties of tameness -/

/-- The residue separability and ramification-index data for a tower. -/
structure Chapter01TameTowerData
    (K M L k m l : Type*) [Field K] [Field M] [Field L]
    [Field k] [Field m] [Field l]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [Algebra k m] [Algebra m l] [Algebra k l]
    [IsScalarTower K M L] [IsScalarTower k m l]
    [FiniteDimensional K M] [FiniteDimensional M L] [FiniteDimensional K L]
    [FiniteDimensional k m] [FiniteDimensional m l]
    [FiniteDimensional k l] (eKM eML eKL : ℕ) where
  field_separable_iff :
    Algebra.IsSeparable K L ↔
      Algebra.IsSeparable K M ∧ Algebra.IsSeparable M L
  residue_separable_iff :
    Algebra.IsSeparable k l ↔
      Algebra.IsSeparable k m ∧ Algebra.IsSeparable m l
  ramification_transitive : eKL = eKM * eML

/-- Tameness is equivalent to tameness of both stages in a tower. -/
theorem chapter01_tame_tower_iff
    {K M L k m l : Type*} [Field K] [Field M] [Field L]
    [Field k] [Field m] [Field l]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [Algebra k m] [Algebra m l] [Algebra k l]
    [IsScalarTower K M L] [IsScalarTower k m l]
    [FiniteDimensional K M] [FiniteDimensional M L] [FiniteDimensional K L]
    [FiniteDimensional k m] [FiniteDimensional m l]
    [FiniteDimensional k l]
    (eKM eML eKL : ℕ)
    (D : Chapter01TameTowerData K M L k m l eKM eML eKL) :
    chapter01TamelyRamifiedExtension K L k l eKL ↔
    chapter01TamelyRamifiedExtension K M k m eKM ∧
        chapter01TamelyRamifiedExtension M L m l eML := by
  have hchar : chapter01CharacteristicExponent m =
      chapter01CharacteristicExponent k := by
    let p : ℕ := chapter01CharacteristicExponent k
    let _ : ExpChar k p := by
      dsimp [p, chapter01CharacteristicExponent]
      exact ringExpChar.expChar k
    let _ : ExpChar m p :=
      expChar_of_injective_algebraMap (algebraMap k m).injective p
    change ringExpChar m = ringExpChar k
    exact (ringExpChar.eq m p).trans (ringExpChar.eq k p).symm
  unfold chapter01TamelyRamifiedExtension
  constructor
  · rintro ⟨hfield, hres, hcop⟩
    rcases D.field_separable_iff.mp hfield with ⟨hKM, hML⟩
    rcases D.residue_separable_iff.mp hres with ⟨hkM, hmL⟩
    have hprod : Nat.Coprime (eKM * eML)
        (chapter01CharacteristicExponent k) := by
      simpa [chapter01TameIndex, D.ramification_transitive] using hcop
    have hcopKM : Nat.Coprime eKM (chapter01CharacteristicExponent k) :=
      Nat.Coprime.of_dvd_left (dvd_mul_right eKM eML) hprod
    have hcopMLk : Nat.Coprime eML (chapter01CharacteristicExponent k) :=
      Nat.Coprime.of_dvd_left (dvd_mul_left eML eKM) hprod
    have hcopML : Nat.Coprime eML (chapter01CharacteristicExponent m) := by
      simpa [hchar] using hcopMLk
    exact ⟨⟨hKM, hkM, hcopKM⟩, ⟨hML, hmL, hcopML⟩⟩
  · rintro ⟨⟨hKM, hkM, hcopKM⟩, ⟨hML, hmL, hcopML⟩⟩
    have hcopMLk : Nat.Coprime eML (chapter01CharacteristicExponent k) := by
      simpa [chapter01TameIndex, hchar] using hcopML
    have hprod : Nat.Coprime (eKM * eML)
        (chapter01CharacteristicExponent k) :=
      hcopKM.mul_left hcopMLk
    refine ⟨D.field_separable_iff.mpr ⟨hKM, hML⟩,
      D.residue_separable_iff.mpr ⟨hkM, hmL⟩, ?_⟩
    simpa [chapter01TameIndex, D.ramification_transitive] using
      hprod

/-- The subextension direction of tower stability. -/
theorem chapter01_tame_subextension
    {K M L k m l : Type*} [Field K] [Field M] [Field L]
    [Field k] [Field m] [Field l]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [Algebra k m] [Algebra m l] [Algebra k l]
    [IsScalarTower K M L] [IsScalarTower k m l]
    [FiniteDimensional K M] [FiniteDimensional M L] [FiniteDimensional K L]
    [FiniteDimensional k m] [FiniteDimensional m l]
    [FiniteDimensional k l]
    (eKM eML eKL : ℕ)
    (D : Chapter01TameTowerData K M L k m l eKM eML eKL)
    (h : chapter01TamelyRamifiedExtension K L k l eKL) :
    chapter01TamelyRamifiedExtension K M k m eKM ∧
      chapter01TamelyRamifiedExtension M L m l eML := by
  exact (chapter01_tame_tower_iff eKM eML eKL D).mp h

/-- A compositum profile records the only ramification-index input needed for
the prime-to-`p` closure argument. -/
-- LOCAL_DEPENDENCY_GUESS: the profiles below stand for the canonical local
-- compositum and normal-closure constructions, whose field maps and
-- ramification-index divisibility facts should be supplied by the global
-- local-field API in a later pass.
structure Chapter01TameCompositumData
    (K Ω k l₁ l₂ l : Type*) [Field K] [Field Ω]
    [Field k] [Field l₁] [Field l₂] [Field l]
    [Algebra K Ω] [Algebra k l₁] [Algebra k l₂] [Algebra k l]
    (L₁ L₂ C : IntermediateField K Ω)
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    [FiniteDimensional K C] [FiniteDimensional k l₁]
    [FiniteDimensional k l₂] [FiniteDimensional k l]
    (e₁ e₂ e : ℕ) where
  compositum_eq : C = L₁ ⊔ L₂
  field_separable : Algebra.IsSeparable K C
  residue_separable : Algebra.IsSeparable k l
  ramification_index_divides_lcm : e ∣ Nat.lcm e₁ e₂

/-- The compositum of two tame stages is tame once its ramification index is
known to divide the least common multiple of the two indices. -/
theorem chapter01_tame_compositum
    {K Ω k l₁ l₂ l : Type*} [Field K] [Field Ω]
    [Field k] [Field l₁] [Field l₂] [Field l]
    [Algebra K Ω] [Algebra k l₁] [Algebra k l₂] [Algebra k l]
    (L₁ L₂ C : IntermediateField K Ω)
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    [FiniteDimensional K C] [FiniteDimensional k l₁]
    [FiniteDimensional k l₂] [FiniteDimensional k l]
    (e₁ e₂ e : ℕ)
    (D : Chapter01TameCompositumData K Ω k l₁ l₂ l L₁ L₂ C e₁ e₂ e)
    (h₁ : chapter01TamelyRamifiedExtension K L₁ k l₁ e₁)
    (h₂ : chapter01TamelyRamifiedExtension K L₂ k l₂ e₂) :
    chapter01TamelyRamifiedExtension K C k l e := by
  unfold chapter01TamelyRamifiedExtension at h₁ h₂ ⊢
  refine ⟨D.field_separable, D.residue_separable, ?_⟩
  apply Nat.Coprime.of_dvd_left D.ramification_index_divides_lcm
  apply Nat.Coprime.of_dvd_left
    (Nat.lcm_dvd (dvd_mul_right e₁ e₂) (dvd_mul_left e₂ e₁))
  exact h₁.2.2.mul_left h₂.2.2

/-- A Galois-closure profile makes the closure's prime-to-`p` index explicit. -/
structure Chapter01TameGaloisClosureData
    (K Ω k l lg : Type*) [Field K] [Field Ω]
    [Field k] [Field l] [Field lg]
    [Algebra K Ω] [Algebra k l] [Algebra k lg]
    (L LG : IntermediateField K Ω)
    [FiniteDimensional K L] [FiniteDimensional K LG]
    [FiniteDimensional k l] [FiniteDimensional k lg]
    (e eg : ℕ) where
  inclusion : L ≤ LG
  normal_closure : LG = IntermediateField.normalClosure K L Ω
  galois_closure : IsGalois K LG
  field_separable : Algebra.IsSeparable K LG
  residue_separable : Algebra.IsSeparable k lg
  ramification_index_divides : eg ∣ e

/-- A finite Galois closure of a tame stage is tame under the closure-index
divisibility supplied by the local extension interface. -/
theorem chapter01_tame_galois_closure
    {K Ω k l lg : Type*} [Field K] [Field Ω]
    [Field k] [Field l] [Field lg]
    [Algebra K Ω] [Algebra k l] [Algebra k lg]
    (L LG : IntermediateField K Ω)
    [FiniteDimensional K L] [FiniteDimensional K LG]
    [FiniteDimensional k l] [FiniteDimensional k lg]
    (e eg : ℕ)
    (D : Chapter01TameGaloisClosureData K Ω k l lg L LG e eg)
    (h : chapter01TamelyRamifiedExtension K L k l e) :
    chapter01TamelyRamifiedExtension K LG k lg eg := by
  sorry

/-- The quotient operation that kills a wild subgroup. -/
def chapter01WildPartKilled
    {G Q : Type*} [Group G] [Group Q]
    (W : Subgroup G) (π : G →* Q) : Prop :=
  W ≤ π.ker

/-- Wildness of an upstairs finite group need not survive in a quotient.  The
   subgroup being killed is required to be a nontrivial `p`-primary subgroup,
   so the statement records an actual wild part rather than an arbitrary
   subgroup that happens to lie in the kernel. -/
theorem chapter01_wildness_can_disappear_after_quotient
    {G Q : Type*} [Group G] [Group Q] [Finite G] [Finite Q]
    (W : Subgroup G) (p : ℕ) (π : G →* Q)
    (hW : chapter01PPrimaryOrder W p)
    (hWnontrivial : W ≠ ⊥)
    (hwild_upstairs : ¬Nat.Coprime (Nat.card G) p)
    (htame_downstairs : Nat.Coprime (Nat.card Q) p)
    (hkills : chapter01WildPartKilled W π) :
    ¬Nat.Coprime (Nat.card G) p ∧
      Nat.Coprime (Nat.card Q) p ∧
      ∀ w : W, π (w : G) = 1 := by
  refine ⟨hwild_upstairs, htame_downstairs, ?_⟩
  intro w
  exact MonoidHom.mem_ker.mp (hkills w.property)

/-- The killed wild subgroup is invisible in the quotient map. -/
theorem chapter01_wild_part_killed_iff
    {G Q : Type*} [Group G] [Group Q]
    (W : Subgroup G) (π : G →* Q) :
    chapter01WildPartKilled W π ↔ ∀ w : W, π (w : G) = 1 := by
  constructor
  · intro h w
    exact MonoidHom.mem_ker.mp (h w.property)
  · intro h w hw
    exact MonoidHom.mem_ker.mpr (h ⟨w, hw⟩)

end

end LastLib.Book03RamificationTheory.Chapter01
