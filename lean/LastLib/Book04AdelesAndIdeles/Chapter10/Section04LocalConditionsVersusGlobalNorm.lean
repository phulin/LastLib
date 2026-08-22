import LastLib.Book04AdelesAndIdeles.Chapter10.Section03CompatibilityWithPrincipalIdeles

namespace LastLib.Book04AdelesAndIdeles.Chapter10

noncomputable section

open scoped BigOperators
open Chapter10GlobalNormData

/-! ## 10.4. Local conditions versus a global norm -/

namespace Chapter10GlobalNormData

variable {ιK ιL : Type*} {Kloc : ιK → Type*} {Lloc : ιL → Type*}
  [∀ v, CommGroup (Kloc v)] [∀ w, CommGroup (Lloc w)]

/-- The local norm map at a base place. -/
def localNormAtPlace
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc) (v : ιK) :
    (∀ w : {w : ιL // d.below w = v}, Lloc (w : ιL)) →* Kloc v where
  toFun y := by
    exact ∏ w : {w : ιL // d.below w = v},
      d.chapter10LocalNormAt v w (y w)
  map_one' := by
    apply Finset.prod_eq_one
    intro w hw
    rcases w with ⟨w, rfl⟩
    simp [chapter10LocalNormAt]
  map_mul' := by
    intro x y
    change (∏ w : {w : ιL // d.below w = v},
      d.chapter10LocalNormAt v w ((x * y) w)) =
      (∏ w : {w : ιL // d.below w = v},
        d.chapter10LocalNormAt v w (x w)) *
        ∏ w : {w : ιL // d.below w = v},
          d.chapter10LocalNormAt v w (y w)
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro w hw
    rcases w with ⟨w, rfl⟩
    simp [chapter10LocalNormAt]

@[simp]
theorem localNormAtPlace_apply
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc) (v : ιK)
    (y : ∀ w : {w : ιL // d.below w = v}, Lloc (w : ιL)) :
    d.localNormAtPlace v y =
      ∏ w : {w : ιL // d.below w = v},
        d.chapter10LocalNormAt v w (y w) := by
  rfl

/-- The local norm image at a place. -/
def localNormImageAtPlace
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc) (v : ιK) : Set (Kloc v) :=
  Set.range (d.localNormAtPlace v)

theorem mem_localNormImageAtPlace_iff
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc) (v : ιK) (x : Kloc v) :
    x ∈ d.localNormImageAtPlace v ↔
      ∃ y : ∀ w : {w : ιL // d.below w = v}, Lloc (w : ιL),
        d.localNormAtPlace v y = x := Iff.rfl

end Chapter10GlobalNormData

/-- Componentwise local normicity for an element of the base restricted
product. -/
def chapter10ComponentwiseLocalNormicity
    {ιK ιL : Type*} {Kloc : ιK → Type*} {Lloc : ιL → Type*}
    [∀ v, CommGroup (Kloc v)] [∀ w, CommGroup (Lloc w)]
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc)
    (x : kIdeles d) : Prop :=
  ∀ v, x v ∈ d.localNormImageAtPlace v

theorem chapter10_mem_componentwise_local_normicity_iff
    {ιK ιL : Type*} {Kloc : ιK → Type*} {Lloc : ιL → Type*}
    [∀ v, CommGroup (Kloc v)] [∀ w, CommGroup (Lloc w)]
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc) (x : kIdeles d) :
    chapter10ComponentwiseLocalNormicity d x ↔
      ∀ v, x v ∈ d.localNormImageAtPlace v := Iff.rfl

theorem chapter10_adelic_norm_image_imp_componentwise_local_norm
    {ιK ιL : Type*} {Kloc : ιK → Type*} {Lloc : ιL → Type*}
    [∀ v, CommGroup (Kloc v)] [∀ w, CommGroup (Lloc w)]
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc)
    (x : kIdeles d) (y : lIdeles d) (hy : d.adelicNormHom y = x) :
    chapter10ComponentwiseLocalNormicity d x := by
  intro v
  rw [← hy]
  exact ⟨fun w => y (w : ιL), rfl⟩

/-- The finite-exception hypothesis needed for assembling local preimages.
At almost every place it asks for a unit preimage in one factor, exactly as
in the proof of the source statement. -/
def chapter10UnitPreimageOutsideFiniteSet
    {ιK ιL : Type*} {Kloc : ιK → Type*} {Lloc : ιL → Type*}
    [∀ v, CommGroup (Kloc v)] [∀ w, CommGroup (Lloc w)]
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc) : Prop :=
  ∀ᶠ v in Filter.cofinite, ∀ u : Kloc v, u ∈ d.unitK v →
    ∃ w : {w : ιL // d.below w = v}, ∃ y : Lloc (w : ιL),
      y ∈ d.unitL (w : ιL) ∧ d.chapter10LocalNormAt v w y = u

theorem chapter10_adelic_norm_image_componentwise_iff
    {ιK ιL : Type*} {Kloc : ιK → Type*} {Lloc : ιL → Type*}
    [∀ v, CommGroup (Kloc v)] [∀ w, CommGroup (Lloc w)]
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc)
    (hunit : chapter10UnitPreimageOutsideFiniteSet d) (x : kIdeles d) :
    x ∈ Set.range d.adelicNormHom ↔
      chapter10ComponentwiseLocalNormicity d x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact chapter10_adelic_norm_image_imp_componentwise_local_norm d
      (d.adelicNormHom y) y rfl
  · intro hx
    classical
    have hlocalPreimage : ∀ v, ∃ z :
        ∀ w : {w : ιL // d.below w = v}, Lloc (w : ιL),
        d.localNormAtPlace v z = x v := by
      intro v
      exact (mem_localNormImageAtPlace_iff d v (x v)).mp (hx v)
    let z : ∀ v, ∀ w : {w : ιL // d.below w = v}, Lloc (w : ιL) :=
      fun v => Classical.choose (hlocalPreimage v)
    have hz (v) : d.localNormAtPlace v (z v) = x v := by
      exact Classical.choose_spec (hlocalPreimage v)
    let good (v : ιK) : Prop :=
      (∀ u : Kloc v, u ∈ d.unitK v →
        ∃ w : {w : ιL // d.below w = v}, ∃ y : Lloc (w : ιL),
          y ∈ d.unitL (w : ιL) ∧ d.chapter10LocalNormAt v w y = u) ∧
        x v ∈ d.unitK v
    have hgood : ∀ᶠ v in Filter.cofinite, good v := by
      filter_upwards [hunit, x.2] with v hv hunitv
      exact ⟨hv, hunitv⟩
    have hfiber (v : ιK) :
        (d.below ⁻¹' ({v} : Set ιK)).Finite := by
      rw [← Set.finite_coe_iff]
      exact @Finite.of_injective
        (d.below ⁻¹' ({v} : Set ιK))
        {w : ιL // d.below w = v}
        (d.finiteOver v)
        (fun w : d.below ⁻¹' ({v} : Set ιK) =>
          (⟨w.1, by
            have hw : d.below w.1 ∈ ({v} : Set ιK) := w.2
            exact Set.mem_singleton_iff.mp hw⟩ :
            {w : ιL // d.below w = v}))
        (by
          intro w₁ w₂ h
          exact Subtype.ext (congrArg Subtype.val h))
    have hbad : Set.Finite {v : ιK | ¬ good v} :=
      Filter.eventually_cofinite.mp hgood
    have hbadL :
        (d.below ⁻¹' {v : ιK | ¬ good v}).Finite :=
      hbad.preimage' (fun v _hmem => hfiber v)
    have hgoodL : ∀ᶠ w in Filter.cofinite, good (d.below w) := by
      filter_upwards [hbadL.compl_mem_cofinite] with w hw
      by_contra hnot
      exact hw hnot
    let q (v : ιK) (hv : good v) :
        {w : ιL // d.below w = v} :=
      Classical.choose (hv.1 (x v) hv.2)
    let yq (v : ιK) (hv : good v) : Lloc (q v hv : ιL) :=
      Classical.choose (Classical.choose_spec (hv.1 (x v) hv.2))
    let zGood (v : ιK) (hv : good v) :
        ∀ w : {w : ιL // d.below w = v}, Lloc (w : ιL) :=
      fun w => if h : w = q v hv then
        cast (congrArg (fun w : {w : ιL // d.below w = v} =>
          Lloc (w : ιL)) h.symm) (yq v hv)
      else 1
    let z' (v : ιK) :
        ∀ w : {w : ιL // d.below w = v}, Lloc (w : ιL) :=
      if hv : good v then zGood v hv else z v
    have hz_unit (v : ιK) (hv : good v)
        (w : {w : ιL // d.below w = v}) :
        z' v w ∈ d.unitL (w : ιL) := by
      simp only [z', dif_pos hv]
      by_cases h : w = q v hv
      · simp only [zGood, dif_pos h]
        cases h
        exact (Classical.choose_spec
          (Classical.choose_spec (hv.1 (x v) hv.2))).1
      · simp only [zGood, dif_neg h]
        exact (d.unitL (w : ιL)).one_mem
    have hz_norm (v : ιK) : d.localNormAtPlace v (z' v) = x v := by
      by_cases hv : good v
      · simp only [z', dif_pos hv, localNormAtPlace_apply]
        rw [Finset.prod_eq_single (q v hv)]
        · simp only [zGood, dif_pos rfl]
          exact (Classical.choose_spec
            (Classical.choose_spec (hv.1 (x v) hv.2))).2
        · intro w hw hne
          simp only [zGood, dif_neg hne]
          change cast (congrArg Kloc w.property)
              (d.localNorm (w : ιL) (1 : Lloc (w : ιL))) = 1
          rw [map_one]
          cases w with
          | mk w hbelow =>
            cases hbelow
            rfl
        · intro hqmem
          exact (hqmem (Finset.mem_univ (q v hv))).elim
      · simp only [z', dif_neg hv]
        exact hz v
    let y : lIdeles d :=
      ⟨fun w => z' (d.below w) ⟨w, rfl⟩, by
        filter_upwards [hgoodL] with w hw
        exact hz_unit (d.below w) hw ⟨w, rfl⟩⟩
    exact ⟨y, by
      ext v
      rw [← hz_norm v]
      apply Finset.prod_congr rfl
      intro w hw
      rcases w with ⟨w, hwv⟩
      cases hwv
      rfl⟩

/-- The intersection `G ∩ N(I)` expressed through the principal embedding. -/
def chapter10AdelicNormIntersectionSet
    {G I J : Type*} [Group G] [CommGroup I] [CommGroup J]
    (principal : G →* I) (N : J →* I) : Set G :=
  {b | principal b ∈ Set.range N}

theorem chapter10_mem_adelic_norm_intersection_iff
    {G I J : Type*} [Group G] [CommGroup I] [CommGroup J]
    (principal : G →* I) (N : J →* I) (b : G) :
    b ∈ chapter10AdelicNormIntersectionSet principal N ↔
      ∃ y : J, N y = principal b := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, hy⟩

theorem chapter10_global_norm_implies_local_norm
    {G_K G_L : Type*} [Group G_K] [Group G_L]
    {ιK ιL : Type*} {Kloc : ιK → Type*} {Lloc : ιL → Type*}
    [∀ v, CommGroup (Kloc v)] [∀ w, CommGroup (Lloc w)]
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc)
    (pK : G_K →* kIdeles d) (pL : G_L →* lIdeles d)
    (globalNorm : G_L →* G_K)
    (hcompat : chapter10PrincipalNormCompatibility pK pL globalNorm
      d.adelicNormHom)
    (b : G_K) (hb : ∃ a : G_L, globalNorm a = b) :
    chapter10ComponentwiseLocalNormicity d (pK b) := by
  rcases hb with ⟨a, rfl⟩
  exact chapter10_adelic_norm_image_imp_componentwise_local_norm d
    (pK (globalNorm a)) (pL a) (DFunLike.congr_fun hcompat a)

theorem chapter10_global_norm_intersection_is_everywhere_local_norm
    {G_K G_L : Type*} [Group G_K] [Group G_L]
    {ιK ιL : Type*} {Kloc : ιK → Type*} {Lloc : ιL → Type*}
    [∀ v, CommGroup (Kloc v)] [∀ w, CommGroup (Lloc w)]
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc)
    (pK : G_K →* kIdeles d)
    (hunit : chapter10UnitPreimageOutsideFiniteSet d) :
    chapter10AdelicNormIntersectionSet pK d.adelicNormHom =
      {b | chapter10ComponentwiseLocalNormicity d (pK b)} := by
  ext b
  rw [chapter10_mem_adelic_norm_intersection_iff]
  constructor
  · rintro ⟨y, hy⟩
    exact chapter10_adelic_norm_image_imp_componentwise_local_norm d
      (pK b) y hy
  · intro hb
    have : pK b ∈ Set.range d.adelicNormHom := by
      exact (chapter10_adelic_norm_image_componentwise_iff d hunit (pK b)).2 hb
    exact this

/-! The local--global obstruction is a quotient, not an automatic theorem. -/

def chapter10GlobalFieldNormSubgroup
    {G_K G_L : Type*} [Group G_K] [Group G_L]
    (globalNorm : G_L →* G_K) : Subgroup G_K :=
  Subgroup.map globalNorm ⊤

def chapter10AdelicNormImageSubgroup
    {I J : Type*} [CommGroup I] [CommGroup J]
    (N : J →* I) : Subgroup I :=
  Subgroup.map N ⊤

def chapter10AdelicNormIntersectionSubgroup
    {G I J : Type*} [Group G] [CommGroup I] [CommGroup J]
    (principal : G →* I) (N : J →* I) : Subgroup G :=
  (chapter10AdelicNormImageSubgroup N).comap principal

theorem chapter10_global_norm_subgroup_le_intersection
    {G_K G_L : Type*} [Group G_K] [Group G_L]
    {I_K I_L : Type*} [CommGroup I_K] [CommGroup I_L]
    (pK : G_K →* I_K) (pL : G_L →* I_L)
    (globalNorm : G_L →* G_K) (ideleNorm : I_L →* I_K)
    (hcompat : chapter10PrincipalNormCompatibility pK pL globalNorm ideleNorm) :
    chapter10GlobalFieldNormSubgroup globalNorm ≤
      chapter10AdelicNormIntersectionSubgroup pK ideleNorm := by
  intro b hb
  change b ∈ Subgroup.map globalNorm ⊤ at hb
  change pK b ∈ Subgroup.map ideleNorm ⊤
  rcases Subgroup.mem_map.mp hb with ⟨a, ha, rfl⟩
  exact Subgroup.mem_map.mpr ⟨pL a, by simp, by
    simpa [MonoidHom.comp_apply] using DFunLike.congr_fun hcompat a⟩

/-- The obstruction quotient
`(G_K ∩ N(I_L))/N(G_L)`. -/
def chapter10LocalGlobalNormObstruction
    {G_K G_L : Type*} [CommGroup G_K] [CommGroup G_L]
    {I_K I_L : Type*} [CommGroup I_K] [CommGroup I_L]
    (pK : G_K →* I_K)
    (globalNorm : G_L →* G_K) (ideleNorm : I_L →* I_K)
    (_hle : chapter10GlobalFieldNormSubgroup globalNorm ≤
      chapter10AdelicNormIntersectionSubgroup pK ideleNorm) : Type _ :=
  chapter10AdelicNormIntersectionSubgroup pK ideleNorm ⧸
    (chapter10GlobalFieldNormSubgroup globalNorm).subgroupOf
      (chapter10AdelicNormIntersectionSubgroup pK ideleNorm)

/- The source explicitly warns that no vanishing of this quotient follows from
finite/separable/Galois hypotheses alone; the warning is preserved in the API
by defining the obstruction without postulating it to be trivial. -/

/-- The image in the idele class group permits an arbitrary principal factor. -/
def chapter10ClassNormImage
    {G_K G_L : Type*} [Group G_K] [Group G_L]
    {I_K I_L : Type*} [CommGroup I_K] [CommGroup I_L]
    (pK : G_K →* I_K) (pL : G_L →* I_L)
    (globalNorm : G_L →* G_K) (ideleNorm : I_L →* I_K)
    (hcompat : chapter10PrincipalNormCompatibility pK pL globalNorm ideleNorm) :
    Set (chapter10IdeleClassGroup pK) :=
  Set.range (chapter10IdeleClassNorm pK pL globalNorm ideleNorm hcompat)

def chapter10PrincipalTimesAdelicNormSet
    {G I J : Type*} [Group G] [CommGroup I] [CommGroup J]
    (principal : G →* I) (N : J →* I) : Set I :=
  {x | ∃ g : G, ∃ y : J, principal g * N y = x}

theorem chapter10_class_norm_image_is_principal_times_adelic_norm
    {G_K G_L : Type*} [Group G_K] [Group G_L]
    {I_K I_L : Type*} [CommGroup I_K] [CommGroup I_L]
    (pK : G_K →* I_K) (pL : G_L →* I_L)
    (globalNorm : G_L →* G_K) (ideleNorm : I_L →* I_K)
    (hcompat : chapter10PrincipalNormCompatibility pK pL globalNorm ideleNorm) :
    chapter10ClassNormImage pK pL globalNorm ideleNorm hcompat =
      QuotientGroup.mk' (chapter10PrincipalSubgroup pK) ''
        chapter10PrincipalTimesAdelicNormSet pK ideleNorm := by
  sorry

end
end LastLib.Book04AdelesAndIdeles.Chapter10
