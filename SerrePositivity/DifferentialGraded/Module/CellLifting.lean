module
public import SerrePositivity.DifferentialGraded.Module.Cells
public import SerrePositivity.DifferentialGraded.Complexes.CellCriterion
public import Mathlib.CategoryTheory.LiftingProperties.Basic
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-! # 自由diskによる次数ごとの全射性の持ち上げ判定

dg 加群固有の生成元表現を用いる。モデル構造や小対象一般論は定義しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 指定した対象・次数の評価で全射となる加群射。 -/
def moduleSurjectiveAt (x : D) (n : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) : Prop :=
  Function.Surjective (((moduleEvaluation A D x).map f).f n)

/-- 対象ごと・次数ごとに全射となる加群射のクラス。 -/
def moduleDegreewiseSurjective : MorphismProperty (ModuleCategory A D) :=
  fun _ _ f => ∀ (x : D) (n : ℤ), moduleSurjectiveAt A D x n f

lemma moduleSurjectiveAt_iff_epi (x : D) (n : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleSurjectiveAt A D x n f ↔ Epi (((moduleEvaluation A D x).map f).f n) :=
  (ModuleCat.epi_iff_surjective _).symm

/-- 指定の自由diskの零包含に対する右liftは、指定次数の全射性と同値。 -/
lemma freeDisk_lifting_iff_surjective (x : D) (n : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    HasLiftingProperty (moduleZeroTo A D (freeDisk A D x n)) f ↔
      moduleSurjectiveAt A D x n f := by
  constructor
  · intro h y
    let g := (freeDiskHomEquiv A D x n N).symm y
    let sq : CommSq (moduleZeroTo A D M) (moduleZeroTo A D (freeDisk A D x n)) f g :=
      ⟨(moduleZero_isZero A D).eq_of_src _ _⟩
    obtain ⟨l⟩ := (h.sq_hasLift sq).exists_lift
    refine ⟨freeDiskHomEquiv A D x n M l.l, ?_⟩
    rw [← freeDiskHomEquiv_naturality, l.fac_right]
    exact (freeDiskHomEquiv A D x n N).apply_symm_apply y
  · intro h
    constructor
    intro a b sq
    obtain ⟨z, hz⟩ := h (freeDiskHomEquiv A D x n N b)
    apply CommSq.HasLift.mk'
    refine { l := (freeDiskHomEquiv A D x n M).symm z
             fac_left := (moduleZero_isZero A D).eq_of_src _ _
             fac_right := ?_ }
    apply (freeDiskHomEquiv A D x n N).injective
    rw [freeDiskHomEquiv_naturality, Equiv.apply_symm_apply]
    exact hz

/-- 自由diskへの零包含の具体的な生成射族J。 -/
def freeDiskInclusions : MorphismProperty (ModuleCategory A D) :=
  MorphismProperty.ofHoms (fun i : D × ℤ => moduleZeroTo A D (freeDisk A D i.1 i.2))

lemma freeDiskInclusions_rlp_iff {M N : ModuleCategory A D} (f : M ⟶ N) :
    (freeDiskInclusions A D).rlp f ↔ ∀ (x : D) (n : ℤ),
      HasLiftingProperty (moduleZeroTo A D (freeDisk A D x n)) f := by
  constructor
  · intro h x n
    exact h _ (MorphismProperty.ofHoms.mk (x, n))
  · intro h X Y i hi
    cases hi with
    | mk j => exact h j.1 j.2

/-- Jに対する右持ち上げクラスはちょうどobjectwise degreewise surjective。 -/
lemma freeDiskInclusions_rlp_eq :
    (freeDiskInclusions A D).rlp = moduleDegreewiseSurjective A D := by
  ext M N f
  rw [freeDiskInclusions_rlp_iff]
  change (∀ (x : D) (n : ℤ), HasLiftingProperty (moduleZeroTo A D (freeDisk A D x n)) f) ↔
    ∀ (x : D) (n : ℤ), moduleSurjectiveAt A D x n f
  exact forall_congr' (fun x => forall_congr' (fun n => freeDisk_lifting_iff_surjective A D x n f))

lemma moduleDegreewiseSurjective_iff_epi {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleDegreewiseSurjective A D f ↔ ∀ (x : D) (n : ℤ),
      Epi (((moduleEvaluation A D x).map f).f n) :=
  forall_congr' (fun x => forall_congr' (fun n => moduleSurjectiveAt_iff_epi A D x n f))

instance moduleDegreewiseSurjectiveStableUnderRetracts :
    (moduleDegreewiseSurjective A D).IsStableUnderRetracts := by
  rw [← freeDiskInclusions_rlp_eq]
  infer_instance

instance moduleDegreewiseSurjectiveRespectsIso : (moduleDegreewiseSurjective A D).RespectsIso := by
  rw [← freeDiskInclusions_rlp_eq]
  infer_instance

lemma complexSphereHomEquiv_naturality_val {K L : Complex A} (n : ℤ)
    (a : complexSphere A n ⟶ K) (f : K ⟶ L) :
    (complexSphereHomEquiv A L n (a ≫ f)).val =
      f.f n (complexSphereHomEquiv A K n a).val := by
  change (((HomologicalComplex.singleObjXSelf (.up ℤ) n (𝟙_ (ModuleCat A))).inv) ≫
    (a ≫ f).f n) (1 : A) = _
  rw [HomologicalComplex.comp_f]
  rfl

lemma freeSphereHomEquiv_naturality_val (x : D) (n : ℤ) {M N : ModuleCategory A D}
    (a : freeSphere A D x n ⟶ M) (f : M ⟶ N) :
    (freeSphereHomEquiv A D x n N (a ≫ f)).val =
      ((moduleEvaluation A D x).map f).f n (freeSphereHomEquiv A D x n M a).val := by
  simp only [freeSphereHomEquiv, Equiv.trans_apply, freeHomEquiv_naturality_right]
  exact complexSphereHomEquiv_naturality_val A n _ _

/-- 境界cellのliftを斉次生成元とその微分の方程式として記述する。 -/
def moduleBoundaryLiftAt (x : D) (n : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) : Prop :=
  ∀ z : complexCycles A ((moduleEvaluation A D x).obj M) (n + 1),
    ∀ y : ((moduleEvaluation A D x).obj N).X n,
      ((moduleEvaluation A D x).map f).f (n + 1) z.val =
        ((moduleEvaluation A D x).obj N).d n (n + 1) y →
      ∃ t : ((moduleEvaluation A D x).obj M).X n,
        ((moduleEvaluation A D x).obj M).d n (n + 1) t = z.val ∧
          ((moduleEvaluation A D x).map f).f n t = y

/-- 全dg自然な境界cellの右liftは、生成元と微分の同時liftに一致する。 -/
lemma freeCellBoundary_lifting_iff (x : D) (n : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    HasLiftingProperty (freeCellBoundary A D x n) f ↔ moduleBoundaryLiftAt A D x n f := by
  constructor
  · intro h z y hz
    let a := (freeSphereHomEquiv A D x (n + 1) M).symm z
    let b := (freeDiskHomEquiv A D x n N).symm y
    have sq : CommSq a (freeCellBoundary A D x n) f b := by
      constructor
      apply (freeSphereHomEquiv A D x (n + 1) N).injective
      apply Subtype.ext
      rw [freeSphereHomEquiv_naturality_val, freeCellBoundary_comp]
      simpa only [a, b, Equiv.apply_symm_apply] using hz
    obtain ⟨l⟩ := (h.sq_hasLift sq).exists_lift
    refine ⟨freeDiskHomEquiv A D x n M l.l, ?_, ?_⟩
    · rw [← freeCellBoundary_comp, l.fac_left]
      exact congrArg Subtype.val ((freeSphereHomEquiv A D x (n + 1) M).apply_symm_apply z)
    · rw [← freeDiskHomEquiv_naturality, l.fac_right]
      exact (freeDiskHomEquiv A D x n N).apply_symm_apply y
  · intro h
    constructor
    intro a b sq
    have hc := congrArg (fun k => (freeSphereHomEquiv A D x (n + 1) N k).val) sq.w
    rw [freeSphereHomEquiv_naturality_val, freeCellBoundary_comp] at hc
    obtain ⟨t, ht, hf⟩ := h (freeSphereHomEquiv A D x (n + 1) M a)
      (freeDiskHomEquiv A D x n N b) hc
    apply CommSq.HasLift.mk'
    refine { l := (freeDiskHomEquiv A D x n M).symm t
             fac_left := ?_
             fac_right := ?_ }
    · apply (freeSphereHomEquiv A D x (n + 1) M).injective
      apply Subtype.ext
      rw [freeCellBoundary_comp, Equiv.apply_symm_apply]
      exact ht
    · apply (freeDiskHomEquiv A D x n N).injective
      rw [freeDiskHomEquiv_naturality, Equiv.apply_symm_apply]
      exact hf

/-- 全次数で境界cellをliftできれば、まずcycleをliftし、その後任意の生成元をliftできる。 -/
lemma moduleSurjectiveAt_of_boundary_lifting (x : D) {M N : ModuleCategory A D} (f : M ⟶ N)
    (h : ∀ n : ℤ, moduleBoundaryLiftAt A D x n f) (n : ℤ) : moduleSurjectiveAt A D x n f := by
  intro y
  let y₁ := ((moduleEvaluation A D x).obj N).d n (n + 1) y
  have hy₁ : ((moduleEvaluation A D x).obj N).d (n + 1) (n + 1 + 1) y₁ = 0 := by
    have hd := ((moduleEvaluation A D x).obj N).d_comp_d n (n + 1) (n + 1 + 1)
    have he := congrArg (fun k => k y) hd
    exact he
  have hc : ((moduleEvaluation A D x).map f).f (n + 1 + 1)
      (0 : complexCycles A ((moduleEvaluation A D x).obj M) (n + 1 + 1)).val =
      ((moduleEvaluation A D x).obj N).d (n + 1) (n + 1 + 1) y₁ := by
    rw [hy₁]
    exact map_zero _
  obtain ⟨z, hz, hf⟩ := h (n + 1) 0 y₁ hc
  let zc : complexCycles A ((moduleEvaluation A D x).obj M) (n + 1) := ⟨z, hz⟩
  obtain ⟨t, _, ht⟩ := h n zc y hf
  exact ⟨t, ht⟩

/-- 自由sphere→diskの生成射族I。 -/
def freeCellBoundaries : MorphismProperty (ModuleCategory A D) :=
  MorphismProperty.ofHoms (fun i : D × ℤ => freeCellBoundary A D i.1 i.2)

lemma freeCellBoundaries_rlp_iff {M N : ModuleCategory A D} (f : M ⟶ N) :
    (freeCellBoundaries A D).rlp f ↔ ∀ (x : D) (n : ℤ), moduleBoundaryLiftAt A D x n f := by
  constructor
  · intro h x n
    exact (freeCellBoundary_lifting_iff A D x n f).1 (h _ (MorphismProperty.ofHoms.mk (x, n)))
  · intro h X Y i hi
    cases hi with
    | mk j => exact (freeCellBoundary_lifting_iff A D j.1 j.2 f).2 (h j.1 j.2)

/-- Iに対する右liftは各評価・次数でepiとなることを含意する。 -/
lemma freeCellBoundaries_rlp_degreewiseSurjective :
    (freeCellBoundaries A D).rlp ≤ moduleDegreewiseSurjective A D := by
  intro M N f hf x n
  exact moduleSurjectiveAt_of_boundary_lifting A D x f
    ((freeCellBoundaries_rlp_iff A D f).1 hf x) n

/-- 全評価で境界cellをliftできればobjectwise準同型となる。 -/
lemma moduleQuasiIso_of_boundary_lifting {M N : ModuleCategory A D} (f : M ⟶ N)
    (h : ∀ (x : D) (n : ℤ), moduleBoundaryLiftAt A D x n f) : moduleQuasiIso A D f := by
  intro x
  exact complex_quasiIso_of_boundary_lifting A ((moduleEvaluation A D x).map f) (h x)

lemma moduleBoundaryLiftAt_of_surjective_quasiIso {M N : ModuleCategory A D} (f : M ⟶ N)
    (hs : moduleDegreewiseSurjective A D f) (hq : moduleQuasiIso A D f) (x : D) (n : ℤ) :
    moduleBoundaryLiftAt A D x n f :=
  complex_boundary_lifting_of_surjective_quasiIso A ((moduleEvaluation A D x).map f)
    (hs x) (hq x) n

/-- Iに対する右liftはちょうど次数ごと全射なobjectwise準同型。 -/
lemma freeCellBoundaries_rlp_eq : (freeCellBoundaries A D).rlp =
    moduleDegreewiseSurjective A D ⊓ moduleQuasiIso A D := by
  ext M N f
  constructor
  · intro hf
    exact ⟨freeCellBoundaries_rlp_degreewiseSurjective A D f hf,
      moduleQuasiIso_of_boundary_lifting A D f ((freeCellBoundaries_rlp_iff A D f).1 hf)⟩
  · rintro ⟨hs, hq⟩
    apply (freeCellBoundaries_rlp_iff A D f).2
    exact moduleBoundaryLiftAt_of_surjective_quasiIso A D f hs hq

end SerrePositivity.DifferentialGraded
