module
public import SerrePositivity.DifferentialGraded.Quotient.Differential

/-! # 最終 dg 商 Hom の path 長 filtration

長さ n 以下の全 path の次数ごとの像の和を用いる。
内部微分は長さを保ち、ε 消去は長さを下げるので、最終微分でも部分複体をなす。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 長さ n 以下の path が生成する各次数の部分加群。 -/
def lengthSubmodule (S : Set D) (x y : D) (n : ℕ) (i : ℤ) :
    Submodule A ((internalHom A D S x y).X i) :=
  ⨆ (w : Word S) (_ : w.length ≤ n), LinearMap.range ((ι A D S x y w).f i).hom

lemma path_mem_lengthSubmodule (S : Set D) (x y : D) (n : ℕ) (i : ℤ)
    (w : Word S) (hw : w.length ≤ n) (z : (term A D w x y).X i) :
    (ι A D S x y w).f i z ∈ lengthSubmodule A D S x y n i := by
  have h : LinearMap.range ((ι A D S x y w).f i).hom ≤ lengthSubmodule A D S x y n i :=
    le_iSup_of_le w (le_iSup_of_le hw le_rfl)
  exact h ⟨z, rfl⟩

lemma lengthSubmodule_mono (S : Set D) (x y : D) {m n : ℕ} (hmn : m ≤ n) (i : ℤ) :
    lengthSubmodule A D S x y m i ≤ lengthSubmodule A D S x y n i := by
  refine iSup_le (fun w => iSup_le (fun hw => ?_))
  rintro z ⟨t, rfl⟩
  exact path_mem_lengthSubmodule A D S x y n i w (hw.trans hmn) t

/-- 全消去作用素の各 path 上の成分は、実際の短い path の有限和である。 -/
lemma erasure_path_apply (S : Set D) (x y : D) (w : Word S) (i : ℤ)
    (z : (term A D w x y).X i) :
    (erasure A D S x y).v i (i + 1) rfl ((ι A D S x y w).f i z) =
      ∑ j ∈ Finset.range w.length,
        (ι A D S x y (w.eraseIdx j)).f (i + 1) ((eraseFace A D w j x y).v i (i + 1) rfl z) := by
  let ev : Cochain (term A D w x y) (internalHom A D S x y) 1 →+
      (internalHom A D S x y).X (i + 1) :=
    { toFun := fun f => f.v i (i + 1) rfl z
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have h := congrArg ev (erasure_precomp A D S x y w)
  rw [eraseRow, map_sum] at h
  simpa only [ev, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    eraseSummand, Cochain.comp_zero_cochain_v, ModuleCat.comp_apply] using h

lemma erasure_path_mem_lengthSubmodule (S : Set D) (x y : D) (n : ℕ) (i : ℤ)
    (w : Word S) (hw : w.length ≤ n) (z : (term A D w x y).X i) :
    (erasure A D S x y).v i (i + 1) rfl ((ι A D S x y w).f i z) ∈
      lengthSubmodule A D S x y n (i + 1) := by
  rw [erasure_path_apply]
  apply Submodule.sum_mem
  intro j hj
  exact path_mem_lengthSubmodule A D S x y n (i + 1) (w.eraseIdx j)
    ((List.length_eraseIdx_le w j).trans hw) _

/-- 最終微分は長さの切断を保つ。 -/
lemma lengthSubmodule_d (S : Set D) (x y : D) (n : ℕ) (i : ℤ) :
    lengthSubmodule A D S x y n i ≤
      (lengthSubmodule A D S x y n (i + 1)).comap ((quotientHom A D S x y).d i (i + 1)).hom := by
  refine iSup_le (fun w => iSup_le (fun hw => ?_))
  rintro z ⟨t, rfl⟩
  change (quotientHom A D S x y).d i (i + 1) ((ι A D S x y w).f i t) ∈
    lengthSubmodule A D S x y n (i + 1)
  rw [quotientHom_d]
  change (internalHom A D S x y).d i (i + 1) ((ι A D S x y w).f i t) +
    (erasure A D S x y).v i (i + 1) rfl ((ι A D S x y w).f i t) ∈
      lengthSubmodule A D S x y n (i + 1)
  apply Submodule.add_mem
  · have hc := congrArg (fun f => f t) ((ι A D S x y w).comm i (i + 1))
    simp only [ModuleCat.comp_apply] at hc
    rw [hc]
    exact path_mem_lengthSubmodule A D S x y n (i + 1) w hw _
  · exact erasure_path_mem_lengthSubmodule A D S x y n i w hw t

/-- 最終微分を長さ n 以下の部分加群へ制限した線形写像。 -/
def lengthDifferential (S : Set D) (x y : D) (n : ℕ) (i : ℤ) :
    lengthSubmodule A D S x y n i →ₗ[A] lengthSubmodule A D S x y n (i + 1) :=
  LinearMap.codRestrict _
    (((quotientHom A D S x y).d i (i + 1)).hom.comp (lengthSubmodule A D S x y n i).subtype)
    (fun z => lengthSubmodule_d A D S x y n i z.property)

lemma lengthDifferential_coe (S : Set D) (x y : D) (n : ℕ) (i : ℤ)
    (z : lengthSubmodule A D S x y n i) :
    (lengthDifferential A D S x y n i z).val =
      (quotientHom A D S x y).d i (i + 1) z.val := rfl

/-- dg 商の最終 Hom の長さ n 以下の部分複体。 -/
def lengthComplex (S : Set D) (x y : D) (n : ℕ) : Complex A :=
  CochainComplex.of (fun i => ModuleCat.of A (lengthSubmodule A D S x y n i))
    (fun i => ModuleCat.ofHom (lengthDifferential A D S x y n i)) (fun i => by
      ext z
      exact congrArg (fun f : (quotientHom A D S x y).X i ⟶
        (quotientHom A D S x y).X (i + 1 + 1) => f z.val)
        ((quotientHom A D S x y).d_comp_d i (i + 1) (i + 1 + 1)))

@[simp] lemma lengthComplex_d (S : Set D) (x y : D) (n : ℕ) (i : ℤ) :
    (lengthComplex A D S x y n).d i (i + 1) =
      ModuleCat.ofHom (lengthDifferential A D S x y n i) :=
  CochainComplex.of_d (fun j => ModuleCat.of A (lengthSubmodule A D S x y n j))
    (fun j => ModuleCat.ofHom (lengthDifferential A D S x y n j)) i

/-- 長さ部分複体の最終 Hom への実際の chain map。 -/
def lengthInclusion (S : Set D) (x y : D) (n : ℕ) :
    lengthComplex A D S x y n ⟶ quotientHom A D S x y :=
  CochainComplex.ofHom (fun i => ModuleCat.ofHom (lengthSubmodule A D S x y n i).subtype)
    (fun i => by rw [lengthComplex_d]; ext z; rfl)

instance lengthInclusion_mono (S : Set D) (x y : D) (n : ℕ) :
    Mono (lengthInclusion A D S x y n) :=
  HomologicalComplex.mono_of_mono_f _ (fun _ =>
    (ModuleCat.mono_iff_injective _).2 (Submodule.subtype_injective _))

private lemma codRestrict_inclusion_naturality {V W : Type*}
    [AddCommGroup V] [AddCommGroup W] [Module A V] [Module A W]
    (f : V →ₗ[A] W) (P Q : Submodule A V) (R T : Submodule A W)
    (hPQ : P ≤ Q) (hRT : R ≤ T)
    (hP : ∀ z : P, f z ∈ R) (hQ : ∀ z : Q, f z ∈ T) :
    (LinearMap.codRestrict T (f.comp Q.subtype) hQ).comp (Submodule.inclusion hPQ) =
      (Submodule.inclusion hRT).comp (LinearMap.codRestrict R (f.comp P.subtype) hP) := by
  ext z
  rfl

lemma lengthDifferential_inclusion (S : Set D) (x y : D) {m n : ℕ} (hmn : m ≤ n) (i : ℤ) :
    (lengthDifferential A D S x y n i).comp
        (Submodule.inclusion (lengthSubmodule_mono A D S x y hmn i)) =
      (Submodule.inclusion (lengthSubmodule_mono A D S x y hmn (i + 1))).comp
        (lengthDifferential A D S x y m i) := by
  exact codRestrict_inclusion_naturality A _ _ _ _ _ _ _ _ _

/-- 長さの上限を増やすときの部分複体の包含。 -/
def lengthMap (S : Set D) (x y : D) {m n : ℕ} (hmn : m ≤ n) :
    lengthComplex A D S x y m ⟶ lengthComplex A D S x y n :=
  CochainComplex.ofHom (fun i => ModuleCat.ofHom
    (Submodule.inclusion (lengthSubmodule_mono A D S x y hmn i)))
    (fun i => by
      rw [lengthComplex_d, lengthComplex_d]
      exact ModuleCat.hom_ext (lengthDifferential_inclusion A D S x y hmn i))

@[reassoc] lemma lengthMap_inclusion (S : Set D) (x y : D) {m n : ℕ} (hmn : m ≤ n) :
    lengthMap A D S x y hmn ≫ lengthInclusion A D S x y n = lengthInclusion A D S x y m := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  exact Submodule.subtype_comp_inclusion (lengthSubmodule A D S x y m i)
    (lengthSubmodule A D S x y n i) (lengthSubmodule_mono A D S x y hmn i)

lemma lengthMap_refl (S : Set D) (x y : D) (n : ℕ) :
    lengthMap A D S x y (le_refl n) = 𝟙 (lengthComplex A D S x y n) := by
  apply (cancel_mono (lengthInclusion A D S x y n)).mp
  rw [lengthMap_inclusion, Category.id_comp]

lemma lengthMap_comp (S : Set D) (x y : D) {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p) :
    lengthMap A D S x y hmn ≫ lengthMap A D S x y hnp = lengthMap A D S x y (hmn.trans hnp) := by
  apply (cancel_mono (lengthInclusion A D S x y p)).mp
  rw [Category.assoc, lengthMap_inclusion, lengthMap_inclusion, lengthMap_inclusion]

/-- 消去作用素は filtration を一段下げる。n=0 では元の Hom 上の消去零性を含む。 -/
lemma lengthSubmodule_erasure (S : Set D) (x y : D) (n : ℕ) (i : ℤ) :
    lengthSubmodule A D S x y n i ≤
      (lengthSubmodule A D S x y (n - 1) (i + 1)).comap
        ((erasure A D S x y).v i (i + 1) rfl).hom := by
  refine iSup_le (fun w => iSup_le (fun hw => ?_))
  rintro z ⟨t, rfl⟩
  change (erasure A D S x y).v i (i + 1) rfl ((ι A D S x y w).f i t) ∈
    lengthSubmodule A D S x y (n - 1) (i + 1)
  rw [erasure_path_apply]
  apply Submodule.sum_mem
  intro j hj
  have hlen := List.length_eraseIdx_add_one (Finset.mem_range.mp hj)
  exact path_mem_lengthSubmodule A D S x y (n - 1) (i + 1) (w.eraseIdx j) (by omega) _

/-- 各次数において長さ filtration の和は最終 Hom 全体である。 -/
lemma lengthSubmodule_exhaustive (S : Set D) (x y : D) (i : ℤ) :
    (⨆ n : ℕ, lengthSubmodule A D S x y n i) = ⊤ := by
  let P := ⨆ n : ℕ, lengthSubmodule A D S x y n i
  have hq : ModuleCat.ofHom P.mkQ = 0 := by
    apply (isColimitOfHasCoproductOfPreservesColimit
      (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i)
      (fun w : Word S => term A D w x y)).hom_ext
    rintro ⟨w⟩
    ext z
    change P.mkQ ((ι A D S x y w).f i z) = 0
    apply (Submodule.Quotient.mk_eq_zero P).2
    exact (le_iSup (fun n => lengthSubmodule A D S x y n i) w.length)
      (path_mem_lengthSubmodule A D S x y w.length i w le_rfl z)
  apply top_unique
  intro z _
  apply (Submodule.Quotient.mk_eq_zero P).1
  exact congrArg (fun f => f z) hq

end SerrePositivity.DifferentialGraded.DGQuotient
