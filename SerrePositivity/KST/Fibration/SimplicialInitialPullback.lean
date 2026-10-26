module
public import SerrePositivity.KST.Fibration.PullbackCancellation
public import SerrePositivity.KST.SConstruction.ConnectedDiagramRetractions
public import SerrePositivity.KST.SConstruction.SimplicialCartesianNaturality

/-!
概要：初期評価の引き戻しから全有限旗自然性へ進む共通の単体的計算。
方針：先頭を保つ作用素では水平貼り合わせを消去し、第零面は連結行の退縮で検出する。
規約：商・核・旗の模型に依存しない。元の自然変換の四角形を保持する。
使われ方：既存 q 版と閉じた P 版で全自然性の証明を共有する。
-/
@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Comparison
namespace SerrePositivity.KST.Fibration

/-- 概要：元の初期評価四角形が引き戻しなら、先頭を保つ自然性四角形も引き戻し。
方針：同じ初期評価を後ろへ貼り、元の二つの引き戻しを水平消去する。
規約：全て元の実 SSet 写像。使われ方：有限旗の共通自然性計算。 -/
theorem simplicialInitialComparison_head_homotopyPullback
    {X Y : SimplicialObject SSet.{u}} (α : X ⟶ Y) {A B : SSet.{u}} (f : A ⟶ B)
    (x : ∀ n, X.obj (Opposite.op n) ⟶ A) (y : ∀ n, Y.obj (Opposite.op n) ⟶ B)
    (sq : ∀ n, CommSq (x n) (α.app (Opposite.op n)) f (y n))
    (hsq : ∀ n, IsHomotopyPullback (sq n))
    {m n : SimplexCategory} (θ : m ⟶ n)
    (hx : X.map θ.op ≫ x m = x n) (hy : Y.map θ.op ≫ y m = y n) :
    IsHomotopyPullback (CommSq.mk (α.naturality θ.op)) := by
  let s := CommSq.mk (α.naturality θ.op)
  let t := sq m
  have hout : IsHomotopyPullback (s.horiz_comp t) := by
    apply (isHomotopyPullback_iff_of_localized_isIso (s.horiz_comp t)
      (sq n) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _)
      ?_ ?_ ?_ ?_ (by infer_instance) (by infer_instance)
      (by infer_instance) (by infer_instance)).mpr
    · exact hsq n
    · simpa only [Category.comp_id, Category.id_comp] using hx
    · simp only [Category.comp_id, Category.id_comp]
    · simp only [Category.comp_id, Category.id_comp]
    · simpa only [Category.comp_id, Category.id_comp] using hy
  exact isHomotopyPullback_left_of_horiz s t hout (hsq m)

/-- 概要：連結な行の元の自然変換では、先頭を保つ作用素の引き戻し性で全作用素を検出。
方針：第零面を同じ退化の退縮として検出し、全生成面と退化を合成する。
規約：追加の模型存在仮定なし。使われ方：P 版と q 版の共通の全自然性仕上げ。 -/
theorem simplicialNaturality_homotopyPullback_of_head
    {X Y : SimplicialObject SSet.{u}} (α : X ⟶ Y)
    [∀ n, SSet.IsConnected (Y.obj (Opposite.op n))]
    (hhead : ∀ {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌), θ.toOrderHom 0 = 0 →
      IsHomotopyPullback (CommSq.mk (α.naturality θ.op)))
    {d e : SimplexCategory} (θ : d ⟶ e) :
    IsHomotopyPullback (CommSq.mk (α.naturality θ.op)) := by
  apply simplicial_naturality_homotopyPullback_of_generators α ?_ ?_ θ
  · intro n j
    refine Fin.cases ?_ (fun k => ?_) j
    · have hsr : (SimplexCategory.σ (0 : Fin (n + 1))).op ≫
          (SimplexCategory.δ (0 : Fin (n + 2))).op = 𝟙 _ := by
        rw [← op_comp]
        change (SimplexCategory.δ (Fin.castSucc (0 : Fin (n + 1))) ≫
          SimplexCategory.σ (0 : Fin (n + 1))).op = _
        rw [SimplexCategory.δ_comp_σ_self, op_id]
      apply naturality_homotopyPullback_retraction_of_section α
        (SimplexCategory.σ (0 : Fin (n + 1))).op
        (SimplexCategory.δ (0 : Fin (n + 2))).op hsr (Classical.arbitrary _)
      exact hhead _ rfl
    · exact hhead (SimplexCategory.δ k.succ) (Fin.succ_succAbove_zero k)
  · intro n j
    apply hhead (SimplexCategory.σ j)
    simp [SimplexCategory.σ]

end SerrePositivity.KST.Fibration
