module

public import SerrePositivity.KST.Comparison.FibrantSquareCriterion
public import SerrePositivity.KST.Comparison.KanReplacementSquares

/-!
# 図式の一つの射に沿う厳密ファイバー

概要：図式の射の自然性の四角形に、右側の縦射の厳密な引き戻しを付ける。
方針：引き戻しへの標準比較を作り、Kan 条件とホモトピー引き戻しの判定を適用する。
規約：Segal 1974 Lemma 1.7 の二つのファイバー模型への比較。
使われ方：共通の trivial fibration の模型を span の中央から構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe w v u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
open SerrePositivity.SimplicialModel
variable {D : Type v} [Category.{w} D] {F G : D ⥤ SSet.{u}}

/--
概要：図式の射の右側の成分を、添字の射に沿って引き戻した実対象。
方針：終域図式の射と自然変換の終点の成分の厳密な引き戻しを取る。
規約：基底は添字の射の始点における終域図式の値。
使われ方：span の端点のファイバー模型。
-/
def diagramArrowFiber (α : F ⟶ G) {d e : D} (θ : d ⟶ e) : SSet.{u} :=
  pullback (G.map θ) (α.app e)

/--
概要：図式の始点の値から、終点の厳密ファイバーへの標準比較。
方針：自然性の四角形を引き戻しへ持ち上げる。
規約：第一成分は自然変換の始点の成分、第二成分は始域図式の射。
使われ方：二つのファイバー模型の共通の比較。
-/
def diagramArrowFiberComparison (α : F ⟶ G) {d e : D} (θ : d ⟶ e) :
    F.obj d ⟶ diagramArrowFiber α θ :=
  pullback.lift (α.app d) (F.map θ) (α.naturality θ).symm

/--
概要：終点の縦射が Kan fibration なら、自然性のホモトピー引き戻し性を標準比較の可逆性で判定できる。
方針：Kan な縦射の厳密ファイバーによる判定を適用する。
規約：始点の基底の Kan 性はこの判定には不要。
使われ方：中央の対象から二つのファイバーへの局所化同型。
-/
theorem diagramArrowFiberComparison_isIso_iff (α : F ⟶ G) {d e : D} (θ : d ⟶ e)
    (hα : SSet.modelCategoryQuillen.J.rlp (α.app e)) :
    IsIso (AnodyneHomotopy.anodyneQ.map (diagramArrowFiberComparison α θ)) ↔
      IsHomotopyPullback (naturalitySquare (diagramArrow θ) α) :=
  (isHomotopyPullback_iff_strict_of_left_fibration
    (naturalitySquare (diagramArrow θ) α) hα).symm

/--
概要：始点の基底が Kan で終点の縦射が Kan fibration なら、厳密ファイバーの全空間は Kan である。
方針：引き戻した第一射影の Kan 条件と、基底の Kan 性を合成する。
規約：添字の圏や始域図式の他の値には条件を課さない。
使われ方：共通の trivial fibration の模型の二つの終域の Kan 性。
-/
theorem diagramArrowFiber_kanComplex (α : F ⟶ G) {d e : D} (θ : d ⟶ e)
    [SSet.KanComplex (G.obj d)] (hα : SSet.modelCategoryQuillen.J.rlp (α.app e)) :
    SSet.KanComplex (diagramArrowFiber α θ) := by
  let : (fibrations SSet.{u}).IsStableUnderComposition := by
    rw [SSet.modelCategoryQuillen.fibrations_eq]
    infer_instance
  let : Fibration (pullback.fst (G.map θ) (α.app e)) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mpr
      (SSet.modelCategoryQuillen.J.rlp.pullback_fst (G.map θ) (α.app e) hα)
  exact isFibrant_of_fibration (pullback.fst (G.map θ) (α.app e))

end SerrePositivity.KST.Comparison
