module

public import SerrePositivity.InfinityCategories.ModelBridge.MiddleBackwardMovingExtractFamily
public import SerrePositivity.InfinityCategories.ModelBridge.MiddleBackwardRebuildArrows

/-!
# 動く局所図式から抽出した全対象の回収

概要：抽出した MovingFamily の全対象は、元の局所図式の同じ対象に等しい。
方針：対象ごとに既存の全頂点・全列の回収を適用する。
規約：端点は各対象で元の評価対象であり、添字方向の定数性は要求しない。
使われ方：前後の語と貼り合わせた置換の対象の照合。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.MiddleBackward.MovingExtract
open CategoryTheory HomotopicalAlgebra

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C] [ModelCategory C]
  {n m : ℕ} {A B : D ⥤ C}
  (F : Zigzag.MovingDiagram D C (weakEquivalences C) (word n m) A B)

lemma rebuilt_eq (d : D) : (family F).zigzagObj d = F.obj d := by
  exact Extract.rebuilt_eq (F.obj d)

end SerrePositivity.EInfinity.Hammock.MiddleBackward.MovingExtract
