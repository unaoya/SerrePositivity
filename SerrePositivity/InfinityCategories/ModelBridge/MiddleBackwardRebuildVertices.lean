module

public import SerrePositivity.InfinityCategories.ModelBridge.MiddleBackwardExtractFamily
public import SerrePositivity.EInfinity.Hammock.MiddleBackwardPositionCases

/-!
# 元の固定語から抽出した図式の全頂点の再構成

概要：抽出した左右の射列と三つの脚を貼ると、元の全頂点を回収する。
方針：元の左右の位置の成分回収と、全頂点の場合分けを使う。
規約：両端の同定は元の first/last の等式による。
使われ方：再構成関手を元の恒等図式と同定する。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.MiddleBackward.Extract
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra ForwardPath

variable {C : Type u} [Category.{v} C] [ModelCategory C] {n m : ℕ} {X Y : C}

def rebuilt (S : Zigzag (weakEquivalences C) (word n m) X Y) :
    Zigzag (weakEquivalences C) (word n m) X Y := family.zigzagObj S

def rebuildFunctor : Zigzag (weakEquivalences C) (word n m) X Y ⥤
    Zigzag (weakEquivalences C) (word n m) X Y := family.zigzagFunctor

lemma rebuilt_leftVertex (S : Zigzag (weakEquivalences C) (word n m) X Y)
    (i : Fin (n + 1)) :
    (rebuilt S).vertex (Positions.leftVertex n m i) = S.vertex (Positions.leftVertex n m i) := by
  dsimp only [rebuilt, Family.zigzagObj, family, MiddleBackward.obj, leftBoundaryBlock,
    rightBoundaryBlock, Positions.leftVertex, ZigzagAppend.obj]
  simp only [ZigzagAppend.vertex_left, ZigzagAppend.vertex_right]
  rfl

lemma rebuilt_rightVertex (S : Zigzag (weakEquivalences C) (word n m) X Y)
    (i : Fin (m + 1)) :
    (rebuilt S).vertex (Positions.rightVertex n m i) = S.vertex (Positions.rightVertex n m i) := by
  dsimp only [rebuilt, Family.zigzagObj, family, MiddleBackward.obj, leftBoundaryBlock,
    rightBoundaryBlock, Positions.rightVertex, ZigzagAppend.obj]
  simp only [ZigzagAppend.vertex_right, ZigzagAppend.vertex_left]
  rfl

lemma rebuilt_vertex (S : Zigzag (weakEquivalences C) (word n m) X Y)
    (j : Fin ((word n m).length + 1)) : (rebuilt S).vertex j = S.vertex j := by
  apply Positions.vertex_cases n m (P := fun j => (rebuilt S).vertex j = S.vertex j)
  · exact (rebuilt S).first.trans S.first.symm
  · exact rebuilt_leftVertex S
  · exact rebuilt_rightVertex S
  · exact (rebuilt S).last.trans S.last.symm

end SerrePositivity.EInfinity.Hammock.MiddleBackward.Extract
