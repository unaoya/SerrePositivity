module

public import SerrePositivity.InfinityCategories.ModelBridge.MiddleBackwardMovingFamily

/-!
# 動く局所端点も保持した全縦射の貼り合わせ

概要：元の二つの射列の比較を貼り、両端で元の評価関手の射を回収する。
方針：左右の境界ブロックと中央の正方形を同じ接合点で貼り合わせる。
規約：外側の二つの成分も元の非恒等射のまま保持する。
使われ方：全体の前後の語と貼り合わせる局所置換の図式。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.MiddleBackward.MovingFamily
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra ForwardPath

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C] [ModelCategory C]
  {n m : ℕ} {A B : D ⥤ C} (F : MovingFamily D C n m A B)

def zigzagMapData {d d' : D} (f : d ⟶ d') :
    {g : Zigzag.MovingHom (F.zigzagObj d) (F.zigzagObj d') //
      HEq (g.app 0) (A.map f) ∧ HEq (g.app (Fin.last (word n m).length)) (B.map f)} := by
  let l := leftBoundaryComparison (F.left.map f) (F.left_mem f)
    (F.a.app d) (F.a.app d') (F.a_mem d) (F.a_mem d')
    (A.map f) (F.endpoint_left_mem f) (F.a.naturality f).symm
  let c := BackwardZigzag.movingHom (F.middle_mem d) (F.middle_mem d')
    ((F.left.map f).app (Fin.last n)) ((F.right.map f).app 0)
    (F.left_mem f _) (F.right_mem f _) (F.middle.naturality f).symm
  have hj : HEq (l.app (Fin.last (leftBoundaryWord n).length)) (c.app 0) :=
    leftBoundaryComparison_last _ _ _ _ _ _ _ _ _
  let lc := ZigzagAppend.Moving.map l c hj
  let r := rightBoundaryComparison (F.right.map f) (F.right_mem f)
    (F.b.app d) (F.b.app d') (F.b_mem d) (F.b_mem d')
    (B.map f) (F.endpoint_right_mem f) (F.b.naturality f).symm
  have hj' : HEq (lc.app (Fin.last (Word.append (leftBoundaryWord n)
      (Word.single .backward)).length)) (r.app 0) := by
    apply HEq.trans (ZigzagAppend.Moving.app_right_heq l c hj (Fin.last 1))
    exact (rightBoundaryComparison_first _ _ _ _ _ _ _ _ _).symm
  have hf : HEq (lc.app 0) (A.map f) := by
    apply HEq.trans (ZigzagAppend.Moving.app_left_heq l c 0)
    exact leftBoundaryComparison_first _ _ _ _ _ _ _ _ _
  have hl : HEq (r.app (Fin.last (rightBoundaryWord m).length)) (B.map f) :=
    rightBoundaryComparison_last _ _ _ _ _ _ _ _ _
  exact ⟨ZigzagAppend.Moving.map lc r hj',
    ⟨(ZigzagAppend.Moving.app_left_heq lc r 0).trans hf,
      (ZigzagAppend.Moving.app_right_heq lc r hj' (Fin.last (rightBoundaryWord m).length)).trans
        hl⟩⟩

def zigzagMap {d d' : D} (f : d ⟶ d') : Zigzag.MovingHom (F.zigzagObj d) (F.zigzagObj d') :=
  (F.zigzagMapData f).val

lemma zigzagMap_first {d d' : D} (f : d ⟶ d') : HEq ((F.zigzagMap f).app 0) (A.map f) :=
  (F.zigzagMapData f).property.1

lemma zigzagMap_last {d d' : D} (f : d ⟶ d') :
    HEq ((F.zigzagMap f).app (Fin.last (word n m).length)) (B.map f) :=
  (F.zigzagMapData f).property.2

end SerrePositivity.EInfinity.Hammock.MiddleBackward.MovingFamily
