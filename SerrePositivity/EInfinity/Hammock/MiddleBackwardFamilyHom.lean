module

public import SerrePositivity.EInfinity.Hammock.MiddleBackwardFamilyPushout

/-!
# 元の二つのブロック図式の自然な比較

概要：左右の自然な縦弱同値と三つの脚への整合性を持つ比較を記録する。
方針：元の各対象で左右と中央の正方形を貼り、固定端点の実際の射を得る。
規約：比較の成分は全頂点で弱同値。nerve の弱同値性を仮定しない。
使われ方：元の全体に対する pullback の counit と pushout の unit。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.MiddleBackward.Family
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra ForwardPath

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C] [ModelCategory C]
  {n m : ℕ} {X Y : C}

structure Hom (F G : Family D C n m X Y) where
  left : F.left ⟶ G.left
  right : F.right ⟶ G.right
  left_mem : ∀ d i, weakEquivalences C ((left.app d).app i)
  right_mem : ∀ d i, weakEquivalences C ((right.app d).app i)
  a_comm : Functor.whiskerRight left (pathEvaluation C n 0) ≫ G.a = F.a
  middle_comm : F.middle ≫ Functor.whiskerRight left (pathEvaluation C n (Fin.last n)) =
    Functor.whiskerRight right (pathEvaluation C m 0) ≫ G.middle
  b_comm : F.b ≫ Functor.whiskerRight right (pathEvaluation C m (Fin.last m)) = G.b

namespace Hom
variable {F G : Family D C n m X Y} (h : Hom F G)

def app (d : D) : Zigzag.Hom (F.zigzagObj d) (G.zigzagObj d) := by
  let l := leftBoundaryComparison (h.left.app d) (h.left_mem d)
    (F.a.app d) (G.a.app d) (F.a_mem d) (G.a_mem d)
    (𝟙 X) ((weakEquivalences C).id_mem _)
    ((Category.comp_id _).trans (congr_app h.a_comm d).symm)
  let c := BackwardZigzag.movingHom (F.middle_mem d) (G.middle_mem d)
    ((h.left.app d).app (Fin.last n)) ((h.right.app d).app 0)
    (h.left_mem d _) (h.right_mem d _) (congr_app h.middle_comm d)
  have hj : HEq (l.app (Fin.last (leftBoundaryWord n).length)) (c.app 0) :=
    leftBoundaryComparison_last _ _ _ _ _ _ _ _ _
  let lc := ZigzagAppend.Moving.map l c hj
  let r := rightBoundaryComparison (h.right.app d) (h.right_mem d)
    (F.b.app d) (G.b.app d) (F.b_mem d) (G.b_mem d)
    (𝟙 Y) ((weakEquivalences C).id_mem _)
    ((congr_app h.b_comm d).trans (Category.id_comp _).symm)
  have hj' : HEq (lc.app (Fin.last (Word.append (leftBoundaryWord n)
      (Word.single .backward)).length)) (r.app 0) := by
    apply HEq.trans (ZigzagAppend.Moving.app_right_heq l c hj (Fin.last 1))
    exact (rightBoundaryComparison_first _ _ _ _ _ _ _ _ _).symm
  have hf : HEq (lc.app 0) (𝟙 X) := by
    apply HEq.trans (ZigzagAppend.Moving.app_left_heq l c 0)
    exact leftBoundaryComparison_first _ _ _ _ _ _ _ _ _
  have hl : HEq (r.app (Fin.last (rightBoundaryWord m).length)) (𝟙 Y) :=
    rightBoundaryComparison_last _ _ _ _ _ _ _ _ _
  exact ZigzagAppend.Moving.fixedMap lc r hj'
    (Zigzag.MovingHom.first_of_heq_id lc hf) (Zigzag.MovingHom.last_of_heq_id r hl)

end Hom
end SerrePositivity.EInfinity.Hammock.MiddleBackward.Family
