module

public import SerrePositivity.InfinityCategories.ModelBridge.MiddleBackwardFamilyHom

/-!
# 全体の zigzag 関手間の元の自然変換

概要：二つのブロック図式の自然な比較を、実際の全体の自然変換へ移す。
方針：各頂点で左右の自然性を回収し、一列の正方形の合成則で貼る。
規約：全体の X,Y を保持する。局所端点を恒等射に固定しない。
使われ方：中央の列の置換による counit と unit の自然性。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.MiddleBackward.Family.Hom
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra ForwardPath

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C] [ModelCategory C]
  {n m : ℕ} {X Y : C} {F G : Family D C n m X Y} (h : Hom F G)

def natTrans : F.zigzagFunctor ⟶ G.zigzagFunctor where
  app := h.app
  naturality d d' f := by
    apply Zigzag.hom_ext
    intro j
    change (F.zigzagMap f).app j ≫ (h.app d').app j =
      (h.app d).app j ≫ (G.zigzagMap f).app j
    have hl (i : Fin (n + 1)) :
        (F.left.map f).app i ≫ (h.left.app d').app i =
          (h.left.app d).app i ≫ (G.left.map f).app i := congr_app (h.left.naturality f) i
    have hr (i : Fin (m + 1)) :
        (F.right.map f).app i ≫ (h.right.app d').app i =
          (h.right.app d).app i ≫ (G.right.map f).app i := congr_app (h.right.naturality f) i
    have hl' (i : Fin (n + 1)) {Z : C} (k : (G.left.obj d').obj i ⟶ Z) :
        (F.left.map f).app i ≫ (h.left.app d').app i ≫ k =
          (h.left.app d).app i ≫ (G.left.map f).app i ≫ k := by
      rw [← Category.assoc, hl, Category.assoc]
    have hr' (i : Fin (m + 1)) {Z : C} (k : (G.right.obj d').obj i ⟶ Z) :
        (F.right.map f).app i ≫ (h.right.app d').app i ≫ k =
          (h.right.app d).app i ≫ (G.right.map f).app i ≫ k := by
      rw [← Category.assoc, hr, Category.assoc]
    dsimp only [zigzagMap, app, ZigzagAppend.Moving.fixedMap, ZigzagAppend.Moving.map,
      leftBoundaryComparison, rightBoundaryComparison, ZigzagAppend.Moving.app, movingHom,
      zigzagObj, MiddleBackward.obj, leftBoundaryBlock, rightBoundaryBlock, ZigzagAppend.obj]
    split_ifs <;> simp [BackwardZigzag.movingHom_app_comp_assoc (W := weakEquivalences C),
      Category.assoc, hl, hr, hl', hr']

end SerrePositivity.EInfinity.Hammock.MiddleBackward.Family.Hom
