module

public import SerrePositivity.EInfinity.Hammock.MiddleBackwardMovingFamilyHom
public import SerrePositivity.EInfinity.Hammock.ZigzagMovingDiagramFixed

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
namespace SerrePositivity.EInfinity.Hammock.MiddleBackward.MovingFamily.Hom
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra ForwardPath

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C] [ModelCategory C]
  {n m : ℕ} {A B : D ⥤ C} {F G : MovingFamily D C n m A B} (h : Hom F G)

def diagramHom : Zigzag.MovingDiagram.Hom F.movingDiagram G.movingDiagram where
  app d := Zigzag.MovingHom.ofHom (h.app d)
  naturality := by
    intro d d' f
    apply Zigzag.MovingHom.ext
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
    dsimp only [zigzagMap, zigzagMapData, app, ZigzagAppend.Moving.fixedMap,
      ZigzagAppend.Moving.map,
      leftBoundaryComparison, rightBoundaryComparison, ZigzagAppend.Moving.app, movingHom,
      zigzagObj, MiddleBackward.obj, leftBoundaryBlock, rightBoundaryBlock, ZigzagAppend.obj]
    split_ifs <;> simp [BackwardZigzag.movingHom_app_comp_assoc (W := weakEquivalences C),
      Category.assoc, hl, hr, hl', hr']
  first d := by
    change HEq ((h.app d).app 0) (𝟙 (A.obj d))
    apply (conj_eqToHom_iff_heq _ _ (F.zigzagObj d).first (G.zigzagObj d).first).1
    simpa only [Category.id_comp, eqToHom_trans] using (h.app d).first
  last d := by
    change HEq ((h.app d).app (Fin.last (word n m).length)) (𝟙 (B.obj d))
    apply (conj_eqToHom_iff_heq _ _ (F.zigzagObj d).last (G.zigzagObj d).last).1
    simpa only [Category.id_comp, eqToHom_trans] using (h.app d).last

end SerrePositivity.EInfinity.Hammock.MiddleBackward.MovingFamily.Hom
