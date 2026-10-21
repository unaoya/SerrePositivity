module

public import SerrePositivity.EInfinity.Hammock.MiddleBackwardMovingFamilyMaps
public import SerrePositivity.EInfinity.Hammock.BackwardZigzagLaws
public import SerrePositivity.EInfinity.Hammock.ForwardPathZigzagLaws
public import SerrePositivity.EInfinity.Hammock.ZigzagMovingAppendFixedLaws

/-!
# 動く局所端点を持つ全体の図式の恒等と合成

概要：元の左右射列と三つの自然な脚の図式を、動く端点の zigzag 図式にする。
方針：元の成分の恒等・合成則を、全ての貼り合わせ頂点で検証する。
規約：添字圏は任意。元の縦弱同値だけを使う。
使われ方：中央の列の置換の関手性と counit/unit の自然性。
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

lemma zigzagMap_id (d : D) : F.zigzagMap (𝟙 d) = Zigzag.MovingHom.id (F.zigzagObj d) := by
  dsimp only [zigzagMap, zigzagMapData]
  simp only [F.left.map_id, F.right.map_id, A.map_id, B.map_id, NatTrans.id_app,
    leftBoundaryComparison, rightBoundaryComparison, ForwardPath.movingHom_id,
    BackwardZigzag.movingHom_id (W := weakEquivalences C) (X := A.obj d)
      (Y := (F.left.obj d).obj 0),
    BackwardZigzag.movingHom_id (W := weakEquivalences C)
      (X := (F.left.obj d).obj (Fin.last n)) (Y := (F.right.obj d).obj 0),
    BackwardZigzag.movingHom_id (W := weakEquivalences C)
      (X := (F.right.obj d).obj (Fin.last m)) (Y := B.obj d),
    ZigzagAppend.Moving.map_id]
  apply Zigzag.MovingHom.ext
  intro j
  dsimp only [ZigzagAppend.Moving.map,
    ZigzagAppend.Moving.app, Zigzag.MovingHom.id]
  dsimp only [zigzagObj, MiddleBackward.obj, leftBoundaryBlock, rightBoundaryBlock,
    ZigzagAppend.obj]
  split_ifs <;> simp

lemma zigzagMap_comp {d d' d'' : D} (f : d ⟶ d') (g : d' ⟶ d'') :
    F.zigzagMap (f ≫ g) = (F.zigzagMap f).comp (F.zigzagMap g) := by
  apply Zigzag.MovingHom.ext
  intro j
  change (F.zigzagMap (f ≫ g)).app j = (F.zigzagMap f).app j ≫ (F.zigzagMap g).app j
  dsimp only [zigzagMap, zigzagMapData, ZigzagAppend.Moving.map,
    leftBoundaryComparison, rightBoundaryComparison, ZigzagAppend.Moving.app, movingHom,
    zigzagObj, MiddleBackward.obj, leftBoundaryBlock, rightBoundaryBlock, ZigzagAppend.obj]
  split_ifs <;> simp [F.left.map_comp, F.right.map_comp, A.map_comp, B.map_comp,
    BackwardZigzag.movingHom_app_comp_assoc (W := weakEquivalences C), Category.assoc]

def movingDiagram : Zigzag.MovingDiagram D C (weakEquivalences C) (word n m) A B where
  obj := F.zigzagObj
  map := F.zigzagMap
  map_id := F.zigzagMap_id
  map_comp := F.zigzagMap_comp
  first := F.zigzagMap_first
  last := F.zigzagMap_last

end SerrePositivity.EInfinity.Hammock.MiddleBackward.MovingFamily
