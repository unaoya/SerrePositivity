module

public import SerrePositivity.InfinityCategories.ModelBridge.MiddleBackwardFamilyMaps
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.BackwardZigzagLaws
public import SerrePositivity.EInfinity.Hammock.ForwardPathZigzagLaws
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagMovingAppendFixedLaws

/-!
# 元の全体の zigzag の関手的な貼り合わせ

概要：元の左右射列と三つの自然な脚の図式を、固定端点の zigzag 図式にする。
方針：元の成分の恒等・合成則を、全ての貼り合わせ頂点で検証する。
規約：添字圏は任意。元の縦弱同値だけを使う。
使われ方：中央の列の置換の関手性と counit/unit の自然性。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.MiddleBackward.Family
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra ForwardPath

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C] [ModelCategory C]
  {n m : ℕ} {X Y : C} (F : Family D C n m X Y)

lemma zigzagMap_id (d : D) : F.zigzagMap (𝟙 d) = 𝟙 (F.zigzagObj d) := by
  unfold zigzagMap
  simp only [F.left.map_id, F.right.map_id, NatTrans.id_app,
    leftBoundaryComparison, rightBoundaryComparison, ForwardPath.movingHom_id,
    BackwardZigzag.movingHom_id (W := weakEquivalences C) (X := X)
      (Y := (F.left.obj d).obj 0),
    BackwardZigzag.movingHom_id (W := weakEquivalences C)
      (X := (F.left.obj d).obj (Fin.last n)) (Y := (F.right.obj d).obj 0),
    BackwardZigzag.movingHom_id (W := weakEquivalences C)
      (X := (F.right.obj d).obj (Fin.last m)) (Y := Y),
    ZigzagAppend.Moving.map_id]
  apply Zigzag.hom_ext
  intro j
  dsimp only [ZigzagAppend.Moving.fixedMap, ZigzagAppend.Moving.map,
    ZigzagAppend.Moving.app, Zigzag.MovingHom.id]
  dsimp only [zigzagObj, MiddleBackward.obj, leftBoundaryBlock, rightBoundaryBlock,
    ZigzagAppend.obj]
  split_ifs <;> simp

lemma zigzagMap_comp {d d' d'' : D} (f : d ⟶ d') (g : d' ⟶ d'') :
    F.zigzagMap (f ≫ g) =
      ((F.zigzagMap f : F.zigzagObj d ⟶ F.zigzagObj d') ≫
        (F.zigzagMap g : F.zigzagObj d' ⟶ F.zigzagObj d'') :
          F.zigzagObj d ⟶ F.zigzagObj d'') := by
  apply Zigzag.hom_ext
  intro j
  change (F.zigzagMap (f ≫ g)).app j = (F.zigzagMap f).app j ≫ (F.zigzagMap g).app j
  dsimp only [zigzagMap, ZigzagAppend.Moving.fixedMap, ZigzagAppend.Moving.map,
    leftBoundaryComparison, rightBoundaryComparison, ZigzagAppend.Moving.app, movingHom,
    zigzagObj, MiddleBackward.obj, leftBoundaryBlock, rightBoundaryBlock, ZigzagAppend.obj]
  split_ifs <;> simp [F.left.map_comp, F.right.map_comp,
    BackwardZigzag.movingHom_app_comp_assoc (W := weakEquivalences C), Category.assoc]

def zigzagFunctor : D ⥤ Zigzag (weakEquivalences C) (word n m) X Y where
  obj := F.zigzagObj
  map := F.zigzagMap
  map_id := F.zigzagMap_id
  map_comp := F.zigzagMap_comp

end SerrePositivity.EInfinity.Hammock.MiddleBackward.Family
