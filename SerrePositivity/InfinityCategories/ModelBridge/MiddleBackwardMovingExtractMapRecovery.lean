module

public import SerrePositivity.InfinityCategories.ModelBridge.MiddleBackwardMovingExtractRecovery
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagMovingDiagramExt

/-!
# 動く局所図式の全縦射と図式自体の回収

概要：元の図式から抽出したブロックの貼り直しは、元の図式に厳密に等しい。
方針：左右の全縦成分と両端の元の射を回収し、図式の外延性を使う。
規約：端点の射は非恒等射でもよい。長さ零も含む。
使われ方：局所置換の counit を元の全図式へ戻す。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.MiddleBackward.MovingExtract
open CategoryTheory HomotopicalAlgebra ForwardPath

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C] [ModelCategory C]
  {n m : ℕ} {A B : D ⥤ C}
  (F : Zigzag.MovingDiagram D C (weakEquivalences C) (word n m) A B)
  {d d' : D} (f : d ⟶ d')

lemma rebuilt_map_left (i : Fin (n + 1)) :
    HEq (((family F).zigzagMap f).app (Positions.leftVertex n m i))
      ((F.map f).app (Positions.leftVertex n m i)) := by
  dsimp only [MovingFamily.zigzagMap, MovingFamily.zigzagMapData, Positions.leftVertex]
  apply HEq.trans (ZigzagAppend.Moving.app_left_heq (b := rightBoundaryWord m) _ _ _)
  apply HEq.trans (ZigzagAppend.Moving.app_left_heq (b := Word.single .backward) _ _ _)
  dsimp only [leftBoundaryComparison, ZigzagAppend.Moving.map]
  apply HEq.trans (ZigzagAppend.Moving.app_right_heq (a := Word.single .backward)
    (b := forwardWord n) _ _ HEq.rfl i)
  rfl

lemma rebuilt_map_right (i : Fin (m + 1)) :
    HEq (((family F).zigzagMap f).app (Positions.rightVertex n m i))
      ((F.map f).app (Positions.rightVertex n m i)) := by
  dsimp only [MovingFamily.zigzagMap, MovingFamily.zigzagMapData, Positions.rightVertex]
  apply HEq.trans (ZigzagAppend.Moving.app_right_heq
    (a := Positions.leftWithMiddle n) (b := rightBoundaryWord m) _ _ ?_
    (Word.leftVertex (forwardWord m) (Word.single .backward) i))
  · dsimp only [rightBoundaryComparison, ZigzagAppend.Moving.map]
    apply HEq.trans (ZigzagAppend.Moving.app_left_heq (a := forwardWord m)
      (b := Word.single .backward) _ _ i)
    rfl
  · apply HEq.trans (ZigzagAppend.Moving.app_right_heq (b := Word.single .backward)
      _ _ ?_ (Fin.last 1))
    · exact (rightBoundaryComparison_first (rightPathMap (F.map f))
        (fun i => (F.map f).app_mem _) ((rightLeg F).app d) ((rightLeg F).app d')
        (rightLeg_mem F d) (rightLeg_mem F d') (B.map f) (F.endpoint_right_mem f)
        ((rightLeg F).naturality f).symm).symm
    · exact leftBoundaryComparison_last _ _ _ _ _ _ _ _ _

lemma rebuilt_map_app (j : Fin ((word n m).length + 1)) :
    HEq (((family F).zigzagMap f).app j) ((F.map f).app j) := by
  apply Positions.vertex_cases n m
    (P := fun j => HEq (((family F).zigzagMap f).app j) ((F.map f).app j))
  · exact ((family F).zigzagMap_first f).trans (F.first f).symm
  · exact rebuilt_map_left F f
  · exact rebuilt_map_right F f
  · exact ((family F).zigzagMap_last f).trans (F.last f).symm

lemma rebuildDiagram_eq : (family F).movingDiagram = F :=
  Zigzag.MovingDiagram.ext _ _ (rebuilt_eq F) (rebuilt_map_app F)

end SerrePositivity.EInfinity.Hammock.MiddleBackward.MovingExtract
