module

public import SerrePositivity.EInfinity.Hammock.MiddleBackwardRebuildVertices
public import SerrePositivity.EInfinity.Hammock.MiddleBackwardExtractLegRecovery

/-!
# 再構成した元の zigzag の全列の回収

概要：左右の射列と三つの脚から再構成した全列は、元の同じ全列と異種等しい。
方針：元の連結の全列の成分回収を繰り返し、抽出した各隣接射へ戻す。
規約：語の向きと順序、元の全ての射を保持する。
使われ方：再構成対象と元の対象の厳密な等式。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.MiddleBackward.Extract
open CategoryTheory HomotopicalAlgebra ForwardPath

variable {C : Type u} [Category.{v} C] [ModelCategory C] {n m : ℕ} {X Y : C}

lemma rebuilt_firstColumn (S : Zigzag (weakEquivalences C) (word n m) X Y) :
    HEq ((rebuilt S).arrow (Positions.firstColumn n m)) (S.arrow (Positions.firstColumn n m)) := by
  dsimp only [rebuilt, Family.zigzagObj, family, MiddleBackward.obj, leftBoundaryBlock,
    rightBoundaryBlock, Positions.firstColumn]
  apply HEq.trans (ZigzagAppend.arrow_left_heq (b := rightBoundaryWord m) _ _ _)
  apply HEq.trans (ZigzagAppend.arrow_left_heq (b := Word.single .backward) _ _ _)
  apply HEq.trans (ZigzagAppend.arrow_left_heq (b := forwardWord n) _ _ _)
  exact leftLeg_heq S

lemma rebuilt_leftColumn (S : Zigzag (weakEquivalences C) (word n m) X Y) (i : Fin n) :
    HEq ((rebuilt S).arrow (Positions.leftColumn n m i))
      (S.arrow (Positions.leftColumn n m i)) := by
  dsimp only [rebuilt, Family.zigzagObj, family, MiddleBackward.obj, leftBoundaryBlock,
    rightBoundaryBlock, Positions.leftColumn]
  apply HEq.trans (ZigzagAppend.arrow_left_heq (b := rightBoundaryWord m) _ _ _)
  apply HEq.trans (ZigzagAppend.arrow_left_heq (b := Word.single .backward) _ _ _)
  apply HEq.trans (ZigzagAppend.arrow_right_heq (a := Word.single .backward) _ _ _)
  exact leftPath_map_succ_heq S i.val i.isLt

lemma rebuilt_middleColumn (S : Zigzag (weakEquivalences C) (word n m) X Y) :
    HEq ((rebuilt S).arrow (Positions.middleColumn n m))
      (S.arrow (Positions.middleColumn n m)) := by
  dsimp only [rebuilt, Family.zigzagObj, family, MiddleBackward.obj, leftBoundaryBlock,
    rightBoundaryBlock, Positions.middleColumn]
  apply HEq.trans (ZigzagAppend.arrow_left_heq (b := rightBoundaryWord m) _ _ _)
  apply HEq.trans (ZigzagAppend.arrow_right_heq (a := leftBoundaryWord n) _ _ _)
  exact middleLeg_heq S

lemma rebuilt_rightColumn (S : Zigzag (weakEquivalences C) (word n m) X Y) (i : Fin m) :
    HEq ((rebuilt S).arrow (Positions.rightColumn n m i))
      (S.arrow (Positions.rightColumn n m i)) := by
  dsimp only [rebuilt, Family.zigzagObj, family, MiddleBackward.obj, leftBoundaryBlock,
    rightBoundaryBlock, Positions.rightColumn]
  apply HEq.trans (ZigzagAppend.arrow_right_heq (a := Positions.leftWithMiddle n) _ _ _)
  apply HEq.trans (ZigzagAppend.arrow_left_heq (b := Word.single .backward) _ _ _)
  exact rightPath_map_succ_heq S i.val i.isLt

lemma rebuilt_lastColumn (S : Zigzag (weakEquivalences C) (word n m) X Y) :
    HEq ((rebuilt S).arrow (Positions.lastColumn n m)) (S.arrow (Positions.lastColumn n m)) := by
  dsimp only [rebuilt, Family.zigzagObj, family, MiddleBackward.obj, leftBoundaryBlock,
    rightBoundaryBlock, Positions.lastColumn]
  apply HEq.trans (ZigzagAppend.arrow_right_heq (a := Positions.leftWithMiddle n) _ _ _)
  apply HEq.trans (ZigzagAppend.arrow_right_heq (a := forwardWord m) _ _ _)
  exact rightLeg_heq S

lemma rebuilt_arrow (S : Zigzag (weakEquivalences C) (word n m) X Y)
    (j : Fin (word n m).length) : HEq ((rebuilt S).arrow j) (S.arrow j) :=
  Positions.column_cases n m (P := fun j => HEq ((rebuilt S).arrow j) (S.arrow j))
    (rebuilt_firstColumn S) (rebuilt_leftColumn S)
    (rebuilt_middleColumn S) (rebuilt_rightColumn S) (rebuilt_lastColumn S) j

lemma rebuilt_eq (S : Zigzag (weakEquivalences C) (word n m) X Y) : rebuilt S = S :=
  Zigzag.object_ext _ _ (rebuilt_vertex S) (rebuilt_arrow S)

end SerrePositivity.EInfinity.Hammock.MiddleBackward.Extract
