module

public import SerrePositivity.EInfinity.Hammock.MiddleBackwardExtractPaths

/-!
# 元の固定語の zigzag 圏から三つの脚と全ブロック図式を抽出する

概要：元の graph の全対象・全縦射から、左右射列と三つの自然な脚を抽出する。
方針：元の一列の評価図式と元の first/last の自然同型を合成する。
規約：元のモデル圏の弱同値を使用する。Family を未知の入力にしない。
使われ方：左右の置換関手と counit/unit を元の固定語の graph に適用する。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.MiddleBackward.Extract
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {n m : ℕ} {X Y : C}

def leftLeg :
    leftFunctor (W := W) (n := n) (m := m) (X := X) (Y := Y) ⋙ pathEvaluation C n 0 ⟶
      (Functor.const (Zigzag W (word n m) X Y)).obj X :=
  Zigzag.columnDiagram (Positions.firstColumn n m) (Positions.leftVertex n m 0) 0
    (Positions.first_source n m).symm (Positions.first_target n m) ≫
      Zigzag.firstEvaluationIso.hom

def middleLeg :
    rightFunctor (W := W) (n := n) (m := m) (X := X) (Y := Y) ⋙ pathEvaluation C m 0 ⟶
      leftFunctor ⋙ pathEvaluation C n (Fin.last n) :=
  Zigzag.columnDiagram (Positions.middleColumn n m) (Positions.rightVertex n m 0)
    (Positions.leftVertex n m (Fin.last n))
    (Positions.middle_source n m).symm (Positions.middle_target n m)

def rightLeg :
    (Functor.const (Zigzag W (word n m) X Y)).obj Y ⟶
      rightFunctor ⋙ pathEvaluation C m (Fin.last m) :=
  Zigzag.lastEvaluationIso.inv ≫
    Zigzag.columnDiagram (Positions.lastColumn n m) (Fin.last (word n m).length)
      (Positions.rightVertex n m (Fin.last m))
      (Positions.last_source n m).symm (Positions.last_target n m)

lemma leftLeg_mem (S : Zigzag W (word n m) X Y) : W (leftLeg.app S) :=
  W.comp_mem _ _ (Zigzag.columnDiagram_mem _ _ _ _ _ (Positions.first_direction n m) S)
    (Segment.eqToHom_mem S.first)

lemma middleLeg_mem (S : Zigzag W (word n m) X Y) : W (middleLeg.app S) :=
  Zigzag.columnDiagram_mem _ _ _ _ _ (Positions.middle_direction n m) S

lemma rightLeg_mem (S : Zigzag W (word n m) X Y) : W (rightLeg.app S) :=
  W.comp_mem _ _ (Segment.eqToHom_mem S.last.symm)
    (Zigzag.columnDiagram_mem _ _ _ _ _ (Positions.last_direction n m) S)

variable [ModelCategory C]

def family : Family (Zigzag (weakEquivalences C) (word n m) X Y) C n m X Y where
  left := leftFunctor
  right := rightFunctor
  a := leftLeg
  middle := middleLeg
  b := rightLeg
  a_mem := leftLeg_mem
  middle_mem := middleLeg_mem
  b_mem := rightLeg_mem
  left_mem f i := f.app_mem (Positions.leftVertex n m i)
  right_mem f i := f.app_mem (Positions.rightVertex n m i)

end SerrePositivity.EInfinity.Hammock.MiddleBackward.Extract
