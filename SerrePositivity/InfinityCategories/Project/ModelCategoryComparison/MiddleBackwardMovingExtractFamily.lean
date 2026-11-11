module

public import SerrePositivity.EInfinity.Hammock.MiddleBackwardMovingExtractPaths
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyReplacementComparisons

/-!
# 元の動く局所図式から三つの脚と MovingFamily を抽出する

概要：元の局所図式の各列と端点関手から、実際の左右ブロック図式を得る。
方針：列の自然変換と端点の自然同型を合成し、全縦弱同値を回収する。
規約：端点関手を定数と仮定せず、追加の Family 入力も要求しない。
使われ方：任意の前後の語の中の中央 backward 列への左右置換の適用。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingExtractFamily
open CategoryTheory HomotopicalAlgebra

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative] {n m : ℕ} {A B : D ⥤ C}
  (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) A B)

def leftLeg :
    _root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.MovingExtract.leftFunctor F ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pathEvaluation C n 0 ⟶
      A :=
  F.columnDiagram (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.firstColumn n m) (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.leftVertex n m 0) 0
    (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.first_source n m).symm (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.first_target n m) ≫
      F.firstEvaluationIso.hom

def middleLeg :
    _root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.MovingExtract.rightFunctor F ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pathEvaluation C m 0 ⟶
      _root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.MovingExtract.leftFunctor F ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pathEvaluation C n (Fin.last n) :=
  F.columnDiagram (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.middleColumn n m) (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.rightVertex n m 0)
    (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.leftVertex n m (Fin.last n))
    (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.middle_source n m).symm (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.middle_target n m)

def rightLeg :
    B ⟶
      _root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.MovingExtract.rightFunctor F ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pathEvaluation C m (Fin.last m) :=
  F.lastEvaluationIso.inv ≫
    F.columnDiagram (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.lastColumn n m) (Fin.last (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m).length)
      (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.rightVertex n m (Fin.last m))
      (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.last_source n m).symm (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.last_target n m)

lemma leftLeg_mem (d : D) : W ((leftLeg F).app d) :=
  W.comp_mem _ _ (F.columnDiagram_mem _ _ _ _ _ (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.first_direction n m) d)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.eqToHom_mem (F.obj d).first)

lemma middleLeg_mem (d : D) : W ((middleLeg F).app d) :=
  F.columnDiagram_mem _ _ _ _ _ (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.middle_direction n m) d

lemma rightLeg_mem (d : D) : W ((rightLeg F).app d) :=
  W.comp_mem _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.eqToHom_mem (F.obj d).last.symm)
    (F.columnDiagram_mem _ _ _ _ _ (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.last_direction n m) d)

variable [ModelCategory C]

def family (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) A B) :
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MovingFamily D C n m A B where
  left := _root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.MovingExtract.leftFunctor F
  right := _root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.MovingExtract.rightFunctor F
  a := leftLeg F
  middle := middleLeg F
  b := rightLeg F
  a_mem := leftLeg_mem F
  middle_mem := middleLeg_mem F
  b_mem := rightLeg_mem F
  left_mem f i := (F.map f).app_mem (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.leftVertex n m i)
  right_mem f i := (F.map f).app_mem (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.rightVertex n m i)
  endpoint_left_mem := F.endpoint_left_mem
  endpoint_right_mem := F.endpoint_right_mem

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingExtractFamily
