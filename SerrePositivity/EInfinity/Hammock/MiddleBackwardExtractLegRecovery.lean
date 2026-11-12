module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardExtractFamily

/-!
# 抽出した三つの脚の元の列への回収

概要：抽出した外側の脚と中央の脚は、元の同じ backward 列と異種等しい。
方針：番号と first/last の等式による移送だけを消す。
規約：元の弱同値の列を別の代表で置き換えない。
使われ方：全体を再構成した全列の元の列への照合。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.MiddleBackward.Extract
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {n m : ℕ} {X Y : C}

lemma leftLeg_heq (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardExtractFamily.leftLeg.app S) (S.arrow (Positions.firstColumn n m)) := by
  change HEq ((eqToHom _ ≫ S.arrow (Positions.firstColumn n m) ≫ eqToHom _) ≫
    eqToHom S.first) (S.arrow (Positions.firstColumn n m))
  simp only [comp_eqToHom_heq_iff, eqToHom_comp_heq_iff]
  rfl

lemma middleLeg_heq (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardExtractFamily.middleLeg.app S) (S.arrow (Positions.middleColumn n m)) := by
  change HEq (eqToHom _ ≫ S.arrow (Positions.middleColumn n m) ≫ eqToHom _)
    (S.arrow (Positions.middleColumn n m))
  simp only [comp_eqToHom_heq_iff, eqToHom_comp_heq_iff]
  rfl

lemma rightLeg_heq (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardExtractFamily.rightLeg.app S) (S.arrow (Positions.lastColumn n m)) := by
  change HEq (eqToHom S.last.symm ≫
    (eqToHom _ ≫ S.arrow (Positions.lastColumn n m) ≫ eqToHom _))
    (S.arrow (Positions.lastColumn n m))
  simp only [comp_eqToHom_heq_iff, eqToHom_comp_heq_iff]
  rfl

end SerrePositivity.EInfinity.Hammock.MiddleBackward.Extract
