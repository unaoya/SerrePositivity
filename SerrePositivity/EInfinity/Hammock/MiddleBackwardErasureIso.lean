module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertionComparison
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordInsertBetweenRange
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordFactorization

/-!
# 中央恒等列の挿入と元の eraseInclusion の照合

概要：元の同じ列の像により、挿入の始域を元の削除語と同型にする。
方針：単射の列の像が共に追加列の補集合であることから、両向きの因子分解を得る。
規約：語の長さだけで同定せず、元の二つの包含との合成を厳密に回収する。
使われ方：元の削除語の graph の標準射の弱同値性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.MiddleBackward.IdentityInsertion
open CategoryTheory ForwardPath

variable (n m : ℕ)

def toErasedData :
    {f : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertion.sourceWord n m ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.erase (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) (Positions.middleColumn n m) //
      f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) (Positions.middleColumn n m) = _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertion.wordMap n m} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.factorEmbedding _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion_injective _ _) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertion.wordMap n m) (by
    change Set.range (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord n)
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord m) .backward).orderHom ⊆ _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion_range, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween_range]
    rfl)

def fromErasedData :
    {f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.erase (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) (Positions.middleColumn n m) ⟶ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertion.sourceWord n m //
      f ≫ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertion.wordMap n m = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) (Positions.middleColumn n m)} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.factorEmbedding (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertion.wordMap n m) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween_injective _ _ _) _ (by
    change Set.range (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) (Positions.middleColumn n m)).orderHom ⊆
      Set.range (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord n) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord m) .backward).orderHom
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion_range, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween_range]
    rfl)

def eraseIso : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertion.sourceWord n m ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.erase (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) (Positions.middleColumn n m) where
  hom := (toErasedData n m).val
  inv := (fromErasedData n m).val
  hom_inv_id := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.hom_ext
    intro i
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween_injective (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord n) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord m) .backward
    have h : ((toErasedData n m).val ≫ (fromErasedData n m).val) ≫ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertion.wordMap n m = _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertion.wordMap n m := by
      rw [Category.assoc, (fromErasedData n m).property, (toErasedData n m).property]
    exact congrArg (fun f => f.orderHom i) h
  inv_hom_id := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.hom_ext
    intro i
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion_injective (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) (Positions.middleColumn n m)
    have h : ((fromErasedData n m).val ≫ (toErasedData n m).val) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) (Positions.middleColumn n m) =
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) (Positions.middleColumn n m) := by
      rw [Category.assoc, (toErasedData n m).property, (fromErasedData n m).property]
    exact congrArg (fun f => f.orderHom i) h

lemma eraseIso_hom_fac : (eraseIso n m).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) (Positions.middleColumn n m) = _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertion.wordMap n m :=
  (toErasedData n m).property

end SerrePositivity.EInfinity.Hammock.MiddleBackward.IdentityInsertion
