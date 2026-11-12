module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertion
public import Mathlib.CategoryTheory.EssentialImage

/-!
# 元の右置換が中央恒等列の挿入の本質像に入ること

概要：元の右置換対象から恒等列だけを省き、元の挿入の実際の前像を構成する。
方針：左右の同じブロックを貼り、insertBetween の WordAction の厳密な対象同定を使う。
規約：本質像への所属を入力仮定にしない。
使われ方：全忠実な元の挿入を通して右置換関手を持ち上げる。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardRightEssentialImage
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C] {n m : ℕ} {X Y : C}

def preimageObj (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialCofibration.Objects
    (C := C) (n := n) (m := m) (X := X) (Y := Y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertion.sourceWord n m) X Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryBlock (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialRightReplacement.sourceFamily.left.obj S)
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialRightReplacement.sourceFamily.a.app S) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialRightReplacement.sourceFamily.a_mem S))
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pushoutRightBoundary (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialRightReplacement.sourceFamily.pushoutInputs.obj S)
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialRightReplacement.sourceFamily_middle_trivial S)
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialRightReplacement.sourceFamily.b.app S) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialRightReplacement.sourceFamily.b_mem S))

lemma originalFunctor_obj_preimage (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialCofibration.Objects
    (C := C) (n := n) (m := m) (X := X) (Y := Y)) :
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertion.originalFunctor.obj (preimageObj S) = _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialRightReplacement.rightReplacement.obj S := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertion.originalFunctor, preimageObj, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord n) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord m) .backward)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj _ _) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.action_obj_eq]
  rfl

lemma rightReplacement_essImage (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialCofibration.Objects
    (C := C) (n := n) (m := m) (X := X) (Y := Y)) :
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertion.originalFunctor (C := C) (n := n) (m := m) (X := X) (Y := Y)).essImage
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialRightReplacement.rightReplacement.obj S) :=
  ⟨preimageObj S, ⟨eqToIso (originalFunctor_obj_preimage S)⟩⟩

def rightReplacement : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialCofibration.Objects
    (C := C) (n := n) (m := m) (X := X) (Y := Y) ⥤
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertion.sourceWord n m) X Y :=
  Functor.essImage.liftFunctor _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialRightReplacement.rightReplacement _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertion.originalFunctor
    rightReplacement_essImage

def rightReplacementCompIso : rightReplacement (C := C) (n := n) (m := m) (X := X) (Y := Y) ⋙
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertion.originalFunctor ≅ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialRightReplacement.rightReplacement :=
  Functor.essImage.liftFunctorCompIso _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialRightReplacement.rightReplacement _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertion.originalFunctor
    rightReplacement_essImage

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardRightEssentialImage
