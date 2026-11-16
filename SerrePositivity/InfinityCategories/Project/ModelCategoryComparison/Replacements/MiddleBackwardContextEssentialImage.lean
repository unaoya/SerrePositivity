module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.MiddleBackwardContextErasure
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityPreimageRecovery
public import Mathlib.CategoryTheory.EssentialImage

/-!
# 元の削除語の挿入の本質像への右置換の持ち上げ

概要：元の右置換の各対象の実際の前像を構成し、右置換関手を持ち上げる。
方針：元の中央恒等列と既存の対象の像の特徴付けを使う。
規約：未知の本質像所属を入力にしない。元の eraseInclusion を使う。
使われ方：元の unit を第二の包含の比較へ戻す。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextEssentialImage
open CategoryTheory _root_.HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (n m : ℕ) (X Y : C)

lemma rightReplacement_identityOutside (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextTrivialCofibration.Objects a b n m X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityOutside (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextErasure.wordMap a b n m) ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextRightReplacement.rightReplacement a b n m X Y).obj S) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.identityOutside_erase_iff _ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.middleColumn a b n m)).2
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightReplacement_identity a b n m X Y S)

def preimageObj (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextTrivialCofibration.Objects a b n m X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextErasure.sourceWord a b n m) X Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityPreimageObjects.obj (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextErasure.wordMap a b n m) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion_injective _ _)
    ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextRightReplacement.rightReplacement a b n m X Y).obj S)
    (rightReplacement_identityOutside a b n m X Y S)

lemma originalFunctor_obj_preimage (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextTrivialCofibration.Objects a b n m X Y) :
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextErasure.originalFunctor a b n m X Y).obj (preimageObj a b n m X Y S) =
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextRightReplacement.rightReplacement a b n m X Y).obj S :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityPreimage.obj_image (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextErasure.wordMap a b n m) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion_injective _ _) _
    (rightReplacement_identityOutside a b n m X Y S)

lemma rightReplacement_essImage (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextTrivialCofibration.Objects a b n m X Y) :
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextErasure.originalFunctor a b n m X Y).essImage
      ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextRightReplacement.rightReplacement a b n m X Y).obj S) :=
  ⟨preimageObj a b n m X Y S, ⟨eqToIso (originalFunctor_obj_preimage a b n m X Y S)⟩⟩

def rightReplacement : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextTrivialCofibration.Objects a b n m X Y ⥤
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextErasure.sourceWord a b n m) X Y :=
  Functor.essImage.liftFunctor (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextRightReplacement.rightReplacement a b n m X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextErasure.originalFunctor a b n m X Y) (rightReplacement_essImage a b n m X Y)

def rightReplacementCompIso : rightReplacement a b n m X Y ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextErasure.originalFunctor a b n m X Y ≅
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextRightReplacement.rightReplacement a b n m X Y :=
  Functor.essImage.liftFunctorCompIso (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextRightReplacement.rightReplacement a b n m X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextErasure.originalFunctor a b n m X Y) (rightReplacement_essImage a b n m X Y)

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextEssentialImage
