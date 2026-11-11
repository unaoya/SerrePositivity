module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectWordDiagram
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram

/-!
# 固定対象の相対圏の図式から元の zigzag 圏への augmentation

概要：対象表示を戻す元の相対 augmentation は、全語・全作用素で自然な比較を与える。
方針：元の相対自然性を固定端点の関手の合成・同定へ移す。
規約：元の対象の等式と元の全縦射を保持する。
使われ方：自由解像の hammock 図式の元の hammock への左比較。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u uI vI
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {I : Type uI} [Category.{vI} I] (D : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})
  (p : (i : I) → C.category → (D.obj i).category)
  (hp : ∀ {i j : I} (θ : i ⟶ j) (X : C.category), (D.map θ).functor.obj (p i X) = p j X)
  (A : D ⟶ (Functor.const I).obj C)
  (ha : ∀ i X, (A.app i).functor.obj (p i X) = X)

def categoryAugmentation (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : C.category) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectZigzagDiagram.zigzagDiagram D p hp w X Y ⟶
    (Functor.const I).obj (Cat.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag C.weakEquivalences w X Y)) where
  app i := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor (A.app i) (ha i X) (ha i Y)).toCatHom
  naturality i j θ := by
    apply Cat.Hom.ext
    have h := congrArg (fun F : D.obj i ⟶ C => F.functor) (A.naturality θ)
    change (D.map θ).functor ⋙ (A.app j).functor = (A.app i).functor ⋙ 𝟭 _ at h
    have h' : ((D.map θ).comp (A.app j)).functor = (A.app i).functor := by
      change (D.map θ).functor ⋙ (A.app j).functor = (A.app i).functor
      simpa only [CategoryTheory.Functor.comp_id] using h
    have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor_comp (D.map θ) (A.app j)
      (hp θ X) (hp θ Y) (ha j X) (ha j Y) (w := w)).symm.trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor_congr h'
          ((congrArg (A.app j).functor.obj (hp θ X)).trans (ha j X))
          ((congrArg (A.app j).functor.obj (hp θ Y)).trans (ha j Y)) (ha i X) (ha i Y))
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor (D.map θ) (hp θ X) (hp θ Y) ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor (A.app j) (ha j X) (ha j Y) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor (A.app i) (ha i X) (ha i Y) ⋙ 𝟭 _
    rw [CategoryTheory.Functor.comp_id]
    exact he

def categoryWordAugmentation (X Y : C.category) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectWordDiagram.categoryWordDiagram D p hp X Y ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.categoryDiagram C.weakEquivalences X Y ⋙ Functor.const I where
  app w := categoryAugmentation D C p hp A ha w X Y
  naturality _ _ f := by
    apply NatTrans.ext
    funext i
    apply Cat.Hom.ext
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordAction_fixedFunctor_eq (A.app i) (ha i X) (ha i Y) f).symm

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
