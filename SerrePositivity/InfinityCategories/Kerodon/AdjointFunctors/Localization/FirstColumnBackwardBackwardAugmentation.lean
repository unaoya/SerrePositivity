module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstColumnBackwardBackwardDiagram

/-!
# 元の後向き二列の二方向係数図式の augmentation

概要：元の全相対作用素と両端の表示を保って比較を図式に束ねる。
方針：元の切断関手の全自然性と底・両係数の関手則を使う。
規約：元の全圏・graph と同じ augmentation を保持する。
使われ方：DK10.3・5.7の元の対角比較。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory Opposite
private lemma natTrans_hext {C E : Type*} [Category* C] [Category* E]
    {F F' G G' : C ⥤ E} (hF : F = F') (hG : G = G')
    (α : F ⟶ G) (β : F' ⟶ G') (ha : ∀ X, HEq (α.app X) (β.app X)) : HEq α β := by
  cases hF
  cases hG
  apply heq_of_eq
  ext X
  exact eq_of_heq (ha X)
variable {I : Type v} [Category I] (D : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})
  (p : (i : I) → C.category → (D.obj i).category)
  (hp : ∀ {i j : I} (θ : i ⟶ j) (X : C.category), (D.map θ).functor.obj (p i X) = p j X)
  (A : D ⟶ (Functor.const I).obj C) (ha : ∀ i X, (A.app i).functor.obj (p i X) = X)
  (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : C.category)

def backwardBackwardAugmentation : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardDiagram D p hp w X Y ⟶
    (Functor.const I).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardData C w X Y) where
  app i := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardDataMap w (A.app i) (ha i X) (ha i Y)
  naturality i j θ := by
    have hA : A.app i = D.map θ ≫ A.app j := by
      have he := (A.naturality θ).symm
      change A.app i ≫ 𝟙 C = D.map θ ≫ A.app j at he
      exact (Category.comp_id (A.app i : D.obj i ⟶ C)).symm.trans he
    have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap (D.map θ) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap (A.app j) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap (A.app i) :=
      (congrArg (fun f : D.obj i ⟶ C => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap f) hA).symm
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardDataMap w (D.map θ) (hp θ X) (hp θ Y) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardDataMap w (A.app j) (ha j X) (ha j Y) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardDataMap w (A.app i) (ha i X) (ha i Y) ≫ 𝟙 _
    rw [Category.comp_id]
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.hom_ext _ _ hb ?_ ?_
    · refine natTrans_hext rfl ?_ _ _ ?_
      · change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap (D.map θ) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap (A.app j)).op ⋙ _ = _
        rw [hb]
        rfl
      · intro Z
        exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardLeftMap_comp_heq w (D.map θ) (A.app j) (A.app i) hA
          (p i X) (p i Y) (p j X) (p j Y) X Y (hp θ X) (ha j X) (ha i X)
          Z.unop).symm
    · refine natTrans_hext rfl ?_ _ _ ?_
      · change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap (D.map θ) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap (A.app j)) ⋙ _ = _
        rw [hb]
        rfl
      · intro Z
        exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedFunctor_comp_toCatHom_heq
          (D.map θ) (A.app j) (A.app i) hA Z.obj
          (p i Y) (p j Y) Y (hp θ Y) (ha j Y) (ha i Y)).symm
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
