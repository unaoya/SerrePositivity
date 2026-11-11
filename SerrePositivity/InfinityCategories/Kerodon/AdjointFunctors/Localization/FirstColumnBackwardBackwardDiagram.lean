module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstColumnBackwardBackwardCoefficientCoherence
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedCoefficientCoherence

/-!
# 後向き二列の元の底と両係数の図式

概要：任意の相対圏図式と固定対象の表示から二方向係数図式を作る。
方針：指定 Hom と残りの zigzag の元の恒等・合成則を使う。
規約：元の全相対作用素と端点移送を保持する。
使われ方：自由解像の左対角比較への帰納。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v wO
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
variable {I : Type v} [Category I] (D : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {O : Type wO}
  (p : (i : I) → O → (D.obj i).category)
  (hp : ∀ {i j : I} (θ : i ⟶ j) (X : O), (D.map θ).functor.obj (p i X) = p j X)
  (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : O)

def backwardBackwardDiagram : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.Data.{u} where
  obj i := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardData (D.obj i) w (p i X) (p i Y)
  map θ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardDataMap w (D.map θ) (hp θ X) (hp θ Y)
  map_id i := by
    have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap (D.map (𝟙 i)) = 𝟭 _ :=
      congrArg (fun f : D.obj i ⟶ D.obj i => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap f) (D.map_id i)
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.hom_ext _ _ hb ?_ ?_
    · refine natTrans_hext rfl ?_ _ _ ?_
      · change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap (D.map (𝟙 i))).op ⋙ _ = _
        rw [hb]
        rfl
      · intro Z
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardLeftMap_id_heq w (D.map (𝟙 i)) (D.map_id i)
          (p i X) (p i Y) (hp (𝟙 i) X) Z.unop
    · refine natTrans_hext rfl ?_ _ _ ?_
      · change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap (D.map (𝟙 i)) ⋙ _ = _
        rw [hb]
        rfl
      · intro Z
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedFunctor_id_toCatHom_heq (D.map (𝟙 i)) (D.map_id i)
          Z.obj (p i Y) (hp (𝟙 i) Y)
  map_comp {i j k} θ φ := by
    have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap (D.map (θ ≫ φ)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap (D.map θ) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap (D.map φ) :=
      congrArg (fun f : D.obj i ⟶ D.obj k => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap f) (D.map_comp θ φ)
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.hom_ext _ _ hb ?_ ?_
    · refine natTrans_hext rfl ?_ _ _ ?_
      · change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap (D.map (θ ≫ φ))).op ⋙ _ = _
        rw [hb]
        rfl
      · intro Z
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardLeftMap_comp_heq w (D.map θ) (D.map φ) (D.map (θ ≫ φ))
          (D.map_comp θ φ) (p i X) (p i Y) (p j X) (p j Y) (p k X) (p k Y)
          (hp θ X) (hp φ X) (hp (θ ≫ φ) X) Z.unop
    · refine natTrans_hext rfl ?_ _ _ ?_
      · change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap (D.map (θ ≫ φ)) ⋙ _ = _
        rw [hb]
        rfl
      · intro Z
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedFunctor_comp_toCatHom_heq
          (D.map θ) (D.map φ) (D.map (θ ≫ φ)) (D.map_comp θ φ) Z.obj
          (p i Y) (p j Y) (p k Y) (hp θ Y) (hp φ Y) (hp (θ ≫ φ) Y)
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
