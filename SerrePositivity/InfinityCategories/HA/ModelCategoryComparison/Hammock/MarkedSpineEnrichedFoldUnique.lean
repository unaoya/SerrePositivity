module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MarkedSpineEnrichedFoldMap

/-!
# 元の全因子列からの豊穣拡張の単体写像の一意性

概要：指定因子と非指定生成矢の像で元の全 Hom の単体写像は一意に決まる。
方針：元の次数ごとの拡張の一意性を同じ全次数・全点で適用する。
規約：元の明示的な合成を保存する写像を比較する。
使われ方：自由積の豊穣普遍性の存在と一意性。
-/

@[expose] public section
universe u uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
namespace EnrichedFoldData
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{u} C] {W : MorphismProperty C}
  {D : Type uD} [EnrichedCategory SSet.{u} D] (F : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.EnrichedFoldData W D)

lemma foldMap_unique (H : ∀ X Y, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.space W Y X ⟶ F.obj X ⟶[SSet.{u}] F.obj Y)
    (hm : ∀ X Y, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.nilMap W Y X ≫ H X Y = F.marked X Y)
    (hg : ∀ g, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.generatorMap W g ≫ H g.val.left g.val.right = F.generator g)
    (hc : ∀ X Y Z, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.composition W X Y Z ≫ H X Z =
      (H X Y ⊗ₘ H Y Z) ≫ eComp SSet.{u} (F.obj X) (F.obj Y) (F.obj Z))
    (X Y : Paths C) : H X Y = F.foldMap X Y := by
  ext n t
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedDegreeCategory.category (D := D) n
  exact (F.degreeData n).fold_unique (fun {X Y} s => (H X Y).app n s)
    (fun {X Y} p => congrArg (fun k => k.app n p) (hm X Y))
    (fun g => congrArg (fun k => k.app n PUnit.unit) (hg g))
    (fun {X Y Z} s t => congrArg (fun k => k.app n (s, t)) (hc X Y Z)) t

lemma existsUnique_foldMap :
    ∃! H : ∀ X Y, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.space W Y X ⟶ F.obj X ⟶[SSet.{u}] F.obj Y,
      (∀ X Y, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.nilMap W Y X ≫ H X Y = F.marked X Y) ∧
      (∀ g, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.generatorMap W g ≫ H g.val.left g.val.right = F.generator g) ∧
      (∀ X, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.unitMap W X ≫ H X X = eId SSet.{u} (F.obj X)) ∧
      (∀ X Y Z, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.composition W X Y Z ≫ H X Z =
        (H X Y ⊗ₘ H Y Z) ≫ eComp SSet.{u} (F.obj X) (F.obj Y) (F.obj Z)) := by
  refine ⟨F.foldMap, ⟨F.foldMap_marked, F.foldMap_generator, F.foldMap_unit, F.foldMap_comp⟩, ?_⟩
  intro H hH
  funext X Y
  exact F.foldMap_unique H hH.1 hH.2.1 hH.2.2.2 X Y

end EnrichedFoldData
end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
