module

public import SerrePositivity.EInfinity.Hammock.FreeHammockEnrichedFold

/-!
# 元の自由圏の hammock の豊穣拡張の存在と一意性

概要：任意の豊穣目標への元の単体写像は指定部分と非指定生成矢の像で一意に決まる。
方針：元の貼り戻しを前合成し、全因子列の普遍性と元の両逆を使う。
規約：元の hammock の単位と合成そのものを保存する。
使われ方：DK 命題3.2の元の自由積の豊穣普遍性。
-/

@[expose] public section
universe u uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
namespace EnrichedFoldData
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{u} C] {W : MorphismProperty C}
  {D : Type uD} [EnrichedCategory SSet.{u} D] (F : EnrichedFoldData W D)

lemma hammockFoldMap_unique
    (H : ∀ X Y, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y ⟶ F.obj X ⟶[SSet.{u}] F.obj Y)
    (hm : ∀ X Y, AllMarked.inclusion W X Y ≫ H X Y = F.marked X Y)
    (hg : ∀ g, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W.paths g.val.hom.toPath ≫ H g.val.left g.val.right = F.generator g)
    (hc : ∀ X Y Z, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition W.paths X Y Z ≫ H X Z =
      (H X Y ⊗ₘ H Y Z) ≫ eComp SSet.{u} (F.obj X) (F.obj Y) (F.obj Z))
    (X Y : Paths C) : H X Y = F.hammockFoldMap X Y := by
  have he := F.foldMap_unique (fun X Y => gluing W Y X ≫ H X Y)
    (fun X Y => by rw [← Category.assoc, nilMap_gluing]; exact hm X Y)
    (fun g => by rw [← Category.assoc, generatorMap_gluing]; exact hg g)
    (fun X Y Z => by
      rw [← Category.assoc, composition_gluing, Category.assoc, hc,
        ← Category.assoc, tensorHom_comp_tensorHom]) X Y
  calc
    H X Y = extraction W Y X ≫ (gluing W Y X ≫ H X Y) := by
      rw [← Category.assoc, extraction_gluing, Category.id_comp]
    _ = F.hammockFoldMap X Y := congrArg (fun k => extraction W Y X ≫ k) he

lemma existsUnique_hammockFoldMap :
    ∃! H : ∀ X Y, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y ⟶ F.obj X ⟶[SSet.{u}] F.obj Y,
      (∀ X Y, AllMarked.inclusion W X Y ≫ H X Y = F.marked X Y) ∧
      (∀ g, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W.paths g.val.hom.toPath ≫ H g.val.left g.val.right = F.generator g) ∧
      (∀ X, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit W.paths X ≫ H X X = eId SSet.{u} (F.obj X)) ∧
      (∀ X Y Z, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition W.paths X Y Z ≫ H X Z =
        (H X Y ⊗ₘ H Y Z) ≫ eComp SSet.{u} (F.obj X) (F.obj Y) (F.obj Z)) := by
  refine ⟨F.hammockFoldMap,
    ⟨F.hammockFoldMap_marked, F.hammockFoldMap_generator, F.hammockFoldMap_unit,
      F.hammockFoldMap_comp⟩, ?_⟩
  intro H hH
  funext X Y
  exact F.hammockFoldMap_unique H hH.1 hH.2.1 hH.2.2.2 X Y

end EnrichedFoldData
end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
