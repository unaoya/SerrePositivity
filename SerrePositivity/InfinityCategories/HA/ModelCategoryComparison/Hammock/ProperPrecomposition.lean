module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ProperSubsetImages

/-!
# 元の列の交わりを保つ語関手による proper 性の保存

概要：単射と元の列の像の交わりを保つ語関手による前合成は proper 性を保つ。
方針：単射の像の部分語表示で、元の二つの交わりの像を比較する。
規約：前合成の交わりの保存は明示条件であり、任意の語関手では仮定しない。
使われ方：分数計算の padding・forward 部分語による元の graph 図式。
-/

@[expose] public section
universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
open _root_.CategoryTheory

lemma _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ProperDiagram.precomp {F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{w}} (hF : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ProperDiagram F) (P : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word)
    (hm : ∀ {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b), Function.Injective f.orderHom →
      Function.Injective (P.map f).orderHom)
    (hi : ∀ {a b c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ c) (g : b ⟶ c),
      Function.Injective f.orderHom → Function.Injective g.orderHom →
      Set.range (P.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionInclusion f g)).orderHom =
        Set.range (P.map f).orderHom ∩ Set.range (P.map g).orderHom) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ProperDiagram (P ⋙ F) where
  map_mono f hf := hF.map_mono (P.map f) (hm f hf)
  intersection_range f g hf hg := by
    change Subfunctor.range (F.map (P.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionInclusion f g))) =
      Subfunctor.range (F.map (P.map f)) ⊓ Subfunctor.range (F.map (P.map g))
    rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.range_eq_subsetImage F _ _ (hm _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionInclusion_injective f g)),
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.range_eq_subsetImage F _ _ (hm f hf), _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.range_eq_subsetImage F _ _ (hm g hg)]
    have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.columnImage (P.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionInclusion f g)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.columnImage (P.map f) ⊓ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.columnImage (P.map g) := by
      apply Finset.coe_injective
      rw [Finset.inf_eq_inter, Finset.coe_inter, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.coe_columnImage,
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.coe_columnImage, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.coe_columnImage]
      exact hi f g hf hg
    rw [hc]
    exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.subsetImage_inf F _ hF _ _

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
