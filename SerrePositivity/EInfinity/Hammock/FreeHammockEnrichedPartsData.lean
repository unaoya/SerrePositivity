module

public import SerrePositivity.EInfinity.Hammock.FreeHammockEnrichedParts
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedHomTransport

/-!
# 元の二つの自由部分からの関手から生成矢の像の指定への回収

概要：二つの豊穣関手と対象表示の等式から元の EnrichedFoldData を構成する。
方針：非指定生成矢の同じ一定単体の像の終域 Hom を元の対象等式で移す。
規約：共通対象の表示の等式を保持する。
使われ方：自由積の二つの元の部分による普遍性。
-/

@[expose] public section
universe u uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open CategoryTheory

variable {C : Type u} [Category.{u} C]

def unmarkedGeneratorPath (W : MorphismProperty C) (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W) :
    Quiver.Path (V := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.unmarked W))
      g.val.left g.val.right :=
  Quiver.Hom.toPath ⟨g.val.hom, g.property⟩

namespace EnrichedParts
variable {W : MorphismProperty C} {D : Type uD} [EnrichedCategory SSet.{u} D]
  (G : EnrichedParts W D)

def foldData : EnrichedFoldData W D := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory (⊤ : MorphismProperty (WideSubcategory W.paths))
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment.enrichedCategory
    (C := Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.unmarked W)))
  exact
    { obj := fun X => G.marked.obj ⟨X⟩
      marked := fun X Y => G.marked.map ⟨X⟩ ⟨Y⟩
      generator := fun g => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment.point (unmarkedGeneratorPath W g) ≫
        G.unmarked.map g.val.left g.val.right ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.homMap (G.objects g.val.left).symm (G.objects g.val.right).symm
      marked_unit := fun X => G.marked.map_id ⟨X⟩
      marked_comp := fun X Y Z => G.marked.map_comp ⟨X⟩ ⟨Y⟩ ⟨Z⟩ }

end EnrichedParts
end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
