module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.ThreeArrowPaddingSpan
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization

/-!
# 元の padding の二配置の nerve の比較ホモトピー

概要：元の中間配置からの二つの自然変換が nerve のホモトピーを与える。
方針：全単体で定義された元の nerve ホモトピーを二つの自然変換へ適用する。
規約：元の nerve の Kan 性や単体集合のモデル構造は要求しない。
使われ方：anodyne 反転後に外側と内側の配置の比較を同じ射へ移す。
-/

@[expose] public section
universe u v uH vH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory HomotopicalAlgebra
open _root_.SerrePositivity.SimplicialModel

variable {C : Type u} [Category.{v} C] [ModelCategory C] {X Y : C}

def toOuterHomotopy : SSet.Homotopy (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.middleFunctor (X := X) (Y := Y)))
    (nerveMap _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.outerFunctor) := NerveHomotopy.homotopy _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.toOuterNat

def toInnerHomotopy : SSet.Homotopy (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.middleFunctor (X := X) (Y := Y)))
    (nerveMap _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.innerFunctor) := NerveHomotopy.homotopy _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.toInnerNat

lemma outer_inner_image_eq {H : Type uH} [Category.{vH} H] (L : SSet.{max u v} ⥤ H)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    L.map (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.outerFunctor (X := X) (Y := Y))) = L.map (nerveMap _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.innerFunctor) :=
  (AnodyneHomotopy.map_homotopy_eq L hL toOuterHomotopy).symm.trans
    (AnodyneHomotopy.map_homotopy_eq L hL toInnerHomotopy)

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
