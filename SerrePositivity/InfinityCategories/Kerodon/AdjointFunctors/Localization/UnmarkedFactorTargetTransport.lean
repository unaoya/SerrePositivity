module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EndpointColimit

/-!
# 元の生成矢の表示と因子の依存和の等式

概要：同じ生成矢と前後の hammock の端点移送で、依存和の元の点を同定する。
方針：Subtype の外延性と元の端点表示で帰納する。
規約：実際の W-hammock と残りの hammock の余極限の点を使う。
使われ方：切断の各幅の像の比較を単体集合の自然性へ束ねる。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTargetTransport
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) {X Y : Paths C}
  {n m : SimplexCategoryᵒᵖ}

lemma map_mk (θ : n ⟶ m) (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W) (p : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.left W X g.val).obj n)
    (r : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.right W Y g.val).obj n) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.space W X Y).map θ ⟨g, p, r⟩ =
      ⟨g, (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.left W X g.val).map θ p, (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.right W Y g.val).map θ r⟩ := rfl

lemma point_ext {g g' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W} (hg : g.val = g'.val)
    (p : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.left W X g.val).obj n) (p' : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.left W X g'.val).obj n)
    (r : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.right W Y g.val).obj n) (r' : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.right W Y g'.val).obj n)
    (hp : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EndpointColimit.colimitMap (⊤ : MorphismProperty (WideSubcategory W.paths)) rfl
      (congrArg (fun a : Quiver.Total C => (⟨a.left⟩ : WideSubcategory W.paths)) hg)).app n p = p')
    (hr : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EndpointColimit.colimitMap W.paths
      (congrArg (fun a : Quiver.Total C => (show Paths C from a.right)) hg) rfl).app n r = r') :
    (⟨g, p, r⟩ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.space W X Y).obj n) = ⟨g', p', r'⟩ := by
  have hgg : g = g' := Subtype.ext hg
  cases hgg
  change p = p' at hp
  change r = r' at hr
  cases hp
  cases hr
  rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTargetTransport
