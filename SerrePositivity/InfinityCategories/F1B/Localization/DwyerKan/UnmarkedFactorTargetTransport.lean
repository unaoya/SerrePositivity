module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedFactorTarget
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.EndpointColimit

/-!
# 元の生成矢の表示と因子の依存和の等式

概要：同じ生成矢と前後の hammock の端点移送で、依存和の元の点を同定する。
方針：Subtype の外延性と元の端点表示で帰納する。
規約：実際の W-hammock と残りの hammock の余極限の点を使う。
使われ方：切断の各幅の像の比較を単体集合の自然性へ束ねる。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FactorTarget
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) {X Y : Paths C}
  {n m : SimplexCategoryᵒᵖ}

lemma map_mk (θ : n ⟶ m) (g : Index W) (p : (left W X g.val).obj n)
    (r : (right W Y g.val).obj n) :
    (space W X Y).map θ ⟨g, p, r⟩ =
      ⟨g, (left W X g.val).map θ p, (right W Y g.val).map θ r⟩ := rfl

lemma point_ext {g g' : Index W} (hg : g.val = g'.val)
    (p : (left W X g.val).obj n) (p' : (left W X g'.val).obj n)
    (r : (right W Y g.val).obj n) (r' : (right W Y g'.val).obj n)
    (hp : (EndpointChange.colimitMap (⊤ : MorphismProperty (WideSubcategory W.paths)) rfl
      (congrArg (fun a : Quiver.Total C => (⟨a.left⟩ : WideSubcategory W.paths)) hg)).app n p = p')
    (hr : (EndpointChange.colimitMap W.paths
      (congrArg (fun a : Quiver.Total C => (show Paths C from a.right)) hg) rfl).app n r = r') :
    (⟨g, p, r⟩ : (space W X Y).obj n) = ⟨g', p', r'⟩ := by
  have hgg : g = g' := Subtype.ext hg
  cases hgg
  change p = p' at hp
  change r = r' at hr
  cases hp
  cases hr
  rfl

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FactorTarget
