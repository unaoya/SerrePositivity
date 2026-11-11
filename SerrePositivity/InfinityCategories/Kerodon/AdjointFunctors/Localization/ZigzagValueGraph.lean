module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueMaps

/-!
# 元の各 hammock graph から定数 Hom への評価

概要：全縦射で不変な元の zigzag の値は、全単体作用素と可換な評価を与える。
方針：元の各射列の先頭の値を使い、任意の行への元の縦射で自然性を証明する。
規約：全体を同じ宇宙に置く。空語・幅零を含む。
使われ方：元の全語の余極限から通常の局所化 Hom への右比較。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueGraph
open CategoryTheory

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {W : MorphismProperty C} [W.IsMultiplicative] (L : C ⥤ D) (hL : W.IsInvertedBy L)
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}

lemma rowValue_eq {n : SimplexCategoryᵒᵖ} (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W w X Y).obj n)
    (k : Fin (n.unop.len + 1)) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value L hL (τ.obj k) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value L hL (τ.obj 0) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.value_eq L hL (τ.map (homOfLE (Fin.zero_le k)))).symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.rowValue_eq export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueGraph (rowValue_eq)


def graphMap : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W w X Y ⟶ (Functor.const SimplexCategoryᵒᵖ).obj (L.obj X ⟶ L.obj Y) where
  app _ := ↾fun τ => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value L hL (τ.obj 0)
  naturality n m θ := by
    apply ConcreteCategory.hom_ext
    intro τ
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value L hL (τ.obj (θ.unop.toOrderHom 0)) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value L hL (τ.obj 0)
    exact rowValue_eq L hL τ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.graphMap export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueGraph (graphMap)


lemma graphMap_app {n : SimplexCategoryᵒᵖ} (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W w X Y).obj n) :
    (graphMap L hL).app n τ = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value L hL (τ.obj 0) := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.graphMap_app export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueGraph (graphMap_app)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueGraph
