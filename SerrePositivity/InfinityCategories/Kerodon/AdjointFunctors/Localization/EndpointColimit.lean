module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitGraph
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagEndpointChange

/-!
# 元の hammock 余極限と端点表示の変更

概要：端点の等式による同じ hammock 余極限の移送と元の標準射の整合を証明する。
方針：端点の等式で帰納し、元の恒等射・標準余錐の自然性を使う。
規約：同型の選択や弱比較を仮定しない。
使われ方：切断因子の元の標準射の像の一致。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EndpointColimit
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {X X' Y Y' : C}

def colimitMap (hX : X = X') (hY : Y = Y') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X' Y' :=
  eqToHom (by cases hX; cases hY; rfl)

lemma inclusion (hX : X = X') (hY : Y = Y') (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagEndpointChange.functor (W := W) (w := w) hX hY) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X' Y' w = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y w ≫ colimitMap W hX hY := by
  cases hX
  cases hY
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagEndpointChange.functor_refl]
  have hid : nerveMap (𝟭 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y)) = 𝟙 _ := by
    ext n F
    exact Functor.comp_id F
  rw [hid]
  simp only [colimitMap, eqToHom_refl, Category.id_comp, Category.comp_id]

lemma image_eq {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) (hX : X = X') (hY : Y = Y')
    {n : SimplexCategoryᵒᵖ} (S : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W a X Y).obj n) (T : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W b X' Y').obj n)
    (hST : S ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagEndpointChange.functor hX hY = T) :
    (colimitMap W hX hY).app n ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y a).app n S) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X' Y' b).app n T := by
  have hι := congrArg (fun g => g.app n S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion_naturality W X Y f)
  have he := congrArg (fun g => g.app n (S ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f)) (inclusion W hX hY b)
  have ht := congrArg (fun z => (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X' Y' b).app n z) hST
  exact (congrArg (fun z => (colimitMap W hX hY).app n z) hι.symm).trans
    (he.symm.trans ht)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EndpointColimit
