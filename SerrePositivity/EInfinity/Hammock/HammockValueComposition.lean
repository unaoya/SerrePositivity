module

public import SerrePositivity.EInfinity.Hammock.HammockValue
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueAppend
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitCompositionPoints
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitPoints

/-!
# 元の全 hammock 評価の合成則

概要：元の全語の評価は元の composePoint を同じ二つの値の合成へ送る。
方針：元の全標準射の共同全射性と元の zigzag の連結の評価を使う。
規約：元の全標準射と元の単体を保持する。
使われ方：全因子列の評価と元の通常の局所化評価の照合。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Zigzag.Value
open CategoryTheory

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {W : MorphismProperty C} [W.IsMultiplicative] (L : C ⥤ D) (hL : W.IsInvertedBy L)
  {n : SimplexCategoryᵒᵖ}

lemma colimitValue_inclusion_app (X Y : C) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W w X Y).obj n) :
    (colimitValue L hL X Y).app n ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y w).app n τ) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value L hL (τ.obj 0) :=
  congrArg (fun f => f.app n τ) (graphInclusion_colimitValue L hL X Y w)

lemma colimitValue_composePoint (X Y Z : C) (p : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y).obj n)
    (q : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W Y Z).obj n) :
    (colimitValue L hL X Z).app n (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W X Y Z p q) =
      (colimitValue L hL X Y).app n p ≫ (colimitValue L hL Y Z).app n q := by
  obtain ⟨a, σ, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimit_point_surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y) n p
  obtain ⟨b, τ, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimit_point_surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W Y Z) n q
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint_inclusions W X Y Z a b σ τ
  have hv := colimitValue_inclusion_app L hL X Z (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b)
    (σ.prod' τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendFunctor.functor)
  have hp := colimitValue_inclusion_app L hL X Y a σ
  have hq := colimitValue_inclusion_app L hL Y Z b τ
  exact (congrArg ((colimitValue L hL X Z).app n) hc).trans
    (hv.trans ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.value_append L hL (σ.obj 0) (τ.obj 0)).trans
      (congrArg₂ (fun f g => f ≫ g) hp.symm hq.symm)))

end SerrePositivity.EInfinity.Hammock.Zigzag.Value
