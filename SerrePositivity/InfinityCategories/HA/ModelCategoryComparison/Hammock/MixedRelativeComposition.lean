module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelativeColimitMap
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeAppendFunctor
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitCompositionPoints
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitPoints

/-!
# 異なる Hom の宇宙を持つ元の相対関手の合成保存

概要：全語の標準射で定めた元の写像が各次数の全ての合成を保つ。
方針：両変数の共同全射性と宇宙に依存しない元の連結関手の一致を使う。
規約：元の余極限と元の合成を使用する。
使われ方：cofibrant 包含と HomLift を通る元の比較の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative
open _root_.CategoryTheory
variable {C D : Type (u + 1)} [Category.{u + 1} C] [Category.{u} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  (F : LocalizerMorphism W V) {X Y Z : C} {n : SimplexCategoryᵒᵖ}

lemma graphInclusion_point {a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W a X Y).obj n) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative.colimitMap F X Y).app n ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y a).app n σ) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion V (F.functor.obj X) (F.functor.obj Y) a).app n
        (σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor F) :=
  congrArg (fun k => k.app n σ) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative.graphInclusion_colimitMap F X Y a)

lemma append_simplex {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W a X Y).obj n)
    (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W b Y Z).obj n) :
    (σ.prod' τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendFunctor.functor) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor F =
      (σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor F).prod' (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor F) ⋙
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendFunctor.functor := by
  rw [CategoryTheory.Functor.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.append_functor]
  rfl

lemma composePoint_map (p : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y).obj n) (q : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W Y Z).obj n) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative.colimitMap F X Z).app n (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W X Y Z p q) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint V (F.functor.obj X) (F.functor.obj Y) (F.functor.obj Z)
        ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative.colimitMap F X Y).app n p) ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative.colimitMap F Y Z).app n q) := by
  obtain ⟨a, σ, hp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimit_point_surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y) n p
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y a).app n σ = p at hp
  cases hp
  obtain ⟨b, τ, hq⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimit_point_surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W Y Z) n q
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W Y Z b).app n τ = q at hq
  cases hq
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint_inclusions, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative.graphInclusion_point, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative.graphInclusion_point,
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative.graphInclusion_point, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint_inclusions]
  exact congrArg (fun H =>
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion V (F.functor.obj X) (F.functor.obj Z) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b)).app n H)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative.append_simplex F σ τ)

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative
