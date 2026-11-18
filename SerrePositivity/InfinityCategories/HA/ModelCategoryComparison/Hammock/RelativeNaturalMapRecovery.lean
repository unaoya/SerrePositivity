module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalGraphHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalWordRows
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RelativeCompositionPoints
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.PointActions
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitArrowMap

/-!
# 比較ホモトピーの両端と元の前後合成の一致

概要：二つの行の像を元の相対写像と η の前後合成へ厳密に回収する。
方針：元の標準射で合成を計算し、外側の恒等列を単位則で消す。
規約：既存の colimitMap・arrowMap・合成を使う。
使われ方：全語のホモトピーの両端の同定。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RelativeNatural
open _root_.CategoryTheory

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  {F G : LocalizerMorphism W V} (η : F.functor ⟶ G.functor) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : C)

lemma beforeMap_recovery : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeMap η w X Y = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y w ≫
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitMap F X Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap (F.functor.obj X) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap V (η.app Y)) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro σ
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion V (F.functor.obj X) (G.functor.obj Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordFunctor.obj w)).app n
    (σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeFunctor η w X Y) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint V _ _ _
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitMap F X Y).app n ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y w).app n σ))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint V (η.app Y) n)
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.graphInclusion_point]
  have h : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion V (F.functor.obj X) (G.functor.obj Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordFunctor.obj w)).app n
      (σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeFunctor η w X Y) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint V _ _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint V (𝟙 (F.functor.obj X)) n)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint V _ _ _
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion V (F.functor.obj X) (F.functor.obj Y) w).app n
            (σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint V (η.app Y) n)) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint_inclusions, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint_inclusions]
    rfl
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint_identity_left] at h
  exact h

lemma afterMap_recovery : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterMap η w X Y = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y w ≫
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitMap G X Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap V (η.app X)) (G.functor.obj Y) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro σ
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion V (F.functor.obj X) (G.functor.obj Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordFunctor.obj w)).app n
    (σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterFunctor η w X Y) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint V _ _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint V (η.app X) n)
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitMap G X Y).app n ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y w).app n σ))
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.graphInclusion_point]
  have h : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion V (F.functor.obj X) (G.functor.obj Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordFunctor.obj w)).app n
      (σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterFunctor η w X Y) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint V _ _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint V (η.app X) n)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint V _ _ _
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion V (G.functor.obj X) (G.functor.obj Y) w).app n
            (σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor G)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint V (𝟙 (G.functor.obj Y)) n)) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint_inclusions, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint_inclusions]
    rfl
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint_identity_right] at h
  exact h

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RelativeNatural
