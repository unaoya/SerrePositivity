module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MarkedValueSpineDescentRecovery
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LocalizationValue
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueComparison

/-!
# 元の指定因子の評価と同じ局所化評価の一致

概要：指定因子を自由 groupoid へ評価して延長した値は元の局所化評価と一致する。
方針：全語の標準射上で元の関手の可換性による zigzag 評価の比較を使う。
規約：元の指定部分の包含と元の Q を保持する。
使われ方：元の全因子列の評価と右比較射の照合。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) (X Y : Paths C)

def nativeValueHomMap : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueHom W X Y ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj (W.paths.Q.obj X ⟶ W.paths.Q.obj Y) :=
  (Functor.const SimplexCategoryᵒᵖ).map
    (↾fun p => (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.markedValueDescent W W.paths.Q W.paths.Q_inverts).map p)

lemma nativeValue_localizationValue :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.inclusion W X Y ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.localizationValue W.paths X Y =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeValue W X Y ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.nativeValueHomMap W X Y := by
  apply colimit.hom_ext
  intro w
  change _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeInclusion W X Y w ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.inclusion W X Y ≫
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.localizationValue W.paths X Y = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeInclusion W X Y w ≫
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Zigzag.Value.colimitValue (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeFreeEvaluation W)
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeFreeEvaluation_inverts_top W) ⟨X⟩ ⟨Y⟩ ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.nativeValueHomMap W X Y
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeInclusion_inclusion, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.graphInclusion_localizationValue]
  change nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedZigzagLift.inclusion W.paths)) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueGraph.graphMap W.paths.Q W.paths.Q_inverts =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion (⊤ : MorphismProperty (WideSubcategory W.paths)) ⟨X⟩ ⟨Y⟩ w ≫
        _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Zigzag.Value.colimitValue (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeFreeEvaluation W)
          (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeFreeEvaluation_inverts_top W) ⟨X⟩ ⟨Y⟩ ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.nativeValueHomMap W X Y
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Zigzag.Value.graphInclusion_colimitValue]
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro τ
  exact eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.value_comparison (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedZigzagLift.inclusion W.paths)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeFreeEvaluation W) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeFreeEvaluation_inverts_top W)
    W.paths.Q W.paths.Q_inverts (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.markedValueDescent W W.paths.Q W.paths.Q_inverts)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.nativeFreeEvaluation_descent W W.paths.Q W.paths.Q_inverts) (τ.obj 0))

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
