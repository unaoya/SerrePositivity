module

public import SerrePositivity.EInfinity.Hammock.MarkedValueSpineDescentRecovery
public import SerrePositivity.EInfinity.Hammock.LocalizationValue
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
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open CategoryTheory Limits

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) (X Y : Paths C)

def nativeValueHomMap : valueHom W X Y ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj (W.paths.Q.obj X ⟶ W.paths.Q.obj Y) :=
  (Functor.const SimplexCategoryᵒᵖ).map
    (↾fun p => (markedValueDescent W W.paths.Q W.paths.Q_inverts).map p)

lemma nativeValue_localizationValue :
    AllMarked.inclusion W X Y ≫ localizationValue W.paths X Y =
      AllMarked.nativeValue W X Y ≫ nativeValueHomMap W X Y := by
  apply colimit.hom_ext
  intro w
  change AllMarked.nativeInclusion W X Y w ≫ AllMarked.inclusion W X Y ≫
    localizationValue W.paths X Y = AllMarked.nativeInclusion W X Y w ≫
      Zigzag.Value.colimitValue (AllMarked.nativeFreeEvaluation W)
        (AllMarked.nativeFreeEvaluation_inverts_top W) ⟨X⟩ ⟨Y⟩ ≫ nativeValueHomMap W X Y
  rw [← Category.assoc, AllMarked.nativeInclusion_inclusion, Category.assoc,
    graphInclusion_localizationValue]
  change nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedZigzagLift.inclusion W.paths)) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueGraph.graphMap W.paths.Q W.paths.Q_inverts =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion (⊤ : MorphismProperty (WideSubcategory W.paths)) ⟨X⟩ ⟨Y⟩ w ≫
        Zigzag.Value.colimitValue (AllMarked.nativeFreeEvaluation W)
          (AllMarked.nativeFreeEvaluation_inverts_top W) ⟨X⟩ ⟨Y⟩ ≫ nativeValueHomMap W X Y
  rw [← Category.assoc, Zigzag.Value.graphInclusion_colimitValue]
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro τ
  exact eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.value_comparison (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedZigzagLift.inclusion W.paths)
    (AllMarked.nativeFreeEvaluation W) (AllMarked.nativeFreeEvaluation_inverts_top W)
    W.paths.Q W.paths.Q_inverts (markedValueDescent W W.paths.Q W.paths.Q_inverts)
    (nativeFreeEvaluation_descent W W.paths.Q W.paths.Q_inverts) (τ.obj 0))

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
