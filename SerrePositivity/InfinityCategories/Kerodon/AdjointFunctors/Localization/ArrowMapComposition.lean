module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardPairComposition
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.PointActions
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitArrowMap

/-!
# 元の射の単位からの hammock 写像の合成保存

概要：同じ二射を連結する元の合成は、元の合成射の一定単体写像に一致する。
方針：二列 forward の全次数での圧縮を単位からの写像へ束ねる。
規約：元の任意の射・実単位・全単体を保持する。
使われ方：通常圏から hammock への実関手。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory
variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {X Y Z : C}

lemma composeUnitMaps_arrowMap (f : X ⟶ Y) (g : Y ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composeUnitMaps (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W f) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W g) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W (f ≫ g) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro p
  cases p
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardPairComposition.composePoint_arrowPoint W f g n

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
