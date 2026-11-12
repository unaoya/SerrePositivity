module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.TensorHomotopyEquivalence

/-!
概要：二つの Kan 値関手同型を、同じ二成分への射の直積の関手同型へ束ねる。
方針：指定された二つのホモトピーを同じ時間の対にして、Kan 値の可逆性を使う。
規約：元の二つの指定関手同型を使う。
使われ方：一次元境界の両端の自然性を同じ境界全体の自然性へ貼る。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensor_isKan

/-- 同じ時間の二つの指定関手同型から、二成分の対の関手同型を構成する。 -/
def pairedKanFunctorIso {T X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    {f f' : T ⟶ X} {g g' : T ⟶ Y} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f f') (k : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g g') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (lift f g) (lift f' g') :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.pairedSimplicialHomotopy h.simplicialHomotopy k.simplicialHomotopy)

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
