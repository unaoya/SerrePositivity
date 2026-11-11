module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.QCatDiagramCoherentNerve
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianStrictTransportEquivalence

/-!
概要：通常の小圏の nerve 上の一般の cocartesian fibration に、Cat∞ 値の実際の図式を与える。
方針：F1B の cocartesian section の strict transport を QCat 値に束ね、coherent nerve へ実現する。
規約：図式の対象での fiber 比較は同じ恒等射評価。全 fibration の分類同値はまだ主張しない。
使われ方：Cat∞ 値 straightening の通常圏の nerve 上の分類図式の構成。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiber_quasicategory_of_innerFibration

/-- cocartesian section による元の strict transport を、小さい quasicategory 値の関手に束ねる。 -/
def cocartesianStrictTransportQCatFunctor {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [InnerFibration p] : C ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u} where
  obj c := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransport p c, inferInstance⟩
  map f := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportMap p f
  map_id c := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportMap_id p c
  map_comp f g := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportMap_comp p f g

/-- 一般の cocartesian fibration の strict transport の、元の Cat∞ への coherent な実現。 -/
def cocartesianStrictTransportCoherentDiagram {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.qCatDiagramCoherentNerve (cocartesianStrictTransportQCatFunctor p)

/-- 実現した同じ図式は、各頂点で元の cocartesian section の quasicategory を表す。 -/
lemma cocartesianStrictTransportCoherentDiagram_vertex
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (c : C) :
    (cocartesianStrictTransportCoherentDiagram p).app (Opposite.op ⦋0⦌)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((cocartesianStrictTransportQCatFunctor p).obj c) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.qCatDiagramCoherentNerve_vertex _ _

/-- この同じ図式が表す quasicategory は、元の指定 fiber と恒等射評価で同値。 -/
def cocartesianStrictTransportCoherentDiagramFiberEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (c : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject
      ((cocartesianStrictTransportCoherentDiagram p).app (Opposite.op ⦋0⦌)
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)))).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)) := by
  rw [cocartesianStrictTransportCoherentDiagram_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject_vertex]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportFiberEquivalence p c

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
