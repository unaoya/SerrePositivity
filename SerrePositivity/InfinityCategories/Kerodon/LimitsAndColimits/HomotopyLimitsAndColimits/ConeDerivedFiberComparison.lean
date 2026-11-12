module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.FibrationDerivedFiberSpan

/-!
概要：coherent な錐の slice 内の pinched Hom を始点評価の導来ファイバーと比較する。
方針：前工程の strict fiber の同型を、Kan fibration の strict・導来 fiber の同値へ接続する。
規約：比較する射は既存の span の始点評価であり、sHom からの q_x との同定は含めない。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の主比較の写像空間側。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

/-- 概要：right fibration の頂点 fiber の Kan 性を型クラスとして使える。
方針：既存の right fibration の fiber の Kan 性を登録する。
規約：始域と標的の quasicategory 性は要求しない。
使われ方：Kerodon 4.4.2.3（Tag 019E）、7.5.4.6（Tag 03BB） の比較の始点評価の導来ファイバー。 -/
instance rightFibrationVertexFiber_kanComplex {E B : SSet.{u}} (r : E ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration r] (x : B.obj (Opposite.op ⦋0⦌)) : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber r x) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex r x

/-- 概要：right fibration の pinched Hom は比較 span の始点評価の導来ファイバーと同値。
方針：strict fiber の厳密な同型を、Kan fibration の導来ファイバーへの同値と合成する。
規約：E の quasicategory 性は B と r から導出できるが、ここでは型の前提として明示する。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の写像空間と導来ファイバーの比較の一般形。 -/
noncomputable def rightFibrationPinchedEvaluationDerivedFiberEquivalence {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (r : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration r]
    (c : E.obj (Opposite.op ⦋0⦌)) (x : B.obj (Opposite.op ⦋0⦌))
    (d : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber r x).obj (Opposite.op ⦋0⦌)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom d.val c)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationMappingEvaluation r c x) d) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationMappingEvaluationFiberIso r c x d).symm).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.fibrationStrictDerivedFiberEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationMappingEvaluation r c x) d)

/-- 概要：任意の coherent な錐の間の pinched Hom は始点評価の実際の導来ファイバーと同値。
方針：錐の頂点への slice 射影を一般の right fibration の比較へ適用する。
規約：strict な通常の錐に制限せず、全ての coherent な錐 d・c を扱う。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の極限錐の検出。 -/
noncomputable def conePinchedHom_mappingEvaluationDerivedFiberEquivalence
    {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X} (d c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) d c)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationMappingEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p) c d.vertex)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneVertexFiberPoint d)) :=
  rightFibrationPinchedEvaluationDerivedFiberEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p) c d.vertex
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneVertexFiberPoint d)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
