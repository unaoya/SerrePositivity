module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ComparisonFiberFunctor
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ConeDerivedFiberComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.RightFibrationHomComparison

/-!
概要：right fibration の選んだ写像空間の比較の導来 fiber を全空間の pinched Hom と比較する。
方針：span の切断は同値であり、その切断が同じ底上の導来 fiber に誘導する射を使う。
規約：極限性や可縮性を仮定せず、全ての指定頂点上で実際の fiber を比較する。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6（Tag 05QS）・7.5.4.6（Tag 03BB）、錐の切断比較の導来 fiber の同定。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
noncomputable section

/-- 概要：right fibration の比較 span への選んだ切断はホモトピー同値。
方針：射影の自明 Kan fibration 性と切断の厳密な左逆の式に二対三則を使う。
規約：底が quasicategory なら、全空間の Kan 性は比較 span 自身から得る。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、比較射の始域の置換を各導来 fiber へ移す。 -/
lemma rightFibrationMappingSection_homotopyEquivalence {E B : SSet.{u}}
    [Quasicategory B] (r : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration r]
    (c : E _⦋0⦌) (x : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationMappingSection r c x) := by
  have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationMappingHomProjection r c x)
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationMappingSection r c x) := by
    apply hp.cancel_right
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationMappingSection_projection]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (Iso.refl _)).isQCatEquivalence
  exact hs.isSimplicialHomotopyEquivalence

/-- 概要：選んだ表現可能な比較の導来 fiber から比較 span の始点評価の導来 fiber への射。
方針：同じ底上で span の切断が誘導する既存の実際の fiber 射を使う。
規約：底の fiber の頂点 d を変更しない。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、pinched Hom との同値を選んだ比較射へ移す。 -/
def rightFibrationHomDerivedFiberMap {E B : SSet.{u}} (r : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration r]
    (c : E _⦋0⦌) (x : B _⦋0⦌) (d : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber r x) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationHomComparison r c x) d ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationMappingEvaluation r c x) d :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.comparisonFiberMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationHomComparison r c x)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationMappingEvaluation r c x) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationMappingSection r c x) rfl d

/-- 概要：実際の fiber 射の源成分は span の切断と厳密に可換。
方針：同じ底上の fiber 射の源成分の式を適用する。
規約：底の頂点 d は固定する。
使われ方：選択した切断の fiber 上の作用を追跡する。 -/
lemma rightFibrationHomDerivedFiberMap_source {E B : SSet.{u}}
    (r : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration r] (c : E _⦋0⦌) (x : B _⦋0⦌)
    (d : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber r x) _⦋0⦌) :
    rightFibrationHomDerivedFiberMap r c x d ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.comparisonFiberSource (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationMappingEvaluation r c x) d =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.comparisonFiberSource (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationHomComparison r c x) d ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationMappingSection r c x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.comparisonFiberMap_source _ _ _ _ _

/-- 概要：span の切断による実際の fiber 射は底の可逆 path を保つ。
方針：同じ底上の fiber 射の path 成分の式を使う。
規約：path の両端も変更しない。
使われ方：fiber の比較が元の指定頂点のデータに整合することの確認。 -/
lemma rightFibrationHomDerivedFiberMap_path {E B : SSet.{u}}
    (r : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration r] (c : E _⦋0⦌) (x : B _⦋0⦌)
    (d : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber r x) _⦋0⦌) :
    rightFibrationHomDerivedFiberMap r c x d ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.comparisonFiberPath (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationMappingEvaluation r c x) d =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.comparisonFiberPath (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationHomComparison r c x) d :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.comparisonFiberMap_path _ _ _ _ _

/-- 概要：選んだ比較と始点評価の間の実際の導来 fiber の射はホモトピー同値。
方針：span の切断の同値性を同じ底上の源の比較に適用する。
規約：r の Kan fibration 性、比較射の同値性、fiber の可縮性は要求しない。
使われ方：Kerodon 7.4.1.6（Tag 05QS）・7.5.4.6（Tag 03BB）、全空間の pinched Hom と選んだ比較の接続。 -/
lemma rightFibrationHomDerivedFiberMap_homotopyEquivalence {E B : SSet.{u}}
    [Quasicategory B] (r : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration r]
    (c : E _⦋0⦌) (x : B _⦋0⦌) (d : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber r x) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (rightFibrationHomDerivedFiberMap r c x d) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.comparisonFiberMap_homotopyEquivalence _ _ _ _
    (rightFibrationMappingSection_homotopyEquivalence r c x) d

/-- 概要：全空間の二頂点間の pinched Hom と選んだ表現可能な比較の導来 fiber は同値。
方針：始点評価の fiber の同値と切断から誘導した実際の fiber 射の逆を合成する。
規約：d は x 上の任意の頂点で、終対象性や可縮性を仮定しない。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6（Tag 05QS）・7.5.4.6（Tag 03BB）、任意の coherent な錐の比較。 -/
def rightFibrationPinchedHomComparisonDerivedFiberEquivalence {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (r : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration r]
    (c : E _⦋0⦌) (x : B _⦋0⦌) (d : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber r x) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom d.val c)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationHomComparison r c x) d) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.rightFibrationPinchedEvaluationDerivedFiberEquivalence r c x d).trans
    (rightFibrationHomDerivedFiberMap_homotopyEquivalence r c x d).isQCatEquivalence.choose.symm

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
