module
public import SerrePositivity.KST.Fibration.ZeroMiddleFullSComparisonReconstruction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ControlledTriangleNormalizedFamilySupply

/-!
概要：Ind-S (9) の実正規化供給を採用済みの全族可逆比較仕様へ代入する。
方針：公開された元の encode/read・native 回収・正規化対角を同じ型で消費する。
規約：F1 正本は読み取り専用。厳密切断版の供給や c4 の完了は主張しない。
使われ方：K-6 c4 の正規化と可逆移送から供給命題引数を除く。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 概要：採用済みの全族可逆比較版の再構成仕様は実供給される。
方針：F1 正本の正規化全族定理を同じ仕様へ代入する。
規約：旧厳密切断仕様とは区別する。
使われ方：同じ実全 S• 座標の再構成と下側正規化への代入。 -/
theorem zeroMiddleControlledTriangleComparisonSupply_of_indS9 :
    zeroMiddleControlledTriangleComparisonSupply.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleNormalizedFamilySupply

/-- 概要：同じ実全 S• 座標で全族可逆比較・native 回収・正規化対角が実供給される。
方針：元の二短辺と全ホーンを、供給済みの同じ再構成データへ代入する。
規約：存在仮定は不要。読出し合成は厳密等式ではなく全族関手同型。
使われ方：K-6 c4 の実上側正規化と共有対角の可逆移送。 -/
theorem zeroMiddleFullSComparisonReconstruction_supplied
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌) (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (s.obj ⟨ULift.up 1⟩))
    (K : SSet.{u + 1}) :
    ∃ (encode : zeroMiddleFullSReconstructionLongSpace s hZ K ⟶
        zeroMiddleFullSReconstructionTriangleSpace s hZ K)
      (read : zeroMiddleFullSReconstructionTriangleSpace s hZ K ⟶
        zeroMiddleFullSReconstructionLongSpace s hZ K),
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (encode ≫ read) (𝟙 _)) ∧
      zeroMiddleFullSReconstructionRecovery s hZ K read ∧
      zeroMiddleFullSReconstructionDiagonalRecovery s hZ K encode read ∧
      zeroMiddleFullSReconstructionNormalizeComparison s hZ K encode read :=
  zeroMiddleFullSComparisonReconstruction_exists s hZ K
    zeroMiddleControlledTriangleComparisonSupply_of_indS9

end SerrePositivity.KST.Fibration
