module
public import SerrePositivity.KST.Fibration.ZeroMiddleFullSReconstruction

/-!
概要：厳密切断を要求しない全族再構成を、同じ実全 S• 座標へ代入する。
方針：採用済みの可逆比較版を元の core・全 S•・二短辺へ適用する。
規約：供給命題に条件付き。旧仕様の厳密読出し保存や冪等性は推論しない。
使われ方：K-6 c4 の全族の可逆移送への入力。
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
variable (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌) (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (s.obj ⟨ULift.up 1⟩))
  (K : SSet.{u + 1})

/-- 概要：同じ実全 S• 再構成の読出し合成を恒等へ可逆比較する。
方針：二短辺と全ホーンを元のまま可逆比較版の供給仕様へ代入する。
規約：供給命題に条件付き。合成を厳密恒等とは主張しない。
使われ方：正規化対角を元の指定長 Hom 族へ移送する際の共通データ。 -/
theorem zeroMiddleFullSComparisonReconstruction_exists
    (h9 : zeroMiddleControlledTriangleComparisonSupply.{u}) :
    ∃ (encode : zeroMiddleFullSReconstructionLongSpace s hZ K ⟶
        zeroMiddleFullSReconstructionTriangleSpace s hZ K)
      (read : zeroMiddleFullSReconstructionTriangleSpace s hZ K ⟶
        zeroMiddleFullSReconstructionLongSpace s hZ K),
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (encode ≫ read) (𝟙 _)) ∧
      zeroMiddleFullSReconstructionRecovery s hZ K read ∧
      zeroMiddleFullSReconstructionDiagonalRecovery s hZ K encode read ∧
      zeroMiddleFullSReconstructionNormalizeComparison s hZ K encode read := by
  obtain ⟨encode, read, he, hread, hdiag, hnorm, _⟩ := h9
    (stableCoreSingleKanObject (s.obj ⟨ULift.up 0⟩))
    (fullSRealizationKanObject (s.obj ⟨ULift.up 0⟩))
    (stableCoreSingleKanObject (s.obj ⟨ULift.up 2⟩)) K
    (zeroMiddleFullSFirstFamily s K) (zeroMiddleFullSLastFamily s hZ K)
    (zeroMiddleFullSReconstructionHorn s hZ K)
    (zeroMiddleFullSReconstructionHorn_first s hZ K)
    (zeroMiddleFullSReconstructionHorn_last s hZ K)
  exact ⟨encode, read, he, hread, hdiag, hnorm⟩

/-- 概要：全族の可逆比較を同じ指定長 Hom 入力で評価する。
方針：関手空間の評価写像で同じ比較を写す。
規約：元入力への厳密等式へは置き換えない。
使われ方：再構成の読み戻しから元入力へ戻る可逆移送。 -/
def zeroMiddleFullSComparisonReadPoint
    (encode : zeroMiddleFullSReconstructionLongSpace s hZ K ⟶
      zeroMiddleFullSReconstructionTriangleSpace s hZ K)
    (read : zeroMiddleFullSReconstructionTriangleSpace s hZ K ⟶
      zeroMiddleFullSReconstructionLongSpace s hZ K)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (encode ≫ read) (𝟙 _))
    (ℓ : (zeroMiddleFullSReconstructionLongSpace s hZ K) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (read.app (Opposite.op ⦋0⦌)
      (encode.app (Opposite.op ⦋0⦌) ℓ)) ℓ := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt ℓ)
  simpa [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex] using h

end SerrePositivity.KST.Fibration
