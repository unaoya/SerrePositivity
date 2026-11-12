module

public import SerrePositivity.KST.Spectra.SkeletalCellBoundaryRestriction
public import SerrePositivity.KST.Spectra.SkeletalFiberDifferential

/-!
概要：骨格の塔の実際の微分の各セルの係数をセル境界の連結準同型へ帰着する。
方針：係数の境界 fiber 表示と源の正方形に対する連結準同型の自然性を合成する。
規約：通常の交代微分との同定と符号の最終計算は局所的な連結射の計算に残す。
使われ方：Goerss–Jardine VIII §1。塔の微分の実際のセルごとの計算。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 2000000 in
-- 塔の源の関手と通常の制限射の定義的一致を検査するための局所的な上限。
lemma stageDifferential_connecting (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n r : ℕ)
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.stageFiber K Y n).right (r + 1)
      (UnbasedPointedMapping.stageFiber K Y n).basepoint) :
    UnbasedPointedMapping.stageDifferential K Y n r x =
      pointedConnectingHom (UnbasedPointedMapping.pre
        (UnbasedPointedMapping.skeletalInclusion K (n + 1)) Y) r
        (pointedGroupMap (r + 1) (pointedFiberι (UnbasedPointedMapping.pre
          (UnbasedPointedMapping.skeletalInclusion K n) Y)) x) := rfl

/-- 概要：塔の微分の指定セルでの値はそのセルの境界制限の連結射で計算できる。
方針：微分を包含と連結射へ展開し、セルの源の正方形への自然性を適用する。
規約：零性ではなく、既存の係数同型による値そのものの等式。
使われ方：Goerss–Jardine VIII §1。交代式を証明すべき局所的な連結射を固定する。 -/
theorem stageFiberDifferential_cellConnecting (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n r : ℕ)
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.stageFiber K Y n).right (r + 1)
      (UnbasedPointedMapping.stageFiber K Y n).basepoint) (s : K.nonDegenerate (n + 2)) :
    stageFiberCoefficientEquiv K Y (n + 1) r
        (UnbasedPointedMapping.stageDifferential K Y n r x) s =
      SimplexCell.positiveHomotopyEquiv Y (n + 1) r
        (pointedGroupMap r
          (UnbasedPointedMapping.restrictionFiberIso (boundary (n + 2)).ι Y).inv
          (pointedConnectingHom (UnbasedPointedMapping.pre (boundary (n + 2)).ι Y) r
            (pointedGroupMap (r + 1)
              (UnbasedPointedMapping.pre
                (cellBoundarySource K (n + 2) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 2)).symm s)) Y)
              (pointedGroupMap (r + 1)
                (pointedFiberι (UnbasedPointedMapping.pre
                  (UnbasedPointedMapping.skeletalInclusion K n) Y)) x)))) := by
  rw [stageFiberCoefficientEquiv_boundaryRestriction, stageDifferential_connecting]
  have h := UnbasedPointedMapping.restrictionSourceFiberMap_connecting
    (UnbasedPointedMapping.skeletalInclusion K (n + 1)) (boundary (n + 2)).ι
    (cellBoundarySource K (n + 2) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 2)).symm s))
    (cellSimplexSource K (n + 2) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 2)).symm s))
    (cellSourceSquare K (n + 2) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 2)).symm s)) Y r
    (pointedGroupMap (r + 1)
      (pointedFiberι (UnbasedPointedMapping.pre
        (UnbasedPointedMapping.skeletalInclusion K n) Y)) x)
  exact congrArg (fun t ↦ SimplexCell.positiveHomotopyEquiv Y (n + 1) r
    (pointedGroupMap r
      (UnbasedPointedMapping.restrictionFiberIso (boundary (n + 2)).ι Y).inv t)) h

end
end SerrePositivity.KST.Spectra.SkeletalCellAttachment
