module

public import SerrePositivity.KST.Spectra.RestrictionZeroConnecting
public import SerrePositivity.KST.Spectra.SkeletalCellBoundaryRestriction
public import SerrePositivity.KST.Spectra.SkeletalZeroComponents

/-!
概要：実際の骨格の成分微分の各セルの値を境界制限の接続写像へ帰着する。
方針：セルの正方形への成分自然性を使い、相対商の実際の射の代表を供給する。
規約：入力と出力を同じセルと同じ充填で比較する。
使われ方：Goerss–Jardine VIII §1。成分微分の交代和を計算する局所化。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open SSet.modelCategoryQuillen
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- セル境界の制限の成分で、実際の骨格 fiber の成分係数を計算する。 -/
lemma stageFiberComponentEquiv_boundaryRestriction (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ)
    (x : π₀ (UnbasedPointedMapping.stageFiber K Y n).right)
    (s : K.nonDegenerate (n + 1)) :
    stageFiberComponentEquiv K Y n x s = SimplexCell.componentEquiv Y n
      (mapπ₀ (UnbasedPointedMapping.restrictionFiberIso (boundary (n + 1)).ι Y).inv.right
        (mapπ₀ (cellBoundaryFiberMap K Y n ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 1)).symm s)).right x)) := by
  have h := congrArg Under.Hom.right
    (cellBoundaryFiberMap_sphere K Y n ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 1)).symm s))
  simp only [Under.comp_right] at h
  rw [stageFiberComponentEquiv_restriction, ← mapπ₀_comp_apply, ← h, mapπ₀_comp_apply]

set_option maxHeartbeats 2000000 in
-- 塔の遷移と骨格の制限射の定義的一致を確認するために必要。
lemma stageComponentDifferential_connecting (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.stageFiber K Y n).right 0
      (UnbasedPointedMapping.stageFiber K Y n).basepoint) :
    UnbasedPointedMapping.stageComponentDifferential K Y n a =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero
        (pointedConnectingZero (UnbasedPointedMapping.pre
          (UnbasedPointedMapping.skeletalInclusion K (n + 1)) Y)
          (pointedGroupMap 0 (pointedFiberι (UnbasedPointedMapping.pre
            (UnbasedPointedMapping.skeletalInclusion K n) Y)) a)) := rfl

/-- 各セルの成分微分を計算する実際の基本群入力。 -/
def cellComponentConnectingInput (K : SSet.{u}) (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.stageFiber K Y n).right 0
      (UnbasedPointedMapping.stageFiber K Y n).basepoint) (s : K.nonDegenerate (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.obj (boundary (n + 2) : SSet.{u}) Y).right 0
      (UnbasedPointedMapping.obj (boundary (n + 2) : SSet.{u}) Y).basepoint :=
  pointedGroupMap 0 (UnbasedPointedMapping.pre
    (cellBoundarySource K (n + 2) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 2)).symm s)) Y)
    (pointedGroupMap 0 (pointedFiberι (UnbasedPointedMapping.pre
      (UnbasedPointedMapping.skeletalInclusion K n) Y)) a)

/-- 概要：骨格の成分微分の各セルの値は、そのセル境界の零次数接続写像の値。
方針：fiber のセル制限式に実際の接続写像の源自然性を合成する。
規約：標準の成分係数そのものを比較する。
使われ方：Goerss–Jardine VIII §1。局所的な cofiber 代表での値の計算。 -/
theorem stageComponentDifferential_cellConnecting (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.stageFiber K Y n).right 0
      (UnbasedPointedMapping.stageFiber K Y n).basepoint) (s : K.nonDegenerate (n + 2)) :
    stageFiberComponentEquiv K Y (n + 1)
        (UnbasedPointedMapping.stageComponentDifferential K Y n a) s =
      SimplexCell.componentEquiv Y (n + 1)
        (mapπ₀ (UnbasedPointedMapping.restrictionFiberIso (boundary (n + 2)).ι Y).inv.right
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero
            (pointedConnectingZero (UnbasedPointedMapping.pre (boundary (n + 2)).ι Y)
              (cellComponentConnectingInput K Y n a s)))) := by
  rw [stageFiberComponentEquiv_boundaryRestriction, stageComponentDifferential_connecting]
  have h := UnbasedPointedMapping.restrictionSourceFiberMap_componentConnecting
    (UnbasedPointedMapping.skeletalInclusion K (n + 1)) (boundary (n + 2)).ι
    (cellBoundarySource K (n + 2) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 2)).symm s))
    (cellSimplexSource K (n + 2) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 2)).symm s))
    (cellSourceSquare K (n + 2) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 2)).symm s)) Y
    (pointedGroupMap 0 (pointedFiberι (UnbasedPointedMapping.pre
      (UnbasedPointedMapping.skeletalInclusion K n) Y)) a)
  exact congrArg (fun t ↦ SimplexCell.componentEquiv Y (n + 1)
    (mapπ₀ (UnbasedPointedMapping.restrictionFiberIso (boundary (n + 2)).ι Y).inv.right t)) h

end
end SerrePositivity.KST.Spectra.SkeletalCellAttachment
