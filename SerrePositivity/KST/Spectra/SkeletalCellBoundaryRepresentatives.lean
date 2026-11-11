module

public import SerrePositivity.KST.Spectra.SkeletalCellConnecting
public import SerrePositivity.KST.Spectra.RestrictionConnectingNullhomotopy

/-!
概要：塔の微分の各セルの値を相対ホーン充填の最後の面で代表する。
方針：セルへの帰着で得た実際の入力の単体と充填を選び、公開連結射の代表式を使う。
規約：局所入力との対応を保持する。交代式の符号の最終比較はなお別に必要。
使われ方：Goerss–Jardine VIII §1。微分の局所的な値を計算する代表の供給。
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

/-- 概要：塔の微分を局所化したときのセル境界上の実際の入力。
方針：前の fiber を共通の段へ含め、セルの付着境界へ制限する。
規約：入力の実際のホモトピー次数は r+2。
使われ方：Goerss–Jardine VIII §1。微分の入力を局所的な充填へ渡す。 -/
def cellConnectingInput (K : SSet.{u}) (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (n r : ℕ)
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.stageFiber K Y n).right (r + 1)
      (UnbasedPointedMapping.stageFiber K Y n).basepoint) (s : K.nonDegenerate (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.obj (boundary (n + 2) : SSet.{u}) Y).right (r + 1)
      (UnbasedPointedMapping.obj (boundary (n + 2) : SSet.{u}) Y).basepoint :=
  pointedGroupMap (r + 1) (UnbasedPointedMapping.pre
    (cellBoundarySource K (n + 2) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 2)).symm s)) Y)
    (pointedGroupMap (r + 1) (pointedFiberι (UnbasedPointedMapping.pre
      (UnbasedPointedMapping.skeletalInclusion K n) Y)) x)

/-- 概要：任意の塔の微分のセル係数を実際の充填の最後の面で代表できる。
方針：局所入力の基点移送を戻して代表と充填を取り、その代表式を係数同型へ送る。
規約：局所入力との対応も結論に含むので、代表と元の入力を取り違えない。
使われ方：Goerss–Jardine VIII §1。交代微分との比較に用いる実際の代表。 -/
theorem exists_cellDifferential_boundaryRepresentative (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n r : ℕ)
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.stageFiber K Y n).right (r + 1)
      (UnbasedPointedMapping.stageFiber K Y n).basepoint) (s : K.nonDegenerate (n + 2)) :
    ∃ (t : (UnbasedPointedMapping.obj (boundary (n + 2) : SSet.{u}) Y).right.PtSimplex (r + 2)
        ((UnbasedPointedMapping.pre (boundary (n + 2)).ι Y).right.app _
          (UnbasedPointedMapping.obj (Δ[n + 2] : SSet.{u}) Y).basepoint))
      (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift (UnbasedPointedMapping.pre (boundary (n + 2)).ι Y).right
        (UnbasedPointedMapping.obj (Δ[n + 2] : SSet.{u}) Y).basepoint t),
      cellConnectingInput K Y n r x s =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (r + 1)
          (Iso.refl (UnbasedPointedMapping.obj (boundary (n + 2) : SSet.{u}) Y).right)
          (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint
            (UnbasedPointedMapping.pre (boundary (n + 2)).ι Y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk t) ∧
      stageFiberCoefficientEquiv K Y (n + 1) r
          (UnbasedPointedMapping.stageDifferential K Y n r x) s =
        SimplexCell.positiveHomotopyEquiv Y (n + 1) r
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk
            (UnbasedPointedMapping.cofiberBoundarySimplex (boundary (n + 2)).ι Y L)) := by
  obtain ⟨t, L, ht, hL⟩ := UnbasedPointedMapping.exists_connecting_boundaryRepresentative
    (boundary (n + 2)).ι Y r (cellConnectingInput K Y n r x s)
  refine ⟨t, L, ht, ?_⟩
  rw [stageFiberDifferential_cellConnecting]
  exact congrArg (SimplexCell.positiveHomotopyEquiv Y (n + 1) r) hL

end
end SerrePositivity.KST.Spectra.SkeletalCellAttachment
