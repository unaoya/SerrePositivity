module

public import SerrePositivity.KST.Spectra.SkeletalZeroCellConnecting

/-!
概要：成分微分のセル係数を、相対商からの実際の射の境界定数単体で代表する。
方針：セル境界の接続写像の入力と充填を選び、成分の球面比較の代表公式を適用する。
規約：元の基本群入力との対応を結論に残す。
使われ方：Goerss–Jardine VIII §1。path 延長の終点と成分微分の出力の照合。
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

/-- 概要：任意の成分微分のセルの値は相対ホーン充填の相対商の射で表せる。
方針：実際の局所入力の代表と充填を取り、球面の成分係数を同じ射の単体で計算する。
規約：零性でなく出力の群の値の等式。
使われ方：Goerss–Jardine VIII §1。成分微分と幾何的 coboundary の代表の比較。 -/
theorem exists_cellComponentDifferential_boundaryRepresentative (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.stageFiber K Y n).right 0
      (UnbasedPointedMapping.stageFiber K Y n).basepoint) (s : K.nonDegenerate (n + 2)) :
    ∃ (t : (UnbasedPointedMapping.obj (boundary (n + 2) : SSet.{u}) Y).right.PtSimplex 1
        ((UnbasedPointedMapping.pre (boundary (n + 2)).ι Y).right.app _
          (UnbasedPointedMapping.obj (Δ[n + 2] : SSet.{u}) Y).basepoint))
      (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift (UnbasedPointedMapping.pre (boundary (n + 2)).ι Y).right
        (UnbasedPointedMapping.obj (Δ[n + 2] : SSet.{u}) Y).basepoint t),
      cellComponentConnectingInput K Y n a s =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso 0
          (Iso.refl (UnbasedPointedMapping.obj (boundary (n + 2) : SSet.{u}) Y).right)
          (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint
            (UnbasedPointedMapping.pre (boundary (n + 2)).ι Y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk t) ∧
      stageFiberComponentEquiv K Y (n + 1)
          (UnbasedPointedMapping.stageComponentDifferential K Y n a) s =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (SphereSimplex.equiv Y (n + 2)
          ((SimplexCell.sphereIso.{u} (n + 2)).inv ≫
            UnbasedPointedMapping.cofiberBoundaryMap (boundary (n + 2)).ι Y L)) := by
  obtain ⟨t, L, ht, hL⟩ := UnbasedPointedMapping.exists_connectingZero_boundaryRepresentative
    (boundary (n + 2)).ι Y (cellComponentConnectingInput K Y n a s)
  refine ⟨t, L, ht, ?_⟩
  rw [stageComponentDifferential_cellConnecting, hL,
    SimplexCell.componentEquiv_familyVertex]

end
end SerrePositivity.KST.Spectra.SkeletalCellAttachment
