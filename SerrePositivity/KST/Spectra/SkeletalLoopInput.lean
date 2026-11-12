module

public import SerrePositivity.KST.Spectra.UnbasedLoopVertices
public import SerrePositivity.KST.Spectra.SkeletalFiberLoopZero
public import SerrePositivity.KST.Spectra.SkeletalFiberRepresentatives
public import SerrePositivity.KST.Spectra.SkeletalCellBoundaryRestriction
public import SerrePositivity.KST.Spectra.SkeletalZeroCellConnecting

/-!
概要：骨格 fiber の通常の loop 成分比較と、明示した loop の辺の入力の一致。
方針：厳密な loop 交換の包含への自然性と、頂点の転置の計算を合成する。
規約：実際の fiber 包含による基本群の入力を保持する。
使われ方：Goerss–Jardine VIII §1。塔の係数微分と交代微分の比較。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open UnbasedPointedMapping

set_option maxHeartbeats 600000 in
-- 骨格の fiber と制限写像の fiber の別名を含む自然性の合成を照合するため。
/-- 骨格 fiber の零 loop 比較を含めると、全空間の零 loop 比較になる。 -/
lemma stageFiberOrdinaryLoopComponentEquiv_ι (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ)
    (a : π₀ (stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).right) :
    pointedGroupMap 0 (pointedFiberι (pre (skeletalInclusion K n) Y))
        (stageFiberOrdinaryLoopComponentEquiv K Y n a) =
      loopZeroHomotopyEquiv (obj (K.skeleton (n + 2)) Y)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero.symm
          (mapπ₀ (loopSwap (K.skeleton (n + 2)) Y).inv.right
            (mapπ₀ (pointedFiberι (pre (skeletalInclusion K n) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y))).right a))) := by
  let b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).right 0
    (stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).basepoint := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero.symm a
  have h := restrictionLoopIso_inv_ι (skeletalInclusion K n) Y
  have hm := congrArg (fun f ↦ pointedHomotopyMap 0 f b) h
  simp only [pointedHomotopyMap_comp] at hm
  change pointedGroupMap 0 _
    (loopZeroHomotopyEquiv (stageFiber K Y n)
      (pointedHomotopyMap 0 (stageFiberLoopIso K Y n).inv b)) = _
  rw [← loopZeroHomotopyEquiv_pointed_natural]
  have hi := pointedHomotopyZero_symm_natural
    (pointedFiberι (pre (skeletalInclusion K n) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y))) a
  have hs := pointedHomotopyZero_symm_natural
    (loopSwap (K.skeleton (n + 2)) Y).inv
    (mapπ₀ (pointedFiberι (pre (skeletalInclusion K n) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y))).right a)
  have hz := hs.trans (congrArg
    (pointedHomotopyMap 0 (loopSwap (K.skeleton (n + 2)) Y).inv) hi)
  exact (congrArg (loopZeroHomotopyEquiv (obj (K.skeleton (n + 2)) Y)) hm).trans
    (congrArg (loopZeroHomotopyEquiv (obj (K.skeleton (n + 2)) Y)) hz.symm)

/-- 骨格射から作った fiber 頂点の基本群入力は、明示した loop 族の逆辺。 -/
lemma stageFiberOrdinaryLoopComponentEquiv_vertex (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ)
    (f : (K.skeleton (n + 2) : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right)
    (hf : skeletalInclusion K n ≫ f = SSet.const (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint) :
    pointedGroupMap 0 (pointedFiberι (pre (skeletalInclusion K n) Y))
      (stageFiberOrdinaryLoopComponentEquiv K Y n
        (π₀.mk (skeletalFiberVertex K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n f hf))) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (loopFamilySimplex Y f))⁻¹ := by
  rw [stageFiberOrdinaryLoopComponentEquiv_ι, mapπ₀_mk]
  have hv : (pointedFiberι (pre (skeletalInclusion K n) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y))).right.app _
      (skeletalFiberVertex K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n f hf) = mapVertex (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) f :=
    (skeletalFiberVertex_ι K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n f hf).trans
      (freeHomIso_familyVertex (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) f)
  have hc := congrArg (fun v ↦ loopZeroHomotopyEquiv (obj (K.skeleton (n + 2)) Y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero.symm
      (mapπ₀ (loopSwap (K.skeleton (n + 2)) Y).inv.right (π₀.mk v)))) hv
  exact hc.trans (loopZero_mapVertex Y f)

/-- 通常の loop 成分比較で作った入力の塔の微分を、明示した逆辺で計算する。 -/
lemma stageComponentDifferential_loop_vertex (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ)
    (f : (K.skeleton (n + 2) : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right)
    (hf : skeletalInclusion K n ≫ f = SSet.const (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint) :
    stageComponentDifferential K Y n
      (stageFiberOrdinaryLoopComponentEquiv K Y n
        (π₀.mk (skeletalFiberVertex K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n f hf))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero
        (pointedConnectingZero (pre (skeletalInclusion K (n + 1)) Y)
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (loopFamilySimplex Y f))⁻¹)) := by
  rw [stageComponentDifferential_connecting]
  exact congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero
    (pointedConnectingZero (pre (skeletalInclusion K (n + 1)) Y) z))
      (stageFiberOrdinaryLoopComponentEquiv_vertex K Y n f hf)

end
end SerrePositivity.KST.Spectra.SkeletalCellAttachment
