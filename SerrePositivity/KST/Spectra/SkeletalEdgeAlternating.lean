module

public import SerrePositivity.KST.Spectra.SkeletalEdgeConnecting
public import SerrePositivity.KST.Spectra.SkeletalLoopInput

/-!
概要：次数一の通常の交代微分と実際の骨格の成分微分の係数の一致。
方針：path 延長の終点と逆辺の接続写像を、標準の fiber の入力に照合する。
規約：充填の選択を結論に残さず、各セルで値そのものを比較する。
使われ方：Goerss–Jardine VIII §1。次数一の群の係数微分への移送。
-/

@[expose] public section
universe u
open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open UnbasedPointedMapping

/-- 次数一の loop cochain の微分は、対応する骨格の実際の成分微分の係数。 -/
theorem edge_normalizedDifferential_stageComponent (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (f : (K.skeleton 2 : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right)
    (hf : skeletalInclusion K 0 ≫ f = SSet.const (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint)
    (s : K.nonDegenerate 2) :
    (loopPositiveHomotopyEquiv Y 0).toAdditive
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K
        (AddCommGrpCat.of (Additive
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right 0 (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint))) 1
        (SkeletalEdgeCochain.cochain K Y f hf) s) =
      Additive.ofMul (stageFiberComponentEquiv K Y 1
        (stageComponentDifferential K Y 0 (stageFiberOrdinaryLoopComponentEquiv K Y 0
          (π₀.mk (skeletalFiberVertex K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) 0 f hf)))) s) := by
  obtain ⟨H, hH⟩ := SkeletalEdgePath.exists_extension K Y f
  have hi := stageComponentDifferential_loop_vertex K Y 0 f hf
  have hc := SkeletalEdgePath.componentConnecting_inverse_family K Y f H hH
  have hcomp := hi.trans hc
  have hend := SkeletalEdgePath.endpointFiberVertex_coefficient K Y f H hH s
  exact (SkeletalEdgePath.normalizedDifferential_endpoint K Y f H hH hf s).trans
    ((congrArg Additive.ofMul hend.symm).trans
      (congrArg (fun z ↦ Additive.ofMul (stageFiberComponentEquiv K Y 1 z s)) hcomp.symm))

end
end SerrePositivity.KST.Spectra.SkeletalCellAttachment
