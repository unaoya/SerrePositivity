module

public import SerrePositivity.KST.Spectra.SkeletalLoopInput
public import SerrePositivity.KST.Spectra.SkeletalConnectingAlternating

/-!
概要：骨格 fiber の実際の成分微分の係数と正規化交代微分の一致。
方針：通常の loop 成分比較の入力を明示した逆辺と同定して交代式へ代入する。
規約：cochain 次数二以上。向きの係数を明示する。
使われ方：Goerss–Jardine VIII §1。塔の微分の幾何的な同定。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open UnbasedPointedMapping

/-- loop 値の骨格射の交代微分は、対応する fiber の実際の成分微分の係数。 -/
theorem normalizedDifferential_stageComponent (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] {n : ℕ}
    (f : (K.skeleton (n + 3) : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right)
    (hf : skeletalInclusion K (n + 1) ≫ f = SSet.const (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint)
    (s : K.nonDegenerate (n + 3)) :
    (loopPositiveHomotopyEquiv Y (n + 1)).toAdditive
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K
          (AddCommGrpCat.of (Additive
            (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right (n + 1) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint)))
          (n + 2) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cochain f
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.lower_constant f hf)) s) =
      (-1 : ℤ) ^ (n + 3) • Additive.ofMul
        (stageFiberComponentEquiv K Y (n + 2)
          (stageComponentDifferential K Y (n + 1)
            (stageFiberOrdinaryLoopComponentEquiv K Y (n + 1)
              (π₀.mk (skeletalFiberVertex K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) (n + 1) f hf)))) s) := by
  have hi := stageComponentDifferential_loop_vertex K Y (n + 1) f hf
  have hc := congrArg (fun z ↦ (-1 : ℤ) ^ (n + 3) • Additive.ofMul
    (stageFiberComponentEquiv K Y (n + 2) z s)) hi
  exact (SkeletalPathCoboundary.normalizedDifferential_connecting K Y f
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.lower_constant f hf) s).trans hc.symm

end
end SerrePositivity.KST.Spectra.SkeletalCellAttachment
