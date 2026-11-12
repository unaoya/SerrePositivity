module

public import SerrePositivity.KST.Spectra.PositiveLoopNaturality

/-!
概要：loop 空間の基本群の可換性。
方針：既存の loop 群同型を通じて、標的の二次ホモトピー群の可換性を戻す。
規約：基本群の既存の積を保持する。
使われ方：Goerss–Jardine I §7、VIII §1。次数一の cochain の加法的係数。
-/

@[expose] public section
universe u
open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- loop 空間の基本群は既存の積について可換群。 -/
instance loopFundamentalCommGroup (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    CommGroup (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right 0 (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint) where
  __ := (inferInstance : Group (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right 0 (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint))
  mul_comm a b := by
    apply (loopPositiveHomotopyEquiv Y 0).injective
    rw [map_mul, map_mul, mul_comm]

end
end SerrePositivity.KST.Spectra
