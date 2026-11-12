module

public import SerrePositivity.KST.Spectra.LoopMappingPositiveEquiv
public import SerrePositivity.KST.Spectra.SimplexCellPositiveNaturality

/-!
概要：球面の高次群の係数表示と loop 値の写像空間の正次数比較の整合性。
方針：標準球面の帰納式を源の比較同型への自然性でセル球面へ移す。
規約：既存の球面の向きと loop の次数移動をそのまま使う。
使われ方：Goerss–Jardine I §7、VIII §1。骨格の係数比較を全正次数へ反復する。
-/

@[expose] public section
universe u
open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SphereSimplex

/-- 概要：標準球面の係数表示は loop 値の正次数比較と正符号で可換。
方針：既存の帰納式の二つの交換射と loop の群同型の順逆を消す。
規約：球面次元 n+1、写像空間の次数 r+2。
使われ方：Goerss–Jardine I §7。球面の次数移動の帰納段の検査。 -/
theorem positiveHomotopyEquiv_loopPositive (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (n r : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup
      (PointedObject.basedHom (PointedSimplicialSet.sphere.{u} (n + 1)) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).right r
      (PointedSimplicialSet.basepoint
        (PointedObject.basedHom (PointedSimplicialSet.sphere.{u} (n + 1)) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)))) :
    positiveHomotopyEquiv Y n (r + 1)
      (PointedMapping.loopPositiveEquiv (PointedSimplicialSet.sphere.{u} (n + 1)) Y r a) =
        loopPositiveHomotopyEquiv Y (n + 1 + r)
          (positiveHomotopyEquiv (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n r a) := by
  rw [PointedMapping.loopPositiveEquiv_apply, positiveHomotopyEquiv_succ,
    MulEquiv.symm_apply_apply]
  change loopPositiveHomotopyEquiv Y (n + 1 + r)
    (positiveHomotopyEquiv (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n r
      (pointedGroupMap r
        (PointedMapping.loopSwap (PointedSimplicialSet.sphere.{u} (n + 1)) Y).hom
        (pointedGroupMap r
          (PointedMapping.loopSwap (PointedSimplicialSet.sphere.{u} (n + 1)) Y).inv a))) = _
  rw [← pointedGroupMap_comp, Iso.inv_hom_id, pointedGroupMap_id]

end SphereSimplex

namespace SimplexCell

/-- 概要：セル球面の全正次数係数は loop 値の係数から同じ符号で得られる。
方針：源の球面比較への自然性で標準球面の帰納式へ戻す。
規約：群同型そのものの可換式であり、零性だけの比較ではない。
使われ方：Goerss–Jardine VIII §1。塔の連結準同型を比較するための次数帰納。 -/
theorem positiveHomotopyEquiv_loopPositive (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (n r : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (PointedObject.basedHom (sphere.{u} (n + 1)) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).right r
      (PointedSimplicialSet.basepoint
        (PointedObject.basedHom (sphere.{u} (n + 1)) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)))) :
    positiveHomotopyEquiv Y n (r + 1)
      (PointedMapping.loopPositiveEquiv (sphere.{u} (n + 1)) Y r a) =
        loopPositiveHomotopyEquiv Y (n + 1 + r)
          (positiveHomotopyEquiv (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n r a) := by
  rw [positiveHomotopyEquiv_formula, ← PointedMapping.loopPositiveEquiv_pre,
    SphereSimplex.positiveHomotopyEquiv_loopPositive, positiveHomotopyEquiv_formula]

end SimplexCell
end
end SerrePositivity.KST.Spectra
