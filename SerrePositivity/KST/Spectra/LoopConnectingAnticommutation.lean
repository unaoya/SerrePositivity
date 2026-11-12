module

public import SerrePositivity.KST.Spectra.LoopConnectingStandardRepresentatives

/-!
概要：標準の点つき連結準同型と loop の正次数の群同型の反可換性。
方針：底の高次群の任意の代表を選び、二つの実際の相対ホーン充填から代表での逆元式を適用する。
規約：既存の loop 同型・連結射・fiber 同型をそのまま用い、符号は逆元として述べる。
使われ方：Goerss–Jardine I §8、VIII §1。骨格の塔の微分の次数移動。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：loop による次数移動と連結射は全正次数で逆符号を伴って交換する。
方針：底の群の代表から二つの充填を選び、共通 path と隣接比較ホーンによる逆元公式へ帰着する。
規約：a の実際の次数は n+2、結論の実際の次数は n+2。零 loop 成分は別に扱う。
使われ方：Goerss–Jardine I §8、VIII §1。係数微分の loop との交換の符号。 -/
theorem pointedConnectingHom_loopPositive {E B : PointedSimplicialSet.{u}}
    (p : E ⟶ B) [Fibration p.right] [KanComplex E.right] [KanComplex B.right]
    (n : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B).right (n + 1) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B).basepoint) :
    loopPositiveHomotopyEquiv (pointedFiber p) n
      (pointedGroupMap n (loopPointedFiberIso p).inv
        (pointedConnectingHom (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p) n a)) =
      (pointedConnectingHom p (n + 1) (loopPositiveHomotopyEquiv B (n + 1) a))⁻¹ := by
  let eb := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (n + 2) (Iso.refl B.right)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p)
  let b := eb.symm (loopPositiveHomotopyEquiv B (n + 1) a)
  obtain ⟨s, hs⟩ := Quotient.mk_surjective b
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s = b at hs
  let L := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.chooseBoundaryLift p.right E.basepoint s
  let M := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.chooseBoundaryLift (pathEndpoint B).right (basedPathSpace B).basepoint
    (LoopConnectingComparison.pathBaseSimplex p s)
  let V := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.chooseBoundaryLift
    (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p).right
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace E).basepoint (LoopConnectingComparison.sourceLoop p s M)
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (n + 2) (Iso.refl B.right)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s) =
      loopPositiveHomotopyEquiv B (n + 1) a := by
    rw [hs]
    exact eb.apply_symm_apply _
  have ha : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (n + 1) (Iso.refl (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B).right)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint
        (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (LoopConnectingComparison.sourceLoop p s M)) = a := by
    apply (loopPositiveHomotopyEquiv B (n + 1)).injective
    rw [LoopConnectingComparison.sourceLoop_positive, hb]
  have he := LoopConnectingComparison.pointedConnecting_loop_representative p s M L V
  rw [ha, hb] at he
  exact he

end
end SerrePositivity.KST.Spectra
