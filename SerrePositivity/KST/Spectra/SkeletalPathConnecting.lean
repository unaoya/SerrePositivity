module

public import SerrePositivity.KST.Spectra.SkeletalPathCoboundary
public import SerrePositivity.KST.Spectra.UnbasedLoopFamilies
public import SerrePositivity.KST.Spectra.ReverseComponentConnecting
public import SerrePositivity.KST.Spectra.SkeletalCellBoundaryRestriction

/-!
概要：path 延長の終点の fiber 成分を実際の零次数接続写像で計算する。
方針：延長の辺を通常の写像空間へ転置し、底の逆 loop の接続写像の式へ代入する。
規約：入力は実際の loop 族の辺の逆元で明示する。
使われ方：Goerss–Jardine VIII §1。交代 coboundary と塔の成分微分の接続。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.SkeletalPathCoboundary

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (K : SSet.{u}) (Y : PointedSimplicialSet.{u}) {n : ℕ}
  (f : (K.skeleton (n + 3) : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right)
  (H : (K.skeleton (n + 4) : SSet.{u}) ⟶ (basedPathSpace Y).right)
  (hH : UnbasedPointedMapping.skeletalInclusion K (n + 2) ≫ H =
    f ≫ (PointedMapping.loopToPath Y).right)

/-- 延長の終点の fiber 頂点を含めると、終点の通常の射の頂点になる。 -/
lemma endpointFiberVertex_ι :
    (pointedFiberι (UnbasedPointedMapping.pre
      (UnbasedPointedMapping.skeletalInclusion K (n + 2)) Y)).right.app _
        (endpointFiberVertex K Y f H hH) =
      UnbasedPointedMapping.mapVertex Y (H ≫ (pathEndpoint Y).right) := by
  have hv := SkeletalCellAttachment.skeletalFiberVertex_ι K Y (n + 2)
    (H ≫ (pathEndpoint Y).right) (endpoint_lower K Y f H hH)
  exact hv.trans (UnbasedPointedMapping.freeHomIso_familyVertex Y _)

include hH in
/-- 転置した延長の辺の射影は元の loop 族の辺そのもの。 -/
lemma familyEdge_projection :
    UnbasedPointedMapping.pathFamilyEdge Y H ≫
        (UnbasedPointedMapping.pre (UnbasedPointedMapping.skeletalInclusion K (n + 2)) Y).right =
      (UnbasedPointedMapping.loopFamilySimplex Y f).map := by
  rw [UnbasedPointedMapping.pathFamilyEdge_pre, hH]
  rfl

/-- 概要：path 延長の終点は、元の loop 族の逆辺の零次数接続写像で得られる。
方針：延長の転置の射影と両端を使い、逆 loop の相対ホーン充填の公式を適用する。
規約：標準の基点と実際の終点の頂点を保持する。
使われ方：Goerss–Jardine VIII §1。正規化交代式を実際の接続写像へ移す界面。 -/
theorem connecting_inverse_family [KanComplex Y.right] :
    pointedConnectingZero (UnbasedPointedMapping.pre
        (UnbasedPointedMapping.skeletalInclusion K (n + 2)) Y)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (UnbasedPointedMapping.loopFamilySimplex Y f))⁻¹) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk 0
        ((PtSimplex.equiv₀ (pointedFiber (UnbasedPointedMapping.pre
          (UnbasedPointedMapping.skeletalInclusion K (n + 2)) Y)).basepoint).symm
          (endpointFiberVertex K Y f H hH)) := by
  let p := UnbasedPointedMapping.pre (UnbasedPointedMapping.skeletalInclusion K (n + 2)) Y
  let s := SimplexBasepoint.rebase (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p).symm
    (UnbasedPointedMapping.loopFamilySimplex Y f)
  let a := (PtSimplex.equiv₀ (pointedFiber p).basepoint).symm
    (endpointFiberVertex K Y f H hH)
  have hT : UnbasedPointedMapping.pathFamilyEdge Y H ≫ p.right = s.map :=
    familyEdge_projection K Y f H hH
  have hv : (pointedFiberι p).right.app _ (endpointFiberVertex K Y f H hH) =
      UnbasedPointedMapping.mapVertex Y (H ≫ (pathEndpoint Y).right) :=
    endpointFiberVertex_ι K Y f H hH
  have h₀ : stdSimplex.δ (0 : Fin 2) ≫ UnbasedPointedMapping.pathFamilyEdge Y H =
      a.map ≫ (pointedFiberι p).right := by
    rw [UnbasedPointedMapping.pathFamilyEdge_face_zero, a.map_eq_const_equiv₀, const_comp]
    change SSet.yonedaEquiv.symm _ = SSet.const
      ((pointedFiberι p).right.app _ ((PtSimplex.equiv₀ (pointedFiber p).basepoint) a))
    rw [show (PtSimplex.equiv₀ (pointedFiber p).basepoint) a =
      endpointFiberVertex K Y f H hH from Equiv.apply_symm_apply _ _, hv]
    exact SSet.yonedaEquiv_symm_zero _
  have he := pointedConnectingZero_inverse_edge p s a
    (UnbasedPointedMapping.pathFamilyEdge Y H) hT h₀
    (UnbasedPointedMapping.pathFamilyEdge_face_one Y H)
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso 0 (Iso.refl _)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (UnbasedPointedMapping.loopFamilySimplex Y f) := by
    rw [SimplexBasepoint.group_mk]
    congr 1
  exact (congrArg (fun z ↦ pointedConnectingZero p (z⁻¹)) hs).symm.trans he

/-- 上の接続写像の値を、基点に依存しない終点の fiber 成分へ移す。 -/
lemma componentConnecting_inverse_family [KanComplex Y.right] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero
        (pointedConnectingZero (UnbasedPointedMapping.pre
          (UnbasedPointedMapping.skeletalInclusion K (n + 2)) Y)
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (UnbasedPointedMapping.loopFamilySimplex Y f))⁻¹)) =
      π₀.mk (endpointFiberVertex K Y f H hH) := by
  rw [connecting_inverse_family K Y f H hH]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.mk _) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero_mk, Equiv.apply_symm_apply]

end
end SerrePositivity.KST.Spectra.SkeletalPathCoboundary
