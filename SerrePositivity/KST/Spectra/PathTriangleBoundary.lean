module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Pullbacks.FiberTriangleConnecting
public import SerrePositivity.KST.Spectra.SphericalPathBoundary

/-!
概要：path 空間内の三角形の三つの loop の交代和を終点の二次ホモトピー類で計算する。
方針：相対三角形の積を path fiber の同型と loop の正次数同型で可換群へ送る。
規約：三角形の向きを反転せず、符号は正。
使われ方：Goerss–Jardine I §8、VIII §1。cochain 次数一の幾何的な微分。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.PathTriangleBoundary

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 三辺の loop の交代和は、path の終点の二単体の類に一致する。 -/
theorem alternating_loopPositive (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (s : Y.right.PtSimplex 2
      ((pathEndpoint Y).right.app _ (basedPathSpace Y).basepoint))
    (a : Fin 3 → (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right.PtSimplex 1 (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint)
    (T : (Δ[2] : SSet.{u}) ⟶ (basedPathSpace Y).right)
    (hT : T ≫ (pathEndpoint Y).right = s.map)
    (hface : ∀ j, stdSimplex.δ j ≫ T = (a j).map ≫
      (loopBasedPathFiberIso Y).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι (pathEndpoint Y).right
        ((pathEndpoint Y).right.app _ (basedPathSpace Y).basepoint)) :
    (∑ j : Fin 3, (-1 : ℤ) ^ j.val • Additive.ofMul
      (loopPositiveHomotopyEquiv Y 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (a j)))) =
      Additive.ofMul (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso 1 (Iso.refl Y.right)
        (pathEndpoint_basepoint Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s)) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso 0 (loopBasedPathFiberIso Y)
    (loopBasedPathFiberIso_basepoint Y)
  let φ := (loopPositiveHomotopyEquiv Y 0).toMonoidHom.comp e.symm.toMonoidHom
  let L : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SphericalFiberLift (pathEndpoint Y).right (basedPathSpace Y).basepoint s
      (fun j ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (loopBasedPathFiberIso Y).hom
        (loopBasedPathFiberIso_basepoint Y) (a j)) :=
    { map := T
      map_comp := hT
      face_eq j := hface j }
  have h := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.alternating_connecting L φ
  have hm (j : Fin 3) : φ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (loopBasedPathFiberIso Y).hom (loopBasedPathFiberIso_basepoint Y) (a j))) =
      loopPositiveHomotopyEquiv Y 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (a j)) := by
    change loopPositiveHomotopyEquiv Y 0 (e.symm (e (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (a j)))) = _
    rw [MulEquiv.symm_apply_apply]
  have hc := connecting_loopPositiveHomotopyEquiv Y 0
    ((loopPositiveHomotopyEquiv Y 0).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso 1 (Iso.refl Y.right)
        (pathEndpoint_basepoint Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s)))
  rw [MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply] at hc
  simp only [hm] at h
  rw [hc] at h
  simpa only [φ, e, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply] using h

end
end SerrePositivity.KST.Spectra.PathTriangleBoundary
