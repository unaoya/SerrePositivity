module

public import SerrePositivity.KST.Spectra.PointedFibrationBoundary
public import SerrePositivity.KST.Spectra.PointedFiberComparison
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FibrationBoundaryOverNaturality
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares

/-!
概要：標準基点での点つき連結準同型の可換正方形への自然性。
方針：底と fiber の基点の群同型の正方形を、相対ホーンの自然性に合成する。
規約：fiber 間の射は実際の点つき可換正方形から構成する。
使われ方：Goerss–Jardine I §§7–8、VIII §1。塔の微分の係数自然性。
-/

@[expose] public section

universe u

open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：点つき fibration の可換正方形で連結準同型は可換。
方針：各基点の群同型を用いて L9b の fiber の自然性へ帰着する。
規約：底の次数は r+2、fiber の次数は r+1。
使われ方：Goerss–Jardine I §8、VIII §1。骨格の塔の微分の自然性。 -/
theorem pointedConnectingHom_natural {E B E' B' : PointedSimplicialSet.{u}}
    [KanComplex E.right] [KanComplex B.right] [KanComplex E'.right] [KanComplex B'.right]
    (p : E ⟶ B) (q : E' ⟶ B') [Fibration p.right] [Fibration q.right]
    (f : E ⟶ E') (g : B ⟶ B') (h : p ≫ g = f ≫ q) (r : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B.right (r + 1) B.basepoint) :
    pointedGroupMap r (PointedFiberComparison.map p q f g h) (pointedConnectingHom p r a) =
      pointedConnectingHom q r (pointedGroupMap (r + 1) g a) := by
  let Φ := PointedFiberComparison.map p q f g h
  let φ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p.right (p.right.app _ E.basepoint) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber q.right (q.right.app _ E'.basepoint) := Φ.right
  have hφ : φ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι q.right (q.right.app _ E'.basepoint) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p.right (p.right.app _ E.basepoint) ≫ f.right := by
    have hv := congrArg Under.Hom.right (PointedFiberComparison.map_ι p q f g h)
    exact hv
  have hfpoint : φ.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p.right E.basepoint) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint q.right E'.basepoint := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_vertex_ext q.right (q.right.app _ E'.basepoint)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point]
    have hv := congrArg (fun k : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p.right (p.right.app _ E.basepoint) ⟶ E'.right ↦
      k.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p.right E.basepoint)) hφ
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι q.right _).app _ (φ.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p.right E.basepoint)) =
      f.right.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p.right _).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p.right E.basepoint)) at hv
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point] at hv
    exact hv.trans (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint f)
  have hc : p.right ≫ g.right = f.right ≫ q.right := congrArg Under.Hom.right h
  have hb : g.right.app _ (p.right.app _ E.basepoint) = q.right.app _ E'.basepoint :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.base_eq p.right q.right f.right g.right hc E.basepoint).trans
      (congrArg (q.right.app _) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint f))
  let bP := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (r + 1) (Iso.refl B.right)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p)
  let bQ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (r + 1) (Iso.refl B'.right)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint q)
  have hF (t : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (pointedFiber p).right r (pointedFiber p).basepoint) :
      pointedFiberGroupEquiv q r (pointedGroupMap r Φ t) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map φ hfpoint (pointedFiberGroupEquiv p r t) := by
    exact (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares.KanHomotopyGroup.map_square (𝟙 (pointedFiber p).right)
      (𝟙 (pointedFiber q).right) Φ.right φ (by
        simp only [Category.id_comp, Category.comp_id]
        rfl)
      (PointedSimplicialSet.basepoint_ofVertex _ _)
      (PointedSimplicialSet.basepoint_ofVertex _ _)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint Φ) hfpoint r t).symm
  have hB (t : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B.right (r + 1) (p.right.app _ E.basepoint)) :
      pointedGroupMap (r + 1) g (bP t) = bQ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map g.right hb t) :=
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares.KanHomotopyGroup.map_square (𝟙 B.right) (𝟙 B'.right) g.right g.right (by simp)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint q)
      hb (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint g) (r + 1) t
  have hBinv : bQ.symm (pointedGroupMap (r + 1) g a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map g.right hb (bP.symm a) := by
    apply bQ.injective
    rw [MulEquiv.apply_symm_apply, ← hB, MulEquiv.apply_symm_apply]
  apply (pointedFiberGroupEquiv q r).injective
  rw [hF, pointedConnectingHom_compute, pointedConnectingHom_compute]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map φ hfpoint (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connectingHom p.right E.basepoint r (bP.symm a)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connectingHom q.right E'.basepoint r (bQ.symm (pointedGroupMap (r + 1) g a))
  rw [hBinv]
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.connectingHomOver_natural p.right q.right f.right g.right hc
    E.basepoint E'.basepoint (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint f) φ hφ hfpoint hb r (bP.symm a)

end

end SerrePositivity.KST.Spectra
