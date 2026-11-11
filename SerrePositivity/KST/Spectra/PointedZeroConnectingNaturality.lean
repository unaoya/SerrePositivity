module

public import SerrePositivity.KST.Spectra.PointedZeroConnecting
public import SerrePositivity.KST.Spectra.PointedFiberComparison
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FibrationBoundaryOverNaturality
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares

/-!
概要：標準基点での零次数接続写像の可換正方形への自然性。
方針：底の群同型と fiber の成分集合の同値の正方形を、相対ホーンの自然性に合成する。
規約：fiber 間の射は実際の点つき可換正方形から構成する。
使われ方：Goerss–Jardine I §§7–8、VIII §1。塔の微分の係数自然性。
-/

@[expose] public section

universe u

open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FibrationSquare

/-- 概要：指定参照頂点の fiber 間の射でも零次数接続写像は自然。
方針：参照頂点の等式で戻し、包含後の一意性で既存の fiberMap と同定する。
規約：出力の零次数は集合。
使われ方：Goerss–Jardine I §8。標準基点の零次数自然性の移送。 -/
theorem connectingZeroOver_natural {E B E' B' : SSet.{u}}
    [KanComplex B] [KanComplex B']
    (p : E ⟶ B) (q : E' ⟶ B') [Fibration p] [Fibration q]
    (f : E ⟶ E') (g : B ⟶ B') (comm : p ≫ g = f ≫ q)
    (e : E _⦋0⦌) (e' : E' _⦋0⦌) (he : f.app _ e = e')
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber q (q.app _ e'))
    (hφ : φ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι q (q.app _ e') = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e) ≫ f)
    (hpoint : φ.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint q e')
    (hb : g.app _ (p.app _ e) = q.app _ e')
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B 0 (p.app _ e)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map 0 φ hpoint (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e 0 a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting q e' 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map g hb a) := by
  subst e'
  have hφeq : φ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap p q f g comm e := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext q (q.app _ (f.app _ e))
    exact hφ.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap_ι p q f g comm e).symm
  subst φ
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.connecting_natural p q f g comm e 0 a

end FibrationSquare

/-- 概要：点つき fibration の可換正方形で零次数の接続写像は可換。
方針：各基点の群同型を用いて L9b の fiber の自然性へ帰着する。
規約：底は基本群、fiber は成分集合。
使われ方：Goerss–Jardine I §8、VIII §1。骨格の塔の微分の自然性。 -/
theorem pointedConnectingZero_natural {E B E' B' : PointedSimplicialSet.{u}}
    [KanComplex E.right] [KanComplex B.right] [KanComplex E'.right] [KanComplex B'.right]
    (p : E ⟶ B) (q : E' ⟶ B') [Fibration p.right] [Fibration q.right]
    (f : E ⟶ E') (g : B ⟶ B') (h : p ≫ g = f ≫ q)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B.right 0 B.basepoint) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map 0 (PointedFiberComparison.map p q f g h).right
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (PointedFiberComparison.map p q f g h))
      (pointedConnectingZero p a) =
      pointedConnectingZero q (pointedGroupMap 0 g a) := by
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
  let bP := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso 0 (Iso.refl B.right)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p)
  let bQ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso 0 (Iso.refl B'.right)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint q)
  have hF (t : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (pointedFiber p).right 0 (pointedFiber p).basepoint) :
      pointedFiberZeroEquiv q (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map 0 Φ.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint Φ) t) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map 0 φ hfpoint (pointedFiberZeroEquiv p t) := by
    exact (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares.KanHomotopy.map_square (𝟙 (pointedFiber p).right)
      (𝟙 (pointedFiber q).right) Φ.right φ (by
        simp only [Category.id_comp, Category.comp_id]
        rfl)
      (PointedSimplicialSet.basepoint_ofVertex _ _)
      (PointedSimplicialSet.basepoint_ofVertex _ _)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint Φ) hfpoint 0 t).symm
  have hB (t : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B.right 0 (p.right.app _ E.basepoint)) :
      pointedGroupMap 0 g (bP t) = bQ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map g.right hb t) :=
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares.KanHomotopyGroup.map_square (𝟙 B.right) (𝟙 B'.right) g.right g.right (by simp)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint q)
      hb (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint g) 0 t
  have hBinv : bQ.symm (pointedGroupMap 0 g a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map g.right hb (bP.symm a) := by
    apply bQ.injective
    rw [MulEquiv.apply_symm_apply, ← hB, MulEquiv.apply_symm_apply]
  apply (pointedFiberZeroEquiv q).injective
  rw [hF]
  dsimp only [pointedConnectingZero]
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map 0 φ hfpoint (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p.right E.basepoint 0 (bP.symm a)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting q.right E'.basepoint 0 (bQ.symm (pointedGroupMap 0 g a))
  rw [hBinv]
  exact FibrationSquare.connectingZeroOver_natural p.right q.right f.right g.right hc
    E.basepoint E'.basepoint (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint f) φ hφ hfpoint hb (bP.symm a)

end
end SerrePositivity.KST.Spectra
