module

public import SerrePositivity.KST.Spectra.PathNaturality
public import SerrePositivity.KST.Spectra.LoopZeroHomotopy
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares

/-!
概要：loop の全自然数次数のホモトピー類の次数移動の自然性。
方針：path の連結同値、基点の移送、loop と fiber の自然な同型を合成する。
規約：零次数も集合の同値として同時に扱う。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。スペクトルの段の自然な比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：path の連結写像による全自然数次数の同値。
方針：零次数の全境界充填と、正次数の連結群同型をまとめる。
規約：始域の添字 n は実際の次数 n+1、終域は実際の次数 n。
使われ方：Goerss–Jardine I §7。loop の自然性の共通表示。 -/
def pathConnectingEquiv (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    (n : ℕ) → (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right n
      ((pathEndpoint Y).right.app _ (basedPathSpace Y).basepoint) ≃
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber (pathEndpoint Y).right
          ((pathEndpoint Y).right.app _ (basedPathSpace Y).basepoint)) n
            (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint (pathEndpoint Y).right (basedPathSpace Y).basepoint))
  | 0 => connectingZeroEquiv (pathEndpoint Y).right (basedPathSpace Y).basepoint
      (basedPathSpace_terminal_rlp Y)
  | n + 1 => (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connectingHomEquivOfTotalSubsingleton (pathEndpoint Y).right
      (basedPathSpace Y).basepoint n).toEquiv

/-- 概要：path の連結同値の順写像は元の連結写像。
方針：次数で場合分けして構成を読む。
規約：零次数も含む。
使われ方：Goerss–Jardine I §7。連結写像の自然性の適用。 -/
@[simp]
theorem pathConnectingEquiv_apply (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (n : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right n
      ((pathEndpoint Y).right.app _ (basedPathSpace Y).basepoint)) :
    pathConnectingEquiv Y n a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting (pathEndpoint Y).right
      (basedPathSpace Y).basepoint n a := by
  cases n <;> rfl

/-- 概要：path の連結同値は標的に関して自然。
方針：順写像を連結写像へ直し、path fibration の自然性を使う。
規約：全自然数次数の集合の同値。
使われ方：Goerss–Jardine I §7。loop の次数移動の自然性。 -/
theorem pathConnectingEquiv_natural {Y Z : PointedSimplicialSet.{u}}
    [KanComplex Y.right] [KanComplex Z.right] (p : Y ⟶ Z) (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right n
      ((pathEndpoint Y).right.app _ (basedPathSpace Y).basepoint)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (pathFiberMap p) (pathFiberMap_point p) (pathConnectingEquiv Y n a) =
      pathConnectingEquiv Z n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map p.right (pathFiberMap_base p) a) := by
  rw [pathConnectingEquiv_apply, pathConnectingEquiv_apply]
  exact pathConnecting_natural p n a

/-- 概要：path の基点の像と標的の基点の間の群同型。
方針：恒等射と終点評価の基点保存式を使う。
規約：添字 n は実際の次数 n+1。
使われ方：Goerss–Jardine I §7。loop の次数移動の基点の正規化。 -/
def pathBasepointGroupEquiv (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right n ((pathEndpoint Y).right.app _ (basedPathSpace Y).basepoint) ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right n Y.basepoint :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso n (Iso.refl Y.right) (pathEndpoint_basepoint Y)

/-- 概要：loop の全次数の比較を連結同値と二つの基点同型で計算する。
方針：零次数と正次数の構成を同じ式にまとめる。
規約：右辺の path の連結同値は集合の同値として扱う。
使われ方：Goerss–Jardine I §7、BF 1978 §2。自然性の図式の計算。 -/
theorem loopHomotopyEquiv_formula (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (n : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right n (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint) :
    loopHomotopyEquiv Y n a = pathBasepointGroupEquiv Y n
      ((pathConnectingEquiv Y n).symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfIso n (loopBasedPathFiberIso Y)
          (loopBasedPathFiberIso_basepoint Y) a)) := by
  cases n <;> rfl

/-- 概要：loop の全自然数次数の次数移動は点つき射に関して自然。
方針：fiber 同型、連結同値、基点移送の三つの可換正方形を合成する。
規約：零次数を含み、右辺の標的次数は n+1。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。段の比較の自然性。 -/
theorem loopHomotopyEquiv_natural {Y Z : PointedSimplicialSet.{u}}
    [KanComplex Y.right] [KanComplex Z.right] (p : Y ⟶ Z) (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right n (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint) :
    loopHomotopyEquiv Z n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n
      (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p).right
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _) a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map (n + 1) p.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p)
        (loopHomotopyEquiv Y n a) := by
  let eY := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfIso n (loopBasedPathFiberIso Y) (loopBasedPathFiberIso_basepoint Y)
  let eZ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfIso n (loopBasedPathFiberIso Z) (loopBasedPathFiberIso_basepoint Z)
  let cY := pathConnectingEquiv Y n
  let cZ := pathConnectingEquiv Z n
  let bY := (pathBasepointGroupEquiv Y n).toEquiv
  let bZ := (pathBasepointGroupEquiv Z n).toEquiv
  let mL := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n
    (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p).right
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _)
  let mF := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (pathFiberMap p) (pathFiberMap_point p)
  let mB := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := n) p.right (pathFiberMap_base p)
  let mY := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := n) p.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p)
  have hF : ∀ t, mF (eY t) = eZ (mL t) :=
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares.KanHomotopy.map_square (loopBasedPathFiberIso Y).hom (loopBasedPathFiberIso Z).hom
      (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p).right (pathFiberMap p)
      (loopBasedPathFiberIso_natural p) (loopBasedPathFiberIso_basepoint Y)
      (loopBasedPathFiberIso_basepoint Z) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _)
      (pathFiberMap_point p) n
  have hC : ∀ t, mF (cY t) = cZ (mB t) := pathConnectingEquiv_natural p n
  have hB : ∀ t, mY (bY t) = bZ (mB t) :=
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares.KanHomotopyGroup.map_square (𝟙 Y.right) (𝟙 Z.right) p.right p.right (by simp)
      (pathEndpoint_basepoint Y) (pathEndpoint_basepoint Z) (pathFiberMap_base p)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p) n
  rw [loopHomotopyEquiv_formula, loopHomotopyEquiv_formula]
  change bZ (cZ.symm (eZ (mL a))) = mY (bY (cY.symm (eY a)))
  apply bZ.symm.injective
  rw [bZ.symm_apply_apply]
  apply cZ.injective
  rw [cZ.apply_symm_apply]
  calc
    eZ (mL a) = mF (eY a) := (hF a).symm
    _ = mF (cY (cY.symm (eY a))) := by rw [cY.apply_symm_apply]
    _ = cZ (mB (cY.symm (eY a))) := hC _
    _ = cZ (bZ.symm (mY (bY (cY.symm (eY a))))) := by
      congr 1
      apply bZ.injective
      rw [bZ.apply_symm_apply]
      exact (hB _).symm

end

end SerrePositivity.KST.Spectra
