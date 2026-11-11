module

public import SerrePositivity.KST.LocalizingInvariants.FibrationFiberMap
public import SerrePositivity.KST.Spectra.PointedFibrationNaturality

/-!
概要：BF fiber の整数 π を、標準基点を持つ元の点つき fiber の一段で表示する。
方針：正次数の段表示と各段の置換比較射の π 同型を合成する。
規約：fiberPoint への基点輸送との比較も保持。使われ方：点つき接続射の自然性の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.FibrationFiberComparison
variable {X Y : OmegaSpectrum.{u}} (p : X ⟶ Y)
  [hp : ∀ n, Fibration (p.app n).right]
local instance pointedStageFibration (n : ℕ) : Fibration (p.app n).right := hp n

def projectionPointedEquiv (k n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup ((fiber p hp).level k).space.right n ((fiber p hp).level k).space.basepoint ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (pointedFiber (p.app k)).right n (pointedFiber (p.app k)).basepoint :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism n (fiberLevelProjection p hp k).right
    (fiberLevelProjection_piIsomorphism p hp k) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _)

lemma projectionPointedEquiv_apply (k n : ℕ)
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup ((fiber p hp).level k).space.right n
      ((fiber p hp).level k).space.basepoint) :
    projectionPointedEquiv p k n x = pointedGroupMap n (fiberLevelProjection p hp k) x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism_apply _ _ _ _ x

lemma projectionPointedEquiv_transport (k n : ℕ)
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup ((fiber p hp).level k).space.right n
      ((fiber p hp).level k).space.basepoint) :
    pointedFiberGroupEquiv (p.app k) n (projectionPointedEquiv p k n x) =
      fiberProjectionGroupEquiv p k n x := by
  rw [projectionPointedEquiv_apply, fiberProjectionGroupEquiv_apply]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (𝟙 _) _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (fiberLevelProjection p hp k).right _ x) = _
  have hc := DFunLike.congr_fun (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_comp
    (fiberLevelProjection p hp k).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _)
    (𝟙 (pointedFiber (p.app k)).right) (PointedSimplicialSet.basepoint_ofVertex _ _)
    (fiberLevelProjection_basepoint p k)) x
  exact hc.symm.trans (DFunLike.congr_fun
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares.KanHomotopyGroup.map_congr n (Category.comp_id (fiberLevelProjection p hp k).right) _ _) x)

def pointedStageEquiv (j : ℤ) (k n : ℕ) (hk : -j ≤ (k : ℤ)) (hd : degree j k = n + 1) :
    homotopyGroup (fiber p hp) j ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (pointedFiber (p.app k)).right n (pointedFiber (p.app k)).basepoint :=
  (positiveStageEquiv (fiber p hp) j k n hk hd).trans (projectionPointedEquiv p k n)

lemma pointedStageEquiv_transport (j : ℤ) (k n : ℕ) (hk : -j ≤ (k : ℤ))
    (hd : degree j k = n + 1) (x : homotopyGroup (fiber p hp) j) :
    pointedFiberGroupEquiv (p.app k) n (pointedStageEquiv p j k n hk hd x) =
      fiberPositiveStageEquiv p j k n hk hd x :=
  projectionPointedEquiv_transport p k n _

end SerrePositivity.KST.LocalizingInvariants.FibrationFiberComparison
