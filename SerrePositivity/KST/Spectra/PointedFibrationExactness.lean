module

public import SerrePositivity.KST.Spectra.PointedFibrationBoundary
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.GroupExactTransfer

/-!
概要：標準の点つき基点での Kan fibration の正次数の完全列。
方針：L9b の像の基点での完全性を三つの群同型で移す。
規約：fiber と底の基点の移送を明示する。追加の完全性仮定は使わない。
使われ方：Goerss–Jardine I §§7–8、VIII §1。骨格の塔の exact couple の完全性。
-/

@[expose] public section

universe u

open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E B : PointedSimplicialSet.{u}} (p : E ⟶ B) [Fibration p.right]
  [KanComplex E.right] [KanComplex B.right]

/-- 概要：点つき fiber の包含の核は連結準同型の像。
方針：fiber の基点表示と底の像の基点での表示で L9b の完全性を移す。
規約：fiber の次数は r+1。
使われ方：Goerss–Jardine I §8、VIII §1。塔の fiber の位置の完全性。 -/
theorem pointed_exact_connecting_fiber (r : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (pointedFiber p).right r (pointedFiber p).basepoint) :
    pointedGroupMap r (pointedFiberι p) a = 1 ↔
      ∃ b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B.right (r + 1) B.basepoint, pointedConnectingHom p r b = a := by
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.group_exact_of_equivalences (pointedConnectingHom p r)
    (pointedGroupMap r (pointedFiberι p)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connectingHom p.right E.basepoint r)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p.right (p.right.app _ E.basepoint))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point p.right E.basepoint))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (r + 1) (Iso.refl B.right)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p)).symm
    (pointedFiberGroupEquiv p r) (MulEquiv.refl _)
    (pointedConnectingHom_compute p r) (pointedFiberGroupEquiv_inclusion p r)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exact_connecting_fiber p.right E.basepoint r) a

/-- 概要：点つき連結準同型の核は全空間からの射影の像。
方針：像の基点へ戻す自然な群同型で L9b の底の完全性を移す。
規約：底と全空間の次数は r+2。
使われ方：Goerss–Jardine I §8、VIII §1。塔の段の位置の完全性。 -/
theorem pointed_exact_total_base (r : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B.right (r + 1) B.basepoint) :
    pointedConnectingHom p r a = 1 ↔
      ∃ b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup E.right (r + 1) E.basepoint,
        pointedGroupMap (r + 1) p b = a := by
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.group_exact_of_equivalences (pointedGroupMap (r + 1) p)
    (pointedConnectingHom p r) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := r + 1) p.right rfl)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connectingHom p.right E.basepoint r) (MulEquiv.refl _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (r + 1) (Iso.refl B.right)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p)).symm
    (pointedFiberGroupEquiv p r)
    (KanHomotopyGroup.map_basepoint_transport p.right
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p) (r + 1))
    (pointedConnectingHom_compute p r) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exact_total_base p.right E.basepoint r) a

/-- 概要：点つき全空間から底への準同型の核は fiber 包含の像。
方針：fiber と底の基点表示の群同型で L9b の全空間の完全性を移す。
規約：次数は r+1。正次数のすべてで成立する。
使われ方：Goerss–Jardine I §8、VIII §1。塔の exact couple の残りの位置。 -/
theorem pointed_exact_fiber_total (r : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup E.right r E.basepoint) :
    pointedGroupMap r p a = 1 ↔
      ∃ b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (pointedFiber p).right r (pointedFiber p).basepoint,
        pointedGroupMap r (pointedFiberι p) b = a := by
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.group_exact_of_equivalences (pointedGroupMap r (pointedFiberι p))
    (pointedGroupMap r p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p.right (p.right.app _ E.basepoint))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point p.right E.basepoint)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := r) p.right rfl)
    (pointedFiberGroupEquiv p r) (MulEquiv.refl _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso r (Iso.refl B.right)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p)).symm
    (pointedFiberGroupEquiv_inclusion p r)
    (KanHomotopyGroup.map_basepoint_transport p.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p) r)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exact_fiber_total p.right E.basepoint r) a

end

end SerrePositivity.KST.Spectra
