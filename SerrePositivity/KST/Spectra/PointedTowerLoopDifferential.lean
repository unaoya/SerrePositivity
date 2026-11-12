module

public import SerrePositivity.KST.Spectra.LoopConnectingAnticommutation
public import SerrePositivity.KST.Spectra.LoopConnectingZeroAnticommutation
public import SerrePositivity.KST.Spectra.PositiveLoopNaturality
public import SerrePositivity.KST.Spectra.PointedTowerDifferential

/-!
概要：点つき fibration の塔の微分と loop による次数移動の反可換性。
方針：loop–fiber 同型の包含式と loop 同型の自然性を、接続準同型の反可換式へ合成する。
規約：全正次数の群で比較し、符号は逆元で表す。
使われ方：Goerss–Jardine VIII §1。骨格の塔の係数微分の次数移動。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- loop–fiber 同型の逆射も、loop に送った包含と可換。 -/
@[reassoc]
lemma loopPointedFiberIso_inv_ι {E B : PointedSimplicialSet.{u}} (p : E ⟶ B) :
    (loopPointedFiberIso p).inv ≫
      PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (pointedFiberι p) =
    pointedFiberι (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p) := by
  rw [← loopPointedFiberIso_hom_ι, Iso.inv_hom_id_assoc]

/-- 概要：loop による fiber の次数移動は全空間への包含と可換。
方針：loop–fiber 同型の包含式を群に送り、loop の群同型の自然性を使う。
規約：全正次数。
使われ方：Goerss–Jardine VIII §1。塔の微分の源の次数移動。 -/
lemma loopFiberPositive_inclusion {E B : PointedSimplicialSet.{u}} (p : E ⟶ B)
    [Fibration p.right] [KanComplex E.right] [KanComplex B.right] (r : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup
      (pointedFiber (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p)).right r
      (pointedFiber (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p)).basepoint) :
    loopPositiveHomotopyEquiv E r
      (pointedGroupMap r
        (pointedFiberι (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p)) a) =
    pointedGroupMap (r + 1) (pointedFiberι p)
      (loopPositiveHomotopyEquiv (pointedFiber p) r
        (pointedGroupMap r (loopPointedFiberIso p).inv a)) := by
  have h := congrArg (fun f ↦ pointedGroupMap r f a) (loopPointedFiberIso_inv_ι p)
  simp only [pointedGroupMap_comp] at h
  rw [← h]
  exact loopPositiveHomotopyEquiv_natural (pointedFiberι p) r _

namespace PointedFibrationTower

variable (X : ℕ → PointedSimplicialSet.{u}) (p : ∀ n, X (n + 1) ⟶ X n)
  [∀ n, KanComplex (X n).right] [∀ n, Fibration (p n).right]

/-- 概要：塔を loop に送った微分は、元の塔の一つ高い次数の微分の逆符号。
方針：次の段の接続射の反可換性と、前の段の fiber 包含の自然性を合成する。
規約：通常の厳密な loop–fiber 同型を使用する。
使われ方：Goerss–Jardine VIII §1。骨格係数の交代微分への移送。 -/
theorem differential_loopPositive (n r : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup
      (pointedFiber (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (p n))).right
      (r + 1)
      (pointedFiber (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (p n))).basepoint) :
    loopPositiveHomotopyEquiv (pointedFiber (p (n + 1))) r
      (pointedGroupMap r (loopPointedFiberIso (p (n + 1))).inv
        (differential (fun k ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (X k))
          (fun k ↦ PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (p k)) n r a)) =
    (differential X p n (r + 1)
      (loopPositiveHomotopyEquiv (pointedFiber (p n)) (r + 1)
        (pointedGroupMap (r + 1) (loopPointedFiberIso (p n)).inv a)))⁻¹ := by
  rw [differential_apply, pointedConnectingHom_loopPositive,
    loopFiberPositive_inclusion, differential_apply]

/-- 概要：loop に送った塔の零次数の接続写像も、元の塔の微分と逆符号で交換する。
方針：零 loop の反可換式と、前の fiber 包含の基本群での自然性を合成する。
規約：左辺の接続写像の出力は成分集合、比較の出力は元の fiber の基本群。
使われ方：Goerss–Jardine VIII §1。成分から始める反復 loop 比較の基本段。 -/
theorem differential_loopZero (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup
      (pointedFiber (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (p n))).right 0
      (pointedFiber (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (p n))).basepoint) :
    loopZeroHomotopyEquiv (pointedFiber (p (n + 1)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map 0 (loopPointedFiberIso (p (n + 1))).inv.right
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (loopPointedFiberIso (p (n + 1))).inv)
        (pointedConnectingZero
          (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (p (n + 1)))
          (pointedGroupMap 0
            (pointedFiberι (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (p n))) a))) =
    (differential X p n 0
      (loopPositiveHomotopyEquiv (pointedFiber (p n)) 0
        (pointedGroupMap 0 (loopPointedFiberIso (p n)).inv a)))⁻¹ := by
  rw [pointedConnectingZero_loopZero, loopFiberPositive_inclusion, differential_apply]

end PointedFibrationTower
end
end SerrePositivity.KST.Spectra
