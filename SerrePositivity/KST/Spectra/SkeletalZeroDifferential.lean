module

public import SerrePositivity.KST.Spectra.SkeletalLoopDifferential
public import SerrePositivity.KST.Spectra.PointedTowerZeroDifferential

/-!
概要：骨格の塔の零次数微分と通常の loop による成分比較。
方針：写像空間の交換の自然同型で零次数接続写像を移し、既存の基本段の逆元式を適用する。
規約：零次数は集合、戻した先は元の fiber の基本群。
使われ方：Goerss–Jardine VIII §1。係数微分の成分計算への接続。
-/

@[expose] public section
universe u
open CategoryTheory Opposite SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 基本群から次の骨格 fiber の零次数への実際の微分。 -/
def UnbasedPointedMapping.stageDifferentialZero (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (stageFiber K Y n).right 0 (stageFiber K Y n).basepoint →
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (stageFiber K Y (n + 1)).right 0 (stageFiber K Y (n + 1)).basepoint := by
  let p := fun m ↦ (tower K Y).map (homOfLE (Nat.le_succ m)).op
  let : ∀ m, Fibration (p m).right := fun m ↦ tower_map_fibration K Y _
  exact PointedFibrationTower.differentialZero (fun m ↦ (tower K Y).obj (op m)) p n

namespace SkeletalCellAttachment

/-- 通常の loop 値の骨格 fiber の零次数と元の骨格 fiber の基本群の同値。 -/
def stageFiberLoopZeroEquiv (K : SSet.{u}) (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (UnbasedPointedMapping.stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).right 0
        (UnbasedPointedMapping.stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).basepoint ≃
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.stageFiber K Y n).right 0
        (UnbasedPointedMapping.stageFiber K Y n).basepoint := by
  letI : KanComplex (PointedSimplicialSet.forget.obj
      (UnbasedPointedMapping.stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n)) :=
    UnbasedPointedMapping.stageFiber_kanComplex K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n
  letI : KanComplex (PointedSimplicialSet.forget.obj
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (UnbasedPointedMapping.stageFiber K Y n))) :=
    inferInstanceAs (KanComplex (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (UnbasedPointedMapping.stageFiber K Y n)).right)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfIso 0
    (PointedSimplicialSet.forget.mapIso (stageFiberLoopIso K Y n).symm)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (stageFiberLoopIso K Y n).inv)).trans
      (loopZeroHomotopyEquiv (UnbasedPointedMapping.stageFiber K Y n))

lemma stageFiberLoopZeroEquiv_apply (K : SSet.{u}) (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (UnbasedPointedMapping.stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).right 0
      (UnbasedPointedMapping.stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).basepoint) :
    stageFiberLoopZeroEquiv K Y n a =
    loopZeroHomotopyEquiv (UnbasedPointedMapping.stageFiber K Y n)
      (pointedHomotopyMap 0 (stageFiberLoopIso K Y n).inv a) := rfl

set_option maxHeartbeats 1000000 in
-- 塔の射と二つの fiber 同型の合成を展開して照合するために必要。
/-- 概要：骨格の零次数微分も、元の骨格微分と逆符号で交換する。
方針：loop に送った塔と loop 値の塔の零次数自然性を使い、一般の塔の基本段へ帰着する。
規約：接続写像の出力は零次数の集合のまま保持する。
使われ方：Goerss–Jardine VIII §1。零次数の成分係数へ移す基本段。 -/
theorem stageDifferential_loopZero (K : SSet.{u}) (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).right 0
      (UnbasedPointedMapping.stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).basepoint) :
    stageFiberLoopZeroEquiv K Y (n + 1)
      (UnbasedPointedMapping.stageDifferentialZero K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n a) =
    (UnbasedPointedMapping.stageDifferential K Y n 0
      (stageFiberLoopPositiveEquiv K Y n 0 a))⁻¹ := by
  let X := fun k ↦ (UnbasedPointedMapping.tower K Y).obj (op k)
  let Z := fun k ↦ (UnbasedPointedMapping.tower K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).obj (op k)
  let p := fun k ↦ (UnbasedPointedMapping.tower K Y).map (homOfLE (Nat.le_succ k)).op
  let q := fun k ↦ (UnbasedPointedMapping.tower K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).map
    (homOfLE (Nat.le_succ k)).op
  let pl := fun k ↦ PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (p k)
  have : ∀ k, KanComplex (X k).right := fun k ↦
    UnbasedPointedMapping.tower_level_kanComplex K Y (op k)
  have : ∀ k, KanComplex (Z k).right := fun k ↦
    UnbasedPointedMapping.tower_level_kanComplex K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) (op k)
  have : ∀ k, KanComplex (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (X k)).right := fun k ↦ inferInstance
  have : ∀ k, Fibration (p k).right := fun k ↦
    UnbasedPointedMapping.tower_map_fibration K Y _
  have : ∀ k, Fibration (q k).right := fun k ↦
    UnbasedPointedMapping.tower_map_fibration K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) _
  have : ∀ k, Fibration (pl k).right := fun k ↦ inferInstance
  let e := fun k ↦ UnbasedPointedMapping.loopSwap (K.skeleton (k + 1) : SSet.{u}) Y
  have h : ∀ k, pl k ≫ (e k).hom = (e (k + 1)).hom ≫ q k := fun k ↦
    UnbasedPointedMapping.loopSwap_pre (UnbasedPointedMapping.skeletalInclusion K k) Y
  let C := fun k ↦ PointedFiberComparison.iso (pl k) (q k) (e (k + 1)) (e k) (h k)
  let b := pointedGroupMap 0 (C n).inv a
  have ha : pointedGroupMap 0 (C n).hom b = a := by
    dsimp only [b]
    rw [← pointedGroupMap_comp, Iso.inv_hom_id, pointedGroupMap_id]
  have hn := PointedFibrationTower.differentialZero_natural
    (X := fun k ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (X k)) (Y := Z) pl q (fun k ↦ (e k).hom) h n b
  change pointedHomotopyMap 0 (C (n + 1)).hom
    (PointedFibrationTower.differentialZero (fun k ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (X k)) pl n b) =
      PointedFibrationTower.differentialZero Z q n
        (pointedGroupMap 0 (C n).hom b) at hn
  rw [ha] at hn
  rw [stageFiberLoopZeroEquiv_apply, stageFiberLoopPositiveEquiv_eq]
  change loopZeroHomotopyEquiv (pointedFiber (p (n + 1)))
    (pointedHomotopyMap 0 ((C (n + 1)).inv ≫ (loopPointedFiberIso (p (n + 1))).inv)
      (PointedFibrationTower.differentialZero Z q n a)) =
    (PointedFibrationTower.differential X p n 0
      (loopPositiveHomotopyEquiv (pointedFiber (p n)) 0
        (pointedGroupMap 0 ((C n).inv ≫ (loopPointedFiberIso (p n)).inv) a)))⁻¹
  rw [← hn, pointedHomotopyMap_comp,
    ← pointedHomotopyMap_comp 0 (C (n + 1)).hom (C (n + 1)).inv,
    Iso.hom_inv_id, pointedHomotopyMap_id, pointedGroupMap_comp]
  exact PointedFibrationTower.differential_loopZero X p n b

end SkeletalCellAttachment
end
end SerrePositivity.KST.Spectra
