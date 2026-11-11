module

public import SerrePositivity.KST.Spectra.SkeletalLoopFiberIso
public import SerrePositivity.KST.Spectra.SkeletalFiberDifferential
public import SerrePositivity.KST.Spectra.PointedTowerLoopDifferential
public import SerrePositivity.KST.Spectra.PointedTowerDifferentialNaturality

/-!
概要：骨格の塔の微分は既存の loop 値の係数比較と逆符号で交換する。
方針：写像空間の交換の自然同型で塔の微分を移し、一般の塔の反可換式を適用する。
規約：既存のセル商による群同型を使用する。
使われ方：Goerss–Jardine VIII §1。正規化交代微分との全正次数での比較。
-/

@[expose] public section
universe u
open CategoryTheory Opposite SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000 in
-- 塔と fiber の厳密な同型を展開した可換図式の照合に必要。
/-- 概要：実際の骨格微分と loop 値の既存群同型の反可換式。
方針：loop に送った塔と loop 値の塔の自然同型を通して、一般の塔の式を移す。
規約：r は出力側の正次数の添字。
使われ方：Goerss–Jardine VIII §1。係数微分の次数帰納の正符号と負符号の分離。 -/
theorem stageDifferential_loopPositive (K : SSet.{u}) (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (n r : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).right (r + 1)
      (UnbasedPointedMapping.stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).basepoint) :
    stageFiberLoopPositiveEquiv K Y (n + 1) r
      (UnbasedPointedMapping.stageDifferential K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n r a) =
    (UnbasedPointedMapping.stageDifferential K Y n (r + 1)
      (stageFiberLoopPositiveEquiv K Y n (r + 1) a))⁻¹ := by
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
  let b := pointedGroupMap (r + 1) (C n).inv a
  have ha : pointedGroupMap (r + 1) (C n).hom b = a := by
    dsimp only [b]
    rw [← pointedGroupMap_comp, Iso.inv_hom_id, pointedGroupMap_id]
  have hn := PointedFibrationTower.differential_natural
    (X := fun k ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (X k)) (Y := Z) pl q (fun k ↦ (e k).hom) h n r b
  change pointedGroupMap r (C (n + 1)).hom
    (PointedFibrationTower.differential (fun k ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (X k)) pl n r b) =
      PointedFibrationTower.differential Z q n r
        (pointedGroupMap (r + 1) (C n).hom b) at hn
  rw [ha] at hn
  rw [stageFiberLoopPositiveEquiv_eq, stageFiberLoopPositiveEquiv_eq]
  change loopPositiveHomotopyEquiv (pointedFiber (p (n + 1))) r
    (pointedGroupMap r ((C (n + 1)).inv ≫ (loopPointedFiberIso (p (n + 1))).inv)
      (PointedFibrationTower.differential Z q n r a)) =
    (PointedFibrationTower.differential X p n (r + 1)
      (loopPositiveHomotopyEquiv (pointedFiber (p n)) (r + 1)
        (pointedGroupMap (r + 1) ((C n).inv ≫ (loopPointedFiberIso (p n)).inv) a)))⁻¹
  rw [← hn, pointedGroupMap_comp, ← pointedGroupMap_comp r (C (n + 1)).hom,
    Iso.hom_inv_id, pointedGroupMap_id,
    PointedFibrationTower.differential_loopPositive X p n r b, pointedGroupMap_comp]

end
end SerrePositivity.KST.Spectra.SkeletalCellAttachment
