module

public import SerrePositivity.KST.Spectra.RestrictionLoopFiber
public import SerrePositivity.KST.Spectra.SkeletalFiberLoopPositive
public import SerrePositivity.KST.Spectra.PositiveLoopNaturality

/-!
概要：骨格の fiber の loop 交換を、既存のセル商による係数表示と同定する。
方針：相対 cofiber の比較に、セル商の源同型の自然性を合成する。
規約：通常の circle による loop。既存の係数表示の向きを保つ。
使われ方：Goerss–Jardine VIII §1。骨格の微分の高次数への移送。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 骨格の fiber の loop と loop 値の骨格の fiber の同型。 -/
def stageFiberLoopIso (K : SSet.{u}) (Y : PointedSimplicialSet.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (UnbasedPointedMapping.stageFiber K Y n) ≅
      UnbasedPointedMapping.stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n :=
  UnbasedPointedMapping.restrictionLoopIso (UnbasedPointedMapping.skeletalInclusion K n) Y

/-- 概要：セル商による骨格 fiber の表示は loop の交換と可換。
方針：相対 cofiber の交換式と、セル商への源同型の自然性を順に適用する。
規約：厳密な点つき射の等式。
使われ方：Goerss–Jardine VIII §1。係数表示と塔の loop 比較の整合性。 -/
@[reassoc]
lemma stageFiberLoopIso_cell (K : SSet.{u}) (Y : PointedSimplicialSet.{u}) (n : ℕ) :
    PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (stageFiberCellIso K Y n).hom ≫
      (stageFiberLoopIso K Y n).hom =
    (PointedMapping.loopSwap (cellCofiber K (n + 1)) Y).hom ≫
      (stageFiberCellIso K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).hom := by
  have h := UnbasedPointedMapping.restrictionLoopIso_cofiber
    (UnbasedPointedMapping.skeletalInclusion K n) Y
  have hs := PointedMapping.loopSwap_pre
    (A := UnbasedPointedMapping.skeletalRelativeSource K n)
    (B := cellCofiber K (n + 1)) (relativeCofiberIso K (n + 1)).hom Y
  dsimp only [stageFiberCellIso, Iso.trans_hom]
  change PointedObject.basedHomMap PointedSimplicialSet.circle.{u}
    ((MonoidalClosed.pre (relativeCofiberIso K (n + 1)).hom).app Y ≫
      (UnbasedPointedMapping.stageFiberIso K Y n).hom) ≫ _ =
    (PointedMapping.loopSwap (cellCofiber K (n + 1)) Y).hom ≫
      (MonoidalClosed.pre (relativeCofiberIso K (n + 1)).hom).app (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) ≫ _
  rw [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre,
    ← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
  change (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u}).map
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (relativeCofiberIso K (n + 1)).hom Y ≫
      (UnbasedPointedMapping.stageFiberIso K Y n).hom) ≫ _ = _
  rw [Functor.map_comp, Category.assoc]
  erw [h]
  rw [← Category.assoc]
  change (PointedObject.basedHomMap PointedSimplicialSet.circle.{u}
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (relativeCofiberIso K (n + 1)).hom Y) ≫
      (PointedMapping.loopSwap (UnbasedPointedMapping.skeletalRelativeSource K n) Y).hom) ≫
        (UnbasedPointedMapping.stageFiberIso K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).hom = _
  rw [hs, Category.assoc]

/-- 逆の交換同型と loop に送ったセル表示の可換式。 -/
@[reassoc]
lemma stageFiberLoopIso_cell_inv (K : SSet.{u}) (Y : PointedSimplicialSet.{u}) (n : ℕ) :
    (PointedMapping.loopSwap (cellCofiber K (n + 1)) Y).inv ≫
      PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (stageFiberCellIso K Y n).hom =
    (stageFiberCellIso K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).hom ≫ (stageFiberLoopIso K Y n).inv := by
  apply (cancel_epi (PointedMapping.loopSwap (cellCofiber K (n + 1)) Y).hom).mp
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← stageFiberLoopIso_cell,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- 概要：既存の正次数係数の loop 比較は、fiber の厳密な loop 交換による比較そのもの。
方針：セル表示の交換式を群へ送り、loop の群同型の標的自然性を合成する。
規約：各元の値を比較する。符号や自己同型による補正を加えない。
使われ方：Goerss–Jardine VIII §1。幾何的な塔の微分を既存の係数へ移す界面。 -/
lemma stageFiberLoopPositiveEquiv_eq (K : SSet.{u}) (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (n r : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).right r
      (UnbasedPointedMapping.stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).basepoint) :
    stageFiberLoopPositiveEquiv K Y n r a =
    loopPositiveHomotopyEquiv (UnbasedPointedMapping.stageFiber K Y n) r
      (pointedGroupMap r (stageFiberLoopIso K Y n).inv a) := by
  let b := pointedGroupMap r (stageFiberCellIso K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).inv a
  have ha : pointedGroupMap r (stageFiberCellIso K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).hom b = a := by
    dsimp only [b]
    rw [← pointedGroupMap_comp, Iso.inv_hom_id, pointedGroupMap_id]
  have hm := congrArg (fun f ↦ pointedGroupMap r f b) (stageFiberLoopIso_cell_inv K Y n)
  simp only [pointedGroupMap_comp, ha] at hm
  rw [stageFiberLoopPositiveEquiv_apply, PointedMapping.loopPositiveEquiv_apply]
  change pointedGroupMap (r + 1) (stageFiberCellIso K Y n).hom
    (loopPositiveHomotopyEquiv (PointedObject.basedHom (cellCofiber K (n + 1)) Y) r
      (pointedGroupMap r (PointedMapping.loopSwap (cellCofiber K (n + 1)) Y).inv b)) = _
  rw [← loopPositiveHomotopyEquiv_natural, hm]

end
end SerrePositivity.KST.Spectra.SkeletalCellAttachment
