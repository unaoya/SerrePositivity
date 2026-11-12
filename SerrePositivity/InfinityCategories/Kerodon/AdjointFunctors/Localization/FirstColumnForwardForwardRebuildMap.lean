module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstColumnForwardForwardRebuild
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendFixed

/-!
# 元の前向き切断の縦射の貼り戻し

概要：二方向 Grothendieck 圏の射を元の先頭列と残りの縦射へ戻して貼る。
方針：元の底の指定射と両係数の射をそのまま使い、接合点と残りの全成分を回収する。
規約：元の全縦射と全正方形を保持する。
使われ方：DK9.4・10.3の切断関手の充満性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory Opposite Zigzag.FirstBoundary
variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : C)
def forwardForwardRebuildTail {Z Z' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardTarget W w X Y} (h : Z ⟶ Z') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BoundaryHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.baseMap h).hom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.left _ _ Z) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.left _ _ Z') :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardHomToMoving (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.baseMap h).property (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.leftMap h)

def forwardForwardRebuildHead {Z Z' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardTarget W w X Y} (h : Z ⟶ Z') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.right _ _ Z).as)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.right _ _ Z').as) where
  app := Fin.cases (𝟙 X) (fun _ => (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.baseMap h).hom)
  app_mem j := by
    change Fin 2 at j
    cases j using Fin.cases with
    | zero => exact W.id_mem X
    | succ _ => exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.baseMap h).property
  comm i := by
    change Fin 1 at i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    have hc := Discrete.eq_of_hom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.rightMap h)
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.right _ _ Z).as ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.baseMap h).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.right _ _ Z').as at hc
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.right _ _ Z).as ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.baseMap h).hom =
      (𝟙 X) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.right _ _ Z').as
    simpa only [Category.id_comp] using hc

lemma forwardForwardRebuild_joint_map {Z Z' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardTarget W w X Y} (h : Z ⟶ Z') :
    HEq ((forwardForwardRebuildHead W w X Y h).app (Fin.last (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward).length))
      ((forwardForwardRebuildTail W w X Y h).hom.app 0) := by
  change HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.baseMap h).hom
    ((forwardForwardRebuildTail W w X Y h).hom.app 0)
  exact ((conj_eqToHom_iff_heq _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.left _ _ Z).first
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.left _ _ Z').first).mp
      (forwardForwardRebuildTail W w X Y h).first).symm

def forwardForwardRebuildMap {Z Z' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardTarget W w X Y} (h : Z ⟶ Z') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardRebuild W w X Y Z ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardRebuild W w X Y Z' :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedMap (forwardForwardRebuildHead W w X Y h)
    (forwardForwardRebuildTail W w X Y h).hom
    (forwardForwardRebuild_joint_map W w X Y h)
    rfl (forwardForwardRebuildTail W w X Y h).last

lemma forwardForwardRebuildMap_joint {Z Z' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardTarget W w X Y} (h : Z ⟶ Z') :
    HEq ((forwardForwardRebuildMap W w X Y h).app
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w)
        (Fin.last (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward).length))) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.baseMap h).hom :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_left_heq (forwardForwardRebuildHead W w X Y h)
    (forwardForwardRebuildTail W w X Y h).hom (Fin.last (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward).length)

lemma forwardForwardRebuildMap_tail {Z Z' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardTarget W w X Y} (h : Z ⟶ Z')
    (j : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w).length + 1)) :
    HEq ((forwardForwardRebuildMap W w X Y h).app
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w) j))
      ((forwardForwardRebuildTail W w X Y h).hom.app j) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_right_heq (forwardForwardRebuildHead W w X Y h)
    (forwardForwardRebuildTail W w X Y h).hom (forwardForwardRebuild_joint_map W w X Y h) j
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
