module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FirstColumnForwardForwardRebuild
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagMovingAppendFixed

/-!
# 元の前向き切断の縦射の貼り戻し

概要：二方向 Grothendieck 圏の射を元の先頭列と残りの縦射へ戻して貼る。
方針：元の底の指定射と両係数の射をそのまま使い、接合点と残りの全成分を回収する。
規約：元の全縦射と全正方形を保持する。
使われ方：DK9.4・10.3の切断関手の充満性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory Opposite Zigzag.FirstBoundary
variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (w : Word) (X Y : C)
def forwardForwardRebuildTail {Z Z' : forwardForwardTarget W w X Y} (h : Z ⟶ Z') :
    BoundaryHom (TwoSidedGrothendieck.baseMap h).hom
      (TwoSidedGrothendieck.left _ _ Z) (TwoSidedGrothendieck.left _ _ Z') :=
  forwardHomToMoving (TwoSidedGrothendieck.baseMap h).property (TwoSidedGrothendieck.leftMap h)

def forwardForwardRebuildHead {Z Z' : forwardForwardTarget W w X Y} (h : Z ⟶ Z') :
    Zigzag.MovingHom (ForwardZigzag.obj (W := W) (TwoSidedGrothendieck.right _ _ Z).as)
      (ForwardZigzag.obj (W := W) (TwoSidedGrothendieck.right _ _ Z').as) where
  app := Fin.cases (𝟙 X) (fun _ => (TwoSidedGrothendieck.baseMap h).hom)
  app_mem j := by
    change Fin 2 at j
    cases j using Fin.cases with
    | zero => exact W.id_mem X
    | succ _ => exact (TwoSidedGrothendieck.baseMap h).property
  comm i := by
    change Fin 1 at i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    have hc := Discrete.eq_of_hom (TwoSidedGrothendieck.rightMap h)
    change (TwoSidedGrothendieck.right _ _ Z).as ≫ (TwoSidedGrothendieck.baseMap h).hom =
      (TwoSidedGrothendieck.right _ _ Z').as at hc
    change (TwoSidedGrothendieck.right _ _ Z).as ≫ (TwoSidedGrothendieck.baseMap h).hom =
      (𝟙 X) ≫ (TwoSidedGrothendieck.right _ _ Z').as
    simpa only [Category.id_comp] using hc

lemma forwardForwardRebuild_joint_map {Z Z' : forwardForwardTarget W w X Y} (h : Z ⟶ Z') :
    HEq ((forwardForwardRebuildHead W w X Y h).app (Fin.last (Word.single .forward).length))
      ((forwardForwardRebuildTail W w X Y h).hom.app 0) := by
  change HEq (TwoSidedGrothendieck.baseMap h).hom
    ((forwardForwardRebuildTail W w X Y h).hom.app 0)
  exact ((conj_eqToHom_iff_heq _ _ (TwoSidedGrothendieck.left _ _ Z).first
    (TwoSidedGrothendieck.left _ _ Z').first).mp
      (forwardForwardRebuildTail W w X Y h).first).symm

def forwardForwardRebuildMap {Z Z' : forwardForwardTarget W w X Y} (h : Z ⟶ Z') :
    forwardForwardRebuild W w X Y Z ⟶ forwardForwardRebuild W w X Y Z' :=
  ZigzagAppend.Moving.fixedMap (forwardForwardRebuildHead W w X Y h)
    (forwardForwardRebuildTail W w X Y h).hom
    (forwardForwardRebuild_joint_map W w X Y h)
    rfl (forwardForwardRebuildTail W w X Y h).last

lemma forwardForwardRebuildMap_joint {Z Z' : forwardForwardTarget W w X Y} (h : Z ⟶ Z') :
    HEq ((forwardForwardRebuildMap W w X Y h).app
      (Word.leftVertex (Word.single .forward) (Word.cons .forward w)
        (Fin.last (Word.single .forward).length))) (TwoSidedGrothendieck.baseMap h).hom :=
  ZigzagAppend.Moving.app_left_heq (forwardForwardRebuildHead W w X Y h)
    (forwardForwardRebuildTail W w X Y h).hom (Fin.last (Word.single .forward).length)

lemma forwardForwardRebuildMap_tail {Z Z' : forwardForwardTarget W w X Y} (h : Z ⟶ Z')
    (j : Fin ((Word.cons .forward w).length + 1)) :
    HEq ((forwardForwardRebuildMap W w X Y h).app
      (Word.rightVertex (Word.single .forward) (Word.cons .forward w) j))
      ((forwardForwardRebuildTail W w X Y h).hom.app j) :=
  ZigzagAppend.Moving.app_right_heq (forwardForwardRebuildHead W w X Y h)
    (forwardForwardRebuildTail W w X Y h).hom (forwardForwardRebuild_joint_map W w X Y h) j
end SerrePositivity.EInfinity.Hammock.FirstColumn
