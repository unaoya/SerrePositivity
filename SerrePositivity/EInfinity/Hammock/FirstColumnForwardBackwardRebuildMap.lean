module

public import SerrePositivity.EInfinity.Hammock.FirstColumnForwardBackwardRebuild
public import SerrePositivity.EInfinity.Hammock.ZigzagMovingAppendFixed

/-!
# 元の混合二方向の切断の縦射の貼り戻し

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
def forwardBackwardRebuildTail {Z Z' : forwardBackwardTarget W w X Y} (h : Z ⟶ Z') :
    BoundaryHom (TwoSidedGrothendieck.baseMap h).hom
      ((TwoSidedGrothendieck.right _ _ Z).2) ((TwoSidedGrothendieck.right _ _ Z').2) :=
  backwardHomToMoving (hf := (TwoSidedGrothendieck.baseMap h).property)
    ((TwoSidedGrothendieck.rightMap h).2)

def forwardBackwardRebuildHead {Z Z' : forwardBackwardTarget W w X Y} (h : Z ⟶ Z') :
    Zigzag.MovingHom (ForwardZigzag.obj (W := W) ((TwoSidedGrothendieck.right _ _ Z).1).as)
      (ForwardZigzag.obj (W := W) ((TwoSidedGrothendieck.right _ _ Z').1).as) where
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
    have hc := Discrete.eq_of_hom ((TwoSidedGrothendieck.rightMap h).1)
    change ((TwoSidedGrothendieck.right _ _ Z).1).as ≫ (TwoSidedGrothendieck.baseMap h).hom =
      ((TwoSidedGrothendieck.right _ _ Z').1).as at hc
    change ((TwoSidedGrothendieck.right _ _ Z).1).as ≫ (TwoSidedGrothendieck.baseMap h).hom =
      (𝟙 X) ≫ ((TwoSidedGrothendieck.right _ _ Z').1).as
    simpa only [Category.id_comp] using hc

lemma forwardBackwardRebuild_joint_map {Z Z' : forwardBackwardTarget W w X Y} (h : Z ⟶ Z') :
    HEq ((forwardBackwardRebuildHead W w X Y h).app (Fin.last (Word.single .forward).length))
      ((forwardBackwardRebuildTail W w X Y h).hom.app 0) := by
  change HEq (TwoSidedGrothendieck.baseMap h).hom
    ((forwardBackwardRebuildTail W w X Y h).hom.app 0)
  exact ((conj_eqToHom_iff_heq _ _ ((TwoSidedGrothendieck.right _ _ Z).2).first
    ((TwoSidedGrothendieck.right _ _ Z').2).first).mp
      (forwardBackwardRebuildTail W w X Y h).first).symm

def forwardBackwardRebuildMap {Z Z' : forwardBackwardTarget W w X Y} (h : Z ⟶ Z') :
    forwardBackwardRebuild W w X Y Z ⟶ forwardBackwardRebuild W w X Y Z' :=
  ZigzagAppend.Moving.fixedMap (forwardBackwardRebuildHead W w X Y h)
    (forwardBackwardRebuildTail W w X Y h).hom
    (forwardBackwardRebuild_joint_map W w X Y h)
    rfl (forwardBackwardRebuildTail W w X Y h).last

lemma forwardBackwardRebuildMap_joint {Z Z' : forwardBackwardTarget W w X Y} (h : Z ⟶ Z') :
    HEq ((forwardBackwardRebuildMap W w X Y h).app
      (Word.leftVertex (Word.single .forward) (Word.cons .backward w)
        (Fin.last (Word.single .forward).length))) (TwoSidedGrothendieck.baseMap h).hom :=
  ZigzagAppend.Moving.app_left_heq (forwardBackwardRebuildHead W w X Y h)
    (forwardBackwardRebuildTail W w X Y h).hom (Fin.last (Word.single .forward).length)

lemma forwardBackwardRebuildMap_tail {Z Z' : forwardBackwardTarget W w X Y} (h : Z ⟶ Z')
    (j : Fin ((Word.cons .backward w).length + 1)) :
    HEq ((forwardBackwardRebuildMap W w X Y h).app
      (Word.rightVertex (Word.single .forward) (Word.cons .backward w) j))
      ((forwardBackwardRebuildTail W w X Y h).hom.app j) :=
  ZigzagAppend.Moving.app_right_heq (forwardBackwardRebuildHead W w X Y h)
    (forwardBackwardRebuildTail W w X Y h).hom (forwardBackwardRebuild_joint_map W w X Y h) j
end SerrePositivity.EInfinity.Hammock.FirstColumn
