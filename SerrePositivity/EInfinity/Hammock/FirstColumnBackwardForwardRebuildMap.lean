module

public import SerrePositivity.EInfinity.Hammock.FirstColumnBackwardForwardRebuild
public import SerrePositivity.EInfinity.Hammock.ZigzagMovingAppendFixed

/-!
# 元の混合二方向 −+の全縦射の貼り戻し

概要：元の指定 Hom の等式と残りの全縦射を同じ接合点で貼り戻す。
方針：元の底の指定射と両係数の射を使い、接合点と残りの全成分を回収する。
規約：指定 Hom の元の構造と全正方形を保持する。
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
def backwardForwardRebuildTail {Z Z' : backwardForwardTarget W w X Y} (h : Z ⟶ Z') :
    BoundaryHom (TwoSidedGrothendieck.baseMap h).hom
      ((TwoSidedGrothendieck.left _ _ Z).2) ((TwoSidedGrothendieck.left _ _ Z').2) :=
  forwardHomToMoving (TwoSidedGrothendieck.baseMap h).property
    ((TwoSidedGrothendieck.leftMap h).2)

def backwardForwardRebuildHead {Z Z' : backwardForwardTarget W w X Y} (h : Z ⟶ Z') :
    Zigzag.MovingHom (BackwardZigzag.obj (W := W) ((TwoSidedGrothendieck.left _ _ Z).1).as.hom
      ((TwoSidedGrothendieck.left _ _ Z).1).as.property)
      (BackwardZigzag.obj (W := W) ((TwoSidedGrothendieck.left _ _ Z').1).as.hom
        ((TwoSidedGrothendieck.left _ _ Z').1).as.property) where
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
    have hc : ((TwoSidedGrothendieck.left _ _ Z).1).as = TwoSidedGrothendieck.baseMap h ≫
        ((TwoSidedGrothendieck.left _ _ Z').1).as := Discrete.eq_of_hom
          ((TwoSidedGrothendieck.leftMap h).1)
    have hc' := congrArg (fun e : TwoSidedGrothendieck.base _ _ Z ⟶
      (⟨X⟩ : WideSubcategory W) => e.hom) hc
    change ((TwoSidedGrothendieck.left _ _ Z).1).as.hom ≫ (𝟙 X) =
      (TwoSidedGrothendieck.baseMap h).hom ≫ ((TwoSidedGrothendieck.left _ _ Z').1).as.hom
    simpa only [WideSubcategory.comp_def, Category.comp_id] using hc'

lemma backwardForwardRebuild_joint_map {Z Z' : backwardForwardTarget W w X Y} (h : Z ⟶ Z') :
    HEq ((backwardForwardRebuildHead W w X Y h).app (Fin.last (Word.single .backward).length))
      ((backwardForwardRebuildTail W w X Y h).hom.app 0) := by
  change HEq (TwoSidedGrothendieck.baseMap h).hom
    ((backwardForwardRebuildTail W w X Y h).hom.app 0)
  exact ((conj_eqToHom_iff_heq _ _ ((TwoSidedGrothendieck.left _ _ Z).2).first
    ((TwoSidedGrothendieck.left _ _ Z').2).first).mp
      (backwardForwardRebuildTail W w X Y h).first).symm

def backwardForwardRebuildMap {Z Z' : backwardForwardTarget W w X Y} (h : Z ⟶ Z') :
    backwardForwardRebuild W w X Y Z ⟶ backwardForwardRebuild W w X Y Z' :=
  ZigzagAppend.Moving.fixedMap (backwardForwardRebuildHead W w X Y h)
    (backwardForwardRebuildTail W w X Y h).hom (backwardForwardRebuild_joint_map W w X Y h)
    rfl (backwardForwardRebuildTail W w X Y h).last

lemma backwardForwardRebuildMap_joint {Z Z' : backwardForwardTarget W w X Y} (h : Z ⟶ Z') :
    HEq ((backwardForwardRebuildMap W w X Y h).app
      (Word.leftVertex (Word.single .backward) (Word.cons .forward w)
        (Fin.last (Word.single .backward).length))) (TwoSidedGrothendieck.baseMap h).hom :=
  ZigzagAppend.Moving.app_left_heq (backwardForwardRebuildHead W w X Y h)
    (backwardForwardRebuildTail W w X Y h).hom (Fin.last (Word.single .backward).length)
lemma backwardForwardRebuildMap_tail {Z Z' : backwardForwardTarget W w X Y} (h : Z ⟶ Z')
    (j : Fin ((Word.cons .forward w).length + 1)) :
    HEq ((backwardForwardRebuildMap W w X Y h).app
      (Word.rightVertex (Word.single .backward) (Word.cons .forward w) j))
      ((backwardForwardRebuildTail W w X Y h).hom.app j) :=
  ZigzagAppend.Moving.app_right_heq (backwardForwardRebuildHead W w X Y h)
    (backwardForwardRebuildTail W w X Y h).hom (backwardForwardRebuild_joint_map W w X Y h) j
end SerrePositivity.EInfinity.Hammock.FirstColumn
