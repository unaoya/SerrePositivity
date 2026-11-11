module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstColumnBackwardBackwardRebuild
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendFixed

/-!
# 元の後向き二列の全縦射の貼り戻し

概要：元の指定 Hom の等式と残りの全縦射を同じ接合点で貼り戻す。
方針：元の底の指定射と両係数の射を使い、接合点と残りの全成分を回収する。
規約：指定 Hom の元の構造と全正方形を保持する。
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
def backwardBackwardRebuildTail {Z Z' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardTarget W w X Y} (h : Z ⟶ Z') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BoundaryHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.baseMap h).hom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.right _ _ Z) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.right _ _ Z') :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardHomToMoving (hf := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.baseMap h).property)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.rightMap h)

def backwardBackwardRebuildHead {Z Z' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardTarget W w X Y} (h : Z ⟶ Z') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.obj (W := W) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.left _ _ Z).as.hom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.left _ _ Z).as.property)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.obj (W := W) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.left _ _ Z').as.hom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.left _ _ Z').as.property) where
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
    have hc : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.left _ _ Z).as = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.baseMap h ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.left _ _ Z').as := Discrete.eq_of_hom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.leftMap h)
    have hc' := congrArg (fun e : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.base _ _ Z ⟶
      (⟨X⟩ : WideSubcategory W) => e.hom) hc
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.left _ _ Z).as.hom ≫ (𝟙 X) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.baseMap h).hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.left _ _ Z').as.hom
    simpa only [WideSubcategory.comp_def, Category.comp_id] using hc'

lemma backwardBackwardRebuild_joint_map {Z Z' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardTarget W w X Y} (h : Z ⟶ Z') :
    HEq ((backwardBackwardRebuildHead W w X Y h).app (Fin.last (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward).length))
      ((backwardBackwardRebuildTail W w X Y h).hom.app 0) := by
  change HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.baseMap h).hom
    ((backwardBackwardRebuildTail W w X Y h).hom.app 0)
  exact ((conj_eqToHom_iff_heq _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.right _ _ Z).first
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.right _ _ Z').first).mp
      (backwardBackwardRebuildTail W w X Y h).first).symm

def backwardBackwardRebuildMap {Z Z' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardTarget W w X Y} (h : Z ⟶ Z') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardRebuild W w X Y Z ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardRebuild W w X Y Z' :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedMap (backwardBackwardRebuildHead W w X Y h)
    (backwardBackwardRebuildTail W w X Y h).hom (backwardBackwardRebuild_joint_map W w X Y h)
    rfl (backwardBackwardRebuildTail W w X Y h).last

lemma backwardBackwardRebuildMap_joint {Z Z' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardTarget W w X Y} (h : Z ⟶ Z') :
    HEq ((backwardBackwardRebuildMap W w X Y h).app
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w)
        (Fin.last (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward).length))) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.baseMap h).hom :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_left_heq (backwardBackwardRebuildHead W w X Y h)
    (backwardBackwardRebuildTail W w X Y h).hom (Fin.last (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward).length)
lemma backwardBackwardRebuildMap_tail {Z Z' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardTarget W w X Y} (h : Z ⟶ Z')
    (j : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w).length + 1)) :
    HEq ((backwardBackwardRebuildMap W w X Y h).app
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) j))
      ((backwardBackwardRebuildTail W w X Y h).hom.app j) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_right_heq (backwardBackwardRebuildHead W w X Y h)
    (backwardBackwardRebuildTail W w X Y h).hom (backwardBackwardRebuild_joint_map W w X Y h) j
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
