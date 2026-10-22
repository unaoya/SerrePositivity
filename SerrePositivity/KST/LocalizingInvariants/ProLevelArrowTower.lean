module

public import SerrePositivity.KST.LocalizingInvariants.ProTowerNatMap

/-!
概要：元の塔の実レベル射を、元の二つの遷移を持つ矢印の塔にする。
方針：元の自然性の四角形を矢印の射へ送り、二射影で塔の関手則を検証する。
規約：元の添字・対象・射を変更しない。使われ方：実因子分解関手への元の塔の入力。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory
namespace SerrePositivity.KST.LocalizingInvariants.TowerDiagram
open ProExcision
variable {C : Type u} [Category.{v} C] {X Y : Tower C}

def arrowTower (f : LevelHom X Y) : Tower (Arrow C) where
  obj n := Arrow.mk (f.app n)
  transition h := Arrow.homMk (X.transition h) (Y.transition h) (f.naturality h)
  transition_self n := Arrow.hom_ext _ _ (X.transition_self n) (Y.transition_self n)
  transition_comp hm hn := Arrow.hom_ext _ _ (X.transition_comp hm hn) (Y.transition_comp hm hn)

lemma arrowTower_left (f : LevelHom X Y) : (arrowTower f).map Arrow.leftFunc = X := rfl
lemma arrowTower_right (f : LevelHom X Y) : (arrowTower f).map Arrow.rightFunc = Y := rfl

end SerrePositivity.KST.LocalizingInvariants.TowerDiagram
