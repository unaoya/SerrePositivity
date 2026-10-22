module

public import SerrePositivity.KST.LocalizingInvariants.ProMonoidPullbackBaseChange

/-!
概要：元の塔の厳密な可換正方形から、通常の代数 pullback への元の実レベル射を作る。
方針：各段の元の二射を普遍 lift へ渡し、両射影の一意性で自然性を示す。
規約：新しい源の表示を仮定しない。使われ方：底を揃えた有限 Postnikov 射。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits
namespace SerrePositivity.KST.LocalizingInvariants.MonoidPullback
open ProExcision
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasPullbacks C]
  {W X Y Z : Tower (Mon C)} (f : LevelHom X Y) (g : LevelHom Z Y)
  (a : LevelHom W X) (b : LevelHom W Z) (hs : a.comp f = b.comp g)

def squareLiftApp (i : ℕ) : W.obj i ⟶ (pullbackTower f g).obj i :=
  lift (f.app i) (g.app i) (a.app i) (b.app i) (congrArg (fun t => t.app i) hs)

lemma squareLiftApp_fst (i : ℕ) :
    squareLiftApp f g a b hs i ≫ fst (f.app i) (g.app i) = a.app i := lift_fst _ _ _ _ _

lemma squareLiftApp_snd (i : ℕ) :
    squareLiftApp f g a b hs i ≫ snd (f.app i) (g.app i) = b.app i := lift_snd _ _ _ _ _

lemma squareLiftApp_naturality {m i : ℕ} (hi : i ≤ m) :
    W.transition hi ≫ squareLiftApp f g a b hs i =
      squareLiftApp f g a b hs m ≫ (pullbackTower f g).transition hi := by
  have hl : (pullbackTower f g).transition hi ≫ fst (f.app i) (g.app i) =
      fst (f.app m) (g.app m) ≫ X.transition hi :=
    diagramMap_fst ((TowerDiagram.cospanTower f g).transition hi)
  have hr : (pullbackTower f g).transition hi ≫ snd (f.app i) (g.app i) =
      snd (f.app m) (g.app m) ≫ Z.transition hi :=
    diagramMap_snd ((TowerDiagram.cospanTower f g).transition hi)
  apply hom_ext (f.app i) (g.app i)
  · rw [Category.assoc, squareLiftApp_fst, Category.assoc, hl,
      ← Category.assoc, squareLiftApp_fst]
    exact a.naturality hi
  · rw [Category.assoc, squareLiftApp_snd, Category.assoc, hr,
      ← Category.assoc, squareLiftApp_snd]
    exact b.naturality hi

def squareLift : LevelHom W (pullbackTower f g) where
  app := squareLiftApp f g a b hs
  naturality hi := squareLiftApp_naturality f g a b hs hi

lemma squareLift_comp_left : (squareLift f g a b hs).comp (leftProjection f g) = a := by
  apply ProSpectrum.levelHom_ext
  intro i
  exact squareLiftApp_fst f g a b hs i

lemma squareLift_comp_right : (squareLift f g a b hs).comp (rightProjection f g) = b := by
  apply ProSpectrum.levelHom_ext
  intro i
  exact squareLiftApp_snd f g a b hs i

end SerrePositivity.KST.LocalizingInvariants.MonoidPullback
