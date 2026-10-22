module

public import SerrePositivity.KST.LocalizingInvariants.MonoidPullbackFunctor
public import SerrePositivity.KST.LocalizingInvariants.ProCospanBaseChange

/-!
概要：元の左脚の実 pro 逆から、通常の代数 pullback の右射影の実 pro 逆を構成する。
方針：元の cospan 図式の逆へ通常 pullback 関手を適用し、恒等脚の射影で戻す。
規約：局所化と連結度の仮定は不要。使われ方：零切断を底に持つ実拡大の比較。
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
  {X Y Z : Tower (Mon C)} (f : LevelHom X Y) (g : LevelHom Z Y)

def pullbackTower : Tower (Mon C) := (TowerDiagram.cospanTower f g).map diagramFunctor

def baseMap : LevelHom (pullbackTower f g) (pullbackTower (LevelHom.id Y) g) :=
  (TowerDiagram.cospanBaseMap f g).map diagramFunctor

def rightProjection : LevelHom (pullbackTower f g) Z where
  app i := snd (f.app i) (g.app i)
  naturality hi := diagramMap_snd ((TowerDiagram.cospanTower f g).transition hi)

def leftProjection : LevelHom (pullbackTower f g) X where
  app i := fst (f.app i) (g.app i)
  naturality hi := diagramMap_fst ((TowerDiagram.cospanTower f g).transition hi)

lemma baseMap_comp_right : (baseMap f g).comp (rightProjection (LevelHom.id Y) g) =
    rightProjection f g := by
  apply ProSpectrum.levelHom_ext
  intro i
  exact (diagramMap_snd ((TowerDiagram.cospanBaseMap f g).app i)).trans (Category.comp_id _)

lemma snd_identity_isIso {B D : Mon C} (g : D ⟶ B) : IsIso (snd (𝟙 B) g) := by
  have : IsIso ((Mon.forget C).map (snd (𝟙 B) g)) := by
    change IsIso (pullback.snd (𝟙 B.X) g.hom)
    infer_instance
  exact isIso_of_reflects_iso (snd (𝟙 B) g) (Mon.forget C)

lemma rightProjection_isProIso (hf : IsProIso f) : IsProIso (rightProjection f g) := by
  have : ∀ i, IsIso ((rightProjection (LevelHom.id Y) g).app i) :=
    fun i => snd_identity_isIso (g.app i)
  have hc := ((TowerDiagram.cospanBaseMap_isProIso f g hf).map diagramFunctor).comp
    (TowerDiagram.isProIso_of_levelwiseIso (rightProjection (LevelHom.id Y) g))
  change IsProIso ((baseMap f g).comp (rightProjection (LevelHom.id Y) g)) at hc
  rw [baseMap_comp_right] at hc
  exact hc

end SerrePositivity.KST.LocalizingInvariants.MonoidPullback
