module

public import SerrePositivity.KST.LocalizingInvariants.ProCospanBaseChange
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackFunctor
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackIdentity

/-!
概要：元の代数の pro 逆を、元の経路模型の塔の実 pro 逆へ送る。
方針：実 cospan 図式の逆に厳密模型関手を適用し、元の右射影との合成式を保つ。
規約：一般の ∞ 極限保存を入力しない。使われ方：零切断の実逆による拡大の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
open ProExcision
variable (R : Type u) [CommRing R] {X Y Z : Tower (Mon (Complex R))}
  (f : LevelHom X Y) (g : LevelHom Z Y)

def modelTower : Tower (Mon (Complex R)) :=
  (TowerDiagram.cospanTower f g).map (diagramFunctor R)

def modelBaseMap : LevelHom (modelTower R f g) (modelTower R (LevelHom.id Y) g) :=
  (TowerDiagram.cospanBaseMap f g).map (diagramFunctor R)

def rightProjection : LevelHom (modelTower R f g) Z where
  app i := right R (f.app i) (g.app i)
  naturality h := diagramMap_right R ((TowerDiagram.cospanTower f g).transition h)

def leftProjection : LevelHom (modelTower R f g) X where
  app i := left R (f.app i) (g.app i)
  naturality h := diagramMap_left R ((TowerDiagram.cospanTower f g).transition h)

lemma modelBaseMap_comp_right :
    (modelBaseMap R f g).comp (rightProjection R (LevelHom.id Y) g) =
      rightProjection R f g := by
  apply ProSpectrum.levelHom_ext
  intro i
  change diagramMap R ((TowerDiagram.cospanBaseMap f g).app i) ≫
      right R (𝟙 (Y.obj i)) (g.app i) = right R (f.app i) (g.app i)
  exact (diagramMap_right R ((TowerDiagram.cospanBaseMap f g).app i)).trans
    (Category.comp_id _)

lemma modelBaseMap_isProIso (hf : IsProIso f) : IsProIso (modelBaseMap R f g) :=
  (TowerDiagram.cospanBaseMap_isProIso f g hf).map (diagramFunctor R)

lemma rightProjection_identity_quasiIso (i : ℕ) :
    QuasiIso ((rightProjection R (LevelHom.id Y) g).app i).hom :=
  right_identity_quasiIso R (g.app i)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
