module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackProBase
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathInvertingFunctor

/-!
概要：左脚の実 pro 逆から、経路模型の元の右射影の局所化後の実 pro 逆を構成する。
方針：恒等脚への実底変更と準同型な右射影を合成し、元の右射影を正確に回収する。
規約：一般の導来極限保存は入力しない。使われ方：零切断の実逆による拡大の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
open ProExcision
variable (R : Type u) [CommRing R] {X Y Z : Tower (Mon (Complex R))}
  (f : LevelHom X Y) (g : LevelHom Z Y)
  {C : Type v} [Category.{w} C] (L : Mon (Complex R) ⥤ C)

lemma rightProjection_isProIso_of_inverts (hL : InvertsQuasiIsos R L)
    (hf : IsProIso f) : IsProIso ((rightProjection R f g).map L) := by
  have : ∀ i, IsIso (((rightProjection R (LevelHom.id Y) g).map L).app i) :=
    fun i => hL _ (rightProjection_identity_quasiIso R g i)
  have hc := ((modelBaseMap_isProIso R f g hf).map L).comp
    (TowerDiagram.isProIso_of_levelwiseIso ((rightProjection R (LevelHom.id Y) g).map L))
  rw [← TowerDiagram.levelHom_map_comp, modelBaseMap_comp_right] at hc
  exact hc

lemma rightProjection_isProIso_of_connective (hL : InvertsConnectiveQuasiIsos R L)
    (hZ : ∀ i, IsConnective R (Z.obj i)) (hf : IsProIso f) :
    IsProIso ((rightProjection R f g).map L) := by
  have : ∀ i, IsIso (((rightProjection R (LevelHom.id Y) g).map L).app i) :=
    fun i => hL (identity_isConnective R (g.app i) (hZ i)) (hZ i)
      ((rightProjection R (LevelHom.id Y) g).app i)
      (rightProjection_identity_quasiIso R g i)
  have hc := ((modelBaseMap_isProIso R f g hf).map L).comp
    (TowerDiagram.isProIso_of_levelwiseIso ((rightProjection R (LevelHom.id Y) g).map L))
  rw [← TowerDiagram.levelHom_map_comp, modelBaseMap_comp_right] at hc
  exact hc

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
