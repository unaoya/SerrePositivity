module

public import SerrePositivity.KST.LocalizingInvariants.ProCospanSourceFactor
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackFunctor
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackSourceQuasiIso
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathInvertingFunctor

/-!
概要：左が各段準同型・中心と右が実 pro 同型の cospan 射を、元の経路模型で比較する。
方針：左対象を固定する実図式の pro 逆と、元の sourceMap の準同型性を合成する。
規約：一般導来極限の保存を仮定しない。使われ方：n=1 の class 模型の実逆 roof。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits WalkingCospan WalkingCospan.Hom
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
open ProExcision
variable (R : Type u) [CommRing R] {X Y : Tower (WalkingCospan ⥤ Mon (Complex R))}
  (f : LevelHom X Y)

lemma sourceFactorSecond_diagramMap (i : ℕ) :
    diagramMap R ((TowerDiagram.sourceFactorSecond f).app i) =
      sourceMap R ((Y.obj i).map inl) ((Y.obj i).map inr) ((f.app i).app .left) := by
  apply hom_ext R ((Y.obj i).map inl) ((Y.obj i).map inr)
  · exact (diagramMap_left R ((TowerDiagram.sourceFactorSecond f).app i)).trans
      (sourceMap_left R _ _ _).symm
  · exact (diagramMap_right R ((TowerDiagram.sourceFactorSecond f).app i)).trans
      ((Category.comp_id _).trans (sourceMap_right R _ _ _).symm)
  · have h := diagramMap_path R ((TowerDiagram.sourceFactorSecond f).app i)
    change diagramMap R ((TowerDiagram.sourceFactorSecond f).app i) ≫
      path R ((Y.obj i).map inl) ((Y.obj i).map inr) =
        path R _ _ ≫ Path.map R (𝟙 ((Y.obj i).obj .one)) at h
    rw [Path.map_id, Category.comp_id] at h
    exact h.trans (sourceMap_path R _ _ _).symm

lemma sourceFactorSecond_quasiIso (hL : ∀ i, QuasiIso ((f.app i).app .left).hom) (i : ℕ) :
    QuasiIso (diagramMap R ((TowerDiagram.sourceFactorSecond f).app i)).hom := by
  rw [sourceFactorSecond_diagramMap]
  exact sourceMap_quasiIso R _ _ _ (hL i)

lemma diagramMap_isProIso_of_inverts {D : Type v} [Category.{w} D]
    (L : Mon (Complex R) ⥤ D) (hL : InvertsQuasiIsos R L)
    (hS : ∀ i, QuasiIso ((f.app i).app .left).hom)
    (hC : IsProIso (f.map (TowerDiagram.cospanEval .one)))
    (hR : IsProIso (f.map (TowerDiagram.cospanEval .right))) :
    IsProIso ((f.map (diagramFunctor R)).map L) := by
  have : ∀ i, IsIso ((((TowerDiagram.sourceFactorSecond f).map (diagramFunctor R)).map L).app i) :=
    fun i => hL _ (sourceFactorSecond_quasiIso R f hS i)
  have ha := ((TowerDiagram.sourceFactorFirst_isProIso f hC hR).map (diagramFunctor R)).map L
  have hb := TowerDiagram.isProIso_of_levelwiseIso
    (((TowerDiagram.sourceFactorSecond f).map (diagramFunctor R)).map L)
  have hc := ha.comp hb
  rw [← TowerDiagram.levelHom_map_comp, ← TowerDiagram.levelHom_map_comp,
    TowerDiagram.sourceFactor_fac] at hc
  exact hc

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
