module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCospanProComparison
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConnectiveQuasiIso

/-!
概要：元の経路模型の pro 比較に、connective 準同型の反転だけを使う。
方針：標的模型の connective 性を、元の sourceMap の準同型性で混合模型へ移す。
規約：混合模型の connective 性を追加入力しない。使われ方：元の不変量値の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
open ProExcision
variable (R : Type u) [CommRing R] {X Y : Tower (WalkingCospan ⥤ Mon (Complex R))}
  (f : LevelHom X Y)

lemma diagramMap_isProIso_of_connective {D : Type v} [Category.{w} D]
    (L : Mon (Complex R) ⥤ D) (hL : InvertsConnectiveQuasiIsos R L)
    (hS : ∀ i, QuasiIso ((f.app i).app .left).hom)
    (hY : ∀ i, IsConnective R (diagramObject R (Y.obj i)))
    (hC : IsProIso (f.map (TowerDiagram.cospanEval .one)))
    (hR : IsProIso (f.map (TowerDiagram.cospanEval .right))) :
    IsProIso ((f.map (diagramFunctor R)).map L) := by
  have : ∀ i, IsIso ((((TowerDiagram.sourceFactorSecond f).map (diagramFunctor R)).map L).app i) :=
    fun i => hL ((quasiIso_isConnective_iff R
      (diagramMap R ((TowerDiagram.sourceFactorSecond f).app i))
      (sourceFactorSecond_quasiIso R f hS i)).2 (hY i)) (hY i) _
        (sourceFactorSecond_quasiIso R f hS i)
  have ha := ((TowerDiagram.sourceFactorFirst_isProIso f hC hR).map (diagramFunctor R)).map L
  have hb := TowerDiagram.isProIso_of_levelwiseIso
    (((TowerDiagram.sourceFactorSecond f).map (diagramFunctor R)).map L)
  have hc := ha.comp hb
  rw [← TowerDiagram.levelHom_map_comp, ← TowerDiagram.levelHom_map_comp,
    TowerDiagram.sourceFactor_fac] at hc
  exact hc

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
