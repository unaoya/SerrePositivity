module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeProRoof
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCospanProComparison

/-!
概要：元の cospan 模型の逆を、実次数全射準同型 span と元の両三角形で構成する。
方針：左対象を固定する図式の実逆と、元の sourceMap の MappingPath 逆 roof を合成。
規約：元の図式と同じ射を使う。使われ方：構成した一切断の class 逆の実 roof。
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
  (f : LevelHom X Y) {D : Type v} [Category.{w} D]

lemma hasSurjectiveRoofProInverse
    (hS : ∀ i, QuasiIso ((f.app i).app .left).hom)
    (hC : IsProIso (f.map (TowerDiagram.cospanEval .one)))
    (hR : IsProIso (f.map (TowerDiagram.cospanEval .right))) :
    HasSurjectiveRoofProInverse R (D := D) (f.map (diagramFunctor R)) := by
  let a := (TowerDiagram.sourceFactorFirst f).map (diagramFunctor R)
  let b := (TowerDiagram.sourceFactorSecond f).map (diagramFunctor R)
  have ha : IsProIso a := (TowerDiagram.sourceFactorFirst_isProIso f hC hR).map _
  have hb : ∀ i, QuasiIso (b.app i).hom := sourceFactorSecond_quasiIso R f hS
  have he : a.comp b = f.map (diagramFunctor R) := by
    rw [← TowerDiagram.levelHom_map_comp, TowerDiagram.sourceFactor_fac]
  intro i
  obtain ⟨m, hi, r, hr⟩ := exists_inverse_roof_of_factor R (D := D) a b ha hb i
  refine ⟨m, hi, r, ?_⟩
  intro L hL
  have h := hr L hL
  rw [he] at h
  exact h

lemma hasConnectiveRoofProInverse
    (hS : ∀ i, QuasiIso ((f.app i).app .left).hom)
    (hY : ∀ i, IsConnective R (diagramObject R (Y.obj i)))
    (hC : IsProIso (f.map (TowerDiagram.cospanEval .one)))
    (hR : IsProIso (f.map (TowerDiagram.cospanEval .right))) :
    HasConnectiveRoofProInverse R (D := D) (f.map (diagramFunctor R)) hY := by
  let a := (TowerDiagram.sourceFactorFirst f).map (diagramFunctor R)
  let b := (TowerDiagram.sourceFactorSecond f).map (diagramFunctor R)
  have ha : IsProIso a := (TowerDiagram.sourceFactorFirst_isProIso f hC hR).map _
  have hb : ∀ i, QuasiIso (b.app i).hom := sourceFactorSecond_quasiIso R f hS
  have he : a.comp b = f.map (diagramFunctor R) := by
    rw [← TowerDiagram.levelHom_map_comp, TowerDiagram.sourceFactor_fac]
  intro i
  obtain ⟨m, hi, r, hr⟩ :=
    exists_connective_inverse_roof_of_factor R (D := D) a b ha hb hY i
  refine ⟨m, hi, r, ?_⟩
  intro L hL
  have h := hr L hL
  rw [he] at h
  exact h

lemma hasNativeRoofProInverse
    (hS : ∀ i, QuasiIso ((f.app i).app .left).hom)
    (hC : IsProIso (f.map (TowerDiagram.cospanEval .one)))
    (hR : IsProIso (f.map (TowerDiagram.cospanEval .right))) :
    HasNativeRoofProInverse R (f.map (diagramFunctor R)) := by
  let a := (TowerDiagram.sourceFactorFirst f).map (diagramFunctor R)
  let b := (TowerDiagram.sourceFactorSecond f).map (diagramFunctor R)
  have ha : IsProIso a := (TowerDiagram.sourceFactorFirst_isProIso f hC hR).map _
  have hb : ∀ i, QuasiIso (b.app i).hom := sourceFactorSecond_quasiIso R f hS
  have he : a.comp b = f.map (diagramFunctor R) := by
    rw [← TowerDiagram.levelHom_map_comp, TowerDiagram.sourceFactor_fac]
  have h := hasNativeRoofProInverse_of_factor R a b ha hb
  rw [he] at h
  exact h

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
