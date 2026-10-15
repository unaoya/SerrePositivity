module
public import SerrePositivity.DifferentialGraded.Derived.GradedExtensionProjective
public import SerrePositivity.DifferentialGraded.Module.ColimitHom
public import SerrePositivity.DifferentialGraded.Complexes.TowerLimitAcyclic
public import SerrePositivity.DifferentialGraded.Module.Semifree.Resolution

/-! # semifree加群のhomotopically projective性

各有限段のHom acyclic性、Hom制限の全射性と実際の極限普遍性を接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma ModuleSemifreeFiltration.homotopicallyProjective {M : ModuleCategory A D}
    (F : ModuleSemifreeFiltration A D M) : moduleHomotopicallyProjective A D M := by
  apply moduleHomotopicallyProjective_of_iso A D F.iso
  intro T hT
  apply complexTowerLimit_acyclic A
    (moduleHomSourceDiagram A D (Functor.ofSequence F.transition) T)
    (moduleColimitHomIsLimit A D F.isColimit T)
  · intro n
    exact F.stage_homotopicallyProjective A D n T hT
  · intro n q
    change Function.Surjective
      ((eHomWhiskerRight (Complex A)
        ((Functor.ofSequence F.transition).map (homOfLE (n.le_add_right 1))) T).f q)
    rw [Functor.ofSequence_map_homOfLE_succ]
    exact (F.split n).homRestriction_surjective T q

lemma moduleSemifree_homotopicallyProjective {M : ModuleCategory A D}
    (hM : moduleSemifree A D M) : moduleHomotopicallyProjective A D M := by
  obtain ⟨F⟩ := hM
  exact F.homotopicallyProjective A D

theorem exists_homotopicallyProjective_resolution (M : ModuleCategory A D) :
    ∃ (P : ModuleCategory A D) (q : P ⟶ M),
      moduleHomotopicallyProjective A D P ∧
        moduleDegreewiseSurjective A D q ∧ moduleQuasiIso A D q := by
  obtain ⟨P, q, hP, hq, hW⟩ := exists_semifree_resolution A D M
  exact ⟨P, q, moduleSemifree_homotopicallyProjective A D hP, hq, hW⟩

end SerrePositivity.DifferentialGraded
