module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentCutProjective
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentCutColimit
public import SerrePositivity.DifferentialGraded.Module.ColimitHom
public import SerrePositivity.DifferentialGraded.Complexes.TowerLimitAcyclic

/-!
概要：h-projective 頂点の coherent 図式の実正規化 bar は h-projective。
方針：有限次元段階の射影性と Hom 制限の全射性を Hom 塔の極限へ接続する。
規約：HA 成分は次元を下げる項としてすべて保持する。
使われ方：全加群の native 余極限を射影的模型で回収する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarNormalizedModule_homotopicallyProjective
    (hG : ∀ s : I _⦋0⦌, moduleHomotopicallyProjective R D
      (ForgetEnrichment.of (Complex R) (coherentDiagramVertex G s))) :
    moduleHomotopicallyProjective R D
      (ForgetEnrichment.of (Complex R) (dgCoherentBarNormalizedModuleUnconditional R D G)) := by
  intro T hT
  apply complexTowerLimit_acyclic R
    (moduleHomSourceDiagram R D (dgCoherentBarCutModuleDiagram R D G) T)
    (moduleColimitHomIsLimit R D (dgCoherentBarCutModuleIsColimit R D G) T)
  · intro n
    exact dgCoherentBarCutModule_projective R D G hG n T hT
  · intro n q
    exact (dgCoherentBarCutGradedSplit R D G n).homRestriction_surjective T q

end SerrePositivity.InfinityCategories
