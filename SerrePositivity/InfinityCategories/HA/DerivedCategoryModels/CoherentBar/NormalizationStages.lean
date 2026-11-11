module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.DegeneracyOperators
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.EndRebase
/-!
概要：退化作用素の境界から、実 bar の微分と可換な段階的正規化作用素を作る。
方針：実 Hom の二乗零で境界を閉零射にし、恒等射との和と反復合成を取る。
規約：同じ theta の微分で計算する。像の正規化性と段階の安定化は別に証明する。
使われ方：退化除去の射影と、元の bar への変形 retract の鎖ホモトピー。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))
  (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F)

abbrev dgCoherentBarObject : ModuleCategory R D :=
  ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule R D F hMC)

def dgCoherentBarNormalizationHomotopy (q : ℕ) :
    (moduleHom R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule R D F hMC)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule R D F hMC)).X (-1) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarEndRebase R D F hMC (-1) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationHomotopyGraded R D F q)

def dgCoherentBarNormalizationBoundary (q : ℕ) :
    dgCoherentBarObject R D F hMC ⟶ dgCoherentBarObject R D F hMC :=
  _root_.SerrePositivity.DifferentialGraded.moduleMorphismOfCycle R D
    ((moduleHom R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule R D F hMC)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule R D F hMC)).d (-1) 0
        (dgCoherentBarNormalizationHomotopy R D F hMC q)) (by
    exact ConcreteCategory.congr_hom
      ((moduleHom R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule R D F hMC)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule R D F hMC)).d_comp_d (-1) 0 1)
      (dgCoherentBarNormalizationHomotopy R D F hMC q))

def dgCoherentBarNormalizationBoundaryHomotopy (q : ℕ) :
    _root_.SerrePositivity.DifferentialGraded.ModuleHomotopy R D (dgCoherentBarNormalizationBoundary R D F hMC q) 0 :=
  ⟨dgCoherentBarNormalizationHomotopy R D F hMC q, by
    rw [dgCoherentBarNormalizationBoundary, _root_.SerrePositivity.DifferentialGraded.moduleMorphismOfCycle_cycle]
    change _ = _ - (0 : (moduleHom R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule R D F hMC)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule R D F hMC)).X 0)
    exact (sub_zero _).symm⟩

set_option maxHeartbeats 800000 in
-- 実 bar と元の全 Hom end の特殊次数での照合に限って上限を増やす。
lemma dgCoherentBarNormalizationBoundary_cycle (q : ℕ) :
    (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex R)
      (dgCoherentBarNormalizationBoundary R D F hMC q))).val =
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarEndRebase R D F hMC 0
      (compose R (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
        (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
        (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationHomotopyGraded R D F q)
        (show (-1 : ℤ) + 1 = 0 from rfl) +
      compose R (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
        (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
        (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationHomotopyGraded R D F q) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F)
        (show (1 : ℤ) + -1 = 0 from rfl)) := by
  rw [dgCoherentBarNormalizationBoundary, _root_.SerrePositivity.DifferentialGraded.moduleMorphismOfCycle_cycle]
  have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarEndRebase_d R D F hMC (-1)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationHomotopyGraded R D F q)
  simp only [show (-1 : ℤ) + 1 = 0 from rfl,
    Int.negOnePow_zero, one_smul] at h
  change _ = _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarEndRebase R D F hMC 0
    ((_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).d (-1) 0
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationHomotopyGraded R D F q) + _ + _) at h
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationHomotopyGraded_d, zero_add] at h
  exact h

def dgCoherentBarNormalizationStage : ℕ →
    (dgCoherentBarObject R D F hMC ⟶ dgCoherentBarObject R D F hMC)
  | 0 => 𝟙 _
  | q + 1 => dgCoherentBarNormalizationStage q ≫
      (𝟙 _ + dgCoherentBarNormalizationBoundary R D F hMC q)

lemma dgCoherentBarNormalizationStage_homotopyClass (q : ℕ) :
    (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy R D).map (dgCoherentBarNormalizationStage R D F hMC q) =
      (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy R D).map (𝟙 (dgCoherentBarObject R D F hMC)) := by
  have hzero (q : ℕ) :
      (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy R D).map (dgCoherentBarNormalizationBoundary R D F hMC q) = 0 := by
    have h := (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy_map_eq_iff R D
      (dgCoherentBarNormalizationBoundary R D F hMC q) 0).2
        ⟨dgCoherentBarNormalizationBoundaryHomotopy R D F hMC q⟩
    simpa only [Functor.map_zero] using h
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [dgCoherentBarNormalizationStage, Functor.map_comp, Functor.map_add,
      hzero, add_zero, ih, CategoryTheory.Functor.map_id, Category.id_comp]

def dgCoherentBarNormalizationStageHomotopy (q : ℕ) :
    _root_.SerrePositivity.DifferentialGraded.ModuleHomotopy R D (dgCoherentBarNormalizationStage R D F hMC q) (𝟙 _) :=
  Classical.choice ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy_map_eq_iff R D _ _).1
    (dgCoherentBarNormalizationStage_homotopyClass R D F hMC q))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
