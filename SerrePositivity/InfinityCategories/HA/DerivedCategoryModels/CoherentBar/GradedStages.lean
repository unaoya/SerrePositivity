module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.BoundaryFiltration
public import SerrePositivity.DifferentialGraded.Module.Hom.ColimitsAndRightHom
/-!
概要：同じ theta の境界で作る有限段階を、元の graded bar の全 Hom 上に置く。
方針：単位と境界の和を反復合成し、標的単体次数のフィルトレーションを保つことを示す。
規約：段階ごとの反復は有限。全段階の無限積は作らない。
使われ方：各単体上で安定した正規化作用素と実 bar 上の鎖写像との比較。
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

def dgCoherentBarNormalizationStageGraded : ℕ →
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).X 0
  | 0 => (unitElement R (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).val
  | q + 1 => _root_.SerrePositivity.DifferentialGraded.compose R
      (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      ((unitElement R (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).val +
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationBoundaryGraded R D F q)
      (dgCoherentBarNormalizationStageGraded q) (show (0 : ℤ) + 0 = 0 from rfl)

lemma dgCoherentBarUnit_restrict (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I) :
    (eHomWhiskerRight (Complex R) (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)).f 0
      (unitElement R (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).val =
    (eHomWhiskerLeft (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s)
      (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s)).f 0
      (unitElement R (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s))).val := by
  have hpre := moduleHomCycle_precompose R D (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s)
    (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
  have hpost := moduleHomCycle_postcompose R D (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s))
    (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s)
  rw [Category.comp_id] at hpre
  rw [Category.id_comp] at hpost
  exact hpre.trans hpost.symm

lemma dgCoherentBarUnit_restrict_mem_filtration (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I) :
    (eHomWhiskerRight (Complex R) (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)).f 0
      (unitElement R (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).val ∈
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHomFiltration R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s) 0 s.1 := by
  rw [dgCoherentBarUnit_restrict]
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHomFiltration_inclusion R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s) 0 s.1 s le_rfl _

set_option maxHeartbeats 800000 in
-- 反復合成の全 Hom と各段階の支持上限の照合に限って上限を増やす。
lemma dgCoherentBarNormalizationStageGraded_mem_filtration (q : ℕ)
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I) :
    (eHomWhiskerRight (Complex R) (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)).f 0 (dgCoherentBarNormalizationStageGraded R D F q) ∈
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHomFiltration R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s) 0 s.1 := by
  induction q with
  | zero => exact dgCoherentBarUnit_restrict_mem_filtration R D F s
  | succ q ih =>
    change (eHomWhiskerRight (Complex R) (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)).f 0
        (_root_.SerrePositivity.DifferentialGraded.compose R
          (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
          (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
          (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
          ((_root_.SerrePositivity.DifferentialGraded.unitElement R
            (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).val +
            _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationBoundaryGraded R D F q)
          (dgCoherentBarNormalizationStageGraded R D F q) rfl) ∈ _
    rw [_root_.SerrePositivity.DifferentialGraded.moduleHomRestriction_compose R D
      (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s)
      (dgCoherentBarNormalizationStageGraded R D F q)]
    refine _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHomFiltration_postcompose R D F
      (M := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s) (p := 0) (q := 0) (k := 0)
      (n := s.1) (m := s.1)
      ((eHomWhiskerRight (Complex R) (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)).f 0 (dgCoherentBarNormalizationStageGraded R D F q))
      ((_root_.SerrePositivity.DifferentialGraded.unitElement R
        (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).val +
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationBoundaryGraded R D F q) ih ?_ rfl
    intro t ht
    rw [map_add]
    apply Submodule.add_mem
    · exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHomFiltration_mono R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F t) 0
        (n := t.1) (m := s.1) ht (dgCoherentBarUnit_restrict_mem_filtration R D F t)
    · exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHomFiltration_mono R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F t) 0
        (n := t.1) (m := s.1) ht
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationBoundaryGraded_mem_filtration R D F q t)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
