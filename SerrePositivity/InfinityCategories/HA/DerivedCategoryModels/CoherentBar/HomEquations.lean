module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.HomDegrees
/-!
概要：実 bar からの閉斉次射を、元の全単体列上の twisted 微分方程式に同定する。
方針：Hom の次数同値と微分公式を全単体ラベルの直積へ送る。
規約：native 余錐の退化整合性と普遍性はこの代数的同値とは別に証明する。
使われ方：bar 余錐の構成と全 Hom 普遍性に必要な係数方程式の正本。
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
  (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F) (N : RightModule R D)

def dgCoherentBarHomColumnDifferential (q : ℤ)
    (a : ∀ s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I,
      (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
        (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s)) N).X q) :
    ∀ s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I,
      (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
        (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s)) N).X (q + 1) :=
  let z := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarHomEquiv R D F (ForgetEnrichment.of (Complex R) N) q).symm a
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarHomEquiv R D F (ForgetEnrichment.of (Complex R) N) (q + 1)
    ((_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)) N).d q (q + 1) z +
      (q + 1).negOnePow • _root_.SerrePositivity.DifferentialGraded.compose R
        (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
        (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)) (z := N)
        z (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F) (by omega : 1 + q = q + 1))

lemma dgCoherentBarHomColumnsEquiv_d (q : ℤ)
    (z : (moduleHom R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule R D F hMC) N).X q) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHomColumnsEquiv R D F hMC N (q + 1)
      ((moduleHom R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule R D F hMC) N).d q (q + 1) z) =
    dgCoherentBarHomColumnDifferential R D F N q
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHomColumnsEquiv R D F hMC N q z) := by
  simp only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHomColumnsEquiv, LinearEquiv.trans_apply,
    dgCoherentBarHomColumnDifferential, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHomDegreeEquiv_d]
  erw [(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarHomEquiv R D F (ForgetEnrichment.of (Complex R) N) q).symm_apply_apply
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHomDegreeEquiv R D F hMC N q z)]
  rfl

lemma dgCoherentBarHomColumnsEquiv_closed_iff (q : ℤ)
    (z : (moduleHom R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule R D F hMC) N).X q) :
    (moduleHom R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule R D F hMC) N).d q (q + 1) z = 0 ↔
      dgCoherentBarHomColumnDifferential R D F N q
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHomColumnsEquiv R D F hMC N q z) = 0 := by
  rw [← dgCoherentBarHomColumnsEquiv_d]
  exact (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHomColumnsEquiv R D F hMC N (q + 1)).map_eq_zero_iff.symm

def dgCoherentBarClosedColumnsEquiv (q : ℤ) :
    {z : (moduleHom R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule R D F hMC) N).X q //
      (moduleHom R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule R D F hMC) N).d q (q + 1) z = 0} ≃
    {a : ∀ s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I,
      (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
        (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s)) N).X q //
      dgCoherentBarHomColumnDifferential R D F N q a = 0} :=
  (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHomColumnsEquiv R D F hMC N q).toEquiv.subtypeEquiv
    (dgCoherentBarHomColumnsEquiv_closed_iff R D F hMC N q)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
