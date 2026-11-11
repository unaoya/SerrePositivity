module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NormalizedHomDegrees
/-!
概要：正規化実 bar からの閉斉次射を、非退化列の twisted 方程式へ同定する。
方針：正規化側の全 Hom 線形同値と実微分公式を各次数で使う。
規約：この代数的同値と native 余錐の普遍性を区別する。
使われ方：工程Bの全 Hom 普遍性と任意パラメータの高次成分の比較。
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

def dgCoherentBarNormalizedHomColumnDifferential (q : ℤ)
    (a : ∀ s : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedIndex I,
      (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
        (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedFamily R D F s)) N).X q) :
    ∀ s : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedIndex I,
      (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
        (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedFamily R D F s)) N).X (q + 1) :=
  let z := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedHomEquiv R D F N q).symm a
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedHomEquiv R D F N (q + 1)
    ((_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D F)) N).d q (q + 1) z +
      (q + 1).negOnePow • _root_.SerrePositivity.DifferentialGraded.compose R
        (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D F))
        (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D F)) (z := N)
        z (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedTheta R D F) (by omega : 1 + q = q + 1))

lemma dgCoherentBarNormalizedHomColumnsEquiv_d (q : ℤ)
    (z : (moduleHom R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N).X q) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedHomColumnsEquiv R D F hMC N (q + 1)
      ((moduleHom R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N).d q (q + 1) z) =
    dgCoherentBarNormalizedHomColumnDifferential R D F N q
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedHomColumnsEquiv R D F hMC N q z) := by
  simp only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedHomColumnsEquiv, LinearEquiv.trans_apply,
    dgCoherentBarNormalizedHomColumnDifferential, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedHomDegreeEquiv_d]
  erw [(_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedHomEquiv R D F N q).symm_apply_apply
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedHomDegreeEquiv R D F hMC N q z)]

lemma dgCoherentBarNormalizedHomColumnsEquiv_closed_iff (q : ℤ)
    (z : (moduleHom R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N).X q) :
    (moduleHom R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N).d q (q + 1) z = 0 ↔
      dgCoherentBarNormalizedHomColumnDifferential R D F N q
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedHomColumnsEquiv R D F hMC N q z) = 0 := by
  rw [← dgCoherentBarNormalizedHomColumnsEquiv_d]
  exact (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedHomColumnsEquiv R D F hMC N (q + 1)).map_eq_zero_iff.symm

def dgCoherentBarNormalizedClosedColumnsEquiv (q : ℤ) :
    {z : (moduleHom R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N).X q //
      (moduleHom R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N).d q (q + 1) z = 0} ≃
    {a : ∀ s : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedIndex I,
      (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
        (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedFamily R D F s)) N).X q //
      dgCoherentBarNormalizedHomColumnDifferential R D F N q a = 0} :=
  (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedHomColumnsEquiv R D F hMC N q).toEquiv.subtypeEquiv
    (dgCoherentBarNormalizedHomColumnsEquiv_closed_iff R D F hMC N q)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
