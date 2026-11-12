module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.StageCoefficientCriterion
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedIdentityColumn
/-!
概要：実正規化の零段階と普遍係数の零段階が一致する。
方針：恒等ラベルの単項係数へ自由加群を制限し、恒等単体写像の実単位列を使う。
規約：段階比較の基底だけを無条件に証明する。帰納段の比較は別に行う。
使われ方：DGCoherentBarStageCoefficientComparison の帰納証明の初期段。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]

abbrev dgCoherentBarBasedUniversalIdentity (n : ℕ) : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.DGCoherentBarBasedLabel.{u} n n :=
  ⟨_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalIdentity n, rfl⟩

lemma dgCoherentBarUniversalStageCoefficients_zero_based (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalStageCoefficients R n 0).subtypeDomain (fun a => a 0 = 0) =
      Finsupp.single (dgCoherentBarBasedUniversalIdentity n) 1 := by
  classical
  change (Finsupp.single (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalIdentity n) (1 : R)).subtypeDomain _ = _
  ext a
  simp only [Finsupp.subtypeDomain_apply, Finsupp.single_apply, Subtype.ext_iff]

variable (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarStageCoefficientComparison_zero {n : ℕ} (s : I _⦋n⦌) :
    HEq ((eHomWhiskerRight (Complex R) (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) ⟨n, s⟩)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)).f 0 (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationStageGraded R D F 0))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedColumnAction R D F n s
        ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalStageCoefficients R n 0).subtypeDomain (fun a => a 0 = 0))) := by
  have hc := congrArg (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedColumnAction R D F n s)
    (dgCoherentBarUniversalStageCoefficients_zero_based R n)
  have haction : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedColumnAction R D F n s
        ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalStageCoefficients R n 0).subtypeDomain (fun a => a 0 = 0)) =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedColumn R D F (𝟙 ⦋n⦌) rfl s := by
    exact hc.trans (by
      simp only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedColumnAction, Finsupp.linearCombination_single, one_smul]
      rfl)
  exact ((heq_of_eq haction).trans (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedIdentityColumn_heq R D F s)).symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
