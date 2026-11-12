module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Module
/-!
概要：未正規化 bar の各単体因子の包含は、その因子が非零なら零にならない。
方針：元の直和の同じ因子への射影を合成して恒等射を回収する。
規約：退化ラベルも独立因子であり、native 余錐の退化条件を自動では満たさない。
使われ方：native 余錐へ移る前の正規化比較の必要性の検査。
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

lemma dgCoherentBar_raw_inclusion_ne_zero (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I)
    (hs : 𝟙 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s) ≠ 0) :
    Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s ≠ 0 := by
  classical
  intro h
  apply hs
  have hp := congrArg (fun f => f ≫ Sigma.π (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s) h
  simpa using hp

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
