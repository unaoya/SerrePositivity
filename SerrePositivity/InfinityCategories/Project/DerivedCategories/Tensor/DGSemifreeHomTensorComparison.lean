module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGSemifreeHomTensorInfinity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleOutputUnliftedPrecomp
/-!
概要：同じ二入力 Hom の固定入力制限を、元の共変・反変 D(R) 値 Hom へ全関手同型で比較する。
方針：同じ実分解の指定逆と augmentation を保ち、元の関手・値に照合する。
規約：始域は tensor dg 圏の nerve。元の直積上の二変数関手との比較は別工程。
使われ方：二変数導来 Hom の実出力分解。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded Opposite
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
/-- 同じ実 Hom ∞ 関手の固定入力制限の全関手比較。 -/
def dgSemifreeDerivedHomTensor_sourceIso (Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgTensorIncludeFirst R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) Q) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomTensorInfinity R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomSourceDGopInfinity R D Q) := by
  have e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_unliftedPrecompIso.{u, v, 0} R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ
    (DGTensorCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)) PUnit.{1}
    (dgTensorIncludeFirst R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) Q)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomTensorModuleDG R D)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomTensorModuleDG_first] at e
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomTensorInfinity, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomSourceDGopInfinity,
    Category.assoc] using! e.symm
/-- 同じ実 Hom ∞ 関手の固定入力制限の全関手比較。 -/
def dgSemifreeDerivedHomTensor_targetIso (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgTensorIncludeSecond R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) (_root_.Opposite.op P)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomTensorInfinity R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomTargetInfinity R D P) := by
  have e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_unliftedPrecompIso.{u, v, 0} R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)
    (DGTensorCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)) PUnit.{1}
    (dgTensorIncludeSecond R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) (_root_.Opposite.op P))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomTensorModuleDG R D)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomTensorModuleDG_second] at e
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomTensorInfinity, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomTargetInfinity,
    Category.assoc] using! e.symm
end SerrePositivity.InfinityCategories.Project.DerivedCategories
