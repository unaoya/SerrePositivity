module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseDerivedStructure
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.TensorCoefficientExactTransfer
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPretriangulatedModuleValuedCommonExact
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleAllResolvedExact
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.UniverseExactFunctorLift
/-!
概要：元の Yoneda・係数・実半自由分解の共通宇宙での完全性を無条件で接続する。
方針：D-14 の公開された混在宇宙の完全性と ULift 保存を、構成済み tensor 比較へ接続する。
規約：Small は元の dg 圏だけ。元の単体・Hom・分解関手を変更しない。
使われ方：G-1 e の正本 lax pullback の二脚へ、隔離していた完全性を供給する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
lemma dgGluingUniverseModuleDerivedComparison_isExactFunctor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u, v, w} R C) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_ulift.{max (u + 1) v, max (u + 1) v w} _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionInfinity_isExactFunctor R C)
lemma dgGluingUniverseYoneda_isExactFunctor (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseYoneda.{u, v, w} R C) := by
  let := hC
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPretriangulatedModuleValuedFunctorCommon_isExactFunctor.{u, v, v, w}
    R C C (_root_.SerrePositivity.DifferentialGraded.dgYoneda R C)
lemma dgGluingUniverseDerivedYoneda_isExactFunctor (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, v, w} R C) := by
  let := dgGluingUniverseYoneda_isExactFunctor.{u, v, w} R C hC
  let := dgGluingUniverseModuleDerivedComparison_isExactFunctor.{u, v, w} R C
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseYoneda.{u, v, w} R C ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)
  infer_instance
variable (D : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)
lemma dgGluingUniverseCoefficient_isExactFunctor (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseCoefficient R C D M) := by
  have hT : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseNerveMap.{u, max (u + 1) w, max (u + 1) v, max (u + 1) v w}
        (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R D C M)) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorCommonNerve_isExactFunctor.{u, w, v, max (u + 1) v w}
      R D C (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R D C M)
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseCoefficient_isExactFunctor_of_tensor R C D M
    (dgGluingUniverseYoneda_isExactFunctor.{u, w, v} R D hD) hT
lemma dgGluingUniverseDerivedCoefficient_isExactFunctor (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M) := by
  let := dgGluingUniverseCoefficient_isExactFunctor R C D M hD
  let := dgGluingUniverseModuleDerivedComparison_isExactFunctor.{u, v, w} R C
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseCoefficient R C D M ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)
  infer_instance
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
