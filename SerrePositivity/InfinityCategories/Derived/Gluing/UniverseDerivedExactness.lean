module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseDerivedStructure
public import SerrePositivity.InfinityCategories.Derived.Gluing.TensorCoefficientExactTransfer
public import SerrePositivity.InfinityCategories.Derived.DGPretriangulatedModuleValuedCommonExact
public import SerrePositivity.InfinityCategories.Derived.DGModuleAllResolvedExact
public import SerrePositivity.InfinityCategories.Stable.UniverseExactFunctorLift
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
lemma dgGluingUniverseModuleDerivedComparison_isExactFunctor :
    IsExactFunctor (dgGluingUniverseModuleDerivedComparison.{u, v, w} R C) :=
  isExactFunctor_ulift.{max (u + 1) v, max (u + 1) v w} _
    (dgModuleResolutionInfinity_isExactFunctor R C)
lemma dgGluingUniverseYoneda_isExactFunctor (hC : IsDGPretriangulated R C) :
    IsExactFunctor (dgGluingUniverseYoneda.{u, v, w} R C) := by
  let := hC
  exact dgPretriangulatedModuleValuedFunctorCommon_isExactFunctor.{u, v, v, w}
    R C C (dgYoneda R C)
lemma dgGluingUniverseDerivedYoneda_isExactFunctor (hC : IsDGPretriangulated R C) :
    IsExactFunctor (dgGluingUniverseDerivedYoneda.{u, v, w} R C) := by
  let := dgGluingUniverseYoneda_isExactFunctor.{u, v, w} R C hC
  let := dgGluingUniverseModuleDerivedComparison_isExactFunctor.{u, v, w} R C
  change IsExactFunctor (dgGluingUniverseYoneda.{u, v, w} R C ≫
    dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)
  infer_instance
variable (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
lemma dgGluingUniverseCoefficient_isExactFunctor (hD : IsDGPretriangulated R D) :
    IsExactFunctor (dgGluingUniverseCoefficient R C D M) := by
  have hT : IsExactFunctor
      (dgGluingUniverseNerveMap.{u, max (u + 1) w, max (u + 1) v, max (u + 1) v w}
        (Morita.kernelTensor R D C M)) :=
    dgModuleFunctorCommonNerve_isExactFunctor.{u, w, v, max (u + 1) v w}
      R D C (Morita.kernelTensor R D C M)
  exact dgGluingUniverseCoefficient_isExactFunctor_of_tensor R C D M
    (dgGluingUniverseYoneda_isExactFunctor.{u, w, v} R D hD) hT
lemma dgGluingUniverseDerivedCoefficient_isExactFunctor (hD : IsDGPretriangulated R D) :
    IsExactFunctor (dgGluingUniverseDerivedCoefficient R C D M) := by
  let := dgGluingUniverseCoefficient_isExactFunctor R C D M hD
  let := dgGluingUniverseModuleDerivedComparison_isExactFunctor.{u, v, w} R C
  change IsExactFunctor (dgGluingUniverseCoefficient R C D M ≫
    dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)
  infer_instance
end SerrePositivity.InfinityCategories
