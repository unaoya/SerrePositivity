module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolvedInfinity
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.InfinityCategory
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison

/-!
# 半自由一点 dg 加群から既存 D(R) への実評価

概要：一点 dg 加群の半自由出力分解を既存の semifree 複体模型へ送る。
方針：同じ全 Hom の評価射を半自由部分圏へ制限する。
規約：既存 derivedInfinityCategory を終域とし、別の導来模型で代用しない。
使われ方：全複体と実 E 代数忘却から U の ∞ 関手を構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SerrePositivity.DifferentialGraded
open _root_.SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

def semifreeRingEvaluationDG : DGFunctor A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules A PUnit.{1}) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree A) where
  obj M := ⟨(moduleEvaluationDG A PUnit.{1} PUnit.unit).obj M.val,
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree_evaluation A (ForgetEnrichment.of (Complex A) M.val)).mpr M.property⟩
  map M N := (moduleEvaluationDG A PUnit.{1} PUnit.unit).map M.val N.val
  map_id M := (moduleEvaluationDG A PUnit.{1} PUnit.unit).map_id M.val
  map_comp M N P := (moduleEvaluationDG A PUnit.{1} PUnit.unit).map_comp M.val N.val P.val

def semifreeRingEvaluationInfinity :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory A PUnit.{1} ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.ComplexLimits.semifreeRingEvaluationDG A)

def complexSemifreeResolutionInfinity :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity A (Complex A) PUnit.{1} (ringConstantDG A) ≫
    _root_.SerrePositivity.ComplexLimits.semifreeRingEvaluationInfinity A

end SerrePositivity.ComplexLimits
