module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedDerivedComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleDerivedFunctorComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedPrecomposition
/-!
概要：全加群の恒等関手の実半自由分解は、半自由包含上で恒等と全関手同型。
方針：入力前合成比較と既存の射影的導来関手比較を、指定恒等比較へ接続する。
規約：元の指定分解を保持する。使われ方：全加群 nerve の局所化普遍性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- 全加群の実半自由分解を元の半自由包含へ制限した、指定の恒等比較。 -/
def dgModuleResolutionRetractIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R E)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R E)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R E) E
          (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E)))
      (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R E)) := by
  let I := dgFullSubcategoryInclusion R (RightModule R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R E)
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_precompIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E)
    (_root_.SerrePositivity.DifferentialGraded.RightModule R E) E I (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E))).symm ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_derivedFunctorIso R E E (DGFunctor.id (RightModule R E))
        (fun _ h => h) ≪≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedFunctor_id_iso R E
end SerrePositivity.InfinityCategories.Project.DerivedCategories
