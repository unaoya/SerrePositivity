module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedDerivedComparison
public import SerrePositivity.InfinityCategories.Derived.DGModuleDerivedFunctorComposition
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedPrecomposition
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
/-- 全加群の実半自由分解を元の半自由包含へ制限した、指定の恒等比較。 -/
def dgModuleResolutionRetractIso :
    FunctorIso
      (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R E)
        (dgModuleSemifreeProperty R E)) ≫
        dgModuleResolvedInfinity R (RightModule R E) E
          (DGFunctor.id (RightModule R E)))
      (𝟙 (dgModuleDerivedInfinityCategory R E)) := by
  let I := dgFullSubcategoryInclusion R (RightModule R E) (dgModuleSemifreeProperty R E)
  exact (dgModuleResolvedInfinity_precompIso R (SemifreeDGModules R E)
    (RightModule R E) E I (DGFunctor.id (RightModule R E))).symm ≪≫
      dgModuleResolvedInfinity_derivedFunctorIso R E E (DGFunctor.id (RightModule R E))
        (fun _ h => h) ≪≫ dgModuleDerivedFunctor_id_iso R E
end SerrePositivity.InfinityCategories
