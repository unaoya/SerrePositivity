module
public import SerrePositivity.InfinityCategories.Derived.DGModuleDerivedUnderlyingIso
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedProjectiveComparison
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullyFaithfulPostcomposition
/-!
概要：同じ実出力分解による関手を、既存の射影的模型による実導来関手と比較する。
方針：同じ生の包含先で二つの全関手同型を合成し、完全充満包含で回収する。
規約：元の dg 関手が射影的対象を保つことを明示する。使われ方：graph tensor 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  (F : DGFunctor R (RightModule R D) (RightModule R E))
  (hF : ∀ M, dgModuleProjectiveProperty R D M → dgModuleProjectiveProperty R E (F.obj M))
/-- 射影的対象を保つ元の関手について、二つの実導来化は全関手同型。 -/
def dgModuleResolvedInfinity_derivedFunctorIso :
    FunctorIso (dgModuleResolvedInfinity R (SemifreeDGModules R D) E
      ((dgFullSubcategoryInclusion R (RightModule R D) (dgModuleSemifreeProperty R D)).comp F))
      (dgModuleDerivedFunctor R D E F hF) := by
  have e := dgModuleResolvedInfinity_inclusionIso R (SemifreeDGModules R D) E
    ((dgFullSubcategoryInclusion R (RightModule R D) (dgModuleSemifreeProperty R D)).comp F)
    (fun M => hF M.val (dgSemifreeModule_isProjective R D M))
  exact (dgSemifreeModulesInclusion_isFullyFaithful R E).preimageFunctorIso
    (e ≪≫ (dgModuleDerivedFunctor_underlyingIso R D E F hF).symm)
end SerrePositivity.InfinityCategories
