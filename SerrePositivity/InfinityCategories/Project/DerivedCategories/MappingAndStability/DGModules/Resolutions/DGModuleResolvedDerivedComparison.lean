module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleDerivedUnderlyingIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolvedProjectiveComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulPostcomposition
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R (_root_.SerrePositivity.DifferentialGraded.RightModule R D) (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
  (hF : ∀ M, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D M → _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R E (F.obj M))
/-- 射影的対象を保つ元の関手について、二つの実導来化は全関手同型。 -/
def dgModuleResolvedInfinity_derivedFunctorIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
      ((dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)).comp F))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedFunctor R D E F hF) := by
  have e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_inclusionIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
    ((dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)).comp F)
    (fun M => hF M.val (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModule_isProjective R D M))
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModulesInclusion_isFullyFaithful R E).preimageFunctorIso
    (e ≪≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedFunctor_underlyingIso R D E F hF).symm)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
