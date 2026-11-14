module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleStability
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolvedLimitTransfer
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolvedZeroObjects
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleFunctorExact
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.DGSemifreeProjectiveEquivalence

/-!
概要：全 dg 加群から実半自由出力への分解関手の完全性を供給する。
方針：生の dg 関手の cofiber 保存を pullback に直し、実分解へ移送する。
規約：Small 仮定は係数 dg 圏だけに置き、全加群圏には要求しない。
使われ方：D2 の G-1 e における全加群の実分解と完全関手の合成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]

/-- 全加群間の任意の dg 関手の、同じ実半自由出力分解は完全。 -/
theorem dgModuleAllResolvedFunctor_isExactFunctor
    (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R (_root_.SerrePositivity.DifferentialGraded.RightModule R D) (_root_.SerrePositivity.DifferentialGraded.RightModule R E)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R D) E F) where
  preservesZero := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_preservesZeroVertices R (RightModule R D) E F
  preservesCofiber t ht := by
    let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory_isStable R E
    let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorNerve_isExactFunctor R D E F
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesCofiber (F := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) t ht
    apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pushout_of_pullback_square
    apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_isPullbackSquare_of_raw R (RightModule R D) E F
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pullback_of_pushout_square _ h

omit [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] in
/-- 全加群から同じ実半自由分解への ∞ 関手は完全。 -/
theorem dgModuleResolutionInfinity_isExactFunctor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R D) D (DGFunctor.id _)) :=
  dgModuleAllResolvedFunctor_isExactFunctor R D D (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id _)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
