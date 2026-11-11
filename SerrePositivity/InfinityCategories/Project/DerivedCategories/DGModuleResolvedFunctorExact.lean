module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleStability
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedLimitTransfer
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedZeroObjects
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSemifreeRawFunctorExact
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelDerivedInfinity
/-!
概要：一般 dg 加群関手の同じ実導来作用と、任意 kernel の同じ ∞ 作用の完全性を結論する。
方針：零頂点を保存し、生の cofiber 像の引き戻し性を全 Hom 試験で半自由出力へ戻す。
規約：生の出力の射影性・局所 Hom 平坦性は追加しない。使われ方：一般 RHom の ∞ 随伴。
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
/-- 同じ一般 dg 関手の実分解後の cofiber 保存。 -/
lemma dgModuleResolvedFunctor_isExactFunctor
    (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R (_root_.SerrePositivity.DifferentialGraded.RightModule R D) (_root_.SerrePositivity.DifferentialGraded.RightModule R E)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
      ((_root_.SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion R (_root_.SerrePositivity.DifferentialGraded.RightModule R D)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)).comp F)) where
  preservesZero := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_preservesZeroVertices R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E _
  preservesCofiber t ht := by
    let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory_isStable R E
    let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModuleFunctorRaw_isExactFunctor R D E F
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesCofiber
      (F := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((dgFullSubcategoryInclusion R (RightModule R D)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)).comp F)) t ht
    apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pushout_of_pullback_square
    apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_isPullbackSquare_of_raw R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E _
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pullback_of_pushout_square _ h
/-- 同じ一般 dg 関手の実分解後の cofiber 保存。 -/
lemma dgKernelDerivedInfinity_isExactFunctor (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P) :=
  dgModuleResolvedFunctor_isExactFunctor R D E (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R D E P)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
