module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelDerivedInfinity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedDerivedComparison
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExactFunctorChoice
/-!
概要：任意双加群作用の実 graph を、既存の相対 tensor ∞ 関手に比較する。
方針：元の graph dg 関手の厳密等式と二つの実導来化の全関手比較を使う。
規約：同じ元の graph を保持する。使われ方：一般作用の graph 整合性と完全性。
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
/-- 一般双加群作用の同じ graph は、既存の実相対 tensor ∞ 関手と同型。 -/
def dgKernelDerivedInfinity_graphIso (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E (functorGraph R D E F))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R D E F) := by
  have e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_derivedFunctorIso R D E (dgModuleExtension R D E F)
    (fun _ h => _root_.SerrePositivity.DifferentialGraded.dgModuleExtension_homotopicallyProjective R D E F h)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E (functorGraph R D E F))) _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG, Morita.kernelTensor_graph]
  exact e
/-- 同じ一般作用の graph 制限は完全関手。 -/
lemma dgKernelDerivedInfinity_graph_isExactFunctor (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E (functorGraph R D E F)) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity_isExactFunctor R D E F
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_functorIso (dgKernelDerivedInfinity_graphIso R D E F).symm
end SerrePositivity.InfinityCategories.Project.DerivedCategories
