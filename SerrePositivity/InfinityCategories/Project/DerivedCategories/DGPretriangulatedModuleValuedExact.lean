module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelTensorYonedaNerveIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPretriangulatedYonedaExact
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorExact
/-!
概要：前三角な小 dg 圏から全加群圏への任意の dg 関手は共通宇宙で完全。
方針：Yoneda と kernel tensor の完全性を同じ実関手同型で移送する。
規約：Small 仮定は始域と係数圏だけに要求し、全加群圏には課さない。
使われ方：D2 の G-1 e の第二脚 M.toFunctor を直接接続する。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D C : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]

/-- 前三角な小始域の任意の全加群値 dg 関手は、共通宇宙の nerve 上で完全。 -/
theorem dgPretriangulatedModuleValuedFunctor_isExactFunctor
    [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D] (F : DGFunctor R D (RightModule R C)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v, max (u + 1) v} R D).comp F)) := by
  let P : Bimodule R C D := F
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPretriangulatedYoneda_isExactFunctor R D
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorNerve_isExactFunctor R D C (Morita.kernelTensor R D C P)
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_functorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorYonedaCompositeIso R D C P)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
