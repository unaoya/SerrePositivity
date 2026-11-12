module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGBimoduleIsoNerve
public import SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionKernel
/-!
概要：任意の二つの通常 tensor 作用の実 dg nerve 上の合成比較。
方針：主 Hom 鎖写像の厳密等式と、同じ全 Hom 自然な双加群結合子を使う。
規約：生の dg nerve 上の比較であり導来化後の一般合成とは区別する。
使われ方：分解後の一般双加群作用の合成比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D E F : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R F] [Small.{u} F]
/-- 通常 tensor 作用の合成は、同じ通常合成双加群の作用と全関手同型。 -/
def dgKernelTensorCompositionNerveIso (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) (Q : _root_.SerrePositivity.DifferentialGraded.Bimodule R F E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R E F Q))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D F (BimoduleTensor.compose R F E D Q P))) := by
  have e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleIsoNerve R F (RightModule R D)
    (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R F E D (_root_.SerrePositivity.DifferentialGraded.RightModule R D) Q P
      (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R D))).symm
  dsimp only [_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying, _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of] at e
  rw [← Morita.kernelTensorComposition_eq, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp] at e
  exact e
end SerrePositivity.InfinityCategories.Project.DerivedCategories
