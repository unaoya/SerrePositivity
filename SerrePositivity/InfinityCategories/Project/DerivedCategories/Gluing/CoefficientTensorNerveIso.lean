module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CoefficientTensorComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPretriangulatedYonedaExact
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorExact
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPretriangulatedModuleValuedExact
/-!
概要：Yoneda 後の kernelTensor と元係数脚の比較を、実関手同型と完全性へ接続する。
方針：全 Hom 自然な右単位同型を既存の厳密自然変換の nerve 比較へ渡す。
規約：この入口では元 C・D の対象宇宙を同じに固定する。一般宇宙の主経路に制限を加えない。
使われ方：D-14 を待つ間の係数脚の接続検証と、その後の共通宇宙比較に用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C D : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)
def dgGluingCoefficientTensorNerveIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v,max (u + 1) v} R D).comp
        ((_root_.SerrePositivity.DifferentialGraded.dgYoneda R D).comp (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R D C M))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v,max (u + 1) v} R D).comp M.toFunctor)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorIsoOfStrictNatTrans R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientTensorLiftedStrict R C D M)
    (fun x => (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.rightUnitIso R C D M x.label.down).hom)
    (fun _ => rfl) (fun _ => inferInstance)
def dgGluingCoefficientTensorCompositeIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v,max (u + 1) v} R D).comp (dgYoneda R D)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D C M))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v,max (u + 1) v} R D).comp M.toFunctor)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorYonedaCompositeIso R D C M
lemma dgGluingCoefficientLiftedNerve_isExactFunctor [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v,max (u + 1) v} R D).comp M.toFunctor)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPretriangulatedModuleValuedFunctor_isExactFunctor R D C M.toFunctor
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
