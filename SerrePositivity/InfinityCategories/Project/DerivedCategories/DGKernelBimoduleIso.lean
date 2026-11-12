module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGBimoduleIsoNerve
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedRawFactor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelDerivedInfinity
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.Actions
/-!
概要：元の双加群同型を実 tensor と半自由出力分解の全関手同型へ送る。
方針：指定の通常 tensor と全 Hom 自然な実同型、同じ出力分解を使う。
規約：元の Hom の平坦性と出力の射影性を仮定しない。
使われ方：一般 kernel の入力模型移送。
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
/-- 元の双加群同型による、実 tensor dg 関手の nerve の全関手同型。 -/
def dgKernelTensorIsoNerveOfBimoduleIso {P Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (e : P ≅ Q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D P)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D Q))) := by
  let J := _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R D (_root_.SerrePositivity.DifferentialGraded.RightModule R D) (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R D))
  let ee : (P, J) ≅ (Q, J) := Iso.prod e (Iso.refl J)
  let ep := (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeFunctor R E D (_root_.SerrePositivity.DifferentialGraded.RightModule R D)).mapIso ee
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleIsoNerve R E (RightModule R D) ep
  exact h
/-- 元の双加群同型による、同じ実導来作用の全関手同型。 -/
def dgKernelDerivedInfinity_bimoduleIso {P Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (e : P ≅ Q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D P))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D Q)) := by
  let I := dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)
  have h := (dgKernelTensorIsoNerveOfBimoduleIso R D E e).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map I)
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_isoOfRawFunctorIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E (BimoduleCategory.underlying R E D P))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E (BimoduleCategory.underlying R E D Q))
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp] using! h
end SerrePositivity.InfinityCategories.Project.DerivedCategories
