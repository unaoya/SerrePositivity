module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleExtensionYonedaNerveIso
public import SerrePositivity.DifferentialGraded.Morita.CriterionPerfTriangulated
/-!
概要：元の係数脚を、Yoneda 後の実 kernelTensor と全 Hom 自然な比較で結ぶ。
方針：公開済み criterionPerfTensorYonedaHom_naturality を厳密 dg 自然変換へ渡す。
規約：元の双加群・右単位同型・全次数の作用を保持し、前三角性や平坦性を仮定しない。
使われ方：全加群間の kernelTensor の完全性を元の係数脚へ移す入口に用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)
def dgGluingCoefficientTensorStrict :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans ((dgYoneda R D).comp (Morita.kernelTensor R D C M)) M.toFunctor :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleStrictNatTransOfHomNaturality R C
    (fun d => (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.rightUnitIso R C D M d).hom)
    (fun d d' => by
      simpa only [EnrichedFunctor.comp_map, _root_.SerrePositivity.DifferentialGraded.dgYoneda, _root_.SerrePositivity.DifferentialGraded.moduleHomPostcompose,
        _root_.SerrePositivity.DifferentialGraded.moduleHomPrecompose, Category.assoc] using!
          _root_.SerrePositivity.DifferentialGraded.Morita.criterionPerfTensorYonedaHom_naturality R D C M d d')
lemma dgGluingCoefficientTensorStrict_app (d : D) :
    (dgGluingCoefficientTensorStrict R C D M).app d =
      _root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.rightUnitIso R C D M d).hom) := rfl

def dgGluingCoefficientTensorLiftedStrict :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, w,max (u + 1) v} R D).comp
        ((_root_.SerrePositivity.DifferentialGraded.dgYoneda R D).comp (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R D C M)))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, w,max (u + 1) v} R D).comp M.toFunctor) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPrecomp _ (dgGluingCoefficientTensorStrict R C D M)
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
