module
public import SerrePositivity.InfinityCategories.Derived.DGModuleExtensionYonedaNerveIso
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
def dgGluingCoefficientTensorStrict :
    StrictNatTrans ((dgYoneda R D).comp (Morita.kernelTensor R D C M)) M.toFunctor :=
  dgModuleStrictNatTransOfHomNaturality R C
    (fun d => (BimoduleTensor.rightUnitIso R C D M d).hom)
    (fun d d' => by
      simpa only [EnrichedFunctor.comp_map, dgYoneda, moduleHomPostcompose,
        moduleHomPrecompose, Category.assoc] using!
          Morita.criterionPerfTensorYonedaHom_naturality R D C M d d')
lemma dgGluingCoefficientTensorStrict_app (d : D) :
    (dgGluingCoefficientTensorStrict R C D M).app d =
      cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
        (BimoduleTensor.rightUnitIso R C D M d).hom) := rfl

def dgGluingCoefficientTensorLiftedStrict :
    StrictNatTrans
      ((dgUniverseLiftDown.{u, w,max (u + 1) v} R D).comp
        ((dgYoneda R D).comp (Morita.kernelTensor R D C M)))
      ((dgUniverseLiftDown.{u, w,max (u + 1) v} R D).comp M.toFunctor) :=
  dgStrictNatTransPrecomp _ (dgGluingCoefficientTensorStrict R C D M)
end SerrePositivity.InfinityCategories
