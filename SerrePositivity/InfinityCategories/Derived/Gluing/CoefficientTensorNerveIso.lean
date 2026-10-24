module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CoefficientTensorComparison
public import SerrePositivity.InfinityCategories.Derived.DGPretriangulatedYonedaExact
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorExact
public import SerrePositivity.InfinityCategories.Derived.DGPretriangulatedModuleValuedExact
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C D : Type v)
  [DGCategory R C] [Small.{u} C] [DGCategory R D] [Small.{u} D]
  (M : Bimodule R C D)
def dgGluingCoefficientTensorNerveIso :
    FunctorIso
      (dgNerve.map ((dgUniverseLiftDown.{u, v,max (u + 1) v} R D).comp
        ((dgYoneda R D).comp (Morita.kernelTensor R D C M))))
      (dgNerve.map ((dgUniverseLiftDown.{u, v,max (u + 1) v} R D).comp M.toFunctor)) :=
  dgModuleFunctorIsoOfStrictNatTrans R C (dgGluingCoefficientTensorLiftedStrict R C D M)
    (fun x => (BimoduleTensor.rightUnitIso R C D M x.label.down).hom)
    (fun _ => rfl) (fun _ => inferInstance)
def dgGluingCoefficientTensorCompositeIso :
    FunctorIso
      (dgNerve.map ((dgUniverseLiftDown.{u, v,max (u + 1) v} R D).comp (dgYoneda R D)) ≫
        dgNerve.map (Morita.kernelTensor R D C M))
      (dgNerve.map ((dgUniverseLiftDown.{u, v,max (u + 1) v} R D).comp M.toFunctor)) :=
  dgKernelTensorYonedaCompositeIso R D C M
lemma dgGluingCoefficientLiftedNerve_isExactFunctor [IsDGPretriangulated R D] :
    IsExactFunctor (dgNerve.map
      ((dgUniverseLiftDown.{u, v,max (u + 1) v} R D).comp M.toFunctor)) :=
  dgPretriangulatedModuleValuedFunctor_isExactFunctor R D C M.toFunctor
end SerrePositivity.InfinityCategories
