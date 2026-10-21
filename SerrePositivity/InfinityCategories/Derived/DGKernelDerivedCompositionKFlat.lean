module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedComposition
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedRawFactor
public import SerrePositivity.InfinityCategories.Derived.DGKernelCompositionAugmentation
public import SerrePositivity.InfinityCategories.Derived.DGKernelTensorComposition
/-!
概要：最初の右相対 K-flat kernel について、二つの実導来 ∞ 作用の合成を比較する。
方針：同じ augmentation の全単体ホモトピーと、通常 tensor の実結合子を使う。
規約：後の kernel は任意。局所 Hom の平坦性は仮定しない。
使われ方：平坦模型から元の一般 kernel へ合成比較を移す計算段階。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D E K : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R K] [Small.{u} K]
/-- 最初の kernel が右相対 K-flat なら、実導来 ∞ 作用の合成は通常合成 kernel の作用と全関手同型。 -/
def dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat
    (P : Bimodule R E D) (Q : Bimodule R K E)
    (hP : Bimodule.rightRelativeKFlat R E D P) :
    FunctorIso (dgKernelDerivedInfinity R D E P ≫ dgKernelDerivedInfinity R E K Q)
      (dgKernelDerivedInfinity R D K (BimoduleTensor.compose R K E D Q P)) := by
  let C := SemifreeDGModules R D
  let I := dgFullSubcategoryInclusion R (RightModule R D) (dgModuleSemifreeProperty R D)
  let F := dgSemifreeKernelModuleDG R D E P
  let G := dgSemifreeKernelModuleDG R D K (BimoduleTensor.compose R K E D Q P)
  let H := Morita.kernelTensor R E K Q
  have a := dgModuleResolvedInfinity_compositionIso R C E K F H
    (dgKernelResolutionAugmentation_tensor_quasiIso R D E K P Q hP)
  have er : FunctorIso (dgNerve.map (F.comp H)) (dgNerve.map G) := by
    have e := (dgKernelTensorCompositionNerveIso R D E K P Q).precomp (dgNerve.map I)
    simpa only [F, G, H, I, dgSemifreeKernelModuleDG, dgNerve.map_comp,
      Category.assoc] using! e
  have b := dgModuleResolvedInfinity_isoOfRawFunctorIso R C K (F.comp H) G er
  exact a ≪≫ b
end SerrePositivity.InfinityCategories
