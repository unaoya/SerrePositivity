module
public import SerrePositivity.InfinityCategories.Derived.DGBimoduleIsoNerve
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D E F : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R F] [Small.{u} F]
/-- 通常 tensor 作用の合成は、同じ通常合成双加群の作用と全関手同型。 -/
def dgKernelTensorCompositionNerveIso (P : Bimodule R E D) (Q : Bimodule R F E) :
    FunctorIso (dgNerve.map (Morita.kernelTensor R D E P) ≫
      dgNerve.map (Morita.kernelTensor R E F Q))
      (dgNerve.map (Morita.kernelTensor R D F (BimoduleTensor.compose R F E D Q P))) := by
  have e := dgBimoduleIsoNerve R F (RightModule R D)
    (BimoduleTensor.associatorIso R F E D (RightModule R D) Q P
      (DGFunctor.id (RightModule R D))).symm
  dsimp only [BimoduleCategory.underlying, BimoduleCategory.of] at e
  rw [← Morita.kernelTensorComposition_eq, dgNerve.map_comp] at e
  exact e
end SerrePositivity.InfinityCategories
