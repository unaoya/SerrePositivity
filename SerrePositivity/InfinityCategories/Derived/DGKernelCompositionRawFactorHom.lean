module
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedCompositionRawFactor
/-!
概要：元の指定導来 kernel 合成子の raw factor 計算を、同じ全関手射の等式へ移す。
方針：証明済みの同じ指定同型等式から順方向射を回収する。
規約：合成子や比較の値を展開しない。使われ方：K-flat の共通経路への型付き移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D E K : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R K] [Small.{u} K]
  (P : Bimodule R E D) (Q : Bimodule R K E)
/-- 元の同じ合成子の raw factor 計算は、同じ通常後続 augmentation の全関手射で可換。 -/
lemma dgKernelDerivedInfinity_compIso_rawFactor_hom
    (hP : Bimodule.rightRelativeKFlat R E D P) :
    (dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E K P Q hP).hom ≫
      (dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R D) K
        (dgSemifreeKernelModuleDG R D K (BimoduleTensor.compose R K E D Q P))).hom =
    ((dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R E) K
      (dgSemifreeKernelModuleDG R E K Q)).precomp (dgKernelDerivedInfinity R D E P)).hom ≫
      (dgModuleResolvedAugmentationRawFactorIso R (SemifreeDGModules R D) E K
        (dgSemifreeKernelModuleDG R D E P) (Morita.kernelTensor R E K Q)
        (dgKernelResolutionAugmentation_tensor_quasiIso R D E K P Q hP)).hom ≫
      ((dgKernelTensorCompositionSemifreeIso R D E K P Q).postcomp
        (dgModuleResolvedInfinity R (RightModule R K) K (DGFunctor.id (RightModule R K)))).hom := by
  have h := congrArg Iso.hom (dgKernelDerivedInfinity_compIso_rawFactor R D E K P Q hP)
  simpa only [Iso.trans_hom] using! h
end SerrePositivity.InfinityCategories
