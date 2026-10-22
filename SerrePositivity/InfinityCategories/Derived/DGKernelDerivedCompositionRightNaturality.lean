module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedCompositorRawNaturality
public import SerrePositivity.InfinityCategories.Derived.DGKernelRawFactorHomNaturality
public import SerrePositivity.InfinityCategories.Derived.DGKernelCompositionSemifreeRightNaturality
public import SerrePositivity.InfinityCategories.Derived.DGKernelCompositionRawFactorHom
/-!
概要：第一 kernel だけの右相対 K-flat 性から元の κ の右変数自然性を証明する。
方針：同じ raw factor・augmentation・通常 tensor の実四角形を加群値の一般補題へ渡す。
規約：後続 kernel の平坦性と射の可逆性は不要。使われ方：入力模型の比較の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
variable (R : Type u) [CommRing R] (D E K : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R K] [Small.{u} K]
variable (P : BimoduleCategory R E D) {Q0 Q1 : BimoduleCategory R K E} (g : Q0 ⟶ Q1)
local notation "p" => BimoduleCategory.underlying R E D P
local notation "q0" => BimoduleCategory.underlying R K E Q0
local notation "q1" => BimoduleCategory.underlying R K E Q1
local notation "H0" => Morita.kernelTensor R E K q0
local notation "H1" => Morita.kernelTensor R E K q1
local notation "KP" => Morita.kernelTensor R D E p
local notation "C0" => Morita.kernelTensor R D K (BimoduleTensor.compose R K E D q0 p)
local notation "C1" => Morita.kernelTensor R D K (BimoduleTensor.compose R K E D q1 p)
local notation "I" => dgFullSubcategoryInclusion R (RightModule R D)
  (dgModuleSemifreeProperty R D)
local notation "J" => dgSemifreeKernelModuleDG R D E p
local notation "L" => dgModuleResolvedInfinity R (RightModule R K) K
  (DGFunctor.id (RightModule R K))
lemma dgKernelDerivedInfinity_compIso_right_naturality
    (hP : Bimodule.rightRelativeKFlat R E D p) :
    (dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E K p q0 hP).hom ≫
      (dgKernelDerivedFunctorHomFunctor R D K).map
        (BimoduleTensor.composeMap R K E D g (𝟙 P)) =
    functorHomPrecomp (dgKernelDerivedInfinity R E K q0)
      (dgKernelDerivedInfinity R E K q1) (dgKernelDerivedInfinity R D E p)
      ((dgKernelDerivedFunctorHomFunctor R E K).map g) ≫
      (dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E K p q1 hP).hom := by
  exact dgModuleResolved_compositor_hom_naturality_of_raw R (SemifreeDGModules R D) E K
    J H0 H1 (dgSemifreeKernelModuleDG R D K (BimoduleTensor.compose R K E D q0 p))
    (dgSemifreeKernelModuleDG R D K (BimoduleTensor.compose R K E D q1 p))
    (dgKernelResolutionAugmentation_tensor_quasiIso R D E K p q0 hP)
    (dgKernelResolutionAugmentation_tensor_quasiIso R D E K p q1 hP)
    (dgKernelTensorCompositionSemifreeIso R D E K p q0)
    (dgKernelTensorCompositionSemifreeIso R D E K p q1)
    (dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E K p q0 hP)
    (dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E K p q1 hP)
    (functorHomPostcomp (dgNerve.map H0) (dgNerve.map H1) L
      ((dgKernelTensorFunctorHomFunctor R E K).map g))
    ((dgKernelDerivedFunctorHomFunctor R E K).map g)
    ((dgKernelDerivedFunctorHomFunctor R D K).map
      (BimoduleTensor.composeMap R K E D g (𝟙 P)))
    (dgModuleRawOutputPrecompHom R D K (SemifreeDGModules R D) I C0 C1
      (functorHomPostcomp (dgNerve.map C0) (dgNerve.map C1) L
        ((dgKernelTensorFunctorHomFunctor R D K).map
          (BimoduleTensor.composeMap R K E D g (𝟙 P)))))
    (dgKernelDerived_rawFactor_hom_naturality R E K g)
    (dgKernelDerived_rawFactor_hom_naturality R D K
      (BimoduleTensor.composeMap R K E D g (𝟙 P)))
    (dgKernelTensorCompositionSemifreeIso_right_naturality R D E K P g)
    (dgKernelDerivedInfinity_compIso_rawFactor_hom R D E K p q0 hP)
    (dgKernelDerivedInfinity_compIso_rawFactor_hom R D E K p q1 hP)
end SerrePositivity.InfinityCategories
