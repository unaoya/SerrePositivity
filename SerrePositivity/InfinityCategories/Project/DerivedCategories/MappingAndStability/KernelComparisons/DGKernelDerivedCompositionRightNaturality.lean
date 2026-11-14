module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolvedCompositorRawNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelRawFactorHomNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelCompositionSemifreeRightNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelCompositionRawFactorHom
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded MonoidalClosed
variable (R : Type u) [CommRing R] (D E K : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R K] [Small.{u} K]
variable (P : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D) {Q0 Q1 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R K E} (g : Q0 ⟶ Q1)
local notation "p" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P
local notation "q0" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R K E Q0
local notation "q1" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R K E Q1
local notation "H0" => _root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R E K q0
local notation "H1" => _root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R E K q1
local notation "KP" => _root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R D E p
local notation "C0" => _root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R D K (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R K E D q0 p)
local notation "C1" => _root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R D K (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R K E D q1 p)
local notation "I" => _root_.SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion R (_root_.SerrePositivity.DifferentialGraded.RightModule R D)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)
local notation "J" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E p
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R K) K
  (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R K))
lemma dgKernelDerivedInfinity_compIso_right_naturality
    (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D p) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E K p q0 hP).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D K).map
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R K E D g (𝟙 P)) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E K q0)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E K q1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E p)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R E K).map g) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E K p q1 hP).hom := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolved_compositor_hom_naturality_of_raw R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E K
    J H0 H1 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D K (BimoduleTensor.compose R K E D q0 p))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D K (BimoduleTensor.compose R K E D q1 p))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelResolutionAugmentation_tensor_quasiIso R D E K p q0 hP)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelResolutionAugmentation_tensor_quasiIso R D E K p q1 hP)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionSemifreeIso R D E K p q0)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionSemifreeIso R D E K p q1)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E K p q0 hP)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E K p q1 hP)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H1) L
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R E K).map g))
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R E K).map g)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D K).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R K E D g (𝟙 P)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleRawOutputPrecompHom R D K (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) I C0 C1
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map C0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map C1) L
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R D K).map
          (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R K E D g (𝟙 P)))))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerived_rawFactor_hom_naturality R E K g)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerived_rawFactor_hom_naturality R D K
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R K E D g (𝟙 P)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionSemifreeIso_right_naturality R D E K P g)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_rawFactor_hom R D E K p q0 hP)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_rawFactor_hom R D E K p q1 hP)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
