module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelRawFactorHomNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedAugmentationHomNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelCompositionAugmentation
/-!
概要：元の導来 kernel の raw factor と augmentation の任意射自然性を照合する。
方針：同じ比較と実射作用を保ち、全前合成・同じ指定切断上の四角形を使う。
規約：後続 kernel の平坦性・射の可逆性を要求しない。使われ方：元の κ の自然性。
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
lemma dgKernelDerived_augmentation_hom_naturality
    (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D p) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedAugmentationRawFactorIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E K J H0
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelResolutionAugmentation_tensor_quasiIso R D E K p q0 hP)).hom ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleRawOutputPrecompHom R E K (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) J H0 H1 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H1) L ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R E K).map g))) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((dgFullSubcategoryInclusion R (RightModule R E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R E)).comp H0) ≫ L) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((dgFullSubcategoryInclusion R
    (RightModule R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R E)).comp H1) ≫ L) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E
    p) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleRawOutputPrecompHom R E K (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E) (dgFullSubcategoryInclusion R
    (RightModule R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R E)) H0 H1 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H0)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H1) L ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R E K).map g)))) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedAugmentationRawFactorIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E K J H1
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelResolutionAugmentation_tensor_quasiIso R D E K p q1 hP)).hom := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedAugmentationRawFactorIso_hom_naturality
    R E K (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) J H0 H1
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelResolutionAugmentation_tensor_quasiIso R D E K p q0 hP)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelResolutionAugmentation_tensor_quasiIso R D E K p q1 hP)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H1) L
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R E K).map g))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
