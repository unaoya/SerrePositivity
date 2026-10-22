module
public import SerrePositivity.InfinityCategories.Derived.DGKernelRawFactorHomNaturality
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedAugmentationHomNaturality
public import SerrePositivity.InfinityCategories.Derived.DGKernelCompositionAugmentation
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
lemma dgKernelDerived_augmentation_hom_naturality
    (hP : Bimodule.rightRelativeKFlat R E D p) :
    (dgModuleResolvedAugmentationRawFactorIso R (SemifreeDGModules R D) E K J H0
    (dgKernelResolutionAugmentation_tensor_quasiIso R D E K p q0 hP)).hom ≫
    (dgModuleRawOutputPrecompHom R E K (SemifreeDGModules R D) J H0 H1 (functorHomPostcomp
    (dgNerve.map H0) (dgNerve.map H1) L ((dgKernelTensorFunctorHomFunctor R E K).map g))) =
    (functorHomPrecomp (dgNerve.map ((dgFullSubcategoryInclusion R (RightModule R E)
    (dgModuleSemifreeProperty R E)).comp H0) ≫ L) (dgNerve.map ((dgFullSubcategoryInclusion R
    (RightModule R E) (dgModuleSemifreeProperty R E)).comp H1) ≫ L) (dgKernelDerivedInfinity R D E
    p) (dgModuleRawOutputPrecompHom R E K (SemifreeDGModules R E) (dgFullSubcategoryInclusion R
    (RightModule R E) (dgModuleSemifreeProperty R E)) H0 H1 (functorHomPostcomp (dgNerve.map H0)
    (dgNerve.map H1) L ((dgKernelTensorFunctorHomFunctor R E K).map g)))) ≫
    (dgModuleResolvedAugmentationRawFactorIso R (SemifreeDGModules R D) E K J H1
    (dgKernelResolutionAugmentation_tensor_quasiIso R D E K p q1 hP)).hom := by
  exact dgModuleResolvedAugmentationRawFactorIso_hom_naturality
    R E K (SemifreeDGModules R D) J H0 H1
    (dgKernelResolutionAugmentation_tensor_quasiIso R D E K p q0 hP)
    (dgKernelResolutionAugmentation_tensor_quasiIso R D E K p q1 hP)
    (functorHomPostcomp (dgNerve.map H0) (dgNerve.map H1) L
      ((dgKernelTensorFunctorHomFunctor R E K).map g))
end SerrePositivity.InfinityCategories
