module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationResolvedIso
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedInfinity
public import SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionKernel
/-!
概要：最初の右相対 K-flat kernel について、同じ実 augmentation の tensor 像の準同型性を証明する。
方針：元の指定切断・augmentation と、全単体上の関手比較を使う。
規約：元の入力 Hom の平坦性・出力の射影性を仮定しない。
使われ方：一般 kernel の導来合成とその模型移送。
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
/-- 最初の kernel が右相対 K-flat なら、後の任意 kernel は同じ実 augmentation を準同型へ送る。 -/
lemma dgKernelResolutionAugmentation_tensor_quasiIso
    (P : Bimodule R E D) (Q : Bimodule R K E)
    (hP : Bimodule.rightRelativeKFlat R E D P)
    (X : DGModuleFunctorResolutionObject R (SemifreeDGModules R D) E
      (dgSemifreeKernelModuleDG R D E P)) :
    moduleQuasiIso R K ((Morita.kernelTensor R E K Q).onClosed.map X.augmentation) := by
  apply Morita.kernelTensor_relativeKFlat_quasiIso R E K Q
  · exact dgSemifreeModule_isRelativeKFlat R E X.replacement
  · exact Morita.kernelTensor_relativeKFlat R D E P hP
      (ForgetEnrichment.of (Complex R) X.source.val)
      (dgSemifreeModule_isRelativeKFlat R D X.source)
  · exact X.quasiIso
end SerrePositivity.InfinityCategories
