module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Bar.DGModuleAugmentationResolvedIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelDerivedInfinity
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D E K : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R K] [Small.{u} K]
/-- 最初の kernel が右相対 K-flat なら、後の任意 kernel は同じ実 augmentation を準同型へ送る。 -/
lemma dgKernelResolutionAugmentation_tensor_quasiIso
    (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) (Q : _root_.SerrePositivity.DifferentialGraded.Bimodule R K E)
    (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D P)
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P)) :
    _root_.SerrePositivity.DifferentialGraded.moduleQuasiIso R K ((_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R E K Q).onClosed.map X.augmentation) := by
  apply _root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor_relativeKFlat_quasiIso R E K Q
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModule_isRelativeKFlat R E X.replacement
  · exact _root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor_relativeKFlat R D E P hP
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) X.source.val)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModule_isRelativeKFlat R D X.source)
  · exact X.quasiIso
end SerrePositivity.InfinityCategories.Project.DerivedCategories
