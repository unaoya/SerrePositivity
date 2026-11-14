module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelDerivedInfinity
public import SerrePositivity.DifferentialGraded.Morita.Kernel
/-!
概要：任意の双加群射の実 tensor 成分を、半自由入力の全 Hom 自然な閉射族にする。
方針：元の全 Hom 自然な双加群合成射の成分と自然性を、同じ充満包含へ制限する。
規約：通常の次数零自然性だけで代用しない。使われ方：一般双加群の実 ∞ 関手比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  {P Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (f : P ⟶ Q)
/-- 同じ双加群射が、元の同じ半自由入力上へ与える実 tensor 閉射。 -/
def dgSemifreeKernelMap (M : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E (BimoduleCategory.underlying R E D P)).obj M) ⟶
    ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E (BimoduleCategory.underlying R E D Q)).obj M) :=
  (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensorMap R D E f).app (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) M.val)
/-- 同じ実 tensor 閉射族は、半自由入力の全 Hom 鎖写像に関して自然。 -/
lemma dgSemifreeKernelMap_hom_naturality (M N : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E (BimoduleCategory.underlying R E D P)).map M N ≫
      eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R)
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E (BimoduleCategory.underlying R E D P)).obj M))
        (dgSemifreeKernelMap R D E f N) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E (BimoduleCategory.underlying R E D Q)).map M N ≫
      eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) (dgSemifreeKernelMap R D E f M)
        (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R)
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E (BimoduleCategory.underlying R E D Q)).obj N)) := by
  let b := _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R E D (_root_.SerrePositivity.DifferentialGraded.RightModule R D) f
    (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R D (_root_.SerrePositivity.DifferentialGraded.RightModule R D) (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R D))))
  have h := b.property M.val N.val
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG, EnrichedFunctor.comp_map, dgFullSubcategoryInclusion,
    Category.id_comp, dgSemifreeKernelMap, _root_.SerrePositivity.DifferentialGraded.Morita.kernelTensorMap,
    _root_.SerrePositivity.DifferentialGraded.Morita.kernelClosedFamilyNatTrans] using! h
end SerrePositivity.InfinityCategories.Project.DerivedCategories
