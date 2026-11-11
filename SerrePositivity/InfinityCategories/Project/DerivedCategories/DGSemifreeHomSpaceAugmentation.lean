module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleUnderlyingSpaceInfinity
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.UniverseHomotopy
/-!
概要：固定入力の実 D(R) 値 Hom の augmentation を、空間値の全関手族へ送る。
方針：同じ実ホモトピーを対象宇宙ごと持ち上げ、R からの写像空間関手で後合成する。
規約：有向ホモトピーであり、比較の可逆性は別途検証する。
使われ方：空間値 Hom の実比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
/-- 実 D(R) の半自由模型から R を始域とする写像空間への全 ∞ 関手。 -/
def dgHomDerivedSpaceInfinity :
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomDerivedNerve R D) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{max (u + 1) v} :=
  (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleInclusionInfinity R D) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomUnderlyingSpaceInfinity R D
/-- 共変 D(R) 値 Hom に R からの写像空間を適用した全 ∞ 関手。 -/
def dgSemifreeDerivedHomTargetSpaceInfinity (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{max (u + 1) v} :=
  (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomTargetInfinity R D P) ≫ dgHomDerivedSpaceInfinity R D
/-- 元の全 Hom の R 加群値関手に、同じ基礎空間関手を適用する。 -/
def dgSemifreeHomTargetSpaceInfinity (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{max (u + 1) v} :=
  (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomTargetModuleInfinity R D P) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomUnderlyingSpaceInfinity R D
/-- 実反対 ∞ 圏上の D(R) 値 Hom から作る、同じ全空間値関手。 -/
def dgSemifreeDerivedHomContravariantSpaceInfinity (Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D).op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{max (u + 1) v} :=
  (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedContravariantHomInfinity R D Q) ≫ dgHomDerivedSpaceInfinity R D
/-- 実反対 ∞ 圏上の元の全 Hom から作る、同じ全空間値関手。 -/
def dgSemifreeHomContravariantSpaceInfinity (Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D).op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{max (u + 1) v} :=
  (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomContravariantModuleInfinity R D Q) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomUnderlyingSpaceInfinity R D
/-- 共変の実 augmentation を同じ基礎空間関手へ送った、全単体上のホモトピー。 -/
def dgSemifreeDerivedHomTargetSpaceAugmentation (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    SSet.Homotopy (dgSemifreeDerivedHomTargetSpaceInfinity R D P)
      (dgSemifreeHomTargetSpaceInfinity R D P) := by
  have H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftHomotopy.{max (u + 1) v, max (u + 1) v + 1}
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomTargetAugmentationInfinity R D P))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomUnderlyingSpaceInfinity R D)
  simpa only [Functor.map_comp, Category.assoc, dgSemifreeDerivedHomTargetSpaceInfinity,
    dgHomDerivedSpaceInfinity, dgSemifreeHomTargetSpaceInfinity] using H
/-- 反変の実 augmentation も、実反対 ∞ 圏上の全単体的ホモトピーを与える。 -/
def dgSemifreeDerivedHomContravariantSpaceAugmentation (Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    SSet.Homotopy (dgSemifreeDerivedHomContravariantSpaceInfinity R D Q)
      (dgSemifreeHomContravariantSpaceInfinity R D Q) := by
  have H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftHomotopy.{max (u + 1) v, max (u + 1) v + 1}
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomContravariantAugmentationInfinity R D Q))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomUnderlyingSpaceInfinity R D)
  simpa only [Functor.map_comp, Category.assoc, dgSemifreeDerivedHomContravariantSpaceInfinity,
    dgHomDerivedSpaceInfinity, dgSemifreeHomContravariantSpaceInfinity] using H
end SerrePositivity.InfinityCategories.Project.DerivedCategories
