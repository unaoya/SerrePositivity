module
public import SerrePositivity.InfinityCategories.Derived.DGModuleUnderlyingSpaceInfinity
public import SerrePositivity.InfinityCategories.Core.UniverseHomotopy
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
/-- 実 D(R) の半自由模型から R を始域とする写像空間への全 ∞ 関手。 -/
def dgHomDerivedSpaceInfinity :
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj (dgHomDerivedNerve R D) ⟶
      SpaceInfinity.{max (u + 1) v} :=
  (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
    (dgHomModuleInclusionInfinity R D) ≫ dgHomUnderlyingSpaceInfinity R D
/-- 共変 D(R) 値 Hom に R からの写像空間を適用した全 ∞ 関手。 -/
def dgSemifreeDerivedHomTargetSpaceInfinity (P : SemifreeDGModules R D) :
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (dgModuleDerivedInfinityCategory R D) ⟶ SpaceInfinity.{max (u + 1) v} :=
  (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
    (dgSemifreeDerivedHomTargetInfinity R D P) ≫ dgHomDerivedSpaceInfinity R D
/-- 元の全 Hom の R 加群値関手に、同じ基礎空間関手を適用する。 -/
def dgSemifreeHomTargetSpaceInfinity (P : SemifreeDGModules R D) :
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (dgModuleDerivedInfinityCategory R D) ⟶ SpaceInfinity.{max (u + 1) v} :=
  (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
    (dgSemifreeHomTargetModuleInfinity R D P) ≫ dgHomUnderlyingSpaceInfinity R D
/-- 実反対 ∞ 圏上の D(R) 値 Hom から作る、同じ全空間値関手。 -/
def dgSemifreeDerivedHomContravariantSpaceInfinity (Q : SemifreeDGModules R D) :
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (dgModuleDerivedInfinityCategory R D).op ⟶ SpaceInfinity.{max (u + 1) v} :=
  (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
    (dgSemifreeDerivedContravariantHomInfinity R D Q) ≫ dgHomDerivedSpaceInfinity R D
/-- 実反対 ∞ 圏上の元の全 Hom から作る、同じ全空間値関手。 -/
def dgSemifreeHomContravariantSpaceInfinity (Q : SemifreeDGModules R D) :
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (dgModuleDerivedInfinityCategory R D).op ⟶ SpaceInfinity.{max (u + 1) v} :=
  (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
    (dgSemifreeHomContravariantModuleInfinity R D Q) ≫ dgHomUnderlyingSpaceInfinity R D
/-- 共変の実 augmentation を同じ基礎空間関手へ送った、全単体上のホモトピー。 -/
def dgSemifreeDerivedHomTargetSpaceAugmentation (P : SemifreeDGModules R D) :
    SSet.Homotopy (dgSemifreeDerivedHomTargetSpaceInfinity R D P)
      (dgSemifreeHomTargetSpaceInfinity R D P) := by
  have H := functorHomotopyPostcomp
    (DoldKanComparison.uliftHomotopy.{max (u + 1) v, max (u + 1) v + 1}
      (dgSemifreeDerivedHomTargetAugmentationInfinity R D P))
    (dgHomUnderlyingSpaceInfinity R D)
  simpa only [Functor.map_comp, Category.assoc, dgSemifreeDerivedHomTargetSpaceInfinity,
    dgHomDerivedSpaceInfinity, dgSemifreeHomTargetSpaceInfinity] using H
/-- 反変の実 augmentation も、実反対 ∞ 圏上の全単体的ホモトピーを与える。 -/
def dgSemifreeDerivedHomContravariantSpaceAugmentation (Q : SemifreeDGModules R D) :
    SSet.Homotopy (dgSemifreeDerivedHomContravariantSpaceInfinity R D Q)
      (dgSemifreeHomContravariantSpaceInfinity R D Q) := by
  have H := functorHomotopyPostcomp
    (DoldKanComparison.uliftHomotopy.{max (u + 1) v, max (u + 1) v + 1}
      (dgSemifreeDerivedHomContravariantAugmentationInfinity R D Q))
    (dgHomUnderlyingSpaceInfinity R D)
  simpa only [Functor.map_comp, Category.assoc, dgSemifreeDerivedHomContravariantSpaceInfinity,
    dgHomDerivedSpaceInfinity, dgSemifreeHomContravariantSpaceInfinity] using H
end SerrePositivity.InfinityCategories
