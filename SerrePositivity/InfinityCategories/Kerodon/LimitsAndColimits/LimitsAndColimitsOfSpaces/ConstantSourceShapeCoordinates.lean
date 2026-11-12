module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.ConstantSourceComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningBaseChange

/-!
概要：定値 unstraightening の元の直積表示と形状制限を厳密に照合する。
方針：引き戻しの二射影で、指定 fiber と元の底の座標を検査する。
規約：定値図式の表示の等式も明示し、選択した同型をそのまま使う。
使われ方：相対写像空間の制限を全切断の制限へ移す際の始域の座標。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 元の定値始域の直積座標では、形状制限は底だけの前合成になる。 -/
lemma constantSourceOverIso_inv_shape {B K : SSet.{u + 1}}
    (i : K ⟶ B) (z : SpaceInfinity.{u} _⦋0⦌)
    (h : i ≫ (SSet.const z : B ⟶ _) = SSet.const z) :
    (constantUnstraighteningSourceOverIso K z).inv.left ≫
      leftUnstraighteningMap (SSet.const z) (SSet.const z) i h =
    (i ▷ vertexFiber pointedSpaceProjection z) ≫
      (constantUnstraighteningSourceOverIso B z).inv.left := by
  apply pullback.hom_ext
  · rw [Category.assoc, leftUnstraighteningMap_pointed, Category.assoc]
    change tensorToPullbackConstant pointedSpaceProjection z K ≫ pullback.fst _ _ =
      (i ▷ vertexFiber pointedSpaceProjection z) ≫
        tensorToPullbackConstant pointedSpaceProjection z B ≫ pullback.fst _ _
    rw [tensorToPullbackConstant, pullback.lift_fst, tensorToPullbackConstant,
      pullback.lift_fst, whiskerRight_snd_assoc]
  · erw [Category.assoc, leftUnstraighteningMap_projection]
    change _ ≫ leftUnstraighteningProjection (SSet.const z : K ⟶ _) ≫ i =
      (i ▷ vertexFiber pointedSpaceProjection z) ≫
        (constantUnstraighteningSourceOverIso B z).inv.left ≫
          leftUnstraighteningProjection (SSet.const z : B ⟶ _)
    erw [← Category.assoc, (constantUnstraighteningSourceOverIso K z).inv.w,
      (constantUnstraighteningSourceOverIso B z).inv.w, whiskerRight_fst]
    rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
