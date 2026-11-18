module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RightKanLimitCompositionArbitrary

/-!
概要：恒等余単位を持つ指定右 Kan 延長では、元の全錐の制限は極限性を保ち反映する。
方針：既存の指定右 Kan に沿う極限比較を、同じ錐の恒等ホモトピーに適用する。
規約：HTT 4.3.2、Kerodon §7.3（Tag 02Y1）の既存構成の合成則。
使われ方：層の係数を局所単射の元の圏へ制限する操作。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 指定恒等余単位による右 Kan 条件は、元の全錐の制限の極限性を特徴づける。 -/
lemma isLimitCone_iff_restrict_of_rightKan_refl
    {I K D : SSet.{u}} [Quasicategory I] [Quasicategory K] [Quasicategory D]
    (δ : I ⟶ K) (p : K ⟶ D)
    (h : IsRightKanExtension δ (δ ≫ p) p
      (SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm (δ ≫ p))))
    (c : JoinCone p) : IsLimitCone c ↔ IsLimitCone (restrictJoinCone c δ) := by
  let H : SSet.Homotopy (restrictJoinCone c δ).val (restrictJoinCone c δ).val :=
    SSet.RelativeMorphism.Homotopy.refl
      (SSet.RelativeMorphism.botEquiv.symm (restrictJoinCone c δ).val)
  refine isLimitCone_iff_of_rightKan_comparison δ c (restrictJoinCone c δ) _ h H ?_ ?_
  · change (joinInr (Δ[0] : SSet.{u}) I ▷ Δ[1]) ≫
      (fst _ _ ≫ (restrictJoinCone c δ).val) = fst _ _ ≫ (δ ≫ p)
    rw [← Category.assoc, whiskerRight_fst, Category.assoc, (restrictJoinCone c δ).property]
  · change (joinInl (Δ[0] : SSet.{u}) I ▷ Δ[1]) ≫
      (fst _ _ ≫ (restrictJoinCone c δ).val) = _
    rw [← Category.assoc, whiskerRight_fst, Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
