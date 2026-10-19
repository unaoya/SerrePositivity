module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconePointHomFamily

/-!
概要：始対象の場合、全 Hom の族と既存の始対象の Hom 比較が互いにホモトピー逆であることを示す。
方針：評価と底への射影の自明 fibration 上で二つの選ばれた切断を比較する。
規約：実際の比較射と持ち上げの選択を保持する。使われ方：native な span の普遍余錐の族の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
  (d : E _⦋0⦌) (hd : IsInitialVertex d) (y : B _⦋0⦌)

/-- 始対象の全 Hom の族を Hom 比較で戻すと、恒等族と全単体でホモトピック。 -/
lemma pointHomFamily_initialComparison_homotopy :
    Nonempty (SSet.Homotopy
      (leftFibrationPointHomFamily p d y ≫ leftFibrationInitialHomComparison p d hd y)
      (𝟙 _)) := by
  have := leftFibrationInitialEvaluation_trivialKanFibration p d hd y
  obtain ⟨H, _⟩ := exists_homotopy_over_trivialKanFibration
    (leftFibrationInitialEvaluation p d y)
    (leftFibrationPointHomFamily p d y ≫ leftFibrationInitialSection p d hd y)
    (leftFibrationPointHomLift p d y) (by
      rw [Category.assoc, leftFibrationInitialSection_evaluation, Category.comp_id]
      rfl)
  have HH := functorHomotopyPostcomp H
    (leftFibrationInitialProjection p d y ≫ (leftFibrationInitialBaseIso p d y).hom)
  simpa only [leftFibrationInitialHomComparison, ← Category.assoc,
    leftFibrationPointHomLift_projection, Iso.inv_hom_id] using
      (show Nonempty (SSet.Homotopy _ _) from ⟨HH⟩)

/-- 始対象の Hom 比較に全 Hom の族を続けても、fiber の恒等族と全単体でホモトピック。 -/
lemma initialComparison_pointHomFamily_homotopy :
    Nonempty (SSet.Homotopy
      (leftFibrationInitialHomComparison p d hd y ≫ leftFibrationPointHomFamily p d y)
      (𝟙 _)) := by
  obtain ⟨H, _⟩ := exists_homotopy_over_trivialKanFibration
    (leftFibrationInitialProjection p d y)
    (leftFibrationInitialSection p d hd y ≫ leftFibrationInitialProjection p d y ≫
      leftFibrationPointProjectionSection p d y) (leftFibrationInitialSection p d hd y) (by
        rw [Category.assoc, Category.assoc, leftFibrationPointProjectionSection_projection,
          Category.comp_id])
  have HH := functorHomotopyPostcomp H (leftFibrationInitialEvaluation p d y)
  simpa only [leftFibrationInitialHomComparison, leftFibrationPointHomFamily,
    leftFibrationPointHomLift, Category.assoc, Iso.hom_inv_id_assoc,
    leftFibrationInitialSection_evaluation] using
      (show Nonempty (SSet.Homotopy _ _) from ⟨HH⟩)

/-- 余極限余錐の全 Hom の族は、既存の余錐空間の Hom 比較の実際のホモトピー逆。 -/
lemma coconePointHomFamily_comparison_homotopy {K X : SSet.{u}} [Quasicategory X]
    {F : K ⟶ X} (d : JoinCocone F) (hd : IsColimitCone d) (y : X _⦋0⦌) :
    Nonempty (SSet.Homotopy
      (coconePointHomFamily d y ≫ coconeMappingSpaceHomComparison d hd y) (𝟙 _)) :=
  pointHomFamily_initialComparison_homotopy (sliceUnderProjection F) d hd y

/-- 余極限余錐の Hom 比較に全 Hom の族を続けた合成も、余錐空間の恒等族とホモトピック。 -/
lemma coconeComparison_pointHomFamily_homotopy {K X : SSet.{u}} [Quasicategory X]
    {F : K ⟶ X} (d : JoinCocone F) (hd : IsColimitCone d) (y : X _⦋0⦌) :
    Nonempty (SSet.Homotopy
      (coconeMappingSpaceHomComparison d hd y ≫ coconePointHomFamily d y) (𝟙 _)) :=
  initialComparison_pointHomFamily_homotopy (sliceUnderProjection F) d hd y

end
end SerrePositivity.InfinityCategories.HomotopyLimits
