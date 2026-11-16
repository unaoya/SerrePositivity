module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.WeightedColimitWeightTransport
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.WeightedColimitAugmentation

/-!
概要：重みの指定同型による coend の移送は、元の通常の余錐への増大を保つ。
方針：同じ普遍脚で計算し、重みを忘れる第一射影との可換性を使う。
規約：Kerodon §7.5.1（Tag 03A0）の既存の重み模型の移送の法則。
使われ方：S8 の Čech 図式の元の増大の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories.Project.FilteredExchange
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
variable {I : Type u} [SmallCategory I]

/-- 重みの指定同型を介しても、同じ通常の余錐への増大は変わらない。 -/
lemma weightedColimitWeightIso_augmentation {W V : Iᵒᵖ ⥤ SSet.{u}}
    (e : W ≅ V) {F : I ⥤ SSet.{u}} (c : Cocone F) :
    (weightedColimitWeightIso e F).hom ≫ weightedColimitAugmentation V c =
      weightedColimitAugmentation W c := by
  apply weightedColimit_hom_ext
  intro i
  rw [← Category.assoc, weightedColimitWeightIso_ι_hom, Category.assoc,
    weightedColimitι_augmentation, weightedColimitι_augmentation, ← Category.assoc]
  rfl

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
