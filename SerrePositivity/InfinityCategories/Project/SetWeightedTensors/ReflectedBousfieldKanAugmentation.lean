module

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.ReflectedBousfieldKanElements
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.WeightedColimitWeightAugmentation
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.ReplacementCoconeAugmentation

/-!
概要：指定された反転 BK 比較は、元の通常の余錐への増大を保つ。
方針：同じ重みの移送と Under 評価の計算則を合成する。
規約：Kerodon §7.5（Tag 039Y）の既存模型の評価の法則。
使われ方：S8 の元の Čech 増大の照合。余極限性はまだ主張しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Project.FilteredExchange
namespace SerrePositivity.InfinityCategories.Project.SetWeightedTensors
variable {I : Type u} [SmallCategory I] {F : I ⥤ SSet.{u}}

/-- 指定 replacement 比較は元の通常の余錐への同じ増大と可換。 -/
lemma reflectedBousfieldKanReplacementIso_augmentation (c : Cocone F) :
    (reflectedBousfieldKanReplacementIso F).hom ≫ replacementCoconeAugmentation c =
      weightedColimitAugmentation (bousfieldKanWeight Iᵒᵖ ⋙ SSet.opFunctor) c := by
  change ((weightedColimitWeightIso (reflectedBousfieldKanUnderWeightIso I) F).hom ≫
    underWeightedColimitToReplacement F) ≫ replacementCoconeAugmentation c = _
  rw [Category.assoc, underWeightedColimitToReplacement_augmentation,
    weightedColimitWeightIso_augmentation]

end SerrePositivity.InfinityCategories.Project.SetWeightedTensors
