module

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.ReflectedBousfieldKanElements
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSectionsNaturality
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.UnderWeightedColimitNaturality
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.WeightedColimitWeightNaturality

/-!
概要：元の反転 BK coend と元の圏の指定比較は、集合値係数の全ての射に自然。
方針：既存の三つの自然性を合成し、元の elementsToReplacement の同じ順方向で照合する。
規約：Kerodon §7.5（Tag 039Y）、Construction 5.3.2.1（Tag 035V）の既存模型の自然性。
使われ方：S8 の Čech 解消の同じ増大と余極限の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
namespace SerrePositivity.InfinityCategories.Project.SetWeightedTensors
variable {I : Type u} [SmallCategory I]

/-- 元の反転 BK と replacement の指定比較は係数に自然。 -/
lemma reflectedBousfieldKanReplacementIso_naturality {F G : I ⥤ SSet.{u}} (η : F ⟶ G) :
    weightedColimitMap (bousfieldKanWeight Iᵒᵖ ⋙ SSet.opFunctor) η ≫
      (reflectedBousfieldKanReplacementIso G).hom =
      (reflectedBousfieldKanReplacementIso F).hom ≫ simplicialReplacementMap η := by
  change weightedColimitMap _ η ≫
    ((weightedColimitWeightIso (reflectedBousfieldKanUnderWeightIso I) G).hom ≫
      underWeightedColimitToReplacement G) =
    ((weightedColimitWeightIso (reflectedBousfieldKanUnderWeightIso I) F).hom ≫
      underWeightedColimitToReplacement F) ≫ simplicialReplacementMap η
  rw [← Category.assoc, weightedColimitWeightIso_naturality, Category.assoc,
    underWeightedColimitToReplacement_naturality, ← Category.assoc]

/-- 同じ元の圏の比較の後に既存の順方向を合成すると、指定 replacement 比較に戻る。 -/
lemma reflectedBousfieldKanElementsIso_comp_elements (P : I ⥤ Type u) :
    (reflectedBousfieldKanElementsIso P).hom ≫ elementsToReplacement P =
      (reflectedBousfieldKanReplacementIso (coefficients P)).hom := by
  change ((reflectedBousfieldKanReplacementIso (coefficients P)).hom ≫
    (asIso (elementsToReplacement P)).inv) ≫ (asIso (elementsToReplacement P)).hom = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- 集合値係数の全ての射に対し、同じ元の圏の nerve の射で自然性が成り立つ。 -/
lemma reflectedBousfieldKanElementsIso_naturality {P Q : I ⥤ Type u} (φ : P ⟶ Q) :
    weightedColimitMap (bousfieldKanWeight Iᵒᵖ ⋙ SSet.opFunctor) (SetWeight.coefficientsMap φ) ≫
      (reflectedBousfieldKanElementsIso Q).hom =
      (reflectedBousfieldKanElementsIso P).hom ≫ nerveMap φ.mapElements := by
  apply (cancel_mono (elementsToReplacement Q)).mp
  rw [Category.assoc, reflectedBousfieldKanElementsIso_comp_elements, Category.assoc,
    SetWeight.elementsToReplacement_naturality, ← Category.assoc,
    reflectedBousfieldKanElementsIso_comp_elements]
  exact reflectedBousfieldKanReplacementIso_naturality (SetWeight.coefficientsMap φ)

end SerrePositivity.InfinityCategories.Project.SetWeightedTensors
