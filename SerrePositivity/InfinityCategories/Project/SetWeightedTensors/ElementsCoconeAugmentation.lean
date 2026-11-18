module

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.ReflectedBousfieldKanAugmentation
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.ReflectedBousfieldKanElementsNaturality
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteNerveIso

/-!
概要：集合値図式の通常の余錐の増大は、元の圏から離散な頂点への元の関手の nerve である。
方針：同じ余錐の脚を元で評価し、既存 replacement 比較を各単体で照合する。
規約：Kerodon Construction 5.3.2.1（Tag 035V）の既存模型の評価の法則。
使われ方：S8 の Čech 増大で、元の圏の収縮を反転 BK coend の同じ増大へ通す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Project.FilteredExchange
namespace SerrePositivity.InfinityCategories.Project.SetWeightedTensors
variable {I : Type u} [SmallCategory I] {P : I ⥤ Type u}

/-- 元の通常の余錐の離散係数への同じ像。 -/
abbrev setCoconeCoefficients (c : Cocone P) : Cocone (coefficients P) :=
  (setsToKan ⋙ kanObjectForget).mapCocone c

/-- 元の圏の各元を、元の余錐の脚で離散な頂点へ送る。 -/
def elementsCoconeFunctor (c : Cocone P) : P.Elements ⥤ Discrete c.pt where
  obj a := Discrete.mk (c.ι.app a.obj a.val)
  map {a b} f := eqToHom (by
    apply Discrete.ext
    change c.ι.app a.obj a.val = c.ι.app b.obj b.val
    rw [← f.map_val]
    exact (ConcreteCategory.congr_hom (c.w f.hom) a.val).symm)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- 元の圏から元の余錐の頂点への同じ増大。 -/
def elementsCoconeAugmentation (c : Cocone P) :
    nerve P.Elements ⟶ (setCoconeCoefficients c).pt :=
  nerveMap (elementsCoconeFunctor c) ≫
    (SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteNerveIso.iso
      c.pt).hom

/-- 同じ replacement の順方向で、元の関手の nerve の全単体の式を回収する。 -/
lemma elementsToReplacement_augmentation (c : Cocone P) :
    elementsToReplacement P ≫ replacementCoconeAugmentation (setCoconeCoefficients c) =
      elementsCoconeAugmentation c := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  rfl

/-- 元の反転 BK 増大を、同じ離散な頂点への元の圏の関手の nerve と照合する。 -/
lemma reflectedBousfieldKanElementsIso_augmentation (c : Cocone P) :
    (reflectedBousfieldKanElementsIso P).hom ≫ elementsCoconeAugmentation c =
      weightedColimitAugmentation (bousfieldKanWeight Iᵒᵖ ⋙ SSet.opFunctor)
        (setCoconeCoefficients c) := by
  rw [← elementsToReplacement_augmentation, ← Category.assoc,
    reflectedBousfieldKanElementsIso_comp_elements,
    reflectedBousfieldKanReplacementIso_augmentation]

end SerrePositivity.InfinityCategories.Project.SetWeightedTensors
