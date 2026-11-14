module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.WeightedSectionsParameters
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.ParameterPoint

/-!
概要：重み付き end の作用を切断点で固定すると、元の切断への係数の作用になる。
方針：パラメーター付き end の射影公式と、単位・tensor の自然性を使う。
規約：Kan 性を仮定しない全パラメーターの式。使われ方：BK 切断点から比較族を回収する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra
variable {I : Type u} [SmallCategory I]

/-- 切断点で固定した作用の評価は、その切断の元の成分への係数の作用そのもの。 -/
lemma weightedSectionsParameterMap_point_evaluation (W : I ⥤ SSet.{u})
    {H H' : I ⥤ SSet.{u}} {A : SSet.{u}} (η : H ⋙ tensorRight A ⟶ H')
    (p : 𝟙_ SSet.{u} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W H) (i : I) :
    uncurry ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.family p A ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsParameterMap W η) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W H' i) =
      (((ρ_ (W.obj i)).inv ≫ uncurry (p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W H i)) ▷ A) ≫ η.app i := by
  rw [uncurry_natural_left, whiskerLeft_comp, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsParameterMap_evaluation, uncurry_natural_left]
  have h : (W.obj i ◁ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.family p A) ≫
      (α_ (W.obj i) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W H) A).inv ≫
      (uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W H i) ▷ A) =
      (((ρ_ (W.obj i)).inv ≫ (W.obj i ◁ p) ≫
        uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W H i)) ▷ A) := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨w, a⟩
    rfl
  simpa only [Category.assoc] using congrArg
    (fun f : W.obj i ⊗ A ⟶ H.obj i ⊗ A ↦ f ≫ η.app i) h

end SerrePositivity.KST.Spectra
