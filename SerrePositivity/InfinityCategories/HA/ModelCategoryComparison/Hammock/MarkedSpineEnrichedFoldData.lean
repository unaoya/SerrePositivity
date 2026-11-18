module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedDegreeSimplex
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MarkedSpineFoldSimplex
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MarkedSpineFoldTarget
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MarkedSpineEnrichedCategory

/-!
# 任意の単体的豊穣目標への自由積の像の指定

概要：元の指定 hammock と非指定生成矢の像を単体写像として指定する。
方針：各次数で評価して同じ元の FoldData を得る。
規約：指定部分の単位・合成を保つ像を仮定し、弱比較は仮定しない。
使われ方：元の全因子列からの一意な豊穣拡張。
-/

@[expose] public section
universe u uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{u} C]

structure EnrichedFoldData (W : MorphismProperty C) (D : Type uD)
    [EnrichedCategory SSet.{u} D] where
  obj : Paths C → D
  marked : ∀ X Y, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeSpace W X Y ⟶ obj X ⟶[SSet.{u}] obj Y
  generator : ∀ g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W, 𝟙_ SSet.{u} ⟶ obj g.val.left ⟶[SSet.{u}] obj g.val.right
  marked_unit : ∀ X,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit (⊤ : MorphismProperty (WideSubcategory W.paths)) ⟨X⟩ ≫ marked X X =
      eId SSet.{u} (obj X)
  marked_comp : ∀ X Y Z,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition (⊤ : MorphismProperty (WideSubcategory W.paths)) ⟨X⟩ ⟨Y⟩ ⟨Z⟩ ≫ marked X Z =
      (marked X Y ⊗ₘ marked Y Z) ≫ eComp SSet.{u} (obj X) (obj Y) (obj Z)

namespace EnrichedFoldData
variable {W : MorphismProperty C} {D : Type uD} [EnrichedCategory SSet.{u} D]
  (F : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.EnrichedFoldData W D)

def degreeData (n : SimplexCategoryᵒᵖ) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedDegreeCategory.category (D := D) n
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.FoldData W n (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedDegreeCategory.Objects D) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedDegreeCategory.category (D := D) n
  exact
    { obj := F.obj
      marked := fun {X Y} p => (F.marked X Y).app n p
      generator := fun g => (F.generator g).app n PUnit.unit
      marked_unit := fun X => congrArg (fun k => k.app n PUnit.unit) (F.marked_unit X)
      marked_comp := fun {X Y Z} p q =>
        congrArg (fun k => k.app n (p, q)) (F.marked_comp X Y Z) }

def foldPoint {X Y : Paths C} (n : SimplexCategoryᵒᵖ) (t : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine W Y n X) :
    (F.obj X ⟶[SSet.{u}] F.obj Y).obj n :=
  @_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.FoldData.fold C _ W n (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedDegreeCategory.Objects D) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedDegreeCategory.category n)
    (F.degreeData n) X Y t

end EnrichedFoldData
end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
