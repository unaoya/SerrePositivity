module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MarkedValueSpineFold
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MarkedValueSpineCoreDescent

/-!
# 元の反転関手の指定値の因子列からの延長

概要：元の指定矢を反転する関手を、同じ値の因子列の圏から延長する。
方針：指定部分の Core への自由延長と非指定生成矢の元の像を列で合成する。
規約：元の自由圏からの関手を厳密に回収する。
使われ方：通常の局所化 Hom との比較。
-/

@[expose] public section
universe u uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open _root_.CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)
  {D : Type uD} [Category.{vD} D] (F : Paths C ⥤ D) (hF : W.paths.IsInvertedBy F)

def valueDescent : letI := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueCategory W
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.ValueObjects C ⥤ D := by
  letI := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueCategory W
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueFoldFunctor W (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.markedValueDescent W F hF) (fun g => F.map g.val.hom.toPath)

lemma valueDescent_marked : letI := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueCategory W
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueMarkedFunctor W ⋙ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueDescent W F hF = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.markedValueDescent W F hF :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueFoldFunctor_marked W _ _

lemma valueDescent_generator (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W) : letI := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueCategory W
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueDescent W F hF).map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.ValueSpine.generator W g) = F.map g.val.hom.toPath :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueFoldFunctor_generator W _ _ g

lemma valueDescent_fac : letI := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueCategory W
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueLift W ⋙ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueDescent W F hF = F := by
  let := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueCategory W
  apply Paths.ext_functor (F := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueLift W ⋙ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueDescent W F hF) (G := F)
    (funext (fun _ => rfl))
  intro X Y f
  simp only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id]
  by_cases hf : W f
  · rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueLift_marked W f hf]
    exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.markedValueDescent_generator W F hF ⟨f, hf⟩
  · rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueLift_unmarked W f hf]
    exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueDescent_generator W F hF ⟨⟨X, Y, f⟩, hf⟩

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
