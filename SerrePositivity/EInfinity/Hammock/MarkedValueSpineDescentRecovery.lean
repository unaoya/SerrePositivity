module

public import SerrePositivity.EInfinity.Hammock.MarkedValueSpineDescent

/-!
# 元の指定部分の反転関手への回収

概要：指定自由 groupoid からの延長を元の指定生成圏・指定部分圏へ戻す。
方針：元の二つの包含の回収式と、元の指定射列の持ち上げの回収を使う。
規約：元の全対象と全射を厳密に保持する。
使われ方：指定 hammock の元の局所化評価との比較。
-/

@[expose] public section
universe u uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)
  {D : Type uD} [Category.{vD} D] (F : Paths C ⥤ D) (hF : W.paths.IsInvertedBy F)

lemma markedValueDescent_positive_fac :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation (Q := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver W) ⋙
      markedValueDescent W F hF = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.inclusion W ⋙ F := by
  let := valueCategory W
  rw [← valueDescent_marked W F hF, ← Functor.assoc, ← valueLift_marked_fac,
    Functor.assoc, valueDescent_fac]

lemma fromWide_inclusion : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorCategory.fromWide W ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.inclusion W =
    wideSubcategoryInclusion W.paths := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.inclusion_lift W f.hom f.property

lemma nativeFreeEvaluation_descent :
    AllMarked.nativeFreeEvaluation W ⋙ markedValueDescent W F hF =
      wideSubcategoryInclusion W.paths ⋙ F := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorCategory.fromWide W ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation) ⋙ _ = _
  rw [Functor.assoc, markedValueDescent_positive_fac, ← Functor.assoc, fromWide_inclusion]

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
