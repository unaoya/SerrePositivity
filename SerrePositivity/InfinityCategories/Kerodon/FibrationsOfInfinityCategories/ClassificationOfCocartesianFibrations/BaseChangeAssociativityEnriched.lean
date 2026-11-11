module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.BaseChangeAssociativityAction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.BaseChangeEnrichedComparison

/-!
概要：底変換の同じ結合同型は、元の全 fibration の全高次 Hom に自然な豊穣比較。
方針：元の全相対 section 作用の可換式を、豊穣比較の自然性へ渡す。
規約：元の二回の底変換関手と直接の底変換関手の Hom 作用を保持する。
使われ方：底全体と元の分類主写像の全高次に同時に自然な結合比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 同じ結合同型は、二回の底変換と直接の底変換の section 評価の間の豊穣比較。 -/
def cocartesianBaseChangeAssociativityEnrichedComparison
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (a : A) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparison
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFibrationBaseChangeEnriched (nerveMap k)).comp SSet
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFibrationBaseChangeEnriched (nerveMap l))).comp SSet
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsEnrichedEvaluation (Over.mk (nerveMap (Under.forget a)))))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFibrationBaseChangeEnriched (nerveMap (l ⋙ k))).comp SSet
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsEnrichedEvaluation (Over.mk (nerveMap (Under.forget a))))) := by
  refine ⟨fun p ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityComponent p.val.hom l k a).hom, ?_⟩
  intro p q
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityComponent p.val.hom l k a).hom ▷ _) ≫
      uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeRestriction p.val.hom q.val.hom
        (Over.mk (nerveMap (l ⋙ k))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsPostHom (Over.mk (nerveMap (Under.forget a)))
          (Over.mk (pullback.fst (nerveMap (l ⋙ k)) p.val.hom))
          (Over.mk (pullback.fst (nerveMap (l ⋙ k)) q.val.hom))) =
    uncurry ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeRestriction p.val.hom q.val.hom
      (Over.mk (nerveMap k)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeRestriction
        (pullback.fst (nerveMap k) p.val.hom) (pullback.fst (nerveMap k) q.val.hom)
          (Over.mk (nerveMap l))) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsPostHom (Over.mk (nerveMap (Under.forget a)))
        (Over.mk (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p.val.hom)))
        (Over.mk (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) q.val.hom)))) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityComponent q.val.hom l k a).hom
  rw [uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsPostHom, uncurry_curry,
    uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsPostHom, uncurry_curry,
    ← Category.assoc, ← tensorHom_def]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityComponent_action p.val.hom q.val.hom l k a).symm

/-- 豊穣比較の成分は、元の section の結合同型そのもの。 -/
lemma cocartesianBaseChangeAssociativityEnrichedComparison_component
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (a : A) (p : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationObject (nerve C)) :
    (cocartesianBaseChangeAssociativityEnrichedComparison l k a).val p =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityComponent p.val.hom l k a).hom := rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
