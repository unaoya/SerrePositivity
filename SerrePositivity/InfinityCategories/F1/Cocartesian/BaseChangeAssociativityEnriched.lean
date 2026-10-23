module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeAssociativityAction
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeEnrichedComparison

/-!
概要：底変換の同じ結合同型は、元の全 fibration の全高次 Hom に自然な豊穣比較。
方針：元の全相対 section 作用の可換式を、豊穣比較の自然性へ渡す。
規約：元の二回の底変換関手と直接の底変換関手の Hom 作用を保持する。
使われ方：底全体と元の分類主写像の全高次に同時に自然な結合比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 同じ結合同型は、二回の底変換と直接の底変換の section 評価の間の豊穣比較。 -/
def cocartesianBaseChangeAssociativityEnrichedComparison
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (a : A) :
    QuasicategoryEnrichedComparison
      (((cocartesianFibrationBaseChangeEnriched (nerveMap k)).comp SSet
        (cocartesianFibrationBaseChangeEnriched (nerveMap l))).comp SSet
          (cocartesianSectionsEnrichedEvaluation (Over.mk (nerveMap (Under.forget a)))))
      ((cocartesianFibrationBaseChangeEnriched (nerveMap (l ⋙ k))).comp SSet
        (cocartesianSectionsEnrichedEvaluation (Over.mk (nerveMap (Under.forget a))))) := by
  refine ⟨fun p ↦ (cocartesianBaseChangeAssociativityComponent p.val.hom l k a).hom, ?_⟩
  intro p q
  change ((cocartesianBaseChangeAssociativityComponent p.val.hom l k a).hom ▷ _) ≫
      uncurry (cocartesianPullbackNativeRestriction p.val.hom q.val.hom
        (Over.mk (nerveMap (l ⋙ k))) ≫
        cocartesianSectionsPostHom (Over.mk (nerveMap (Under.forget a)))
          (Over.mk (pullback.fst (nerveMap (l ⋙ k)) p.val.hom))
          (Over.mk (pullback.fst (nerveMap (l ⋙ k)) q.val.hom))) =
    uncurry ((cocartesianPullbackNativeRestriction p.val.hom q.val.hom
      (Over.mk (nerveMap k)) ≫ cocartesianPullbackNativeRestriction
        (pullback.fst (nerveMap k) p.val.hom) (pullback.fst (nerveMap k) q.val.hom)
          (Over.mk (nerveMap l))) ≫
      cocartesianSectionsPostHom (Over.mk (nerveMap (Under.forget a)))
        (Over.mk (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p.val.hom)))
        (Over.mk (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) q.val.hom)))) ≫
      (cocartesianBaseChangeAssociativityComponent q.val.hom l k a).hom
  rw [uncurry_natural_left, cocartesianSectionsPostHom, uncurry_curry,
    uncurry_natural_left, cocartesianSectionsPostHom, uncurry_curry,
    ← Category.assoc, ← tensorHom_def]
  exact (cocartesianBaseChangeAssociativityComponent_action p.val.hom q.val.hom l k a).symm

/-- 豊穣比較の成分は、元の section の結合同型そのもの。 -/
lemma cocartesianBaseChangeAssociativityEnrichedComparison_component
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (a : A) (p : CocartesianFibrationObject (nerve C)) :
    (cocartesianBaseChangeAssociativityEnrichedComparison l k a).val p =
      (cocartesianBaseChangeAssociativityComponent p.val.hom l k a).hom := rfl

end SerrePositivity.InfinityCategories
