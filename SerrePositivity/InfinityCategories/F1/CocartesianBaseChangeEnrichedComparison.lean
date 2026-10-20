module

public import SerrePositivity.InfinityCategories.F1.QuasicategoryEnrichedComparison
public import SerrePositivity.InfinityCategories.F1.CocartesianFibrationBaseChange
public import SerrePositivity.InfinityCategories.F1.CocartesianStrictTransportBaseChangeAction
public import SerrePositivity.InfinityCategories.F1.CocartesianStrictTransportBaseChangeEquivalence
public import SerrePositivity.InfinityCategories.F1.CocartesianSectionsEnrichedEvaluation

/-!
概要：元の strict transport の底変換比較を、全 fibration の全 Hom に自然な豊穣比較へ束ねる。
方針：元の全パラメーターの section 作用の可換式を比較の条件へ渡す。
規約：元の底変換の豊穣関手と、構成済みの同じ比較成分を使う。
使われ方：同じ分類主写像の底変換との coherent な比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 同じ strict transport の底変換比較は、全 fibration の元の全相対 Hom に対して自然。 -/
def cocartesianBaseChangeEnrichedComparison
    {C D : Type u} [Category.{u} C] [Category.{u} D] (k : D ⥤ C) (d : D) :
    QuasicategoryEnrichedComparison
      (cocartesianSectionsEnrichedEvaluation (Over.mk (nerveMap (Under.forget (k.obj d)))))
      ((cocartesianFibrationBaseChangeEnriched (nerveMap k)).comp SSet
        (cocartesianSectionsEnrichedEvaluation (Over.mk (nerveMap (Under.forget d))))) := by
  refine ⟨fun p ↦ cocartesianStrictTransportBaseChangeComponent p.val.hom k d, ?_⟩
  intro p q
  change (cocartesianStrictTransportBaseChangeComponent p.val.hom k d ▷ _) ≫
      uncurry (cocartesianPullbackNativeRestriction p.val.hom q.val.hom (Over.mk (nerveMap k)) ≫
        cocartesianSectionsPostHom (Over.mk (nerveMap (Under.forget d)))
          (Over.mk (pullback.fst (nerveMap k) p.val.hom))
          (Over.mk (pullback.fst (nerveMap k) q.val.hom))) =
    uncurry (cocartesianSectionsPostHom (Over.mk (nerveMap (Under.forget (k.obj d))))
      p.val q.val) ≫ cocartesianStrictTransportBaseChangeComponent q.val.hom k d
  rw [uncurry_natural_left, cocartesianSectionsPostHom, uncurry_curry,
    cocartesianSectionsPostHom, uncurry_curry, ← Category.assoc, ← tensorHom_def]
  exact (cocartesianStrictTransportBaseChangeComponent_action p.val.hom q.val.hom k d).symm

/-- 全 fibration の同じ比較成分は、構成済みの実際の成分そのもの。 -/
lemma cocartesianBaseChangeEnrichedComparison_component
    {C D : Type u} [Category.{u} C] [Category.{u} D] (k : D ⥤ C) (d : D)
    (p : CocartesianFibrationObject (nerve C)) :
    (cocartesianBaseChangeEnrichedComparison k d).val p =
      cocartesianStrictTransportBaseChangeComponent p.val.hom k d := rfl

end SerrePositivity.InfinityCategories
