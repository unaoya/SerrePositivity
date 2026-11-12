module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoDisplayComponent
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoCurryPointComparison

/-!
概要：端点表示を揃えた curry の指定成分を、元の同じ係数制限へ戻す。
方針：表示変更の除去と curry の一点評価を一つの一般補題で合成する。
規約：指定同型を再選択しない。使われ方：巨大な全作用の内部を再展開せず成分を照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 表示変更済みの curry の成分は、同じ元の二係数比較の固定係数への制限。 -/
lemma functorIsoOfEq_curry_app_heq_precomp {A B Y : SSet.{u}}
    [Quasicategory B] [Quasicategory Y] {f g : A ⊗ B ⟶ Y}
    {f' g' : B ⟶ (ihom A).obj Y} (e : FunctorIso f g)
    (hf : curry f = f') (hg : curry g = g') (v : B _⦋0⦌) :
    HEq ((functorIsoOfEq e.curry hf hg).app v)
      (e.precomp (lift (𝟙 A) (SSet.const v))) :=
  (functorIsoOfEq_app_heq e.curry hf hg v).trans (functorIso_curry_app_heq_precomp e v)

end SerrePositivity.InfinityCategories.F2
