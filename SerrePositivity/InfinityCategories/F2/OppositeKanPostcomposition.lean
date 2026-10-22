module

public import SerrePositivity.InfinityCategories.F2.PointedOppositeHomActionVertex

/-!
概要：元の Kan 射の二辺合成による全反転 Hom の後合成は二段の作用に等しい。
方針：豊穣 Hom の後合成則を反転関手と宇宙持ち上げで写す。
規約：元の二辺と同じ全係数を保持する。
使われ方：指定終点同型の始点を元の二段の全係数作用へ正規化する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 元の二辺合成による全反転 Hom の作用は元の二段の後合成に厳密に等しい。 -/
lemma uliftOppositeKanPostcomposition_comp {K L M : KanObject.{u}}
    (f : K ⟶ L) (g : L ⟶ M) :
    (SSet.uliftFunctor.{u + 1, u}).map
      (SSet.opFunctor.map (eHomWhiskerLeft SSet pointKanObject (f ≫ g))) =
    (SSet.uliftFunctor.{u + 1, u}).map
      (SSet.opFunctor.map (eHomWhiskerLeft SSet pointKanObject f)) ≫
    (SSet.uliftFunctor.{u + 1, u}).map
      (SSet.opFunctor.map (eHomWhiskerLeft SSet pointKanObject g)) := by
  rw [eHomWhiskerLeft_comp, Functor.map_comp, Functor.map_comp]

end SerrePositivity.InfinityCategories.F2
