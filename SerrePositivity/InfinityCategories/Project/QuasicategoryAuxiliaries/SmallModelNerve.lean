module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.EssentiallySmall

/-!
概要：本質的に小さい圏の小模型から元の圏への比較を nerve に写す。
規約：小模型の単体だけを持ち上げる。比較の向きは equivSmallModel の逆関手。
使われ方：小さい site から元の大きい圏上の図式を制限する。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 小模型の各射列を、選んだ同値の逆関手によって元の圏へ送る。 -/
def smallModelNerveComparison (C : Type (u + 1)) [Category.{u} C] [EssentiallySmall.{u} C] :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve (SmallModel.{u} C)) ⟶ nerve C where
  app _ := ↾fun σ => σ.down ⋙ (equivSmallModel.{u} C).inverse
  naturality _ _ _ := rfl

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
