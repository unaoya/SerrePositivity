module

public import SerrePositivity.InfinityCategories.F2.Presentable.FunctorColimitCreation
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorPointwiseColimitCriterion

/-!
概要：指定形状を保つ関手の後合成は、関手圏でも同じ形状の余極限を保つ。
方針：元の余極限を各点で計算し、像の点ごとの余極限性をまとめる。
規約：元の指定余錐の像を保持する。
使われ方：有限余積比較の両側の生成操作保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：指定した形状の余極限保存は後合成関手にも移る。
方針：元の各点での余極限と指定した像の各点での余極限を使う。
規約：始域に同じ形状の余極限の存在だけを要求する。
使われ方：有限余積の全関手比較の保存条件。 -/
lemma postcomposition_map_isColimit {J A X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (hX : ∀ p : J ⟶ X, HasColimit p) (q : X ⟶ Y)
    (hq : ∀ (p : J ⟶ X) (c : JoinCocone p), IsColimitCone c →
      IsColimitCone (mapJoinCocone q c))
    {p : J ⟶ (ihom A).obj X} (c : JoinCocone p) (hc : IsColimitCone c) :
    IsColimitCone (mapJoinCocone ((ihom A).map q) c) := by
  have hpw := isPointwiseColimitCone_of_hasColimits hX c hc
  apply isColimitCone_of_pointwise
  intro a
  have h := hq _ _ (hpw a)
  have hv : (evaluateFunctorCocone (mapJoinCocone ((ihom A).map q) c) a).val =
      (mapJoinCocone q (evaluateFunctorCocone c a)).val := rfl
  exact (isColimitCone_iff_of_cocone_val_eq _ _ hv).mpr h

end SerrePositivity.InfinityCategories.F2.Presentable
