module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.SpanCollapse
public import SerrePositivity.InfinityCategories.Stable.PushoutShape
public import SerrePositivity.InfinityCategories.F2.CatInfinity.CoconeValEquality
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorCoconeReindex

/-!
概要：二本の水平辺が恒等である元の縦長退化四角形は pushout である。
方針：元の全余錐を、共終的に畳んだ標準辺の終点余錐と厳密に比較する。
規約：ホモトピー圏の通常の押し出しで代用しない。
使われ方：辺の pushout を射圏内で計算する際の始点側の普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits

/-- 退化四角形の全余錐形状は、畳んだ辺の終点余錐形状そのもの。 -/
lemma spanCoconeSquare_secondProjection :
    spanCoconeSquareIso.{u}.hom ≫ snd (Δ[1] : SSet.{u}) Δ[1] =
      joinMap spanRightCollapse (𝟙 (Δ[0] : SSet.{u})) ≫ (edgeTargetCocone (𝟙 Δ[1])).val := by
  apply spanCocone_isPushout.hom_ext
  · rw [← Category.assoc, spanCoconeSquareIso_left]
    simp only [spanCoconeTriangleLeft, Category.assoc]
    rw [← Category.assoc (joinMap horn₂₀.ι₀₁ (𝟙 Δ[0])), ← joinMap_comp,
      Category.id_comp, spanRightCollapse_left]
    apply SSet.yonedaEquiv.injective
    decide
  · rw [← Category.assoc, spanCoconeSquareIso_right]
    simp only [spanCoconeTriangleRight, Category.assoc]
    rw [← Category.assoc (joinMap horn₂₀.ι₀₂ (𝟙 Δ[0])), ← joinMap_comp,
      Category.id_comp, spanRightCollapse_right]
    apply SSet.yonedaEquiv.injective
    decide

/-- 元の任意の縦辺を横に恒等として伸ばした四角形は、元の全 pushout 四角形。 -/
lemma secondProjection_isPushoutSquare {C : SSet.{u}} [Quasicategory C]
    (g : (Δ[1] : SSet.{u}) ⟶ C) : IsPushoutSquare (snd Δ[1] Δ[1] ≫ g) := by
  have he : (pushoutCocone (snd Δ[1] Δ[1] ≫ g)).val =
      ((edgeTargetCocone g).restrict spanRightCollapse).val := by
    simpa only [pushoutCocone, JoinCocone.restrict, edgeTargetCocone,
      Category.assoc, Category.comp_id] using
      congrArg (fun f ↦ f ≫ g) spanCoconeSquare_secondProjection.{u}
  exact (F2.isColimitCone_iff_of_coconeMap_eq _ _ he).mpr
    (spanRightCollapse_edgeTarget_isColimit g)

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
