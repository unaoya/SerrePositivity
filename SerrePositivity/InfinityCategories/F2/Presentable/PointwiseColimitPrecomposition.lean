module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.CoconeValEquality
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorCoconeEvaluation
public import SerrePositivity.InfinityCategories.F1.PreFiberKan
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentCoconeTransport

/-!
概要：元の点ごとの余極限余錐を、関手の定義域の前合成と図式の等号で輸送する。
方針：同じ全余錐の評価を元の評価へ厳密に戻す。
規約：余錐の頂点や脚を選び直さない。使われ方：WithInitial の模型から元の錐形状へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 元の点ごとの余極限は、関手の定義域の任意の前合成で保たれる。 -/
lemma pointwiseColimitCocone_precomp {J K A X : SSet.{u}} [Quasicategory X]
    {p : J ⟶ (ihom K).obj X} (c : JoinCocone p) (hc : IsPointwiseColimitCone c)
    (a : A ⟶ K) : IsPointwiseColimitCone (mapJoinCocone ((pre a).app X) c) := by
  intro k
  have hv : (evaluateFunctorCocone (mapJoinCocone ((pre a).app X) c) k).val =
      (evaluateFunctorCocone c (a.app _ k)).val := by
    change (c.val ≫ (pre a).app X) ≫ evaluateFunctorAt k = c.val ≫ evaluateFunctorAt _
    rw [Category.assoc, evaluateFunctorAt_pre]
  exact (isColimitCone_iff_of_cocone_val_eq _ _ hv).mpr (hc (a.app _ k))

/-- 元の図式の等号による全余錐の輸送も、点ごとの余極限性を保つ。 -/
lemma pointwiseColimitCocone_diagramEq {J K X : SSet.{u}}
    {p q : J ⟶ (ihom K).obj X} (h : p = q) (c : JoinCocone p)
    (hc : IsPointwiseColimitCone c) :
    IsPointwiseColimitCone (HomotopyLimits.coherentCoconeOfDiagramEq h c) := by
  cases h
  exact hc

end SerrePositivity.InfinityCategories.F2.Presentable
