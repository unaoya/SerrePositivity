module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedLeftHomDiagonalValue
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoPrecompEndpointTransport

/-!
概要：元の左全対角値比較の表示変更を、同じ全係数の制限でも除去する。
方針：元の反転合成の指定比較へ戻し、両端の表示変更だけを除く。
規約：元の実全 prism と比較を保持。使われ方：元の固定射の比較の実 prism 表示。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 元の左全対角値比較の同じ係数制限は、元の全反転合成の値比較の同じ制限。 -/
lemma pointedLeftHomDiagonalValueIso_precomp_heq_reverse {P Q : SSet.{u + 1}}
    (K L : KanObject.{u})
    (x : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom pointKanObject K).op)
    (y : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L).op)
    (r : Q ⟶ P) :
    HEq ((pointedLeftHomDiagonalValueIso K L x y).precomp r)
      ((pointedReverseKanDiagonalValueIso K L x y).precomp r) := by
  unfold pointedLeftHomDiagonalValueIso
  exact functorIsoOfEq_precomp_heq _ _ _ r

end SerrePositivity.InfinityCategories.F2
