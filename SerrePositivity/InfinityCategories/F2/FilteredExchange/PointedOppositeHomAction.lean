module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CurriedSwapAction
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedCoherentHomComposition

/-!
概要：全反転 Hom の合成作用を、同じ実 pointed fiber への関手の全族にする。
方針：元の二係数の合成を curry する。
規約：Kan 射の一点だけでなく全 Hom を保持する。
使われ方：元の指定精密化の反転と指定比較の実終点辺を同じ path として読む。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable (K L : KanObject.{u})
/-- 元の全反転 Hom による合成を実 pointed fiber の関手族として保持する。 -/
def pointedOppositeHomAction :
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L).op ⟶
      (ihom ((SSet.uliftFunctor.{u + 1, u}).obj
        (SimplicialCategory.sHom pointKanObject K).op)).obj
          (vertexFiber pointedSpaceProjection (coherentNerveVertex L)) :=
  curry ((β_ ((SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom pointKanObject K).op)
      ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L).op)).hom ≫
    (uliftTensorIso (SimplicialCategory.sHom K L).op
      (SimplicialCategory.sHom pointKanObject K).op).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (oppositeHomPrecomposition pointKanObject K L) ≫
        pointedCoherentFiberComparison L)

/-- 同じ関手族を任意の係数へ制限すると元の全 Hom 合成作用の円柱を回収する。 -/
lemma pointedOppositeHomAction_uncurry {P : SSet.{u + 1}}
    (r : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L).op) :
    uncurry (r ≫ pointedOppositeHomAction K L) =
      lift (snd ((SSet.uliftFunctor.{u + 1, u}).obj
        (SimplicialCategory.sHom pointKanObject K).op) P ≫ r)
        (fst ((SSet.uliftFunctor.{u + 1, u}).obj
          (SimplicialCategory.sHom pointKanObject K).op) P) ≫
        (uliftTensorIso (SimplicialCategory.sHom K L).op
          (SimplicialCategory.sHom pointKanObject K).op).inv ≫
          (SSet.uliftFunctor.{u + 1, u}).map (oppositeHomPrecomposition pointKanObject K L) ≫
            pointedCoherentFiberComparison L :=
  curriedSwapAction_uncurry r _

end SerrePositivity.InfinityCategories.F2
