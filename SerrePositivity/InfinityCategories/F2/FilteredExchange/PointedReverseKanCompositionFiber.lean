module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedReverseKanHomComposition

/-!
概要：反対 Kan の同じ全合成の pointed fiber 像を元の反転 Hom 作用へ戻す。
方針：全 Hom 合成の一致に元の交換同型と fiber 比較を後合成する。
規約：同じ終点表示の移送を保持。使われ方：全係数の左区間輸送の値の式。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 同じ反転合成の実 fiber 像は、元の Hom 合成作用の終点表示変更そのもの。 -/
lemma pointedReverseKanComposition_fiber (K L : KanObject.{u}) :
    ((uliftOppositeIso (SimplicialCategory.sHom pointKanObject K)).hom ⊗ₘ
      (uliftOppositeIso (SimplicialCategory.sHom K L)).hom) ≫
      coherentReverseHomComposition (Opposite.op L) (Opposite.op K)
        (Opposite.op pointKanObject) ≫ pointedReverseKanFiberComparison L =
    (β_ ((SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom pointKanObject K).op)
      ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L).op)).hom ≫
      (uliftTensorIso (SimplicialCategory.sHom K L).op
        (SimplicialCategory.sHom pointKanObject K).op).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (oppositeHomPrecomposition pointKanObject K L) ≫
      pointedCoherentFiberComparison L ≫
        eqToHom (congrArg (vertexFiber pointedSpaceProjection)
          (spaceInfinityVertex_eq_coherent L).symm) := by
  have h := congrArg (fun f => f ≫
    (uliftOppositeIso (SimplicialCategory.sHom pointKanObject L)).hom ≫
      pointedReverseKanFiberComparison L) (pointedReverseKanHomComposition_normalized K L)
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at h
  rw [pointedReverseKanFiberComparison_normalized] at h
  exact h

end SerrePositivity.InfinityCategories.F2
