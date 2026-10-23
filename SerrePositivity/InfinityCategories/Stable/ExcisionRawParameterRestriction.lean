module
public import SerrePositivity.InfinityCategories.Stable.ExcisionRawSuspensionSquare
public import SerrePositivity.InfinityCategories.Stable.ExcisionSuspensionCospanRestriction
public import SerrePositivity.InfinityCategories.F2.Compact.FlipEvaluation

/-!
概要：四つの実 suspension 面の引き戻し性から、元の押し出しの像の普遍性を導く。
方針：全 cospan の厳密保存、同じ θ と対角合成、元の入力面の極限錐を接続する。
規約：標的の零対象や一般安定性は仮定しない。使われ方：一般切除・loop 同値判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma excisionRawSuspensionSquare_replaced_evaluate_cospan {X : SSet.{u}}
    {F : nerve ExcisionGridIndex.{u} ⟶ X}
    (c : JoinCone (nerveMap (posetSubtypeInclusion IsExcisionFullPunctured) ≫ F))
    (j : (horn 2 2 : SSet.{u}) _⦋0⦌) :
    excisionRawSuspensionSquare (excisionReplaceInitial c) ≫ evaluateFunctorAt
      (cospanSquareBoundary.app (Opposite.op ⦋0⦌) j) =
    excisionRawSuspensionSquare F ≫ evaluateFunctorAt
      (cospanSquareBoundary.app (Opposite.op ⦋0⦌) j) := by
  apply functorVertex_injective
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (excisionRawSuspensionFamily_replaced_cospan c) (Opposite.op ⦋0⦌)) j
  exact (F2.Compact.flipFamily_evaluate_vertex
    (excisionRawSuspensionFamily (excisionReplaceInitial c))
      (cospanSquareBoundary.app (Opposite.op ⦋0⦌) j)).trans
    (h.trans (F2.Compact.flipFamily_evaluate_vertex (excisionRawSuspensionFamily F)
      (cospanSquareBoundary.app (Opposite.op ⦋0⦌) j)).symm)

end SerrePositivity.InfinityCategories
