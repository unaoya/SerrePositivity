module

public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.KanCompositionMovingPresentation

/-!
概要：元の定始点 Kan 合成比較を、同じ全 Hom 比較の元の係数制限へ値まで戻す。
方針：元の定義の端点表示の移送だけを外す。
規約：元の指定比較を保持。使われ方：定始点比較と動く始点比較の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の定始点比較は、元の全 Hom 比較の同じ係数制限の指定値を保持する。 -/
lemma coherentKanRightCompositionDiagonalIso_heq_precomp (K L M : KanObject.{u})
    {P : SSet.{u + 1}}
    (v : (vertexFiber pointedSpaceProjection (spaceInfinityVertex K)) _⦋0⦌)
    (y : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L))
    (z : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom L M)) :
    HEq (coherentKanRightCompositionTransport_diagonalIso K L M v y z)
      ((coherentKanRightCompositionTransportIso K L M (SSet.const v)).precomp (lift y z)) := by
  have hm {α β : Sort (u + 2)} (h : α = β) (w : α) : HEq (Eq.mp h w) w := by
    cases h
    rfl
  have hr {α β : Sort (u + 2)} (h : α = β) (w : β) : HEq (Eq.mpr h w) w := by
    cases h
    rfl
  unfold coherentKanRightCompositionTransport_diagonalIso
  dsimp only
  exact (hr _ _).trans (hm _ _)

end SerrePositivity.InfinityCategories.F2
