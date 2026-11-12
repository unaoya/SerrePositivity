module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportSquareConstantTopNaturality
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.KanRightCompositionMoving

/-!
概要：元の動く Kan 合成比較を、同じ実四角形の指定 constantTopIso へ値まで戻す。
方針：元の定義で行った端点の表示変更だけを外す。
規約：元の比較を選び直さない。使われ方：元の Kan 合成比較の指定自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の動く合成比較は、同じ元の係数四角形の constantTopIso の指定値を保つ。 -/
lemma coherentKanRightCompositionMovingIso_heq_constantTop {K L M : KanObject.{u}}
    {P : SSet.{u + 1}}
    (x : P ⟶ vertexFiber pointedSpaceProjection (spaceInfinityVertex K))
    (y : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L))
    (z : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom L M))
    (ht : intervalMappingUncurry
      ((coherentKanRightCompositionSquare K L M).precomp (lift y z)).top =
        SSet.const (spaceInfinityVertex M)) :
    HEq (coherentKanRightCompositionTransport_movingIso x y z)
      (((coherentKanRightCompositionSquare K L M).precomp (lift y z)).constantTopIso
        pointedSpaceProjection x ht) := by
  have hcast {α β : Sort (u + 2)} (h : α = β) (v : α) : HEq (Eq.mp h v) v := by
    cases h
    rfl
  have hcast' {α β : Sort (u + 2)} (h : α = β) (v : β) : HEq (Eq.mpr h v) v := by
    cases h
    rfl
  unfold coherentKanRightCompositionTransport_movingIso
  dsimp only
  exact (hcast' _ _).trans (hcast _ _)

end SerrePositivity.InfinityCategories.F2
