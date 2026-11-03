module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanCompositionDiagonalPresentation

/-!
概要：元の定始点と動く始点の Kan 合成比較を、指定値まで同定する。
方針：元の constantTopIso の係数自然性と、元の定始点のグラフ表示を使う。
規約：元の二つの指定比較を保持。使われ方：右 Hom の点評価比較の合成則。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の定始点 Kan 比較は、同じ定始点を入力した元の movingIso と値まで一致する。 -/
lemma coherentKanRightCompositionDiagonalIso_heq_moving (K L M : KanObject.{u})
    {P : SSet.{u + 1}}
    (v : (vertexFiber pointedSpaceProjection (spaceInfinityVertex K)) _⦋0⦌)
    (y : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L))
    (z : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom L M)) :
    HEq (coherentKanRightCompositionTransport_diagonalIso K L M v y z)
      (coherentKanRightCompositionTransport_movingIso (SSet.const v) y z) := by
  let s := (coherentKanRightCompositionSquare K L M).precomp (lift y z)
  have ht : intervalMappingUncurry s.top = SSet.const (spaceInfinityVertex M) :=
    intervalMappingUncurry_precomp_constant _ (coherentKanRightCompositionSquare_top K L M) _
  have h := transportIntervalSquare_constantTopIso_precomp_heq pointedSpaceProjection
    (coherentKanRightCompositionSquare K L M) (SSet.const v)
    (coherentKanRightCompositionSquare_top K L M) (lift y z) ht
  have hsource {f f' : P ⟶ vertexFiber pointedSpaceProjection (spaceInfinityVertex K)}
      (hf : f = f') :
      HEq (s.constantTopIso pointedSpaceProjection f ht)
        (s.constantTopIso pointedSpaceProjection f' ht) := by
    cases hf
    rfl
  exact (coherentKanRightCompositionDiagonalIso_heq_precomp K L M v y z).trans
    (h.trans ((hsource (SSet.comp_const (lift y z) v)).trans
      (coherentKanRightCompositionMovingIso_heq_constantTop (SSet.const v) y z ht).symm))

end SerrePositivity.InfinityCategories.F2
