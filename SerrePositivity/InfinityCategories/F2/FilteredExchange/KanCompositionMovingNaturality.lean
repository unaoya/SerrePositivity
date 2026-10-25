module

public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.KanCompositionMovingPresentation
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.KanCompositionSquareFaces
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.DiagonalSourceIsoCurve

/-!
概要：元の動く Kan 合成比較は、同じ元の始点同型の輸送に自然である。
方針：同じ係数四角形の constantTopIso の始点正方形を、元の三辺へ戻す。
規約：元の指定比較と全 Hom 係数を保持。使われ方：値の二段評価の中間比較の移動。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の合成輸送の指定比較は、同じ始点同型の二段輸送と合成射輸送に自然。 -/
lemma coherentKanRightCompositionMovingIso_source_naturality {K L M : KanObject.{u}}
    {P : SSet.{u + 1}}
    {x x' : P ⟶ vertexFiber pointedSpaceProjection (spaceInfinityVertex K)} (e : FunctorIso x x')
    (y : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L))
    (z : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom L M)) :
    diagonalFiberTransport_sourceIso pointedSpaceProjection
        (diagonalFiberTransport_sourceIso pointedSpaceProjection e
          (y ≫ coherentKanRightHomInterval K L)) (z ≫ coherentKanRightHomInterval L M) ≪≫
      coherentKanRightCompositionTransport_movingIso x' y z =
    coherentKanRightCompositionTransport_movingIso x y z ≪≫
      diagonalFiberTransport_sourceIso pointedSpaceProjection e
        (lift y z ≫ coherentHomComposition K L M ≫ coherentKanRightHomInterval K M) := by
  let s := (coherentKanRightCompositionSquare K L M).precomp (lift y z)
  have hb : s.bottom = y ≫ coherentKanRightHomInterval K L :=
    coherentKanCompositionSquare_bottom y z
  have hr : s.right = z ≫ coherentKanRightHomInterval L M :=
    coherentKanCompositionSquare_right y z
  have hl : s.left = lift y z ≫ coherentHomComposition K L M ≫
      coherentKanRightHomInterval K M := coherentKanCompositionSquare_left y z
  have ht : intervalMappingUncurry s.top = SSet.const (spaceInfinityVertex M) :=
    coherentKanCompositionSquare_top y z
  have hi := diagonalFiberTransport_sourceIso_heq_of_data pointedSpaceProjection e e
    s.bottom (y ≫ coherentKanRightHomInterval K L) rfl rfl HEq.rfl hb
  have hR := diagonalFiberTransport_sourceIso_heq_of_data pointedSpaceProjection
    (diagonalFiberTransport_sourceIso pointedSpaceProjection e s.bottom)
    (diagonalFiberTransport_sourceIso pointedSpaceProjection e
      (y ≫ coherentKanRightHomInterval K L))
    s.right (z ≫ coherentKanRightHomInterval L M)
    (congrArg (diagonalFiberTransport pointedSpaceProjection x) hb)
    (congrArg (diagonalFiberTransport pointedSpaceProjection x') hb) hi hr
  have hL := diagonalFiberTransport_sourceIso_heq_of_data pointedSpaceProjection e e
    s.left (lift y z ≫ coherentHomComposition K L M ≫ coherentKanRightHomInterval K M)
    rfl rfl HEq.rfl hl
  have hvR (v : P ⟶ vertexFiber pointedSpaceProjection (spaceInfinityVertex K)) :
      functorVertex (diagonalFiberTransport pointedSpaceProjection
        (diagonalFiberTransport pointedSpaceProjection v s.bottom) s.right) =
      functorVertex (diagonalFiberTransport pointedSpaceProjection
        (diagonalFiberTransport pointedSpaceProjection v (y ≫ coherentKanRightHomInterval K L))
          (z ≫ coherentKanRightHomInterval L M)) := by rw [hb, hr]
  have hvL (v : P ⟶ vertexFiber pointedSpaceProjection (spaceInfinityVertex K)) :
      functorVertex (diagonalFiberTransport pointedSpaceProjection v s.left) =
      functorVertex (diagonalFiberTransport pointedSpaceProjection v
        (lift y z ≫ coherentHomComposition K L M ≫ coherentKanRightHomInterval K M)) :=
    congrArg functorVertex (congrArg (diagonalFiberTransport pointedSpaceProjection v) hl)
  exact vertexIso_square_of_heq _ _ _ _ _ _ _ _ (hvR x) (hvR x') (hvL x) (hvL x') hR
    (coherentKanRightCompositionMovingIso_heq_constantTop x' y z ht).symm
    (coherentKanRightCompositionMovingIso_heq_constantTop x y z ht).symm hL
    (transportIntervalSquare_constantTopIso_source_naturality pointedSpaceProjection s ht e)

end SerrePositivity.InfinityCategories.F2
