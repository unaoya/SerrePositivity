module

public import SerrePositivity.InfinityCategories.F1.Coherent.KanRightCompositionTransport
public import SerrePositivity.InfinityCategories.F1.Transport.IntervalSquareReindex

/-!
概要：元の二つの Kan 射の合成輸送を、始点も動く全係数上で比較する。
方針：同じ合成四角形を制限し、定値の最終辺を指定比較で消す。
規約：動く始点・二射・元の四角形を保持する。
使われ方：元の全評価の二段合成と合成射の評価の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
/-- 概要：動く始点と二射に沿う二段輸送を同じ合成射輸送へ比較する。
方針：元の合成四角形の係数制限を使う。規約：全係数を保持。使われ方：値の合成則。 -/
def coherentKanRightCompositionTransport_movingIso {K L M : KanObject.{u}} {P : SSet.{u + 1}}
    (x : P ⟶ vertexFiber pointedSpaceProjection (spaceInfinityVertex K))
    (y : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L))
    (z : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom L M)) :
    FunctorIso
      (diagonalFiberTransport pointedSpaceProjection
        (diagonalFiberTransport pointedSpaceProjection x (y ≫ coherentKanRightHomInterval K L))
        (z ≫ coherentKanRightHomInterval L M))
      (diagonalFiberTransport pointedSpaceProjection x
        (lift y z ≫ coherentHomComposition K L M ≫ coherentKanRightHomInterval K M)) := by
  let s := (coherentKanRightCompositionSquare K L M).precomp (lift y z)
  have ht : intervalMappingUncurry s.top = SSet.const (spaceInfinityVertex M) := by
    change intervalMappingUncurry (lift y z ≫
      (coherentKanRightCompositionSquare K L M).top) = _
    rw [intervalMappingUncurry_precomp, coherentKanRightCompositionSquare_top, SSet.comp_const]
  have h := s.constantTopIso pointedSpaceProjection x ht
  simp only [s, TransportIntervalSquare.precomp, coherentKanRightCompositionSquare,
    TransportIntervalSquare.changeVertices, coherentCompositionIntervalSquare, Category.assoc,
    ← Category.assoc (lift y z) (fst _ _), lift_fst,
    ← Category.assoc (lift y z) (snd _ _), lift_snd] at h
  convert h using 1 <;> rfl
end SerrePositivity.InfinityCategories
