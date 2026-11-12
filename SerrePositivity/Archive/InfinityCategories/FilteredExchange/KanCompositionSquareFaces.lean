module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.KanRightCompositionMoving
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ConstantTransportPrecomp

/-!
概要：元の動く二射の係数四角形の四辺を、同じ元の右 Hom 区間へ戻す。
方針：元の頂点表示変更と直積射影を厳密に計算する。
規約：全係数と元の四辺を保持。使われ方：元の合成比較の指定自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {K L M : KanObject.{u}} {P : SSet.{u + 1}}
  (y : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L))
  (z : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom L M))

/-- 元の係数四角形の下辺は、元の第一射の同じ全区間。 -/
lemma coherentKanCompositionSquare_bottom :
    ((coherentKanRightCompositionSquare K L M).precomp (lift y z)).bottom =
      y ≫ coherentKanRightHomInterval K L := by
  simp only [TransportIntervalSquare.precomp, coherentKanRightCompositionSquare,
    TransportIntervalSquare.changeVertices, coherentCompositionIntervalSquare,
    coherentKanRightHomInterval, Category.assoc, ← Category.assoc (lift y z) (fst _ _), lift_fst]
  rfl

/-- 元の係数四角形の右辺は、元の第二射の同じ全区間。 -/
lemma coherentKanCompositionSquare_right :
    ((coherentKanRightCompositionSquare K L M).precomp (lift y z)).right =
      z ≫ coherentKanRightHomInterval L M := by
  simp only [TransportIntervalSquare.precomp, coherentKanRightCompositionSquare,
    TransportIntervalSquare.changeVertices, coherentCompositionIntervalSquare,
    coherentKanRightHomInterval, Category.assoc, ← Category.assoc (lift y z) (snd _ _), lift_snd]
  rfl

/-- 元の係数四角形の左辺は、元の合成射の同じ全区間。 -/
lemma coherentKanCompositionSquare_left :
    ((coherentKanRightCompositionSquare K L M).precomp (lift y z)).left =
      lift y z ≫ coherentHomComposition K L M ≫ coherentKanRightHomInterval K M := by
  simp only [TransportIntervalSquare.precomp, coherentKanRightCompositionSquare,
    TransportIntervalSquare.changeVertices, coherentCompositionIntervalSquare,
    coherentKanRightHomInterval, Category.assoc]
  rfl

/-- 元の係数四角形の終辺は、同じ元の最終頂点に定値。 -/
lemma coherentKanCompositionSquare_top :
    intervalMappingUncurry ((coherentKanRightCompositionSquare K L M).precomp (lift y z)).top =
      SSet.const (spaceInfinityVertex M) :=
  intervalMappingUncurry_precomp_constant _ (coherentKanRightCompositionSquare_top K L M) _

end SerrePositivity.InfinityCategories.F2
