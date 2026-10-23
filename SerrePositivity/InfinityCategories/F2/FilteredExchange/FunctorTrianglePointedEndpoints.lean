module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTrianglePointedWitness

/-!
概要：元の全 pointed 三角形の実中間頂点と実終点を、元の二図式の全空間へ戻す。
方針：元の全底の頂点式と引き戻しの普遍性を使う。
規約：元の実持ち上げと全係数を保持。使われ方：同じ三辺の指定始域比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  {T : FunctorCompositionTriangle a b c} {p : C ⟶ B} {s : C ⟶ leftUnstraightening F}
  (w : FunctorTrianglePointedWitness T p s)

/-- 元の全三角形の同じ実中間頂点を、元の中間図式の全空間へ戻す。 -/
def FunctorTrianglePointedWitness.middle : C ⟶ leftUnstraightening G :=
  pullback.lift (simplexPrismVertex 2 1 C ≫ w.prism) p (by
    rw [Category.assoc, w.projection]
    exact functorTrianglePrism_middle_base T p)

/-- 元の実中間頂点は、同じ元の全底を保つ。 -/
lemma FunctorTrianglePointedWitness.middle_projection :
    w.middle ≫ leftUnstraighteningProjection G = p := pullback.lift_snd _ _ _

/-- 元の実中間頂点の pointed 成分は、同じ全三角形の頂点一そのもの。 -/
lemma FunctorTrianglePointedWitness.middle_pointed :
    simplexPrismVertex 2 1 C ≫ w.prism =
      w.middle ≫ pullback.fst pointedSpaceProjection G := (pullback.lift_fst _ _ _).symm

/-- 元の全三角形の同じ実終点を、元の標的図式の全空間へ戻す。 -/
def FunctorTrianglePointedWitness.endpoint : C ⟶ leftUnstraightening J :=
  pullback.lift (simplexPrismVertex 2 2 C ≫ w.prism) p (by
    rw [Category.assoc, w.projection]
    exact functorTrianglePrism_terminal_base T p)

/-- 元の実終点は、同じ元の全底を保つ。 -/
lemma FunctorTrianglePointedWitness.endpoint_projection :
    w.endpoint ≫ leftUnstraighteningProjection J = p := pullback.lift_snd _ _ _

/-- 元の実終点の pointed 成分は、同じ全三角形の最終頂点そのもの。 -/
lemma FunctorTrianglePointedWitness.endpoint_pointed :
    simplexPrismVertex 2 2 C ≫ w.prism =
      w.endpoint ≫ pullback.fst pointedSpaceProjection J := (pullback.lift_fst _ _ _).symm

end SerrePositivity.InfinityCategories.F2
