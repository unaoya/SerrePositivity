module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTrianglePointedWitness

/-!
概要：元の全三角形の実始域射の厳密な表示変更を、同じ実持ち上げに施す。
方針：初期値の等式だけを移し、実 prism と底の射影をそのまま保持する。
規約：比較も実持ち上げも再選択しない。使われ方：第零面の始点を共通頂点一へ揃える。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 元の実始域射の表示を変えても、同じ全実三角形と全底をそのまま保持する。 -/
def FunctorTrianglePointedWitness.withSource
    {B C : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
    {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
    {T : FunctorCompositionTriangle a b c} {p : C ⟶ B}
    {s t : C ⟶ leftUnstraightening F} (w : FunctorTrianglePointedWitness T p s) (h : s = t) :
    FunctorTrianglePointedWitness T p t where
  prism := w.prism
  projection := w.projection
  initial := w.initial.trans (congrArg (fun f => f ≫ pullback.fst pointedSpaceProjection F) h)

end SerrePositivity.InfinityCategories.F2
